#!/usr/bin/env python3
"""Standalone proof verifier — difficulty-adaptive verification pipeline.

Two modes:
  - Problem + Proof: classifies difficulty, then routes through a 1-agent
    (Easy) or 3-agent (Hard) verification pipeline.
  - Problem only: reviews the problem statement for well-definedness and
    defects (no proof needed).

Usage:
    python verify/verify.py problem.txt proof.txt
    python verify/verify.py problem.txt --problem-only         # problem-only mode
    python verify/verify.py problem.txt proof.txt -o report.md
    python verify/verify.py problem.txt proof.txt --provider gemini
    python verify/verify.py problem.txt proof.txt --model sonnet
    python verify/verify.py problem.txt proof.txt --config /path/to/config.yaml
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

import yaml

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(SCRIPT_DIR)
DEFAULT_CONFIG = os.path.join(REPO_ROOT, "config.yaml")

PROMPT_JUDGE = os.path.join(SCRIPT_DIR, "prompt_judge.md")
PROMPT_STRUCTURAL = os.path.join(SCRIPT_DIR, "prompt_verify_structural.md")
PROMPT_DETAILED = os.path.join(SCRIPT_DIR, "prompt_verify_detailed.md")
PROMPT_CHECK_PROBLEM = os.path.join(SCRIPT_DIR, "prompt_check_problem.md")


# ---------------------------------------------------------------------------
# Config helpers
# ---------------------------------------------------------------------------

def load_config(path: str) -> dict:
    with open(path) as f:
        return yaml.safe_load(f)


def make_claude_options(claude_cfg: dict) -> dict:
    """Build options dict for the Claude CLI (mirrors pipeline.py)."""
    provider = claude_cfg.get("provider", "subscription")
    env = {}

    if provider == "subscription":
        sub_cfg = claude_cfg.get("subscription", {})
        model = sub_cfg.get("model", "opus")
    elif provider == "api_key":
        api_cfg = claude_cfg.get("api_key", {})
        model = api_cfg.get("model", "claude-opus-4-6")
        key = api_cfg.get("key", "")
        if key:
            env["ANTHROPIC_API_KEY"] = key
    elif provider == "bedrock":
        bedrock_cfg = claude_cfg.get("bedrock", {})
        model = bedrock_cfg.get("model", "us.anthropic.claude-opus-4-6-v1[1m]")
        env["CLAUDE_CODE_USE_BEDROCK"] = "1"
        env["AWS_PROFILE"] = bedrock_cfg.get("aws_profile", "default")
    else:
        raise ValueError(f"Unknown claude.provider '{provider}'.")

    return {
        "cli_path": claude_cfg.get("cli_path", "claude"),
        "model": model,
        "env": env,
    }


def resolve_agent_role_cfg(config: dict, agent_name: str,
                           cli_provider: str | None,
                           cli_model: str | None) -> dict:
    sv_cfg = config.get("standalone_verifier", {})
    raw = sv_cfg.get(agent_name)
    if not isinstance(raw, dict) or "provider" not in raw:
        raise ValueError(
            f"standalone_verifier.{agent_name} must be a dict with a 'provider' key. Got: {raw!r}"
        )
    role_cfg = dict(raw)
    if cli_provider:
        role_cfg["provider"] = cli_provider
    if cli_model:
        role_cfg["model"] = cli_model
    return role_cfg


def merge_provider_section(config: dict, role_cfg: dict) -> tuple[str, dict]:
    provider = role_cfg["provider"].lower().strip()
    if provider not in ("claude", "codex", "gemini"):
        raise ValueError(
            f"Unknown provider {provider!r}; expected 'claude', 'codex', or 'gemini'."
        )
    overrides = {k: v for k, v in role_cfg.items() if k != "provider"}
    global_section = config.get(provider, {})

    if provider == "claude":
        merged = dict(global_section)
        auth_mode = merged.get("provider", "subscription")
        if "model" in overrides:
            sub = dict(merged.get(auth_mode, {}))
            sub["model"] = overrides["model"]
            merged[auth_mode] = sub
        for k, v in overrides.items():
            if k == "model":
                continue
            merged[k] = v
        return provider, merged

    merged = {**global_section, **overrides}
    return provider, merged


# ---------------------------------------------------------------------------
# Prompt loading
# ---------------------------------------------------------------------------

def load_prompt(path: str, **kwargs) -> str:
    with open(path) as f:
        template = f.read()
    return template.format(**kwargs)


# ---------------------------------------------------------------------------
# Model invocation (Modified to route directly via OpenRouter SDK)
# ---------------------------------------------------------------------------

def run_claude(prompt: str, claude_opts: dict, model_override: str | None = None) -> str:
    """Invoke Claude CLI and return response text."""
    cli_path = claude_opts.get("cli_path", "claude")
    model = model_override or claude_opts.get("model", "opus")
    extra_env = claude_opts.get("env", {})

    cmd = [
        cli_path,
        "-p",
        "--output-format", "json",
        "--dangerously-skip-permissions",
        "--model", model,
        prompt,
    ]

    _PROVIDER_VARS = ("CLAUDE_CODE_USE_BEDROCK", "ANTHROPIC_API_KEY",
                      "AWS_PROFILE", "ANTHROPIC_MODEL")
    env = {k: v for k, v in os.environ.items() if k not in _PROVIDER_VARS}
    env.update(extra_env)

    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, env=env)

    try:
        data = json.loads(result.stdout)
        response = data.get("result", "")
    except (json.JSONDecodeError, ValueError):
        response = result.stdout.strip()

    if not response.strip():
        raise RuntimeError(f"Claude returned empty response. Exit code: {result.returncode}")
    return response


def run_codex(prompt: str, codex_cfg: dict, model_override: str | None = None) -> str:
    """Directly invokes OpenRouter API securely via the OpenAI SDK wrapper."""
    try:
        from openai import OpenAI
    except ImportError:
        print("[Error] The 'openai' python library is missing inside the container terminal.", file=sys.stderr)
        raise RuntimeError("Missing python 'openai' dependency.")

    # Fetch authorization keys safely
    api_key = os.environ.get("OPENROUTER_API_KEY")
    if not api_key:
        api_key = codex_cfg.get("api_key", "")
    
    if not api_key:
        raise RuntimeError("Authentication Failed: No 'OPENROUTER_API_KEY' found in environment variables or config.")

    # Determine targeted model architecture smoothly
    model = model_override or codex_cfg.get("model", "openai/gpt-4o")
    
    # Auto-patch if the user supplies a naked slug like "gpt-4o"
    if "/" not in model:
        print(f"[OpenRouter Wrapper] Automatically adapting model name to: openai/{model}", file=sys.stderr)
        model = f"openai/{model}"

    print(f"[OpenRouter] Forwarding verification packet to: {model}", file=sys.stderr)

    # Instantiate explicit OpenRouter Client wrapper
    client = OpenAI(
        base_url="https://openrouter.ai/api/v1",
        api_key=api_key,
        default_headers={
            "HTTP-Referer": "https://github.com/QED-verification",
            "X-Title": "QED Adaptive Standalone Verifier"
        }
    )

    try:
        # Wrap the math verification payload inside Chat Completion Architecture
        response = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": "You are a precise, rigorous automated mathematical proof verification agent."},
                {"role": "user", "content": prompt}
            ],
            temperature=0.0,  # Force exact determinism for verification math gates
            max_tokens=2500   # Dropped slightly to squeeze under your remaining balance (2984)
        )
        
        output_text = response.choices[0].message.content
        if not output_text or not output_text.strip():
            raise RuntimeError("API warning: OpenRouter processed request successfully but returned a completely empty body string.")
        
        return output_text

    except Exception as e:
        # CRITICAL: Prevent execution swallowing. Force failures straight to console trace
        print(f"\n[!!!] CRITICAL OPENROUTER CONTEXT EXCEPTION: {e}\n", file=sys.stderr)
        raise RuntimeError(f"OpenRouter routing engine failed: {e}")


def run_gemini(prompt: str, gemini_cfg: dict, model_override: str | None = None) -> str:
    """Invoke Gemini CLI and return response text."""
    cli_path = gemini_cfg.get("cli_path", "gemini")
    model = model_override or gemini_cfg.get("model", "gemini-3.1-pro-preview")
    api_key = gemini_cfg.get("api_key", "")
    approval_mode = gemini_cfg.get("approval_mode", "yolo")
    thinking_level = gemini_cfg.get("thinking_level", "")
    thinking_budget = gemini_cfg.get("thinking_budget")

    cmd = [
        cli_path,
        "-m", model,
        "--approval-mode", approval_mode,
        "-o", "json",
        "-p", prompt,
    ]

    env = os.environ.copy()
    if api_key:
        env["GEMINI_API_KEY"] = api_key

    thinking_config = {}
    if thinking_level:
        thinking_config["thinkingLevel"] = thinking_level
    if thinking_budget is not None:
        thinking_config["thinkingBudget"] = thinking_budget

    if thinking_config:
        with tempfile.TemporaryDirectory(prefix="qed-gemini-home-") as gemini_home:
            settings_dir = os.path.join(gemini_home, ".gemini")
            os.makedirs(settings_dir, exist_ok=True)
            settings_path = os.path.join(settings_dir, "settings.json")
            settings = {
                "modelConfigs": {
                    "overrides": [{
                        "match": {"model": model},
                        "modelConfig": {
                            "generateContentConfig": {
                                "thinkingConfig": thinking_config,
                            }
                        },
                    }]
                }
            }
            with open(settings_path, "w") as f:
                json.dump(settings, f)
            env["GEMINI_CLI_HOME"] = gemini_home
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
    else:
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)

    try:
        data = json.loads(result.stdout)
        response = data.get("response", "")
    except (json.JSONDecodeError, ValueError):
        response = result.stdout.strip()

    if not response.strip():
        raise RuntimeError(f"Gemini returned empty response. Exit code: {result.returncode}")
    return response


def run_model_for_role(role_cfg: dict, prompt: str, config: dict) -> str:
    provider, merged_section = merge_provider_section(config, role_cfg)
    model_override = role_cfg.get("model")
    if provider == "claude":
        claude_opts = make_claude_options(merged_section)
        return run_claude(prompt, claude_opts)
    elif provider == "codex":
        return run_codex(prompt, merged_section, model_override)
    elif provider == "gemini":
        return run_gemini(prompt, merged_section, model_override)
    else:
        raise ValueError(f"Unknown provider: {provider!r}.")


# ---------------------------------------------------------------------------
# Output parsing
# ---------------------------------------------------------------------------

def parse_difficulty(judge_output: str) -> str:
    match = re.search(r'\*\*Difficulty:\*\*\s*(Easy|Hard)', judge_output, re.IGNORECASE)
    if match:
        return match.group(1).capitalize()
    for line in judge_output.split("\n")[:20]:
        if "easy" in line.lower() and "difficult" in line.lower():
            continue
        if re.search(r'\bEasy\b', line):
            return "Easy"
        if re.search(r'\bHard\b', line):
            return "Hard"
    return "Hard"


def parse_structural_verdict(structural_output: str) -> str:
    match = re.search(r'Overall Structural Verdict:\s*(PASS|FAIL)', structural_output, re.IGNORECASE)
    if match:
        return match.group(1).upper()
    match = re.search(r'Overall\s+Verdict:\s*(PASS|FAIL)', structural_output, re.IGNORECASE)
    if match:
        return match.group(1).upper()
    return "FAIL"


# ---------------------------------------------------------------------------
# Report assembly
# ---------------------------------------------------------------------------

def assemble_report(difficulty: str, judge_output: str,
                    structural_output: str | None = None,
                    structural_verdict: str | None = None,
                    detailed_output: str | None = None) -> str:
    sections = []

    if difficulty == "Easy":
        sections.append(judge_output)
    else:
        sections.append("# Standalone Proof Verification Report")
        sections.append("")
        sections.append("**Difficulty:** Hard")
        sections.append("**Pipeline:** Judge -> Structural -> Detailed")
        sections.append("")

        rationale_match = re.search(r'\*\*Rationale:\*\*\s*(.+)', judge_output)
        if rationale_match:
            sections.append(f"**Rationale:** {rationale_match.group(1).strip()}")
            sections.append("")

        sections.append("---")
        sections.append("")

        if structural_output:
            sections.append("# Structural Verification")
            sections.append("")
            sections.append(structural_output)
            sections.append("")

        if structural_verdict == "FAIL":
            sections.append("---")
            sections.append("")
            sections.append("*Detailed verification skipped — structural verification FAILED.*")
        elif detailed_output:
            sections.append("---")
            sections.append("")
            sections.append("# Detailed Verification")
            sections.append("")
            sections.append(detailed_output)

    return "\n".join(sections)


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

def write_report(report: str, output_path: str | None):
    if output_path:
        with open(output_path, "w") as f:
            f.write(report)
        print(f"Report written to {output_path}", file=sys.stderr)
    else:
        print(report)


def run_problem_only(args):
    if not os.path.isfile(args.problem):
        print(f"Error: problem file not found: {args.problem}", file=sys.stderr)
        sys.exit(1)

    with open(args.problem) as f:
        problem_text = f.read()

    config = load_config(args.config)
    role_cfg = resolve_agent_role_cfg(config, "problem_reviewer", args.provider, args.model)

    print(f"[Problem Review] Checking problem statement ({role_cfg['provider']})", file=sys.stderr)
    prompt = load_prompt(PROMPT_CHECK_PROBLEM, problem=problem_text)
    report = run_model_for_role(role_cfg, prompt, config)

    print(f"[Problem Review] Done", file=sys.stderr)
    write_report(report, args.output)


def output_dir_from_args(args) -> str | None:
    if args.output is None:
        return None
    return os.path.dirname(args.output) or "."


def run_verification(args):
    with open(args.problem) as f:
        problem_text = f.read()
    with open(args.proof) as f:
        proof_text = f.read()

    config = load_config(args.config)
    out_dir = output_dir_from_args(args)

    # --- Agent 1: Difficulty Judge ---
    judge_role = resolve_agent_role_cfg(config, "judge", args.provider, args.model)

    print(f"[Agent 1] Difficulty Judge ({judge_role['provider']})", file=sys.stderr)
    judge_prompt = load_prompt(PROMPT_JUDGE, problem=problem_text, proof=proof_text)
    judge_output = run_model_for_role(judge_role, judge_prompt, config)

    difficulty = parse_difficulty(judge_output)
    print(f"[Agent 1] Difficulty: {difficulty}", file=sys.stderr)

    if difficulty == "Easy":
        report = assemble_report("Easy", judge_output)
        write_report(report, args.output)
        return

    # --- Agent 2: Structural Verifier ---
    struct_role = resolve_agent_role_cfg(config, "structural_verifier", args.provider, args.model)

    print(f"[Agent 2] Structural Verifier ({struct_role['provider']})", file=sys.stderr)
    struct_prompt = load_prompt(PROMPT_STRUCTURAL, problem=problem_text, proof=proof_text)
    structural_output = run_model_for_role(struct_role, struct_prompt, config)

    if out_dir:
        write_report(structural_output, os.path.join(out_dir, "structural_report.md"))

    structural_verdict = parse_structural_verdict(structural_output)
    print(f"[Agent 2] Structural Verdict: {structural_verdict}", file=sys.stderr)

    if structural_verdict == "FAIL":
        report = assemble_report("Hard", judge_output, structural_output, structural_verdict)
        write_report(report, args.output)
        return

    # --- Agent 3: Detailed Verifier ---
    detail_role = resolve_agent_role_cfg(config, "detailed_verifier", args.provider, args.model)

    print(f"[Agent 3] Detailed Verifier ({detail_role['provider']})", file=sys.stderr)
    detail_prompt = load_prompt(PROMPT_DETAILED, problem=problem_text, proof=proof_text, structural_report=structural_output)
    detailed_output = run_model_for_role(detail_role, detail_prompt, config)

    print(f"[Agent 3] Done", file=sys.stderr)

    if out_dir:
        write_report(detailed_output, os.path.join(out_dir, "detailed_report.md"))

    report = assemble_report("Hard", judge_output, structural_output, structural_verdict, detailed_output)
    write_report(report, args.output)


def main():
    parser = argparse.ArgumentParser(
        description="Standalone proof verifier — difficulty-adaptive verification pipeline.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("problem", help="Path to problem statement file")
    parser.add_argument("proof", nargs="?", default=None, help="Path to proof file")
    parser.add_argument("--problem-only", action="store_true", help="Review problem statement only (no proof needed)")
    parser.add_argument("-o", "--output", default=None, help="Write report to file (default: stdout)")
    parser.add_argument("--provider", default=None, choices=["claude", "codex", "gemini"], help="Override all agents to one provider")
    parser.add_argument("-m", "--model", default=None, help="Override model name for all agents")
    parser.add_argument("-c", "--config", default=DEFAULT_CONFIG, help=f"Path to config.yaml (default: {DEFAULT_CONFIG})")

    args = parser.parse_args()

    if not os.path.isfile(args.problem):
        print(f"Error: problem file not found: {args.problem}", file=sys.stderr)
        sys.exit(1)
    if not os.path.isfile(args.config):
        print(f"Error: config file not found: {args.config}", file=sys.stderr)
        sys.exit(1)

    if args.problem_only:
        run_problem_only(args)
    else:
        if args.proof is None:
            print("Error: proof file is required (or use --problem-only)", file=sys.stderr)
            sys.exit(1)
        if not os.path.isfile(args.proof):
            print(f"Error: proof file not found: {args.proof}", file=sys.stderr)
            sys.exit(1)
        run_verification(args)


if __name__ == "__main__":
    main()