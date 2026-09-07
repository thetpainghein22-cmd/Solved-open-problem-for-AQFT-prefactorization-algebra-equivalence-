FROM continuumio/miniconda3:latest

ENV DEBIAN_FRONTEND=noninteractive
WORKDIR /work/QED-main

RUN apt-get update && apt-get install -y --no-install-recommends
bash
ca-certificates
nodejs
npm
&& rm -rf /var/lib/apt/lists/*

COPY . /work/QED-main

RUN conda create -n agent python=3.11 -y &&
ln -sf /opt/conda/envs/agent/bin/python /opt/conda/envs/agent/bin/python3 &&
/opt/conda/envs/agent/bin/python -m pip install --no-cache-dir pyyaml openai

RUN npm install -g @openai/codex

RUN cat >/usr/local/bin/claude <<'EOF' && chmod +x /usr/local/bin/claude
#!/usr/bin/env bash
echo "claude shim: this repo's current config does not use Claude" >&2
exit 0
EOF

ENV PATH="/usr/local/bin:/opt/conda/envs/agent/bin:${PATH}"

CMD ["python3", "verify/verify.py", "standalone_verifier/problem.txt", "standalone_verifier/proof.txt", "--provider", "codex", "--model", "gpt-4o"]
