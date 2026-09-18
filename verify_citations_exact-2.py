# Exact citation verifier for the five uploaded/pinned arXiv PDFs.
#
# It checks the exact wording found in the PDF text after only:
#   1. Unicode normalization
#   2. removal of soft hyphens
#   3. joining PDF line-break hyphenation
#   4. whitespace normalization
#
# IMPORTANT:
# PDF extraction does not reproduce the original LaTeX source. Therefore,
# formula-heavy citations are verified by exact prose fragments that occur
# around the displayed mathematics. The source quotations printed below
# preserve the paper's mathematical notation in readable LaTeX.

# Install pypdf automatically when necessary.
import sys
import subprocess

try:
    from pypdf import PdfReader
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "pypdf"])
    from pypdf import PdfReader

from pathlib import Path
from urllib.request import urlretrieve
import re
import unicodedata


# ---------------------------------------------------------------------
# 1. Download the EXACT arXiv versions corresponding to the uploaded PDFs
# ---------------------------------------------------------------------

PDF_URLS = {
    "BCGS26": "https://arxiv.org/pdf/2412.07318v2",
    "Carmona26": "https://arxiv.org/pdf/2107.14176v5",
    "BPS20": "https://arxiv.org/pdf/1903.03396v2",
    "BMS26": "https://arxiv.org/pdf/2504.15759v2",
    "Harpaz": "https://arxiv.org/pdf/1210.0229v1",
}

PDF_DIR = Path("citation_pdfs")
PDF_DIR.mkdir(exist_ok=True)

# Prefer the exact uploaded files when this script is run in the
# ChatGPT/container environment; otherwise download the pinned versions.
UPLOADED = {
    "BCGS26": Path("/mnt/data/2412.07318v2.pdf"),
    "Carmona26": Path("/mnt/data/2107.14176v5.pdf"),
    "BPS20": Path("/mnt/data/1903.03396v2.pdf"),
    "BMS26": Path("/mnt/data/2504.15759v2.pdf"),
    "Harpaz": Path("/mnt/data/1210.0229v1.pdf"),
}

PDFS = {}

for key, url in PDF_URLS.items():
    if UPLOADED[key].exists():
        PDFS[key] = UPLOADED[key]
    else:
        path = PDF_DIR / f"{key}.pdf"
        if not path.exists():
            print(f"Downloading {key}...")
            urlretrieve(url, path)
        PDFS[key] = path


# ---------------------------------------------------------------------
# 2. PDF text extraction
# ---------------------------------------------------------------------
#
# IMPORTANT:
# `pypdf.extract_text()` is convenient but often drops spaces around
# PDF-positioned mathematical material.  For verbatim-ish checking of
# the visible PDF wording, use Poppler's `pdftotext -layout` instead.
#
# We preserve ordinary spaces and line structure.  The ONLY matching
# cleanup below is:
#   1. Unicode normalization
#   2. removal of soft hyphens
#   3. joining a word split by a PDF line-break hyphen
#   4. converting a line break to one ordinary space
#
# We deliberately DO NOT collapse ordinary spaces inside a line.

def extract_layout_text(pdf_path: Path, start_page: int, end_page: int) -> str:
    """Extract visible PDF text with ordinary spaces preserved (raw reading order)."""
    import shutil
    import subprocess

    pdftotext = shutil.which("pdftotext")
    if pdftotext is None:
        raise RuntimeError(
            "pdftotext was not found. Install Poppler's pdftotext command."
        )

    cmd = [
        pdftotext,
        "-raw",
        "-f", str(start_page),
        "-l", str(end_page),
        str(pdf_path),
        "-",
    ]
    result = subprocess.run(
        cmd,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
    )
    return result.stdout


def normalize_for_match(text: str) -> str:
    """
    Minimal normalization for matching PDF prose.

    Unlike the previous version, this does NOT use `re.sub(r"\\s+", " ", ...)`,
    so spaces in the source wording are not silently deleted/collapsed.
    """
    text = unicodedata.normalize("NFKC", text)
    text = text.replace("\u00ad", "")

    # Join only a word split by a PDF line-break hyphen:
    # "homotop-\nical" -> "homotopical"
    text = re.sub(r"(?<=\w)-[ \t]*\n[ \t]*(?=\w)", "", text)

    # A line break between ordinary words represents the continuation of
    # the same paragraph. Preserve it as one ordinary space.
    text = re.sub(r"[ \t]*\n[ \t]*", " ", text)

    return text


def get_page_text(pdf_path: Path, start_page: int, end_page: int) -> str:
    return normalize_for_match(
        extract_layout_text(pdf_path, start_page, end_page)
    )


def exact_fragment_found(
    pdf_key: str,
    fragment: str,
    start_page: int,
    end_page: int,
) -> bool:
    """
    Exact substring search with spaces preserved.

    The target is expected to contain the source's actual spaces.
    No whitespace collapsing or fuzzy matching is performed.
    """
    text = get_page_text(PDFS[pdf_key], start_page, end_page)
    target = normalize_for_match(fragment)
    return target in text


# ---------------------------------------------------------------------
# 3. VERIFICATION TARGETS
#
# Formula-heavy statements are split into exact prose fragments because
# pypdf represents displayed LaTeX mathematics differently from the
# original source. Every fragment below is copied from the surrounding
# paper wording, not paraphrased.
# ---------------------------------------------------------------------

CHECKS = {
    "C1": {
        "paper": "BCGS26",
        "pages": (35, 35),
        # This is the complete homotopical-operadic-localization argument
        # from Section 5.2.  The explicit citation to Carmona is part of
        # the paper's text: [Car23a, Theorem 3.13].
        "citation": "[Car23a, Theorem 3.13]",
        "fragments": [
            "Homotopical operadic localization:",
            "Use [Car23a, Theorem 3.13] to observe that Open Problem 5.6",
            "would be solved if the composite multifunctor",
            "exhibits a homotopical localization of the spacetime-wise tPFA operad",
            "given by all Cauchy morphisms in",
            "Denoting by",
            "such a homotopical localization as an operad in simplicial sets, this amounts to showing",
            "is a weak equivalence of operads in simplicial sets.",
            "A mild generalization of Theorem 3.3 entails that",
            "exhibits the ordinary localization",
            "hence it suffices to show that all spaces of operations",
            "are discrete, i.e. they have vanishing higher homotopy groups",
            "Since homotopical localizations of operads are currently not yet well-developed and studied",
            "we are uncertain if this approach will be successful.",
        ],
    },

    "C2": {
        "paper": "BCGS26",
        "pages": (9, 9),
        "fragments": [
            "Proposition 2.8.",
            "of the functor (2.8) to the full subcategory",
            "of additive AQFTs over Loc is fully faithful.",
        ],
    },

    "C3": {
        "paper": "Carmona26",
        "pages": (15, 15),
        "fragments": [
            "Theorem 3.13.",
            "The homotopical localization morphism",
            "induces a Quillen equivalence",
        ],
    },

    "C4": {
        "paper": "Carmona26",
        "pages": (14, 14),
        "fragments": [
            "Since homotopy S-constant field theories are presented as algebras over the operad",
            "the projective model structure on these algebras",
            "presents the homotopy theory of those field theories.",
        ],
    },

    "C5": {
        "paper": "BPS20",
        "pages": (20, 20),
        "fragments": [
            "We can also define a Set-valued colored operad PLoc such that",
            "By operadic left Kan extension, there exists an adjunction",
        ],
    },

    "C6": {
        "paper": "BMS26",
        "pages": (16, 16),
        "fragments": [
            "This means that an FQFT is a multifunctor",
            "and that a morphism between FQFTs is a multinatural transformation",
        ],
    },

    "C7": {
        "paper": "Harpaz",
        "pages": (2, 2),
        "fragments": [
            "Note that Bun 0 is a (discrete) ∞-groupoid.",
        ],
    },

    "C8": {
        "paper": "BMS26",
        "pages": (6, 6),
        "fragments": [
            "This means that an AQFT is a multifunctor",
            "sends every Cauchy morphism",
            "to an isomorphism",
        ],
    },

    "C9": {
        "paper": "BMS26",
        "pages": (23, 23),
        "fragments": [
            "Theorem 5.7.",
            "For every spacetime dimension",
            "are quasi-inverse to each other. Hence, they exhibit an equivalence",
            "between the category",
            "of additive AQFTs satisfying the time-slice axiom",
            "of additive FQFTs satisfying the time-slice axiom",
        ],
    },
}


# ---------------------------------------------------------------------
# 3b. C1: print the ENTIRE homotopical-operadic-localization passage
#
# This avoids hard-coding a long copyrighted quotation into this script.
# The script extracts it directly from the pinned PDF when run locally.
# ---------------------------------------------------------------------

def show_c1_homotopical_operadic_localization():
    """
    Print the complete 'Homotopical operadic localization' subsection
    from BCGS26, Section 5.2, including its Carmona citation.

    The extraction is intentionally local: the paper itself supplies
    the full wording, while this script merely locates and prints it.
    """
    text = get_page_text("BCGS26", 35, 35)

    start = text.find("Homotopical operadic localization:")
    end = text.find("∞-categorical localization:", start)

    if start == -1:
        raise RuntimeError(
            "Could not locate the C1 heading "
            "'Homotopical operadic localization:' on PDF page 35."
        )

    if end == -1:
        raise RuntimeError(
            "Could not locate the next heading "
            "'∞-categorical localization:' on PDF page 35."
        )

    passage = text[start:end].strip()

    print("\\n" + "=" * 78)
    print("C1 — COMPLETE HOMOTOPICAL OPERADIC LOCALIZATION PASSAGE")
    print("=" * 78)
    print("Source: BCGS26, Section 5.2, PDF page 35")
    print("Carmona citation appearing in the passage: [Car23a, Theorem 3.13]")
    print("-" * 78)
    print(passage)
    print("=" * 78)


# ---------------------------------------------------------------------
# 4. Run all checks
# ---------------------------------------------------------------------

print("\n" + "=" * 78)
print("EXACT SOURCE-WORDING VERIFICATION")
print("=" * 78)

overall_ok = True

for cid, info in CHECKS.items():
    paper = info["paper"]
    start_page, end_page = info["pages"]

    print(f"\n{cid}  |  {PDFS[paper].name}  |  PDF pages {start_page}-{end_page}")
    print("-" * 78)

    results = []

    for fragment in info["fragments"]:
        ok = exact_fragment_found(
            paper,
            fragment,
            start_page,
            end_page,
        )
        results.append(ok)

        status = "FOUND" if ok else "NOT FOUND"
        print(f"[{status}] {fragment}")

    citation_ok = all(results)
    overall_ok = overall_ok and citation_ok

    print(
        f"=> {cid}: "
        + ("ALL REQUIRED FRAGMENTS FOUND" if citation_ok else "CHECK FAILED")
    )


print("\n" + "=" * 78)
print(
    "OVERALL:",
    "ALL CHECKS PASSED" if overall_ok else "ONE OR MORE CHECKS FAILED"
)
print("=" * 78)


# ---------------------------------------------------------------------
# 5. Optional helper: inspect the exact PDF text around a phrase
# ---------------------------------------------------------------------

def show_context(
    pdf_key: str,
    phrase: str,
    start_page: int,
    end_page: int,
    context_chars: int = 900,
):
    text = get_page_text(PDFS[pdf_key], start_page, end_page)
    target = normalize(phrase)

    pos = text.find(target)

    if pos == -1:
        print(f"Phrase not found in {pdf_key}, pages {start_page}-{end_page}:")
        print(phrase)
        return

    lo = max(0, pos - context_chars)
    hi = min(len(text), pos + len(target) + context_chars)

    print("\n" + "=" * 78)
    print(f"{pdf_key} — pages {start_page}-{end_page}")
    print("=" * 78)
    print(text[lo:hi])


# Examples:
# show_c1_homotopical_operadic_localization()
# show_context("BCGS26", "Open Problem 5.6 would be solved if", 35, 35)
# show_context("Carmona26", "Theorem 3.13.", 15, 15)
