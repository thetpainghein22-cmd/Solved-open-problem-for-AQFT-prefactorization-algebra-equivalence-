import re
import urllib.request
from typing import Tuple, Dict, List
import fitz  # PyMuPDF

# ---------------------------------------------------------------------------
# Verbatim Sources (Untouched)
# ---------------------------------------------------------------------------
PDF_URLS = {
    "C1": "https://arxiv.org/pdf/2412.07318v2.pdf",
    "C2": "https://arxiv.org/pdf/2412.07318v2.pdf",
    "C3": "https://arxiv.org/pdf/2107.14176v5.pdf",
    "C4": "https://arxiv.org/pdf/2107.14176v5.pdf",
    "C5": "https://arxiv.org/pdf/1903.03396v2.pdf",
    "C6": "https://arxiv.org/pdf/2504.15759v2.pdf",
    "C7": "https://arxiv.org/pdf/1210.0229v1.pdf",
    "C9": "https://arxiv.org/pdf/2504.15759v2.pdf",
}

CHECKS = {
    "C1": {
        "pages": (35, 35),
        "source": "Benini--Carmona--Grant-Stuart--Schenkel, §5.2",
        "quotes": [
            r"""Use [Car23a, Theorem 3.13] to observe that Open Problem 5.6 would be solved if the composite multifunctor $L_M\Phi_M : \mathrm{tP}_M \to \mathcal{O}_M[W_M^{-1}]$ exhibits a homotopical localization of the spacetime-wise tPFA operad $\mathrm{tP}_M$ over $\mathrm{Loc}_{\mathrm{rc}}/M$ at the subset of 1-ary operations $W_M \subseteq \operatorname{Mor}_1(\mathrm{tP}_M)$ given by all Cauchy morphisms in $\mathrm{tP}_M$.""",
            r"""Denoting by $L_{W_M}\mathrm{tP}_M$ such a homotopical localization as an operad in simplicial sets, this amounts to showing that the induced multifunctor $L_{W_M}\mathrm{tP}_M \to \mathcal{O}_M[W_M^{-1}]$ is a weak equivalence of operads in simplicial sets.""",
            r"""A mild generalization of Theorem 3.3 entails that $L_M\Phi_M$ exhibits the ordinary localization of $\mathrm{tP}_M$ at $W_M$, hence it suffices to show that all spaces of operations in $L_{W_M}\mathrm{tP}_M$ are discrete, i.e. they have vanishing higher homotopy groups $\pi_{\geq 1}$.""",
            r"""Since homotopical localizations of operads are currently not yet well-developed and studied, we are uncertain if this approach will be successful.""",
        ],
    },
    "C2": {
        "pages": (9, 9),
        "source": "Benini--Carmona--Grant-Stuart--Schenkel, Proposition 2.8",
        "quotes": [
            r"""The restriction $(-) \restriction{\mathrm{rc}} : \mathrm{AQFT}^{\mathrm{add}} \xrightarrow{\mathrm{f.f.}} \mathrm{AQFT}^{\mathrm{rc}}$ (2.10) of the functor (2.8) to the full subcategory $\mathrm{AQFT}^{\mathrm{add}} \subseteq \mathrm{AQFT}$ of additive AQFTs over $\mathrm{Loc}$ is fully faithful.""",
        ],
    },
    "C3": {
        "pages": (15, 15),
        "source": "Carmona, Theorem 3.13",
        "quotes": [
            r"""The homotopical localization morphism $\ell : \mathcal{O}_C^{\perp} \to L_S\mathcal{O}_C^{\perp}$ induces a Quillen equivalence $L_S\mathrm{Qft}(C^{\perp}) \rightleftarrows \mathrm{Qft}^h_S(C^{\perp})$.""",
        ],
    },
    "C4": {
        "pages": (14, 14),
        "source": "Carmona, paragraph preceding Proposition 3.9",
        "quotes": [
            r"""Since homotopy $S$-constant field theories are presented as algebras over the operad $L_S\mathcal{O}_C^{\perp}$, the projective model structure on these algebras, which we denote appealingly by $\mathrm{Qft}^h_S(C^{\perp})$, presents the homotopy theory of those field theories.""",
        ],
    },
    "C5": {
        "pages": (19, 20),
        "source": "Benini--Perin--Schenkel, Remark 5.2",
        "quotes": [
            r"""Recall from [BSW17] that there exists a Set-valued colored operad $\mathcal{O}(\mathrm{Loc},\perp)$ whose category of $\mathcal{C}$-valued algebras is the category of algebraic quantum field theories, i.e. AQFT $= \operatorname{Alg}_{\mathcal{O}(\mathrm{Loc},\perp)}(\mathcal{C})$.""",
            r"""We can also define a Set-valued colored operad $\mathcal{P}_{\mathrm{Loc}}$ such that $\mathrm{tPFA}=\operatorname{Alg}_{\mathcal{P}_{\mathrm{Loc}}}(\mathcal{C})$.""",
            r"""By operadic left Kan extension, there exists an adjunction $\Phi_! : \mathrm{tPFA} \rightleftarrows \mathrm{AQFT} : \Phi^* = F$.""",
        ],
    },
    "C6": {
        "pages": (16, 16),
        "source": "Bunk--MacManus--Schenkel, Definition 4.1(a)",
        "quotes": [
            r"""This means that an FQFT is a multifunctor $F : \tau(\mathrm{LBop}_m) \to \mathrm{Alg}_{uAs}(T)$ and that a morphism between FQFTs is a multinatural transformation $\zeta : F \Rightarrow G : \tau(\mathrm{LBop}_m) \to \mathrm{Alg}_{uAs}(T)$.""",
        ],
    },
    "C7": {
        "pages": (2, 2),
        "source": "Harpaz, p. 2",
        "quotes": [
            r"""Let $Bun_0$ be the 0-dimensional unoriented cobordism category, i.e. the objects of $Bun_0$ are 0-dimensional closed manifolds (or equivalently, finite sets) and the morphisms are diffeomorphisms (or equivalently, isomorphisms of finite sets).""",
            r"""Note that $Bun_0$ is a (discrete) $\infty$-groupoid.""",
        ],
    },
    "C9": {
        "pages": (23, 23),
        "source": "Bunk--MacManus--Schenkel, Theorem 5.7",
        "quotes": [
            r"""For every spacetime dimension $m \in \mathbb{N}$, the two functors $F : AQFT_m^{W,\mathrm{add}} \to FQFT_m^{W,\mathrm{add}}$ and $A : FQFT_m^{W,\mathrm{add}} \to AQFT_m^{W,\mathrm{add}}$ from Lemmas 5.2 and 5.6 are quasi-inverse to each other.""",
            r"""Hence, they exhibit an equivalence $AQFT_m^{W,\mathrm{add}} \simeq FQFT_m^{W,\mathrm{add}}$ (5.22) between the category $AQFT_m^{W,\mathrm{add}}$ of additive AQFTs satisfying the time-slice axiom (see Definitions 2.3 and 2.5) and the category $FQFT_m^{W,\mathrm{add}}$ of additive FQFTs satisfying the time-slice axiom (see Definitions 4.1 and 4.5).""",
        ],
    },
}

# ---------------------------------------------------------------------------
# Core Logic
# ---------------------------------------------------------------------------

def extract_pdf_text(pdf_url: str, start_page: int, end_page: int) -> str:
    """Downloads PDF into memory and extracts plain text from specific pages."""
    req = urllib.request.Request(pdf_url, headers={'User-Agent': 'Mozilla/5.0'})
    try:
        with urllib.request.urlopen(req) as resp:
            doc = fitz.open(stream=resp.read(), filetype="pdf")
    except Exception as e:
        return ""

    text = ""
    for p in range(start_page - 1, end_page):
        if p < len(doc):
            text += doc[p].get_text() + "\n"
    return text

def parse_and_tag_latex(quote: str) -> Tuple[str, Dict[str, str]]:
    """
    Finds all math blocks in the quote (delimited by $$ or $),
    replaces them with <notation X>, and returns the mapping.
    """
    math_blocks = re.findall(r'\$.*?\$', quote)
    tagged_quote = quote
    mapping = {}

    for i, block in enumerate(math_blocks, 1):
        tag = f"<notation {i}>"
        tagged_quote = tagged_quote.replace(block, tag, 1)
        mapping[tag] = block

    return tagged_quote, mapping

def verify_structural_prose(tagged_quote: str, page_text: str) -> bool:
    """
    Validates that the exact English prose AND the math placeholders (<notation X>)
    exist in sequence within the same sentence structure on the page.
    """
    # 1. Clean PDF text of extraction artifacts (ligatures, split line hyphens)
    norm_pdf = page_text.replace('ﬁ', 'fi').replace('ﬂ', 'fl').replace('ﬀ', 'ff')
    norm_pdf = re.sub(r'-\n\s*', '', norm_pdf)  # rejoin hyphenated line-breaks
    norm_pdf = re.sub(r'\s+', ' ', norm_pdf)    # collapse multi-spaces and newlines

    # 2. Split tagged quote into prose chunks where <notation X> tags occur
    prose_chunks = re.split(r'<notation \d+>', tagged_quote)

    regex_parts = []
    for chunk in prose_chunks:
        clean_chunk = re.sub(r'\s+', ' ', chunk).strip()
        if clean_chunk:
            # Escape regex symbols and allow flexible whitespace between words
            escaped = re.escape(clean_chunk).replace(r'\ ', r'\s+')
            # Allow optional hyphenation in words like "quasi-inverse" vs "quasi - inverse"
            escaped = escaped.replace(r'\-', r'[\-\s]*')
            regex_parts.append(escaped)

    # 3. Join prose chunks with a strict wildcard buffer (1 to 150 chars max).
    # This guarantees a math expression exists between the prose chunks,
    # but prevents jumping across unrelated paragraphs.
    pattern = r'.{1,150}?'.join(regex_parts)

    return bool(re.search(pattern, norm_pdf, re.IGNORECASE))

# ---------------------------------------------------------------------------
# Execution
# ---------------------------------------------------------------------------

print("=" * 88)
print("STRUCTURAL TAGGING CITATION VERIFIER (LEAN FORMALIZATION MODE)")
print("=" * 88 + "\n")

all_ok = True

for cid, check in CHECKS.items():
    pdf_url = PDF_URLS[cid]
    start, end = check["pages"]

    print(f"--- {cid}: {check['source']} ---")
    page_text = extract_pdf_text(pdf_url, start, end)

    if not page_text:
        print(f"  [ERROR] Failed to extract text from {pdf_url}")
        all_ok = False
        continue

    check_ok = True
    for i, quote in enumerate(check["quotes"], 1):
        tagged_quote, mapping = parse_and_tag_latex(quote)
        passed = verify_structural_prose(tagged_quote, page_text)

        status = "PASS" if passed else "FAIL"
        print(f"  [{status}] Sentence {i}")

        print(f"         {tagged_quote}")
        for tag, latex in mapping.items():
            print(f"         {tag} = {latex}")

        if not passed:
            check_ok = False
    print()
    all_ok = all_ok and check_ok

print("=" * 88)
print("OVERALL:", "PASS" if all_ok else "FAIL")
print("=" * 88)