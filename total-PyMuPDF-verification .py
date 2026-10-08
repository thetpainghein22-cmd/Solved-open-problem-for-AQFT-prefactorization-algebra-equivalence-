import re
import urllib.request
import html as html_lib
import tempfile
import os

import fitz  # PyMuPDF


# ============================================================
# PDF SOURCES
# ============================================================

PDF_URLS = {
    "C1": "https://arxiv.org/pdf/2412.07318v2.pdf",
    "C2": "https://arxiv.org/pdf/2412.07318v2.pdf",
    "C3": "https://arxiv.org/pdf/2107.14176v5.pdf",
    "C4": "https://arxiv.org/pdf/2107.14176v5.pdf",
    "C5": "https://arxiv.org/pdf/1903.03396v2.pdf",
    "C6": "https://arxiv.org/pdf/2504.15759v2.pdf",
    "C7": "https://arxiv.org/pdf/1210.0229v1.pdf",
    "C9": "https://arxiv.org/pdf/2504.15759v2.pdf",
    "C10": "https://arxiv.org/pdf/1707.03465v2.pdf",
    "PROBLEM_STATEMENT": "https://arxiv.org/pdf/2412.07318v2.pdf",
}


# ============================================================
# LITERATURE CITATIONS
# ============================================================

CHECKS = {
    "C1": {
        "pages": (35, 35),
        "source": "Benini--Carmona--Grant-Stuart--Schenkel, §5.2",
        "quotes": [
            r"""Use [Car23a, Theorem 3.13] to observe that Open Problem 5.6 would be solved if the composite multifunctor $L_M\Phi_M : \mathrm{tP}M \to \mathcal{O}M[W_M^{-1}]$ exhibits a homotopical localization of the spacetime-wise tPFA operad $\mathrm{tP}M$ over $\mathrm{Loc}{\mathrm{rc}}/M$ at the subset of 1-ary operations $W_M \subseteq \operatorname{Mor}1(\mathrm{tP}M)$ given by all Cauchy morphisms in $\mathrm{tP}M$.""",

            r"""Denoting by $L{W_M}\mathrm{tP}M$ such a homotopical localization as an operad in simplicial sets, this amounts to showing that the induced multifunctor $L{W_M}\mathrm{tP}M \to \mathcal{O}M[W_M^{-1}]$ is a weak equivalence of operads in simplicial sets.""",

            r"""A mild generalization of Theorem 3.3 entails that $L_M\Phi_M$ exhibits the ordinary localization of $\mathrm{tP}M$ at $W_M$, hence it suffices to show that all spaces of operations in $L{W_M}\mathrm{tP}M$ are discrete, i.e. they have vanishing higher homotopy groups $\pi{\geq 1}$.""",

            r"""Since homotopical localizations of operads are currently not yet well-developed and studied, we are uncertain if this approach will be successful.""",
        ],
    },

    "C2": {
        "pages": (9, 9),
        "source": "Benini--Carmona--Grant-Stuart--Schenkel, Proposition 2.8",
        "quotes": [
            r"""The restriction $(-)|^{\mathrm{rc}}:\mathbf{AQFT}^{\mathrm{add}}\xrightarrow{\mathrm{ff.}}\mathbf{AQFT}^{\mathrm{rc}}$ (2.10) of the functor (2.8) to the full subcategory $\mathbf{AQFT}^{\mathrm{add}}\subseteq \mathbf{AQFT}$ of additive AQFTs over Loc is fully faithful.""",
        ],
    },

    "C3": {
        "pages": (15, 15),
        "source": "Carmona, Theorem 3.13",
        "quotes": [
            r"""The homotopical localization morphism $\ell : \mathcal{O}C^{\perp} \to L_S\mathcal{O}C^{\perp}$ induces a Quillen equivalence $L_S\mathrm{Qft}(C^{\perp}) \rightleftarrows \mathrm{Qft}^h_S(C^{\perp})$.""",
        ],
    },

    "C4": {
        "pages": (14, 14),
        "source": "Carmona, paragraph preceding Proposition 3.9",
        "quotes": [
            r"""Since homotopy $S$-constant field theories are presented as algebras over the operad $L_S\mathcal{O}C^{\perp}$, the projective model structure on these algebras, which we denote appealingly by $\mathrm{Qft}^h_S(C^{\perp})$, presents the homotopy theory of those field theories.""",
        ],
    },

    "C5": {
        "pages": (19, 20),
        "source": "Benini--Perin--Schenkel, Remark 5.2",
        "quotes": [
            r"""Recall from [BSW17] that there exists a Set-valued colored operad $\mathcal{O}(\mathrm{Loc},\perp)$ whose category of $\mathcal{C}$-valued algebras is the category of algebraic quantum field theories, i.e. AQFT $= \operatorname{Alg}{\mathcal{O}(\mathrm{Loc},\perp)}(\mathcal{C})$.""",

            r"""We can also define a Set-valued colored operad $\mathcal{P}{\mathrm{Loc}}$ such that $\mathrm{tPFA}=\operatorname{Alg}{\mathcal{P}{\mathrm{Loc}}}(\mathcal{C})$.""",

            r"""By operadic left Kan extension, there exists an adjunction $\Phi! : \mathrm{tPFA} \rightleftarrows \mathrm{AQFT} : \Phi^\* = F$.""",
        ],
    },

    "C6": {
        "pages": (3, 16),
        "source": "Bunk--MacManus--Schenkel, Introduction, Definition 4.1(a), and Construction A.9",
        "quotes": [
            r"""This means that an FQFT is a multifunctor $F: \tau(\mathrm{LBop}m) \to \mathrm{Alg}{uAs}(T)$ and that a morphism between FQFTs is a multinatural transformation $\zeta : F \Rightarrow G : \tau(\mathrm{LBop}m) \to \mathrm{Alg}{uAs}(T)$.""",

            r"""In Section 3, we define our novel $m$-dimensional $globally hyperbolic Lorentzian bordism pseudo-operad \mathrm{LBop}m$ which describes $n-to-1$ bordisms as in $(1.1)$ (together with suitable collar regions) and their gluing.""",
            
            r"""the operad $\tau(\mathrm{LBop}m)$ which is obtained by applying the truncation 2-functor $\tau:\mathrm{PsOpfib} \to \mathrm{Op}(2,1)$ from Construction A.9 to the m-dimensional globally hyperbolic Lorentzian bordism pseudo-operad $\mathrm{LBop}m$ from Section 3.""",

            r"""It is important to stress that the truncated operad $\tau(\mathrm{LBop}m)$ remembers much of the rich geometric structure of the pseudo-operad $\mathrm{LBop}m$. In particular, its objects and operations keep track of the collar regions around Cauchy surfaces and bordisms, which are crucial for a well-defined operadic composition.""",
        ],
    },

    "C7": {
        "pages": (2, 2),
        "source": "Harpaz, p. 2",
        "quotes": [
            r"""Let $Bun_0$ be the 0-dimensional unoriented cobordism category, i.e. the objects of $Bun_0$ are 0-dimensional closed manifolds (or equivalently, finite sets) and the morphisms are diffeomorphisms (or equivalently, isomorphisms of finite sets).""",

            r"""Note that $Bun_0$ is a (discrete) $\infty$groupoid.""",
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

    "C10": {
        "pages": (1, 1),
        "source": "Le Grignou, Introduction, p. 1",
        "quotes": [
            r"""For any dg operad $P$, the category of $P$-algebras admits a projective model structure whose weak equivalences are quasi-isomorphisms and whose fibrations are surjections.""",
        ],
    },

    "PROBLEM_STATEMENT": {
        "pages": (34, 34),
        "source": "Benini--Carmona--Grant-Stuart--Schenkel, Open Problem 5.6",
        "quotes": [
            r"""Open Problem 5.6. Prove that the composite right Quillen functor $(L{M}\Phi{M})^{\*}:\mathsf{HK}^{W}(M)\xrightarrow{L{M}^{\*}}\mathcal{L}{\widetilde{W}{M}}\mathsf{HK}(M)\xrightarrow{\Phi{M}^{}}\mathcal{L}{\widetilde{W}{M}}\mathsf{CG}(M)$ (5.8) from the projective model category $\mathsf{HK}^{W}(M)\simeq \mathsf{Alg}{\mathcal{O}{M}[W\_{M}^{-1}]}(\mathbf{Ch}{R})$ from Theorem 4.1 to the left Bousfield localized semi-model category $\mathcal{L}{\widetilde{W}\_{M}}\mathrm{CG}(M)$ from Theorem 4.4 is a right Quillen equivalence, for all objects $M\in \mathbf{Loc}^{\mathrm{rc}}$.""",
        ],
    },
}


# ============================================================
# NLAB CITATIONS
# ============================================================

# IMPORTANT:
# These are quoted from the current nLab prose.  Mathematical material is
# deliberately tagged as "notation number N" so that the verifier can ignore
# the notation while checking every non-mathematical word, space, and mark of
# punctuation in the statement.
NLAB_CONCEPTS = {
    "Quillen equivalence": {
        "url": "https://ncatlab.org/nlab/show/Quillen+equivalence",
        "quotes": [
            r"""A Quillen adjunction [notation number 1] is a Quillen equivalence if the following equivalent conditions are satisfied:
            The total left derived functor [notation number 2] is an equivalence of the homotopy categories;""",
        ],
    },

    "discrete category": {
        "url": "https://ncatlab.org/nlab/show/discrete+category",
        "quotes": [
            r"""A category is discrete if it is both a groupoid and a preorder. That is, every morphism should be invertible, any two parallel morphisms should be equal.""",
        ],
    },

    "Quillen adjunction": {
        "url": "https://ncatlab.org/nlab/show/Quillen+adjunction",
        "quotes": [
            r"""For [notation number 1] two model categories, a pair [notation number 2] [notation number 3] of adjoint functors (with [notation number 4] left adjoint and [notation number 5] right adjoint) is a Quillen adjunction if the following equivalent conditions are satisfied:""",
            r"""[notation number 6] preserves cofibrations and acyclic cofibrations;""",
            r"""[notation number 7] preserves fibrations and acyclic fibrations;""",
        ],
    },

}


# ============================================================
# UNICODE NORMALIZATION
# ============================================================

UNICODE_TRANS = str.maketrans({
    "–": "-",
    "—": "-",
    "−": "-",
    "’": "'",
    "‘": "'",
    "“": '"',
    "”": '"',
    "\u00a0": " ",
    "\u2009": " ",
    "\u202f": " ",
    "\u200b": "",
    "\ufeff": "",
})


def normalize(text):
    text = html_lib.unescape(text)

    text = (
        text
        .replace("ﬁ", "fi")
        .replace("ﬂ", "fl")
        .replace("ﬀ", "ff")
        .replace("ﬃ", "ffi")
        .replace("ﬄ", "ffl")
    )

    text = text.translate(UNICODE_TRANS)

    # Join words split across PDF line endings.
    text = re.sub(
        r"-\s*\n\s*",
        "",
        text,
    )

    # Normalize whitespace.
    text = re.sub(
        r"\s+",
        " ",
        text,
    )

    return text.strip()


# ============================================================
# DOWNLOAD
# ============================================================

def download_bytes(url):
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": (
                "Mozilla/5.0 "
                "(Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 "
                "(KHTML, like Gecko) "
                "Chrome/131.0 Safari/537.36"
            ),
        },
    )

    try:
        with urllib.request.urlopen(
            req,
            timeout=60,
        ) as resp:
            return resp.read()

    except Exception as e:
        print(
            f"Error fetching {url}: {e}"
        )
        return b""


# ============================================================
# PDF EXTRACTION
# ============================================================

def extract_pdf_text(
    url,
    start_page,
    end_page,
):
    data = download_bytes(url)

    if not data:
        return ""

    fd, path = tempfile.mkstemp(
        suffix=".pdf"
    )

    try:
        # Write the original PDF bytes unchanged.
        with os.fdopen(
            fd,
            "wb",
        ) as f:
            f.write(data)

        doc = fitz.open(path)

        text = ""

        for page in range(
            start_page - 1,
            end_page,
        ):
            if page < len(doc):
                text += (
                    doc[page].get_text(
                        "text"
                    )
                    + "\n"
                )

        doc.close()

        return normalize(text)

    except Exception as e:
        print(
            f"Error opening PDF {url}: {e}"
        )
        return ""

    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


# ============================================================
# NLAB PRINT-PAGE PDF EXTRACTION
# ============================================================

def nlab_print_url(show_url):
    """
    Convert an nLab show URL into the corresponding nLab Print URL.

    nLab explicitly recommends using the page's Print link when printing a
    page.  The verifier then converts that printable page to PDF and uses
    PyMuPDF to read the PDF text.
    """
    return show_url.replace(
        "/nlab/show/",
        "/nlab/print/",
        1,
    )


def html_to_pdf_bytes(
    html_bytes,
    base_url,
):
    """Convert the actual nLab printable HTML page to PDF bytes."""
    try:
        from weasyprint import HTML
    except ImportError as e:
        raise RuntimeError(
            "nLab verification requires WeasyPrint. "
            "Install it with: pip install weasyprint"
        ) from e

    fd_html, html_path = tempfile.mkstemp(
        suffix=".html"
    )
    fd_pdf, pdf_path = tempfile.mkstemp(
        suffix=".pdf"
    )

    try:
        with os.fdopen(
            fd_html,
            "wb",
        ) as f:
            f.write(html_bytes)

        os.close(fd_pdf)

        # The base URL is the nLab origin so the printable page can resolve
        # its own relative CSS/assets.  The verifier never inspects the HTML
        # text itself after this point.
        from weasyprint import HTML

        HTML(
            filename=html_path,
            base_url=base_url,
        ).write_pdf(pdf_path)

        with open(
            pdf_path,
            "rb",
        ) as f:
            return f.read()

    finally:
        for path in (
            html_path,
            pdf_path,
        ):
            try:
                os.unlink(path)
            except OSError:
                pass


def extract_nlab_text(
    show_url,
):
    """
    Read an nLab page through its actual Print endpoint, convert that exact
    printable page to PDF, and then extract ONLY the text that PyMuPDF reads.

    No GitHub markdown source and no DOM-text comparison is used for the
    verification itself.
    """
    print_url = nlab_print_url(show_url)

    html_bytes = download_bytes(
        print_url
    )

    if not html_bytes:
        return ""

    try:
        pdf_bytes = html_to_pdf_bytes(
            html_bytes,
            base_url="https://ncatlab.org/",
        )
    except Exception as e:
        print(
            f"Error converting nLab Print page {print_url} to PDF: {e}"
        )
        return ""

    if not pdf_bytes:
        return ""

    fd, path = tempfile.mkstemp(
        suffix=".pdf"
    )

    try:
        # These are the exact PDF bytes that PyMuPDF will inspect.
        with os.fdopen(
            fd,
            "wb",
        ) as f:
            f.write(pdf_bytes)

        doc = fitz.open(path)

        text = ""

        for page in doc:
            text += (
                page.get_text(
                    "text"
                )
                + "\n"
            )

        doc.close()

        return normalize(text)

    except Exception as e:
        print(
            f"Error extracting nLab Print PDF {print_url}: {e}"
        )
        return ""

    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


# ============================================================
# QUOTE MATCHING
# ============================================================

MATH_PATTERN = re.compile(
    r"\$\$.*?\$\$|\$.*?\$|\\\(.*?\\\)|\\\[.*?\\\]",
    re.DOTALL,
)

NOTATION_TAG_PATTERN = re.compile(
    r"\[notation number \d+\]",
    re.IGNORECASE,
)


def quote_to_pattern(
    quote,
):
    """
    Build a literal-text regex from the quotation.

    Two things are treated as notation placeholders:

      * source-style LaTeX/TeX math in the literature checks;
      * explicit [notation number N] tags in the nLab checks.

    Those spans are ignored.  Every other character is escaped and therefore
    must occur in the PyMuPDF-extracted text, in the same order, with only the
    documented normalization of whitespace/Unicode applied.
    """
    pieces = []
    last = 0

    combined = re.compile(
        rf"(?:{MATH_PATTERN.pattern})|(?:{NOTATION_TAG_PATTERN.pattern})",
        re.DOTALL,
    )

    for match in combined.finditer(
        quote
    ):
        prose = quote[
            last:match.start()
        ]

        if prose:
            pieces.append(
                re.escape(
                    normalize(prose)
                )
            )

        # Mathematical notation is intentionally not verified.
        pieces.append(
            r".*?"
        )

        last = match.end()

    prose = quote[
        last:
    ]

    if prose:
        pieces.append(
            re.escape(
                normalize(prose)
            )
        )

    # Spaces in quoted prose are allowed to be represented by any normalized
    # run of whitespace in PyMuPDF's extraction.
    pattern = "".join(
        pieces
    ).replace(
        r"\ ",
        r"\s+",
    )

    return pattern


def statement_exists(
    quote,
    source,
):
    """
    Check a statement against the normalized text PyMuPDF actually read.

    Mathematical notation is the only ignored region.  No semantic
    paraphrase, Markdown reconstruction, link-label expansion, or source-file
    comparison is performed here.
    """
    pattern = quote_to_pattern(
        quote
    )

    return (
        re.search(
            pattern,
            normalize(source),
            flags=re.DOTALL,
        )
        is not None
    )


# ============================================================
# DISPLAY QUOTATION
# ============================================================

def notation_display(quote):
    """
    Display each mathematical span as "notation number N".

    nLab quotations already carry explicit notation tags, so those tags are
    shown as-is (without brackets).  Literature quotations are numbered in
    order here.
    """
    counter = 0

    def replacement(match):
        nonlocal counter
        counter += 1
        return f"notation number {counter}"

    displayed = MATH_PATTERN.sub(
        replacement,
        quote,
    )

    def display_tag(match):
        return match.group(0)[1:-1]

    return NOTATION_TAG_PATTERN.sub(
        display_tag,
        displayed,
    )



# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":

    print("=" * 88)
    print(
        "STRUCTURAL TAGGING CITATION VERIFIER"
    )
    print("=" * 88)
    print()

    all_ok = True

    # ========================================================
    # LITERATURE
    # ========================================================

    print("=" * 88)
    print("LITERATURE VERIFICATION")
    print("=" * 88)
    print()

    for cid, check in CHECKS.items():

        print(
            f"--- {cid}: {check['source']} ---"
        )

        page_text = extract_pdf_text(
            PDF_URLS[cid],
            check["pages"][0],
            check["pages"][1],
        )

        if len(
            page_text.strip()
        ) < 100:

            print(
                f"  [FAIL] extracted only "
                f"{len(page_text)} characters"
            )

            all_ok = False
            continue

        check_ok = True

        for i, quote in enumerate(
            check["quotes"],
            1,
        ):

            passed = statement_exists(
                quote,
                page_text,
            )

            print(
                f"  [{'PASS' if passed else 'FAIL'}] "
                f"Statement {i}"
            )

            print(
                "      "
                + notation_display(
                    quote
                )
            )

            check_ok = (
                check_ok
                and passed
            )

        print()

        all_ok = (
            all_ok
            and check_ok
        )

    # ========================================================
    # NLAB
    # ========================================================

    print("=" * 88)
    print("NLAB STATEMENT VERIFICATION")
    print("=" * 88)
    print()

    for concept, data in (
        NLAB_CONCEPTS.items()
    ):

        print(
            f"--- {concept} ---"
        )

        print(
            f"    {data['url']}"
        )
        print(
            f"    Print: {nlab_print_url(data['url'])}"
        )

        # Verify the printable nLab page by running PyMuPDF on the PDF
        # produced from that printable page.  The matcher sees only the
        # resulting PyMuPDF text.
        page_text = extract_nlab_text(
            data["url"]
        )

        if len(
            page_text.strip()
        ) < 100:

            print(
                f"  [FAIL] PyMuPDF extracted only "
                f"{len(page_text)} characters"
            )

            all_ok = False
            continue

        check_ok = True

        for i, quote in enumerate(
            data["quotes"],
            1,
        ):

            passed = statement_exists(
                quote,
                page_text,
            )

            print(
                f"  [{'PASS' if passed else 'FAIL'}] "
                f"Statement {i}"
            )

            print(
                "      "
                + notation_display(
                    quote
                )
            )

            if not passed:
                # Show the exact normalized quotation expected by the
                # verifier.  The underlying comparison remains literal for
                # all non-notation text.
                print(
                    "      Expected (normalized):"
                )
                print(
                    "        "
                    + normalize(quote)
                )

                print(
                    "      PyMuPDF extraction length:"
                    f" {len(page_text)}"
                )

            check_ok = (
                check_ok
                and passed
            )

        print()

        all_ok = (
            all_ok
            and check_ok
        )

    print("=" * 88)
    print(
        "OVERALL RESULT:",
        "PASS" if all_ok else "FAIL"
    )
    print("=" * 88)

