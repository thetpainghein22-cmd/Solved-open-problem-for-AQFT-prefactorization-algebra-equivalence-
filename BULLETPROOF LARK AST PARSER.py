# ===========================================================================
# CELL 3: BULLETPROOF LARK AST PARSER (DETERMINISTIC PRE-PROCESSING)
# ===========================================================================
!pip install lark -q
import re
from lark import Lark, Transformer, Token, Tree

FORMALIZED_MATH_INPUTS = {
    "C1": r"\(\operatorname{HomotopicallyDiscrete}(L_{W_M}\mathrm{tP}_M) \implies \operatorname{IsQuillenEquiv}(L_M\Phi_M)\)",
    "C2": r"\(\mathrm{AQFT}^{\mathrm{add}} \xrightarrow{\mathrm{f.f.}} \mathrm{AQFT}\)",
    "C3": r"\(\mathrm{Qft}^h_S(C^{\perp}) \rightleftarrows L_S\mathrm{Qft}(C^{\perp})\)",
    "C4": r"\(L_S\mathrm{Qft}(C^{\perp}) \to L_S\mathcal{O}_C^{\perp}\)",
    "C5a": r"\(\mathrm{AQFT} \to \mathrm{tPFA}\)",
    "C5b": r"\(\operatorname{IsAQFT}(\mathrm{AQFT}^{\mathrm{add}})\)",
    "C6": r"\(FQFT_m = \operatorname{Alg}(\tau_{LB}^{op})\)",
    "C7": r"\(\operatorname{HomotopicallyDiscrete}(\operatorname{Alg}(\tau_{LB}^{op}))\)",
    "C9": r"\(AQFT_m^{W,\mathrm{add}} \simeq FQFT_m^{W,\mathrm{add}}\)"
}

def clean_math(latex_str):
    """
    Strips all MathJax/LaTeX delimiters and pads operators with spaces.
    This guarantees Lark's Lexer can easily isolate structural tokens
    without relying on greedy regex fallback hacks.
    """
    s = latex_str.replace('$', '').replace(r'\(', '').replace(r'\)', '').replace(r'\[', '').replace(r'\]', '')

    operators = [
        r"\operatorname{HomotopicallyDiscrete}", r"\operatorname{IsQuillenEquiv}", r"\operatorname{IsAQFT}",
        r"\implies", r"\xrightarrow{\mathrm{f.f.}}", r"\rightleftarrows", r"\to", r"\simeq", "=", "(", ")"
    ]
    for op in operators:
        s = s.replace(op, f" {op} ")
    return s.strip()

# Now the grammar can be perfectly strict and simple.
AUTOMATED_GRAMMAR = r"""
start: statement

statement: HOM_DISCRETE LPAR term RPAR IMPLIES IS_QUILLEN LPAR term RPAR -> implies
         | term FF term -> full_faithful
         | term ADJ term -> quillen_adj
         | term TO term -> functor_map
         | IS_AQFT LPAR term RPAR -> is_aqft
         | term EQ term -> equality
         | HOM_DISCRETE LPAR term RPAR -> hom_discrete
         | term EQUIV term -> cat_equiv

term: term_item+
term_item: CHAR+ | LPAR term RPAR

HOM_DISCRETE.2: "\\operatorname{HomotopicallyDiscrete}"
IS_QUILLEN.2:   "\\operatorname{IsQuillenEquiv}"
IS_AQFT.2:      "\\operatorname{IsAQFT}"
IMPLIES.2:      "\\implies"
FF.2:           "\\xrightarrow{\\mathrm{f.f.}}"
ADJ.2:          "\\rightleftarrows"
TO.2:           "\\to"
EQUIV.2:        "\\simeq"
EQ.2:           "="
LPAR.2:         "("
RPAR.2:         ")"

# CHAR matches anything that isn't space or parentheses.
CHAR.1: /[^\s()]+/

%import common.WS
%ignore WS
"""

class ASTExtractor(Transformer):
    def implies(self, c):       return ("IMPLIES", self._flat(c[2]), self._flat(c[7]))
    def full_faithful(self, c): return ("FULL_FAITHFUL", self._flat(c[0]), self._flat(c[2]))
    def quillen_adj(self, c):   return ("QUILLEN_ADJ", self._flat(c[0]), self._flat(c[2]))
    def functor_map(self, c):   return ("FUNCTOR_MAP", self._flat(c[0]), self._flat(c[2]))
    def is_aqft(self, c):       return ("IS_AQFT", self._flat(c[2]))
    def equality(self, c):      return ("EQUALS", self._flat(c[0]), self._flat(c[2]))
    def hom_discrete(self, c):  return ("HOM_DISCRETE", self._flat(c[2]))
    def cat_equiv(self, c):     return ("CAT_EQUIV", self._flat(c[0]), self._flat(c[2]))

    def _flat(self, node):
        """Recursively reconstructs the tree, ignoring lexer padding spaces."""
        res = []
        def visit(n):
            if isinstance(n, Token):
                res.append(n.value)
            elif isinstance(n, Tree):
                for child in n.children:
                    visit(child)
            elif isinstance(n, list):
                for child in n:
                    visit(child)
        visit(node)
        return "".join(res)

lark_parser = Lark(AUTOMATED_GRAMMAR, parser='lalr')
extractor = ASTExtractor()
PARSED_AST_MAP = {}

print("=" * 80)
print("CELL 3: EXECUTING LARK AST PARSER")
print("=" * 80 + "\n")

all_c3_ok = True
for ax_id, raw_latex in FORMALIZED_MATH_INPUTS.items():
    clean_latex = clean_math(raw_latex)
    try:
        tree = lark_parser.parse(clean_latex)
        ast_tuple = extractor.transform(tree)
        PARSED_AST_MAP[ax_id] = ast_tuple
        print(f"[{ax_id}] PASS -> AST Extracted: {ast_tuple}")
    except Exception as e:
        print(f"[{ax_id}] FAIL -> {e}")
        all_c3_ok = False

print("\n" + "=" * 80)
print("CELL 3 RESULT:", "PASS" if all_c3_ok else "FAIL")
print("=" * 80)