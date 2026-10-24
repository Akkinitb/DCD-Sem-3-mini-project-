"""
Boolean Expression Simplifier  -  Streamlit dashboard
Digital Circuit Design (DCD) assignment

Features
  * Accepts expressions like  AB + A'C + BC ,  (A+B)(A'+C) ,  A xor B ,  !A & (B | C)
  * Minimal SOP and POS forms (Quine-McCluskey, via SymPy)
  * Truth table, minterm / maxterm lists, Karnaugh map (2-4 variables)
  * Step-by-step Quine-McCluskey working with prime implicants
  * Gate-level circuit diagrams (original vs simplified) + gate / literal savings
  * Personalised output using the user's name, downloadable report, history
"""

import html
import itertools
from datetime import datetime

import pandas as pd
import streamlit as st
from sympy import And, Not, Or, Symbol, Xor, false, preorder_traversal, true
from sympy.logic.boolalg import POSform, SOPform

MAX_VARS = 8

# ----------------------------------------------------------------------------
# Page setup + styling
# ----------------------------------------------------------------------------
st.set_page_config(
    page_title="Boolean Simplifier | DCD Dashboard",
    page_icon="⚡",
    layout="wide",
)

st.markdown(
    """
<style>
.hero {
    background: linear-gradient(135deg, #0ea5e9 0%, #6366f1 55%, #a855f7 100%);
    padding: 1.5rem 2rem; border-radius: 18px; color: white; margin-bottom: 1.2rem;
}
.hero h1 { margin: 0; font-size: 2rem; color: white; }
.hero p  { margin: .35rem 0 0; opacity: .93; font-size: 1.02rem; }
.card {
    background: rgba(148,163,184,.10); border: 1px solid rgba(148,163,184,.28);
    border-radius: 16px; padding: 1rem 1.3rem; margin-bottom: .8rem;
}
.card.primary { border: 1.5px solid #38bdf8; background: rgba(56,189,248,.10); }
.card .tag { font-size: .78rem; letter-spacing: .08em; text-transform: uppercase; opacity: .75; }
.expr {
    font-family: ui-monospace, "JetBrains Mono", Menlo, Consolas, monospace;
    font-size: 1.65rem; font-weight: 600; word-break: break-word; margin-top: .2rem;
}
.badge-ok  { color: #10b981; font-weight: 600; }
.badge-bad { color: #ef4444; font-weight: 600; }
div[data-testid="stMetric"] {
    background: rgba(148,163,184,.10); border: 1px solid rgba(148,163,184,.25);
    padding: .8rem 1rem; border-radius: 14px;
}
table.kmap { border-collapse: collapse; margin: .5rem auto 1rem; }
table.kmap th, table.kmap td {
    border: 1px solid rgba(148,163,184,.45); width: 74px; height: 62px;
    text-align: center; position: relative; font-family: ui-monospace, Menlo, monospace;
}
table.kmap th { background: rgba(99,102,241,.22); font-size: .95rem; }
table.kmap td.one  { background: rgba(16,185,129,.38); font-weight: 700; font-size: 1.3rem; }
table.kmap td.zero { opacity: .75; font-size: 1.1rem; }
table.kmap td span { position: absolute; top: 2px; left: 5px; font-size: .62rem; opacity: .65; font-weight: 400; }
</style>
""",
    unsafe_allow_html=True,
)


# ----------------------------------------------------------------------------
# Parsing  (tokenizer + recursive-descent parser -> SymPy boolean expression)
# ----------------------------------------------------------------------------
class ParseError(Exception):
    pass


KEYWORDS = {"AND": "AND", "OR": "OR", "NOT": "NOT", "XOR": "XOR"}
SYMBOL_TOKENS = {
    "+": "OR", "|": "OR", "∨": "OR",
    ".": "AND", "*": "AND", "&": "AND", "·": "AND", "∧": "AND",
    "^": "XOR", "⊕": "XOR",
    "!": "NOT", "~": "NOT", "¬": "NOT",
    "'": "PRIME", "’": "PRIME",
    "(": "LPAREN", ")": "RPAREN",
}


def tokenize(text):
    tokens, i = [], 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c.isalpha():
            j = i
            while j < len(text) and text[j].isalpha():
                j += 1
            word = text[i:j]
            if word.upper() in KEYWORDS:
                tokens.append((KEYWORDS[word.upper()], word))
            else:  # every letter is its own variable, so "ABC" means A.B.C
                tokens.extend(("VAR", ch.upper()) for ch in word)
            i = j
        elif c in "01":
            tokens.append(("CONST", c))
            i += 1
        elif c in SYMBOL_TOKENS:
            tokens.append((SYMBOL_TOKENS[c], c))
            i += 1
        else:
            raise ParseError(f"Unsupported character '{c}'.")
    return tokens


class Parser:
    """
    Precedence (high -> low):  NOT  >  AND (explicit or implicit)  >  XOR  >  OR
    """

    def __init__(self, tokens):
        self.t, self.i = tokens, 0
        self.vars, self.var_count = set(), 0

    def peek(self):
        return self.t[self.i][0] if self.i < len(self.t) else None

    def eat(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def parse(self):
        if not self.t:
            raise ParseError("Please enter a Boolean expression.")
        node = self.expr()
        if self.i < len(self.t):
            raise ParseError(f"Unexpected '{self.t[self.i][1]}' in the expression.")
        return node

    def expr(self):
        node = self.xor()
        while self.peek() == "OR":
            self.eat()
            node = Or(node, self.xor())
        return node

    def xor(self):
        node = self.term()
        while self.peek() == "XOR":
            self.eat()
            node = Xor(node, self.term())
        return node

    def term(self):
        node = self.unary()
        while True:
            k = self.peek()
            if k == "AND":
                self.eat()
                node = And(node, self.unary())
            elif k in ("VAR", "CONST", "LPAREN", "NOT"):  # implicit AND:  AB, A(B+C)
                node = And(node, self.unary())
            else:
                return node

    def unary(self):
        if self.peek() == "NOT":
            self.eat()
            return Not(self.unary())
        return self.postfix()

    def postfix(self):
        node = self.primary()
        while self.peek() == "PRIME":  # A'  or  (A+B)'
            self.eat()
            node = Not(node)
        return node

    def primary(self):
        k = self.peek()
        if k == "VAR":
            name = self.eat()[1]
            self.vars.add(name)
            self.var_count += 1
            return Symbol(name)
        if k == "CONST":
            return true if self.eat()[1] == "1" else false
        if k == "LPAREN":
            self.eat()
            node = self.expr()
            if self.peek() != "RPAREN":
                raise ParseError("Missing closing parenthesis ')'.")
            self.eat()
            return node
        if k is None:
            raise ParseError("The expression ended unexpectedly.")
        raise ParseError(f"Unexpected '{self.t[self.i][1]}' in the expression.")


def parse_expression(text):
    p = Parser(tokenize(text))
    expr = p.parse()
    return expr, sorted(p.vars), p.var_count


# ----------------------------------------------------------------------------
# Boolean helpers
# ----------------------------------------------------------------------------
def evaluate(expr, variables):
    """Truth-table output column; row i = minterm i (first variable is the MSB)."""
    syms = [Symbol(v) for v in variables]
    out = []
    for bits in itertools.product((False, True), repeat=len(syms)):
        sub = {s: (true if b else false) for s, b in zip(syms, bits)}
        out.append(int(bool(expr.xreplace(sub))))
    return out


def minimise(variables, outputs):
    """Minimal SOP and POS (Quine-McCluskey inside SymPy)."""
    if all(outputs):
        return true, true
    if not any(outputs):
        return false, false
    syms = [Symbol(v) for v in variables]
    minterms = [i for i, o in enumerate(outputs) if o]
    return SOPform(syms, minterms), POSform(syms, minterms)


def _key(s):
    return (s.replace("(", "").replace(")", "").replace("'", ""), s)


def fmt(e):
    """SymPy expression -> textbook notation  (A'B + C, (A + B')(C + D), ...)."""
    if e is true:
        return "1"
    if e is false:
        return "0"
    if isinstance(e, Symbol):
        return e.name
    if isinstance(e, Not):
        a = e.args[0]
        return a.name + "'" if isinstance(a, Symbol) else f"({fmt(a)})'"
    if isinstance(e, And):
        parts = [f"({fmt(a)})" if isinstance(a, (Or, Xor)) else fmt(a) for a in e.args]
        return "".join(sorted(parts, key=_key))
    if isinstance(e, Or):
        parts = [f"({fmt(a)})" if isinstance(a, Xor) else fmt(a) for a in e.args]
        return " + ".join(sorted(parts, key=_key))
    if isinstance(e, Xor):
        parts = [f"({fmt(a)})" if isinstance(a, Or) else fmt(a) for a in e.args]
        return " ⊕ ".join(sorted(parts, key=_key))
    return str(e)


def literal_count(expr):
    return sum(1 for a in preorder_traversal(expr) if isinstance(a, Symbol))


def group_cover(expr, variables, form):
    """For the K-map legend: which cells does each term / clause cover?"""
    if expr is true or expr is false:
        return []
    if form == "SOP":
        parts = list(expr.args) if isinstance(expr, Or) else [expr]
    else:
        parts = list(expr.args) if isinstance(expr, And) else [expr]
    rows = []
    for p in parts:
        vals = evaluate(p, variables)
        want = 1 if form == "SOP" else 0
        idx = [i for i, v in enumerate(vals) if v == want]
        label = fmt(p) if form == "SOP" else f"({fmt(p)})"
        rows.append((label, idx))
    return sorted(rows, key=lambda r: r[0])


# ----------------------------------------------------------------------------
# Quine-McCluskey (for the "Working" tab)
# ----------------------------------------------------------------------------
def quine_mccluskey(minterms, n):
    current = {format(m, f"0{n}b"): {m} for m in minterms}
    stages, primes = [], {}
    while current:
        stages.append(current)
        used, nxt = set(), {}
        for (a, ca), (b, cb) in itertools.combinations(list(current.items()), 2):
            diff = [k for k in range(n) if a[k] != b[k]]
            if len(diff) == 1 and "-" not in (a[diff[0]], b[diff[0]]):
                k = diff[0]
                nxt[a[:k] + "-" + a[k + 1:]] = ca | cb
                used.update((a, b))
        for term, cov in current.items():
            if term not in used:
                primes[term] = cov
        current = nxt
    essential = set()
    for m in minterms:
        owners = [p for p, c in primes.items() if m in c]
        if len(owners) == 1:
            essential.add(owners[0])
    return stages, primes, essential


def term_to_expr(term, variables, pos=False):
    lits = []
    for ch, v in zip(term, variables):
        if ch == "-":
            continue
        if pos:
            lits.append(v if ch == "0" else v + "'")
        else:
            lits.append(v if ch == "1" else v + "'")
    if not lits:
        return "0" if pos else "1"
    return "(" + " + ".join(lits) + ")" if pos else "".join(lits)


# ----------------------------------------------------------------------------
# Visuals: Karnaugh map + gate-level circuit
# ----------------------------------------------------------------------------
GRAY = {1: ["0", "1"], 2: ["00", "01", "11", "10"]}


def kmap_html(variables, outputs):
    n = len(variables)
    rv = n // 2
    row_vars, col_vars = variables[:rv], variables[rv:]
    rows, cols = GRAY[rv], GRAY[n - rv]
    head = "".join(f"<th>{c}</th>" for c in cols)
    h = (
        f"<table class='kmap'><tr><th>{''.join(row_vars)} \\ {''.join(col_vars)}</th>{head}</tr>"
    )
    for r in rows:
        h += f"<tr><th>{r}</th>"
        for c in cols:
            idx = int(r + c, 2)
            v = outputs[idx]
            h += f"<td class='{'one' if v else 'zero'}'><span>m{idx}</span>{v}</td>"
        h += "</tr>"
    return h + "</table>"


def circuit_dot(expr, label="F"):
    colors = {"AND": "#0ea5e9", "OR": "#10b981", "NOT": "#f59e0b", "XOR": "#a855f7"}
    lines = [
        "digraph G {", "rankdir=LR;", 'bgcolor="transparent";', "nodesep=0.35;",
        'node [fontname="Helvetica", fontcolor="white"];', 'edge [color="#94a3b8"];',
    ]
    memo, inputs, counter, gates = {}, [], [0], [0]

    def visit(e):
        if e in memo:
            return memo[e]
        if isinstance(e, Symbol):
            nid = f"in_{e.name}"
            inputs.append(nid)
            lines.append(
                f'{nid} [label="{e.name}", shape=circle, style=filled, fillcolor="#334155", color="#64748b"];'
            )
        elif e is true or e is false:
            counter[0] += 1
            nid = f"c{counter[0]}"
            lines.append(
                f'{nid} [label="{1 if e is true else 0}", shape=square, style=filled, fillcolor="#334155", color="#64748b"];'
            )
        else:
            kind = e.func.__name__.upper()
            kids = [visit(a) for a in e.args]
            counter[0] += 1
            nid = f"g{counter[0]}"
            col = colors.get(kind, "#64748b")
            lines.append(
                f'{nid} [label="{kind}", shape=box, style="rounded,filled", fillcolor="{col}", color="{col}"];'
            )
            lines.extend(f"{k} -> {nid};" for k in kids)
            gates[0] += 1
        memo[e] = nid
        return nid

    root = visit(expr)
    lines.append(
        f'out [label="{label}", shape=doublecircle, style=filled, fillcolor="#e11d48", color="#e11d48"];'
    )
    lines.append(f"{root} -> out;")
    if inputs:
        lines.append("{rank=same; " + " ".join(inputs) + "}")
    lines.append("}")
    return "\n".join(lines), gates[0]


# ----------------------------------------------------------------------------
# Session state + sidebar
# ----------------------------------------------------------------------------
DEFAULT_EXPR = "AB + A'C + BC"
EXAMPLES = {
    "A'B + AB' + AB": "A'B + AB' + AB",
    "AB + A'C + BC  (consensus)": "AB + A'C + BC",
    "(A + B)(A + C)": "(A + B)(A + C)",
    "A'B'C + A'BC + AB'C + ABC": "A'B'C + A'BC + AB'C + ABC",
    "(AB)' + A'B + AB'": "(AB)' + A'B + AB'",
    "A ⊕ B ⊕ C": "A xor B xor C",
    "ABCD + ABC'D + AB'CD + A'BCD": "ABCD + ABC'D + AB'CD + A'BCD",
}

st.session_state.setdefault("expr_input", DEFAULT_EXPR)
st.session_state.setdefault("active_expr", DEFAULT_EXPR)
st.session_state.setdefault("history", [])
st.session_state.setdefault("last_logged", None)


def load_example(e):
    st.session_state.expr_input = e
    st.session_state.active_expr = e


with st.sidebar:
    st.markdown("## ⚡ Control Panel")
    user_name = st.text_input("👤 Your name", placeholder="e.g. Akshay").strip()
    form_choice = st.radio(
        "Preferred output form",
        ["Sum of Products (SOP)", "Product of Sums (POS)"],
        help="Used for the headline result, K-map groups, Q-M working and circuit.",
    )
    st.markdown("---")
    st.markdown("**Quick examples**")
    for i, (label, ex) in enumerate(EXAMPLES.items()):
        st.button(label, key=f"ex{i}", on_click=load_example, args=(ex,), width="stretch")
    st.markdown("---")
    with st.expander("📖 Input syntax guide"):
        st.markdown(
            """
| Operation | You can type |
|---|---|
| AND | `AB`, `A.B`, `A*B`, `A&B`, `A and B` |
| OR | `A+B`, `A\\|B`, `A or B` |
| NOT | `A'`, `!A`, `~A`, `not A`, `(A+B)'` |
| XOR | `A^B`, `A⊕B`, `A xor B` |
| Constants | `0`, `1` |

Each letter is one variable (case-insensitive), so `ABC` = A·B·C.  
Precedence: NOT › AND › XOR › OR.  Up to **8 variables**.
"""
        )

use_sop = form_choice.startswith("SOP")
form_key = "SOP" if use_sop else "POS"

# ----------------------------------------------------------------------------
# Header + input
# ----------------------------------------------------------------------------
greeting = f"Hello, {html.escape(user_name)}! 👋" if user_name else "Hello there! 👋"
sub = (
    "Enter a Boolean expression below and I'll minimise it for you."
    if user_name
    else "Add your name in the sidebar to personalise your results, then enter an expression."
)
st.markdown(
    f"""<div class="hero"><h1>⚡ Boolean Expression Simplifier</h1>
    <p>{greeting} {sub}</p></div>""",
    unsafe_allow_html=True,
)

with st.form("input_form"):
    c1, c2 = st.columns([6, 1])
    c1.text_input(
        "Boolean expression",
        key="expr_input",
        placeholder="e.g.  AB + A'C + BC     or     (A + B)(A' + C)",
        label_visibility="collapsed",
    )
    submitted = c2.form_submit_button("Simplify ⚡", type="primary", width="stretch")
if submitted:
    st.session_state.active_expr = st.session_state.expr_input

text = st.session_state.active_expr

# ----------------------------------------------------------------------------
# Compute
# ----------------------------------------------------------------------------
try:
    parsed, variables, orig_literals = parse_expression(text)
except ParseError as err:
    st.error(f"⚠️ {err}")
    st.stop()
except Exception:
    st.error("⚠️ Couldn't understand that expression. Check the syntax guide in the sidebar.")
    st.stop()

if len(variables) > MAX_VARS:
    st.error(f"⚠️ Please use at most {MAX_VARS} variables (you used {len(variables)}).")
    st.stop()

n = len(variables)
with st.spinner("Simplifying..."):
    outputs = evaluate(parsed, variables)
    sop, pos = minimise(variables, outputs)
    primary = sop if use_sop else pos
    verified = evaluate(sop, variables) == outputs and evaluate(pos, variables) == outputs

minterms = [i for i, o in enumerate(outputs) if o]
maxterms = [i for i, o in enumerate(outputs) if not o]
dot_orig, gates_orig = circuit_dot(parsed)
dot_simp, gates_simp = circuit_dot(primary)
lits_after = literal_count(primary)
saved = max(orig_literals - lits_after, 0)
pct = round(100 * saved / orig_literals) if orig_literals else 0

# History log
if st.session_state.last_logged != text:
    st.session_state.last_logged = text
    st.session_state.history.insert(
        0,
        {
            "Time": datetime.now().strftime("%H:%M:%S"),
            "Input": text,
            "SOP": fmt(sop),
            "POS": fmt(pos),
        },
    )

# ----------------------------------------------------------------------------
# Dashboard
# ----------------------------------------------------------------------------
m1, m2, m3, m4, m5 = st.columns(5)
m1.metric("Variables", n)
m2.metric("Minterms (1s)", len(minterms))
m3.metric("Literals", lits_after, delta=lits_after - orig_literals, delta_color="inverse")
m4.metric("Gates", gates_simp, delta=gates_simp - gates_orig, delta_color="inverse")
m5.metric("Literals saved", f"{pct}%")

tab_res, tab_tt, tab_km, tab_qm, tab_ckt, tab_hist = st.tabs(
    ["✅ Result", "📊 Truth table", "🗺️ K-map", "🧮 Q-M working", "🔌 Circuit", "🕘 History"]
)

# ---- Result -----------------------------------------------------------------
with tab_res:
    who = f"{html.escape(user_name)}, here" if user_name else "Here"
    st.markdown(f"#### {who} is your simplified expression")
    st.caption(f"Input: `{text}`   ·   interpreted as: `{fmt(parsed)}`")

    for label, expr, is_main in (
        ("Minimal Sum of Products (SOP)", sop, use_sop),
        ("Minimal Product of Sums (POS)", pos, not use_sop),
    ):
        st.markdown(
            f"""<div class="card {'primary' if is_main else ''}">
            <div class="tag">{label}{' · selected' if is_main else ''}</div>
            <div class="expr">F = {html.escape(fmt(expr))}</div></div>""",
            unsafe_allow_html=True,
        )

    if verified:
        st.markdown(
            "<span class='badge-ok'>✔ Verified:</span> the simplified forms match the original "
            f"expression on all {2 ** n} input combinations.",
            unsafe_allow_html=True,
        )
    else:
        st.markdown("<span class='badge-bad'>✖ Verification failed.</span>", unsafe_allow_html=True)

    if n:
        sigma = ", ".join(map(str, minterms)) or "—"
        pi = ", ".join(map(str, maxterms)) or "—"
        st.markdown(
            f"**Canonical form**  \nF({', '.join(variables)}) = Σm({sigma})  =  ΠM({pi})"
        )
    st.markdown(
        f"**Cost:** {orig_literals} literals → **{lits_after}** "
        f"({'saved ' + str(saved) + ' literals, ' + str(pct) + '% reduction' if saved else 'already minimal'})."
    )

    report = f"""BOOLEAN EXPRESSION SIMPLIFIER - REPORT
Prepared for : {user_name or 'N/A'}
Date         : {datetime.now():%d %b %Y, %H:%M}

Input expression : {text}
Variables        : {', '.join(variables) or 'none'}
Minimal SOP      : F = {fmt(sop)}
Minimal POS      : F = {fmt(pos)}
Minterms         : {minterms}
Maxterms         : {maxterms}
Literals         : {orig_literals} -> {lits_after}
Verified         : {verified}
"""
    st.download_button("⬇️ Download report (.txt)", report, file_name="simplification_report.txt")

# ---- Truth table --------------------------------------------------------------
with tab_tt:
    if n == 0:
        st.info(f"The expression is the constant **{outputs[0]}**.")
    else:
        rows = list(itertools.product((0, 1), repeat=n))
        df = pd.DataFrame(rows, columns=variables)
        df.insert(0, "m", range(len(rows)))
        df["F (original)"] = outputs
        df["F (simplified)"] = evaluate(primary, variables)

        def hilite(col):
            return ["background-color: rgba(16,185,129,.35); font-weight:700" if v == 1 else "" for v in col]

        st.dataframe(
            df.style.apply(hilite, subset=["F (original)", "F (simplified)"]),
            hide_index=True,
            width="stretch",
            height=min(40 + 35 * len(df), 520),
        )
        st.caption("Both output columns are identical, which confirms the simplification is correct.")

# ---- K-map -----------------------------------------------------------------------
with tab_km:
    if 2 <= n <= 4:
        st.markdown(kmap_html(variables, outputs), unsafe_allow_html=True)
        st.caption("Rows/columns use Gray-code order so neighbouring cells differ by one variable.")
        groups = group_cover(primary, variables, form_key)
        if groups:
            what = "1-cells covered by each product term" if use_sop else "0-cells covered by each sum clause"
            st.markdown(f"**{what} ({form_key}):**")
            st.dataframe(
                pd.DataFrame(
                    [{"Group": lab, "Cells": ", ".join(f"m{i}" for i in idx)} for lab, idx in groups]
                ),
                hide_index=True,
                width="stretch",
            )
    else:
        st.info("The K-map is available for 2 to 4 variables.")

# ---- Quine-McCluskey -----------------------------------------------------------------
with tab_qm:
    target = minterms if use_sop else maxterms
    if n == 0 or not target or n > 6:
        st.info(
            "Q-M working is shown for 1-6 variables when the function is not a constant."
            if n > 6 or n == 0
            else "The function is constant, so there is nothing to combine."
        )
    else:
        what = "minterms (1s)" if use_sop else "maxterms (0s)"
        st.markdown(
            f"Quine-McCluskey on the **{what}** to get the {form_key} form. "
            "Terms differing in exactly one bit are combined; `-` marks an eliminated variable."
        )
        stages, primes, essential = quine_mccluskey(target, n)
        for k, stage in enumerate(stages):
            title = "Individual terms" if k == 0 else f"Combined in groups of {2 ** k}"
            with st.expander(f"Column {k + 1}: {title}", expanded=(k == 0)):
                st.dataframe(
                    pd.DataFrame(
                        sorted(
                            (
                                {
                                    "Group (#1s)": t.count("1"),
                                    "Binary": t,
                                    "Covers": ", ".join(map(str, sorted(c))),
                                }
                                for t, c in stage.items()
                            ),
                            key=lambda r: (r["Group (#1s)"], r["Binary"]),
                        )
                    ),
                    hide_index=True,
                    width="stretch",
                )
        st.markdown("**Prime implicants**" if use_sop else "**Prime implicates**")
        st.dataframe(
            pd.DataFrame(
                [
                    {
                        "Binary": t,
                        "Term": term_to_expr(t, variables, pos=not use_sop),
                        "Covers": ", ".join(map(str, sorted(c))),
                        "Essential": "✔" if t in essential else "",
                    }
                    for t, c in sorted(primes.items())
                ]
            ),
            hide_index=True,
            width="stretch",
        )
        st.caption(
            "Essential terms are the only ones covering some cell and must appear in the answer; "
            "any remaining cells are covered with the fewest extra terms."
        )

# ---- Circuit ----------------------------------------------------------------------
with tab_ckt:
    left, right = st.columns(2)
    with left:
        st.markdown(f"**Original circuit**  ·  {gates_orig} gates, {orig_literals} literals")
        st.graphviz_chart(dot_orig, width="stretch")
    with right:
        st.markdown(f"**Simplified circuit ({form_key})**  ·  {gates_simp} gates, {lits_after} literals")
        st.graphviz_chart(dot_simp, width="stretch")
    st.caption("Multi-input AND / OR gates are drawn as single blocks; shared inputs are reused.")

# ---- History ----------------------------------------------------------------------------
with tab_hist:
    if st.session_state.history:
        st.dataframe(pd.DataFrame(st.session_state.history), hide_index=True, width="stretch")
        if st.button("Clear history"):
            st.session_state.history = []
            st.session_state.last_logged = None
            st.rerun()
    else:
        st.info("Nothing here yet.")

st.markdown("---")
st.caption("Built with Python · Streamlit · SymPy  |  DCD Assignment")
