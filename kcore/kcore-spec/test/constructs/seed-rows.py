"""Writes rows.toml's first version from the extracted key lists (.lake/constructs) and the
evidence that existed when it was written; run once, then rows.toml is edited, not regenerated.

Usage: python3 -I seed-rows.py KEYS_DIR LIBRARY_DIR KIMP_SOURCES KK_K OUT_TOML

A status is carried only where a recorded place gives it; anything else is `not-handled`:
  - findings/K-coverage.md (measured at kcore-reader 57f851ec), rows A.1 to A.3 for E2 and E4,
    Part B for E5 (through partb-sites.tsv), Part C for E6's hooks. Its statuses map as
    read -> supported, inert / inert (unread) -> inert, refused by decision -> refused,
    parameter -> parameter, not handled -> not-handled; a row "read / X" gives its first status.
    A row that K-coverage's dated note (2026-11-14) names as changed since is not carried.
  - E6, the library at this tree: a hooked declaration of a module in BuiltinData.modules is
    `supported` when FixedSignature.regHookNames has its hook (the registry interprets it),
    else `parameter`
    (Builtins.libParams); a hooked sort of such a module is `supported`. A hooked declaration of
    MInt, in any module, is `refused` (sort-parametric, KCORE-SPEC.md Q11; K-coverage Part C). Every other sentence of a
    module in BuiltinData.modules is read as that module's text (Builtins.lean): `supported`,
    lemmas `inert` (K-coverage Part B, "simplification equation"). A module outside
    BuiltinData.modules is refused `builtinText` with no recorded decision: `not-handled`.
  - E5: a site whose Part B rows all carry one status gets it; a site with rows of several
    statuses, or a changed row, is `not-handled` with the rows named.
Marks: `kimp` / `kore` are true when the row's construct occurs in kimp's text (K sources and
f2-examples/ref-kimp.kore) / in kcore-spec's kk/kk.k, false when the check ran and found none;
absent when no check was made for the row (E5, E7, E8, the generated E3 families, kk.k's
KORE-level lists E4 and E6, which need its kompiled text).
"""
import json, os, re, sys

keys_dir, lib, kimp_src, kk_k, out = sys.argv[1:6]


def keys(l):
    return [line.split("\t")[0] for line in open(os.path.join(keys_dir, f"{l}.keys")) if line.strip()]


def uses(nm, l):
    p = os.path.join(keys_dir, f"uses-{nm}.{l}")
    return {x.strip() for x in open(p)} if os.path.exists(p) else None


KC = "K-coverage.md"
CHANGED = "not carried: K-coverage's dated note names it as changed since 57f851ec"

# ---------------------------------------------------------------- the rows' K texts
def ktext(paths):
    t = "\n".join(open(p).read() for p in paths)
    t = re.sub(r"/\*.*?\*/", "", t, flags=re.S)
    return re.sub(r"//[^\n]*", "", t)


kimp_files = [os.path.join(kimp_src, f) for f in ("imp.k", "calc.k", "expr.k")]
KT = {"kimp": ktext(kimp_files), "kore": ktext([kk_k])}


def sentences(t):
    """(kind, text) for every sentence of a K text: syntax, rule, claim, context, configuration, module."""
    out, cur = [], None
    for l in t.split("\n"):
        m = re.match(r"\s*(syntax|rule|claim|context|configuration|module|imports|endmodule|requires)\b", l)
        if m:
            if cur: out.append(cur)
            cur = [m.group(1), l]
        elif cur:
            cur[1] += "\n" + l
    if cur: out.append(cur)
    return [(k, s) for k, s in out]


def trailing_atts(s):
    s = s.rstrip()
    if not s.endswith("]"): return []
    depth, i = 0, len(s) - 1
    while i >= 0:
        if s[i] == "]": depth += 1
        elif s[i] == "[":
            depth -= 1
            if depth == 0: break
        i -= 1
    body = s[i + 1:-1]
    if i <= 0 or not s[i - 1].isspace(): return []  # `M[K]`: a lookup, not an attribute list
    parts, depth, cur = [], 0, ""
    for c in body:
        if c == "(": depth += 1
        if c == ")": depth -= 1
        if c == "," and depth == 0: parts.append(cur); cur = ""
        else: cur += c
    parts.append(cur)
    parts = [p.strip() for p in parts if p.strip()]
    if not all(re.fullmatch(r"[a-z][\w.-]*(\(.*\))?", p, re.S) for p in parts): return []
    return [p.split("(")[0].strip() for p in parts]


def att_uses(t):
    """(attribute key, K class) pairs a K text writes: classes symbol/sort for syntax, rule for
    rules, claim, module, cell for configuration cells' properties (key=value)."""
    res = set()
    for kind, s in sentences(t):
        if kind == "syntax":
            for alt in re.split(r"\n\s*[|>]", s):
                for a in trailing_atts(alt): res.add((a, "syntax"))
        elif kind in ("rule", "context"):
            for a in trailing_atts(s): res.add((a, "rule"))
            if re.match(r"\s*(rule|context)\s+\[[\w-]+\]\s*:", s): res.add(("label", "rule"))
        elif kind == "claim":
            for a in trailing_atts(s): res.add((a, "claim"))
        elif kind == "module":
            m = re.match(r"\s*module\s+\S+\s*\[([^\]]*)\]", s)
            if m:
                for a in m.group(1).split(","): res.add((a.strip().split("(")[0], "module"))
        elif kind == "configuration":
            for k, v in re.findall(r"\b([\w-]+)=\"([^\"]*)\"", s): res.add((f"{k}={v}", "cell"))
    return res


E1_PAT = {
    "Require:kw:requires": r"^\s*requires\s+\"", "Require:node:Require": r"^\s*requires\s+\"",
    "Module:kw:module": r"^\s*module\b", "Module:kw:endmodule": r"^\s*endmodule\b",
    "Module:token:MODNAME": r"^\s*module\b", "Module:node:Module": r"^\s*module\b",
    "Import:kw:imports": r"^\s*imports\b", "Import:token:MODNAME": r"^\s*imports\b", "Import:node:Import": r"^\s*imports\b",
    "Import:token:IMPORTSPRIVATE": r"^\s*imports\s+private\b", "Import:token:IMPORTSPUBLIC": r"^\s*imports\s+public\b",
    "Sentence:kw:rule": r"^\s*rule\b", "Sentence:kw:claim": r"^\s*claim\b", "Sentence:kw:context": r"^\s*context\b",
    "Sentence:token:ALIAS": r"^\s*context\s+alias\b", "Sentence:kw:configuration": r"^\s*configuration\b",
    "Sentence:kw:syntax": r"^\s*syntax\b", "Sentence:node:Syntax": r"^\s*syntax\b", "Sentence:lit:::=": r"::=",
    "Sentence:lit:{": r"^\s*syntax\s*\{", "Sentence:lit:,": r"^\s*syntax\s*\{[^}]*,", "Sentence:lit:}": r"^\s*syntax\s*\{",
    "Sentence:lit:>": r"^\s*>\s|^\s*syntax\s+priority\b", "Sentence:lit:=": r"^\s*syntax\s+\S+\s*=\s*\S",
    "Sentence:node:SortSynonym": r"^\s*syntax\s+\S+\s*=\s*\S",
    "Sentence:kw:priority": r"^\s*syntax\s+priority\b", "Sentence:node:PriorityExtended": r"^\s*syntax\s+priority\b",
    "Sentence:node:PriorityBlockExtended": r"^\s*syntax\s+(priority|left|right|non-assoc)\b",
    "Sentence:kw:left": r"^\s*syntax\s+left\b", "Sentence:kw:right": r"^\s*syntax\s+right\b",
    "Sentence:kw:non-assoc": r"^\s*syntax\s+non-assoc\b", "Sentence:node:PriorityExtendedAssoc": r"^\s*syntax\s+(left|right|non-assoc)\b",
    "Sentence:kw:lexical": r"^\s*syntax\s+lexical\b", "Sentence:node:SyntaxLexical": r"^\s*syntax\s+lexical\b",
    "PriorityBlock:kw:left": r"(::=|\||>)\s*left\s*:", "PriorityBlock:kw:right": r"(::=|\||>)\s*right\s*:",
    "PriorityBlock:kw:non-assoc": r"(::=|\||>)\s*non-assoc\s*:", "PriorityBlock:lit::": r"(::=|\||>)\s*(left|right|non-assoc)\s*:",
    "PriorityBlock:lit:|": r"^\s*\|", "PriorityBlock:node:PriorityBlock": r"::=",
    "Production:node:Production": r"::=", "Production:node:Terminal": r"::=[^\n]*\"", "Production:node:NonTerminal": r"::=\s*[A-Z#]",
    "Production:token:LOWER_ID": r"(::=|\|)\s*[a-z][\w]*\(", "Production:lit:(": r"(::=|\|)\s*\w*\(",
    "Production:lit:,": r"(::=|\|)\s*\w*\([^)\n]*,", "Production:lit:)": r"(::=|\|)\s*\w*\(",
    "ProductionItem:kw:List": r"\bList\{", "ProductionItem:kw:NeList": r"\bNeList\{",
    "ProductionItem:lit:{": r"\b(Ne)?List\{", "ProductionItem:lit:,": r"\b(Ne)?List\{", "ProductionItem:lit:}": r"\b(Ne)?List\{",
    "ProductionItem:node:Terminal": r"::=[^\n]*\"", "ProductionItem:node:Lexical": r"\br\"",
    "ProductionItem:node:UserList": r"\b(Ne)?List\{",
    "Tag:token:KEY": r"\[[a-z][\w-]*", "Tag:lit:(": r"\[[^\]\n]*[a-z]\(", "Tag:lit:)": r"\[[^\]\n]*[a-z]\(",
}


def e3_used(key, t):
    rule_text = "\n".join(s for k, s in sentences(t) if k in ("rule", "claim", "context"))
    if key.startswith("generated:"): return None
    if key.startswith("KSEQ-SYMBOLIC:#KVariable::=r"):
        part = key.rsplit("#", 1)[1]
        pat = {"plain": r"\b[A-Z][A-Za-z0-9']*\b", "fresh-!": r"![A-Z]", "existential-?": r"\?[A-Z]",
               "set-@": r"@[A-Z]", "anonymous-_": r"(?<![\w#])_(?![\w])", "named-anonymous-_X": r"(?<![\w#])_[A-Z]"}[part]
        return re.search(pat, rule_text) is not None
    items = key.split("::=", 1)[1]
    terms = re.findall(r'"((?:[^"\\]|\\.)*)"', items)
    terms = [x for x in terms if x]
    if not terms or items.startswith('r"'): return None
    return all(x in rule_text for x in terms)


# ---------------------------------------------------------------- library data at this tree
fs = open(os.path.join(lib, "KcoreSpec/FixedSignature.lean")).read()
reg = fs[fs.index("def regHookNames"):]
reg = reg[:reg.index("]\n")]
REG = set(re.findall(r'"([A-Z]+\.[A-Za-z0-9_]+)"', reg))
bd = open(os.path.join(lib, "KcoreSpec/BuiltinData.lean")).read()
LIBMODS = set(re.findall(r'^  \("([A-Z0-9-]+)", "krust-builtin://', bd, re.M))
REGP = "FixedSignature.lean regHookNames"
LIBP = "BuiltinData.lean modules"

rows = {}


def row(l, k, status, evidence, note=None, **marks):
    r = {"status": status, "evidence": evidence}
    if note: r["note"] = note
    r.update({m: v for m, v in marks.items() if v is not None})
    rows.setdefault(l, {})[k] = r


# ---------------------------------------------------------------- E1
for k in keys("E1"):
    m = {nm: (re.search(E1_PAT[k], KT[nm], re.M) is not None) if k in E1_PAT else None for nm in KT}
    row("E1", k, "not-handled", "", kimp=m["kimp"], kore=m["kore"])

# ---------------------------------------------------------------- E2
# K-coverage A.3: (valname, classes it speaks of, status, row)
A3 = [
    ("SOURCE", ["any"], "supported", "A.3 Source, Location"), ("LOCATION", ["any"], "supported", "A.3 Source, Location"),
    ("UNIQUE_ID", ["any"], "supported", "A.3 UNIQUE'Unds'ID"),
    ("LABEL", ["rule", "equation", "simplification"], "supported", "A.3 label (axioms)"),
    ("PRIORITY", ["rule", "equation"], "supported", "A.3 priority (axioms)"),
    ("OWISE", ["rule", "equation"], "supported", "A.3 owise (rules; on equations read from the premise)"),
    ("SIMPLIFICATION", ["simplification"], "inert", "A.3 simplification (axioms), VISION D2"),
    ("CONCRETE", ["rule", "equation", "simplification"], "inert", "A.3 concrete, symbolic (axioms)"),
    ("SYMBOLIC", ["rule", "equation", "simplification"], "inert", "A.3 concrete, symbolic (axioms)"),
    ("NON_EXECUTABLE", ["rule", "equation", "simplification"], "not-handled", "A.3 non-executable"),
    ("PRESERVES_DEFINEDNESS", ["rule", "equation", "simplification"], "inert", "A.3 preserves-definedness, cool, ... (axioms)"),
    ("COOL", ["rule", "equation", "simplification"], "inert", "A.3 preserves-definedness, cool, ... (axioms)"),
    ("COOL_LIKE", ["any"], "inert", "A.3 preserves-definedness, cool, cool-like, ... (axioms)"),
    ("SMT_LEMMA", ["rule", "equation", "simplification"], "inert", "A.3 ..., smt-lemma, format (axioms)"),
    ("FORMAT", ["symbol"], "inert", "A.3 ..., format (axioms; rules: presentation)"),
    ("CONSTRUCTOR", ["symbol"], "supported", "A.3 constructor (symbols)"),
    ("FUNCTION", ["symbol"], "supported", "A.3 function (symbols)"),
    ("TOTAL", ["symbol"], "supported", "A.3 total / functional (symbols)"),
    ("FUNCTIONAL", ["symbol"], "supported", "A.3 total / functional (symbols)"),
    ("INJECTIVE", ["symbol"], "inert", "A.3 injective (symbols)"),
    ("CELL", ["symbol"], "supported", "A.3 cell (symbols)"),
    ("MACRO", ["symbol"], "inert", "A.3 macro, macro-rec, alias, alias-rec (symbols): unread macroUnused"),
    ("MACRO_REC", ["symbol"], "inert", "A.3 macro, macro-rec, alias, alias-rec (symbols): unread macroUnused"),
    ("ALIAS", ["symbol"], "inert", "A.3 macro, macro-rec, alias, alias-rec (symbols): unread macroUnused"),
    ("ALIAS_REC", ["symbol"], "inert", "A.3 macro, macro-rec, alias, alias-rec (symbols): unread macroUnused"),
    ("HOOK", ["symbol"], "supported", "A.3 hook (hooked symbols): read / parameter"),
    ("HOOK", ["sort"], "supported", "A.3 hook (hooked sorts)"),
    ("ELEMENT", ["symbol"], "supported", "A.3 element, unit, concat (collection sorts; kompile writes them on the hooked sort)"),
    ("UNIT", ["symbol"], "supported", "A.3 element, unit, concat (collection sorts; kompile writes them on the hooked sort)"),
    ("CONCAT", ["any"], "supported", "A.3 element, unit, concat (collection sorts)"),
    ("UPDATE", ["symbol"], "inert", "A.3 update (collection sorts)"),
    ("TOKEN", ["sort"], "not-handled", "A.3 token, hasDomainValues (user sorts)"),
    ("HAS_DOMAIN_VALUES", ["any"], "not-handled", "A.3 token, hasDomainValues (user sorts)"),
    ("IMPURE", ["symbol"], "inert", "A.3 anywhere, impure, ... (symbols)"),
    ("FRESH_GENERATOR", ["symbol"], "inert", "A.3 anywhere, impure, freshGenerator, ... (symbols)"),
    ("NO_EVALUATORS", ["symbol"], "inert", "A.3 ..., no-evaluators, ... (symbols)"),
    ("MEMO", ["symbol"], "inert", "A.3 ..., memo, ... (symbols)"),
    ("SMTLIB", ["symbol"], "inert", "A.3 ..., smtlib, ... (symbols)"),
    ("SMT_HOOK", ["symbol"], "inert", "A.3 ..., smt-hook, ... (symbols)"),
    ("SYMBOL", ["symbol"], "inert", "A.3 ..., symbol'Kywd' (presentation), ... (symbols)"),
    ("DEPRECATED", ["symbol"], "inert", "A.3 ..., deprecated (symbols)"),
    ("SYMBOL_OVERLOAD", ["any"], "supported", "A.3 symbol-overload (axioms): read / refused by decision"),
    ("ONE_PATH", ["frontend"], "not-handled", "A.3 one-path / all-path (modules)"),
    ("ALL_PATH", ["frontend"], "not-handled", "A.3 one-path / all-path (modules)"),
]
a3 = {}
for v, cls, st, where in A3:
    for c in cls: a3[(v, c)] = (st, where)
au = {nm: att_uses(KT[nm]) for nm in KT}
KCLS = {"symbol": "syntax", "sort": "syntax", "rule": "rule", "equation": "rule", "simplification": "rule",
        "claim": "claim", "module": "module"}
for k in keys("E2"):
    m = re.match(r"(\w+)\(([^)]*)\)(?:=(\S+))?@(\w+)$", k)
    v, att, val, cls = m.groups()
    marks = {}
    for nm in KT:
        if val is not None:
            marks[nm] = (f"{att}={val}", "cell") in au[nm]
        elif cls in ("any",):
            marks[nm] = None
        elif cls == "frontend":
            marks[nm] = any(a == att for a, _ in au[nm])
        else:
            marks[nm] = (att, KCLS[cls]) in au[nm]
    if (v, cls) in a3:
        st, where = a3[(v, cls)]
        row("E2", k, st, f"{KC} {where}", kimp=marks["kimp"], kore=marks["kore"])
    elif cls == "frontend":
        row("E2", k, "not-handled", "", note="FrontendOnly: DONE-0 C1 E2 names `erased` (evidence: two equal texts) for KFIX/TRIAGE",
            kimp=marks["kimp"], kore=marks["kore"])
    else:
        row("E2", k, "not-handled", "", kimp=marks["kimp"], kore=marks["kore"])

# ---------------------------------------------------------------- E3
for k in keys("E3"):
    row("E3", k, "not-handled", "", kimp=e3_used(k, KT["kimp"]), kore=e3_used(k, KT["kore"]))

# ---------------------------------------------------------------- E4
A12 = {
    "tree:Sentence.import": ("inert", "A.1 import"), "tree:Sentence.sort": ("supported", "A.1 sort S{}"),
    "tree:Sentence.hookedSort": ("supported", "A.1 hooked-sort"), "tree:Sentence.symbol": ("supported", "A.1 symbol"),
    "tree:Sentence.hookedSymbol": ("supported", "A.1 hooked-symbol"), "tree:Sentence.alias": ("refused", "A.1 alias: aliasDeclaration"),
    "tree:Sentence.axiom": ("supported", "A.1 axiom: read / inert / refused by shape"), "tree:Sentence.claim": ("inert", "A.1 claim"),
    "tree:KSort.var": ("refused", "A.2 sort variable: parametricSort (Q11)"), "tree:KSort.ctor": ("supported", "A.2 sort S{} / S{T...}: read / refused"),
    "tree:VarPattern.evar": ("supported", "A.2 element variable"), "tree:VarPattern.svar": ("not-handled", "A.2 set variable"),
    "tree:Pattern.var": ("supported", "A.2 element variable"), "tree:Pattern.app": ("supported", "A.2 application"),
    "tree:Pattern.string": ("not-handled", "A.2 string literal (outside \\dv and attributes)"),
    "tree:Pattern.top": ("supported", "A.2 \\top"), "tree:Pattern.bottom": ("supported", "A.2 \\bottom"),
    "tree:Pattern.not": ("supported", "A.2 \\not"), "tree:Pattern.and": ("supported", "A.2 \\and"),
    "tree:Pattern.or": ("supported", "A.2 \\or"), "tree:Pattern.implies": ("supported", "A.2 \\implies"),
    "tree:Pattern.iff": ("not-handled", "A.2 \\iff"), "tree:Pattern.exist": ("supported", "A.2 \\exists"),
    "tree:Pattern.forall": ("not-handled", "A.2 \\forall"), "tree:Pattern.mu": ("not-handled", "A.2 \\mu, \\nu"),
    "tree:Pattern.nu": ("not-handled", "A.2 \\mu, \\nu"), "tree:Pattern.ceil": ("inert", "A.2 \\ceil"),
    "tree:Pattern.floor": ("not-handled", "A.2 \\floor"), "tree:Pattern.equals": ("supported", "A.2 \\equals"),
    "tree:Pattern.in": ("supported", "A.2 \\in"), "tree:Pattern.next": ("not-handled", "A.2 \\next"),
    "tree:Pattern.rewrites": ("supported", "A.2 \\rewrites"), "tree:Pattern.dv": ("supported", "A.2 \\dv"),
    "tree:Pattern.leftAssoc": ("not-handled", "A.2 \\left-assoc, \\right-assoc"),
    "tree:Pattern.rightAssoc": ("not-handled", "A.2 \\left-assoc, \\right-assoc"),
}
GRAM = {  # grammar alternative (its start) -> the tree constructor whose K-coverage row speaks of it
    '<sentence>::=<sentence-import>': "tree:Sentence.import", '<sentence-import>::=': "tree:Sentence.import",
    '<sentence>::=<sentence-sort>': "tree:Sentence.sort", '<sentence-sort>::=': "tree:Sentence.sort",
    '<sentence>::=<sentence-hooked-sort>': "tree:Sentence.hookedSort", '<sentence-hooked-sort>::=': "tree:Sentence.hookedSort",
    '<sentence>::=<sentence-symbol>': "tree:Sentence.symbol", '<sentence-symbol>::=': "tree:Sentence.symbol",
    '<sentence>::=<sentence-hooked-symbol>': "tree:Sentence.hookedSymbol", '<sentence-hooked-symbol>::=': "tree:Sentence.hookedSymbol",
    '<sentence>::=<sentence-alias>': "tree:Sentence.alias", '<sentence-alias>::=': "tree:Sentence.alias",
    '<sentence>::=<sentence-axiom>': "tree:Sentence.axiom", '<sentence-axiom>::=': "tree:Sentence.axiom",
    '<sentence>::=<sentence-claim>': "tree:Sentence.claim", '<sentence-claim>::=': "tree:Sentence.claim",
    '<sort>::=<sort-variable>': "tree:KSort.var", '<sort>::=<sort-identifier>': "tree:KSort.ctor",
    '<variable-pattern>::=<element-variable>': "tree:VarPattern.evar", '<variable-pattern>::=<set-variable>': "tree:VarPattern.svar",
    '<pattern>::=<string-literal>': "tree:Pattern.string", '<application-pattern>::=': "tree:Pattern.app",
}
CONN = {"top": "\\top", "bottom": "\\bottom", "not": "\\not", "and": "\\and", "or": "\\or", "implies": "\\implies",
        "iff": "\\iff", "exist": "\\exists", "forall": "\\forall", "mu": "\\mu", "nu": "\\nu", "ceil": "\\ceil",
        "floor": "\\floor", "equals": "\\equals", "in": "\\in", "next": "\\next", "rewrites": "\\rewrites",
        "dv": "\\dv", "leftAssoc": "\\left-assoc", "rightAssoc": "\\right-assoc"}
for c, kw in CONN.items(): GRAM[f'<matching-logic-pattern>::="{kw}"'] = f"tree:Pattern.{c}"
ku4 = uses("kimp", "E4")
for k in keys("E4"):
    t = k if k.startswith("tree:") else next((v for g, v in GRAM.items() if k[len("grammar:"):].startswith(g)), None)
    g = k[len("grammar:"):]
    detectable = (k.startswith(("tree:Sentence.", "tree:VarPattern.")) or k in ("tree:Pattern.var", "tree:KSort.var")
                  or any(k == f"tree:Pattern.{c}" for c in CONN)
                  or g.startswith(("<matching-logic-pattern>::=", "<sentence>::=", "<sentence-", "<variable-pattern>::=",
                                   "<pattern>::=<variable-pattern>", "<sort>::=<sort-variable>")))
    km = (k in ku4) if ku4 is not None and detectable else None
    if t and t in A12:
        st, where = A12[t]
        row("E4", k, st, f"{KC} {where}", kimp=km)
    elif k in ("grammar:<definition>::=\"[\" <attributes> \"]\" <modules>",
               "grammar:<module>::=\"module\" <module-name> <sentences> \"endmodule\" \"[\" <attributes> \"]\""):
        row("E4", k, "supported", f"{KC} A.1 module structure; definition attributes inert")
    else:
        row("E4", k, "not-handled", "")

# ---------------------------------------------------------------- E5
STMAP = {"read": "supported", "inert": "inert", "refused by decision": "refused", "parameter": "parameter",
         "not handled": "not-handled"}
pb = [l.rstrip("\n").split("\t") for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "partb-sites.tsv"))
      if l.strip() and not l.startswith("#")]
for k in keys("E5"):
    rs = [r for r in pb if k in r[3].split(",")]
    sts = {STMAP.get(r[1], "-") for r in rs}
    names = ", ".join(f"B{r[0]} {r[1]}{' (changed)' if r[2] == 'yes' else ''}" for r in rs)
    if len(sts) == 1 and "-" not in sts and all(r[2] == "no" for r in rs):
        row("E5", k, sts.pop(), f"{KC} Part B rows {', '.join(r[0] for r in rs)}", note=names)
    else:
        row("E5", k, "not-handled", "", note=f"Part B rows of several statuses or changed: {names}")

# ---------------------------------------------------------------- E6
KCC = {}  # K-coverage Part C's status per hook name, for the note where the code's differs
for line in open(os.path.join(lib, "../findings/K-coverage.md")):
    m = re.match(r"\| `(\w+\.md|\w+\.k)` ([A-Z0-9-]+) \| (.*?) \| (\d+) \| ([a-z ]+) \|", line)
    if m:
        for h in re.findall(r"`([A-Z]+\.[A-Za-z0-9_]+)`", m.group(3)): KCC[(m.group(2), h)] = m.group(5)
ku6 = uses("kimp", "E6")
for line in open(os.path.join(keys_dir, "E6.keys")):
    k, where = line.rstrip("\n").split("\t")
    km = (k in ku6) if ku6 is not None else None
    kind = k.split(":")[0]
    if kind == "hook":
        h, nm = k.split(":")[1], k.split(":", 2)[2]
        mod = where.split()[-1]
        if "MInt" in nm or h.startswith("MINT."):
            st, ev = "refused", f"{KC} Part C: sort-parametric MInt, KCORE-SPEC.md Q11"
        elif mod not in LIBMODS:
            st, ev = "not-handled", f"{LIBP}: {mod} is not a library module (refused builtinText)"
        elif nm.startswith("Sort"):
            st, ev = "supported", f"{LIBP}: {mod}; the library's sort"
        elif h in REG:
            st, ev = "supported", f"{REGP}: {h}"
        else:
            st, ev = "parameter", f"{LIBP}: {mod}; Builtins.libParams (no registry hook)"
        kc = STMAP.get(KCC.get((mod, h), ""), None)
        note = f"K-coverage Part C at 57f851ec: {KCC[(mod, h)]}" if kc and kc != st else None
        row("E6", k, st, ev, note=note, kimp=km)
    elif kind == "module":
        mod = k.split(":", 1)[1]
        if mod in LIBMODS: row("E6", k, "supported", f"{LIBP}: the module's text is library data", kimp=None)
        else: row("E6", k, "not-handled", f"{LIBP}: not a library module", kimp=None)
    elif kind == "token":
        srt = k.split(":", 1)[1]
        ev = {"SortInt": "A.2 \\dv: Int canonical literals", "SortBool": "A.2 \\dv: Bool true/false",
              "SortString": "Part C STRING.String: literals as tokens (values since 6365ce2f)",
              "SortBytes": "Part C BYTES.Bytes: literals as tokens (values since 6365ce2f)",
              "SortFloat": "Part C FLOAT.Float: literals as tokens"}.get(srt)
        if ev: row("E6", k, "supported", f"{KC} {ev}", kimp=km)
        else: row("E6", k, "not-handled", "", kimp=km)
    else:
        mod = k.split(":")[1]
        if mod in LIBMODS:
            if kind == "lemma": row("E6", k, "inert", f"{KC} Part B simplification equation; {LIBP}: {mod}", kimp=km)
            else: row("E6", k, "supported", f"{LIBP}: {mod}, read as the library's text", kimp=km)
        else:
            row("E6", k, "not-handled", f"{LIBP}: {mod} is not a library module", kimp=km)

# ---------------------------------------------------------------- E7, E8
for l in ("E7", "E8"):
    for k in keys(l): row(l, k, "not-handled", "")


def q(s):
    return json.dumps(s, ensure_ascii=False)


with open(out, "w") as fh:
    fh.write(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "rows-header.toml")).read())
    for l in sorted(rows):
        fh.write(f"\n[{l}]\n")
        for k, r in rows[l].items():
            fh.write(f"{q(k)} = {{ " + ", ".join(f"{a} = {q(b) if isinstance(b, str) else str(b).lower()}" for a, b in r.items()) + " }\n")
print(", ".join(f"{l} {len(d)}" for l, d in sorted(rows.items())))
