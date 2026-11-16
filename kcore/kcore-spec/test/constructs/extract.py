"""The eight key lists of K constructs (E1 to E8), extracted from K 7.1.337's sources.

Usage: python3 -I extract.py K_CHECKOUT K_INSTALL KORE_SYNTAX_MD E6_DEFINITION_KORE OUTDIR

Writes OUTDIR/E1.keys .. OUTDIR/E8.keys (one key per line, a tab, then where the key was found)
and OUTDIR/recount.txt (the second-method recounts). Exits 1 when a recount disagrees with the
extraction by a difference no statement below explains.

Each list's extraction unit:
  E1  Outer.jj: the grammar keywords outside the action blocks of the outer-syntax productions
      Require, Module, Import, Sentence, PriorityBlock, Production, ProductionItem, Tag, and the AST
      class each action builds (`new X(`).
  E2  Att.scala: every `final val NAME = Key.builtin(...)` / `Key.internal(...)`. A WholePipeline
      key gives one row per KORE sentence class its `onlyon` set reaches (CLASS_OF below); a
      FrontendOnly key one row `@frontend`; a key whose value kompile matches against a closed
      set (CLOSED below, read from the code that matches it) one row per value.
  E3  The rule grammar of a module importing every builtin module: the productions of kast.md's
      modules that RuleGrammarGenerator.getRuleGrammar adds (K, RULE-CELLS, DEFAULT-LAYOUT, with
      their imports), one row per alternative; the `#KVariable` token split by the meaning of its
      prefix; and every `Production(` site of RuleGrammarGenerator.java (a generated family, one
      row per site). The library's own productions are E6's symbols and token sorts.
  E4  kore-syntax.md: one row per alternative of each BNF production; and the constructors of
      kore-lean's KSort, VarPattern, Pattern, Sentence.
  E5  ModuleToKORE.java: every `append("  axiom…` / `claim` / `alias` / `symbol ` / `sort ` /
      `hooked-` site (also through `String.format`), keyed by method, keyword and ordinal.
  E6  The kompiled text of test/constructs/all-builtins.k: every sentence of its main module with a
      Source in the builtin directory, keyed: hooked declarations by hook then name, unhooked
      symbols by module and name, axioms by module and Location; one row per module of the builtin
      files, one per token sort.
  E7  KoreBackend.steps' default stepOrdering, in order, and the passes getKompiledModule applies
      before ModuleToKORE.
  E8  KompileOptions.java, the classes it delegates to (@ParametersDelegate, transitively) and the
      two backends' *KompileOptions.java: one row per @Parameter, keyed by its first name.
"""
import os, re, sys
from collections import Counter, defaultdict

kco, kinst, koresyn, e6kore, out = sys.argv[1:6]
FE = os.path.join(kco, "k-frontend/src/main")
BUILTIN = os.path.join(kinst, "include/kframework/builtin")
os.makedirs(out, exist_ok=True)
lists = {f"E{i}": {} for i in range(1, 9)}
recount = []
bad = []


def add(lst, key, where):
    d = lists[lst]
    if key in d:
        raise SystemExit(f"{lst}: duplicate key {key} ({d[key]}; {where})")
    d[key] = where


def read(p):
    return open(p, encoding="utf-8").read()


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


# ---------------------------------------------------------------- E1 outer syntax
OUTER = os.path.join(FE, "javacc/Outer.jj")
jj = read(OUTER)
E1_BLOCKS = ["Require", "Module", "Import", "Sentence", "PriorityBlock", "Production",
             "ProductionItem", "Tag"]


def jj_block(name):
    m = re.search(r"^\w[\w<>]*\s+" + name + r"\s*\([^)]*\)\s*:", jj, re.M)
    if not m:
        raise SystemExit(f"E1: no production {name} in Outer.jj")
    # declarations block { ... } then the expansion block { ... }
    i = jj.index("{", m.end())
    def skip(i):
        depth, j = 0, i
        while True:
            c = jj[j]
            if c == '"':
                j += 1
                while jj[j] != '"':
                    j += 2 if jj[j] == "\\" else 1
            elif c == "{": depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0: return j + 1
            j += 1
    k = skip(i)
    k2 = jj.index("{", k)
    return m.start(), k2, skip(k2)


for b in E1_BLOCKS:
    start, s, e = jj_block(b)
    body = jj[s + 1:e - 1]
    # split the expansion into grammar text (outside action braces) and actions
    gram, acts, depth, j, cur = [], [], 0, 0, []
    while j < len(body):
        c = body[j]
        if c == '"':
            k = j + 1
            while body[k] != '"':
                k += 2 if body[k] == "\\" else 1
            (cur if depth else gram).append(body[j:k + 1]); j = k + 1; continue
        if c == "{":
            depth += 1
            if depth == 1: cur = []; j += 1; continue
        elif c == "}":
            depth -= 1
            if depth == 0: acts.append("".join(cur)); j += 1; continue
        (cur if depth else gram).append(c)
        j += 1
    g = "".join(gram)
    ln = line_of(jj, start)
    for kw in re.findall(r'"((?:[^"\\]|\\.)+)"', g):
        k = f"{b}:{'kw' if re.fullmatch(r'[A-Za-z][A-Za-z-]*', kw) else 'lit'}:{kw}"
        if k not in lists["E1"]: add("E1", k, f"Outer.jj:{ln}")
    for tok in re.findall(r"<([A-Z_]+)>", g):
        k = f"{b}:token:{tok}"
        if k not in lists["E1"]: add("E1", k, f"Outer.jj:{ln}")
    for cls in re.findall(r"\bnew\s+([A-Z]\w*)\s*\(", "\n".join(acts)):
        if cls in ("ArrayList", "StringBuilder", "HashSet", "HashMap") or cls.endswith("Comparator"): continue
        k = f"{b}:node:{cls}"
        if k not in lists["E1"]: add("E1", k, f"Outer.jj:{ln}")

# ---------------------------------------------------------------- E2 attributes
ATT = os.path.join(FE, "scala/org/kframework/attributes/Att.scala")
att = read(ATT)
CLASS_OF = {
    "Production": ["symbol"], "SyntaxSort": ["sort"],
    "Rule": ["rule", "equation", "simplification"], "Claim": ["claim"], "Module": ["module"],
    "Context": ["rule"], "ContextAlias": ["rule"],  # ResolveContexts turns contexts into rules
    "RuleOrClaim": ["rule", "equation", "simplification", "claim"],
    "Sentence": ["sort", "symbol", "rule", "equation", "simplification", "claim"],
}
GSFCD = read(os.path.join(FE, "java/org/kframework/compile/GenerateSentencesFromConfigDecl.java"))
CINFO = read(os.path.join(FE, "java/org/kframework/compile/ConfigurationInfo.java"))
RIOS = read(os.path.join(FE, "java/org/kframework/compile/ResolveIOStreams.java"))
sw = GSFCD[GSFCD.index("switch (type)"):]
sw = sw[:sw.index("default:")]
CLOSED = {
    "MULTIPLICITY": re.findall(r'case "([^"]+)" ->', CINFO[CINFO.index("Multiplicity of("):]),
    "TYPE": re.findall(r'case "([^"]+)":', sw),
    "STREAM": re.findall(r'streams\.add\("([^"]+)"\)', RIOS),
}
decl_re = re.compile(r'^  final val (\w+)\s*=\s*Key\.(builtin|internal)\(\s*(.*?)\)\s*$', re.M | re.S)
# a declaration ends at the next `final val`, a comment or a blank line
starts = [m.start() for m in re.finditer(r"^  final val \w+", att, re.M)]
n_final = len(starts)
e2_keys = {}
for i, st in enumerate(starts):
    seg = att[st:starts[i + 1] if i + 1 < len(starts) else att.index("\n\n", st)]
    seg = re.split(r"\n\s*(/\*|//|\n)", seg)[0]
    m = re.match(r'  final val (\w+)\s*=\s*Key\.(builtin|internal)\((.*)\)\s*$', seg, re.S)
    if not m:
        raise SystemExit(f"E2: unparsed declaration at Att.scala:{line_of(att, st)}: {seg[:80]!r}")
    name, kind, args = m.group(1), m.group(2), " ".join(m.group(3).split())
    ln = line_of(att, st)
    km = re.match(r'"([^"]+)"|classOf\[(\w+)\]\.getName', args)
    # classOf[X].getName: the class's full name, by Att.scala's imports
    key = km.group(1) or {"Location": "org.kframework.attributes.Location",
                          "Source": "org.kframework.attributes.Source",
                          "Production": "org.kframework.definition.Production",
                          "Sort": "org.kframework.kore.Sort"}[km.group(2)]
    rng = re.search(r"KeyRange\.(\w+)", args).group(1)
    if kind == "builtin":
        param = re.search(r"KeyParameter\.(\w+)", args).group(1)
        on = re.search(r"onlyon\d?\[([^\]]+)\]", args).group(1).replace(" ", "").split(",")
    else:
        param, on = "Optional", ["AnyRef"]
    e2_keys[name] = (key, kind, param, on, rng, ln)
    where = f"Att.scala:{ln} {kind} {param} onlyon[{','.join(on)}] {rng}"
    base = f"{name}({key})"
    if name in CLOSED:
        if not CLOSED[name]:
            raise SystemExit(f"E2: no closed set found for {name}")
        for v in CLOSED[name]:
            add("E2", f"{base}={v}@{'frontend' if rng == 'FrontendOnly' else 'any'}", where)
    elif rng == "FrontendOnly":
        add("E2", f"{base}@frontend", where)
    else:
        classes = []
        for c in on:
            for k in CLASS_OF.get(c, ["any"]):
                if k not in classes: classes.append(k)
        for c in classes:
            add("E2", f"{base}@{c}", where)
nb = sum(1 for v in e2_keys.values() if v[1] == "builtin")
ni = sum(1 for v in e2_keys.values() if v[1] == "internal")
raw_b = len(re.findall(r"Key\.builtin\(", att)) - 0
raw_i = len(re.findall(r"Key\.internal", att))
raw_b_def = len(re.findall(r"def builtin\(", att))
raw_i_def = len(re.findall(r"def internal\(", att))
recount.append(f"E2: {n_final} `final val` declarations at the start of a line; parsed {nb} Key.builtin + {ni} Key.internal = {nb + ni}")
recount.append(f"E2: grep counts in Att.scala: `Key.builtin(` {raw_b}, `Key.internal` {raw_i} (of which "
               f"{raw_i - ni} outside a declaration: the error message at Att.scala:534 quotes "
               "`final val MY_ATT = Key.internal`)")
if nb + ni != n_final: bad.append("E2: parsed declarations differ from the `final val` count")
# the manual's Attributes Reference, the other way: each key it lists is an E2 key
man = read(os.path.join(kco, "docs/user_manual.md"))
sec = man[man.index("### Attribute Index"):man.index("### Index Legend")]
mkeys = set()
for m in re.finditer(r"^\| `([^`]+)`", sec, re.M):
    k = re.sub(r"\(.*\)$", "", m.group(1).split("=")[0].strip()).strip()
    mkeys.add(k)
allk = {v[0] for v in e2_keys.values()}
missing = sorted(mkeys - allk)
recount.append(f"E2: manual Attribute Index and Internal Attribute Index: {len(mkeys)} distinct keys; "
               f"not an E2 key: {missing if missing else 'none'}")
recount.append(f"E2: E2 keys the manual's indexes do not list: {len(allk - mkeys)}")
if missing: bad.append(f"E2: manual keys missing from the extraction: {missing}")

# ---------------------------------------------------------------- E3 rule grammar
KAST = read(os.path.join(BUILTIN, "kast.md"))
code = "\n".join(re.findall(r"^```k\n(.*?)^```", KAST, re.M | re.S))
mods = {}
for m in re.finditer(r"^\s*module ([A-Z0-9-]+).*?\n(.*?)^\s*endmodule", code, re.M | re.S):
    mods[m.group(1)] = m.group(2)
RGG = read(os.path.join(FE, "java/org/kframework/parser/inner/RuleGrammarGenerator.java"))
gm = RGG[RGG.index("private Module getGrammar("):]
roots = ["K", "RULE-CELLS", "DEFAULT-LAYOUT"]  # getGrammar(mod, RULE_CELLS): K, name, DEFAULT_LAYOUT
for r in ("K)", "name)", "DEFAULT_LAYOUT)"):
    if f"baseK.getModule({r}" not in gm: raise SystemExit("E3: getGrammar no longer imports K, RULE-CELLS, DEFAULT-LAYOUT")
seen, order = set(), []
def visit(mn):
    if mn in seen: return
    seen.add(mn)
    for im in re.findall(r"^\s*imports\s+(?:public\s+|private\s+)?([A-Z0-9-]+)", mods[mn], re.M):
        if im in mods: visit(im)
    order.append(mn)
for r in roots: visit(r)
# the #KVariable token's alternatives of different meaning (kast.md: `!X` fresh, `?X` existential,
# `@X` set variable, `_` anonymous, `_X` named anonymous, `X` plain)
KVAR_SPLIT = ["plain", "fresh-!", "existential-?", "set-@", "anonymous-_", "named-anonymous-_X"]
def strip_comment(l):
    out, q = [], False
    i = 0
    while i < len(l):
        c = l[i]
        if c == '"' : q = not q
        if not q and l.startswith("//", i): break
        if q and c == "\\": out.append(l[i:i + 2]); i += 2; continue
        out.append(c); i += 1
    return "".join(out)
for mn in order:
    body = re.sub(r"/\*.*?\*/", "", mods[mn], flags=re.S)
    stmts, cur = [], None
    for l in body.split("\n"):
        l = strip_comment(l).rstrip()
        s = l.strip()
        if not s: continue
        if s.startswith("syntax"):
            if cur: stmts.append(cur)
            cur = s
        elif cur and not re.match(r"(syntax|imports|rule|context|claim|configuration|module|endmodule)\b", s):
            cur += " " + s
        else:
            if cur: stmts.append(cur)
            cur = None
    if cur: stmts.append(cur)
    for st in stmts:
        m = re.match(r"syntax\s+(\{[^}]*\}\s*)?(\S+)\s*::=\s*(.*)$", st)
        if not m: continue
        sort = m.group(2)
        rhs = m.group(3)
        rhs = re.sub(r"^(left|right|non-assoc):", "", rhs.strip())
        alts, buf, q, depth = [], [], False, 0
        i = 0
        while i < len(rhs):
            c = rhs[i]
            if c == '"' and (i == 0 or rhs[i - 1] != "\\"): q = not q
            if not q and c == "[": depth += 1
            if not q and c == "]": depth -= 1
            if not q and depth == 0 and c in "|>" and rhs[i - 1:i + 1] != "=>" and rhs[i:i + 2] != ">K" :
                # `|` and `>` separate alternatives outside strings and attribute lists
                if c == ">" and i + 1 < len(rhs) and rhs[i + 1] == '"':
                    pass
                alts.append("".join(buf).strip()); buf = []; i += 1
                alts[-1] = re.sub(r"^(left|right|non-assoc):", "", alts[-1]).strip()
                continue
            buf.append(c); i += 1
        alts.append(re.sub(r"^(left|right|non-assoc):", "", "".join(buf).strip()).strip())
        for a in alts:
            items = re.sub(r"\s*\[[^\]]*\]\s*$", "", a).strip()
            items = " ".join(items.split())
            sym = re.search(r"symbol\(([^)]*)\)", a)
            key = f"{mn}:{sort}::={items}"
            if sort == "#KVariable" and items.startswith('r"'):
                for part in KVAR_SPLIT:
                    add("E3", f"{key}#{part}", "kast.md (split: the token's prefixes)")
                continue
            add("E3", key, f"kast.md {mn}" + (f" symbol({sym.group(1)})" if sym else ""))
fam, mt = Counter(), "?"
for ln, l in enumerate(RGG.split("\n"), 1):
    m = re.match(r"  (?:public |private |protected )(?:static )?[\w<>, .\[\]]+? (\w+)\(", l)
    if m: mt = m.group(1)
    for _ in re.finditer(r"(?<![\w.])Production\(", l):
        fam[mt] += 1
        add("E3", f"generated:{mt}#{fam[mt]}", f"RuleGrammarGenerator.java:{ln}")
n_syntax = len(re.findall(r"^\s*syntax", code, re.M))
recount.append(f"E3: kast.md has {n_syntax} `syntax` lines in all; the rule grammar's modules "
               f"({', '.join(order)}) give {sum(1 for k in lists['E3'] if not k.startswith('generated:'))} production rows")

# ---------------------------------------------------------------- E4 KORE grammar
ks = read(koresyn)
blocks = re.findall(r"^```\n(.*?)^```", ks, re.M | re.S)
nprod = 0
for bl in blocks:
    name, rhs = None, []
    def flush():
        global nprod
        if name is None: return
        text = " ".join(rhs)
        if not text.strip(): return
        nprod += 1
        # alternatives: split on `|` outside quotes and brackets
        alts, buf, q, depth = [], [], False, 0
        for i, c in enumerate(text):
            if c == '"' and text[i - 1:i] != "\\" : q = not q
            if not q and c == "[": depth += 1
            if not q and c == "]": depth -= 1
            if c == "|" and not q and depth == 0:
                alts.append("".join(buf)); buf = []; continue
            buf.append(c)
        alts.append("".join(buf))
        for a in alts:
            a = " ".join(a.split())
            if a == "" and name == "<[$item]-sep-by-[$separator]>": a = '""'
            add("E4", f"grammar:{name}::={a}", "kore-syntax.md")
    for l in bl.split("\n"):
        l = re.sub(r"\s*//.*$", "", l)
        if not l.strip(): continue
        m = re.match(r"^(<[^>]+>)\s*(::=)?\s*(.*)$", l)
        if m and not l.startswith(" "):
            flush(); name, rhs = m.group(1), [m.group(3)] if m.group(3) else []
        else:
            s = l.strip()
            s = re.sub(r"^::=?\s*", "", s)  # kore-syntax.md writes `<modules>`'s as `::`
            rhs.append(s)
    flush()
AST = read(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../kore-lean/KoreParser/AST.lean"))
for ind in ("KSort", "VarPattern", "Pattern", "Sentence"):
    m = re.search(r"^inductive " + ind + r" where\n(.*?)\n  deriving", AST, re.M | re.S)
    for c in re.findall(r"^  \| (\S+)", m.group(1), re.M):
        add("E4", f"tree:{ind}.{c.strip('«»')}", "kore-lean/KoreParser/AST.lean")

# ---------------------------------------------------------------- E5 emitted shapes
M2K = os.path.join(FE, "java/org/kframework/backend/kore/ModuleToKORE.java")
m2k = read(M2K).split("\n")
meth, cnt = None, Counter()
for i, l in enumerate(m2k, 1):
    m = re.match(r"\s+(?:public |private |protected |static |final |synchronized )+[\w<>\[\], ?.]+\s+(\w+)\s*\(", l)
    if m and not l.strip().startswith("return"): meth = m.group(1)
    m = re.search(r'append\((?:String\.format\()?"\s*(axiom|claim|alias|symbol |sort |hooked-)', l)
    if m:
        kw = m.group(1).strip()
        cnt[(meth, kw)] += 1
        add("E5", f"{meth}:{kw}#{cnt[(meth, kw)]}", f"ModuleToKORE.java:{i}")
raw = sum(1 for l in m2k if re.search(r'"\s*(axiom|claim|alias|symbol |sort |hooked-)', l) and "append" in l)
recount.append(f"E5: {len(lists['E5'])} sites; lines of ModuleToKORE.java with `append` and such a literal: {raw}")
if raw != len(lists["E5"]): bad.append("E5: site count differs from the line count")
# second method: K-coverage Part B's rows (partb-sites.tsv), each naming the sites that write it
pb = [l.rstrip("\n").split("\t") for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "partb-sites.tsv"))
      if l.strip() and not l.startswith("#")]
with_status = [r for r in pb if r[1] != "-"]
named, unknown, siteless = set(), [], []
for r in pb:
    if r[3] == "-":
        siteless.append(r[0]); continue
    for k in r[3].split(","):
        if k in lists["E5"]: named.add(k)
        else: unknown.append((r[0], k))
unnamed = sorted(set(lists["E5"]) - named)
recount.append(f"E5: K-coverage Part B: {len(pb)} rows, {len(with_status)} with a status; rows naming no site: {siteless} "
               f"(the prelude, copied as text); sites named by no row: {unnamed or 'none'}; names that are no site: {unknown or 'none'}")
if unknown or unnamed or len(with_status) != 58:
    bad.append("E5: Part B rows and sites do not correspond")

# ---------------------------------------------------------------- E6 builtin library
modlines = {}  # file -> [(start, end, module)]
src_hooks = Counter()
for f in sorted(os.listdir(BUILTIN)):
    t = read(os.path.join(BUILTIN, f))
    lines = t.split("\n")
    if f.endswith(".md"):
        inblk, sel = False, []
        for i, l in enumerate(lines):
            if l.startswith("```"):
                if not inblk:
                    tag = l[3:].strip()
                    inblk = True
                    keep = tag == "k" or re.search(r"(^|[ {])\.?k([ }]|$)", tag) is not None
                    sel.append(None)
                else:
                    inblk = False
                continue
            if inblk and keep: sel.append((i + 1, l))
        code_lines = [x for x in sel if x]
    else:
        code_lines = [(i + 1, l) for i, l in enumerate(lines)]
    stack = []
    for ln, l in code_lines:
        m = re.match(r"\s*module ([A-Z0-9-]+)", l)
        if m: stack.append([ln, None, m.group(1)])
        if re.match(r"\s*endmodule", l) and stack and stack[-1][1] is None: stack[-1][1] = ln
        s = re.sub(r"//.*$", "", l)
        for h in re.findall(r"(?<![-\w])hook\(([^)]*)\)", s):
            src_hooks[(f, h)] += 1
    modlines[f] = stack


def module_at(f, line):
    for a, b, n in modlines.get(f, []):
        if a <= line <= (b or 10 ** 9): return n
    return "?"


for f, ms in modlines.items():
    for a, b, n in ms:
        add("E6", f"module:{n}", f"{f}:{a}")
if not os.path.exists(e6kore):
    raise SystemExit(f"E6: {e6kore} absent; run test/constructs/kompile-e6.sh first")
src_re = re.compile(r"Source\{\}\(\"Source\(([^)]*)\)\"\)")
loc_re = re.compile(r"Location\{\}\(\"Location\((\d+),(\d+),(\d+),(\d+)\)\"\)")


def kore_sentences(text):
    """The sentences of a kompiled text's last module (comment lines dropped)."""
    mainmod = text[text.rindex("\nmodule "):]
    sents, cur = [], None
    for l in mainmod.split("\n"):
        if l.lstrip().startswith("//"): continue
        if re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol|claim|alias|import) ", l) or re.match(r"\s+axiom\s*\{", l):
            if cur: sents.append(cur)
            cur = l.strip()
        elif l.startswith("endmodule"):
            if cur: sents.append(cur)
            cur = None
        elif cur is not None:
            cur += "\n" + l
    return sents


def e6_keys(text):
    """E6's keys of a kompiled text's sentences placed in the builtin directory, with the hooks."""
    keys, hooks, token_sorts, axk = [], Counter(), [], Counter()
    for s in kore_sentences(text):
        sm = src_re.search(s)
        if not sm or "/include/kframework/builtin/" not in sm.group(1):
            continue
        f = os.path.basename(sm.group(1))
        lm = loc_re.search(s)
        ln = int(lm.group(1)) if lm else 0
        mod = module_at(f, ln)
        head = s.split()[0]
        where = f"{f}:{ln}"
        if head in ("hooked-sort", "hooked-symbol", "sort", "symbol"):
            nm = re.match(r"\S+ (\S+?)\{", s).group(1)
            hm = re.search(r'(?<![-\w])hook\{\}\("([^"]*)"\)', s)
            if hm:
                hooks[(f, hm.group(1))] += 1
                keys.append((f"hook:{hm.group(1)}:{nm}", where + f" {mod}"))
            elif head in ("sort", "hooked-sort"):
                keys.append((f"sort:{mod}:{nm}", where))
            else:
                keys.append((f"symbol:{mod}:{nm}", where))
            if head in ("sort", "hooked-sort") and re.search(r"\btoken\{\}\(\)|hasDomainValues\{\}\(\)", s):
                token_sorts.append((nm, where))
        elif head.startswith("axiom"):
            kind = "lemma" if "simplification{}(" in s else ("rule" if "\\rewrites{" in s else "axiom")
            base = f"{kind}:{mod}:{lm.group(1)}:{lm.group(2)}" if lm else f"{kind}:{mod}:?"
            axk[base] += 1
            keys.append((base + (f"#{axk[base]}" if axk[base] > 1 else ""), where))
        else:
            keys.append((f"{head}:{mod}:{ln}", where))
    keys += [(f"token:{nm}", where) for nm, where in token_sorts]
    return keys, hooks


kore = read(e6kore)
e6k, kore_hooks = e6_keys(kore)
for k, w in e6k:
    add("E6", k, w)
# second method: `hook(` in the source files against the kompiled text's hooked declarations
s_tot, k_tot = sum(src_hooks.values()), sum(kore_hooks.values())
s_dis = len({h for _, h in src_hooks}); k_dis = len({h for _, h in kore_hooks})
recount.append(f"E6: `hook(` occurrences in the builtin files' selected code (smt-hook excluded): {s_tot} ({s_dis} distinct names); "
               f"hooked declarations with a builtin Source in the kompiled text: {k_tot} ({k_dis} distinct names)")
by_file = defaultdict(lambda: [0, 0])
for (f, h), n in src_hooks.items(): by_file[f][0] += n
for (f, h), n in kore_hooks.items(): by_file[f][1] += n
recount.append("E6: per file (source / kompiled): " + ", ".join(f"{f} {a}/{b}" for f, (a, b) in sorted(by_file.items())))
only_src = sorted({h for _, h in src_hooks} - {h for _, h in kore_hooks})
only_kore = sorted({h for _, h in kore_hooks} - {h for _, h in src_hooks})
recount.append(f"E6: hook names in the source and not in the kompiled text: {len(only_src)}: {' '.join(only_src)}")
recount.append(f"E6: hook names in the kompiled text and not in the source: {len(only_kore)}: {' '.join(only_kore)}")
E6_EXPLAINED = os.path.join(os.path.dirname(os.path.abspath(__file__)), "e6-unkompiled-hooks.txt")
expl = set()
if os.path.exists(E6_EXPLAINED):
    for l in open(E6_EXPLAINED):
        l = l.split("#")[0].strip()
        if l: expl.add(l.split()[0])
unexpl = [h for h in only_src if h not in expl]
if unexpl or only_kore:
    bad.append(f"E6: unexplained hook differences: source-only {unexpl}, kompiled-only {only_kore}")

# ---------------------------------------------------------------- E7 compile passes
KB = read(os.path.join(FE, "java/org/kframework/backend/kore/KoreBackend.java"))
so = KB[KB.index("stepOrdering =\n"):]
so = so[so.index("List.of("):so.index(");")]
steps = re.findall(r'"(\w+)"', so)
named = dict(re.findall(r'entry\("(\w+)",\s*([^)]*?)\)', KB))
for i, s in enumerate(steps, 1):
    add("E7", f"{i:02d}:{s}", f"KoreBackend.java stepOrdering #{i}")
gk = KB[KB.index("getKompiledModule("):]
gk = gk[:gk.index("return mainModule;")]
for i, (cls, desc) in enumerate(re.findall(r"new (\w+)\([^)]*\)::\w+, \"([^\"]+)\"", gk), 1):
    add("E7", f"emit{i}:{cls}", f"KoreBackend.getKompiledModule: {desc}")
# the parse phase's definition transformers (DefinitionParsing, Kompile.excludeModulesByTag), before steps
def transformer_descs(text):
    res = []
    for m in re.finditer(r"DefinitionTransformer\.from\(", text):
        j, depth, last = m.end(), 1, None
        while depth:
            c = text[j]
            if c == '"':
                k = j + 1
                while text[k] != '"': k += 2 if text[k] == "\\" else 1
                if depth == 1: last = text[j + 1:k]
                j = k + 1; continue
            depth += c == "("; depth -= c == ")"; j += 1
        res.append((line_of(text, m.start()), last))
    return res
for fn in ("kompile/DefinitionParsing.java", "kompile/Kompile.java"):
    t = read(os.path.join(FE, "java/org/kframework", fn))
    for ln, d in transformer_descs(t):
        if fn.endswith("Kompile.java") and "resolving io streams" == d: continue  # step resolveIO
        add("E7", f"parse:{os.path.basename(fn)[:-5]}:{d}", f"{fn}:{ln}")
# second method: the directory listing of compile/
CD = os.path.join(FE, "java/org/kframework/compile")
files = sorted(f[:-5] for f in os.listdir(CD) if f.endswith(".java"))
used = set()
pipeline_src = KB[KB.index("public Function<Definition, Definition> steps()"):KB.index("Function1<Definition, Definition> applyPipeline")]
for f in files:
    if re.search(r"\b" + f + r"\b", pipeline_src) or re.search(r"\b" + f + r"\b", gk): used.add(f)
unused = [f for f in files if f not in used]
n_emit = sum(1 for k in lists["E7"] if k.startswith("emit"))
recount.append(f"E7: {len(steps)} default steps ({len(set(steps))} distinct names), {n_emit} emit-time passes, "
               f"{len(lists['E7']) - len(steps) - n_emit} parse-phase transformers; "
               f"compile/ holds {len(files)} .java files (and the directory checks/); named in steps() or getKompiledModule: {len(used)}; "
               f"not named there: {len(unused)}: {' '.join(unused)}")
E7_EXPLAINED = os.path.join(os.path.dirname(os.path.abspath(__file__)), "e7-unused-files.txt")
expl7 = set()
if os.path.exists(E7_EXPLAINED):
    for l in open(E7_EXPLAINED):
        l = l.split("#")[0].strip()
        if l: expl7.add(l.split()[0])
if [f for f in unused if f not in expl7]:
    bad.append(f"E7: compile/ files used by no step and not explained: {[f for f in unused if f not in expl7]}")

# ---------------------------------------------------------------- E8 kompile options
def opt_classes():
    root = os.path.join(FE, "java/org/kframework/kompile/KompileOptions.java")
    todo, done = [root], []
    idx = {}
    for dp, _, fs in os.walk(FE):
        for f in fs:
            if f.endswith(".java"): idx.setdefault(f[:-5], os.path.join(dp, f))
    while todo:
        p = todo.pop(0)
        if p in done: continue
        done.append(p)
        for cls in re.findall(r"@ParametersDelegate\s+(?:public |private |protected )?(?:final )?(?:transient )?(\w+)", read(p)):
            if cls in idx: todo.append(idx[cls])
    for b in ("haskell-backend/src/main/java/org/kframework/backend/haskell/HaskellKompileOptions.java",
              "llvm-backend/src/main/java/org/kframework/backend/llvm/LLVMKompileOptions.java"):
        done.append(os.path.join(kco, b))
    return done
src_names = set()
for p in opt_classes():
    t = read(p)
    rel = os.path.relpath(p, kco)
    for m in re.finditer(r"@Parameter\((.*?)\)\s*(?:public|private|protected)?", t, re.S):
        nm = re.search(r"names\s*=\s*(\{[^}]*\}|\"[^\"]*\")", m.group(1))
        if not nm:
            continue  # the main parameter (the definition file)
        names = re.findall(r'"([^"]+)"', nm.group(1))
        src_names.update(names)
        add("E8", names[0], f"{rel}:{line_of(t, m.start())} {' '.join(names)}")
helpf = os.environ.get("KOMPILE_HELP")
if helpf and os.path.exists(helpf):
    hn = set()
    for l in open(helpf):
        if re.match(r"^    -", l):
            # `--name <arg>, -n <arg>`: every word that starts with `-`
            hn.update(w.rstrip(",") for w in l.split() if w.startswith("-"))
    recount.append(f"E8: {len(lists['E8'])} @Parameter rows ({len(src_names)} names with aliases); "
                   f"`kompile --help` and `--help-hidden` list {len(hn)} names; in the help and not the source: "
                   f"{sorted(hn - src_names) or 'none'}; in the source and not the help: {sorted(src_names - hn) or 'none'}")
    if hn - src_names: bad.append(f"E8: help names not extracted: {sorted(hn - src_names)}")
else:
    recount.append("E8: no help text (KOMPILE_HELP); recount not run")
    bad.append("E8: recount not run")

# the rows' texts (KCORE_ROW_TEXTS="name=definition.kore ..."): the E4 and E6 keys each text meets
E4_CONN = {"top": "\\top", "bottom": "\\bottom", "not": "\\not", "and": "\\and", "or": "\\or",
           "implies": "\\implies", "iff": "\\iff", "exist": "\\exists", "forall": "\\forall",
           "mu": "\\mu", "nu": "\\nu", "ceil": "\\ceil", "floor": "\\floor", "equals": "\\equals",
           "in": "\\in", "next": "\\next", "rewrites": "\\rewrites", "dv": "\\dv",
           "leftAssoc": "\\left-assoc", "rightAssoc": "\\right-assoc"}
E4_SENT = {"import": "import", "sort": "sort", "hookedSort": "hooked-sort", "symbol": "symbol",
           "hookedSymbol": "hooked-symbol", "alias": "alias", "axiom": "axiom", "claim": "claim"}


def e4_uses(text):
    used = set()
    body = "\n".join(l for l in text.split("\n") if not l.lstrip().startswith("//"))
    for c, kw in E4_CONN.items():
        if re.search(re.escape(kw) + r"\s*\{", body):
            used.add(f"tree:Pattern.{c}")
            used.update(k for k in lists["E4"] if k.startswith(f'grammar:<matching-logic-pattern>::="{kw}"'))
    for c, kw in E4_SENT.items():
        if re.search(r"^\s*" + re.escape(kw) + r"\b", body, re.M):
            used.add(f"tree:Sentence.{c}")
            used.add(f"grammar:<sentence>::=<sentence-{kw if kw in ('import', 'sort', 'symbol', 'alias', 'axiom', 'claim') else kw}>")
            used.update(k for k in lists["E4"] if k.startswith(f'grammar:<sentence-{kw}>::='))
    if re.search(r"[(,]\s*@\w+\s*:\s*Sort", body):
        used.update({"tree:VarPattern.svar", "grammar:<variable-pattern>::=<set-variable>"})
    if re.search(r"[(,]\s*[A-Za-z][\w'-]*\s*:\s*Sort", body):
        used.update({"tree:VarPattern.evar", "tree:Pattern.var", "grammar:<variable-pattern>::=<element-variable>",
                     "grammar:<pattern>::=<variable-pattern>"})
    if re.search(r"\{[^{}]*\bR\b[^{}]*\}", body):
        used.update({"tree:KSort.var", "grammar:<sort>::=<sort-variable>"})
    return used & set(lists["E4"])


for spec in os.environ.get("KCORE_ROW_TEXTS", "").split():
    nm, path = spec.split("=", 1)
    t = read(path)
    with open(os.path.join(out, f"uses-{nm}.E4"), "w") as fh:
        fh.write("".join(k + "\n" for k in sorted(e4_uses(t))))
    ks = {k for k, _ in e6_keys(t)[0]}
    with open(os.path.join(out, f"uses-{nm}.E6"), "w") as fh:
        fh.write("".join(k + "\n" for k in sorted(ks)))
    recount.append(f"rows' texts: {nm}: {len(e4_uses(t))} E4 keys met; {len(ks)} builtin sentences keyed, "
                   f"{len(ks - set(lists['E6']))} of them not E6 keys: {sorted(ks - set(lists['E6']))[:8]}")

for l, d in lists.items():
    with open(os.path.join(out, f"{l}.keys"), "w") as fh:
        for k, w in d.items():
            fh.write(f"{k}\t{w}\n")
with open(os.path.join(out, "recount.txt"), "w") as fh:
    fh.write("\n".join(recount) + "\n")
    for b in bad: fh.write("RECOUNT FAILS: " + b + "\n")
print("\n".join(recount))
print("counts: " + ", ".join(f"{l} {len(d)}" for l, d in lists.items()))
for b in bad: print("RECOUNT FAILS: " + b)
sys.exit(1 if bad else 0)
