"""The E6 rows of the library's sentences against the theorems that tie those sentences on a tied
text (DONE-0 C2 'supported', C14 part 2): the supported rows of keys axiom, module, sort, symbol and
token, and the inert rows of key lemma.

Usage (from kcore-spec):
  python3 -I test/constructs/e6map.py           print, per module, each row's ties and the rows left
                                                uncovered; exit 0
  python3 -I test/constructs/e6map.py --write   also write each row's field e6_tie
  python3 -I test/constructs/e6map.py --check   exit 1 unless every row's e6_tie is the one computed
                                                and the self-check passes
  python3 -I test/constructs/e6map.py --self-check   form (d)'s self-check only (below)

Tied texts and their tie files: the Lean files test/TieEns*.lean, test/TieKimp*.lean,
test/TieKk*.lean and test/LibEv*.lean, each on the text its `user_axioms U from "TEXT"` names.
A sentence of a text is its axiom of index N (KCore's AxiomDecl.index: the 1-based position among
the text's axioms, every module counted, in text order; U.axN in a tie file). A sentence is tied by
a theorem when one of these holds, read from the files' text:
  (a) the theorem's statement (its text up to `:=`) names an interpretation H (`HookParams`) and
      U.axN, and N is among the U.axM it names;
  (b) the theorem's statement is `∀ ad ∈ X, ...` with H, where the file defines
      `X : List AxiomDecl := U.all.filter fun ad => I.contains ad.index` and `I : List Nat` as a
      literal list holding N;
  (c) on kimp's text, N is in a class of test/TieKimp.lean's `classes` for which test/imp-tie.toml
      records the class's sentences proved, entailed at values or refuted with no remainder, or with
      its remainder given by `remainder_indices` and N not among them, and neither (a) nor (b) ties N
      there, and the class's list has the class's count; the theorems are the class's in
      imp-tie.toml (its file and theorems, those stating the class's list of indices left out).
A theorem whose statement holds `¬` refutes the sentence (Γ with it has no model, or it fails at a
valuation), one stating `SvAtMostOne` holds it only where its set variables hold one value at most, and
so does a theorem of a class of direction refuted: neither ties it. A row whose only theorems are such
gets "refuted: MODULE; ..." with them, is not tied, and counts as not tied for its module.
A row's sentences are the text's axioms whose key, computed as test/constructs/extract.py computes
E6's keys (the axiom's Source file, the module of that file holding its Location line, and the
Location's line and column; `lemma` when it is a simplification, and `#N` after the key for the
N-th sentence of a text with that key where rows.toml has a row of that name, as extract.py
numbers the sentences of one location, a `comm` rule's two among them), is the row's key.
A declaration is not an axiom, so (a) to (c) tie none. A row of a declaration (sort, symbol, token) is
tied by form (d), on the declaration files: the Lean files test/TieEns*.lean, test/TieKimp*.lean,
test/TieKk*.lean, test/TieRangeMap*.lean and test/LibEv*.lean, each on the text its
`kore_term kore from "TEXT"` names. A row's declarations are the text's sort and symbol declarations
with a builtin Source whose key, computed as extract.py computes E6's (the declaration's kind, the
module of its Location line, its name; a hooked one is a hook row's, outside this scope), is the
row's key; a token row's declaration is that of its sort, declared `token` or `hasDomainValues`, so
it is tied as the sort declaration's item (G-sort), which says nothing of how a `\\dv` string is read.
  (d) a theorem with H whose statement (its text up to `:=`, spaces collapsed) holds one of:
      - `∀ it ∈ declItems, Γ (cH H) ⊧ it.pat`, the file defining `plainSorts` and `declItems` by the
        lines PLAIN_SORTS and DECL_ITEMS, or `∀ sd ∈ kore.sortDecls, sd.params = [] → Γ (cH H) ⊧
        (sortConstantItem sd).pat`: it ties each sort declaration of the text without sort parameters;
      - `∀ sd ∈ X, Γ (cH H) ⊧ (sortConstantItem sd).pat`, the file defining
        `X : List SortDecl := kore.sortDecls.filter (N.contains ·.name)` and `N : List String` as a
        literal list: it ties each sort declaration without sort parameters named in N;
      - `∀ sd ∈ kore.symbolDecls, sd.params = [] → sd.name ∈ N → Γ (cH H) ⊧ (arityItem sd).pat`,
        the file defining `N : List String` as a literal list: it ties each symbol declaration without
        sort parameters named in N.
      A symbol declaration is tied only by a list naming it: that it names a symbol of Γ (and so is
      among the items `decls_entailed` reaches) is the kernel's fact in that file, not this script's.
The self-check: each theorem `decls_entailed` of a declaration file is in a form of (d); each name of
a symbol statement's list is an unhooked symbol declaration of the file's text with a builtin Source
and without sort parameters; and the control row DECL_CONTROL, which those texts declare without sort
parameters and no list names, is held by a text of (d) and not tied.
A module row is tied when every row of the module in this scope (axiom, lemma, sort, symbol) is, and
at least one exists.
e6_tie, on a row: a list of "THEOREM (FILE; TEXT axiom N)" or "THEOREM (FILE; TEXT sort|symbol
declaration NAME)" strings, "refuted: MODULE; ..." (above), or "uncovered: MODULE" with, after the
module, why: no tied text holds the sentence or declaration, the texts that hold it tie it by no
theorem (or a module with a row left uncovered).
"""
import os, re, sys, tomllib
from collections import defaultdict

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(K, "test"))
sys.dont_write_bytecode = True
import relsource
ROWS = os.path.join(K, "test/constructs/rows.toml")
KR = relsource.krust_root() or "K_RUST-unset"
KOMPILE = os.environ.get("K_KOMPILE", os.path.join(KR, "k/result/bin/kompile"))
BUILTIN = os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(KOMPILE))), "include/kframework/builtin")
TIE_FILE = re.compile(r"^(TieEns|TieKimp|TieKk|LibEv)\w*\.lean$")
DECL_FILE = re.compile(r"^(TieEns|TieKimp|TieKk|TieRangeMap|LibEv)\w*\.lean$")
SRC = re.compile(r"Source\{\}\(\"Source\(([^)]*)\)\"\)")
LOC = re.compile(r"Location\{\}\(\"Location\((\d+),(\d+),(\d+),(\d+)\)\"\)")


def module_lines():
    """file -> [(first line, last line, module)] of K's builtin files, the module blocks of their
    selected code as extract.py selects it (the `k` blocks of a .md file, every line of a .k file)."""
    if not os.path.isdir(BUILTIN):
        raise SystemExit(f"e6map: no K builtin directory {BUILTIN}: set K_RUST or K_KOMPILE")
    out = {}
    for f in sorted(os.listdir(BUILTIN)):
        lines = open(os.path.join(BUILTIN, f)).read().split("\n")
        if f.endswith(".md"):
            inblk, keep, code = False, False, []
            for i, l in enumerate(lines):
                if l.startswith("```"):
                    if not inblk:
                        tag = l[3:].strip()
                        inblk = True
                        keep = tag == "k" or re.search(r"(^|[ {])\.?k([ }]|$)", tag) is not None
                    else:
                        inblk = False
                    continue
                if inblk and keep:
                    code.append((i + 1, l))
        else:
            code = [(i + 1, l) for i, l in enumerate(lines)]
        stack = []
        for ln, l in code:
            m = re.match(r"\s*module ([A-Z0-9-]+)", l)
            if m:
                stack.append([ln, None, m.group(1)])
            if re.match(r"\s*endmodule", l) and stack and stack[-1][1] is None:
                stack[-1][1] = ln
        out[f] = stack
    return out


MODLINES = module_lines()


def module_at(f, line):
    for a, b, n in MODLINES.get(f, []):
        if a <= line <= (b or 10 ** 9):
            return n
    return "?"


def axioms(path):
    """[(index, module of the text, sentence text)] of the text's axioms, index 1-based over all its
    modules in text order (comment lines dropped)."""
    out, cur, mod = [], None, None
    for l in open(os.path.join(K, path)).read().split("\n"):
        if l.lstrip().startswith("//"):
            continue
        m = re.match(r"module (\S+)", l)
        if m:
            mod = m.group(1)
        starts = re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol|claim|alias|import) ", l) or \
            re.match(r"\s+axiom\s*\{", l) or l.startswith("endmodule") or l.startswith("module ")
        if starts:
            if cur:
                out.append(cur)
            cur = [mod, l.strip()] if re.match(r"\s+axiom\s*\{", l) else None
        elif cur:
            cur[1] += "\n" + l
    if cur:
        out.append(cur)
    return [(i + 1, m, s) for i, (m, s) in enumerate(out)]


def e6_key(s):
    """E6's key of an axiom with a builtin Source, as extract.py's e6_keys writes it, else None."""
    sm = SRC.search(s)
    if not sm or "/include/kframework/builtin/" not in sm.group(1):
        return None
    lm = LOC.search(s)
    if not lm:
        return None
    f = os.path.basename(sm.group(1))
    kind = "lemma" if "simplification{}(" in s else ("rule" if "\\rewrites{" in s else "axiom")
    return f"{kind}:{module_at(f, int(lm.group(1)))}:{lm.group(1)}:{lm.group(2)}"


def file_theorems(t):
    """[(full name, statement)] of a Lean file's theorems: the statement is the text up to `:=`
    (namespaces tracked by their `namespace` and `end` lines)."""
    ns, out = [], []
    for l in t.split("\n"):
        m = re.match(r"namespace (\S+)", l)
        if m:
            ns.append(m.group(1))
        m = re.match(r"end (\S+)\s*$", l)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
        m = re.match(r"(?:private )?theorem (\S+)", l)
        if m:
            out.append([".".join(ns + [m.group(1)]), l])
        elif out and out[-1][1] is not None:
            out[-1][1] += "\n" + l
        if out and out[-1][1] is not None and ":=" in out[-1][1]:
            out[-1].append(out[-1][1].split(":=")[0]); out[-1][1] = None
    return [(th[0], th[2]) for th in out if len(th) >= 3]


def lean_ties():
    """text -> index -> [(theorem, file)], from the tie files' text (forms (a) and (b))."""
    ties = defaultdict(lambda: defaultdict(list))
    for f in sorted(os.listdir(os.path.join(K, "test"))):
        if not TIE_FILE.match(f):
            continue
        rel = "test/" + f
        t = open(os.path.join(K, rel)).read()
        um = re.search(r'user_axioms U from "([^"]+)"', t)
        if not um:
            continue
        text = um.group(1)
        idx = {m.group(1): [int(x) for x in re.findall(r"\d+", m.group(2))]
               for m in re.finditer(r"^def (\w+) : List Nat :=\s*\[([\d,\s]*)\]", t, re.M)}
        lists = {m.group(1): idx[m.group(2)] for m in re.finditer(
            r"^(?:noncomputable )?def (\w+) : List AxiomDecl :=\s*U\.all\.filter fun ad => (\w+)\.contains ad\.index\s*$",
            t, re.M) if m.group(2) in idx}
        for name, stmt in file_theorems(t):
            if "HookParams" not in stmt:
                continue
            ns_ = {int(x) for x in re.findall(r"\bU\.ax(\d+)\b", stmt)}
            m = re.search(r"∀ ad ∈ (\w+),", stmt)
            if m and m.group(1) in lists:
                ns_ |= set(lists[m.group(1)])
            kind = "refutes" if "¬" in stmt else ("partial" if "SvAtMostOne" in stmt else "ties")
            for n in ns_:
                ties[text][n].append((name, rel, kind))
    return ties


def kimp_ties():
    """kimp's index -> [(theorem, file)] by the classes test/imp-tie.toml records tied (form (c))."""
    tie = tomllib.load(open(os.path.join(K, "test/imp-tie.toml"), "rb"))
    t = open(os.path.join(K, "test/TieKimp.lean")).read()
    blk = re.search(r"^def classes : List \(String × List Nat\) :=\n(.*?)\n\n", t, re.M | re.S).group(1)
    classes = {m.group(1): [int(x) for x in re.findall(r"\d+", m.group(2))]
               for m in re.finditer(r'\("([^"]+)", \[([\d,\s]*)\]\)', blk)}
    out = defaultdict(list)
    for c in tie["class"]:
        tied = sum(c.get(k, 0) or 0 for k in ("proved", "at_values", "refuted"))
        rem = c.get("remainder", 0) or 0
        if not c.get("file") or tied == 0 or tied + rem != c["count"] or len(classes.get(c["name"], [])) != c["count"]:
            continue
        if rem and len(c.get("remainder_indices", [])) != rem:
            continue
        for n in classes.get(c["name"], []):
            if n not in c.get("remainder_indices", []):
                for th in c["theorems"]:
                    if not re.search(r"_(indices|account|length|text|checked)$", th):
                        kind = "refutes" if c.get("direction") == "refuted" else "ties"
                        out[n].append((f"{c['name']}: {th}", c["file"], kind))
    return tie["text"], out


def declarations(path):
    """[(row key, kind, name, has sort parameters)] of a text's sort and symbol declarations with a
    builtin Source, keyed as test/constructs/extract.py keys E6's declarations (a hooked one's key is
    a hook row's, outside this scope), and a `token:` key beside the sort key of a sort declared
    `token` or `hasDomainValues`."""
    out, cur = [], None
    for l in open(os.path.join(K, path)).read().split("\n"):
        if l.lstrip().startswith("//"):
            continue
        if re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol|claim|alias|import|axiom)\b", l) or \
                l.startswith("endmodule") or l.startswith("module "):
            if cur:
                out.append(cur)
            cur = l.strip() if re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol) ", l) else None
        elif cur:
            cur += "\n" + l
    if cur:
        out.append(cur)
    res = []
    for s in out:
        sm = SRC.search(s)
        if not sm or "/include/kframework/builtin/" not in sm.group(1):
            continue
        lm = LOC.search(s)
        mod = module_at(os.path.basename(sm.group(1)), int(lm.group(1)) if lm else 0)
        head = s.split()[0]
        m = re.match(r"\S+ (\S+?)\{([^}]*)\}", s)
        nm, params = m.group(1), bool(m.group(2).strip())
        kind = "sort" if head in ("sort", "hooked-sort") else "symbol"
        if not re.search(r'(?<![-\w])hook\{\}\("([^"]*)"\)', s):
            res.append((f"{kind}:{mod}:{nm}", kind, nm, params))
        if kind == "sort" and re.search(r"\btoken\{\}\(\)|hasDomainValues\{\}\(\)", s):
            res.append((f"token:{nm}", kind, nm, params))
    return res


def str_lists(t):
    """name -> the literal `List String` the file defines under that name."""
    return {m.group(1): re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(2))
            for m in re.finditer(r"^def (\w+) : List String :=\s*\[([^\]]*)\]", t, re.M)}


PLAIN_SORTS = "noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)"
DECL_ITEMS = "noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem"


def decl_forms():
    """file -> (text, [(theorem, 'sort' | 'symbol', None for every declaration without sort
    parameters or the set of names)]), each declaration file's text and its statements of form (d)
    (none for a file stating none), and the theorems `decls_entailed` of the declaration files in no
    form of (d) (the self-check's)."""
    forms, odd = {}, []
    for f in sorted(os.listdir(os.path.join(K, "test"))):
        if not DECL_FILE.match(f):
            continue
        rel = "test/" + f
        t = open(os.path.join(K, rel)).read()
        km = re.search(r'^kore_term kore from "([^"]+)"', t, re.M)
        if not km:
            continue
        lines = set(l.strip() for l in t.split("\n"))
        strs = str_lists(t)
        sortsets = {m.group(1): set(strs[m.group(2)]) for m in re.finditer(
            r"^noncomputable def (\w+) : List SortDecl := kore\.sortDecls\.filter \((\w+)\.contains ·\.name\)\s*$",
            t, re.M) if m.group(2) in strs}
        got = []
        for name, stmt in file_theorems(t):
            s = " ".join(stmt.split())
            n0 = len(got)
            if "(H : HookParams)" in s:
                if ("∀ it ∈ declItems, Γ (cH H) ⊧ it.pat" in s and PLAIN_SORTS in lines and DECL_ITEMS in lines) or \
                        "∀ sd ∈ kore.sortDecls, sd.params = [] → Γ (cH H) ⊧ (sortConstantItem sd).pat" in s:
                    got.append((name, "sort", None))
                for m in re.finditer(r"∀ sd ∈ (\w+), Γ \(cH H\) ⊧ \(sortConstantItem sd\)\.pat", s):
                    if m.group(1) in sortsets:
                        got.append((name, "sort", sortsets[m.group(1)]))
                for m in re.finditer(r"∀ sd ∈ kore\.symbolDecls, sd\.params = \[\] → sd\.name ∈ (\w+) → "
                                     r"Γ \(cH H\) ⊧ \(arityItem sd\)\.pat", s):
                    if m.group(1) in strs:
                        got.append((name, "symbol", set(strs[m.group(1)])))
            if name.split(".")[-1] == "decls_entailed" and len(got) == n0:
                odd.append(f"{rel}: {name} is in no form of (d)")
        forms[rel] = (km.group(1), got)
    return forms, odd


def decl_ties(forms):
    """text -> row key -> [(theorem, file, declaration name)] (form (d)), and text -> the row keys of
    the text's declarations with a builtin Source."""
    ties, held = defaultdict(lambda: defaultdict(list)), defaultdict(set)
    decls = {}
    for rel, (text, got) in sorted(forms.items()):
        if text not in decls:
            decls[text] = declarations(text)
            held[text] = {k for k, *_ in decls[text]}
        for key, kind, nm, params in decls[text]:
            for th, k, names in got:
                if k == kind and not params and (names is None or nm in names):
                    ties[text][key].append((th, rel, nm))
    return ties, held


DECL_CONTROL = "symbol:INT-COMMON:Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int"


def self_check(rows, res):
    """Form (d)'s self-check: each `decls_entailed` of a declaration file is in a form of (d); each
    name of a symbol statement's list is a declaration of the file's text with a builtin Source,
    unhooked and without sort parameters; and the control row (`dividesInt`, which the texts declare
    without sort parameters and no list names) is held by a text of (d) and not tied."""
    forms, odd = decl_forms()
    bad = list(odd)
    for rel, (text, got) in sorted(forms.items()):
        ds = {(kind, nm): params for key, kind, nm, params in declarations(text) if not key.startswith("token:")}
        for th, k, names in got:
            for n in sorted(names or []) if k == "symbol" else []:
                if ds.get((k, n), True):
                    bad.append(f"{rel}: {th} names {n}, no unhooked {k} declaration of {text} with a builtin "
                               f"Source and without sort parameters")
    if not any(DECL_CONTROL in h for h in decl_ties(forms)[1].values()):
        bad.append(f"control {DECL_CONTROL}: held by no text of form (d)")
    elif DECL_CONTROL not in rows or isinstance(res.get(DECL_CONTROL), list):
        bad.append(f"control {DECL_CONTROL}: not a row, or tied")
    for b in bad:
        print(f"e6map self-check: {b}")
    print(f"e6map self-check: {len(forms)} declaration files ({sum(1 for _, g in forms.values() if g)} with a "
          f"statement of form (d)), "
          f"{sum(len(g) for _, g in forms.values())} statements of form (d), {len(bad)} failures")
    return not bad


def compute():
    rows = tomllib.load(open(ROWS, "rb"))["E6"]
    ties = lean_ties()
    ktext, kt = kimp_ties()
    for n, l in kt.items():
        if not ties[ktext].get(n):
            ties[ktext][n] += l
    dties, dheld_by = decl_ties(decl_forms()[0])
    # key -> text -> [index]
    where = defaultdict(lambda: defaultdict(list))
    for text in sorted(ties) + ([] if ktext in ties else [ktext]):
        seen = defaultdict(int)
        for i, _m, s in axioms(text):
            k = e6_key(s)
            if k:
                seen[k] += 1
                if seen[k] > 1 and f"{k}#{seen[k]}" in rows:
                    k = f"{k}#{seen[k]}"
                where[k][text].append(i)
    scope = {k: v for k, v in rows.items()
             if (v["status"] == "supported" and k.split(":")[0] in ("axiom", "module", "sort", "symbol", "token"))
             or (v["status"] == "inert" and k.startswith("lemma:"))}
    res = {}
    for k, v in scope.items():
        kind = k.split(":")[0]
        mod = k.split(":")[1] if kind != "token" else "(token sort)"
        if kind in ("axiom", "lemma"):
            got, other = [], []
            for text, ns in sorted(where.get(k, {}).items()):
                for n in ns:
                    for th, f, kind in ties[text].get(n, []):
                        (got if kind == "ties" else other).append(f"{th} ({f}; {text} axiom {n})" + (
                            "" if kind == "ties" else f" [{kind}]"))
            if got:
                res[k] = sorted(set(got))
            elif other:
                res[k] = (f"refuted: {mod}; no theorem entails the sentence; it is refuted (Γ with it has no "
                          f"model) or holds only where its set variables hold at most one value: "
                          + ", ".join(sorted(set(other))))
            elif k in where:
                res[k] = f"uncovered: {mod}; held by {', '.join(sorted(where[k]))}, tied there by no theorem"
            else:
                res[k] = f"uncovered: {mod}; no tied text holds the sentence"
        elif kind == "module":
            continue
        else:
            got = [f"{th} ({f}; {text} {'sort' if kind == 'token' else kind} declaration {nm})"
                   for text in sorted(dties) for th, f, nm in dties[text].get(k, [])]
            dheld = sorted(text for text, h in dheld_by.items() if k in h)
            res[k] = (sorted(set(got)) if got else
                      f"uncovered: {mod}; a declaration held by {', '.join(dheld)}, tied there by no theorem" if dheld
                      else f"uncovered: {mod}; a declaration no tied text holds")
    for k in scope:
        if k.startswith("module:"):
            m = k.split(":")[1]
            mine = [r for r in res if r.split(":")[1] == m and not r.startswith("module:")]
            left = sum(1 for r in mine if not isinstance(res[r], list))
            if mine and not left:
                res[k] = [f"every axiom, lemma, sort and symbol row of {m} ({len(mine)}) is tied"]
            else:
                res[k] = (f"uncovered: {m}; {left} of its {len(mine)} axiom, lemma, sort and symbol rows uncovered"
                          if mine else f"uncovered: {m}; no axiom, lemma, sort or symbol row of the module")
    return scope, res


def toml_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def write(res):
    lines = open(ROWS).read().split("\n")
    sect, n = None, 0
    for i, l in enumerate(lines):
        m = re.match(r"^\[(\w+)\]$", l)
        if m:
            sect = m.group(1); continue
        if sect != "E6":
            continue
        m = re.match(r'^("[^"]*") = \{ (.*) \}$', l)
        if not m:
            continue
        key = tomllib.loads(f"k = {m.group(1)}")["k"]
        if key not in res:
            continue
        v = res[key]
        val = "[" + ", ".join(toml_str(x) for x in v) + "]" if isinstance(v, list) else toml_str(v)
        body = re.sub(r', e6_tie = (\[[^\]]*\]|"(?:[^"\\]|\\.)*")', "", m.group(2))
        lines[i] = f"{m.group(1)} = {{ {body}, e6_tie = {val} }}"
        n += 1
    open(ROWS, "w").write("\n".join(lines))
    return n


def main():
    scope, res = compute()
    if "--self-check" in sys.argv or "--check" in sys.argv:
        ok = self_check(tomllib.load(open(ROWS, "rb"))["E6"], res)
        if "--self-check" in sys.argv:
            return 0 if ok else 1
    if "--check" in sys.argv:
        bad = [k for k, v in scope.items() if v.get("e6_tie") != res[k]]
        for k in bad[:20]:
            print(f"e6map: {k}: e6_tie is not the computed one")
        print(f"e6map check: {len(scope) - len(bad)} of {len(scope)} rows' e6_tie current")
        return 1 if bad or not ok else 0
    by = defaultdict(list)
    for k in scope:
        by[k.split(":")[1] if not k.startswith("token:") else "(token sort)"].append(k)
    tied = sum(1 for v in res.values() if isinstance(v, list))
    for m in sorted(by):
        un = [k for k in by[m] if not isinstance(res[k], list)]
        print(f"{m}: {len(by[m]) - len(un)} tied, {len(un)} uncovered")
        for k in by[m]:
            if isinstance(res[k], list):
                print(f"  tied {k}: {res[k][0]}" + (f" (+{len(res[k]) - 1})" if len(res[k]) > 1 else ""))
        for k in un:
            print(f"  uncovered {k}: {res[k].split('; ', 1)[1]}")
    print(f"e6map: {len(scope)} rows ({sum(1 for k in scope if scope[k]['status'] == 'supported')} supported, "
          f"{sum(1 for k in scope if scope[k]['status'] == 'inert')} inert lemma): {tied} tied, "
          f"{len(scope) - tied} uncovered")
    if "--write" in sys.argv:
        print(f"e6map: e6_tie written on {write(res)} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
