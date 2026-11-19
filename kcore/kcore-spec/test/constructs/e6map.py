"""The E6 rows of the library's sentences against the theorems that tie those sentences on a tied
text (DONE-0 C2 'supported', C14 part 2): the supported rows of keys axiom, module, sort, symbol and
token, and the inert rows of key lemma.

Usage (from kcore-spec):
  python3 -I test/constructs/e6map.py           print, per module, each row's ties and the rows left
                                                uncovered; exit 0
  python3 -I test/constructs/e6map.py --write   also write each row's field e6_tie
  python3 -I test/constructs/e6map.py --check   exit 1 unless every row's e6_tie is the one computed
                                                and the self-check passes
  python3 -I test/constructs/e6map.py --self-check   the self-check of forms (d) and (e) only (below)

Tied texts and their tie files: the Lean files test/TieEns*.lean, test/TieKimp*.lean,
test/TieKk*.lean, test/TieE6*.lean and test/LibEv*.lean, each on the text its `user_axioms U from "TEXT"` names.
A sentence of a text is its axiom of index N (KCore's AxiomDecl.index: the 1-based position among
the text's axioms, every module counted, in text order; U.axN in a tie file). A sentence is tied by
a theorem when one of these holds, read from the files' text:
  (a) the theorem's statement (its text up to `:=`) names an interpretation H (`HookParams`) and
      U.axN, and N is among the U.axM it names;
  (b) the theorem's statement is `∀ ad ∈ X, ...` with H, where the file defines
      `X : List AxiomDecl := U.all.filter fun ad => I.contains ad.index` and `I : List Nat` as a
      literal list holding N, or, in a file test/TieE6*.lean (tiegen's output on a construct fixture),
      `X : List AxiomDecl := [U.axA, ...]` as a literal list holding U.axN (beside the axioms of other
      `user_axioms` literals, `PreludeKseq.ax1`, which tie no row here);
  (c) on kimp's text, N is in a class of test/TieKimp.lean's `classes` for which test/imp-tie.toml
      records the class's sentences proved, entailed at values or refuted with no remainder, or with
      its remainder given by `remainder_indices` and N not among them, and neither (a) nor (b) ties N
      there, and the class's list has the class's count; the theorems are the class's in
      imp-tie.toml (its file and theorems, those stating the class's list of indices left out).
  (f) N is a sentence of the class `parameter lemma` (direction hypothesis: it applies a parameter
      symbol without `impl`, whose value the interpretation gives, so it is owed as a hypothesis on
      H, at values) of a tie file test/Tie*.lean on the text that defines
      `paramLemmaText : List AxiomDecl` as a literal list holding U.axN, `ParamLemmaWitnessAtValues`
      as `∃ H : HookParams, FnObligations (cH H) callOrder [] ∧ ∀ ad ∈ paramLemmaText,
      EntailsAtValues (cH H) ad (trS ad).pat`, has N under "parameter lemma" in its `classes`, and
      declares `paramlemma_account` (the class is that list) and a theorem whose statement is
      `ParamLemmaWitnessAtValues` (some H meets the hypothesis: the text with it has a model). The
      definition alone ties nothing. The theorems are those two, each item ending in
      "; direction hypothesis".
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
test/TieKk*.lean, test/TieE6*.lean, test/TieRangeMap*.lean and test/LibEv*.lean, each on the text its
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
No direction (form (e); owed-sentence rule item 7 of rows-header.toml): a sentence or declaration
that applies a symbol Γ lacks is of the tie's no-direction class, which no theorem entails or refutes.
  (e1) an axiom row's sentence N on a tied text is of that class where a tie file of the text (the
       files of (a)) has a `classes` list holding N under "no direction" and declares the theorems
       account_absent and absent_closed, which state that the class holds exactly the sentences
       applying a head Γ lacks; the theorems are those two;
  (e2) or where a theorem, without `¬`, of a file test/LibEv*.lean or test/TieRangeMap*.lean on the
       text states `absentOf U.axN = L`, or `[U.axA, ...].map absentOf = [LA, ...]` (paired by
       position), with L a nonempty list literal of strings (or `String` defs) each of which the text
       declares as a symbol without sort parameters: Γ then has no symbol of that name. An absent head
       that is an instance of a symbol declared with sort parameters (`ite{SortInt}`) is not of this
       form: Γ has a symbol of that name, and the sentence may fix a value of it (rows-header.toml,
       item 7, library parameters);
  a symbol row's declaration NAME on a text is of that class where a theorem, without `¬`, of a
       declaration file on the text has a statement holding `hasSym NAME = false` (NAME a string
       literal or a `String` def), or `(X.filter (!hasSym ·.name)).map (·.name) = L` with L a literal
       list holding NAME.
A row that a form of (a) to (d) or (f) ties on any text is tied; else one that a theorem only refutes is
"refuted: ..."; else one of the no-direction class on some text is "no direction: ...", never tied;
else it is uncovered.
The self-check: each theorem `decls_entailed` of a declaration file is in a form of (d); each name of
a symbol statement's list is an unhooked symbol declaration of the file's text with a builtin Source
and without sort parameters; every symbol row held by a text of (d) that no list of (d) names is not
tied, and is of no direction exactly where a declaration fact of (e) names it on a text holding it.
The control is stated on one text: a declaration no list of (d) on a text names is not tied there,
and is of no direction there only where form (e) holds; the control DECL_CONTROL (dividesInt on
silentflt, which declares it without sort parameters and whose Γ lacks it) is held by that text's
declaration files, named by no list of (d) on that text, and of form (e) there. AX_CONTROL controls (e2):
on silentflt, dividesInt's equation (274) is of (e2), and findChar's (296), whose absent heads are
`ite{SortInt}`, is not, although a statement names it with absentOf and a nonempty list literal.
MODULE_CONTROL controls the module form below: STDIN-STREAM is not of it, SORT-BOOL is.
A module row is tied when every row of the module in this scope (axiom, lemma, sort, symbol) is tied
or of no direction with a theorem of kind "in a model" naming it, and at least one is tied. Such a
theorem is one of a file test/LibParamExpand*.lean whose statement holds ∃ and ⊧ᴵP and names, on the
file's text, U.axN for a sentence the row's no-direction class holds there, or, for a declaration
row, the declaration's name as a string (or a `String` def). Without such a file, a module with a
row of no direction is not tied.
A module row in this scope with no axiom, lemma, sort or symbol row of its module in this scope is
tied by form (w), the whole-text tie, where its `fixture` text f2-examples/FIXTURE.kompile.kore holds
a sentence (an axiom, or a sort or symbol declaration, hooked or not) whose builtin Source and
Location place it in the module, and a tie file test/Tie*.lean on that text (its `user_axioms U from
"TEXT"`) defines `uncovered : List (Nat × String)` as the literal empty list (every class with a
theorem has a theorem holding each of its sentences: the tie leaves no remainder) and declares each
theorem of WHOLE_THEOREMS: `account` (the classes partition the user module's axioms),
`account_absent` and `absent_closed` (the no-direction class), `lists_in_account`, `decls_entailed`
(the declarations' items) and `consistent` (Γ has a model); the theorems are those. WHOLE_CONTROL
controls it: TIMER is of it, and e6-mod-sort-kbott's text, whose tie file's `uncovered` holds KItem's
no-junk sentence, has no whole-text tie. Form (w) is tried before the next one.
A module of hooks and generated declarations only is accounted by its declarations' rows, with no
theorem owed for the module itself: a module row in this scope with no row of E6, of any status,
keyed to its module other than hook rows (no axiom, lemma, rule, sort or symbol row: each sentence
of E6's text placed in the module is a hooked declaration, whose key is its hook's, and a declaration
kompile generates carries no builtin Source), and whose selected code holds no `rule`,
`configuration`, `context` or `claim` sentence (a module whose rules E6's text leaves out, such as
STDIN-STREAM, is not of the form; MODULE_CONTROL checks it). Its hook rows are those of the hooks the
module's selected code names in `hook(...)`.
e6_tie, on a row: a list of "THEOREM (FILE; TEXT axiom N)" or "THEOREM (FILE; TEXT sort|symbol
declaration NAME)" strings (form (w): "THEOREM (FILE; TEXT whole text: ...; the text holds n
sentences of MODULE)"), "refuted: MODULE; ..." (above), "no direction: MODULE; THEOREM (FILE;
TEXT axiom N|symbol declaration NAME); ..." with the theorems of form (e), or "uncovered: MODULE" with,
after the module, why: no tied text holds the sentence or declaration, the texts that hold it tie it
by no theorem (or a module with a row left uncovered, the rows of no direction counted apart).
A module row that is tied reads "every axiom, lemma, sort and symbol row of MODULE (n) is tied",
followed by ", or of no direction with a theorem in a model (k)" where k of them are. A module of
hooks and generated declarations only reads, as a list (counted as tied), "module of hooks and
generated declarations only: no axiom, lemma, rule, sort or symbol row of MODULE in E6; its
declarations are accounted by their rows: n hook rows (HOOK, ...)" (one hook row: "1 hook row"),
or "0 hook rows: E6's text places no sentence in the module".
The summary counts the rows tied, of no direction and uncovered apart.
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
TIE_FILE = re.compile(r"^(TieEns|TieKimp|TieKk|TieE6|LibEv)\w*\.lean$")
DECL_FILE = re.compile(r"^(TieEns|TieKimp|TieKk|TieE6|TieRangeMap|LibEv)\w*\.lean$")
SRC = re.compile(r"Source\{\}\(\"Source\(([^)]*)\)\"\)")
LOC = re.compile(r"Location\{\}\(\"Location\((\d+),(\d+),(\d+),(\d+)\)\"\)")


def code_lines(f):
    """[(line, text)] of the selected code of K's builtin file f, as extract.py selects it (the `k`
    blocks of a .md file, every line of a .k file)."""
    lines = open(os.path.join(BUILTIN, f)).read().split("\n")
    if not f.endswith(".md"):
        return [(i + 1, l) for i, l in enumerate(lines)]
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
    return code


def module_lines():
    """file -> [(first line, last line, module)] of K's builtin files, the module blocks of their
    selected code (`code_lines`)."""
    if not os.path.isdir(BUILTIN):
        raise SystemExit(f"e6map: no K builtin directory {BUILTIN}: set K_RUST or K_KOMPILE")
    out = {}
    for f in sorted(os.listdir(BUILTIN)):
        stack = []
        for ln, l in code_lines(f):
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


def module_hooks():
    """(module -> the hook names the module's selected code names in `hook(...)`, each once, in
    source order; the modules whose selected code holds a `rule`, `configuration`, `context` or
    `claim` sentence), comments dropped."""
    out, sents = defaultdict(list), set()
    for f, st in MODLINES.items():
        code = code_lines(f)
        for a, b, n in st:
            for ln, l in code:
                if a <= ln <= (b or 10 ** 9):
                    l = re.sub(r"//.*$", "", l)
                    if re.match(r"\s*(rule|configuration|context|claim)\b", l):
                        sents.add(n)
                    for h in re.findall(r"(?<![-\w])hook\(([^)]*)\)", l):
                        if h not in out[n]:
                            out[n].append(h)
    return out, sents


HOOKS_ONLY = "module of hooks and generated declarations only"
MEMBER_KINDS = ("axiom", "lemma", "rule", "sort", "symbol")


def hooks_only(m, rows, mhooks, msents):
    """The form of a module of hooks and generated declarations only, for module m, or None: E6
    keys no axiom, lemma, rule, sort or symbol row of any status to m, and m's selected code holds
    no `rule`, `configuration`, `context` or `claim` sentence; its hook rows are those of the hooks
    its selected code names."""
    if m in msents or any(r.split(":")[0] in MEMBER_KINDS and r.split(":")[1] == m for r in rows):
        return None
    hs = [h for h in mhooks.get(m, []) if any(r.startswith(f"hook:{h}:") for r in rows)]
    acc = (f"{len(hs)} hook row{'' if len(hs) == 1 else 's'} ({', '.join(hs)})" if hs
           else "0 hook rows: E6's text places no sentence in the module")
    return [f"{HOOKS_ONLY}: no axiom, lemma, rule, sort or symbol row of {m} in E6; its declarations "
            f"are accounted by their rows: {acc}"]


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
        if f.startswith("TieE6"):
            lists.update({m.group(1): [int(x) for x in re.findall(r"U\.ax(\d+)", m.group(2))] for m in re.finditer(
                r"^(?:noncomputable )?def (\w+) : List AxiomDecl :=\s*\[((?:\s*\w+\.ax\d+\s*,)*\s*\w+\.ax\d+\s*)\]\s*$",
                t, re.M)})
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


PL_FILE = re.compile(r"^Tie\w*\.lean$")
PL_WITNESS = ("def ParamLemmaWitnessAtValues : Prop := ∃ H : HookParams, FnObligations (cH H) callOrder [] ∧ "
              "∀ ad ∈ paramLemmaText, EntailsAtValues (cH H) ad (trS ad).pat")


def paramlemma_ties():
    """text -> index -> [(theorem, file)]: the sentences of the class `parameter lemma` tied as a
    direction hypothesis (form (f))."""
    out = defaultdict(lambda: defaultdict(list))
    for f in sorted(os.listdir(os.path.join(K, "test"))):
        if not PL_FILE.match(f):
            continue
        rel = "test/" + f
        t = open(os.path.join(K, rel)).read()
        um = re.search(r'user_axioms U from "([^"]+)"', t)
        if not um or " ".join(PL_WITNESS.split()) not in " ".join(t.split()):
            continue
        lm = re.search(r"^noncomputable def paramLemmaText : List AxiomDecl := \[([^\]]*)\]", t, re.M)
        cm = re.search(r"^def classes : List \(String × List Nat\) :=\n(.*?)\n\n", t, re.M | re.S)
        if not lm or not cm:
            continue
        lit = {int(x) for x in re.findall(r"U\.ax(\d+)", lm.group(1))}
        cls = {int(x) for m in re.finditer(r'\("parameter lemma", \[([\d,\s]*)\]\)', cm.group(1))
               for x in re.findall(r"\d+", m.group(1))}
        ths = file_theorems(t)
        acc = [n for n, _ in ths if n.split(".")[-1] == "paramlemma_account"]
        wit = [n for n, st in ths if re.fullmatch(r"\s*(?:private )?theorem \S+\s*:\s*ParamLemmaWitnessAtValues\s*", st)]
        if not acc or not wit:
            continue
        for n in sorted(lit & cls):
            for th in acc + wit:
                out[um.group(1)][n].append((th, rel))
    return out


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



ND_FILE = re.compile(r"^(LibEv|TieRangeMap)\w*\.lean$")
MODEL_FILE = re.compile(r"^LibParamExpand\w*\.lean$")


def str_defs(t):
    """name -> the string literal of a `def NAME : String := "..."` of a Lean file."""
    return {m.group(1): m.group(2) for m in re.finditer(r'^def (\w+) : String := "((?:[^"\\]|\\.)*)"', t, re.M)}


def name_list(lit, defs):
    """The strings of a Lean list literal of string literals and `String` defs, None if an item is
    neither."""
    out = []
    for it in [x.strip() for x in lit.strip()[1:-1].split(",") if x.strip()]:
        m = re.fullmatch(r'"((?:[^"\\]|\\.)*)"', it)
        if m:
            out.append(m.group(1))
        elif it in defs:
            out.append(defs[it])
        else:
            return None
    return out


def symbol_params(path):
    """name -> whether the text declares the symbol with sort parameters, over every symbol and
    hooked-symbol declaration of the text."""
    out = {}
    for l in open(os.path.join(K, path)).read().split("\n"):
        m = re.match(r"\s+(?:hooked-)?symbol (\S+?)\{([^}]*)\}", l)
        if m:
            out[m.group(1)] = out.get(m.group(1), False) or bool(m.group(2).strip())
    return out


def nodir_axioms():
    """text -> index -> [(theorem, file)]: the sentences of the no-direction class (form (e1), (e2))."""
    nd = defaultdict(lambda: defaultdict(list))
    for f in sorted(os.listdir(os.path.join(K, "test"))):
        e1, e2 = TIE_FILE.match(f), ND_FILE.match(f)
        if not (e1 or e2):
            continue
        rel = "test/" + f
        t = open(os.path.join(K, rel)).read()
        um = re.search(r'user_axioms U from "([^"]+)"', t)
        if not um:
            continue
        text = um.group(1)
        ths = file_theorems(t)
        if e1:
            names = {n.split(".")[-1]: n for n, _ in ths}
            cm = re.search(r"^def classes : List \(String × List Nat\) :=\n(.*?)\n\n", t, re.M | re.S)
            if cm and "account_absent" in names and "absent_closed" in names:
                for m in re.finditer(r'\("no direction", \[([\d,\s]*)\]\)', cm.group(1)):
                    for n in re.findall(r"\d+", m.group(1)):
                        for th in ("account_absent", "absent_closed"):
                            nd[text][int(n)].append((names[th], rel))
        if e2:
            defs, decl = str_defs(t), None
            for name, stmt in ths:
                s = " ".join(stmt.split())
                if "¬" in s or "absentOf" not in s:
                    continue
                pairs = [(int(m.group(1)), name_list(m.group(2), defs))
                         for m in re.finditer(r"absentOf U\.ax(\d+) = (\[[^\[\]]*\])", s)]
                for m in re.finditer(r"\[((?:U\.ax\d+, )*U\.ax\d+)\]\.map absentOf = \[((?:\[[^\[\]]*\](?:, )?)+)\]", s):
                    ns_ = [int(x) for x in re.findall(r"U\.ax(\d+)", m.group(1))]
                    ls = re.findall(r"\[[^\[\]]*\]", m.group(2))
                    if len(ns_) == len(ls):
                        pairs += [(n, name_list(l, defs)) for n, l in zip(ns_, ls)]
                for n, names_ in pairs:
                    if not names_:
                        continue
                    if decl is None:
                        decl = symbol_params(text)
                    if all(decl.get(x) is False for x in names_):
                        nd[text][n].append((name, rel))
    return nd


def nodir_decls():
    """text -> symbol name -> [(theorem, file)]: the declarations of the no-direction class (form (e)
    for declarations)."""
    nd = defaultdict(lambda: defaultdict(list))
    for f in sorted(os.listdir(os.path.join(K, "test"))):
        if not DECL_FILE.match(f):
            continue
        rel = "test/" + f
        t = open(os.path.join(K, rel)).read()
        km = re.search(r'^kore_term kore from "([^"]+)"', t, re.M)
        if not km:
            continue
        defs = str_defs(t)
        for name, stmt in file_theorems(t):
            s = " ".join(stmt.split())
            if "¬" in s:
                continue
            got = [x for m in re.finditer(r'hasSym ("(?:[^"\\]|\\.)*"|\w+) = false', s)
                   for x in (name_list(f"[{m.group(1)}]", defs) or [])]
            for m in re.finditer(r"\.filter \(!hasSym ·\.name\)\)\.map \(·\.name\) = (\[[^\[\]]*\])", s):
                got += name_list(m.group(1), defs) or []
            for x in got:
                nd[km.group(1)][x].append((name, rel))
    return nd


def model_theorems():
    """text -> [(theorem, file, statement)]: the theorems of kind "in a model" of the files
    test/LibParamExpand*.lean (a statement holding ∃ and ⊧ᴵP), each on its file's text."""
    out = defaultdict(list)
    for f in sorted(os.listdir(os.path.join(K, "test"))):
        if not MODEL_FILE.match(f):
            continue
        rel = "test/" + f
        t = open(os.path.join(K, rel)).read()
        um = re.search(r'user_axioms U from "([^"]+)"', t)
        if not um:
            continue
        defs = str_defs(t)
        for name, stmt in file_theorems(t):
            if "∃" in stmt and "⊧ᴵP" in stmt:
                s = stmt
                for d, v in defs.items():
                    s = re.sub(rf"\b{re.escape(d)}\b", '"' + v + '"', s)
                out[um.group(1)].append((name, rel, s))
    return out


DECL_CONTROL = ("f2-examples/silentflt.kompile.kore",
                "symbol:INT-COMMON:Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int",
                "Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int")
AX_CONTROL = ("f2-examples/silentflt.kompile.kore", 274, 296)
MODULE_CONTROL = ("module:STDIN-STREAM", "module:SORT-BOOL")
WHOLE_CONTROL = ("module:TIMER", "f2-examples/e6-mod-sort-kbott.kompile.kore")


def self_check(rows, res):
    """The self-check of forms (d) and (e): each `decls_entailed` of a declaration file is in a form
    of (d); each name of a symbol statement's list is a declaration of the file's text with a builtin
    Source, unhooked and without sort parameters; every symbol row held by a text of (d) that no list
    of (d) names is not tied, and is of no direction exactly where a fact of form (e) on a text holding
    it names its declaration; the control DECL_CONTROL (`dividesInt` on silentflt, which declares it
    without sort parameters and whose Γ lacks it) is held by that text's declaration files, named by no
    list of (d) on that text, and of form (e) there; and of AX_CONTROL's text, form (e2) takes the first sentence (`dividesInt`'s equation)
    and not the second (`findChar`'s, whose absent heads are `ite{SortInt}`, an instance of a symbol
    declared with sort parameters), although a statement naming the second and absentOf with a
    nonempty list literal exists; and of MODULE_CONTROL, the first module (STDIN-STREAM, which E6
    keys no row to but whose code holds rules) is not of the form of a module of hooks and generated
    declarations only, and the second (SORT-BOOL, one hooked sort) is."""
    forms, odd = decl_forms()
    bad = list(odd)
    for rel, (text, got) in sorted(forms.items()):
        ds = {(kind, nm): params for key, kind, nm, params in declarations(text) if not key.startswith("token:")}
        for th, k, names in got:
            for n in sorted(names or []) if k == "symbol" else []:
                if ds.get((k, n), True):
                    bad.append(f"{rel}: {th} names {n}, no unhooked {k} declaration of {text} with a builtin "
                               f"Source and without sort parameters")
    dties, held = decl_ties(forms)
    ndd = nodir_decls()
    named = {key for kd in dties.values() for key in kd}
    for key in sorted({k for h in held.values() for k in h}):
        if not key.startswith("symbol:") or key in named or key not in res:
            continue
        if isinstance(res[key], list):
            bad.append(f"{key}: named by no list of form (d), tied")
        e = any(ndd[t2].get(nm) for t2 in held if key in held[t2]
                for k2, _k, nm, _p in declarations(t2) if k2 == key)
        if e != is_nodir(res[key]):
            bad.append(f"{key}: of no direction {is_nodir(res[key])}, a fact of form (e) {e}")
    ctext, ckey, cname = DECL_CONTROL
    if ckey not in rows:
        bad.append(f"control {ckey}: not a row")
    elif ckey not in held.get(ctext, set()):
        bad.append(f"control {ckey}: not held by {ctext} in a file of form (d)")
    elif dties.get(ctext, {}).get(ckey):
        bad.append(f"control {ckey}: named by a list of form (d) on {ctext}")
    elif not ndd[ctext].get(cname):
        bad.append(f"control {ckey}: no fact of form (e) on {ctext}")
    text, yes, no = AX_CONTROL
    nda = nodir_axioms()
    stmts = [s for f in os.listdir(os.path.join(K, "test")) if ND_FILE.match(f)
             for _, s in file_theorems(open(os.path.join(K, "test", f)).read())
             if f'"{text}"' in open(os.path.join(K, "test", f)).read()]
    if not nda[text].get(yes):
        bad.append(f"control {text} axiom {yes}: not of form (e2)")
    if nda[text].get(no) or not any(re.search(rf"absentOf U\.ax{no} = \[\s*\"", s) for s in stmts):
        bad.append(f"control {text} axiom {no}: of form (e2), or no statement names it with absentOf and a "
                   f"nonempty list literal")
    mno, myes = MODULE_CONTROL
    if res.get(mno) is None or (isinstance(res[mno], list) and res[mno][0].startswith(HOOKS_ONLY)):
        bad.append(f"control {mno}: of the form of a module of hooks and generated declarations only, or no row")
    if not (isinstance(res.get(myes), list) and res[myes][0].startswith(HOOKS_ONLY)):
        bad.append(f"control {myes}: not of the form of a module of hooks and generated declarations only")
    wyes, wno = WHOLE_CONTROL
    if not (isinstance(res.get(wyes), list) and res[wyes] and WHOLE in res[wyes][0]):
        bad.append(f"control {wyes}: not of form (w)")
    wfiles = [f for f in os.listdir(os.path.join(K, "test")) if WHOLE_FILE.match(f)
              and f'user_axioms U from "{wno}"' in open(os.path.join(K, "test", f)).read()]
    if not wfiles or whole_ties().get(wno):
        bad.append(f"control {wno}: no tie file on it, or a whole-text tie (its `uncovered` holds a sentence)")
    for b in bad:
        print(f"e6map self-check: {b}")
    print(f"e6map self-check: {len(forms)} declaration files ({sum(1 for _, g in forms.values() if g)} with a "
          f"statement of form (d)), "
          f"{sum(len(g) for _, g in forms.values())} statements of form (d), {len(bad)} failures")
    return not bad


WHOLE_FILE = re.compile(r"^Tie\w*\.lean$")
WHOLE_THEOREMS = ("account", "account_absent", "absent_closed", "lists_in_account", "decls_entailed", "consistent")
WHOLE_UNCOVERED = re.compile(r"^def uncovered : List \(Nat × String\) :=\s*\[\s*\]\s*$", re.M)


def whole_ties():
    """text -> [(file, [theorem])]: the whole-text ties (form (w)), each tie file test/Tie*.lean on
    the text its `user_axioms U from "TEXT"` names that defines `uncovered` as the literal empty list
    and declares each theorem of WHOLE_THEOREMS, with those theorems."""
    out = defaultdict(list)
    for f in sorted(os.listdir(os.path.join(K, "test"))):
        if not WHOLE_FILE.match(f):
            continue
        rel = "test/" + f
        t = open(os.path.join(K, rel)).read()
        um = re.search(r'^user_axioms U from "([^"]+)"', t, re.M)
        if not um or not WHOLE_UNCOVERED.search(t):
            continue
        names = {n.split(".")[-1]: n for n, _ in file_theorems(t)}
        if all(x in names for x in WHOLE_THEOREMS):
            out[um.group(1)].append((rel, [names[x] for x in WHOLE_THEOREMS]))
    return out


def module_sentences(path):
    """module -> the number of the text's sentences (axioms and sort and symbol declarations, hooked
    ones included) whose builtin Source and Location place them in that module of K's builtin files."""
    out, cur = defaultdict(int), None
    sents = []
    for l in open(os.path.join(K, path)).read().split("\n"):
        if l.lstrip().startswith("//"):
            continue
        if re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol|claim|alias|import|axiom)\b", l) or \
                l.startswith("endmodule") or l.startswith("module "):
            if cur:
                sents.append(cur)
            cur = l if re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol|axiom)\b", l) else None
        elif cur:
            cur += "\n" + l
    if cur:
        sents.append(cur)
    for s in sents:
        sm, lm = SRC.search(s), LOC.search(s)
        if sm and lm and "/include/kframework/builtin/" in sm.group(1):
            out[module_at(os.path.basename(sm.group(1)), int(lm.group(1)))] += 1
    return out


def whole_tie(m, row, wties):
    """Form (w) for the module row of module m, or None: the row's `fixture` text has a whole-text tie
    (`whole_ties`) and holds a sentence the module's code places there; the items name the tie's
    theorems."""
    fx = row.get("fixture")
    text = f"f2-examples/{fx}.kompile.kore" if isinstance(fx, str) else None
    if not text or not wties.get(text):
        return None
    n = module_sentences(text).get(m, 0)
    if not n:
        return None
    return [f"{th} ({rel}; {text} whole text: {WHOLE}; the text holds {n} sentence{'' if n == 1 else 's'} of {m})"
            for rel, ths in wties[text] for th in ths]


WHOLE = "every axiom of its user module in one class of the account, none uncovered"


def compute():
    rows = tomllib.load(open(ROWS, "rb"))["E6"]
    ties = lean_ties()
    ktext, kt = kimp_ties()
    for n, l in kt.items():
        if not ties[ktext].get(n):
            ties[ktext][n] += l
    dties, dheld_by = decl_ties(decl_forms()[0])
    nda, ndd, models = nodir_axioms(), nodir_decls(), model_theorems()
    pla = paramlemma_ties()
    # key -> text -> [index]
    where = defaultdict(lambda: defaultdict(list))
    for text in sorted(set(ties) | set(nda) | set(pla) | {ktext}):
        seen = defaultdict(int)
        for i, _m, s in axioms(text):
            k = e6_key(s)
            if k:
                seen[k] += 1
                if seen[k] > 1 and f"{k}#{seen[k]}" in rows:
                    k = f"{k}#{seen[k]}"
                where[k][text].append(i)
    dnames = {}
    for text in dheld_by:
        for key, _kind, nm, _p in declarations(text):
            dnames[(text, key)] = nm
    scope = {k: v for k, v in rows.items()
             if (v["status"] == "supported" and k.split(":")[0] in ("axiom", "module", "sort", "symbol", "token"))
             or (v["status"] == "inert" and k.startswith("lemma:"))}
    res, modeled = {}, {}
    for k, v in scope.items():
        kind = k.split(":")[0]
        mod = k.split(":")[1] if kind != "token" else "(token sort)"
        if kind in ("axiom", "lemma"):
            got, other, nd, inm = [], [], [], False
            for text, ns in sorted(where.get(k, {}).items()):
                for n in ns:
                    for th, f, kind in ties[text].get(n, []):
                        (got if kind == "ties" else other).append(f"{th} ({f}; {text} axiom {n})" + (
                            "" if kind == "ties" else f" [{kind}]"))
                    for th, f in pla[text].get(n, []):
                        got.append(f"{th} ({f}; {text} axiom {n}; direction hypothesis)")
                    for th, f in nda[text].get(n, []):
                        nd.append(f"{th} ({f}; {text} axiom {n})")
                        inm = inm or any(re.search(rf"\bU\.ax{n}\b", s) for _, _, s in models.get(text, []))
            if got:
                res[k] = sorted(set(got))
            elif other:
                res[k] = (f"refuted: {mod}; no theorem entails the sentence; it is refuted (Γ with it has no "
                          f"model) or holds only where its set variables hold at most one value: "
                          + ", ".join(sorted(set(other))))
            elif nd:
                res[k] = f"no direction: {mod}; " + "; ".join(sorted(set(nd)))
                modeled[k] = inm
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
            nd, inm = [], False
            for text in dheld:
                nm = dnames.get((text, k))
                if kind == "symbol" and nm:
                    for th, f in ndd[text].get(nm, []):
                        nd.append(f"{th} ({f}; {text} symbol declaration {nm})")
                        inm = inm or any(f'"{nm}"' in s for _, _, s in models.get(text, []))
            if got:
                res[k] = sorted(set(got))
            elif nd:
                res[k] = f"no direction: {mod}; " + "; ".join(sorted(set(nd)))
                modeled[k] = inm
            else:
                res[k] = (f"uncovered: {mod}; a declaration held by {', '.join(dheld)}, tied there by no theorem"
                          if dheld else f"uncovered: {mod}; a declaration no tied text holds")
    mhooks, msents = module_hooks()
    wties = whole_ties()
    for k in scope:
        if k.startswith("module:"):
            m = k.split(":")[1]
            mine = [r for r in res if r.split(":")[1] == m and not r.startswith("module:")]
            tied = sum(1 for r in mine if isinstance(res[r], list))
            ndm = sum(1 for r in mine if modeled.get(r) is True)
            ndo = sum(1 for r in mine if modeled.get(r) is False)
            left = len(mine) - tied - ndm - ndo
            if mine and tied and not left and not ndo:
                res[k] = [f"every axiom, lemma, sort and symbol row of {m} ({len(mine)}) is tied"
                          + (f", or of no direction with a theorem in a model ({ndm})" if ndm else "")]
            elif not mine:
                res[k] = (whole_tie(m, rows[k], wties) or hooks_only(m, rows, mhooks, msents)
                          or f"uncovered: {m}; no axiom, lemma, sort or symbol row of the module")
            else:
                res[k] = (f"uncovered: {m}; {left} of its {len(mine)} axiom, lemma, sort and symbol rows uncovered"
                          + (f", {ndo + ndm} of no direction ({ndo} with no theorem in a model)" if ndo + ndm else ""))
    return scope, res


def is_nodir(v):
    return isinstance(v, str) and v.startswith("no direction: ")


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
    nodir = sum(1 for v in res.values() if is_nodir(v))
    for m in sorted(by):
        nd = [k for k in by[m] if is_nodir(res[k])]
        un = [k for k in by[m] if not isinstance(res[k], list) and not is_nodir(res[k])]
        print(f"{m}: {len(by[m]) - len(un) - len(nd)} tied, {len(nd)} no direction, {len(un)} uncovered")
        for k in by[m]:
            if isinstance(res[k], list):
                print(f"  tied {k}: {res[k][0]}" + (f" (+{len(res[k]) - 1})" if len(res[k]) > 1 else ""))
        for k in nd:
            print(f"  no direction {k}: {res[k].split('; ', 1)[1]}")
        for k in un:
            print(f"  uncovered {k}: {res[k].split('; ', 1)[1]}")
    print(f"e6map: {len(scope)} rows ({sum(1 for k in scope if scope[k]['status'] == 'supported')} supported, "
          f"{sum(1 for k in scope if scope[k]['status'] == 'inert')} inert lemma): {tied} tied, "
          f"{nodir} no direction, {len(scope) - tied - nodir} uncovered")
    if "--write" in sys.argv:
        print(f"e6map: e6_tie written on {write(res)} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
