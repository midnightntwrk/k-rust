"""DONE-0 C2's evidence per status, over every entry of test/constructs/rows.toml: each row of the
lists E1 to E8 and of [C3], and each table nested in a row's `cases` (recursively), `also_refused`
or `split`, as units.py walks them.

Usage (from kcore-spec):
  python3 -I test/constructs/rest.py [list] [--fresh] [--out FILE] [ROWS.toml]
      the entries FIX-core does not hold (below), grouped by list, status and evidence form, each
      with the evidence present and missing; prints the count per group, and every entry when no
      FILE is given (with FILE, the entries go there)
  python3 -I test/constructs/rest.py check [--report] [--fresh] [--gate] [--list LFILE] [--out FILE] [ROWS.toml]
      DONE-0 C2's check of every entry, FIX-core's included: an entry fails when an item its form
      needs is missing; prints per list and form how many entries have their evidence, and the
      failures (all of them into FILE, the first 40 on the output); with --list, also the list
      above (its entries into LFILE); exit 1 on a failure, exit 0 with --report (failures listed,
      not failing: test/constructs.sh's mode until the closing check of FIX-rest)
      Then the entries whose reading is owed (READER_OWED): every entry of status supported,
      parameter or inert with reader_does_it = false, with the ticket that owes the reading; exit 1
      (--report or not) on one that names no ticket, or whose ticket is done or not in PROGRESS
      (KCORE_PROGRESS, else ../progress beside kcore-spec, else the main checkout's, as units.py);
      with --gate (the completion gate), on every one
      Then the owed CondDecided (`owed_state`, rows-header.toml): exit 1 (--report or not) on an
      entry whose `fixture` or `also_fixtures` has an account.txt printing `CondDecided open` and
      that names no state for it; on a key that is neither a fixture of the entry nor named in its
      text; on a key whose account prints no `CondDecided open` unless its state is 'proved:
      THEOREM (FILE)' with THEOREM stated as a MatchIndependent and every text FILE reads
      (`definition_of`) that fixture's (f2-examples/FIXTURE.kompile.kore, or a text whose Source
      is fixtures/FIXTURE's .k file); on a state of no known form; on a
      theorem not declared, under its full name, in the state's FILE (a test/X.lean that
      test/integration.sh builds) or, without FILE, in a file of the entry's `tie`; on a
      fixture printing `CondDecided open` that no entry's `owed_state` keys; and on an entry none
      of whose states is proved where no state ends `; no fixture of this shape has it proved:
      REASON` (rows-header.toml: why no fixture of the entry's shape has the fact proved), or where
      one does beside a proved state. Prints the entries by their best fixture (proved, else open, else false)
  python3 -I test/constructs/rest.py --self-test
      the check on entries and fixtures written to a scratch directory, each accepted or refused
      as expected
  --fresh  `kcore account` of each fixture an entry names, from kfix.py's cache of its kompiled text
           (kfix.account_of: no kompile; the built .lake/build/bin/kcore, or $KCORE_BIN), compared
           with its account.txt. Without it the item `fresh account` is reported as not run and is
           missing (a check without --fresh fails on every entry that needs it).

The entries FIX-core holds (DONE-0 2.2 row FIX-core; the rest are FIX-rest's), with their nested
entries: a [C3] pair with `core = true`; a row with `notes`; a supported row of E6 keyed `hook:`; a
row whose `cone` names a cone declaration (it does not start with "none"; "as ROW" is that row's);
a row whose `fixture` or `also_fixtures` is a fixture of FIX-core's waves (WAVE below). The fields
`derived` and `tie` do not define the set: FIX-core writes them on rows already in it, and the
FIX-rest tickets write them on rows of the rest.

The evidence forms (DONE-0 C2's table), by status and list, and the items each needs:
  supported (E1, E2, E3, E7, E8, C3)
      fixture      `fixture` names a directory of fixtures/ (a nested entry: its own `fixture`)
      sentence     each `sentence` occurs in its kore.txt (or kompile.txt)
      clean        its account.txt refuses nothing: `parse: ok`, no `N refused` class line above 0,
                   `stage refusals ...: 0`, `refused by the account: 0`, no line `sentence I (...): R`
      fresh        the account equals a fresh one (--fresh)
      no direction (owed-sentence rule item 7, rows-header.toml; also on supported E4, E5) on an
                   entry with `no_direction`, or where a sentence `sentence` locates is of the
                   no-direction class: the class of a sentence is the one the fixture's tie gives
                   it (`classes` of the file of `tie`, else of test/, that reads
                   f2-examples/FIXTURE.kompile.kore; the indices AxiomDecl.index, a `// rule`
                   comment locating the axiom after it), never whether a sentence applies a symbol.
                   A declaration is no axiom and has no class: a `sentence` that locates no axiom
                   counts neither way, one that does not occur in that text is missing (its class
                   is not read). `no_direction` a non-empty list of indices of that class holding
                   each one `sentence` locates there; that tie file in `tie`; its account,
                   account_absent and absent_closed among tie_theorems; a `derived` table of form
                   (a), kind "in a model", whose sentences are the no_direction indices
      tie          `tie` lists the C14 tie modules: files test/X.lean that test/integration.sh
                   builds (not in its skip list)
      theorems     the theorems the entry names, `tie_theorems` (full names, each declared in a
                   file of `tie`) and the `theorem` of each `derived` table (declared in its
                   `file`): at least one, each declared
      removed      on an entry with `removed` (the sentences an option removes from a reference
                   text; any status): the fixture's `differs_from` names the reference, and of the
                   texts f2-examples/REFERENCE.kompile.kore and f2-examples/FIXTURE.kompile.kore,
                   each `sentence` N (counted from 1 over the reference text's axioms, as
                   AxiomDecl.index and `U.axN` count them) is an axiom of the reference's user
                   module and none of the fixture's text, and every axiom of the reference absent
                   from the fixture's text is listed (axioms compared with whitespace runs one
                   space, Location, Source and UNIQUE'Unds'ID dropped and generated variables
                   renumbered within each); each `theorem` and `companion` is declared in its
                   `file`, which reads the reference text
  supported E4, E5
      fixture, clean, fresh, tie, theorems as above; node: the fixture's kompiled sentences (kore.txt,
      or the text of a `kore` fixture) hold the row's node or translation site, found by
      test/constructs/e4e5.py's parse of the text when that module exists, else by `sentence`;
      with `node_sentence`, the sentence of the fixture's cached kompiled definition whose first
      line contains it holds the node (e4e5.py)
  supported hook (E6, key hook:)
      derived      a `derived` table of form (a) (the in-domain value; FIX-core.rows-evidence names
                   the hook's three statements there)
  supported function of the text (a table nested in an E6 `hook:` row, whose fixture's reading
  takes the row's symbol for no hook: the fixture's params.txt, the `param` lines of `kcore
  sem-fields`, lists no parameter implemented by it, `impl=SYMBOL` with SYMBOL the key's last part;
  the entry reads a symbol of the text of that name, so the hook's in-domain value is not its
  evidence)
      fixture, sentence, clean, fresh, no direction, tie, theorems as for supported (E1, ...)
  supported E6 (other keys)
      tie, theorems (the theorem that ties the row's sentence on a tied text); or the row's
                   `e6_tie` (test/constructs/e6map.py): each "THEOREM (FILE; TEXT axiom N)" a
                   theorem declared in FILE, a tie file as above; on a module row "every ... row
                   of MODULE (n) is tied", with ", or of no direction with a theorem in a model (k)"
                   where k are; an item "uncovered: ...", "refuted: ..." (Γ refutes the sentence or
                   entails it only partly) or "no direction: ..." (the tie's no-direction class) is
                   missing evidence
  parameter
      derived      a `derived` table of form (c): the param_undetermined instance
  parameter (no model) (a parameter entry with a `derived` table of form (r): its fixture's text
  has no model, so no param_undetermined instance exists there; counted apart)
      derived      a `derived` table of form (r)
  inert
      class        `inert_class` or a `reasons` item InertReason.X: a constructor of InertReason
                   (an E6 row keyed lemma: is a [simplification] axiom, of class simplification);
                   where the entry has a fixture, its account prints `N inert X` with N above 0
      tie, theorems (C14's statement for the class: Γ c ⊧ tr s); for an E6 row, its e6_tie as above
  inert of class attribute (`inert_class = "attribute"`): an attribute of a read sentence or
  declaration to which K gives no meaning
      attribute    `attribute`, the attribute's head as KORE writes it (UNIQUE'Unds'ID, cool-like, unit)
      pairs        `attr_pairs`, pairs [TEXT, COMPANION] of texts f2-examples/*.kore: the two differ,
                   and are equal once every attribute of that head is removed from both (and kfix.py's
                   stripped applied: Source, Location, comments and module names); at least one
      tie          `tie` holds a file that reads the fixture's own text (f2-examples/FIXTURE.kompile.kore,
                   or a text f2-examples/*.kore byte for byte the one kompile.txt records, its paths
                   restored as tiegen writes it), other than test/InertSemPairs.lean
      theorems     as above, among them KCore.InertSemPairs.trS_attrs (the translation of a sentence
                   reads none of its attributes); `reader_tests` (a sem_eq of the pair: the reader
                   builds one semantics from both) are not evidence and are not counted
      reason       a reason sentence (`reason`): why K gives the attribute no meaning
  inert of class use: also refused where the entry's fixture differs from its companion (its
      fixture.toml has `differs_from`, or the entry has `attr_pairs`): class use is DONE-0 C1's
      (proof tasks, solver encodings, parsing and unparsing of programs), never a text difference
  inert of class use (`inert_class = "use"`)
      reason       a reason sentence (`reason`): C1's class use
  erased (findings/work/decision-fixrest-erased-forms.md section 4): at least one of the forms
  ERASED_FORMS, each the entry carries checked (conjoined)
      P pair       each fixture `pair` names (one or a list), else the first of the entry's fixtures
                   recording one, has kompile.txt `same_as OTHER: equal after stripping`
      S absent     each pattern found in no kompiled text in scope (kfix.check_absent: the native
                   scan of every fixture's kompiled text and of the corpus; a text held nowhere fails)
      O other_file the entry's fixture keeps that file's lines in other.txt, each `witness` there and
                   in no sentence of its definition.kore (kfix.check_other)
      C carried_by "<list> <row key>": that row is not erased and has its own evidence here, and the
                   entry's `sentence` occurs in that row's fixture
  refused
      reasons      `reasons` holds RefusalReason.X items
      account      a fixture of the entry (`fixture`, `also_fixtures`) whose account prints each of
                   them (a refusal line or a class line, as closed.py reads accounts); or, for an
                   entry kompile refuses (unit "none (scope): rejected", or class R-b with an error
                   fixture), its fixture is an error fixture (fixture.toml expect = "error") and
                   `reasons` is not needed; or, for an option that writes no definition (unit
                   "none (scope): option", `shape` "none: ..."), a fixture of the entry whose
                   kompile.txt holds `definition.kore: none written`, and `reasons` is not needed
      scope        instead of a RefusalReason, on an E8 option row of class R-b or scope (the row's
                   key the option): `reasons` holds SCOPE_OPTION ("none (scope): option"), and a
                   fixture of the entry has kompile.txt's `command:` passing the option outside R-12's
                   option set (an argument other than `--backend haskell`, or `--backend` with another
                   value); RefusalReason items beside it are checked as above (what the reader answers
                   on the text the option gives); the item on another entry is missing evidence
      fresh        as above, for a fixture that has an account
      reason       a reason sentence (`reason`, `reader_reason` or `refused_by`)
  independent (a [C3] pair)
      declarations `declarations`, the two declarations that read the pair's modifiers
  pending-fixture, not-handled
      none: such an entry always fails (DONE-0 C2: not a status at T_DONE)
An entry with no `status` (a nested table that only records a shape) is not checked.
"""
import collections, os, re, shutil, sys, tempfile, tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
K = os.path.dirname(os.path.dirname(HERE))
sys.dont_write_bytecode = True  # no __pycache__ in the tree
sys.path.insert(0, HERE)

LISTS = ["E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "C3"]
KLEVEL = {"E1", "E2", "E3", "E7", "E8", "C3"}
WAVE = re.compile(r"^(e2-unbound|e2-rule|e2-clause-.*|e6-rangemap)$")
ERASED_FORMS = ["P", "S", "O", "C"]
# The `reasons` item of an E8 option row refused for scope: the option is outside R-12's option set,
# whatever the reader answers on the text it gives (closed.py admits it beside the constructors).
SCOPE_OPTION = "none (scope): option"
# R-12's option set: `kompile --backend haskell MAIN`; every other option, or another value of this
# one, is outside it.
R12_OPTIONS = {"--backend": "haskell"}
STATUSES = ["supported", "parameter", "inert", "erased", "refused", "independent",
            "pending-fixture", "not-handled"]


# ------------------------------------------------------------------------------------- the entries

def nested(e):
    """The tables nested in an entry: its `cases` (and theirs), `also_refused`, `split`."""
    for f in ("cases", "also_refused", "split"):
        v = e.get(f)
        for i, c in enumerate(v if isinstance(v, list) else [v]):
            if isinstance(c, dict):
                yield f"{f}[{i}]" + (f" ({str(c['case'])[:40]!r})" if "case" in c else ""), c
                for w, d in nested(c):
                    yield f"{f}[{i}].{w}", d


def entries(t):
    """(list, row key, where, entry, row) for every row and every table nested in one."""
    for l in LISTS:
        for key, r in (t.get(l) or {}).items():
            if not isinstance(r, dict):
                continue
            yield l, key, f"{l} {key!r}", r, r
            for w, c in nested(r):
                yield l, key, f"{l} {key!r} {w}", c, r


def cone_decl(t, l, r, seen=()):
    """Whether the row's `cone` names a cone declaration ("as ROW" follows that row)."""
    c = r.get("cone")
    if not isinstance(c, str) or c.startswith("none"):
        return False
    m = re.match(r"as (\S+)$", c)
    if m:
        k = next((k for k in (t.get(l) or {}) if k.startswith(m[1].split("@")[0] + "(")
                  and k.endswith("@" + m[1].split("@")[-1])), None)
        return bool(k) and k not in seen and cone_decl(t, l, t[l][k], seen + (k,))
    return True


def core(t, l, key, r):
    """Why FIX-core holds the row, or None."""
    if l == "C3" and r.get("core"):
        return "C3 core pair"
    if r.get("notes"):
        return "reading notes"
    if l == "E6" and key.startswith("hook:") and r.get("status") == "supported":
        return "supported hook"
    if cone_decl(t, l, r):
        return "cone declaration"
    fx = [r.get("fixture")] + list(r.get("also_fixtures") or [])
    if any(isinstance(f, str) and WAVE.match(f) for f in fx):
        return "wave fixture"
    return None


def hook_own(fx, key, e, row):
    """Whether a table nested in an E6 `hook:` row reads the row's symbol as a function of the text,
    not as the hook: its fixture's params.txt (the `param` lines of `kcore sem-fields`) lists no
    parameter implemented by the symbol (`impl=SYMBOL`, SYMBOL the key's last part). False for the
    row itself and where the fixture has no params.txt (the reading is not shown)."""
    if fx is None or e is row or not key.startswith("hook:") or key.count(":") < 2:
        return False
    x = e.get("fixture")
    p = fx.read(x, "params.txt") if fx.exists(x) else None
    if p is None:
        return False
    sym = key.split(":", 2)[2]
    return not any(len(c) > 1 and c[0] == "param" and f"impl={sym}" in c[1:]
                   for c in (ln.split("\t") for ln in p.splitlines()))


def form(l, key, e, row=None, fx=None):
    """The evidence form of DONE-0 C2's table for the entry's status, or None without a status.
    With the entry's row and the fixtures, a table nested in an E6 `hook:` row whose reading takes
    the symbol for a function of the text has that form (`hook_own`)."""
    s = e.get("status")
    if s is None:
        return None
    if s == "supported":
        if l == "E6" and hook_own(fx, key, e, row):
            return "supported function of the text"
        return ("supported" if l in KLEVEL else "supported E4/E5" if l in ("E4", "E5") else
                "supported hook" if key.startswith("hook:") else "supported E6")
    if s == "parameter" and any(isinstance(d, dict) and d.get("form") == "r" for d in (e.get("derived") or [])):
        return "parameter (no model)"
    if s == "inert" and e.get("inert_class") == "use":
        return "inert (use)"
    if s == "inert" and e.get("inert_class") == "attribute":
        return "inert (attribute)"
    return s


# ------------------------------------------------------------------------------- fixture evidence

class Fixtures:
    """The fixtures of a directory: account.txt as closed.py reads it, kore.txt, kompile.txt,
    fixture.toml, and the fresh accounts (--fresh)."""

    def __init__(self, fx, fresh, rows=None):
        self.fx, self.fresh, self._acc, self._fresh, self._text = fx, fresh, {}, {}, {}
        self.ctors = constructors()
        self.rows = rows

    def check_absent(self, e):
        """Form S of an erased entry (kfix.check_absent: the scan of the texts in scope)."""
        try:
            import kfix
            return kfix.check_absent(e)
        except (Exception, SystemExit) as err:
            return False, f"absent: the scan did not run: {str(err)[:100]}"

    def check_other(self, e, own):
        """Form O of an erased entry (kfix.check_other) on this directory's fixtures."""
        try:
            import kfix
            return kfix.check_other(e, own, read=self.read)
        except (Exception, SystemExit) as err:
            return False, f"other_file: not checked: {str(err)[:100]}"

    def exists(self, name):
        return isinstance(name, str) and name != "none" and os.path.isdir(os.path.join(self.fx, name))

    def kompiled(self, name):
        """The fixture's kompiled text as tiegen.py and the tie files read it."""
        return os.path.join(K, "f2-examples", f"{name}.kompile.kore")

    def read(self, name, f):
        p = os.path.join(self.fx, name, f)
        return open(p).read() if os.path.isfile(p) else None

    def conf(self, name):
        p = os.path.join(self.fx, name, "fixture.toml")
        return tomllib.load(open(p, "rb")) if os.path.isfile(p) else {}

    def text(self, name):
        """The sentences a row can point into: kore.txt and kompile.txt, or a `kore` fixture's text."""
        if name not in self._text:
            parts = [self.read(name, f) or "" for f in ("kore.txt", "kompile.txt")]
            c = self.conf(name)
            if isinstance(c.get("kore"), str) and os.path.isfile(os.path.join(K, c["kore"])):
                parts.append(open(os.path.join(K, c["kore"])).read())
            self._text[name] = "".join(parts)
        return self._text[name]

    def account(self, name):
        """(names printed: set of (inductive, constructor), refusal reasons printed, refuses
        nothing), or None without account.txt."""
        if name not in self._acc:
            a = self.read(name, "account.txt")
            if a is None:
                self._acc[name] = None
            else:
                names, refusals = set(), set()
                for n, word, r in CLASSLINE.findall(a):
                    ind = CLASSWORD[word]
                    if int(n) > 0:
                        names.add((ind, r))
                        if word == "refused":
                            refusals.add(r)
                for r in REFUSAL.findall(a):
                    names.add(("RefusalReason", r)); refusals.add(r)
                for start, r in COUNTED:
                    if re.search(r"^" + re.escape(start) + r"[1-9]", a, re.M):
                        names.add(("RefusalReason", r)); refusals.add(r)
                clean = (bool(re.search(r"^parse: ok\b", a, re.M)) and not refusals
                         and bool(re.search(r"^stage refusals \(of sentences classified read\): 0$", a, re.M))
                         and bool(re.search(r"^refused by the account: 0$", a, re.M)))
                self._acc[name] = (names, refusals, clean)
        return self._acc[name]

    def nodir_tie(self, name, ties):
        """The tie file of the fixture whose classes give a sentence's class: a file of `ties`, else
        any test/*.lean, that reads f2-examples/NAME.kompile.kore and defines `classes`; or None."""
        want = f"f2-examples/{name}.kompile.kore"
        own = [f for f in ties if isinstance(f, str) and (nodir_classes(f) or ("",))[0] == want]
        if own:
            return own[0]
        return next((f for f in nodir_tie_files() if nodir_classes(f)[0] == want), None)

    def located(self, path, ss):
        """(the indices of the user module's axioms of the text at path that the substrings locate,
        in an axiom's text or in the `//` comment lines just before it; the substrings that do not
        occur in that text). A substring of the text that locates no axiom (a declaration, a module's
        attributes) adds no index: a declaration is no axiom and has no class."""
        p = os.path.join(K, path)
        body = open(p).read() if os.path.isfile(p) else ""
        out, absent = set(), []
        for s in ss:
            if s not in body:
                absent.append(s)
                continue
            out |= {i for i, text, notes in nodir_axioms(path) if s in text or any(s in n for n in notes)}
        return out, absent

    def fresh_equal(self, name):
        """True / False: the account against a fresh one; otherwise why it was not compared: "not
        run" (no --fresh) or "not in the cache" (kfix.py's cache lacks the kompiled text)."""
        if not self.fresh:
            return "not run"
        if name not in self._fresh:
            try:
                import kfix
                got = kfix.account_of(name, kfix.conf(name))
                self._fresh[name] = "not in the cache" if got is None else got == self.read(name, "account.txt")
            except (Exception, SystemExit) as err:  # no K installation, no kcore binary, ...
                self._fresh[name] = f"not compared: {str(err)[:80]}"
        return self._fresh[name]


INDUCTIVES = ["RefusalReason", "InertReason", "UnreadReason", "ReadingNote"]
CLASSWORD = {"refused": "RefusalReason", "inert": "InertReason", "unread": "UnreadReason",
             "read": "ReadingNote"}
CLASSLINE = re.compile(r"^\s+(\d+) (refused|inert|unread|read) (\w+) \[", re.M)
REFUSAL = re.compile(r"(?:sentence \d+|the module) \(.*?\): (\w+)(?: \(.*\))?$", re.M)
COUNTED = [("sentences the library's data induces that the text does not hold: ", "builtinIncomplete"),
           ("library sentences of the modules held that the text does not hold: ", "builtinIncomplete")]


def constructors():
    src = open(os.path.join(K, "KcoreSpec/Parse.lean")).read()
    out = {}
    for ind in INDUCTIVES:
        block = src.split(f"\ninductive {ind} where\n", 1)[1].split("\n  deriving", 1)[0]
        out[ind] = re.findall(r"^  \| (\w+)", block, re.M)
    return out


# ----------------------------------------------------------------------------- Lean declarations

def integration_skips():
    """The test/X.lean files test/integration.sh does not build: those of its `case ... continue`
    list that neither it (outside that list) nor a test/*.sh script it runs names as test/X.lean
    (Pins, Axioms, ... have rows of their own; TieKimpAtValues and its siblings are built by
    test/imp-tie-atvalues.sh)."""
    src = open(os.path.join(K, "test/integration.sh")).read()
    m = re.search(r"case \$\(basename \"\$f\" \.lean\) in\n\s*([^)]*)\) continue;;", src)
    skip = set(m[1].split("|")) if m else set()
    built = set(re.findall(r"\btest/(\w+)\.lean\b", src.replace(m[0], "") if m else src))
    for sh in sorted(set(re.findall(r"\btest/([\w-]+\.sh)\b", src))):
        p = os.path.join(K, "test", sh)
        if os.path.isfile(p) and sh != "integration.sh":
            built |= set(re.findall(r"\btest/(\w+)\.lean\b", open(p).read()))
    return skip - built


SKIPS = None


def tie_file_ok(f):
    """Why the tie file is not one integration.sh builds, or None."""
    global SKIPS
    if SKIPS is None:
        SKIPS = integration_skips()
    if not isinstance(f, str) or not re.match(r"^test/[^/]+\.lean$", f):
        return f"{f!r} is not test/X.lean"
    if not os.path.isfile(os.path.join(K, f)):
        return f"{f} does not exist"
    if os.path.basename(f)[:-5] in SKIPS:
        return f"{f} is in test/integration.sh's skip list"
    return None


_decls = {}


def file_decls(f):
    """The full names the file declares (namespaces tracked by their `namespace` lines; a textual
    check, as provenance.sh's), or None where it is no file."""
    p = os.path.join(K, f) if isinstance(f, str) else None
    if not p or not os.path.isfile(p):
        return None
    if f not in _decls:
        src = re.sub(r"/-.*?-/", "", open(p).read(), flags=re.S)
        src = re.sub(r"--.*", "", src)
        decls = set()
        stack = []
        for line in src.split("\n"):
            s = line.strip()
            m = re.match(r"namespace (\S+)", s)
            if m:
                stack.append(m[1]); continue
            m = re.match(r"end (\S+)$", s)
            if m and stack and stack[-1] == m[1]:
                stack.pop(); continue
            m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                         r"(?:theorem|lemma|def|abbrev|instance|example) ([^\s:({\[]+)", s)
            if m:
                d = m[1].strip("«»")
                decls.add(".".join(stack + [d]) if not d.startswith("_root_.") else d[7:])
        _decls[f] = decls
    return _decls[f]


_ndcls, _ndfiles, _ndax = {}, None, {}


def nodir_classes(f):
    """(the text the tie file reads by `kore_term kore from`, {AxiomDecl.index: class}) from its
    `classes` (the account the kernel checks), or None where it has no such text or no classes."""
    if f not in _ndcls:
        p = os.path.join(K, f) if isinstance(f, str) else None
        r = None
        if p and os.path.isfile(p):
            src = open(p).read()
            m = re.search(r'^kore_term kore from "([^"]+)"', src, re.M)
            i = src.find("\ndef classes : List (String × List Nat) :=")
            if m and i >= 0:
                body = src[i + 1:].split("\n\n", 1)[0]
                cls = {int(n): name for name, nums in re.findall(r'\("([^"]+)", \[([^\]]*)\]\)', body)
                       for n in re.findall(r"\d+", nums)}
                r = (m[1], cls)
        _ndcls[f] = r
    return _ndcls[f]


def nodir_tie_files():
    """The files test/*.lean that read a text and define `classes`."""
    global _ndfiles
    if _ndfiles is None:
        d = os.path.join(K, "test")
        _ndfiles = [f"test/{n}" for n in sorted(os.listdir(d)) if n.endswith(".lean")
                     and nodir_classes(f"test/{n}")]
    return _ndfiles


def nodir_axioms(path):
    """[(index, text, comments)] of the axioms of the text's last module, index counted from 1 over
    every axiom of the text (AxiomDecl.index, the numbering of a tie's `classes`), text its lines up
    to a blank line, a declaration or a comment line, comments the `//` lines just before it."""
    if path not in _ndax:
        p = os.path.join(K, path)
        lines = open(p).read().split("\n") if os.path.isfile(p) else []
        out, cur, mod, notes = [], None, None, []
        for line in lines:
            s = line.strip()
            m = re.match(r"module (\S+)", s)
            if m:
                mod = m[1]
            if re.match(r"axiom\s*\{", s):
                if cur:
                    out.append(cur)
                cur = [len(out) + 1, mod, [line], notes]
                notes = []
                continue
            if cur is not None and (s == "" or re.match(r"(sort|symbol|hooked-sort|hooked-symbol|alias|endmodule"
                                                        r"|import|//)", s)):
                out.append(cur); cur = None
            if cur is not None:
                cur[2].append(line)
            elif s.startswith("//"):
                notes.append(s)
            elif s:
                notes = []
        if cur:
            out.append(cur)
        um = out[-1][1] if out else None
        _ndax[path] = [(i, "\n".join(ls), ns) for i, m, ls, ns in out if m == um]
    return _ndax[path]


def nodir_items(fx, e, x, have, miss):
    """Owed-sentence rule item 7 (rows-header.toml, field no_direction) on a supported entry whose
    fixture is x: the class of each sentence is read from the fixture's tie (`classes`)."""
    nd = e.get("no_direction")
    ts = e.get("tie")
    ts = ts if isinstance(ts, list) else [ts] if ts else []
    tf = fx.nodir_tie(x, ts) if x else None
    text, cls = nodir_classes(tf) if tf else (None, {})
    ss = e.get("sentence")
    ss = ss if isinstance(ss, list) else [ss] if isinstance(ss, str) else []
    loc, absent = fx.located(text, ss) if tf and ss else (set(), [])
    loc_nd = {i for i in loc if cls.get(i) == "no direction"}
    if absent:
        miss.append(f"sentence {absent[0][:50]!r} not in {text}, the text of {tf}: its class is not read")
    if nd is None and not loc_nd:
        return
    if tf is None:
        miss.append(f"no-direction class (no file test/X.lean reads f2-examples/{x}.kompile.kore with its classes)")
        return
    if nd is None:
        miss.append(f"no_direction (sentences `sentence` locates are of the no-direction class of {tf}:"
                    f" {sorted(loc_nd)})")
        nd = []
    elif not (isinstance(nd, list) and nd and all(isinstance(i, int) and not isinstance(i, bool) for i in nd)):
        miss.append("no_direction (not a non-empty list of sentence indices)")
        nd = []
    else:
        out = [i for i in nd if cls.get(i) != "no direction"]
        ok = not out and loc_nd <= set(nd)
        (have if ok else miss).append(
            f"no_direction {sorted(nd)} in the no-direction class of {tf}" if ok else
            "no_direction (" + (", ".join(f"{i} is of class {cls.get(i, 'none: no sentence of the user module')}"
                                          for i in out[:3]) if out else
                                f"{sorted(loc_nd - set(nd))} located by `sentence`, of that class, not listed")
            + f" in {tf})")
    if tf not in ts:
        miss.append(f"tie ({tf}, the tie whose classes hold the no-direction sentences, not in tie)")
    names = [n for n in (e.get("tie_theorems") or []) if isinstance(n, str)]
    lack = [t for t in ("account", "account_absent", "absent_closed")
            if not any(n.endswith("." + t) and declared(n, [tf]) for n in names)]
    (have if not lack else miss).append(
        f"the class's statement ({tf}: account, account_absent, absent_closed)" if not lack else
        f"the class's statement ({', '.join(lack)} of {tf} not in tie_theorems)")
    tabs = [d for d in (e.get("derived") or []) if isinstance(d, dict) and d.get("form") == "a"
            and d.get("kind") == "in a model" and isinstance(d.get("sentences"), list)]
    hit = [d for d in tabs if nd and set(d["sentences"]) == set(nd)]
    (have if hit else miss).append(
        "derived form a, in a model" if hit else
        "derived of form a, kind 'in a model', whose sentences are the no_direction indices"
        + (f" ({len(tabs)} of that kind with other sentences)" if tabs else ""))


def declared(name, files):
    """Whether the full name is declared in one of the files (a declaration's name may also be a
    suffix of it)."""
    for f in files:
        ds = file_decls(f)
        if ds is not None and (name in ds or any(name.endswith("." + d) for d in ds)):
            return True
    return False


# ------------------------------------------------------------------------------------- evidence

def option_passed(fx, x, opt):
    """The fixture's kompile.txt `command:` line passes the option `opt` outside R-12's option set:
    `opt` is an argument of the command, with a value other than R-12's where R-12 sets one."""
    m = re.search(r"^command: kompile (.*?)(?:  \(cwd: [^)]*\))?$", fx.read(x, "kompile.txt") or "", re.M)
    args = m[1].split() if m else []
    if opt not in args:
        return False
    i = args.index(opt)
    return opt not in R12_OPTIONS or args[i + 1:i + 2] != [R12_OPTIONS[opt]]


def evidence(fx, l, key, e, row):
    """(present, missing): two lists of strings, the items of the entry's form (module docstring)."""
    f = form(l, key, e, row, fx)
    have, miss = [], []
    item = lambda ok, yes, no: (have if ok else miss).append(yes if ok else no)
    own = [x for x in [e.get("fixture")] + list(e.get("also_fixtures") or []) if fx.exists(x)]
    named = [x for x in [e.get("fixture")] + list(e.get("also_fixtures") or [])
             if isinstance(x, str) and x != "none"]
    for x in named:
        if not fx.exists(x):
            miss.append(f"fixture {x} (no directory)")

    def fixture_items(clean_needed):
        if not own:
            miss.append("fixture"); return None
        x = own[0]
        have.append(f"fixture {x}")
        if "sentence" in e:
            ss = e["sentence"] if isinstance(e["sentence"], list) else [e["sentence"]]
            out = [s for s in ss if s not in fx.text(x)]
            item(not out, "sentence", f"sentence {out[0][:50]!r} not in {x}" if out else "")
        a = fx.account(x)
        if a is None:
            miss.append(f"account ({x} has no account.txt)")
        elif clean_needed:
            item(a[2], "account refuses nothing", f"account refuses nothing ({x}'s refuses "
                 + (", ".join(sorted(a[1])) or "something: parse, stage or account line") + ")")
        if a is not None:
            fr = fx.fresh_equal(x)
            item(fr is True, "fresh account", "fresh account (" + ("differs" if fr is False else str(fr)) + ")")
        return x

    def ties():
        if l == "E6" and e.get("e6_tie") is not None:
            return e6_ties()
        ts = e.get("tie")
        ts = ts if isinstance(ts, list) else [ts] if ts else []
        if not ts:
            miss.append("tie"); ok = False
        else:
            why = [w for w in map(tie_file_ok, ts) if w]
            item(not why, "tie " + ", ".join(ts), "tie (" + "; ".join(why) + ")")
            ok = not why
        thms = [(n, ts) for n in (e.get("tie_theorems") or [])]
        thms += [(d.get("theorem"), [d.get("file")]) for d in (e.get("derived") or [])
                 if isinstance(d, dict) and d.get("theorem")]
        if not thms:
            miss.append("theorems")
        else:
            bad = [n for n, fs in thms if not declared(n, fs)]
            item(not bad, f"theorems ({len(thms)})", f"theorems ({', '.join(bad[:2])} not declared)")
        return ok

    def e6_ties():
        """An E6 library row's `e6_tie` (test/constructs/e6map.py): "THEOREM (FILE; TEXT axiom N)" items,
        "every ... row of MODULE (n) is tied" on a module row, or "uncovered: ..."."""
        v = e.get("e6_tie")
        v = v if isinstance(v, list) else [v]
        unc = [x for x in v if isinstance(x, str) and x.startswith("uncovered")]
        if unc or not v:
            miss.append("theorems (e6_tie: " + (unc[0][:80] if unc else "empty") + ")"); return False
        nd = [x for x in v if isinstance(x, str) and x.startswith("no direction: ")]
        if nd:
            miss.append("theorems (e6_tie: " + nd[0].split(";")[0] + ": of the tie's no-direction class, which"
                        " no theorem entails; owed-sentence rule item 7)"); return False
        ref = [x for x in v if isinstance(x, str) and x.startswith("refuted")]
        if ref:
            miss.append("theorems (e6_tie: " + ref[0].split(";")[0] + ": Γ refutes the sentence or entails it"
                        " only partly, no tie; a finding for DONE-0 2.6)"); return False
        if all(isinstance(x, str) and re.match(r"every .* row of \S+ \(\d+\) is tied"
                                               r"(, or of no direction with a theorem in a model \(\d+\))?$", x) for x in v):
            have.append("tie: every row of the module tied (e6_tie)"); return True
        thms = [re.match(r"(\S+) \((test/[^;]+\.lean); .+\)$", x) if isinstance(x, str) else None for x in v]
        if not all(thms):
            miss.append(f"theorems (e6_tie item of no known form: {next(x for x, m in zip(v, thms) if not m)!r:.80})")
            return False
        files = sorted({m[2] for m in thms})
        why = [w for w in map(tie_file_ok, files) if w]
        item(not why, "tie " + ", ".join(files) + " (e6_tie)", "tie (e6_tie: " + "; ".join(why) + ")")
        bad = [m[1] for m in thms if not declared(m[1], [m[2]])]
        item(not bad, f"theorems ({len(thms)}, e6_tie)", f"theorems (e6_tie: {', '.join(bad[:2])} not declared)")
        return not why

    def derived(forms):
        ds = [d for d in (e.get("derived") or []) if isinstance(d, dict)]
        got = [d for d in ds if d.get("form") in forms]
        item(bool(got), f"derived form {'/'.join(forms)} ({len(got)})", f"derived of form {'/'.join(forms)}")

    def reason_sentence(fields):
        ok = any(isinstance(e.get(x), str) and e[x].strip() for x in fields)
        item(ok, "reason", "reason sentence")

    if f is None:
        return have, miss
    if f in ("pending-fixture", "not-handled"):
        miss.append(f"a status ({f} is none of DONE-0 C2's five)")
    elif f == "supported":
        x = fixture_items(True); ties()
        nodir_items(fx, e, x, have, miss)
    elif f == "supported E4/E5":
        x = fixture_items(True)
        if x:
            ok, how = node_held(fx, l, key, x, e)
            item(ok, f"node ({how})", f"node ({how})")
        ties()
        nodir_items(fx, e, x, have, miss)
    elif f == "supported hook":
        derived(["a"])
    elif f == "supported function of the text":
        x = fixture_items(True); ties()
        nodir_items(fx, e, x, have, miss)
    elif f == "supported E6":
        ties()
    elif f == "parameter":
        derived(["c"])
    elif f == "parameter (no model)":
        derived(["r"])
    elif f == "inert (use)":
        reason_sentence(["reason"])
        comp = [x for x in own if fx.conf(x).get("differs_from")]
        item(not comp and not e.get("attr_pairs"), "no companion (C1's class use)",
             "class use on a text difference (" + (f"{comp[0]} differs_from {fx.conf(comp[0])['differs_from']}"
                                                  if comp else "attr_pairs") + "): use is C1's class only")
    elif f == "inert (attribute)":
        attribute_items(fx, e, own, item, miss)
        ties()
        if "KCore.InertSemPairs.trS_attrs" not in (e.get("tie_theorems") or []):
            miss.append("theorems (KCore.InertSemPairs.trS_attrs not named)")
        reason_sentence(["reason"])
    elif f == "inert":
        cls = [c for c in [e.get("inert_class")] + [x.split(".", 1)[1] for x in (e.get("reasons") or [])
               if isinstance(x, str) and x.startswith("InertReason.")] if isinstance(c, str)]
        cls = [c for c in cls if c in fx.ctors["InertReason"]]
        if not cls and l == "E6" and key.startswith("lemma:"):
            cls = ["simplification"]        # E6's key: the sentence is a [simplification] axiom
        if not cls:
            miss.append("class (InertReason)")
        else:
            have.append(f"class {cls[0]}")
            if own and fx.account(own[0]) is not None:
                shown = [c for c in cls if ("InertReason", c) in fx.account(own[0])[0]]
                item(bool(shown), f"account prints inert {cls[0]}", f"account prints inert {cls[0]} ({own[0]})")
        ties()
    elif f == "erased":
        letters = erased_forms(fx, l, key, e, have, miss)
        if not letters:
            miss.append("a form of erased (P pair, S absent, O other_file, C carried_by)")
    elif f == "refused":
        rs = [x.split(".", 1)[1] for x in (e.get("reasons") or [])
              if isinstance(x, str) and x.startswith("RefusalReason.")]
        err = [x for x in own if (fx.conf(x).get("expect") == "error")]
        kompile_refuses = bool(err) and (e.get("unit") == "none (scope): rejected" or e.get("class") == "R-b")
        nodef = [x for x in own if re.search(r"^definition\.kore: none written$", fx.read(x, "kompile.txt") or "", re.M)]
        option = (e.get("unit") == "none (scope): option" and isinstance(e.get("shape"), str)
                  and e["shape"].startswith("none: "))
        scope = SCOPE_OPTION in (e.get("reasons") or [])
        if kompile_refuses:
            have.append(f"kompile refuses ({err[0]})")
        elif option and nodef:
            have.append(f"kompile writes no definition ({nodef[0]})")
        elif scope and not (l == "E8" and e.get("class") in ("R-b", "scope")):
            miss.append(f"{SCOPE_OPTION!r} (only on an E8 option row of class R-b or scope)")
        else:
            passed = [x for x in own if option_passed(fx, x, key)] if scope else []
            if scope:
                item(bool(passed), f"scope: option {key} outside R-12 ({passed[0] if passed else ''} kompile.txt)",
                     f"scope: no fixture of the entry whose kompile.txt command passes {key} outside R-12"
                     + (f" ({', '.join(own)})" if own else " (no fixture)"))
            else:
                item(bool(rs), "reasons " + ", ".join(rs), "reasons (RefusalReason)")
            accs = [(x, fx.account(x)) for x in own if fx.account(x) is not None]
            if not accs and not scope:
                miss.append("fixture whose account prints the reason" + ("" if own else " (no fixture)"))
            elif not accs and rs:
                miss.append(f"fixture whose account prints {', '.join(rs)}")
            elif rs:
                hit = [x for x, a in accs if all(r in a[1] for r in rs)]
                item(bool(hit), f"account {hit[0] if hit else ''} prints the reason",
                     f"account prints {', '.join(rs)} ({', '.join(x for x, _ in accs)} print "
                     + (", ".join(sorted(set().union(*[a[1] for _, a in accs]))) or "no refusal") + ")")
                if hit:
                    fr = fx.fresh_equal(hit[0])
                    item(fr is True, "fresh account",
                         "fresh account (" + ("differs" if fr is False else str(fr)) + ")")
        reason_sentence(["reason", "reader_reason", "refused_by"])
    elif f == "independent":
        ds = e.get("declarations")
        item(isinstance(ds, list) and len(ds) == 2, "declarations", "declarations (two)")
    else:
        miss.append(f"a status ({f!r} is none of DONE-0 C2's five)")
    if "removed" in e:
        removed_items(fx, e, own, item, miss)
    return have, miss


def erased_forms(fx, l, key, e, have, miss):
    """The forms of erased (findings/work/decision-fixrest-erased-forms.md section 2) the entry
    carries, each checked, its item appended to have or miss; returns the letters of the forms
    carried. P: each fixture `pair` names (else the first of the entry's own fixtures recording one)
    records `same_as OTHER: equal after stripping`; S: each `absent` pattern is found in no text in
    scope (kfix.check_absent); O: `other_file` and `witness` (kfix.check_other); C: `carried_by`
    names a row that is not erased and has its own evidence, and the entry's `sentence` occurs in
    that row's fixture."""
    letters = []
    own = [x for x in [e.get("fixture")] + list(e.get("also_fixtures") or []) if fx.exists(x)]
    pair_rx = r"^same_as (\S+): equal after stripping$"
    if "pair" in e:
        letters.append("P")
        for x in e["pair"] if isinstance(e["pair"], list) else [e["pair"]]:
            m = re.search(pair_rx, fx.read(x, "kompile.txt") or "", re.M) if fx.exists(x) else None
            (have if m else miss).append(f"P: pair {x} same_as {m[1]} equal" if m else
                                         f"P: pair {x!r} records no same_as equal after stripping")
    else:
        for x in own:
            m = re.search(pair_rx, fx.read(x, "kompile.txt") or "", re.M)
            if m:
                letters.append("P"); have.append(f"P: pair {x} same_as {m[1]} equal"); break
    if "absent" in e:
        letters.append("S")
        ok, what = fx.check_absent(e)
        (have if ok else miss).append(f"S: {what}")
    if "other_file" in e or "witness" in e:
        letters.append("O")
        ok, what = fx.check_other(e, own)
        (have if ok else miss).append(f"O: {what}")
    if "carried_by" in e:
        letters.append("C")
        c = e["carried_by"]
        m = re.match(r"^(E[1-8]|C3) (.+)$", c) if isinstance(c, str) else None
        row = (fx.rows.get(m[1]) or {}).get(m[2]) if m and fx.rows else None
        if row is None:
            miss.append(f"C: carried_by {c!r} is no row of rows.toml")
        elif row.get("status") in ("erased", None):
            miss.append(f"C: carried_by {c!r} is of status {row.get('status')!r}")
        else:
            h2, m2 = evidence(fx, m[1], m[2], row, row)
            ss = e.get("sentence")
            ss = ss if isinstance(ss, list) else [ss] if isinstance(ss, str) else []
            x = row.get("fixture")
            out = [s for s in ss if not fx.exists(x) or s not in fx.text(x)]
            if m2:
                miss.append(f"C: {c} has not its own evidence ({m2[0][:80]})")
            elif not ss or out:
                miss.append(f"C: the entry's sentence " + (f"{out[0][:50]!r} not in {x}" if out else "(none)"))
            else:
                have.append(f"C: carried by {c} ({row.get('status')}, its evidence; {len(ss)} sentences in {x})")
    return letters


def node_held(fx, l, key, x, e):
    """(held, how) for an E4/E5 row's node in fixture x."""
    try:
        import e4e5
    except ImportError:
        e4e5 = None
    if e4e5 is not None:
        return e4e5.holds(fx, l, key, x, e.get("node_sentence"))
    if "sentence" in e:
        return True, "sentence"
    return False, "no parse of the text (test/constructs/e4e5.py) and no sentence"


# -------------------------------------------------------------------------------------- the modes

def run(t, fx):
    """[(list, status, form, where, core reason, present, missing)] over the entries with a status."""
    out = []
    pats = [p for _, _, _, e, _ in entries(t) if e.get("status") == "erased"
            for p in (e["absent"] if isinstance(e.get("absent"), list) else [e.get("absent")]) if p is not None]
    if pats:
        try:
            import kfix
            kfix.scan(pats)     # one pass over the texts in scope for every pattern
        except (Exception, SystemExit):
            pass                # each entry's check reports it
    for l, key, where, e, row in entries(t):
        c = core(t, l, key, row)
        f = form(l, key, e, row, fx)
        if f is None:
            continue
        have, miss = evidence(fx, l, key, e, row)
        out.append((l, e.get("status"), f, where, c, have, miss))
    return out


def order(r):
    return (LISTS.index(r[0]), STATUSES.index(r[1]) if r[1] in STATUSES else 99, r[2], r[3])


def line(r):
    return (f"    {r[3]}" + (f" [FIX-core: {r[4]}]" if r[4] else "") + ": present: "
            + ("; ".join(r[5]) or "nothing") + (f"; MISSING: {'; '.join(r[6])}" if r[6] else ""))


def groups(res):
    g = collections.OrderedDict()
    for r in sorted(res, key=order):
        g.setdefault((r[0], r[1], r[2]), []).append(r)
    return g


def print_list(res, fresh, out):
    """The entries FIX-core does not hold, by group; with out, the entries into that file."""
    nrows = sum(1 for r in res if not re.search(r" (cases|also_refused|split)\[", r[3]))
    lines = []
    for (l, s, f), rs in groups(res).items():
        lines.append(f"  {l} {s} [{f}]: {len(rs)} entries, {sum(1 for r in rs if not r[6])} with the"
                     " evidence of their form")
        lines += [line(r) for r in rs]
    print(f"rest: {nrows} rows and {len(res) - nrows} nested entries FIX-core does not hold"
          f" ({sum(1 for r in res if not r[6])} with the evidence of their form)"
          + ("" if fresh else "; fresh accounts not run (--fresh)"))
    if out:
        open(out, "w").write("\n".join(lines) + "\n")
        print("\n".join(ln for ln in lines if not ln.startswith("    ")))
        print(f"rest: each entry in {out}")
    else:
        print("\n".join(lines))


def print_check(res, fresh, report, out):
    """The check of every entry; returns the exit code."""
    fails = [r for r in res if r[6]]
    by = collections.Counter((r[0], r[2]) for r in fails)
    tot = collections.Counter((r[0], r[2]) for r in res)
    print(f"c2-evidence: {len(res)} entries with a status, {len(fails)} missing evidence"
          + (" (report mode: not failing)" if report else "") + ("" if fresh else "; fresh accounts not run"))
    for l in LISTS:
        ks = sorted({f for (x, f) in tot if x == l})
        if ks:
            print(f"  {l}: " + ", ".join(f"{f} {tot[(l, f)] - by[(l, f)]}/{tot[(l, f)]}" for f in ks))
    flines = [line(r) for r in sorted(fails, key=order)]
    if out:
        open(out, "w").write("\n".join(flines) + "\n")
        print(f"c2-evidence: each failure in {out}")
    for ln in flines[:40]:
        print(ln)
    if len(flines) > 40:
        print(f"    ... and {len(flines) - 40} more")
    return 0 if report or not fails else 1


def main(argv):
    mode = argv.pop(0) if argv[:1] in (["list"], ["check"]) else "list"
    opt = {}
    for o in ("--out", "--list"):
        if o in argv:
            i = argv.index(o); opt[o] = argv[i + 1]; del argv[i:i + 2]
    report, fresh, gate = "--report" in argv, "--fresh" in argv, "--gate" in argv
    argv = [a for a in argv if a not in ("--report", "--fresh", "--gate")]
    t = tomllib.load(open(argv[0] if argv else os.path.join(HERE, "rows.toml"), "rb"))
    fx = Fixtures(os.path.join(HERE, "fixtures"), fresh, t)
    res = run(t, fx)
    if mode == "list":
        print_list([r for r in res if not r[4]], fresh, opt.get("--out"))
        return 0
    if "--list" in opt:
        print_list([r for r in res if not r[4]], fresh, opt["--list"])
    rc = print_check(res, fresh, report, opt.get("--out"))
    rc = print_reader_owed(t, gate) or rc
    return print_owed_state(t, fx) or rc


# ------------------------------------------------------------------------- inert of class attribute

def without_attribute(kore, head):
    """The text with every attribute of the head removed from its attribute lists: an application
    `HEAD{}(...)` standing at the start of a list or after a comma, with the comma that joins it."""
    rx = re.compile(r"(\[|, ?)" + re.escape(head) + r"\{\}\(")
    out, i = [], 0
    while True:
        m = rx.search(kore, i)
        if not m:
            out.append(kore[i:]); return "".join(out)
        import kfix
        end = kfix._close(kore, m.end() - 1) + 1
        if m[1] == "[":
            out.append(kore[i:m.end(1)])
            end += 2 if kore[end:end + 2] == ", " else 1 if kore[end:end + 1] == "," else 0
        else:
            out.append(kore[i:m.start()])
        i = end


def attr_pair(a, b, head):
    """(equal, why) for two texts (paths relative to kcore-spec): they differ, and are equal once
    every attribute of the head is removed and kfix.py's stripped is applied to both."""
    import kfix
    pa, pb = os.path.join(K, a), os.path.join(K, b)
    for p, n in ((pa, a), (pb, b)):
        if not os.path.isfile(p):
            return False, f"{n} does not exist"
    ta, tb = kfix.stripped(open(pa).read()), kfix.stripped(open(pb).read())
    if ta == tb:
        return False, f"{a} and {b} are equal: no difference for the attribute to be"
    if without_attribute(ta, head) != without_attribute(tb, head):
        return False, f"{a} and {b} differ beyond {head}"
    return True, f"{a} = {b} without {head}"


def attribute_items(fx, e, own, item, miss):
    """The items of inert of class attribute other than the tie, its theorems and the reason."""
    head = e.get("attribute")
    item(isinstance(head, str) and bool(head), f"attribute {head}", "attribute (its KORE head)")
    ps = e.get("attr_pairs") or []
    if not ps:
        miss.append("attr_pairs (a text and its companion, equal without the attribute)")
    for p in ps:
        if not (isinstance(p, list) and len(p) == 2 and all(isinstance(x, str) for x in p)):
            miss.append(f"attr_pairs item {p!r} is not [TEXT, COMPANION]"); continue
        if isinstance(head, str):
            ok, why = attr_pair(p[0], p[1], head)
            item(ok, f"pair {why}", f"pair ({why})")
    x = own[0] if own else None
    ts = e.get("tie") if isinstance(e.get("tie"), list) else []
    reads = [f for f in ts if f != "test/InertSemPairs.lean" and x and reads_own_text(f, x)]
    item(bool(reads), f"tie of the fixture's text ({', '.join(reads)})",
         "tie of the fixture's text (no file of `tie` other than test/InertSemPairs.lean reads "
         + (f"f2-examples/{x}.kompile.kore or a text equal to it)" if x else "a fixture's text: no fixture)"))


_OWN_TEXT = {}


def own_text(x):
    """Fixture x's kompiled text as tiegen writes it (its paths restored), or None where it has none."""
    if x not in _OWN_TEXT:
        try:
            import tiegen
            _OWN_TEXT[x] = tiegen.restored_text(x)
        except Exception:
            _OWN_TEXT[x] = None
    return _OWN_TEXT[x]


def reads_own_text(f, x):
    """Whether the Lean file f reads fixture x's own kompiled text: it names
    f2-examples/x.kompile.kore, or a text it reads (`... from "PATH"`) is byte for byte the text x's
    kompile.txt records, with its paths restored as tiegen writes f2-examples/x.kompile.kore."""
    p = os.path.join(K, f)
    if not os.path.isfile(p):
        return False
    if f"f2-examples/{x}.kompile.kore" in open(p).read():
        return True
    paths = set(re.findall(r'\bfrom\s+"(f2-examples/[^"]+)"', lean_source(f) or ""))
    t = own_text(x) if paths else None
    return t is not None and any(os.path.isfile(os.path.join(K, q)) and open(os.path.join(K, q)).read() == t
                                 for q in sorted(paths))


# ------------------------------------------------------------------- the sentences an option removes

def text_axioms(path):
    """[(index, module, sentence)] of the text's axioms: index counted from 1 over the whole text,
    the sentence with whitespace runs one space, the Location, Source and UNIQUE'Unds'ID attributes
    dropped (tiegen.axioms) and kompile's generated variables renumbered within it (kfix.alpha)."""
    import kfix, tiegen
    return [(i, m, kfix.alpha("  " + s)) for i, m, s, _ in tiegen.axioms(open(path).read())]


def removed_items(fx, e, own, item, miss):
    """The items of an entry's `removed` (module docstring, form supported, item removed)."""
    rs = e.get("removed")
    if not (isinstance(rs, list) and rs and all(isinstance(r, dict) for r in rs)):
        miss.append("removed (a list of tables)"); return
    x = own[0] if own else None
    ref = fx.conf(x).get("differs_from") if x else None
    if not isinstance(ref, str):
        miss.append("removed: the fixture names no reference text (differs_from)"); return
    paths = {n: fx.kompiled(n) for n in (ref, x)}
    gone = [n for n, p in paths.items() if not os.path.isfile(p)]
    if gone:
        miss.append(f"removed: no text {os.path.relpath(paths[gone[0]], K)}"); return
    ra, xa = text_axioms(paths[ref]), text_axioms(paths[x])
    user = ra[-1][1] if ra else None
    held = collections.Counter(s for _, _, s in xa)
    by_index = {i: (m, s) for i, m, s in ra}
    ns = [r.get("sentence") for r in rs]
    bad = [n for n in ns if not (isinstance(n, int) and n in by_index and by_index[n][0] == user)]
    item(not bad, f"removed: {len(ns)} axioms of {ref}'s user module {user}",
         f"removed: sentence {bad[0] if bad else ''!r} is no axiom of {ref}'s user module {user}")
    kept = [n for n in ns if n in by_index and held[by_index[n][1]]]
    item(not kept, f"removed: none in {x}'s text", f"removed: axiom {kept[0] if kept else ''} of {ref} is in {x}'s text")
    want = collections.Counter(s for _, _, s in ra)
    unlisted = [i for i, _, s in ra if i not in ns and want[s] > held[s]]
    item(not unlisted, f"removed: every axiom of {ref} absent from {x}'s text listed",
         f"removed: axiom {unlisted[0] if unlisted else ''} of {ref} is absent from {x}'s text and not listed"
         f" ({len(unlisted)} such)")
    lit = f"f2-examples/{ref}.kompile.kore"
    for r in rs:
        f = r.get("file")
        thms = [r.get("theorem"), r.get("companion")]
        undecl = [t for t in thms if not (isinstance(t, str) and isinstance(f, str) and declared(t, [f]))]
        reads = isinstance(f, str) and os.path.isfile(os.path.join(K, f)) and lit in open(os.path.join(K, f)).read()
        if undecl or not reads:
            miss.append(f"removed: sentence {r.get('sentence')}: " + (f"{undecl[0]!r} not declared in {f}"
                        if undecl else f"{f} does not read {lit}"))
            return
    item(True, f"removed: theorems ({2 * len(rs)}) declared, on {lit}", "")


# ------------------------------------------------------------------------------- the reading owed

# The reading an entry's status is owed by, while the reader does not do it (`reader_does_it =
# false` on an entry of status supported, parameter or inert): the ticket of PROGRESS that makes the
# reader do it, with the entries it owes, each named by its fixture or by "<list> <row key>". An
# entry is accepted while its ticket is in PROGRESS and not done; the completion gate (--gate)
# accepts none.
READER_OWED = [
    ("RDR.read-cellcoll-own", ["rdr-cellcoll-own"]),
    ("RDR.read-hook-assoc", ["rdr-hook-assoc"]),
    ("RDR.read-keq-only", ["rdr-keq-only"]),
    ("RDR.read-pred-rule", ["rdr-pred-rule"]),
]
OWED_STATUSES = ("supported", "parameter", "inert")


def progress_status():
    """{ticket id: status} of PROGRESS/tickets-*.toml, PROGRESS as units.py resolves it, or None."""
    import glob
    kr = os.environ.get("K_RUST", os.path.expanduser(
        "~/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust"))
    prog = os.environ.get("KCORE_PROGRESS") or next(
        (d for d in (os.path.join(K, "../progress"),
                     os.path.join(kr, "draft-personal/k-semantics-core-2026-11/progress"))
         if os.path.isdir(d)), None)
    files = sorted(glob.glob(os.path.join(prog, "tickets-*.toml"))) if prog else []
    if not files:
        return None
    st = {}
    for f in files:
        st |= {k: v.get("status") for k, v in tomllib.load(open(f, "rb")).get("ticket", {}).items()
               if isinstance(v, dict)}
    return st


def reader_owed(t, owed, tstatus, gate):
    """[(where, ticket or None, failure or None)] over the entries of a status in OWED_STATUSES
    with reader_does_it = false."""
    out = []
    for l, key, where, e, row in entries(t):
        if e.get("status") not in OWED_STATUSES or e.get("reader_does_it") is not False:
            continue
        names = {f"{l} {key}"} | ({e["fixture"]} if isinstance(e.get("fixture"), str) else set())
        tid = next((tid for tid, sel in owed if names & set(sel)), None)
        st = (tstatus or {}).get(tid)
        why = ("the completion gate: the reader does not do it" if gate else
               "names no ticket that owes the reading (READER_OWED)" if tid is None else
               "PROGRESS has no ticket file" if tstatus is None else
               f"ticket {tid} is not in PROGRESS" if st is None else
               f"ticket {tid} is done, and the entry still says the reader does not do it" if st == "done"
               else None)
        out.append((where, tid, why))
    return out


def print_reader_owed(t, gate):
    """The entries whose reading is owed, each with its ticket; returns the exit code."""
    rs = reader_owed(t, READER_OWED, progress_status(), gate)
    bad = [r for r in rs if r[2]]
    print(f"reader-owed: {len(rs)} entries of status {', '.join(OWED_STATUSES)} with reader_does_it = false"
          + (" (completion gate: none accepted)" if gate else f", {len(rs) - len(bad)} owed by a ticket not done"))
    for where, tid, why in rs:
        print(f"    {where}: {tid or 'no ticket'}" + (f"; FAILS: {why}" if why else ""))
    return 1 if bad else 0


# ------------------------------------------------------------------------- the owed CondDecided

# An account's line for a clause or rule whose CondDecided is owed (KcoreGen's `account`).
OWED_OPEN = re.compile(r"^\s+(.+): CondDecided open, over (\S+)$", re.M)
# A state of `owed_state` (rows-header.toml): proved or refuted by a theorem, or open with a reason.
OWED_STATE = re.compile(r"^(proved|refuted): (\S+)(?: \((test/[^()\s]+\.lean)\))?$|^(open): (\S.*)$")
# The ending of a state saying that no fixture of the entry's shape has its owed fact proved, and why
# (rows-header.toml); the state before it is read as OWED_STATE.
NONE_PROVED = "no fixture of this shape has it proved:"
NONE_PROVED_END = re.compile(r"; " + re.escape(NONE_PROVED) + r" (\S.*)$")
# The fields whose text may name a companion fixture of the entry (its same_as pair, its evidence).
OWED_NAMING = ("evidence", "reader_today", "refused_by", "place", "note", "reading", "no_sentence", "reason")


def owed_open(fx, name):
    """The clauses and rules whose CondDecided fixtures/NAME/account.txt prints open: [(item, over)]."""
    a = fx.read(name, "account.txt") if fx.exists(name) else None
    return OWED_OPEN.findall(a) if a else []


def lean_source(f):
    """The file's text without its comments, or None where it is no file."""
    p = os.path.join(K, f) if isinstance(f, str) else None
    if not p or not os.path.isfile(p):
        return None
    src = re.sub(r"/-.*?-/", "", open(p).read(), flags=re.S)
    return re.sub(r"--.*", "", src)


def decl_type(f, full):
    """The stated type of the theorem `full` in the file (the text after its binders' top-level `:`
    up to its `:=`, whitespace collapsed; textual, as file_decls), or None where it is not found."""
    src = lean_source(f)
    if src is None:
        return None
    lines, stack = src.split("\n"), []
    for i, line in enumerate(lines):
        s = line.strip()
        m = re.match(r"namespace (\S+)", s)
        if m:
            stack.append(m[1]); continue
        m = re.match(r"end (\S+)$", s)
        if m and stack and stack[-1] == m[1]:
            stack.pop(); continue
        m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                     r"(?:theorem|lemma) ([^\s:({\[]+)", s)
        if not m:
            continue
        d = m[1].strip("«»")
        if (".".join(stack + [d]) if not d.startswith("_root_.") else d[7:]) != full:
            continue
        rest, depth, colon = " ".join([s[m.end():]] + lines[i + 1:]), 0, None
        for j, ch in enumerate(rest):
            if ch in "([{⦃⟨":
                depth += 1
            elif ch in ")]}⦄⟩":
                depth -= 1
            elif depth == 0 and rest[j:j + 2] == ":=":
                return " ".join(rest[colon + 1:j].split()) if colon is not None else None
            elif depth == 0 and ch == ":" and colon is None:
                colon = j
        return None
    return None


_text_sources = {}


def text_of_fixture(path, x):
    """Whether the kompiled text at path (relative to kcore-spec) is fixture x's: it is
    f2-examples/X.kompile.kore, or a declaration of it carries the Source of fixtures/X's own .k file."""
    if path == f"f2-examples/{x}.kompile.kore":
        return True
    if path not in _text_sources:
        p = os.path.join(K, path)
        body = open(p).read() if os.path.isfile(p) else ""
        _text_sources[path] = set(re.findall(r'Source\((?:[^()"]*/)?fixtures/([^/()"]+)/\1\.k\)', body))
    return x in _text_sources[path]


def owed_match_elsewhere(th, fl, x):
    """Why THEOREM of FILE is not a MatchIndependent stated of fixture x's text, or None: its stated
    type is `MatchIndependent ...`, and every text FILE reads (`definition_of ... from "PATH"`) is x's."""
    ty = decl_type(fl, th)
    if not ty or not re.match(r"MatchIndependent\b", ty):
        return f"{th} is not stated as a MatchIndependent in {fl} (its type: {(ty or 'not found')[:60]!r})"
    reads = re.findall(r'definition_of\s+\S+\s+from\s+"([^"]+)"', lean_source(fl) or "")
    if not reads:
        return f"{fl} reads no kompiled text (no `definition_of ... from`)"
    other = [r for r in reads if not text_of_fixture(r, x)]
    if other:
        return f"{fl} reads {', '.join(other)}, which is not fixtures/{x}'s text"
    return None


def owed_state(t, fx):
    """[(where, fixture, state word or None, failure or None)] over the entries naming `owed_state`
    or having a fixture whose account prints `CondDecided open`, then one line (where "fixtures")
    per fixture of the directory whose account prints it and that no entry's `owed_state` keys."""
    out, keyed = [], set()
    for l, key, where, e, row in entries(t):
        own = [x for x in [e.get("fixture")] + list(e.get("also_fixtures") or []) if isinstance(x, str)]
        need = [x for x in own if owed_open(fx, x)]
        st = e.get("owed_state")
        if st is None:
            out += [(where, x, None, "its fixture's account prints `CondDecided open` and the entry has no"
                     " owed_state") for x in need]
            continue
        if not isinstance(st, dict) or not st:
            out.append((where, None, None, "owed_state is not a table from a fixture to its state")); continue
        out += [(where, x, None, "owed_state has no key for its fixture, whose account prints"
                 " `CondDecided open`") for x in need if x not in st]
        prose = " ".join(str(e.get(f, "")) for f in OWED_NAMING)
        words, none_proved = set(), False
        for x, v in st.items():
            keyed.add(x)
            if isinstance(v, str) and NONE_PROVED_END.search(v):
                none_proved, v = True, NONE_PROVED_END.sub("", v)
            m = OWED_STATE.match(v) if isinstance(v, str) else None
            word = m and (m[1] or m[4])
            why = None
            # a fixture whose account owes no CondDecided is admitted only with its owed fact of the
            # clause, MatchIndependent, proved on its own text by a theorem of a named file
            unowed = not owed_open(fx, x)
            if unowed and fx.read(x, "account.txt") is None:
                why = f"{x} is no fixture with an account.txt (fixtures/{x})"
            elif x not in own and not re.search(rf"(?<![\w-]){re.escape(x)}(?![\w-])", prose):
                why = f"{x} is no fixture of the entry and its text does not name it"
            elif not m:
                why = (f"state {str(v)[:60]!r} is not 'proved: THEOREM[ (FILE)]', 'refuted: THEOREM[ (FILE)]'"
                       " or 'open: REASON'")
            elif unowed and (word != "proved" or not m[3]):
                why = (f"fixtures/{x}'s account prints no `CondDecided open`, and its state is not"
                       " 'proved: THEOREM (FILE)' with THEOREM a MatchIndependent of its text")
            elif word != "open":
                th, fl = m[2], m[3]
                ts = e.get("tie")
                files = [fl] if fl else (ts if isinstance(ts, list) else [ts] if ts else [])
                if not files:
                    why = f"{th} names no file and the entry has no tie"
                elif fl and tie_file_ok(fl):
                    why = tie_file_ok(fl)
                elif not any(th in (file_decls(f) or ()) for f in files):
                    why = f"{th} is not declared in {', '.join(map(str, files))}"
                elif unowed:
                    why = owed_match_elsewhere(th, fl, x)
            out.append((where, x, word, why))
            words.add(word)
        if "proved" not in words and not none_proved:
            out.append((where, None, None, "no fixture of the entry has its owed fact proved, and no state"
                        f" ends `; {NONE_PROVED} REASON`"))
        elif "proved" in words and none_proved:
            out.append((where, None, None, f"a state ends `; {NONE_PROVED} ...` beside a proved state"))
    for x in sorted(os.listdir(fx.fx)):
        if x not in keyed and owed_open(fx, x):
            out.append(("fixtures", x, None, "its account prints `CondDecided open` and no entry's owed_state"
                        " names its state"))
    return out


def print_owed_state(t, fx):
    """The state of each owed CondDecided the entries name; returns the exit code."""
    rs = owed_state(t, fx)
    bad = [r for r in rs if r[3]]
    states = collections.Counter(r[2] for r in rs if r[2])
    print(f"owed-state: {len({r[0] for r in rs if r[2]})} entries name the state of an owed fact"
          f" at {len({r[1] for r in rs if r[2]})} fixtures: "
          + ", ".join(f"{k} {states[k]}" for k in ("proved", "refuted", "open")) + f"; {len(bad)} failing")
    best = {}
    for where, _, word, _ in rs:
        if word:
            best[where] = min(best.get(where, 2), {"proved": 0, "open": 1}.get(word, 2))
    groups = collections.Counter(best.values())
    print(f"owed-state: entries by their best fixture: proved {groups[0]}, open {groups[1]}, false {groups[2]}")
    for where, x, word, why in rs:
        if why or word != "proved":
            print(f"    {where}: {x or ''} {word or ''}".rstrip() + (f"; FAILS: {why}" if why else ""))
    return 1 if bad else 0


# ------------------------------------------------------------------------------------ self-test

def self_test():
    """The check on written entries and fixtures: each accepted or refused as expected."""
    d = tempfile.mkdtemp(prefix="rest-self-test-", dir=os.path.join(K, ".lake"))
    try:
        fxd = os.path.join(d, "fixtures"); os.makedirs(fxd)
        clean = ("parse: ok; wf true; failing: []\n  3 read [user]\n  1 inert simplification [user]\n"
                 "stage refusals (of sentences classified read): 0\nrefused by the account: 0\n")
        refusing = ("parse: ok; wf true; failing: []\nstage refusals (of sentences classified read): 1\n"
                    "      sentence 7 (Lblf): setVariable (VarS: in the requires)\nrefused by the account: 0\n")
        for name, acc, kore, extra in [("ok", clean, "//@ 3\n  axiom{} f\n", ""),
                                       ("bad", refusing, "//@ 7\n  axiom{} g\n", ""),
                                       ("err", None, None, 'expect = "error"\n'),
                                       ("eq", clean, "", "")]:
            os.makedirs(os.path.join(fxd, name))
            if acc is not None:
                open(os.path.join(fxd, name, "account.txt"), "w").write(acc)
            if kore is not None:
                open(os.path.join(fxd, name, "kore.txt"), "w").write(kore)
            open(os.path.join(fxd, name, "kompile.txt"), "w").write(
                "exit 0\nsame_as ok: equal after stripping\n" if name == "eq" else "exit 0\n")
            if extra:
                open(os.path.join(fxd, name, "fixture.toml"), "w").write(extra)
        os.makedirs(os.path.join(fxd, "oth")); os.makedirs(os.path.join(fxd, "nodef"))
        open(os.path.join(fxd, "oth", "kompile.txt"), "w").write("exit: 0\n")
        open(os.path.join(fxd, "oth", "other.txt"), "w").write(
            "// other_file macros.kore: 9 lines, sha256 0\n  axiom{R} \\equals{SortExp{},R} (\n"
            "    Lblm{}(VarX:SortExp{}),\n    Lblg{}(VarX:SortExp{}))\n  [macro{}()]\n")
        open(os.path.join(fxd, "nodef", "kompile.txt"), "w").write("exit: 0\ndefinition.kore: none written\n")
        # option fixtures: kompile.txt's command passes --opt, --backend llvm, R-12's set only; one
        # with --opt whose account refuses (setVariable)
        for name, args, acc in (("optk", "--backend haskell --opt ref.k", clean),
                                ("optllvm", "--backend llvm --no-llvm-kompile ref.k", clean),
                                ("opthask", "--backend haskell ref.k", clean),
                                ("optref", "--backend haskell --opt ref.k", refusing)):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "kompile.txt"), "w").write(
                f"command: kompile {args} -o out  (cwd: the fixture directory)\nexit: 0\n")
            open(os.path.join(fxd, name, "account.txt"), "w").write(acc)
        rows = {"E3": {"U": {"status": "inert", "inert_class": "use", "reason": "C1", "fixture": "ok"},
                       "V": {"status": "inert", "inert_class": "use", "fixture": "ok"},
                       "E": {"status": "erased", "fixture": "eq"}}}
        fx = Fixtures(fxd, False, rows)
        fx.fresh_equal = lambda name: True
        import kfix
        sm = {"modules": ["BASIC-K", "KSEQ", "INJ", "K", "MAIN"],
              "lists": [[4, 0, "symbol", "constructor,comm", "Source(BUILTIN/kast.md)", "Location(80,3,80,20)"],
                        [4, 1, "axiom", "UNIQUE'Unds'ID", "-", "-"], [None, None, "module", "", "-", "-"],
                        [4, 2, "sort", "", "Source(/nix/store/x-k-6.0.0-y/include/kframework/builtin/domains.md)",
                         "Location(900,1,900,9)"],
                        [4, 3, "sort", "", "Source(FIXTURE/x/other.md)", "Location(1,1,1,9)"]]}
        fake = lambda ps: {p: (1, [], [f"t: {h}" for h in kfix.absent_hits(p, sm)])
                           if kfix.absent_form(p) else None for p in ps}
        fx.check_absent = lambda e: kfix.check_absent(e, fake)
        defn = "module MAIN\n  symbol Lblm{}(SortExp{}) : SortExp{} [macro{}()]\n// rule Lblh{}(VarX:SortExp{})\nendmodule []\n"
        fx.check_other = lambda e, own: kfix.check_other(e, own, read=fx.read, full_text=lambda x: defn)
        tie = "test/C3EqReqEns.lean"
        thm = {"form": "a", "theorem": "KCore.C3EqReqEns.f_5", "file": tie}
        for name, conf in (("cmp", 'differs_from = "ok"\n'), ("e1-module", ""), ("e2-rule", ""), ("opt", 'differs_from = "e8-ref"\n')):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "account.txt"), "w").write(clean)
            open(os.path.join(fxd, name, "kompile.txt"), "w").write("exit 0\n")
            if conf:
                open(os.path.join(fxd, name, "fixture.toml"), "w").write(conf)
        # item 7: fixtures named as two texts with a tie, base (sentence 93, initKCell's equation, of
        # the no-direction class of test/TieBase.lean) and e1-starinit (281, initTCell's equation,
        # of class function equation in test/TieE1Starinit.lean, applied only by 283, of no direction)
        nd_k = '// rule initKCell(Init)=>`<k>`(`project:KItem`(`Map:lookup`(Init,inj{KConfigVar,KItem}(#token("$PGM","KConfigVar")))))'
        nd_kd = "symbol LblinitKCell{}(SortMap{}) : SortKCell{}"
        # isBool's [owise] equation (94, a function equation), and a path of the fixture's kore.txt that
        # the tie's text writes otherwise
        nd_f, nd_src = "\\exists{R} (Var'Unds'Gen0:SortBool{},", 'Source(FIXTURE/base.k)'
        nd_t = "// rule initTCell(Init)=>`TCellSetItem`(`<t>`(initVCell(Init),initPCell(Init)))"
        for name, kore in (("base", f"//@ 30\n  {nd_kd} [function{{}}()]\n//@ 99\n{nd_k}\n  axiom{{R}} x\n"
                                    f"//@ 100\n  axiom{{R}} {nd_f} [{nd_src}]\n"),
                           ("e1-starinit", f"//@ 300\n{nd_t}\n  axiom{{R}} x\n")):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "account.txt"), "w").write(clean)
            open(os.path.join(fxd, name, "kompile.txt"), "w").write("exit 0\n")
            open(os.path.join(fxd, name, "kore.txt"), "w").write(kore)
        tbase, ts_ = "test/TieBase.lean", "test/TieE1Starinit.lean"
        acc3 = lambda ns: [f"KCore.{ns}.account", f"KCore.{ns}.account_absent", f"KCore.{ns}.absent_closed"]
        model = lambda ss, kind="in a model": {"form": "a", "kind": kind, "sentences": ss, "theorem": "KCore.C3EqReqEns.f_5",
                                              "file": tie}
        ndok = {"status": "supported", "fixture": "base", "sentence": [nd_k], "tie": [tbase, tie],
                "tie_theorems": acc3("TieBase"), "no_direction": [93], "derived": [model([93])]}
        nd = lambda **kw: dict({k: v for k, v in ndok.items() if kw.get(k, 0) is not None}, **{k: v for k, v in kw.items() if v is not None})
        txt = ("module M\n  axiom{R} f{}() [UNIQUE'Unds'ID{}(\"%s\"), org.kframework.attributes.Location("
               "Location(%d,1,1,2))]\n  axiom{R} g{}() [%s]\nendmodule []\n")
        ta, tb, tc = (os.path.relpath(os.path.join(d, n), K) for n in ("a.kore", "b.kore", "c.kore"))
        for n, args in ((ta, ("a1", 1, "UNIQUE'Unds'ID{}(\"x\")")), (tb, ("b2", 7, "")),
                        (tc, ("a1", 1, "cool-like{}()"))):
            open(os.path.join(K, n), "w").write(txt % args)
        sp = "test/InertSemPairs.lean"
        # a reference text and an option's text without its axiom 4, generated variables and
        # identifiers numbered otherwise
        refx = ("module INJ\n  axiom{R} inj{}() []\nendmodule []\nmodule REF\n  axiom{R} a{}() [UNIQUE'Unds'ID{}(\"1\")]\n"
                "  axiom{R} b{}(Var'Unds'Gen3:SortInt{}) []\n  axiom{R} c{}() []\nendmodule []\n")
        optx = ("module INJ\n  axiom{R} inj{}() []\nendmodule []\nmodule REF\n  axiom{R} a{}() [UNIQUE'Unds'ID{}(\"9\")]\n"
                "  axiom{R}  b{}(Var'Unds'Gen0:SortInt{}) []\nendmodule []\n")
        for n, t in (("e8-ref", refx), ("opt", optx)):
            open(os.path.join(d, f"{n}.kompile.kore"), "w").write(t)
        fx.kompiled = lambda n: os.path.join(d, f"{n}.kompile.kore")
        rm = lambda n, thm="KCore.LibEvCeilE8Ref.s153_refuted": {
            "sentence": n, "theorem": thm, "companion": "KCore.LibEvCeilE8Ref.s153_one", "file": "test/LibEvCeilE8Ref.lean"}
        opt = lambda rs, fixture="opt": {"status": "supported", "fixture": fixture, "tie": [tie], "derived": [thm], "removed": rs}
        attr = {"status": "inert", "inert_class": "attribute", "fixture": "e1-module", "attribute": "UNIQUE'Unds'ID",
                "attr_pairs": [[ta, tb]], "tie": ["test/TieE1Module.lean", sp],
                "tie_theorems": ["KCore.TieE1Module.fns_entailed", "KCore.InertSemPairs.trS_attrs"],
                "reader_tests": ["KCore.InertSemPairs.StrictAlias.sem_eq"], "reason": "an identifier"}
        if not (without_attribute("[a{}(), u{}(b{}(\"(\")), c{}()] [u{}()] [x{}(), u{}()]", "u")
                == "[a{}(), c{}()] [] [x{}()]"):
            print("rest self-test: FAILS: without_attribute")
            return 1
        cases = [
            # (list, key, entry, accepted)
            # item 7: a no-direction sentence with its class's statement and a table 'in a model'
            ("E7", "A", ndok, True),
            ("E7", "A", nd(no_direction=None, derived=None), False),
            ("E7", "A", nd(derived=None), False),
            ("E7", "A", nd(no_direction=None), False),
            ("E7", "A", nd(derived=[model([93], "from sentences")]), False),
            ("E7", "A", nd(derived=[model([93, 35])]), False),
            ("E7", "A", nd(no_direction=[93, 94], derived=[model([93, 94])]), False),
            ("E7", "A", nd(no_direction=[35], derived=[model([35])]), False),
            ("E7", "A", nd(no_direction=[], derived=[model([])]), False),
            ("E7", "A", nd(tie_theorems=acc3("TieBase")[:2]), False),
            ("E7", "A", nd(tie=[tie], tie_theorems=acc3("TieBase")), False),
            ("E7", "A", nd(tie=[tbase, "test/TieE1Module.lean", tie], tie_theorems=acc3("TieE1Module")), False),
            # a declaration is no axiom and counts neither way: beside a no-direction sentence the entry
            # needs no_direction, alone it needs nothing
            ("E7", "A", {"status": "supported", "fixture": "base", "sentence": [nd_kd, nd_k], "tie": [tbase],
                         "tie_theorems": ["KCore.TieBase.account"]}, False),
            ("E7", "A", nd(sentence=[nd_kd, nd_k]), True),
            ("E7", "A", {"status": "supported", "fixture": "base", "sentence": [nd_kd], "tie": [tbase],
                         "tie_theorems": ["KCore.TieBase.account"]}, True),
            # a no-direction sentence beside one of another class: no_direction is needed all the same
            ("E7", "A", {"status": "supported", "fixture": "base", "sentence": [nd_f, nd_k], "tie": [tbase],
                         "tie_theorems": ["KCore.TieBase.account"]}, False),
            ("E7", "A", nd(sentence=[nd_f, nd_k]), True),
            ("E7", "A", nd(sentence=[nd_f, nd_k], no_direction=[93, 94], derived=[model([93, 94])]), False),
            # the string narrowed to the sentence of the other class: no_direction is not needed
            ("E7", "A", {"status": "supported", "fixture": "base", "sentence": [nd_f], "tie": [tbase],
                         "tie_theorems": ["KCore.TieBase.account"]}, True),
            # a sentence of kore.txt that the tie's text does not hold: its class is not read
            ("E7", "A", {"status": "supported", "fixture": "base", "sentence": [nd_src], "tie": [tbase],
                         "tie_theorems": ["KCore.TieBase.account"]}, False),
            ("E7", "A", nd(sentence=[nd_k, nd_src]), False),
            # the class is the tie's: initTCell's equation, applied only by a no-direction sentence, is a
            # function equation
            ("E1", "A", {"status": "supported", "fixture": "e1-starinit", "sentence": [nd_t], "tie": [ts_],
                         "tie_theorems": ["KCore.TieE1Starinit.fns_entailed"]}, True),
            ("E1", "A", {"status": "supported", "fixture": "e1-starinit", "sentence": [nd_t], "tie": [ts_],
                         "tie_theorems": acc3("TieE1Starinit"), "no_direction": [281], "derived": [model([281])]}, False),
            ("E1", "A", {"status": "supported", "fixture": "e1-starinit", "sentence": [nd_t], "tie": [ts_],
                         "tie_theorems": acc3("TieE1Starinit"), "no_direction": [283], "derived": [model([283])]}, True),
            ("E2", "A", {"status": "supported", "fixture": "ok", "sentence": ["axiom{} f"], "tie": [tie],
                         "derived": [thm]}, True),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": [tie]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": [tie],
                         "tie_theorems": ["KCore.C3EqReqEns.no_such_theorem"]}, False),
            ("E2", "A", {"status": "supported", "fixture": "bad", "tie": [tie], "derived": [thm]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "sentence": ["axiom{} g"], "tie": [tie],
                         "derived": [thm]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": ["test/PrintNames.lean"], "derived": [thm]}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r"}, True),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.ruleShape"],
                         "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"]}, False),
            ("E2", "A", {"status": "refused", "fixture": "err", "class": "R-b", "reason": "r"}, True),
            ("E2", "A", {"status": "refused", "fixture": "err", "class": "R-a", "reason": "r"}, False),
            ("E2", "A", {"status": "erased", "fixture": "eq"}, True),
            ("E2", "A", {"status": "erased", "fixture": "ok"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "pair": "eq"}, True),
            ("E2", "A", {"status": "erased", "fixture": "eq", "pair": "ok"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "pair": ["eq", "ok"]}, False),
            # S: a pattern found nowhere; found (a head, a source range, a module); of no known form
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "attribute cellSort"}, True),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": ["axiom attribute comm",
                         "source kast.md 1-79", "module other than BASIC-K, KSEQ, INJ, K and the main module"]}, True),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "attribute comm"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "symbol attribute comm"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "source kast.md 70-90"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "source kast.md 100-200"}, True),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "source domains.md 1-5"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "source other.md 1-5"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "module other than BASIC-K, KSEQ, K and the main module"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "no sentence holds it"}, False),
            # O: the witness in other.txt and not in definition.kore
            ("E5", "A", {"status": "erased", "fixture": "oth", "other_file": "macros.kore",
                         "witness": ["Lblm{}(VarX:SortExp{}),   Lblg{}(VarX:SortExp{})"]}, True),
            ("E5", "A", {"status": "erased", "fixture": "oth", "other_file": "macros.kore",
                         "witness": ["macro{}()"]}, False),
            ("E5", "A", {"status": "erased", "fixture": "oth", "other_file": "macros.kore",
                         "witness": ["Lblh{}(VarX:SortExp{})"]}, False),
            ("E5", "A", {"status": "erased", "fixture": "oth", "other_file": "syntaxDefinition.kore",
                         "witness": ["Lblm{}(VarX:SortExp{})"]}, False),
            # C: carried by a row with its evidence, the sentence in its fixture
            ("E7", "A", {"status": "erased", "carried_by": "E3 U", "sentence": ["axiom{} f"]}, True),
            ("E7", "A", {"status": "erased", "carried_by": "E3 U", "sentence": ["axiom{} g"]}, False),
            ("E7", "A", {"status": "erased", "carried_by": "E3 V", "sentence": ["axiom{} f"]}, False),
            ("E7", "A", {"status": "erased", "carried_by": "E3 E", "sentence": ["axiom{} f"]}, False),
            ("E7", "A", {"status": "erased", "carried_by": "E3 nothing", "sentence": ["axiom{} f"]}, False),
            # two forms are conjoined
            ("E2", "A", {"status": "erased", "fixture": "eq", "absent": "attribute comm"}, False),
            # an option that writes no definition
            ("E8", "A", {"status": "refused", "fixture": "nodef", "class": "scope", "unit": "none (scope): option",
                         "shape": "none: fixtures/nodef/kompile.txt:2: definition.kore: none written",
                         "reason": "r"}, True),
            ("E8", "A", {"status": "refused", "fixture": "ok", "class": "scope", "unit": "none (scope): option",
                         "shape": "none: fixtures/nodef/kompile.txt:2: definition.kore: none written",
                         "reason": "r"}, False),
            ("E8", "A", {"status": "refused", "fixture": "nodef", "class": "scope", "unit": "none (scope): option",
                         "shape": "E8 X", "reason": "r"}, False),
            # an option outside R-12's set, refused for scope without a RefusalReason
            ("E8", "--opt", {"status": "refused", "fixture": "optk", "class": "R-b",
                             "reasons": [SCOPE_OPTION], "reason": "r"}, True),
            ("E8", "--backend", {"status": "refused", "fixture": "optllvm", "class": "R-b",
                                 "reasons": [SCOPE_OPTION], "reason": "r"}, True),
            ("E8", "--opt", {"status": "refused", "fixture": "optk", "class": "scope",
                             "reasons": [SCOPE_OPTION], "reason": "r"}, True),
            # with the reader's refusal beside it: checked against the account
            ("E8", "--opt", {"status": "refused", "fixture": "optref", "class": "R-b",
                             "reasons": [SCOPE_OPTION, "RefusalReason.setVariable"], "reason": "r"}, True),
            ("E8", "--opt", {"status": "refused", "fixture": "optk", "class": "R-b",
                             "reasons": [SCOPE_OPTION, "RefusalReason.setVariable"], "reason": "r"}, False),
            # R-12's value of --backend; an option the command does not pass; no fixture; no reason
            ("E8", "--backend", {"status": "refused", "fixture": "opthask", "class": "R-b",
                                 "reasons": [SCOPE_OPTION], "reason": "r"}, False),
            ("E8", "--other", {"status": "refused", "fixture": "optk", "class": "R-b",
                               "reasons": [SCOPE_OPTION], "reason": "r"}, False),
            ("E8", "--opt", {"status": "refused", "fixture": "none", "class": "R-b",
                             "reasons": [SCOPE_OPTION], "reason": "r"}, False),
            ("E8", "--opt", {"status": "refused", "fixture": "optk", "class": "R-b",
                             "reasons": [SCOPE_OPTION]}, False),
            # without the item, or off an E8 option row of class R-b or scope
            ("E8", "--opt", {"status": "refused", "fixture": "optk", "class": "R-b", "reason": "r"}, False),
            ("E2", "--opt", {"status": "refused", "fixture": "optk", "class": "R-b",
                             "reasons": [SCOPE_OPTION], "reason": "r"}, False),
            ("E8", "--opt", {"status": "refused", "fixture": "optk", "class": "R-a",
                             "reasons": [SCOPE_OPTION], "reason": "r"}, False),
            ("E2", "A", {"status": "inert", "fixture": "ok", "inert_class": "simplification", "tie": [tie],
                         "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, True),
            ("E2", "A", {"status": "inert", "fixture": "ok", "inert_class": "claim", "tie": [tie],
                         "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, False),
            ("E3", "A", {"status": "inert", "inert_class": "use", "reason": "C1"}, True),
            ("E3", "A", {"status": "inert", "inert_class": "use"}, False),
            ("E3", "A", {"status": "inert", "inert_class": "use", "reason": "C1", "fixture": "cmp"}, False),
            ("E3", "A", {"status": "inert", "inert_class": "use", "reason": "C1", "attr_pairs": [[ta, tb]]}, False),
            ("E7", "A", attr, True),
            ("E7", "A", dict(attr, attr_pairs=[[ta, tc]]), False),
            # a tie reading a text byte for byte the fixture's kompiled text, under another name
            ("E7", "A", dict(attr, fixture="e2-rule", tie=["test/TieRuleCool.lean", sp],
                             tie_theorems=["KCore.TieRuleCool.rules_tie", "KCore.InertSemPairs.trS_attrs"]), True),
            ("E7", "A", dict(attr, fixture="e2-rule"), False),
            ("E7", "A", dict(attr, attr_pairs=[[ta, ta]]), False),
            ("E7", "A", dict(attr, attribute="cool-like"), False),
            ("E7", "A", dict(attr, tie=[sp], tie_theorems=["KCore.InertSemPairs.trS_attrs"]), False),
            ("E7", "A", dict(attr, tie_theorems=["KCore.TieE1Module.fns_entailed"]), False),
            ("E7", "A", {k: v for k, v in attr.items() if k != "reason"}, False),
            ("E6", "x", {"status": "parameter", "derived": [{"form": "c", "theorem": "T", "file": tie}]}, True),
            ("E6", "x", {"status": "parameter", "derived": [thm]}, False),
            ("E6", "x", {"status": "parameter", "derived": [{"form": "r", "theorem": "T", "file": tie}]}, True),
            ("E6", "x", {"status": "parameter", "derived": [{"form": "r", "theorem": "T", "file": tie}, thm]}, True),
            ("E6", "hook:X", {"status": "supported", "derived": [thm]}, True),
            ("E6", "hook:X", {"status": "supported"}, False),
            ("E6", "symbol:X", {"status": "supported", "tie": [tie], "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, True),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)"]}, True),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.C3EqReqEns.nope (test/C3EqReqEns.lean; t axiom 3)"]}, False),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.X.y (test/PrintNames.lean; t axiom 3)"]}, False),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["uncovered: INT; no tied text holds the sentence"]}, False),
            ("E6", "lemma:X", {"status": "inert", "e6_tie": ["refuted: M; no theorem entails the sentence"]}, False),
            ("E6", "module:M", {"status": "supported", "e6_tie": ["every axiom, lemma, sort and symbol row of M (3) is tied"]}, True),
            ("E6", "module:M", {"status": "supported", "e6_tie": ["every axiom, lemma, sort and symbol row of M (3) is tied, "
                                                                  "or of no direction with a theorem in a model (1)"]}, True),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": "no direction: INT; KCore.C3EqReqEns.f_5 "
                                                                "(test/C3EqReqEns.lean; t axiom 3)"}, False),
            ("E6", "lemma:X", {"status": "inert",
                               "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)"]}, True),
            ("E6", "axiom:X", {"status": "inert",
                               "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)"]}, False),
            ("E2", "A", {"status": "pending-fixture"}, False),
            ("E2", "A", {"status": "not-handled"}, False),
            ("C3", "A x B", {"status": "independent", "declarations": ["a", "b"]}, True),
            # removed: axiom 4 of the reference, absent from the option's text and the only one
            ("E8", "A", opt([rm(4)]), True),
            ("E8", "A", opt([rm(3)]), False),
            ("E8", "A", opt([rm(4), rm(3)]), False),
            ("E8", "A", opt([rm(4), rm(9)]), False),
            ("E8", "A", opt([rm(4), rm(1)]), False),
            ("E8", "A", opt([]), False),
            ("E8", "A", opt([rm(4, "KCore.LibEvCeilE8Ref.no_such")]), False),
            ("E8", "A", opt([dict(rm(4), file=tie)]), False),
            ("E8", "A", opt([rm(4)], fixture="ok"), False),
        ]
        bad = []
        for i, (l, key, e, want) in enumerate(cases):
            have, miss = evidence(fx, l, key, e, e)
            if (not miss) != want:
                bad.append(f"case {i} ({l} {e.get('status')}): {'refused' if miss else 'accepted'}, expected "
                           f"{'accepted' if want else 'refused'}; missing {miss}")
        # a table nested in a hook: row: the hook's form where its fixture's reading implements the
        # symbol by the hook (or shows no reading), the form of a function of the text otherwise
        for name, prm in (("hk", "param\tLblx{Foo}\targs=[Foo]\tresult=Foo\timpl=Lblx\traw=false\n(exit 0)\n"),
                          ("own", "param\tLbly\targs=[]\tresult=Foo\timpl=none\traw=false\n(exit 0)\n")):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "account.txt"), "w").write(clean)
            open(os.path.join(fxd, name, "kompile.txt"), "w").write("exit 0\n")
            open(os.path.join(fxd, name, "params.txt"), "w").write(prm)
        hrow = {"status": "supported", "derived": [thm]}
        ncases = [  # (entry nested in the row hook:K.x:Lblx, the form expected, accepted)
            ({"status": "supported", "fixture": "hk", "derived": [thm]}, "supported hook", True),
            ({"status": "supported", "fixture": "hk"}, "supported hook", False),
            ({"status": "supported", "fixture": "ok", "derived": [thm]}, "supported hook", True),
            ({"status": "supported", "fixture": "own", "tie": [tie], "tie_theorems": ["KCore.C3EqReqEns.f_5"]},
             "supported function of the text", True),
            ({"status": "supported", "fixture": "own", "derived": [thm]}, "supported function of the text", False),
            ({"status": "supported", "fixture": "own"}, "supported function of the text", False),
            ({"status": "supported", "fixture": "own", "tie": [tie], "tie_theorems": ["KCore.C3EqReqEns.nope"]},
             "supported function of the text", False),
            ({"status": "supported", "fixture": "own", "tie": ["test/PrintNames.lean"],
              "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, "supported function of the text", False),
            ({"status": "supported", "fixture": "own", "derived": [thm], "tie": [tie]},
             "supported function of the text", True),
            ({"status": "supported", "derived": [thm]}, "supported hook", True),
        ]
        for i, (e, fwant, want) in enumerate(ncases):
            row = dict(hrow, cases=[e])
            fgot = form("E6", "hook:K.x:Lblx", e, row, fx)
            have, miss = evidence(fx, "E6", "hook:K.x:Lblx", e, row)
            if fgot != fwant or (not miss) != want:
                bad.append(f"nested hook case {i}: form {fgot!r} ({'refused' if miss else 'accepted'}), expected "
                           f"{fwant!r} ({'accepted' if want else 'refused'}); missing {miss}")
        rown = dict(hrow, fixture="own")
        if form("E6", "hook:K.x:Lblx", rown, rown, fx) != "supported hook":
            bad.append("the hook: row itself is given the form of a function of the text")
        t = {"C3": {"p": {"status": "supported", "core": True}}, "E6": {"hook:Y": {"status": "supported"}},
             "E2": {"N": {"status": "inert", "notes": {"x": "y"}}, "W": {"status": "supported", "fixture": "e2-clause-1"},
                    "R": {"status": "refused", "cone": "KCore.Term"}, "Q": {"status": "refused", "cone": "as R"},
                    "S": {"status": "supported", "cone": "none (reader only)"}}}
        held = {k for l, k, _, _, r in entries(t) if core(t, l, k, r)}
        if held != {"p", "hook:Y", "N", "W", "R"}:
            bad.append(f"core: {sorted(held)}")
        res = [("E2", "pending-fixture", "pending-fixture", "E2 'A'", None, [], ["a status"])]
        import contextlib, io
        with contextlib.redirect_stdout(io.StringIO()):
            codes = (print_check(res, True, False, None), print_check(res, True, True, None),
                     print_check([], True, False, None))
        if codes != (1, 0, 0):
            bad.append(f"check exit codes (failing, --report, none failing): {codes}, expected (1, 0, 0)")
        t = {"E2": {"P": {"status": "supported", "reader_does_it": False, "cases": [
                 {"case": "c", "status": "inert", "fixture": "rdr-x", "reader_does_it": False},
                 {"case": "d", "status": "refused", "fixture": "rdr-y", "reader_does_it": False}]},
                    "Q": {"status": "parameter", "reader_does_it": False},
                    "R": {"status": "supported", "reader_does_it": True}}}
        owed = [("T.one", ["rdr-x"]), ("T.two", ["E2 P"]), ("T.done", ["E2 Q"])]
        st = {"T.one": "running", "T.two": "pending", "T.done": "done"}
        got = [(w, tid, bool(why)) for w, tid, why in reader_owed(t, owed, st, False)]
        want = [("E2 'P'", "T.two", False), ("E2 'P' cases[0] ('c')", "T.one", False), ("E2 'Q'", "T.done", True)]
        if got != want:
            bad.append(f"reader_owed: {got}, expected {want}")
        got = [(w, tid, bool(why)) for w, tid, why in reader_owed(t, owed[:1], st, False)]
        if [x[2] for x in got] != [True, False, True] or got[0][1] is not None:
            bad.append(f"reader_owed without an owing ticket: {got}")
        if not all(why for _, _, why in reader_owed(t, owed, st, True)):
            bad.append("reader_owed --gate accepts an entry")
        ofx = os.path.join(d, "fixtures-owed")
        for name, acc in (("ow", "      rule 0: CondDecided open, over VarX:S\n"),
                          ("ow2", "      function f, clause 0 at ow2.k:3: CondDecided open, over VarH:S\n"),
                          ("no", clean), ("e2-clause-rhs-unit", clean), ("e2-clause-rhs-int", clean)):
            os.makedirs(os.path.join(ofx, name))
            open(os.path.join(ofx, name, "account.txt"), "w").write(acc)
        ofix = Fixtures(ofx, False)
        np = "; no fixture of this shape has it proved: s"
        b = {"status": "supported", "fixture": "ow2", "owed_state": {"ow2": "open: r" + np}}
        a = lambda **kw: {"status": "supported", "fixture": "ow", **kw}
        f5 = "KCore.C3EqReqEns.f_5"
        my, uf = "KCore.TieClauseRhsUnit.matchY", "test/TieClauseRhsUnit.lean"
        nop ="no fixture of the entry has its owed fact proved"
        ocases = [  # ({row key: entry} of E2, the failures expected, each named by a substring)
            ({"A": a(owed_state={"ow": f"proved: {f5} ({tie})", "ow2": "open: r"}, evidence="fixtures/ow2",
                     cases=[{"case": "c", "fixture": "ow2", "tie": [tie], "owed_state": {"ow2": f"refuted: {f5}" + np}}])}, []),
            ({"A": a(), "B": b}, ["the entry has no owed_state", "no entry's owed_state names"]),
            ({"A": a(owed_state={"ow": "open: r", "no": "open: r" + np}, evidence="fixtures/no"), "B": b},
             ["prints no `CondDecided open`"]),
            ({"A": a(owed_state={"ow": f"proved: KCore.C3EqReqEns.nope ({tie})"}), "B": b},
             [f"KCore.C3EqReqEns.nope is not declared in {tie}"]),
            ({"A": a(owed_state={"ow": f"refuted: {f5}" + np}, tie=["test/TieE1Module.lean"]), "B": b},
             ["is not declared in test/TieE1Module.lean"]),
            ({"A": a(owed_state={"ow": f"refuted: {f5}" + np}), "B": b}, ["names no file and the entry has no tie"]),
            ({"A": a(owed_state={"ow": f"proved: {f5} (test/PrintNames.lean)"}), "B": b}, ["skip list"]),
            ({"A": a(owed_state={"ow": "witnessed" + np}), "B": b}, ["is not 'proved: THEOREM"]),
            ({"A": a(owed_state={"ow": "open: r", "ow2": "open: r" + np})}, ["ow2 is no fixture of the entry"]),
            ({"A": a(owed_state={"ow2": "open: r" + np}, evidence="fixtures/ow2")},
             ["has no key for its fixture", "no entry's owed_state names"]),
            ({"A": a(owed_state="open: r"), "B": b}, ["not a table", "no entry's owed_state names"]),
            # no proved fixture: accepted with the ending on a refuted or an open state, refused without it
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})" + np}), "B": b}, []),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})", "ow2": "open: r" + np},
                     evidence="fixtures/ow2")}, []),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})"}), "B": b}, [nop]),
            ({"A": a(owed_state={"ow": "open: r"}), "B": b}, [nop]),
            ({"A": a(owed_state={"ow": "open: r"}), "B": {**b, "owed_state": {"ow2": "open: r"}}}, [nop, nop]),
            # the ending beside a proved state, or on the proved state itself
            ({"A": a(owed_state={"ow": f"proved: {f5} ({tie})", "ow2": "open: r" + np},
                     evidence="fixtures/ow2")}, ["beside a proved state"]),
            ({"A": a(owed_state={"ow": f"proved: {f5} ({tie})" + np}), "B": b}, ["beside a proved state"]),
            # a fixture the entry's text names whose account owes no CondDecided: admitted only with a
            # MatchIndependent proved on that fixture's own text, by a theorem of a named file
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})", "e2-clause-rhs-unit": f"proved: {my} ({uf})"},
                     evidence="fixtures/e2-clause-rhs-unit"), "B": b}, []),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})",
                                 "e2-clause-rhs-unit": f"proved: KCore.TieClauseRhsUnit.named ({uf})"},
                     evidence="fixtures/e2-clause-rhs-unit"), "B": b}, ["is not stated as a MatchIndependent"]),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})" + np, "e2-clause-rhs-unit": "open: r"},
                     evidence="fixtures/e2-clause-rhs-unit"), "B": b}, ["prints no `CondDecided open`, and its state"]),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})", "e2-clause-rhs-unit": f"proved: {my}"},
                     tie=[tie, uf], evidence="fixtures/e2-clause-rhs-unit"), "B": b},
             ["prints no `CondDecided open`, and its state"]),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})", "e2-clause-rhs-int": f"proved: {my} ({uf})"},
                     evidence="fixtures/e2-clause-rhs-int"), "B": b}, ["not fixtures/e2-clause-rhs-int's text"]),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})", "e2-clause-rhs-unit": f"proved: {my} ({uf})"}),
              "B": b}, ["its text does not name it"]),
            ({"A": a(owed_state={"ow": f"refuted: {f5} ({tie})", "rhsunit": f"proved: {my} ({uf})"},
                     evidence="f2-examples/rhsunit.kompile.kore"), "B": b}, ["rhsunit is no fixture with an account.txt"]),
        ]
        for i, (rows, want) in enumerate(ocases):
            got = [why for _, _, _, why in owed_state({"E2": rows}, ofix) if why]
            if len(got) != len(want) or not all(any(w in g for g in got) for w in want):
                bad.append(f"owed_state case {i}: failures {got}, expected {want}")
        for b in bad:
            print(f"rest self-test: FAILS: {b}")
        print(f"rest self-test: {len(cases)} entries, {len(ncases)} nested in a hook: row, the core predicate and"
              f" {len(ocases)} owed_state tables,"
              f" {len(bad)} failing")
        return 1 if bad else 0
    finally:
        shutil.rmtree(d, ignore_errors=True)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--self-test"]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
