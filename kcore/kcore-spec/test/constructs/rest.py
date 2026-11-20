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
      Then the E6 library rows (`e6_library`: a row of E6 of status supported or inert with an
      `e6_tie`, test/constructs/e6map.py; the tables nested in one are not among them): how many
      are tied, how many are in each group counted apart (E6 no direction (in a model), supported
      (no model), refuted (recorded)), and how many miss evidence, each of these listed with what
      it misses (an "uncovered: ..." e6_tie with the reason e6map gives)
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
      Then, where an entry carries `match_refuted` (rows-header.toml), one line naming those entries
      and their fixtures (an owed MatchIndependent refuted on a text whose reading has a model)
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
                   account_absent and absent_closed among tie_theorems, each declared in that file
                   or in a file of `tie` with the same text and classes (a tie --split writes over
                   several files); a `derived` table of form (a), kind "in a model", whose
                   sentences are the no_direction indices. The recorded exception (DONE-0 section
                   0, the subsort of a cell into its collection sort; item 7's last paragraph): an
                   entry whose `reasons` name UnreadReason.cellCollectionInjection carries in that
                   table's place a `derived` table of form (r), without kind and on its own
                   fixture, with its theorem among tie_theorems, whose sentences hold a
                   no_direction index that is a subsort sentence of the text (attribute
                   subsort{A, B}); every no_direction index is then a sentence applying inj{A, B}
                   of such a refuted one (no model holds the sentences of that head together, so
                   no table "in a model" of them exists). No other entry is exempted
      own sentence (B21, findings/work/wave-B-audit.md; also on supported E4, E5 and a function of
                   the text) an axiom of a fixture's text (`fixture`, `also_fixtures`) that a
                   `sentence` locates is not in `def uncovered` of a file of `tie` reading that
                   text (reads_own_text: its path, or a text byte for byte that fixture's), unless
                   another file of `tie` reading that text, not of the same text and classes as
                   that file (the same tie split over files) and not listing the axiom uncovered
                   itself, declares a theorem the entry names (`tie_theorems`, or a `derived`
                   table's theorem or consistent whose `file` it is): the sentence-level tie
                   (TieRuleLhsAnd, TieRuleConn, a Note file) of the sentence tiegen leaves out.
                   In a file reading several texts, one per namespace (TieRuleLhsAnd,
                   TieExClauseShapes), the theorem is one declared where that fixture's text is
                   the one in scope (declared_on_text); a theorem of another namespace's text
                   ties no sentence of this one.
                   An entry with no `sentence` is not checked; check --report lists the failures
                   apart
      tie          `tie` lists the C14 tie modules: files test/X.lean that test/integration.sh
                   builds (not in its skip list)
      theorems     the theorems the entry names, `tie_theorems` (full names, each declared in a
                   file of `tie`) and the `theorem`, `consistent` (form (r), kind "sentence
                   against the reading"), `inconsistent` and `from_sentences` (form (r), kind "with
                   the reading's families") of each `derived` table (declared in its `file`): at
                   least one, each declared
      match refuted on an entry with `match_refuted` (rows-header.toml; any supported form, E6's
                   aside, and on no other): each table names `fixture`, the entry's `fixture` or
                   one of its `also_fixtures`, once, whose account prints `MatchIndependent open`;
                   `owed_refuted` and `consistent`, declared in `file`, a file as `tie`'s above that
                   reads the fixture's text (reads_own_text); no other field; and the entry has no
                   form (r) table of that fixture other than of kind "sentence against the
                   reading". provenance.sh checks the statements; check prints the records on a
                   line of their own, and the entries stay in the headline count
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
  supported hook (E6, key hook:): the hook's three statements (DONE-0 C2)
      derived      a `derived` table of form (a): the in-domain value
      silent       on the row itself, unless it is a hooked sort (the key's last part starts with
                   Sort: no argument list): `silent_statement`, a non-empty list of tables
                   { theorem, file }: the silent predicate is the region the prose excludes or
                   leaves unstated, or the hook is no key of silentTable and the prose covers every
                   argument list (test/provenance.sh checks the statements)
      region       on the row of a key of silentTable (test/constructs/silentkeys.py): a `derived`
                   table of form (c), the param_undetermined shape at a point of that region
      A table nested in the row whose fixture's reading implements the symbol by the hook needs
      the form (a) table only: the three statements are the row's.
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
                   where k are, or "module of hooks and generated declarations only: ..." (accounted
                   by its declarations' rows); a bare "uncovered: ...", "no direction: ..." without
                   an item "...; in a model)", and "refuted: ..." on a row that names no recorded
                   ruling (a finding for DONE-0 2.6) are missing evidence
  The E6 library rows of the groups e6map counts apart (decision-e6-uncovered section 2), of status
  supported (or inert, an E6 lemma row), each with its own form; every theorem item of the e6_tie
  string declared in its FILE, a tie file as above:
  E6 no direction (in a model)
      "no direction: MODULE; ..." with at least one item "THEOREM (FILE; ...; in a model)" (a theorem
      of kind "in a model" naming the sentence or declaration, rows-header.toml item 7), beside the
      class's theorems; or, on a module row, "no direction in a model: MODULE; every ... row of
      MODULE (n) is ..." (every member of no direction with a theorem in a model)
  supported (tied under a domain premise) (left out of the headline count: an entry of a supported
  form above, E6's aside, with `tie_premise`, rows-header.toml): its form's items, and
      tie premise  each table of `tie_premise` has non-empty `sentences`, `premise`, a boolean
                   `in_gamma`, `ground`, `theorem`, `consistent`, `converse` or `at_values`, and
                   `needed` where in_gamma is false, each theorem declared in a file of `tie`
                   (`needed` and `at_values` also among tie_theorems); each of
                   its sentences is in `def underPremise` of a file of `tie` reading the entry's text,
                   with that premise (tiegen --hand rules, a premise form). On a supported entry
                   without the field, a sentence `sentence` locates that such a file lists in
                   `underPremise` is missing its table. provenance.sh checks the statements
  supported (no model) (left out of the headline count: Γ of every text holding the sentence has
  no model, so an entailment there is vacuous)
      "no model: MODULE; ..." with an item "...; no model)" (the no-model theorem of a form (r)
      table) and an item stating that Γ's item of it is its translation; or, on a module row, "no
      model: MODULE; every ... row of MODULE (n) is ..." (its members' weakest group)
  refuted (recorded)
      "refuted: MODULE; ..." on a row whose `refuted_ruling` names the recorded ruling (it holds
      "DONE-0 section 0 (4)" or a decision file decision-*.md), with its refuting theorems; or, on a
      module row, "refuted (recorded): MODULE; every ... row of MODULE (n) is ..."
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
      reasons      `reasons` holds RefusalReason.X items; or `core_failing` (below) in their place
      account      a fixture of the entry (`fixture`, `also_fixtures`) whose account prints each of
                   them (a refusal line or a class line, as closed.py reads accounts), and, for
                   each, a line of such an account that prints it and that the entry quotes between
                   back quotes in evidence, reader_today, refused_by, place, note, reason or
                   reader_reason: the line from its start (whole, or a prefix of it holding the
                   reason's name), or from the reason's name, where the line writes it after
                   `): `, into its detail; an ellipsis (…) in the quotation stands for any text; the
                   reason's name alone quotes no line (DONE-0 C2: the account prints exactly the
                   named reason, on the sentence the entry says); or, for an
                   entry kompile refuses (unit "none (scope): rejected", or class R-b with an error
                   fixture), its fixture is an error fixture (fixture.toml expect = "error") and
                   `reasons` is not needed; or, for an option that writes no definition (unit
                   "none (scope): option", `shape` "none: ..."), a fixture of the entry whose
                   kompile.txt holds `definition.kore: none written`, and `reasons` is not needed
      option row   instead of a RefusalReason, on an entry outside E8 of unit "none (scope): option"
                   with no RefusalReason item whose `shape` is "E8 <row key>" (a pass or construct that acts only under that
                   option): the E8 row exists, is refused of class scope or R-b, and has its own
                   evidence here; and a fixture of the entry is an error fixture (fixture.toml
                   expect = "error") whose kompile.txt `command:` passes R-12's options only (kompile
                   refuses the text under default options) or passes that option (kompile refuses
                   it under the option): no definition kompile delivers holds what the entry names
      undelivered  instead of a RefusalReason, on an entry of unit "none (scope): not delivered"
                   with no RefusalReason item (the reader reads the frontend's sentence): a fixture
                   of the entry is an error fixture whose kompile.txt records a non-zero exit and the
                   validator's `Error` in its output, and another is a hand-written text (fixture.toml
                   `kore`) whose account refuses nothing, is fresh, and prints a ReadingNote that the
                   entry's `refused_by` or `evidence` names (the sentence read)
      scope        instead of a RefusalReason, on an E8 option row of class R-b or scope (the row's
                   key the option): `reasons` holds SCOPE_OPTION ("none (scope): option"), and a
                   fixture of the entry has kompile.txt's `command:` passing the option outside R-12's
                   option set (an argument other than `--backend haskell`, or `--backend` with another
                   value); RefusalReason items beside it are checked as above (what the reader answers
                   on the text the option gives); the item on another entry is missing evidence
      core failing instead of a RefusalReason, on a text the reader reads but whose semantics
                   fails coreOK: `core_failing`, a non-empty list of conjunct names of coreOK as
                   KcoreGen.coreParts names them, equal as a set to the `failing:` list of the line
                   `coreOK: false; failing: [...]` that the account of a fixture of the entry prints
                   (where `reasons` is also given, its items are checked as above)
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


E6_ND, E6_NM, E6_REF = "E6 no direction (in a model)", "supported (no model)", "refuted (recorded)"
E6_GROUPS = (E6_ND, E6_NM, E6_REF)
# A supported entry with a `tie_premise` table: its sentences tied under a premise that no sentence of
# the text states (rows-header.toml, field tie_premise).
PREMISE_FORM = "supported (tied under a domain premise)"
SUPPORTED_TIED = ("supported", "supported E4/E5", "supported function of the text")
# Left out of the headline count: Γ of the text has no model (decision-e6-uncovered section 3); the
# sentences are tied under a premise, not by the text with no premise.
APART = (E6_NM, PREMISE_FORM)
E6_ITEM = re.compile(r"(\S+) \((test/[^;()]+\.lean); ([^()]*)\)")
RULING = re.compile(r"DONE-0 section 0 \(4\)|\bdecision-[\w-]+\.md\b")


def e6_group(key, e):
    """The group of an E6 library row by its `e6_tie` (e6map.py), or None: E6_ND for "no direction:
    ..." with an item "...; in a model)" or a module row's "no direction in a model: ..."; E6_NM for
    "no model: ..."; E6_REF for "refuted: ..." on a row with a string field `refuted_ruling`, or a
    module row's "refuted (recorded): ..."."""
    v = e.get("e6_tie")
    if not isinstance(v, str):
        return None
    if (v.startswith("no direction: ") and any(m[3].endswith("; in a model") for m in E6_ITEM.finditer(v))) \
            or v.startswith("no direction in a model: "):
        return E6_ND
    if v.startswith("no model: "):
        return E6_NM
    if (v.startswith("refuted: ") and isinstance(e.get("refuted_ruling"), str)) or v.startswith("refuted (recorded): "):
        return E6_REF
    return None


def form(l, key, e, row=None, fx=None):
    """The evidence form of DONE-0 C2's table for the entry's status, or None without a status: that
    of `base_form`, and PREMISE_FORM for an entry of one of the forms SUPPORTED_TIED with a
    `tie_premise` field (`base_form` gives the items it needs beside its tables)."""
    f = base_form(l, key, e, row, fx)
    return PREMISE_FORM if f in SUPPORTED_TIED and e.get("tie_premise") is not None else f


def base_form(l, key, e, row=None, fx=None):
    """The evidence form of DONE-0 C2's table for the entry's status, or None without a status.
    With the entry's row and the fixtures, a table nested in an E6 `hook:` row whose reading takes
    the symbol for a function of the text has that form (`hook_own`). An E6 library row of status
    supported or inert whose `e6_tie` is of a group e6map counts apart has that group's form
    (`e6_group`)."""
    s = e.get("status")
    if s is None:
        return None
    if l == "E6" and s in ("supported", "inert") and e.get("e6_tie") is not None and e6_group(key, e):
        return e6_group(key, e)
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
        self.core_parts = core_part_names()
        self.rows = rows
        self._silent = None

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

    def silent_key(self, key):
        """Whether the E6 row `key` is the row of a key of silentTable (silentkeys.py reads the keys
        from the sources, as test/provenance.sh does)."""
        if self._silent is None:
            import silentkeys
            _, hook, kore = silentkeys.key_names()
            self._silent = (silentkeys, hook, kore)
        sk, hook, kore = self._silent
        return sk.keyed(key, hook, kore)

    def account_lines(self, name):
        """The lines of the fixture's account.txt, stripped (empty without one)."""
        return [ln.strip() for ln in (self.read(name, "account.txt") or "").splitlines()]

    def core_failing(self, name):
        """The conjuncts of coreOK the account prints as failing (its line `coreOK: B; failing:
        [...]`, an empty list where B is true), or None without account.txt or that line."""
        a = self.read(name, "account.txt")
        m = re.search(r"^coreOK: (true|false); failing: \[(.*)\]$", a or "", re.M)
        if not m:
            return None
        return [x.strip() for x in m[2].split(", ") if x.strip()]

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


# The fields of an entry whose back-quoted strings are read as quotations of an account's lines.
QUOTE_FIELDS = ("evidence", "reader_today", "refused_by", "place", "note", "reason", "reader_reason")


def quoted(e):
    """The strings an entry writes between back quotes in QUOTE_FIELDS."""
    return [q.strip() for f in QUOTE_FIELDS if isinstance(e.get(f), str) for q in re.findall(r"`([^`]+)`", e[f])]


def reason_lines(lines, r):
    """The lines of an account (stripped) that print the refusal reason r: those holding its name as
    a word (a refusal line `sentence N (SYMBOL): r (detail)`, its `finish:` copy, a class line
    `N refused r [origin]`, a count line `N r`), and a COUNTED line of r with a count above 0."""
    word = re.compile(r"(?<!\w)" + re.escape(r) + r"(?!\w)")
    return [L for L in lines if word.search(L)
            or any(c == r and re.match(re.escape(start) + r"[1-9]", L) for start, c in COUNTED)]


def quote_is_line(q, r, L):
    """Whether the quotation q is of the account line L, which prints the reason r: q, an ellipsis
    (…) in it standing for any text, is L from its start (L whole or a prefix of it), or starts
    at the reason's name where L writes it after `): ` and goes on into its detail. The reason's name
    alone quotes no line. A COUNTED line does not write the name: q is then L from its start, with
    its count."""
    if not q or q == r:
        return False
    counted = [start for start, c in COUNTED if c == r and L.startswith(start)]
    named = re.search(r"(?<!\w)" + re.escape(r) + r"(?!\w)", q)
    if not named and not (counted and re.match(re.escape(counted[0]) + r"[1-9]", q)):
        return False
    m = re.match(".*".join(re.escape(part) for part in q.split("…")), L)
    if m:
        return True
    if not q.startswith(r):
        return False
    at = L.find("): " + r)
    return at >= 0 and bool(re.match(".*".join(re.escape(part) for part in q.split("…")), L[at + 3:]))


def core_part_names():
    """The names of coreOK's conjuncts, as KcoreGen.coreParts pairs each with its check (the names
    the account's line `coreOK: B; failing: [...]` prints)."""
    src = open(os.path.join(K, "KcoreGen.lean")).read()
    block = src.split("\ndef coreParts ", 1)[1].split("\n\n", 1)[0]
    return re.findall(r'\("([^"]+)", ', block)


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
    # a tie written over several files (tiegen --split) may state account_absent and absent_closed
    # in a file other than the account's: each file of `tie` with the same text and the same
    # classes is a file of that tie
    tfs = [tf] + [f for f in ts if f != tf and nodir_classes(f) == (text, cls)]
    lack = [t for t in ("account", "account_absent", "absent_closed")
            if not any(n.endswith("." + t) and declared(n, tfs) for n in names)]
    (have if not lack else miss).append(
        f"the class's statement ({tf}: account, account_absent, absent_closed)" if not lack else
        f"the class's statement ({', '.join(lack)} of {tf} not in tie_theorems)")
    tabs = [d for d in (e.get("derived") or []) if isinstance(d, dict) and d.get("form") == "a"
            and d.get("kind") == "in a model" and isinstance(d.get("sentences"), list)]
    hit = [d for d in tabs if nd and set(d["sentences"]) == set(nd)]
    if hit:
        have.append("derived form a, in a model")
        return
    exc = cellcoll_refuted(e, x, nd, text, names) if nd else None
    if exc and exc[0]:
        have.append(exc[1])
        return
    miss.append("derived of form a, kind 'in a model', whose sentences are the no_direction indices"
                + (f" ({len(tabs)} of that kind with other sentences)" if tabs else "")
                + (f"; or the cell-collection subsort exception's table ({exc[1]})" if exc else ""))


CELLCOLL_REASON = "UnreadReason.cellCollectionInjection"


def cellcoll_refuted(e, x, nd, text, names):
    """The recorded exception to item 7's table 'in a model' (DONE-0 section 0, the subsort of a cell
    into its collection sort; rows-header.toml item 7): None where the entry does not name it
    (`reasons` without UnreadReason.cellCollectionInjection), else (ok, what). It holds where a
    `derived` table of form (r) without kind, on the entry's own fixture x, whose theorem is among
    tie_theorems (names), has among its sentences a no_direction index (nd) that is a subsort
    sentence of the text (attribute subsort{A, B}), and every no_direction index is a sentence
    applying inj{A, B} of such a refuted one: the sentences of a head whose subsort sentence has no
    model with Γ have no model together, so no table 'in a model' of them exists."""
    if CELLCOLL_REASON not in (e.get("reasons") or []):
        return None
    ax = {i: t for i, t, _ in nodir_axioms(text)}
    tabs = [d for d in (e.get("derived") or []) if isinstance(d, dict) and d.get("form") == "r"
            and d.get("kind") is None and d.get("fixture") in (None, x) and d.get("theorem") in names
            and isinstance(d.get("sentences"), list)]
    if not tabs:
        return False, "no derived table of form r, without kind, on the entry's fixture, with its theorem in tie_theorems"
    for d in tabs:
        heads = {f"inj{{{m[1]}, {m[2]}}}" for i in set(d["sentences"]) & set(nd)
                 for m in re.finditer(r"\[subsort\{(\S+\{\}), (\S+\{\})\}\(\)\]", ax.get(i, ""))}
        out = [i for i in nd if not any(h in ax.get(i, "") for h in heads)]
        if heads and not out:
            return True, (f"derived form r in place of the table in a model ({d['theorem'].rsplit('.', 1)[-1]}: no model"
                          f" with {', '.join(sorted(heads))}'s subsort sentence; the cell-collection subsort exception)")
    return False, ("no form r table refutes a subsort sentence among no_direction" if not heads else
                   f"{out[:3]} of no_direction apply no injection whose subsort sentence the table refutes")


_unc = {}


def tie_uncovered(f):
    """(the text the tie file reads by `kore_term kore from`, the indices of its `def uncovered`),
    or None where it has no such text or no `uncovered` (a file tiegen does not write)."""
    if f not in _unc:
        p = os.path.join(K, f) if isinstance(f, str) else None
        r = None
        if p and os.path.isfile(p):
            src = open(p).read()
            m = re.search(r'^kore_term kore from "([^"]+)"', src, re.M)
            i = src.find("\ndef uncovered : List (Nat × String) :=")
            if m and i >= 0:
                body = src[i + 1:].split("\n\n", 1)[0].split(":=", 1)[1]
                r = (m[1], {int(n) for n in re.findall(r"\(\s*(\d+)\s*,", body)})
        _unc[f] = r
    return _unc[f]


_upr = {}


def tie_under_premise(f):
    """(the text the tie file reads by `kore_term kore from`, {index: premise} of its `def
    underPremise`), or None where it has no such text or no `underPremise` (tiegen writes it only
    where a hand section on the rules ties a sentence under a premise)."""
    if f not in _upr:
        p = os.path.join(K, f) if isinstance(f, str) else None
        r = None
        if p and os.path.isfile(p):
            src = open(p).read()
            m = re.search(r'^kore_term kore from "([^"]+)"', src, re.M)
            i = src.find("\ndef underPremise : List (Nat × String) :=")
            if m and i >= 0:
                body = src[i + 1:].split("\n\n", 1)[0].split(":=", 1)[1]
                r = (m[1], {int(n): q for n, q in re.findall(r'\(\s*(\d+)\s*,\s*"([^"]*)"\s*\)', body)})
        _upr[f] = r
    return _upr[f]


TIE_PREMISE_NAMES = ("theorem", "converse", "needed", "at_values", "consistent")


def tie_premise_items(fx, e, own, have, miss):
    """On a supported entry: each table of `tie_premise` (rows-header.toml) is evidence for its
    sentences, tied under its premise. It has non-empty `sentences` (indices), `premise` (the name
    tiegen writes in `underPremise`), `in_gamma` (a boolean), `ground`, `theorem` and `consistent`,
    `converse` or `at_values` (at least one: the other direction), and `needed` where in_gamma is
    false; each named theorem declared in a file of `tie`, `needed` and `at_values` also among
    `tie_theorems`; and each sentence is in `underPremise`, with
    that premise, of a file of `tie` reading a text of the entry's fixtures. Without the field: a
    sentence `sentence` locates that such a file lists in `underPremise` is missing its table."""
    ts = e.get("tie")
    ts = list(dict.fromkeys(f for f in (ts if isinstance(ts, list) else [ts] if ts else []) if isinstance(f, str)))
    under = {}
    for x in own:
        for f in ts:
            u = tie_under_premise(f)
            if u and reads_own_text(f, x):
                for i, q in u[1].items():
                    under.setdefault(i, []).append((q, f, u[0]))
    tp = e.get("tie_premise")
    if tp is None:
        ss = e.get("sentence")
        ss = ss if isinstance(ss, list) else [ss] if isinstance(ss, str) else []
        for i, ws in sorted(under.items()):
            for q, f, path in ws:
                if ss and i in fx.located(path, ss)[0]:
                    miss.append(f"tie_premise: sentence {i}, which `sentence` locates, is in `underPremise` of {f}"
                                f" (under {q}), and the entry has no tie_premise table for it")
        return
    if not (isinstance(tp, list) and tp and all(isinstance(d, dict) for d in tp)):
        miss.append("tie_premise (not a non-empty list of tables)"); return
    for k, d in enumerate(tp):
        at = f"tie_premise[{k}]"
        ss, q = d.get("sentences"), d.get("premise")
        why = []
        if not (isinstance(ss, list) and ss and all(isinstance(i, int) and not isinstance(i, bool) for i in ss)):
            why.append("`sentences` not a non-empty list of indices")
        if not (isinstance(q, str) and q.strip()):
            why.append("no `premise`")
        if not isinstance(d.get("in_gamma"), bool):
            why.append("`in_gamma` not a boolean")
        if not (isinstance(d.get("ground"), str) and d["ground"].strip()):
            why.append("no `ground`")
        for n in ("theorem", "consistent") + (("needed",) if d.get("in_gamma") is False else ()):
            if not isinstance(d.get(n), str):
                why.append(f"no `{n}`")
        if not any(isinstance(d.get(n), str) for n in ("converse", "at_values")):
            why.append("neither `converse` nor `at_values` (the other direction)")
        bad = [d[n] for n in TIE_PREMISE_NAMES if isinstance(d.get(n), str) and not declared(d[n], ts)]
        if bad:
            why.append(f"{', '.join(bad[:2])} not declared in a file of `tie`")
        unnamed = [d[n] for n in ("needed", "at_values") if isinstance(d.get(n), str)
                   and d[n] not in (e.get("tie_theorems") or [])]
        if unnamed:
            why.append(f"{', '.join(unnamed)} not among tie_theorems")
        if why:
            miss.append(f"{at} (" + "; ".join(why) + ")"); continue
        out = [i for i in ss if not any(q_ == q for q_, _, _ in under.get(i, []))]
        if out:
            miss.append(f"{at}: sentence {out[0]} is in no `underPremise` of a file of `tie` reading the entry's"
                        f" text with the premise {q}" + (f" (there under {under[out[0]][0][0]})" if under.get(out[0]) else ""))
            continue
        have.append(f"tied under a domain premise: {', '.join(map(str, ss))} under {q} "
                    f"({under[ss[0]][0][1]} underPremise)")


def uncovered_items(fx, e, own, have, miss):
    """B21 (findings/work/wave-B-audit.md) on a supported entry: an axiom of a fixture's text that
    the entry's `sentence` locates is not in `uncovered` of a file of `tie` reading that text
    (reads_own_text), unless another file of `tie` that reads the text, and is not that tie (a file
    of the same text and classes is the same tie split over files), declares a theorem the entry
    names (`tie_theorems`, or a `derived` table's theorem or consistent whose `file` it is): the
    sentence-level tie of the sentence that tiegen's account leaves uncovered. In a file reading
    several texts the theorem is declared where the fixture's text is in scope (declared_on_text)."""
    ss = e.get("sentence")
    ss = ss if isinstance(ss, list) else [ss] if isinstance(ss, str) else []
    ts = e.get("tie")
    ts = list(dict.fromkeys(f for f in (ts if isinstance(ts, list) else [ts] if ts else []) if isinstance(f, str)))
    if not ss or not ts:
        return
    names = [n for n in (e.get("tie_theorems") or []) if isinstance(n, str)]
    by_file = collections.defaultdict(list)
    for d in e.get("derived") or []:
        if isinstance(d, dict) and isinstance(d.get("file"), str):
            by_file[d["file"]] += [d[k] for k in ("theorem", "consistent") if isinstance(d.get(k), str)]
    out, ok = [], []
    for x in own:
        for f in ts:
            u = tie_uncovered(f)
            if not u or not u[1] or not reads_own_text(f, x):
                continue
            loc, _ = fx.located(u[0], ss)
            for i in sorted(loc & u[1]):
                comp = [g for g in ts if g != f and reads_own_text(g, x)
                        and not (nodir_classes(g) and nodir_classes(g) == nodir_classes(f))
                        and i not in ((tie_uncovered(g) or ("", set()))[1])
                        and any(declared_on_text(n, g, x) for n in names + by_file.get(g, []))]
                (ok if comp else out).append((x, f, i, comp))
    for x, f, i, comp in ok:
        have.append(f"own sentence {i} of {x}, uncovered in {f}, tied by {comp[0]}")
    for x, f, i, _ in out:
        miss.append(f"uncovered sentence: {i} of {x}, which `sentence` locates, is in `uncovered` of {f},"
                    " and no other file of `tie` reading that text declares a theorem the entry names")


# An owed MatchIndependent refuted on a text whose reading has a model (rows-header.toml, field
# match_refuted): the field, its tables' fields, and an account's line of a clause whose
# MatchIndependent is owed (the package's match_named).
MR_KEY = "match_refuted"
MR_FIELDS = ("fixture", "owed_refuted", "consistent", "file")
MATCH_OPEN = re.compile(r"^\s+(.+): MatchIndependent open\b", re.M)


def match_refuted_tables(e):
    """The tables of the entry's `match_refuted` (a table, or a non-empty list of tables), [] without
    the field, None where it is neither."""
    v = e.get(MR_KEY)
    if v is None:
        return []
    if isinstance(v, dict):
        return [v]
    return v if isinstance(v, list) and v and all(isinstance(d, dict) for d in v) else None


def match_refuted_items(fx, e, f, have, miss):
    """On an entry with `match_refuted` (rows-header.toml): it is of a supported form (SUPPORTED_TIED),
    and each table names a fixture of the entry (`fixture`, `also_fixtures`), once, whose account
    prints `MatchIndependent open`; `owed_refuted`, `consistent` and `file` and no other field; `file` a
    tie file (tie_file_ok) reading the fixture's text (reads_own_text) and declaring both theorems;
    and no form (r) table of the entry, of the same fixture, other than of kind "sentence against
    the reading" (a text without a model has no model of its reading). provenance.sh checks the
    statements."""
    ds = match_refuted_tables(e)
    if ds is None:
        miss.append(f"{MR_KEY} (not a table or a non-empty list of tables)"); return
    if f not in SUPPORTED_TIED:
        miss.append(f"{MR_KEY} on an entry of form {f!r} (it is the record of a supported entry)"); return
    own = [x for x in [e.get("fixture")] + list(e.get("also_fixtures") or []) if isinstance(x, str)]
    nomodel = {(d.get("fixture") or e.get("fixture")): d.get("theorem") for d in (e.get("derived") or [])
               if isinstance(d, dict) and d.get("form") == "r" and d.get("kind") != "sentence against the reading"}
    seen = set()
    for k, d in enumerate(ds):
        at = MR_KEY + (f"[{k}]" if len(ds) > 1 else "")
        x, th, cs, fl = (d.get(n) for n in MR_FIELDS)
        why = [f"no `{n}`" for n in MR_FIELDS if not (isinstance(d.get(n), str) and d[n].strip())]
        why += [f"field `{n}` is none of {', '.join(MR_FIELDS)}" for n in d if n not in MR_FIELDS]
        if isinstance(x, str) and x.strip():
            if x not in own:
                why.append(f"`fixture` {x} is not the entry's `fixture` or one of its `also_fixtures`")
            elif not fx.exists(x):
                why.append(f"no directory fixtures/{x}")
            elif x in seen:
                why.append(f"a second table for {x}")
            elif not MATCH_OPEN.search(fx.read(x, "account.txt") or ""):
                why.append(f"fixtures/{x}'s account prints no `MatchIndependent open` (no owed match independence)")
            elif x in nomodel:
                why.append(f"beside a form (r) table of {x} ({nomodel[x]}: its text has no model)")
        if isinstance(fl, str) and fl.strip():
            w = tie_file_ok(fl)
            if w:
                why.append(w)
            else:
                out = [n for n in (th, cs) if isinstance(n, str) and n.strip() and not declared(n, [fl])]
                if out:
                    why.append(f"{', '.join(out)} not declared in {fl}")
                if isinstance(x, str) and x in own and fx.exists(x) and not reads_own_text(fl, x):
                    why.append(f"{fl} does not read fixtures/{x}'s text")
        if isinstance(x, str):
            seen.add(x)
        if why:
            miss.append(f"{at} (" + "; ".join(why) + ")"); continue
        have.append(f"owed match independence refuted, the reading has a model: {x} ({th}; {cs}, {fl})")


def print_match_refuted(t):
    """The entries recording an owed MatchIndependent refuted on a text with a model, on a line of
    their own (nothing where none does); they stay in the headline count."""
    rs = [(where, d.get("fixture")) for _, _, where, e, _ in entries(t) for d in (match_refuted_tables(e) or [])]
    if rs:
        print(f"match-refuted: {len({w for w, _ in rs})} entries record an owed MatchIndependent refuted on a text"
              f" whose reading has a model (owed fact false; in the headline count), {len(rs)} tables: "
              + "; ".join(f"{w} ({x})" for w, x in rs))


def declared(name, files):
    """Whether the full name is declared in one of the files (a declaration's name may also be a
    suffix of it)."""
    for f in files:
        ds = file_decls(f)
        if ds is not None and (name in ds or any(name.endswith("." + d) for d in ds)):
            return True
    return False


_scope = {}


def decl_scope_texts(f):
    """{full declaration name: the text in scope at it} of a Lean file: the path of the last
    `... from "f2-examples/..."` line before the declaration in its innermost enclosing namespace
    that has one (None before any). Namespaces and declarations as file_decls reads them."""
    if f not in _scope:
        out, stack, cur = {}, [], [(0, None)]
        for line in (lean_source(f) or "").split("\n"):
            s = line.strip()
            m = re.match(r"namespace (\S+)", s)
            if m:
                stack.append(m[1]); continue
            m = re.match(r"end (\S+)$", s)
            if m and stack and stack[-1] == m[1]:
                stack.pop()
                while len(cur) > 1 and cur[-1][0] > len(stack):
                    cur.pop()
                continue
            m = re.search(r'\bfrom\s+"(f2-examples/[^"]+)"', s)
            if m:
                if cur[-1][0] == len(stack):
                    cur[-1] = (len(stack), m[1])
                else:
                    cur.append((len(stack), m[1]))
                continue
            m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                         r"(?:theorem|lemma|def|abbrev|instance|example) ([^\s:({\[]+)", s)
            if m:
                d = m[1].strip("«»")
                out[".".join(stack + [d]) if not d.startswith("_root_.") else d[7:]] = cur[-1][1]
        _scope[f] = out
    return _scope[f]


def declared_on_text(name, f, x):
    """Whether the file declares the name (as `declared`) where fixture x's own text is the one in
    scope. A file reading one text at most is on that text throughout (reads_own_text is the
    caller's check); in a file reading several, each in a namespace of its own, the declaration's
    text in scope is f2-examples/x.kompile.kore or byte for byte x's text."""
    if not declared(name, [f]):
        return False
    sc = decl_scope_texts(f)
    if len({q for q in sc.values() if q}) <= 1:
        return True
    qs = {q for d, q in sc.items() if q and (name == d or name.endswith("." + d))}
    t = None
    for q in sorted(qs):
        if q == f"f2-examples/{x}.kompile.kore":
            return True
        t = own_text(x) if t is None else t
        if t is not None and os.path.isfile(os.path.join(K, q)) and open(os.path.join(K, q)).read() == t:
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


def r12_command(fx, x):
    """The fixture's kompile.txt `command:` line passes R-12's options only, each with R-12's value
    (`-o` aside): the text kompiled under default options."""
    m = re.search(r"^command: kompile (.*?)(?:  \(cwd: [^)]*\))?$", fx.read(x, "kompile.txt") or "", re.M)
    if not m:
        return False
    args, i = m[1].split(), 0
    while i < len(args):
        a = args[i]
        if a == "-o":
            i += 2; continue
        if a.startswith("-"):
            if a not in R12_OPTIONS or args[i + 1:i + 2] != [R12_OPTIONS[a]]:
                return False
            i += 2; continue
        i += 1
    return True


def validator_error(fx, x):
    """The fixture's kompile.txt records a non-zero exit and an `Error` in kompile's output."""
    k = fx.read(x, "kompile.txt") or ""
    out = k.split("\noutput:\n", 1)
    return bool(re.search(r"^exit: [1-9]\d*$", k, re.M)) and len(out) == 2 and "Error" in out[1]


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
        thms += [(d.get(k), [d.get("file")]) for d in (e.get("derived") or [])
                 for k in ("theorem", "consistent", "inconsistent", "from_sentences") if isinstance(d, dict) and d.get(k)]
        if not thms:
            miss.append("theorems")
        else:
            bad = [n for n, fs in thms if not declared(n, fs)]
            item(not bad, f"theorems ({len(thms)})", f"theorems ({', '.join(bad[:2])} not declared)")
        return ok

    def e6_items(v, what):
        """The theorem items "THEOREM (FILE; ...)" of an e6_tie string after its first "; ", each
        theorem declared in its FILE, a tie file; False (missing noted) otherwise or where none."""
        its = list(E6_ITEM.finditer(v.split("; ", 1)[1] if "; " in v else ""))
        if not its:
            miss.append(f"theorems (e6_tie: {what}: no theorem item)"); return None
        files = sorted({m[2] for m in its})
        why = [w for w in map(tie_file_ok, files) if w]
        item(not why, "tie " + ", ".join(files) + " (e6_tie)", "tie (e6_tie: " + "; ".join(why) + ")")
        bad = [m[1] for m in its if not declared(m[1], [m[2]])]
        item(not bad, f"theorems ({len(its)}, e6_tie)", f"theorems (e6_tie: {', '.join(bad[:2])} not declared)")
        return its if not why and not bad else None

    def e6_ties():
        """An E6 library row's `e6_tie` (test/constructs/e6map.py): "THEOREM (FILE; TEXT axiom N)" items,
        "every ... row of MODULE (n) is tied" or "module of hooks and generated declarations only: ..."
        on a module row, or "uncovered: ..."; a module row of form (m) also has a last item "not held
        by TEXT: ..." (the module's sentences inside a block comment of its code, no sentences of the
        module), which names no theorem; a live sentence the text does not hold makes the row
        "uncovered: ..." instead, unless an instance the row's `instances` names ties it (its items
        are then theorem items like the others). The groups counted apart (`e6_group`): "no
        direction: ..." with a theorem in a model; "no model: ..." with the no-model theorem and one
        that Γ's item is the translation; "refuted: ..." where the row's `refuted_ruling` names a
        recorded ruling; and a module row's "no direction in a model: ...", "refuted (recorded):
        ..." or "no model: ..." (its members' weakest group, e6map's module form)."""
        v = e.get("e6_tie")
        v = v if isinstance(v, list) else [v]
        unc = [x for x in v if isinstance(x, str) and x.startswith("uncovered")]
        if unc or not v:
            miss.append("theorems (e6_tie: " + (unc[0][:80] if unc else "empty") + ")"); return False
        x0 = v[0] if len(v) == 1 and isinstance(v[0], str) else None
        if key.startswith("module:") and x0 and re.match(
                r"(no direction in a model|refuted \(recorded\)|no model): \S+; every axiom, lemma, sort and symbol "
                r"row of \S+ \(\d+\) is ", x0):
            have.append(f"module row in its members' group: {x0.split(':')[0]} (e6_tie)"); return True
        if x0 and x0.startswith("no direction: "):
            its = [m for m in E6_ITEM.finditer(x0) if m[3].endswith("; in a model")]
            if not its:
                miss.append("theorems (e6_tie: " + x0.split(";")[0] + ": of the tie's no-direction class, with no"
                            " theorem in a model naming it; owed-sentence rule item 7)"); return False
            got = e6_items(x0, "no direction")
            if got:
                have.append(f"of no direction with a theorem in a model ({len(its)}, e6_tie)")
            return bool(got)
        if x0 and x0.startswith("no model: "):
            its = list(E6_ITEM.finditer(x0))
            if not any(m[3].endswith("; no model") for m in its) or all(m[3].endswith("; no model") for m in its):
                miss.append("theorems (e6_tie: no model: the no-model theorem and one that Γ's item is the"
                            " translation)"); return False
            got = e6_items(x0, "no model")
            if got:
                have.append("of a text without a model, Γ's item the translation (e6_tie; counted apart)")
            return bool(got)
        ref = [x for x in v if isinstance(x, str) and x.startswith("refuted")]
        if ref:
            rr = e.get("refuted_ruling")
            if not (isinstance(rr, str) and RULING.search(rr)):
                miss.append("theorems (e6_tie: " + ref[0].split(";")[0] + ": Γ refutes the sentence or entails it"
                            " only partly, no tie, and `refuted_ruling` names no recorded ruling (DONE-0 section 0"
                            " (4) or a decision file); a finding for DONE-0 2.6)"); return False
            got = e6_items(ref[0], "refuted")
            if got:
                have.append(f"refuted, its recorded ruling named ({rr[:60]}) (e6_tie)")
            return bool(got)
        if all(isinstance(x, str) and re.match(r"every .* row of \S+ \(\d+\) is tied"
                                               r"(, or of no direction with a theorem in a model \(\d+\))?$", x) for x in v):
            have.append("tie: every row of the module tied (e6_tie)"); return True
        if len(v) == 1 and isinstance(v[0], str) and v[0].startswith("module of hooks and generated declarations only: "):
            have.append("module of hooks and generated declarations only, accounted by its declarations' rows (e6_tie)")
            return True
        v = [x for x in v if not (isinstance(x, str) and x.startswith("not held by "))] or [None]
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

    def hook_statements():
        """The second and third statements of a supported `hook:` row (DONE-0 C2; the first is its
        form (a) table). A hooked sort has no argument list, so no region and no silent predicate."""
        if key.split(":", 2)[-1].startswith("Sort"):
            have.append("a hooked sort (no argument list: no region, no silent predicate)"); return
        ss = e.get("silent_statement")
        ok = isinstance(ss, list) and bool(ss) and all(
            isinstance(d, dict) and isinstance(d.get("theorem"), str) and isinstance(d.get("file"), str) for d in ss)
        item(ok, f"silent_statement ({len(ss) if ok else 0})",
             "silent_statement (the hook's third statement: its silent predicate is the region the prose leaves"
             " unstated, or it is no key of silentTable and the prose covers every argument list)")
        if fx.silent_key(key):
            got = [d for d in (e.get("derived") or []) if isinstance(d, dict) and d.get("form") == "c"]
            item(bool(got), f"derived form c ({len(got)}: a key of silentTable)",
                 "derived of form c (a key of silentTable: the param_undetermined shape at a point of the region"
                 " the prose excludes or leaves unstated, the hook's second statement)")

    if f is None:
        return have, miss
    if f == PREMISE_FORM:
        f = base_form(l, key, e, row, fx)
    if f in SUPPORTED_TIED:
        tie_premise_items(fx, e, own, have, miss)
    if f in ("pending-fixture", "not-handled"):
        miss.append(f"a status ({f} is none of DONE-0 C2's five)")
    elif f == "supported":
        x = fixture_items(True); ties()
        nodir_items(fx, e, x, have, miss)
        uncovered_items(fx, e, own, have, miss)
    elif f == "supported E4/E5":
        x = fixture_items(True)
        if x:
            ok, how = node_held(fx, l, key, x, e)
            item(ok, f"node ({how})", f"node ({how})")
        ties()
        nodir_items(fx, e, x, have, miss)
        uncovered_items(fx, e, own, have, miss)
    elif f == "supported hook":
        derived(["a"])
        if e is row:
            hook_statements()
    elif f == "supported function of the text":
        x = fixture_items(True); ties()
        nodir_items(fx, e, x, have, miss)
        uncovered_items(fx, e, own, have, miss)
    elif f in ("supported E6",) + E6_GROUPS:
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
        cf = e.get("core_failing")
        err = [x for x in own if (fx.conf(x).get("expect") == "error")]
        kompile_refuses = bool(err) and (e.get("unit") == "none (scope): rejected" or e.get("class") == "R-b")
        nodef = [x for x in own if re.search(r"^definition\.kore: none written$", fx.read(x, "kompile.txt") or "", re.M)]
        option = (e.get("unit") == "none (scope): option" and isinstance(e.get("shape"), str)
                  and e["shape"].startswith("none: "))
        scope = SCOPE_OPTION in (e.get("reasons") or [])
        e8 = (re.match(r"E8 (\S.*)$", e["shape"]) if l != "E8" and e.get("unit") == "none (scope): option"
              and isinstance(e.get("shape"), str) and not rs else None)
        undelivered = e.get("unit") == "none (scope): not delivered" and not rs
        if kompile_refuses:
            have.append(f"kompile refuses ({err[0]})")
        elif option and nodef:
            have.append(f"kompile writes no definition ({nodef[0]})")
        elif e8:
            k8 = e8[1]
            row8 = ((fx.rows or {}).get("E8") or {}).get(k8)
            if not isinstance(row8, dict):
                miss.append(f"option row: shape {e['shape']!r} names no row of E8")
            elif row8.get("status") != "refused" or row8.get("class") not in ("scope", "R-b"):
                miss.append(f"option row: E8 {k8} is {row8.get('status')!r} of class {row8.get('class')!r},"
                            " not refused of class scope or R-b")
            else:
                _, m8 = evidence(fx, "E8", k8, row8, row8)
                item(not m8, f"option row: E8 {k8} refused, with its own evidence",
                     f"option row: E8 {k8} has not its own evidence ({m8[0][:80] if m8 else ''})")
            how = [(x, "default options" if r12_command(fx, x) else k8) for x in err
                   if r12_command(fx, x) or option_passed(fx, x, k8)]
            item(bool(how), f"option row: kompile refuses {how[0][0]}'s text under {how[0][1]}" if how else "",
                 f"option row: no error fixture of the entry whose kompile.txt command passes R-12's options"
                 f" only or {k8}" + (f" ({', '.join(own)})" if own else " (no fixture)"))
        elif undelivered:
            bad = [x for x in err if validator_error(fx, x)]
            item(bool(bad), f"not delivered: {bad[0]} kompile.txt, the validator's error" if bad else "",
                 "not delivered: no error fixture of the entry whose kompile.txt records a non-zero exit and"
                 " an Error" + (f" ({', '.join(own)})" if own else " (no fixture)"))
            words = set(re.findall(r"\w+", " ".join(str(e.get(f) or "") for f in ("refused_by", "evidence"))))
            hand = [(x, fx.account(x)) for x in own
                    if isinstance(fx.conf(x).get("kore"), str) and fx.account(x) is not None]
            read = [(x, [r for i, r in a[0] if i == "ReadingNote" and r in words]) for x, a in hand if a[2]]
            read = [(x, ns) for x, ns in read if ns]
            item(bool(read), f"not delivered: hand-written {read[0][0]} read ({', '.join(sorted(read[0][1]))})"
                 if read else "",
                 "not delivered: no hand-written fixture of the entry whose account refuses nothing and prints a"
                 " ReadingNote the entry names" + (f" ({', '.join(x for x, _ in hand)})" if hand else ""))
            if read:
                fr = fx.fresh_equal(read[0][0])
                item(fr is True, "fresh account", "fresh account (" + ("differs" if fr is False else str(fr)) + ")")
        elif scope and not (l == "E8" and e.get("class") in ("R-b", "scope")):
            miss.append(f"{SCOPE_OPTION!r} (only on an E8 option row of class R-b or scope)")
        else:
            passed = [x for x in own if option_passed(fx, x, key)] if scope else []
            if scope:
                item(bool(passed), f"scope: option {key} outside R-12 ({passed[0] if passed else ''} kompile.txt)",
                     f"scope: no fixture of the entry whose kompile.txt command passes {key} outside R-12"
                     + (f" ({', '.join(own)})" if own else " (no fixture)"))
            elif cf is None:
                item(bool(rs), "reasons " + ", ".join(rs), "reasons (RefusalReason)")
            accs = [(x, fx.account(x)) for x in own if fx.account(x) is not None]
            fresh_of = []
            if not accs and not scope:
                miss.append("fixture whose account prints the reason" + ("" if own else " (no fixture)"))
            elif not accs and rs:
                miss.append(f"fixture whose account prints {', '.join(rs)}")
            elif rs:
                hit = [x for x, a in accs if all(r in a[1] for r in rs)]
                item(bool(hit), f"account {hit[0] if hit else ''} prints the reason",
                     f"account prints {', '.join(rs)} ({', '.join(x for x, _ in accs)} print "
                     + (", ".join(sorted(set().union(*[a[1] for _, a in accs]))) or "no refusal") + ")")
                fresh_of += hit[:1]
                if hit:
                    quotes = quoted(e)
                    for r in rs:
                        ln = next(((x, L) for x in hit for L in reason_lines(fx.account_lines(x), r)
                                   if any(quote_is_line(q, r, L) for q in quotes)), None)
                        item(ln is not None, f"account line of {r} quoted ({ln[0] if ln else ''})",
                             f"account line of {r}: the entry quotes (between back quotes, in "
                             + ", ".join(QUOTE_FIELDS) + f") no line that {', '.join(hit)}'s account prints with it")
            if cf is not None and not scope:
                names = cf if isinstance(cf, list) and all(isinstance(x, str) for x in cf) else None
                bad = [x for x in (names or []) if x not in fx.core_parts]
                if not names or bad:
                    miss.append("core_failing (" + (f"{bad[0]!r} is no conjunct of KcoreGen.coreParts" if bad
                                                    else "a non-empty list of coreOK's conjunct names") + ")")
                elif accs:
                    printed = [(x, fx.core_failing(x)) for x, _ in accs]
                    hit = [x for x, c in printed if c is not None and set(c) == set(names)]
                    item(bool(hit), f"core_failing {', '.join(names)} (account {hit[0] if hit else ''})",
                         f"core_failing: no account prints coreOK false failing exactly {', '.join(names)} ("
                         + "; ".join(f"{x}: " + ("no coreOK line" if c is None else f"[{', '.join(c)}]")
                                     for x, c in printed) + ")")
                    fresh_of += [x for x in hit[:1] if x not in fresh_of]
            for x in fresh_of:
                fr = fx.fresh_equal(x)
                item(fr is True, "fresh account", "fresh account (" + ("differs" if fr is False else str(fr)) + ")")
        reason_sentence(["reason", "reader_reason", "refused_by"])
    elif f == "independent":
        ds = e.get("declarations")
        item(isinstance(ds, list) and len(ds) == 2, "declarations", "declarations (two)")
    else:
        miss.append(f"a status ({f!r} is none of DONE-0 C2's five)")
    if "removed" in e:
        removed_items(fx, e, own, item, miss)
    if MR_KEY in e:
        match_refuted_items(fx, e, f, have, miss)
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


def e6_library(t, res):
    """The results of `run` for the E6 library rows (a row of E6 of status supported or inert with an
    `e6_tie`; not a table nested in one), and their count by group: "missing evidence" for one with a
    missing item, else its form where it is a group counted apart (E6_GROUPS), else "tied"."""
    lib = {f"E6 {k!r}" for k, r in (t.get("E6") or {}).items()
           if isinstance(r, dict) and r.get("status") in ("supported", "inert") and r.get("e6_tie") is not None}
    rs = [r for r in res if r[0] == "E6" and r[3] in lib]
    return rs, collections.Counter("missing evidence" if r[6] else r[2] if r[2] in E6_GROUPS else "tied" for r in rs)


def print_e6_library(t, res):
    """One line counting the E6 library rows by group (`e6_library`), then each row missing evidence."""
    rs, c = e6_library(t, res)
    print(f"e6-library: {len(rs)} E6 library rows (status supported or inert, with an e6_tie): {c['tied']} tied; "
          f"counted apart: " + ", ".join(f"{c[g]} {g}" for g in E6_GROUPS)
          + f"; {c['missing evidence']} missing evidence")
    for r in sorted(rs, key=order):
        if r[6]:
            print(line(r))


def print_check(res, fresh, report, out):
    """The check of every entry; returns the exit code."""
    fails = [r for r in res if r[6]]
    by = collections.Counter((r[0], r[2]) for r in fails)
    tot = collections.Counter((r[0], r[2]) for r in res)
    head = [r for r in res if r[2] not in APART]
    apart = [f"{sum(1 for r in res if r[2] == f)} {f} ({sum(1 for r in fails if r[2] == f)} missing evidence)"
             for f in APART if any(r[2] == f for r in res)]
    print(f"c2-evidence: {len(head)} entries with a status, {sum(1 for r in fails if r[2] not in APART)} missing evidence"
          + (f"; counted apart: {', '.join(apart)}" if apart else "")
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
    unc = [(r, [m for m in r[6] if m.startswith("uncovered sentence: ")]) for r in sorted(fails, key=order)]
    unc = [(r, ms) for r, ms in unc if ms]
    print(f"c2-evidence: {len(unc)} entries whose `sentence` locates an axiom their tie leaves uncovered (B21)")
    for r, ms in unc:
        print(f"    {r[3]}: " + "; ".join(m[len("uncovered sentence: "):] for m in ms))
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
    print_e6_library(t, res)
    rc = print_reader_owed(t, gate) or rc
    rc = print_owed_state(t, fx) or rc
    print_match_refuted(t)
    return rc


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
        # error fixtures: kompile refuses under default options (validator's error in the output),
        # under --opt, under another option; a hand-written text read, one refused
        for name, args, out in (("errdef", "--backend haskell a.k", "  kore-exec: Error (ErrorParse):\n"),
                                ("erropt", "--backend haskell --opt a.k", "  [Error] Compiler: x\n"),
                                ("errother", "--backend haskell --other a.k", "  [Error] Compiler: x\n"),
                                ("errquiet", "--backend haskell a.k", "  nothing\n")):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "fixture.toml"), "w").write('expect = "error"\n')
            open(os.path.join(fxd, name, "kompile.txt"), "w").write(
                f"command: kompile {args} -o out  (cwd: the fixture directory)\nexit: 113\noutput:\n{out}")
        # a text read whose semantics fails coreOK at two conjuncts; one where coreOK holds
        for name, acc in (("corefail", clean + "coreOK: false; failing: [subsortsOK, clauses sorted]\n"),
                          ("coreok", clean + "coreOK: true; failing: []\n")):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "kompile.txt"), "w").write("exit: 0\n")
            open(os.path.join(fxd, name, "account.txt"), "w").write(acc)
        for name, acc in (("hwread", clean + "  1 read identityAlias [user]\n"), ("hwref", refusing)):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "fixture.toml"), "w").write(f'kore = "{name}.kore"\n')
            open(os.path.join(fxd, name, "kompile.txt"), "w").write("command: none\n")
            open(os.path.join(fxd, name, "account.txt"), "w").write(acc)
        rows = {"E3": {"U": {"status": "inert", "inert_class": "use", "reason": "C1", "fixture": "ok"},
                       "V": {"status": "inert", "inert_class": "use", "fixture": "ok"},
                       "E": {"status": "erased", "fixture": "eq"}},
                "E8": {"--opt": {"status": "refused", "fixture": "optk", "class": "scope",
                                 "reasons": [SCOPE_OPTION], "reason": "r"},
                       "--bare": {"status": "refused", "class": "scope", "reasons": [SCOPE_OPTION], "reason": "r"},
                       "--fine": {"status": "supported", "fixture": "optk"}}}
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
        sil = {"theorem": "KCore.C3EqReqEns.f_5", "file": tie}
        bad_forms = []
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
        # the subsort sentence of TCell into TCellSet (31, of no direction, with the no-junk sentence
        # 183 the two that apply inj{TCell,TCellSet}) and the form (r) table refuting it
        nd_cc = "inj{SortTCell{}, SortTCellSet{}} (From:SortTCell{}))) [subsort{SortTCell{}, SortTCellSet{}}()]"
        for name, kore in (("base", f"//@ 30\n  {nd_kd} [function{{}}()]\n//@ 99\n{nd_k}\n  axiom{{R}} x\n"
                                    f"//@ 100\n  axiom{{R}} {nd_f} [{nd_src}]\n"),
                           ("e1-starinit", f"//@ 300\n{nd_t}\n  axiom{{R}} x\n//@ 301\n  axiom{{R}} {nd_cc}\n"),
                           ("e2-cells-stream", "//@ 7000\n  ostream\n")):
            os.makedirs(os.path.join(fxd, name))
            open(os.path.join(fxd, name, "account.txt"), "w").write(clean)
            open(os.path.join(fxd, name, "kompile.txt"), "w").write("exit 0\n")
            open(os.path.join(fxd, name, "kore.txt"), "w").write(kore)
        tbase, ts_ = "test/TieBase.lean", "test/TieE1Starinit.lean"
        # a tie written over several files: the account in the first, account_absent and absent_closed
        # in another file of the same text and classes
        tcs, tcsa = "test/TieE2CellsStream.lean", "test/TieE2CellsStreamAbsent.lean"
        acc3 = lambda ns: [f"KCore.{ns}.account", f"KCore.{ns}.account_absent", f"KCore.{ns}.absent_closed"]
        model = lambda ss, kind="in a model": {"form": "a", "kind": kind, "sentences": ss, "theorem": "KCore.C3EqReqEns.f_5",
                                              "file": tie}
        tcc, cc_thm = "test/TieE1StarinitCellColl.lean", "KCore.TieE1Starinit.cellcoll_subsort_refuted"
        cc_r = lambda ss, **kw: dict({"form": "r", "sentences": ss, "family": "ΓCons", "theorem": cc_thm, "file": tcc}, **kw)
        ccok = {"status": "supported", "fixture": "e1-starinit", "sentence": [nd_cc], "tie": [ts_, tcc],
                "reasons": ["UnreadReason.cellCollectionInjection"],
                "tie_theorems": acc3("TieE1Starinit") + [cc_thm], "no_direction": [31, 183], "derived": [cc_r([3, 31])]}
        cc = lambda **kw: dict({k: v for k, v in ccok.items() if kw.get(k, 0) is not None}, **{k: v for k, v in kw.items() if v is not None})
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
        # B21: e3-ml-rule-lhs-and, whose rule (sentence 104 of the text test/TieLhsAndVar.lean reads,
        # f2-examples/mllhsandv.kompile.kore, byte for byte the fixture's) that tie leaves uncovered,
        # and test/TieRuleLhsAnd.lean (reading the same text) ties; 94, a no-junk axiom, it covers
        un_r = "\\and{SortExp{}}(VarX:SortExp{},Lbld{}(Var'Unds'Gen0:SortExp{},Lblb{}()))"
        un_c = "axiom{} \\or{SortExp{}} (Lbla{}(), Lblb{}()"
        os.makedirs(os.path.join(fxd, "e3-ml-rule-lhs-and"))
        for f_, c_ in (("account.txt", clean), ("kompile.txt", "exit 0\n"), ("kore.txt", f"{un_r}\n{un_c}\n")):
            open(os.path.join(fxd, "e3-ml-rule-lhs-and", f_), "w").write(c_)
        tlv, trl = "test/TieLhsAndVar.lean", "test/TieRuleLhsAnd.lean"
        # the cases read tlv as a tie leaving 104 uncovered, whatever the file states today
        _unc[tlv] = ("f2-examples/mllhsandv.kompile.kore", {104})
        un = lambda **kw: dict({"status": "supported", "fixture": "e3-ml-rule-lhs-and", "sentence": [un_r],
                                "tie": [tlv, trl], "tie_theorems": ["KCore.TieLhsAndVar.account",
                                                                    "TieRuleLhsAnd.Var.tie"]}, **kw)
        # a tie_premise table: e3-ml-req-not's rule (sentence 157 of f2-examples/mlreqnot.kompile.kore, which
        # test/TieE3MlReqNot.lean reads) as tiegen writes it under a premise form, in `underPremise`
        # and not `uncovered`, its theorems in the tie's section on the rules (namespace Rules)
        os.makedirs(os.path.join(fxd, "e3-ml-req-not"))
        for f_, c_ in (("account.txt", clean), ("kompile.txt", "exit 0\n"), ("kore.txt", "Lblgo{}(VarX:SortInt{})\n")):
            open(os.path.join(fxd, "e3-ml-req-not", f_), "w").write(c_)
        trn, treq = "test/TieE3MlReqNot.lean", "test/TieE3MlEqReqNot.lean"
        _upr[trn] = ("f2-examples/mlreqnot.kompile.kore", {157: "boolClosed"})
        _unc[trn] = ("f2-examples/mlreqnot.kompile.kore", set())
        tpok = {"sentences": [157], "premise": "boolClosed", "in_gamma": False, "ground": "DONE-0 section 0 (4)",
                "theorem": "KCore.TieE3MlReqNot.Rules.rule_from_text_closed",
                "converse": "KCore.TieE3MlReqNot.Rules.rule_w2_closed_noprem",
                "needed": "KCore.TieE3MlReqNot.Rules.rule_not_from_text", "consistent": "KCore.TieE3MlReqNot.consistent"}
        tpt = lambda **kw: {k: v for k, v in dict(tpok, **kw).items() if v is not None}
        pr = lambda tp=None, **kw: dict({"status": "supported", "fixture": "e3-ml-req-not",
                                         "sentence": ["Lblgo{}(VarX:SortInt{})"], "tie": [trn],
                                         "tie_theorems": ["KCore.TieE3MlReqNot.account",
                                                          "KCore.TieE3MlReqNot.Rules.rule_not_from_text"]},
                                        **({"tie_premise": tp} if tp is not None else {}), **kw)
        if form("E3", "A", pr([tpok])) != PREMISE_FORM or form("E3", "A", pr()) != "supported":
            bad_forms.append(f"tie_premise: form {form('E3', 'A', pr([tpok]))!r}, expected {PREMISE_FORM!r}")
        cases = [
            # (list, key, entry, accepted)
            # tie_premise: the table for the sentence in `underPremise`; none, or one wanting a field
            ("E3", "A", pr([tpok]), True),
            ("E3", "A", pr(), False),
            ("E3", "A", pr([]), False),
            ("E3", "A", pr([tpt(needed=None)]), False),
            ("E3", "A", pr([tpt(needed=None, in_gamma=True)]), True),
            ("E3", "A", pr([tpt(in_gamma="no")]), False),
            ("E3", "A", pr([tpt(ground=None)]), False),
            ("E3", "A", pr([tpt(converse=None)]), False),
            ("E3", "A", pr([tpt(converse=None, at_values="KCore.TieE3MlReqNot.Rules.rule_w2_closed")]), False),
            ("E3", "A", pr([tpt(converse=None, at_values="KCore.TieE3MlReqNot.Rules.rule_w2_closed")],
                           tie_theorems=["KCore.TieE3MlReqNot.account", "KCore.TieE3MlReqNot.Rules.rule_w2_closed",
                                         "KCore.TieE3MlReqNot.Rules.rule_not_from_text"]), True),
            ("E3", "A", pr([tpok], tie_theorems=["KCore.TieE3MlReqNot.account"]), False),
            ("E3", "A", pr([tpt(consistent="KCore.TieE3MlReqNot.no_such")]), False),
            ("E3", "A", pr([tpt(premise="boolDist")]), False),
            ("E3", "A", pr([tpt(sentences=[158])]), False),
            ("E3", "A", pr([tpok], tie=[treq]), False),
            # B21: the rule uncovered by tiegen's tie and tied by a companion the entry names a theorem of
            ("E3", "A", un(), True),
            ("E3", "A", un(tie=[tlv], tie_theorems=["KCore.TieLhsAndVar.account"]), False),
            ("E3", "A", un(tie_theorems=["KCore.TieLhsAndVar.account"]), False),
            ("E3", "A", un(tie_theorems=["KCore.TieLhsAndVar.account"],
                           derived=[{"form": "a", "theorem": "TieRuleLhsAnd.Var.tie", "file": trl}]), True),
            # a theorem of the companion declared where another text is in scope ties no sentence here
            ("E3", "A", un(tie_theorems=["KCore.TieLhsAndVar.account", "TieRuleLhsAnd.Ceil.tie"]), False),
            # a file of `tie` declaring a named theorem but reading another text is no companion
            ("E3", "A", un(tie=[tlv, "test/TieE3MlReqTop.lean"],
                           tie_theorems=["KCore.TieLhsAndVar.account", "KCore.TieE3MlReqTop.consistent"]), False),
            # a sentence locating an axiom the tie covers needs no companion
            ("E3", "A", un(sentence=[un_c], tie=[tlv], tie_theorems=["KCore.TieLhsAndVar.account"]), True),
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
            # the cell-collection subsort exception: the form (r) table refuting the subsort sentence
            # stands in place of the table in a model, for the sentences of that injection only and
            # only on an entry naming the reader's reason
            ("E1", "A", ccok, True),
            ("E1", "A", cc(no_direction=[31]), True),
            ("E1", "A", cc(reasons=None), False),
            ("E1", "A", cc(derived=None), False),
            ("E1", "A", cc(derived=[cc_r([3])]), False),
            ("E1", "A", cc(derived=[cc_r([3, 183])]), False),
            ("E1", "A", cc(derived=[cc_r([3, 31], kind="through the reading")]), False),
            ("E1", "A", cc(derived=[cc_r([3, 31], fixture="base")]), False),
            ("E1", "A", cc(tie_theorems=acc3("TieE1Starinit")), False),
            ("E1", "A", cc(no_direction=[31, 183, 283]), False),
            ("E1", "A", cc(no_direction=None), False),
            ("E1", "A", cc(tie_theorems=[cc_thm]), False),
            ("E2", "A", {"status": "supported", "fixture": "e2-cells-stream", "sentence": ["ostream"], "tie": [tcs, tcsa],
                         "tie_theorems": acc3("TieE2CellsStream"), "no_direction": [2895], "derived": [model([2895])]}, True),
            ("E2", "A", {"status": "supported", "fixture": "e2-cells-stream", "sentence": ["ostream"], "tie": [tcs],
                         "tie_theorems": acc3("TieE2CellsStream"), "no_direction": [2895], "derived": [model([2895])]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "sentence": ["axiom{} f"], "tie": [tie],
                         "derived": [thm]}, True),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": [tie]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": [tie],
                         "tie_theorems": ["KCore.C3EqReqEns.no_such_theorem"]}, False),
            ("E2", "A", {"status": "supported", "fixture": "bad", "tie": [tie], "derived": [thm]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "sentence": ["axiom{} g"], "tie": [tie],
                         "derived": [thm]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": ["test/PrintNames.lean"], "derived": [thm]}, False),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": [tie], "derived": [dict(thm, form="r",
                         kind="sentence against the reading", consistent="KCore.C3EqReqEns.f_5")]}, True),
            ("E2", "A", {"status": "supported", "fixture": "ok", "tie": [tie], "derived": [dict(thm, form="r",
                         kind="sentence against the reading", consistent="KCore.C3EqReqEns.no_such_theorem")]}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "evidence": "account.txt: `sentence 7 (Lblf): setVariable (VarS: in the requires)`"}, True),
            # the account's line, quoted: whole, a prefix, from the reason into its detail, with an
            # ellipsis; not the reason's name alone, another sentence's line, another detail, or no
            # quotation
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "note": "`sentence 7 (Lblf): setVariable`"}, True),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "refused_by": "`setVariable (VarS: in the`"}, True),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "evidence": "`sentence 7 (Lblf): setVariable (VarS: …)`"}, True),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "evidence": "`setVariable`"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "evidence": "`sentence 8 (Lblf): setVariable (VarS: in the requires)`"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "evidence": "`setVariable (VarT`"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"],
                         "reason": "r", "evidence": "sentence 7 (Lblf): setVariable (VarS: in the requires)"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.ruleShape"],
                         "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "reasons": ["RefusalReason.setVariable"]}, False),
            # coreOK's failing conjuncts in place of a RefusalReason
            ("E2", "A", {"status": "refused", "fixture": "corefail", "core_failing": ["clauses sorted", "subsortsOK"],
                         "reason": "r"}, True),
            ("E2", "A", {"status": "refused", "fixture": "corefail", "core_failing": ["subsortsOK"],
                         "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "corefail", "core_failing": ["subsortsOK", "clauses sorted",
                         "genWf"], "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "corefail", "core_failing": ["subsortsOK", "noSuchPart"],
                         "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "corefail", "core_failing": [], "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "corefail", "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "coreok", "core_failing": ["subsortsOK"], "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "ok", "core_failing": ["subsortsOK"], "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "core_failing": ["subsortsOK"], "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "corefail", "core_failing": ["subsortsOK", "clauses sorted"],
                         "reasons": ["RefusalReason.setVariable"], "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "fixture": "bad", "also_fixtures": ["corefail"],
                         "core_failing": ["subsortsOK", "clauses sorted"],
                         "reasons": ["RefusalReason.setVariable"], "reason": "r",
                         "evidence": "`sentence 7 (Lblf): setVariable (VarS: in the requires)`"}, True),
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
                             "reasons": [SCOPE_OPTION, "RefusalReason.setVariable"], "reason": "r",
                             "evidence": "`sentence 7 (Lblf): setVariable (VarS: in the requires)`"}, True),
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
            # an entry outside E8 that acts only under an E8 row's option: that row's evidence and an
            # error fixture under default options or under the option
            ("E7", "A", {"status": "refused", "class": "scope", "unit": "none (scope): option", "shape": "E8 --opt",
                         "fixture": "errdef", "reason": "r"}, True),
            ("E7", "A", {"status": "refused", "class": "scope", "unit": "none (scope): option", "shape": "E8 --opt",
                         "fixture": "erropt", "reason": "r"}, True),
            ("E7", "A", {"status": "refused", "class": "scope", "unit": "none (scope): option", "shape": "E8 --opt",
                         "fixture": "errother", "reason": "r"}, False),
            ("E7", "A", {"status": "refused", "class": "scope", "unit": "none (scope): option", "shape": "E8 --opt",
                         "fixture": "optk", "reason": "r"}, False),
            ("E7", "A", {"status": "refused", "class": "scope", "unit": "none (scope): option", "shape": "E8 --bare",
                         "fixture": "errdef", "reason": "r"}, False),
            ("E7", "A", {"status": "refused", "class": "scope", "unit": "none (scope): option", "shape": "E8 --fine",
                         "fixture": "errdef", "reason": "r"}, False),
            ("E7", "A", {"status": "refused", "class": "scope", "unit": "none (scope): option", "shape": "E8 --none",
                         "fixture": "errdef", "reason": "r"}, False),
            # not delivered, the reader reading the frontend's sentence on a hand-written text
            ("E2", "A", {"status": "refused", "class": "scope", "unit": "none (scope): not delivered",
                         "fixture": "errdef", "also_fixtures": ["hwread"], "refused_by": "kore-exec; read (identityAlias)",
                         "reason": "r"}, True),
            ("E2", "A", {"status": "refused", "class": "scope", "unit": "none (scope): not delivered",
                         "fixture": "errdef", "also_fixtures": ["hwread"], "refused_by": "kore-exec", "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "class": "scope", "unit": "none (scope): not delivered",
                         "fixture": "errdef", "also_fixtures": ["hwref"], "refused_by": "identityAlias", "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "class": "scope", "unit": "none (scope): not delivered",
                         "fixture": "errdef", "also_fixtures": ["ok"], "refused_by": "inert simplification", "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "class": "scope", "unit": "none (scope): not delivered",
                         "fixture": "errquiet", "also_fixtures": ["hwread"], "refused_by": "identityAlias", "reason": "r"}, False),
            ("E2", "A", {"status": "refused", "class": "scope", "unit": "none (scope): not delivered",
                         "also_fixtures": ["hwread"], "refused_by": "identityAlias", "reason": "r"}, False),
            # with a RefusalReason, a not-delivered entry is checked against the account as before
            ("E2", "A", {"status": "refused", "class": "scope", "unit": "none (scope): not delivered",
                         "fixture": "hwref", "reasons": ["RefusalReason.setVariable"], "reason": "r",
                         "evidence": "`sentence 7 (Lblf): setVariable (VarS: in the requires)`"}, True),
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
            # a hook's three statements: the value (form a), the silent statement, and, on the row
            # of a key of silentTable (LIST.get), the param_undetermined instance (form c); a hooked
            # sort has no argument list
            ("E6", "hook:X", {"status": "supported", "derived": [thm], "silent_statement": [sil]}, True),
            ("E6", "hook:X", {"status": "supported", "derived": [thm]}, False),
            ("E6", "hook:X", {"status": "supported", "derived": [thm], "silent_statement": []}, False),
            ("E6", "hook:X", {"status": "supported", "silent_statement": [sil]}, False),
            ("E6", "hook:K.Foo:SortFoo", {"status": "supported", "derived": [thm]}, True),
            ("E6", "hook:LIST.get:LblList'Coln'get", {"status": "supported", "derived": [thm, dict(sil, form="c")],
                                                       "silent_statement": [sil]}, True),
            ("E6", "hook:LIST.get:LblList'Coln'get", {"status": "supported", "derived": [thm],
                                                       "silent_statement": [sil]}, False),
            ("E6", "symbol:X", {"status": "supported", "tie": [tie], "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, True),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)"]}, True),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.C3EqReqEns.nope (test/C3EqReqEns.lean; t axiom 3)"]}, False),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.X.y (test/PrintNames.lean; t axiom 3)"]}, False),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["uncovered: INT; no tied text holds the sentence"]}, False),
            ("E6", "lemma:X", {"status": "inert", "e6_tie": ["refuted: M; no theorem entails the sentence"]}, False),
            ("E6", "module:M", {"status": "supported", "e6_tie": ["every axiom, lemma, sort and symbol row of M (3) is tied"]}, True),
            ("E6", "module:M", {"status": "supported", "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)",
                                                                  "not held by t: M; rule r (m.md:1): reason"]}, True),
            ("E6", "module:M", {"status": "supported", "e6_tie": ["not held by t: M; rule r (m.md:1): reason"]}, False),
            ("E6", "module:M", {"status": "supported", "e6_tie": "uncovered: M; rule r (m.md:1) held by no tied text; on t "
                                                                 "1 of its 2 rules are tied (test/C3EqReqEns.lean)"}, False),
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
        # the E6 groups counted apart (e6map.py's forms), each with the form expected
        f5 = "KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3"
        nope = "KCore.C3EqReqEns.nope (test/C3EqReqEns.lean; t axiom 3"
        ref = "refuted: M; no theorem entails the sentence; it is refuted (Γ with it has no model): "
        every = "every axiom, lemma, sort and symbol row of M (3) is "
        rr = "DONE-0 section 0 (4): the known case of this refutation"
        e6cases = [  # (key, e6_tie, other fields, form expected, accepted)
            ("axiom:X", f"no direction: INT; {f5}); {f5}; in a model)", {}, E6_ND, True),
            ("axiom:X", f"no direction: INT; {f5}); {nope}; in a model)", {}, E6_ND, False),
            ("axiom:X", f"no direction: INT; {f5})", {}, "supported E6", False),
            ("axiom:X", f"no model: RAT; {f5}; no model); {f5}; Γ's items are the list's translations, item for item)",
             {}, E6_NM, True),
            ("axiom:X", f"no model: RAT; {f5}; no model)", {}, E6_NM, False),
            ("axiom:X", f"no model: RAT; {f5}; no model); {nope}; Γ has the symbol)", {}, E6_NM, False),
            ("lemma:X", ref + f"{f5}) [refutes]", {"status": "inert", "refuted_ruling": rr}, E6_REF, True),
            ("lemma:X", ref + f"{f5}) [refutes]", {"status": "inert", "refuted_ruling": "see the note"}, E6_REF, False),
            ("lemma:X", ref + f"{nope}) [refutes]", {"status": "inert", "refuted_ruling": rr}, E6_REF, False),
            ("lemma:X", ref + f"{f5}) [refutes]", {"status": "inert"}, "inert", False),
            ("axiom:X", ref + f"{f5}) [refutes]", {}, "supported E6", False),
            ("module:M", f"no direction in a model: M; every axiom, lemma, sort and symbol row of M (2) is of no "
                         f"direction with a theorem in a model", {}, E6_ND, True),
            ("module:M", f"refuted (recorded): M; {every}tied (2) or refuted with its recorded ruling (1)", {}, E6_REF, True),
            ("module:M", f"no model: M; {every}tied (1), of no direction with a theorem in a model (0), refuted with "
                         f"its recorded ruling (0) or of a text without a model (2)", {}, E6_NM, True),
            ("module:M", "uncovered: M; 4 of its 45 axiom, lemma, sort and symbol rows uncovered, 41 of a text "
                         "without a model", {}, "supported E6", False),
            ("axiom:X", "uncovered: RAT; held by t, tied there by no theorem", {}, "supported E6", False),
        ]
        for key, v, more, f, want in e6cases:
            e = dict({"status": "supported", "e6_tie": v}, **more)
            cases.append(("E6", key, e, want))
            if form("E6", key, e) != f:
                bad_forms.append(f"{key} {v[:50]!r}: form {form('E6', key, e)!r}, expected {f!r}")
        # the E6 library line: those rows, a tied row and a nested table without e6_tie, counted by group
        import contextlib, io
        t6 = {"E6": {f"{key}#{i}": dict({"status": "supported", "e6_tie": v}, **more)
                     for i, (key, v, more, _, _) in enumerate(e6cases)}}
        t6["E6"]["axiom:T"] = {"status": "supported", "e6_tie": [f"{f5})"],
                               "cases": [{"status": "supported", "case": "c"}]}
        t6["E6"]["axiom:N"] = {"status": "refused"}
        rs6, c6 = e6_library(t6, run(t6, fx))
        want6 = {"tied": 1, E6_ND: 2, E6_NM: 2, E6_REF: 2,
                 "missing evidence": sum(1 for *_, w in e6cases if not w)}
        if len(rs6) != len(e6cases) + 1 or c6 != collections.Counter(want6):
            bad_forms.append(f"e6_library: {len(rs6)} rows, {dict(c6)}, expected {len(e6cases) + 1}, {want6}")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            print_e6_library(t6, run(t6, fx))
        if not out.getvalue().startswith(f"e6-library: {len(e6cases) + 1} E6 library rows (status supported or "
                                         f"inert, with an e6_tie): 1 tied; counted apart: 2 {E6_ND}, 2 {E6_NM}, 2 "
                                         f"{E6_REF}; {want6['missing evidence']} missing evidence\n") \
                or out.getvalue().count("\n") != 1 + want6["missing evidence"]:
            bad_forms.append(f"print_e6_library: printed {out.getvalue()[:300]!r}")
        # match_refuted: e3-eq-exists-ml-in-or-int's clause, whose MatchIndependent its account names as
        # owed and test/ExClauseFxInOrInt.lean refutes; the scratch fixture's account prints that
        # line, and a `consistent` is added to that file's declarations here (the tie states it)
        mrx, mrf = "e3-eq-exists-ml-in-or-int", "test/ExClauseFxInOrInt.lean"
        mrn, mrc = "ExClauseFixtures.InOrInt.not_matchIndependent", "ExClauseFixtures.InOrInt.consistent"
        mi = "      function f, clause 0 at e3-eq-exists-ml-in-or-int.k:4: MatchIndependent open, existential Var'Hash'Or0:Int\n"
        for name, acc in ((mrx, clean + mi), ("mr-closed", clean), ("mr-other", clean + mi)):
            os.makedirs(os.path.join(fxd, name))
            for f_, c_ in (("account.txt", acc), ("kompile.txt", "exit 0\n"), ("kore.txt", "Lblf{}(VarX:SortInt{})\n")):
                open(os.path.join(fxd, name, f_), "w").write(c_)
        _decls[mrf] = (file_decls(mrf) or set()) | {mrc}
        mrt = {"fixture": mrx, "owed_refuted": mrn, "consistent": mrc, "file": mrf}
        mrw = lambda **kw: {k: v for k, v in dict(mrt, **kw).items() if v is not None}
        mre = lambda mr=None, **kw: dict({"status": "supported", "fixture": mrx, "tie": [mrf], "tie_theorems": [mrn]},
                                         **({MR_KEY: mr} if mr is not None else {}), **kw)
        mrd = lambda **kw: dict({"form": "r", "sentences": [348], "family": "ΓDomains", "theorem": mrn, "file": mrf}, **kw)
        mrcases = [  # (entry, the substring of its one failure, or None where accepted)
            (mre(), None),
            (mre(mrt), None),
            (mre([mrt]), None),
            (mre([mrt, mrw(fixture="mr-other")], also_fixtures=["mr-other"]), "does not read fixtures/mr-other's text"),
            (mre([]), "not a table or a non-empty list"),
            (mre("x"), "not a table or a non-empty list"),
            (mre(mrw(consistent=None)), "no `consistent`"),
            (mre(mrw(file=None)), "no `file`"),
            (mre(mrw(extra="x")), "field `extra` is none of"),
            (mre(mrw(fixture="mr-other")), "is not the entry's `fixture` or one of its `also_fixtures`"),
            (mre([mrt, mrt]), "a second table for e3-eq-exists-ml-in-or-int"),
            (mre(mrw(fixture="mr-closed"), fixture="mr-closed"), "prints no `MatchIndependent open`"),
            (mre(mrw(consistent="ExClauseFixtures.InOrInt.no_such")), "no_such not declared in"),
            (mre(mrw(file="test/NoSuch.lean")), "test/NoSuch.lean does not exist"),
            (mre(mrt, derived=[mrd()]), "beside a form (r) table of e3-eq-exists-ml-in-or-int"),
            (mre(mrt, derived=[mrd(kind="sentence against the reading", consistent=mrc)]), None),
            (mre(mrt, derived=[mrd(fixture="mr-other")], also_fixtures=["mr-other"]), None),
        ]
        for i, (e, want) in enumerate(mrcases):
            _, miss = evidence(fx, "E3", "A", e, e)
            if want is None and miss or want is not None and not (len(miss) == 1 and want in miss[0]):
                bad_forms.append(f"match_refuted case {i}: missing {miss}, expected " + (repr(want) if want else "none"))
        _, miss = evidence(fx, "E2", "A", {"status": "inert", "inert_class": "attribute", MR_KEY: mrt}, {})
        if not any(m.startswith(MR_KEY + " on an entry of form") for m in miss):
            bad_forms.append(f"match_refuted on an inert entry: missing {miss}, expected the field refused")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            print_match_refuted({"E3": {"R": {"status": "supported", "cases": [mre(mrt), mre()]}, "S": mre([mrt])}})
            print_match_refuted({"E3": {"S": mre()}})
        if not out.getvalue().startswith("match-refuted: 2 entries") or out.getvalue().count("\n") != 1 \
                or "E3 'R' cases[0] (e3-eq-exists-ml-in-or-int)" not in out.getvalue():
            bad_forms.append(f"print_match_refuted: printed {out.getvalue()!r}")
        bad = list(bad_forms)
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
              f" {len(ocases)} owed_state tables, {len(mrcases) + 2} match_refuted cases,"
              f" {len(bad)} failing")
        return 1 if bad else 0
    finally:
        shutil.rmtree(d, ignore_errors=True)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--self-test"]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
