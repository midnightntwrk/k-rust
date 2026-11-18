"""DONE-0 C2's evidence per status, over every entry of test/constructs/rows.toml: each row of the
lists E1 to E8 and of [C3], and each table nested in a row's `cases` (recursively), `also_refused`
or `split`, as units.py walks them.

Usage (from kcore-spec):
  python3 -I test/constructs/rest.py [list] [--fresh] [--out FILE] [ROWS.toml]
      the entries FIX-core does not hold (below), grouped by list, status and evidence form, each
      with the evidence present and missing; prints the count per group, and every entry when no
      FILE is given (with FILE, the entries go there)
  python3 -I test/constructs/rest.py check [--report] [--fresh] [--list LFILE] [--out FILE] [ROWS.toml]
      DONE-0 C2's check of every entry, FIX-core's included: an entry fails when an item its form
      needs is missing; prints per list and form how many entries have their evidence, and the
      failures (all of them into FILE, the first 40 on the output); with --list, also the list
      above (its entries into LFILE); exit 1 on a failure, exit 0 with --report (failures listed,
      not failing: test/constructs.sh's mode until the closing check of FIX-rest)
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
      tie          `tie` lists the C14 tie modules: files test/X.lean that test/integration.sh
                   builds (not in its skip list)
      theorems     the theorems the entry names, `tie_theorems` (full names, each declared in a
                   file of `tie`) and the `theorem` of each `derived` table (declared in its
                   `file`): at least one, each declared
  supported E4, E5
      fixture, clean, fresh, tie, theorems as above; node: the fixture's kompiled sentences (kore.txt,
      or the text of a `kore` fixture) hold the row's node or translation site, found by
      test/constructs/e4e5.py's parse of the text when that module exists, else by `sentence`
  supported hook (E6, key hook:)
      derived      a `derived` table of form (a) (the in-domain value; FIX-core.rows-evidence names
                   the hook's three statements there)
  supported E6 (other keys)
      tie, theorems (the theorem that ties the row's sentence on a tied text); or the row's
                   `e6_tie` (test/constructs/e6map.py): each "THEOREM (FILE; TEXT axiom N)" a
                   theorem declared in FILE, a tie file as above; on a module row "every ... row
                   of MODULE (n) is tied"; an item "uncovered: ..." or "refuted: ..." (Γ refutes the
                   sentence or entails it only partly) is missing evidence
  parameter
      derived      a `derived` table of form (c): the param_undetermined instance
  inert
      class        `inert_class` or a `reasons` item InertReason.X: a constructor of InertReason
                   (an E6 row keyed lemma: is a [simplification] axiom, of class simplification);
                   where the entry has a fixture, its account prints `N inert X` with N above 0
      tie, theorems (C14's statement for the class: Γ c ⊧ tr s); for an E6 row, its e6_tie as above
  inert of class use (`inert_class = "use"`)
      reason       a reason sentence (`reason`): C1's class use
  erased (findings/work/decision-fixrest-erased-forms.md section 4): at least one of the forms
  ERASED_FORMS, each the entry carries checked (conjoined)
      P pair       the fixture `pair` names, else the first of the entry's fixtures recording one,
                   has kompile.txt `same_as OTHER: equal after stripping`
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


def form(l, key, e):
    """The evidence form of DONE-0 C2's table for the entry's status, or None without a status."""
    s = e.get("status")
    if s is None:
        return None
    if s == "supported":
        return ("supported" if l in KLEVEL else "supported E4/E5" if l in ("E4", "E5") else
                "supported hook" if key.startswith("hook:") else "supported E6")
    if s == "inert" and e.get("inert_class") == "use":
        return "inert (use)"
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


def declared(name, files):
    """Whether the full name is declared in one of the files (namespaces tracked by their
    `namespace` lines; a textual check, as provenance.sh's)."""
    parts = name.split(".")
    for f in files:
        p = os.path.join(K, f) if isinstance(f, str) else None
        if not p or not os.path.isfile(p):
            continue
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
        if name in _decls[f] or any(name.endswith("." + d) or d == name for d in _decls[f]):
            return True
    return False


# ------------------------------------------------------------------------------------- evidence

def evidence(fx, l, key, e, row):
    """(present, missing): two lists of strings, the items of the entry's form (module docstring)."""
    f = form(l, key, e)
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
        ref = [x for x in v if isinstance(x, str) and x.startswith("refuted")]
        if ref:
            miss.append("theorems (e6_tie: " + ref[0].split(";")[0] + ": Γ refutes the sentence or entails it"
                        " only partly, no tie; a finding for DONE-0 2.6)"); return False
        if all(isinstance(x, str) and re.match(r"every .* row of \S+ \(\d+\) is tied$", x) for x in v):
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
        fixture_items(True); ties()
    elif f == "supported E4/E5":
        x = fixture_items(True)
        if x:
            ok, how = node_held(fx, l, key, x, e)
            item(ok, f"node ({how})", f"node ({how})")
        ties()
    elif f == "supported hook":
        derived(["a"])
    elif f == "supported E6":
        ties()
    elif f == "parameter":
        derived(["c"])
    elif f == "inert (use)":
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
        if kompile_refuses:
            have.append(f"kompile refuses ({err[0]})")
        elif option and nodef:
            have.append(f"kompile writes no definition ({nodef[0]})")
        else:
            item(bool(rs), "reasons " + ", ".join(rs), "reasons (RefusalReason)")
            accs = [(x, fx.account(x)) for x in own if fx.account(x) is not None]
            if not accs:
                miss.append("fixture whose account prints the reason" + ("" if own else " (no fixture)"))
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
    return have, miss


def erased_forms(fx, l, key, e, have, miss):
    """The forms of erased (findings/work/decision-fixrest-erased-forms.md section 2) the entry
    carries, each checked, its item appended to have or miss; returns the letters of the forms
    carried. P: the fixture `pair` names (else the first of the entry's own fixtures recording one)
    records `same_as OTHER: equal after stripping`; S: each `absent` pattern is found in no text in
    scope (kfix.check_absent); O: `other_file` and `witness` (kfix.check_other); C: `carried_by`
    names a row that is not erased and has its own evidence, and the entry's `sentence` occurs in
    that row's fixture."""
    letters = []
    own = [x for x in [e.get("fixture")] + list(e.get("also_fixtures") or []) if fx.exists(x)]
    pair_rx = r"^same_as (\S+): equal after stripping$"
    if "pair" in e:
        letters.append("P")
        x = e["pair"]
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
        return e4e5.holds(fx, l, key, x)
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
        f = form(l, key, e)
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
    report, fresh = "--report" in argv, "--fresh" in argv
    argv = [a for a in argv if a not in ("--report", "--fresh")]
    t = tomllib.load(open(argv[0] if argv else os.path.join(HERE, "rows.toml"), "rb"))
    fx = Fixtures(os.path.join(HERE, "fixtures"), fresh, t)
    res = run(t, fx)
    if mode == "list":
        print_list([r for r in res if not r[4]], fresh, opt.get("--out"))
        return 0
    if "--list" in opt:
        print_list([r for r in res if not r[4]], fresh, opt["--list"])
    return print_check(res, fresh, report, opt.get("--out"))


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
                         "Location(900,1,900,9)"]]}
        fake = lambda ps: {p: (1, [], [f"t: {h}" for h in kfix.absent_hits(p, sm)])
                           if kfix.absent_form(p) else None for p in ps}
        fx.check_absent = lambda e: kfix.check_absent(e, fake)
        defn = "module MAIN\n  symbol Lblm{}(SortExp{}) : SortExp{} [macro{}()]\n// rule Lblh{}(VarX:SortExp{})\nendmodule []\n"
        fx.check_other = lambda e, own: kfix.check_other(e, own, read=fx.read, full_text=lambda x: defn)
        tie = "test/C3EqReqEns.lean"
        thm = {"form": "a", "theorem": "KCore.C3EqReqEns.f_5", "file": tie}
        cases = [
            # (list, key, entry, accepted)
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
            # S: a pattern found nowhere; found (a head, a source range, a module); of no known form
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "attribute cellSort"}, True),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": ["axiom attribute comm",
                         "source kast.md 1-79", "module other than BASIC-K, KSEQ, INJ, K and the main module"]}, True),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "attribute comm"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "symbol attribute comm"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "source kast.md 70-90"}, False),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "source kast.md 100-200"}, True),
            ("E2", "A", {"status": "erased", "fixture": "ok", "absent": "source domains.md 1-5"}, False),
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
            ("E2", "A", {"status": "inert", "fixture": "ok", "inert_class": "simplification", "tie": [tie],
                         "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, True),
            ("E2", "A", {"status": "inert", "fixture": "ok", "inert_class": "claim", "tie": [tie],
                         "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, False),
            ("E3", "A", {"status": "inert", "inert_class": "use", "reason": "C1"}, True),
            ("E3", "A", {"status": "inert", "inert_class": "use"}, False),
            ("E6", "x", {"status": "parameter", "derived": [{"form": "c", "theorem": "T", "file": tie}]}, True),
            ("E6", "x", {"status": "parameter", "derived": [thm]}, False),
            ("E6", "hook:X", {"status": "supported", "derived": [thm]}, True),
            ("E6", "hook:X", {"status": "supported"}, False),
            ("E6", "symbol:X", {"status": "supported", "tie": [tie], "tie_theorems": ["KCore.C3EqReqEns.f_5"]}, True),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)"]}, True),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.C3EqReqEns.nope (test/C3EqReqEns.lean; t axiom 3)"]}, False),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["KCore.X.y (test/PrintNames.lean; t axiom 3)"]}, False),
            ("E6", "axiom:X", {"status": "supported", "e6_tie": ["uncovered: INT; no tied text holds the sentence"]}, False),
            ("E6", "lemma:X", {"status": "inert", "e6_tie": ["refuted: M; no theorem entails the sentence"]}, False),
            ("E6", "module:M", {"status": "supported", "e6_tie": ["every axiom, lemma, sort and symbol row of M (3) is tied"]}, True),
            ("E6", "lemma:X", {"status": "inert",
                               "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)"]}, True),
            ("E6", "axiom:X", {"status": "inert",
                               "e6_tie": ["KCore.C3EqReqEns.f_5 (test/C3EqReqEns.lean; t axiom 3)"]}, False),
            ("E2", "A", {"status": "pending-fixture"}, False),
            ("E2", "A", {"status": "not-handled"}, False),
            ("C3", "A x B", {"status": "independent", "declarations": ["a", "b"]}, True),
        ]
        bad = []
        for i, (l, key, e, want) in enumerate(cases):
            have, miss = evidence(fx, l, key, e, e)
            if (not miss) != want:
                bad.append(f"case {i} ({l} {e.get('status')}): {'refused' if miss else 'accepted'}, expected "
                           f"{'accepted' if want else 'refused'}; missing {miss}")
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
        for b in bad:
            print(f"rest self-test: FAILS: {b}")
        print(f"rest self-test: {len(cases)} entries and the core predicate, {len(bad)} failing")
        return 1 if bad else 0
    finally:
        shutil.rmtree(d, ignore_errors=True)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--self-test"]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
