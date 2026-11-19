"""The reader's reasons against the construct table (DONE-0 C4 part 1), on the committed evidence:
KcoreSpec/Parse.lean's four inductives (RefusalReason, InertReason, UnreadReason, ReadingNote, their
constructors read from the Lean text), test/constructs/rows.toml and the fixtures' account.txt.

What an entry names. Every entry is taken: each row of the lists and of [C3], and each table nested
in a row's `cases` (recursively), `also_refused` or `split`, as units.py walks them. An entry names
  - the constructors that the account.txt of its `fixture` and of each of its `also_fixtures` prints;
  - the constructors of its `reasons`, a list of "RefusalReason.x", "InertReason.x", "UnreadReason.x"
    or "ReadingNote.x": what the reader answers on the entry's construct, for an entry with no
    fixture of its own;
  - the keys of its `notes` (constructors of ReadingNote; kfix.py check checks their fixtures).
What an account prints (KcoreGen's `account`):
  - a class line `  N refused R [origin]`, `  N inert R [origin]`, `  N unread R [origin]`,
    `  N read R [origin]` (a sentence read in another form: ReadingNote R);
  - a refusal `sentence I (head): R` or `sentence I (head): R (detail)`, also after `finish: ` and
    with `the module` for `sentence I` (Refusal.toText): RefusalReason R, with its detail;
  - `sentence I: R, R'`, the connective readings of a sentence: ReadingNote, each name that is one;
  - `... (R): N` with N above 0, a count the account gives under a constructor's name
    (ruleRightDefined, overloadConfusion, ...): the inductive, other than RefusalReason, that has R;
  - a count above 0 on one of the two lines of COUNTED below, whose refusals the account prints
    without their reason.

Failures (exit 1):
  - an account prints, in one of the first two forms, a name that is no constructor of the form's
    inductive (the account is not of this reader);
  - a `reasons` item is not "<one of the four inductives>.<a constructor of it>", nor SCOPE_OPTION
    ("none (scope): option", an E8 option row's scope refusal, which names no constructor; rest.py
    checks where it stands);
  - a `reasons` name that no account.txt of the fixtures the entry's evidence names prints, when the
    evidence names fixtures (a directory of test/constructs/fixtures/ written in `evidence`,
    `reader_today`, `refused_by`, `place` or `note` as `fixtures/NAME`, `FX/NAME` or `fixture NAME`),
    outside the allowance UNSHOWN: such names owed a fixture by a ticket of PROGRESS, pinned at an
    exact count (a count above the pin, or below it, or a ticket missing or done, fails);
  - an entry of status refused of E4, E5 or E6 with no `reasons`, where neither it nor its row has a
    fixture, unless its unit is "none (scope): rejected" (kompile refuses the K text, the reader
    reads nothing);
  - a constructor no entry names that PINNED does not hold; a name PINNED holds that is no
    constructor, or that an entry names, or whose ticket is not in PROGRESS or is done (as
    units.py's ALLOWANCE);
  - a name UNREACHED holds (a constructor no KORE text can make an account print, with why) that is
    no constructor, or that some fixture's account.txt prints. An entry naming one in `reasons`
    without a fixture is not counted among the reasons names no committed account shows.
Printed: per inductive, how many constructors are named; each constructor no entry names with the
ticket that owes it; how many `reasons` names no committed account shows (their entry's evidence
names no fixture); and, per catch-all (CATCHALL below: a reason produced by an arm that takes
whatever the earlier arms of its function did not match), the entries citing it, each with its
fixture and its reason sentence (`reason`, else `reader_reason`, else `note`), and how many of them
lack a fixture of their own or a sentence.

Usage (from kcore-spec): python3 -I test/constructs/closed.py [ROWS.toml]
  PROGRESS  as units.py: KCORE_PROGRESS, else ../progress, else the main checkout's.

Mode `corpus` (DONE-0 C4 part 3):
  python3 -I test/constructs/closed.py corpus [--log DIR] [--expected FILE] [ROWS.toml]
reads the logs of test/corpus.py (DIR, default .lake/corpus/log: one SHA16.gen per text, written by
a native run of `kcore gen TEXT PKG Cov --core` on a kcore built at the tree) for each text of FILE
(default test/corpus.expected, the lines `SHA16 clean|unclean coreOK|no`), and lists every item a
log prints: a refusal of the reader's stages (after "KCore's parse refuses it"), a sentence read and
not accounted for (after "sentences classified read that the definition does not account for"), a
refusal of the account (after "refusals of the account"), the account's `inertMismatch` refusals
apart, and a failing `coreOK` with its conjuncts (finding 9 of findings/TRIAGE-B-E2.toml: a text
read with coreOK false counts as refused, the conjuncts its reason). Each distinct item (its reason
and detail, the account line without its sentence's index and head; for coreOK `coreOK fails:
[conjuncts]`) is mapped to the entries of ROWS that name it: an entry names the item when it names
the item's RefusalReason (as above: its fixtures' accounts, its `reasons`) and either an account.txt
of its own fixtures (or of the fixtures its `reasons` are checked against) prints the same reason
with the same detail, or its `evidence` quotes the item (`R (detail)`, or `coreOK fails: [...]`).
Exit 1 on an item no entry names, a text of FILE without its log, a log line of no known form, or a
log whose items do not agree with the text's verdict in FILE (`unclean` or `no` with no item,
`clean coreOK` with one). Prints the counts (texts, items by kind and reason, unaccounted,
inertMismatch, coreOK failures) and each distinct item with its texts and its entries.
"""
import glob, os, re, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FX = os.path.join(K, "test/constructs/fixtures")
ARGS = sys.argv[1:]
MODE = ARGS.pop(0) if ARGS[:1] == ["corpus"] else "rows"
CORPUS_LOG = os.path.join(K, ".lake/corpus/log")
CORPUS_EXPECTED = os.path.join(K, "test/corpus.expected")
while MODE == "corpus" and ARGS[:1] in (["--log"], ["--expected"]):
    opt = ARGS.pop(0)
    if not ARGS:
        sys.exit(f"closed corpus: {opt} needs a value")
    if opt == "--log":
        CORPUS_LOG = ARGS.pop(0)
    else:
        CORPUS_EXPECTED = ARGS.pop(0)
rows = ARGS[0] if ARGS else os.path.join(K, "test/constructs/rows.toml")
KR = os.environ.get("K_RUST", os.path.expanduser(
    "~/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust"))
prog = os.environ.get("KCORE_PROGRESS") or next(
    (d for d in (os.path.join(K, "../progress"),
                 os.path.join(KR, "draft-personal/k-semantics-core-2026-11/progress"))
     if os.path.isdir(d)), os.path.join(K, "../progress"))
tstatus = {}
for f in sorted(glob.glob(os.path.join(prog, "tickets-*.toml"))):
    tk = tomllib.load(open(f, "rb")).get("ticket", {})
    tstatus |= {k: v.get("status") for k, v in tk.items() if isinstance(v, dict)}
if not tstatus:
    print(f"closed: no progress/tickets-*.toml under {prog} (set KCORE_PROGRESS)")
    sys.exit(1)

INDUCTIVES = ["RefusalReason", "InertReason", "UnreadReason", "ReadingNote"]
# The `reasons` item of an E8 option row refused for scope (rest.py's SCOPE_OPTION): no constructor.
SCOPE_OPTION = "none (scope): option"
CLASSWORD = {"refused": "RefusalReason", "inert": "InertReason", "unread": "UnreadReason",
             "read": "ReadingNote"}

# The catch-alls: (reason, a substring of the detail or None for any detail, the arm that gives it).
CATCHALL = [
    ("axiomShape", None, "classifyAxiom's last arm, and classRefusal's default"),
    ("patternConnective", None, "term's last arm `| p => fail (if isUnkompiledForm p then .unkompiledForm else .patternConnective) (connective p)`"),
    ("ruleShape", None, "ruleBodyOther's arms"),
    ("requiresShape", None, "`need (req? r)`"),
    ("unaccounted", None, "Account.unconsumedWhy's other arms"),
]

# Account lines whose refusals are printed without their reason: (line start, the reason, its
# function in KcoreSpec/Account.lean).
COUNTED = [
    ("sentences the library's data induces that the text does not hold: ", "builtinIncomplete",
     "libraryUnstated"),
    ("library sentences of the modules held that the text does not hold: ", "builtinIncomplete",
     "missingBuiltin"),
]

# `reasons` names that the fixtures their entry's evidence names do not print: (ticket, pinned count).
UNSHOWN = ("R2-release.C4", 0)

# Constructors no entry names, each with the ticket that owes the entry: ("Inductive.x", ticket).
# One holds only while its ticket is in PROGRESS and not done, and while no entry names it.
# R2-release.C4 owes each constructor that no ticket of PROGRESS names: the criterion is not met while
# one stands here.
PINNED = [
]

# Constructors that no KORE text can make an account print, each with why. An entry may name one in
# `reasons` without a fixture (it is then not counted among the reasons names no committed account
# shows); an account.txt printing one fails, since the reason is then false.
UNREACHED = [
    ("RefusalReason.noModule",
     "a KORE definition is a non-empty sequence of modules (kore-syntax.md:286, <modules> sep-by-1) and"
     " KCore's KORE parser reads `many1 module` (kore-lean/KoreParser/Parser.lean:376), so `kcore account`"
     " on a text of no module stops at the KORE read error; Parse.parse and Account.refusals give it only"
     " for a Kore.Definition built in Lean with no module"),
]


def constructors():
    """The constructors of the four inductives, by inductive, in the order of Parse.lean."""
    src = open(os.path.join(K, "KcoreSpec/Parse.lean")).read()
    out = {}
    for ind in INDUCTIVES:
        block = src.split(f"\ninductive {ind} where\n", 1)[1].split("\n  deriving", 1)[0]
        out[ind] = re.findall(r"^  \| (\w+)", block, re.M)
    return out


CTORS = constructors()
CLASSLINE = re.compile(r"^\s+\d+ (refused|inert|unread|read) (\w+) \[", re.M)
REFUSAL = re.compile(r"(?:sentence \d+|the module) \((.*?)\): (\w+)(?: \((.*)\))?$", re.M)
READINGS = re.compile(r"^\s+sentence \d+: (.+)$", re.M)
COUNT = re.compile(r"\((\w+)\): [1-9]")
_accounts = {}


def account(name):
    """What fixtures/NAME/account.txt prints: (the set of (inductive, constructor), the list of
    (refusal reason, detail), the names printed that are no constructor); None without the file."""
    if name not in _accounts:
        p = os.path.join(FX, name, "account.txt")
        if not os.path.isfile(p):
            _accounts[name] = None
            return None
        text = open(p).read()
        names, refusals, unknown = set(), [], []
        for word, r in CLASSLINE.findall(text):
            ind = CLASSWORD[word]
            (names.add((ind, r)) if r in CTORS[ind] else unknown.append(f"{word} {r}"))
        for _, r, detail in REFUSAL.findall(text):
            if r in CTORS["RefusalReason"]:
                names.add(("RefusalReason", r)); refusals.append((r, detail))
            else:
                unknown.append(f"refusal {r}")
        for line in READINGS.findall(text):
            for w in line.split(", "):
                if w in CTORS["ReadingNote"]:
                    names.add(("ReadingNote", w))
        for w in COUNT.findall(text):
            for ind in INDUCTIVES[1:]:
                if w in CTORS[ind]:
                    names.add((ind, w))
        for start, r, _ in COUNTED:
            if re.search(r"^" + re.escape(start) + r"[1-9]", text, re.M):
                names.add(("RefusalReason", r)); refusals.append((r, ""))
        _accounts[name] = (names, refusals, sorted(set(unknown)))
    return _accounts[name]


def nested(e):
    """The tables nested in an entry: its `cases` (and theirs), `also_refused`, `split`."""
    for f in ("cases", "also_refused", "split"):
        v = e.get(f)
        for i, c in enumerate(v if isinstance(v, list) else [v]):
            if isinstance(c, dict):
                yield f"{f}[{i}]" + (f" ({str(c['case'])[:40]!r})" if "case" in c else ""), c
                for w, d in nested(c):
                    yield f"{f}[{i}].{w}", d


def own_fixtures(e):
    """The entry's `fixture` and `also_fixtures` that are fixture directories."""
    fs = [e.get("fixture")] + list(e.get("also_fixtures") or [])
    return [f for f in fs if isinstance(f, str) and f != "none"]


ALLFX = sorted(d for d in os.listdir(FX) if os.path.isdir(os.path.join(FX, d)))
FXWORD = re.compile(r"(?:fixtures/|FX/|fixtures? )`?([A-Za-z0-9][A-Za-z0-9_-]*)")


def evidence_fixtures(e):
    """The fixture directories the entry's prose names."""
    out = []
    for f in ("evidence", "reader_today", "refused_by", "place", "note"):
        v = e.get(f)
        for s in (v if isinstance(v, list) else [v]):
            if isinstance(s, str):
                out += [n for n in FXWORD.findall(s) if n in ALLFX]
    return sorted(set(out))


def sentence(e):
    for f in ("reason", "reader_reason", "note"):
        if isinstance(e.get(f), str) and e[f].strip():
            return " ".join(e[f].split())
    return None


t = tomllib.load(open(rows, "rb"))
bad, named = [], {}                       # (inductive, constructor) -> the entries naming it
cites = {c[:2]: [] for c in CATCHALL}     # catch-all -> (where, fixture or None, sentence or None)
unshown = []                              # `reasons` names with no account to show them
unprinted = []                            # `reasons` names their evidence's fixtures do not print
nreasons = 0
entries = []                              # (where, names, (reason, detail) its fixtures print, evidence)
for name in ALLFX:
    a = account(name)
    if a and a[2]:
        bad.append(f"fixtures/{name}/account.txt prints names that are no constructor: {', '.join(a[2])}")
for l, tab in t.items():
    if not isinstance(tab, dict):
        continue
    for key, r in tab.items():
        if not isinstance(r, dict):
            continue
        for where, e in [(f"{l} {key!r}", r)] + [(f"{l} {key!r} {w}", c) for w, c in nested(r)]:
            here, refusals, fxs = set(), [], own_fixtures(e)
            for f in fxs:
                a = account(f)
                if a:
                    here |= a[0]; refusals += [(x, d, f) for x, d in a[1]]
            for note in (e.get("notes") or {}):
                if note in CTORS["ReadingNote"]:
                    here.add(("ReadingNote", note))
            rs = e.get("reasons")
            if rs is not None:
                nreasons += 1
                if not isinstance(rs, list):
                    bad.append(f"{where}: reasons {rs!r} is not a list"); rs = []
                ev = [f for f in evidence_fixtures(e) if account(f)]
                shown = set().union(*[account(f)[0] for f in ev if account(f)]) if ev else set()
                for x in rs:
                    if x == SCOPE_OPTION:
                        continue
                    ind, _, c = x.partition(".") if isinstance(x, str) else ("", "", "")
                    if ind not in CTORS or c not in CTORS[ind]:
                        bad.append(f"{where}: reasons {x!r} is not <{' | '.join(INDUCTIVES)}>.<constructor>")
                        continue
                    here.add((ind, c))
                    if not ev:
                        if x not in dict(UNREACHED):
                            unshown.append(f"{where}: {x}")
                    elif (ind, c) not in shown:
                        unprinted.append(f"{where}: reasons {x}: no account.txt of the fixtures its evidence"
                                         f" names ({', '.join(ev)}) prints it")
                    else:
                        f0 = next(f for f in ev if (ind, c) in account(f)[0])
                        refusals += [(a, d, f0) for f in ev for a, d in account(f)[1] if a == c and ind == "RefusalReason"] \
                            or ([(c, "", f0)] if ind == "RefusalReason" else [])
            elif (e.get("status") == "refused" and l in ("E4", "E5", "E6") and not fxs
                  and not own_fixtures(r) and e.get("unit") != "none (scope): rejected"):
                bad.append(f"{where} (refused, no fixture): no reasons")
            for x in here:
                named.setdefault(x, []).append(where)
            ev = e.get("evidence")
            entries.append((where, set(here), {(x, d or "") for x, d, _ in refusals},
                            " ".join(" ".join(ev if isinstance(ev, list) else [ev]).split())
                            if isinstance(ev, (str, list)) else ""))
            for (cr, sub) in cites:
                fs = sorted({f for x, d, f in refusals if x == cr and (sub is None or sub in d)})
                if fs:
                    cites[(cr, sub)].append((where, fs, bool(fxs), sentence(e)))

CORPUS_HEAD = re.compile(r"^(?P<file>\S+?): (?:(?P<prelude>\d+ sentences of the prelude; the user module's by class:)"
                         r"|(?P<parse>KCore's parse refuses it: \d+ refusals)"
                         r"|(?P<unacc>\d+ sentences classified read that the definition does not account for:)"
                         r"|(?P<account>\d+ refusals of the account:)"
                         r"|`coreOK` fails: \[(?P<core>.*)\]"
                         r"|(?P<readerr>KORE read error))$")
CORPUS_ITEM = re.compile(r"^  (?:sentence \d+|the module) \((?:.*?)\): (\w+)(?: \((.*)\))?$")
CORPUS_COUNT = re.compile(r"^  \d+ \S.*$")


def corpus_items(text):
    """The items of one `kcore gen` log: (kind, reason, detail), kind one of refusal, unaccounted,
    account, inertMismatch, coreOK, readError; and the lines of no known form."""
    items, odd, sec = [], [], None
    for line in text.split("\n"):
        if not line.strip():
            continue
        m = CORPUS_HEAD.match(line)
        if m:
            sec = ("parse" if m["parse"] else "unacc" if m["unacc"] else "account" if m["account"] else
                   "prelude" if m["prelude"] else None)
            if m["core"] is not None:
                items.append(("coreOK", "coreOK", m["core"]))
            if m["readerr"]:
                items.append(("readError", "readError", ""))
            continue
        m = CORPUS_ITEM.match(line)
        if m and sec in ("parse", "unacc", "account"):
            r, d = m[1], m[2] or ""
            kind = {"parse": "refusal", "unacc": "unaccounted"}.get(sec) or (
                "inertMismatch" if r == "inertMismatch" else "account")
            items.append((kind, r, d))
        elif CORPUS_COUNT.match(line) and sec is not None:
            continue
        elif line.startswith("{") and line.endswith("}"):
            sec = None                    # the package's summary (JSON), written after the account
        else:
            odd.append(line)
    return items, odd


def corpus_line(r, d):
    return (f"coreOK fails: [{d}]" if r == "coreOK" else "KORE read error" if r == "readError" else
            f"{r} ({d})" if d else r)


def corpus():
    """DONE-0 C4 part 3 over test/corpus.py's logs (the docstring's mode `corpus`)."""
    fails = []
    want = [l.split() for l in open(CORPUS_EXPECTED).read().split("\n") if l.strip()]
    found = {}                            # (kind, reason, detail) -> the texts printing it
    for w in want:
        if len(w) != 3:
            fails.append(f"{CORPUS_EXPECTED}: a line of no known form: {' '.join(w)}"); continue
        h, read, core = w
        p = os.path.join(CORPUS_LOG, h + ".gen")
        if not os.path.isfile(p):
            fails.append(f"{h}: no log {p} (run test/corpus.py on a kcore built at the tree)"); continue
        items, odd = corpus_items(open(p).read())
        fails += [f"{h}: a log line of no known form: {o[:160]}" for o in odd]
        if (read == "clean" and core == "coreOK") == bool(items):
            fails.append(f"{h}: the log's items ({len(items)}) do not agree with its verdict '{read} {core}'")
        for it in dict.fromkeys(items):
            found.setdefault(it, []).append(h)
    unmapped, lines = 0, []
    for (kind, r, d), hs in sorted(found.items()):
        line = corpus_line(r, d)
        es = [where for where, names, fxr, ev in entries
              if (kind == "coreOK" or ("RefusalReason", r) in names)
              and ((r, d) in fxr or line in ev)]
        lines.append((kind, line, hs, es))
        if not es:
            unmapped += 1
            fails.append(f"{kind} '{line}' ({len(hs)} texts, {hs[0]}...): no entry of rows.toml names it")
    kinds = {}
    for (kind, r, _), hs in found.items():
        kinds.setdefault((kind, r), set()).update(hs)
    nk = lambda k: sum(len(hs) for (kd, _), hs in kinds.items() if kd == k)
    print(f"closed corpus: {len(want)} texts ({os.path.relpath(CORPUS_EXPECTED)}), "
          f"{len({h for hs in found.values() for h in hs})} with an item; "
          f"refusals of the reader's stages {nk('refusal')}, of the account {nk('account')}, "
          f"unaccounted {nk('unaccounted')}, inertMismatch {nk('inertMismatch')}, "
          f"coreOK failing {nk('coreOK')}, KORE read errors {nk('readError')} (texts per kind)")
    print("  by reason: " + (", ".join(f"{kd} {r} {len(hs)}" for (kd, r), hs in sorted(kinds.items())) or "none"))
    for kind, line, hs, es in lines:
        print(f"  {kind} '{line}': {len(hs)} texts ({', '.join(hs[:3])}{', ...' if len(hs) > 3 else ''}); "
              + (f"entries: {'; '.join(es)}" if es else "NO ENTRY"))
    for b in fails[:40]:
        print(f"  FAILS: {b}")
    if len(fails) > 40:
        print(f"  ... and {len(fails) - 40} more")
    return 1 if fails else 0


if MODE == "corpus":
    sys.exit(corpus())

pinned = dict(PINNED)
unnamed = [(ind, c) for ind in INDUCTIVES for c in CTORS[ind] if (ind, c) not in named]
for ind, c in unnamed:
    if f"{ind}.{c}" not in pinned:
        bad.append(f"{ind}.{c}: no entry of rows.toml names it, and no ticket is pinned for it")
for x, tid in PINNED:
    ind, _, c = x.partition(".")
    st = tstatus.get(tid)
    if ind not in CTORS or c not in CTORS[ind]:
        bad.append(f"pin {x} ({tid}): no constructor of KcoreSpec/Parse.lean")
    elif (ind, c) in named:
        bad.append(f"pin {x} ({tid}): an entry names it ({named[(ind, c)][0]}): remove the pin")
    elif st is None:
        bad.append(f"pin {x}: ticket {tid} is not in {prog}/tickets-*.toml")
    elif st == "done":
        bad.append(f"pin {x}: ticket {tid} is done, so it owes nothing")

for x, why in UNREACHED:
    ind, _, c = x.partition(".")
    if ind not in CTORS or c not in CTORS[ind]:
        bad.append(f"unreached {x}: no constructor of KcoreSpec/Parse.lean")
    for name in ALLFX:
        a = account(name)
        if a and (ind, c) in a[0]:
            bad.append(f"unreached {x}: fixtures/{name}/account.txt prints it, so no text reaching it is false")

utid, upin = UNSHOWN
ust = tstatus.get(utid)
uwhy = ("" if len(unprinted) == upin and (upin == 0 or ust not in (None, "done")) else
        f"ticket {utid} is not in {prog}/tickets-*.toml" if ust is None else
        f"ticket {utid} is done, so it owes nothing" if ust == "done" else
        f"{len(unprinted)} names, pinned {upin}")
if uwhy:
    bad += unprinted + [f"allowance {utid} (reasons names their evidence's fixtures do not print): {uwhy}"]

print("closed: constructors named by an entry: " + ", ".join(
    f"{ind} {sum((ind, c) in named for c in CTORS[ind])} of {len(CTORS[ind])}" for ind in INDUCTIVES)
    + f"; entries with reasons: {nreasons}; reasons names no committed account shows: {len(unshown)}")
print(f"  allowance {utid} (status {ust}): {len(unprinted)} of {upin} pinned: reasons names that the fixtures"
      " their entry's evidence names do not print" + (f"; FAILS: {uwhy}" if uwhy else ""))
for u in unprinted:
    print(f"    {u}")
for x, why in UNREACHED:
    print(f"  unreached by any text: {x} (named by {len(named.get(tuple(x.split('.', 1)), []))} entries): {why}")
for ind, c in unnamed:
    tid = pinned.get(f"{ind}.{c}")
    print(f"  not named: {ind}.{c}: " + (f"owed by {tid} (status {tstatus.get(tid)})" if tid else "no ticket"))
for (cr, sub), arm in [(c[:2], c[2]) for c in CATCHALL]:
    es = cites[(cr, sub)]
    lack = sum(1 for _, _, own, s in es if not own or not s)
    print(f"catch-all {cr}" + (f" with the detail '{sub}'" if sub else "") + f" ({arm}): {len(es)} entries"
          + (f", {lack} without a fixture of their own or a reason sentence" if lack else ""))
    for where, fs, own, s in es:
        print(f"  {where}: fixture {', '.join(fs)}" + ("" if own else " (named by its evidence)")
              + ": " + (s[:200] if s else "NO REASON SENTENCE"))
for b in bad[:40]:
    print(f"  FAILS: {b}")
if len(bad) > 40:
    print(f"  ... and {len(bad) - 40} more")
sys.exit(1 if bad else 0)
