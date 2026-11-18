"""The `unit` field of rows.toml against the work plan and the refusal classes (DONE-0 C2;
findings/EX-KPROV-decision.md D5-D9). Every entry is checked: each row of the lists, and each table
nested in a row's `cases` (recursively), `also_refused` or `split` (those that are tables).

An entry of status refused has a `class`: R-a, R-b, R-c or scope. Every entry of status refused, and
every entry of class R-c, names in `unit` a ticket of PROGRESS/tickets-*.toml (`[ticket."ID"]`) or a
unit of PROGRESS/units.toml (`[unit]`'s keys), or, for an entry not of class R-c, says that no ticket
supports it, in one of these forms, the word in parentheses being the entry's own class:
  none (R-a)[: reason]
  none (R-b): shape at <list> <row key>[, case <name>]   (a passage of K's documentation; the row
                                                         key a key of that list in ROWS.toml)
  none (R-b): no shape (ill-formed)                     (a passage of the KORE syntax document)
  none (scope): rejected | none (scope): never written | none (scope): option |
  none (scope): not delivered
The ground not delivered is a sentence kompile's frontend wrote and its validation step refused
(KPROV-reopen-decision R2): the text exists, but the command delivers no definition, so no
kompiled definition carries the sentence; the reader's verdict is on a hand-written KORE text that
holds the frontend's sentence.
An entry of class scope has unit "none (scope): <ground>" and carries, by its ground:
  place      "DONE-0 R-10" (rejected, not delivered), "DONE-0 R-1" (never written), "DONE-0 R-12"
             (option)
  reversal   the event that ends the scope
  shape      rejected, option: "<list> <row key>[, case <name>]" (the key a key of ROWS.toml) or
             "none: <emitter file>:<lines>: <what the site shows>"
  meaning    never written: "<path>:<line>: \"<passage>\"" (the KORE syntax document's passage)
  refused_by "kompile" (rejected); the reader's reason (never written, not delivered)
  evidence   D6's evidence for the ground; not delivered: "fixtures/<dir>/kompile.txt: exit <n>,
             <validator> <version> <error class> at <location>: <the sentence>" and the
             hand-written fixture's account line ("fixtures/<dir>/account.txt: ...")
An entry of another status may carry `unit`; it is then checked the same way.

Usage (from kcore-spec): python3 -I test/constructs/units.py [ROWS.toml]
  ROWS.toml  default test/constructs/rows.toml
  PROGRESS   the environment variable KCORE_PROGRESS; without it ../progress (beside kcore-spec)
             when it exists, otherwise the main checkout's (K_RUST, as kfix.py:
             K_RUST/draft-personal/k-semantics-core-2026-11/progress)
Prints the refused rows by class (R-a, R-b, scope, R-c, then any other class met) and how many of
them have a unit, the same for the refused nested entries, the scope entries by ground, and each
failing entry not allowed (at most 20, then the count). Exit 1 when an entry fails outside the
allowance, when an allowance's count differs from its pin, or PROGRESS has no ticket file or no
units.toml.

The allowance (ALLOWANCE below, GUARD.units-standing): failures owed by a pending ticket of
PROGRESS, each kind of failure named with the ticket that owes it and pinned at an exact count.
Every run prints each allowance with its observed and pinned count. An allowance holds only while
its ticket is in PROGRESS and its status is not done; a failure it does not cover, a count above the
pin (a new failure of the kind) or below it (the ticket did part of its work: lower the pin), or a
ticket missing or done, fails. Only the failure kinds the allowance names are allowed: an id that is
no ticket, a malformed `none (...)`, a class the unit does not name and the scope fields are never
allowed.
"""
import collections, glob, os, re, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
rows = sys.argv[1] if len(sys.argv) > 1 else os.path.join(K, "test/constructs/rows.toml")
KR = os.environ.get("K_RUST", os.path.expanduser(
    "~/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust"))
prog = os.environ.get("KCORE_PROGRESS") or next(
    (d for d in (os.path.join(K, "../progress"),
                 os.path.join(KR, "draft-personal/k-semantics-core-2026-11/progress"))
     if os.path.isdir(d)), os.path.join(K, "../progress"))
tfiles = sorted(glob.glob(os.path.join(prog, "tickets-*.toml")))
ufile = os.path.join(prog, "units.toml")
if not tfiles or not os.path.isfile(ufile):
    print(f"units: no progress/tickets-*.toml or progress/units.toml under {prog} (set KCORE_PROGRESS)")
    sys.exit(1)
ids = set(tomllib.load(open(ufile, "rb")).get("unit", {}))
tstatus = {}
for f in tfiles:
    tk = tomllib.load(open(f, "rb")).get("ticket", {})
    ids |= set(tk)
    tstatus |= {k: v.get("status") for k, v in tk.items() if isinstance(v, dict)}

CLASSES = ["R-a", "R-b", "scope", "R-c"]
NONE = re.compile(r"none \(([^)]*)\)(.*)$", re.S)
GROUNDS = {"rejected": "DONE-0 R-10", "never written": "DONE-0 R-1", "option": "DONE-0 R-12",
           "not delivered": "DONE-0 R-10"}
ROWREF = re.compile(r"(E[1-8]) (.+?)(?:, case (.+))?$", re.S)
EMITTER = re.compile(r"none: \S+:\d+(?:-\d+)?: .+", re.S)
MEANING = re.compile(r"\S+:\d+(?:-\d+)?: \".+\"$", re.S)
UNDELIVERED = re.compile(r"fixtures/[^/\s]+/kompile\.txt: exit [1-9]\d*, \S+ \S+ .+", re.S)
ACCOUNT = re.compile(r"fixtures/[^/\s]+/account\.txt: ")

t = tomllib.load(open(rows, "rb"))

# (ticket, pinned count, what the failures are, the test on (list, entry, failure kind)). The kinds:
# "nounit" (an entry of status refused or class R-c without unit), "class" (a refused entry whose
# class is outside CLASSES); every other failure is of kind "other" and is never allowed. A failure
# is counted under the first allowance whose test holds.
ALLOWANCE = [
    # 62 -> 40 with FIX-core.rangemap-silent: the 22 RANGEMAP entries (E6's 21 rows, E5
    # translateSorts:hooked-#2 case RANGEMAP.RangeMap) were refused R-c without unit and are what
    # the reader does (supported, or parameter), the carrier and the module having landed.
    # 40 -> 38 with C3.rows-unit-ctor: E2 ASSOC(assoc)@symbol and COMM(comm)@symbol name the ticket
    # whose completion is their fixture read, P2.d2-kompiled (findings/C3-unbound-rulings.md 8.2).
    # 38 -> 37 with CE.rows-partition: the #Exists row's case "an equation's right side" (R-c, no
    # unit) is replaced by one case per shape, each R-c with its ticket or R-a with its reason.
    # 37 -> 38 with R2-release.rdr-corpus-rows: E6 hook:LIST.update's case of List:set in a rule's
    # left side (the corpus text list-set), R-c with no ticket that reads a parameter symbol there.
    # 38 -> 34 with P3.rows-setvar-cut: the four set-variable rows of E4 are R-a with their reason,
    # each shape a case with its fixture, class and unit.
    # 34 -> 33 with P3.rows-ksym-setvar: E3's KSEQ-SYMBOLIC #set-@ row, R-c without unit, is R-a
    # with its reason and the E4 rows' cases.
    # 33 -> 35 with R2-release.fixrest-pending-rows: E2 ML_BINDER(mlBinder)@frontend and
    # ML_OP(mlOp)@frontend take, by rule S1, the status and class of the E3 rows of #Exists and #Ceil
    # (refused R-c without unit), the productions whose KORE their fixture's sentences show.
    # 35 -> 34 with ROWS-1.refresh-k: E3 #Bottom is supported, every shape of it read or inert
    # with its fixture.
    # 34 -> 30 with ROWS-1.refresh-kore: the four E4 \forall and \floor rows are R-a openExtent
    # with their unit (CN-3 section 5), the predicate in a condition a supported case.
    # 30 -> 31 with ROWS.initial-collection-cell: E2 INITIAL(initial)@frontend's case on a cell
    # collection (fixture e2-initial-coll), refused R-c by the reader's initializer decision, with no
    # ticket that reads it yet.
    # 31 -> 33: E6 hook:KEQUAL.ite's cases of the text's own one-sort Lblite
    # with an equation of an instance (NamesNumbered) and hooked to KEQUAL.ite (as E2
    # SYMBOL(symbol)@symbol's registry-name case), R-c with no ticket that reads them.
    # 33 -> 32: E5 translateSorts:hooked-#2's case of a user sort hooked under its own name to a
    # library carrier is supported (scanCarrier, fixture e5-hooked-int); the user's hooked sort
    # whose hook no library sort has is its own case, R-a with its reason.
    # 32 -> 31: E2 INITIAL(initial)@frontend's case on a cell collection is supported, the reader
    # computing the enclosing cell's initializer through the collection's initializer of no argument.
    # 31 -> 30: E6 hook:KEQUAL.ite's case of the text's own one-sort Lblite hooked to KEQUAL.ite
    # is supported, the declaration being the registry's ite declared again (Parse.regIteDeclIoh).
    ("ROWS-1.unit-rc", 29, "entries of class R-c without unit",
     lambda l, e, k: k == "nounit" and e.get("class") == "R-c"),
    # 121: E7 26:genCoverage and 30:removeAnywhereRules carry the status, class and missing unit of
    # their E8 rows --coverage and --allow-anywhere-haskell (refused R-b).
    ("ROWS-1.unit-refused", 121, "refused entries of class R-a, R-b or scope without unit",
     lambda l, e, k: k == "nounit" and e.get("class") in ("R-a", "R-b", "scope")),
]


def rowref(s):
    """None when s is "<list> <row key>[, case <name>]" with the key a key of that list, else why not."""
    m = ROWREF.match(s)
    if not m:
        return f"{s!r} is not \"<list> <row key>[, case <name>]\""
    if m[2] not in t.get(m[1], {}):
        return f"{m[2]!r} is no key of {m[1]}"
    return None


def scope_fields(e, ground):
    """Why a scope entry of this ground lacks D6's fields (empty when it has them)."""
    out = []
    if e.get("status") != "refused":
        out.append(f"status {e.get('status')!r}, not refused")
    if e.get("place") != GROUNDS[ground]:
        out.append(f"place {e.get('place')!r}, not {GROUNDS[ground]!r}")
    for f in ("reversal", "evidence"):
        if not e.get(f):
            out.append(f"no {f}")
    if ground in ("rejected", "option"):
        sh = e.get("shape")
        if not isinstance(sh, str):
            out.append("no shape")
        elif not EMITTER.match(sh) and (w := rowref(sh)):
            out.append(f"shape {w}, nor \"none: <emitter file>:<lines>: <what the site shows>\"")
    elif ground == "not delivered":
        ev = e.get("evidence")
        if isinstance(ev, str) and not UNDELIVERED.search(ev):
            out.append("evidence quotes no \"fixtures/<dir>/kompile.txt: exit <n>, <validator> <version> ...\"")
        if isinstance(ev, str) and not ACCOUNT.search(ev):
            out.append("evidence quotes no hand-written fixture's \"fixtures/<dir>/account.txt: ...\"")
    else:
        mn = e.get("meaning")
        if not isinstance(mn, str) or not MEANING.match(mn):
            out.append(f"meaning {mn!r} is not \"<path>:<line>: \\\"<passage>\\\"\"")
    if ground == "rejected" and e.get("refused_by") != "kompile":
        out.append(f"refused_by {e.get('refused_by')!r}, not 'kompile'")
    if ground in ("never written", "not delivered") and not e.get("refused_by"):
        out.append("no refused_by (the reader's reason)")
    return out


def check(where, e):
    """The failures of one entry: (kind, message), kind "class", "nounit" or "other" (ALLOWANCE)."""
    bad = [("other", x) for x in check_rest(where, e)]
    refused, cls, u = e.get("status") == "refused", e.get("class"), e.get("unit")
    if refused and cls not in CLASSES:
        bad.insert(0, ("class", f"{where} (refused): class {cls!r} is not one of {', '.join(CLASSES)}"))
    if u is None and (refused or cls == "R-c"):
        bad.append(("nounit", f"{where} ({e.get('status')}, {cls}): no unit"))
    return bad


def check_rest(where, e):
    """The failures of one entry other than its class and a missing unit."""
    cls, u = e.get("class"), e.get("unit")
    bad = []
    if u is None:
        if cls == "scope" and e.get("status") != "refused":
            bad.append(f"{where}: a scope entry has unit \"none (scope): <ground>\"")
        return bad
    if not isinstance(u, str):
        return bad + [f"{where}: unit {u!r} is not a string"]
    if not u.startswith("none"):
        if cls == "scope":
            bad.append(f"{where}: unit {u!r}: a scope entry has unit \"none (scope): <ground>\"")
        elif u not in ids:
            bad.append(f"{where}: unit {u!r} is neither a ticket of {prog}/tickets-*.toml nor a unit of {ufile}")
        return bad
    if cls == "R-c":
        return bad + [f"{where}: unit {u!r}: an entry of class R-c names the ticket that supports it"]
    m = NONE.match(u)
    if not m or m[1] not in ("R-a", "R-b", "scope"):
        return bad + [f"{where}: unit {u!r} is not none (R-a | R-b | scope)…"]
    word, rest = m[1], m[2]
    if word != cls:
        bad.append(f"{where}: unit {u!r} names class {word}, the entry's class is {cls!r}")
    if word == "R-a":
        if rest and not (rest.startswith(": ") and rest[2:].strip()):
            bad.append(f"{where}: unit {u!r} is not none (R-a)[: reason]")
    elif word == "R-b":
        if rest == ": no shape (ill-formed)":
            pass
        elif rest.startswith(": shape at "):
            if w := rowref(rest[len(": shape at "):]):
                bad.append(f"{where}: unit {u!r}: shape at {w}")
        else:
            bad.append(f"{where}: unit {u!r} is not none (R-b): shape at <list> <row key>[, case <name>]"
                       " | none (R-b): no shape (ill-formed)")
    else:
        g = rest[2:] if rest.startswith(": ") else None
        if g not in GROUNDS:
            bad.append(f"{where}: unit {u!r} is not none (scope): " + " | ".join(GROUNDS))
        elif cls == "scope":
            bad += [f"{where}: scope ({g}): {x}" for x in scope_fields(e, g)]
    return bad


def nested(e):
    """The tables nested in an entry: its `cases` (and theirs), `also_refused`, `split`."""
    for f in ("cases", "also_refused", "split"):
        v = e.get(f)
        for i, c in enumerate(v if isinstance(v, list) else [v]):
            if isinstance(c, dict):
                yield f"{f}[{i}]" + (f" ({str(c['case'])[:40]!r})" if "case" in c else ""), c
                for w, d in nested(c):
                    yield f"{f}[{i}].{w}", d


tally = {"rows": (collections.Counter(), collections.Counter()),
         "nested": (collections.Counter(), collections.Counter())}
grounds, bad = collections.Counter(), []
allowed = collections.defaultdict(list)   # ticket -> the failures its allowance counts
for l, tab in t.items():
    if not isinstance(tab, dict):
        continue
    for key, r in tab.items():
        if not isinstance(r, dict):
            continue
        for kind, where, e in [("rows", f"{l} {key!r}", r)] + [
                ("nested", f"{l} {key!r} {w}", c) for w, c in nested(r)]:
            for k, msg in check(where, e):
                owner = next((a[0] for a in ALLOWANCE if a[3](l, e, k)), None)
                (allowed[owner] if owner else bad).append(msg)
            if e.get("status") == "refused":
                bycls, withunit = tally[kind]
                bycls[e.get("class")] += 1
                withunit[e.get("class")] += "unit" in e
            m = NONE.match(e["unit"]) if isinstance(e.get("unit"), str) else None
            if m and m[1] == "scope" and m[2].startswith(": "):
                grounds[m[2][2:]] += 1


def counts(kind):
    bycls, withunit = tally[kind]
    cls = CLASSES + sorted((c for c in bycls if c not in CLASSES), key=str)
    return ", ".join(f"{c} {bycls[c]} ({withunit[c]} with unit)" for c in cls)


nbad, pins = len(bad), []
for tid, pin, what, _ in ALLOWANCE:
    got, st = allowed.get(tid, []), tstatus.get(tid)
    why = ("" if len(got) == pin and st not in (None, "done") else
           f"ticket {tid} is not in {prog}/tickets-*.toml" if st is None else
           f"ticket {tid} is done, so it owes nothing" if st == "done" else
           f"{len(got)} failures, pinned {pin}: " + ("a failure of this kind that the ticket does not owe"
                                                     if len(got) > pin else
                                                     "fewer than pinned: lower the pin"))
    pins.append((tid, pin, what, st, got, why))
    if why:
        bad.append(f"allowance {tid}: {why}")
nallow = sum(len(p[4]) for p in pins)
print("units: refused rows by class: " + counts("rows") + "; refused nested entries by class: "
      + counts("nested") + "; scope by ground: "
      + ", ".join(f"{g} {grounds[g]}" for g in GROUNDS)
      + f"; failing entries: {nallow + nbad}"
      + f", of which {nallow} in the allowance of pending tickets")
for tid, pin, what, st, got, why in pins:
    print(f"  allowance {tid} (status {st}): {len(got)} of {pin} pinned: {what}"
          + (f"; FAILS: {why}" if why else ""))
for b in bad[:20]:
    print(f"  {b}")
if len(bad) > 20:
    print(f"  ... and {len(bad) - 20} more")
sys.exit(1 if bad else 0)
