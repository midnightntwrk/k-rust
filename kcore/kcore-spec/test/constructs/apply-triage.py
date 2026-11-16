#!/usr/bin/env python3
"""Applies the TRIAGE decisions (findings/TRIAGE-A-E1-E3-E7-E8.toml, TRIAGE-B-E2.toml,
TRIAGE-C-E4-E5-E6.toml) to test/constructs/rows.toml, row by row, and prints the counts per list
and status.

Usage: apply-triage.py [FINDINGS_DIR]   (default: ../findings beside kcore-spec)

Each decision's fields are copied as written; only their names are made one vocabulary
(rows-header.toml): refusal_class -> class, cone_declaration -> cone, reverse_when -> reversal,
sure -> confidence, note / notes / caveat / todo -> triage_note (a list). `triage` names the entry.
Where a decision gives `evidence`, it becomes the row's evidence and a non-empty earlier one is kept
as evidence_seed. A key a decision names that rows.toml lacks is printed and not applied.
Two entries are not tables of keys and are encoded here, quoting their text:
  - TRIAGE-B [status_wrong]: `decided` is prose; STATUS_WRONG below gives its status and class.
  - TRIAGE-C notes that name rows already refused (the MINT rows, the alias rows): `class` added.
TRIAGE-B [undecided] rows become `pending-fixture` with the entry's `why` as `pending`.
Every row of class R-c gets `planned`: the owner supports every R-c row before R2, and PLANNED
gives the lane of designs/CN-3-merged-constructs.md section 4 that builds it (a shape CN-3 section 5
keeps refused on principle is named in `planned_refused`). A row whose R-c shape is a case of a row
of another status gets the same in `also_planned`.
"""
import json, os, sys, tomllib
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROWS = os.path.join(HERE, "rows.toml")
FD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "..", "..", "..", "findings")
FA, FB, FC = "TRIAGE-A-E1-E3-E7-E8.toml", "TRIAGE-B-E2.toml", "TRIAGE-C-E4-E5-E6.toml"
load = lambda f: tomllib.load(open(os.path.join(FD, f), "rb"))
A, B, C = load(FA), load(FB), load(FC)
rows = tomllib.load(open(ROWS, "rb"))

RENAME = {"refusal_class": "class", "cone_declaration": "cone", "reverse_when": "reversal",
          "sure": "confidence"}
NOTES = ("note", "notes", "caveat", "todo")
SKIP = {"keys", "rows", "group"}

decisions = []     # (list, key, fields, pointer)
def fields_of(d):
    out, notes = {}, []
    for a, v in d.items():
        if a in SKIP: continue
        if a in NOTES: notes += v if isinstance(v, list) else [v]
        else: out[RENAME.get(a, a)] = v
    if notes: out["triage_note"] = notes
    return out

# TRIAGE-A: [<list>.<group>] with keys
for l in ("E1", "E3", "E7", "E8"):
    for g, d in A[l].items():
        for k in d["keys"]:
            decisions.append((l, k, fields_of(d), f'findings/{FA} [{l}."{g}"]'))
# TRIAGE-B: [group.*] with keys, [row."KEY"], [undecided."KEY"], [status_wrong."KEY"]
for g, d in B["group"].items():
    for k in d["keys"]:
        decisions.append(("E2", k, fields_of(d), f'findings/{FB} [group.{g}]'))
for k, d in B["row"].items():
    decisions.append(("E2", k, fields_of(d), f'findings/{FB} [row."{k}"]'))
for k, d in B["undecided"].items():
    decisions.append(("E2", k, {"status": "pending-fixture", "pending": d["why"]}, f'findings/{FB} [undecided."{k}"]'))
STATUS_WRONG = {   # TRIAGE-B status_wrong `decided`, as status and class
    "COOL(cool)@rule": {"status": "inert"},
    "COOL(cool)@equation": {"status": "refused", "class": "R-c", "cone": "KCore.Semantics.clauseSorted (binds)"},
    "COOL(cool)@simplification": {"status": "inert"},
    "FORMAT(format)@symbol": {"status": "erased"},
    "SMT_LEMMA(smt-lemma)@rule": {"status": "refused", "class": "R-b"},
    "SYMBOLIC(symbolic)@rule": {"status": "inert"},
}
for k, d in B["status_wrong"].items():
    f = dict(STATUS_WRONG[k]); f.update({("was" if a == "recorded" else a): v for a, v in fields_of(d).items()})
    decisions.append(("E2", k, f, f'findings/{FB} [status_wrong."{k}"]'))
# TRIAGE-C: [[E4]], [[E5]], [[E6]] with group and keys
for l in ("E4", "E5", "E6"):
    for d in C[l]:
        for k in d["keys"]:
            decisions.append((l, k, fields_of(d), f'findings/{FC} [[{l}]] group "{d["group"]}"'))
# TRIAGE-C notes on rows already refused
def note_of(l, g):
    return next(d for d in C[l] if d["group"] == g)["note"]
for k, r in rows["E6"].items():
    if r["status"] == "refused" and "Q11" in r["evidence"] and "MInt" in r["evidence"]:
        decisions.append(("E6", k, {"class": "R-a", "triage_note": [note_of("E6", "parametric-hooks")]},
                          f'findings/{FC} [[E6]] group "parametric-hooks", note'))
for k in ("grammar:<sentence>::=<sentence-alias>", "tree:Sentence.alias"):
    decisions.append(("E4", k, {"class": "R-b", "triage_note": [note_of("E4", "alias-syntax")]},
                      f'findings/{FC} [[E4]] group "alias-syntax", note'))
for k, r in rows["E4"].items():
    if k.startswith('grammar:<sentence-alias>::='):
        decisions.append(("E4", k, {"class": "R-b", "triage_note": [note_of("E4", "alias-syntax")]},
                          f'findings/{FC} [[E4]] group "alias-syntax", note'))

# ------------------------------------------------------------------ CN-3 lanes for R-c rows
OPEN = "refused (principle): CN-3 section 5, openExtent (a quantifier, complement or \\floor of a term over an unconfined sort)"
ML = 'ML-SYNTAX:'
PLANNED = {   # (list, key) -> (planned, planned_refused or None)
    ("E3", ML + 'Sort::="#Top"'): ("CN-3 P1 (e0, e1: L-2, an anonymous variable, reader only); R3 (e2: R-5, a right side as `?Z` with `post`)", OPEN),
    ("E3", ML + 'Sort::="#Bottom"'): ("CN-3 P1 (e0, e1: L-4 inert vacuousLeft; R-3, FR-3 `ens := false`, reader only)", None),
    ("E3", ML + 'Sort::="#Not" "(" Sort ")"'): ("CN-3 R3 (e2: L-7, `pre := not (exMatch ..)`; R-5 as `?Z` with `post`); e3 (`Clause.pre`)", OPEN),
    ("E3", ML + 'Sort2::="#Ceil" "(" Sort1 ")"'): ("CN-3 R3 (e2: L-9 into `Rule.pre`, R-4 into `Rule.post`); e3 (`Clause.pre`, `Clause.post`); P1 (e1: C-2 `req := false`, reader only)", None),
    ("E3", ML + 'Sort2::="#Floor" "(" Sort1 ")"'): ("CN-3 R3 (e2) and e3: the floor of a predicate is the predicate (`Cond`)", OPEN),
    ("E3", ML + 'Sort2::="{" Sort1 "#Equals" Sort1 "}"'): ("CN-3 P1 (e1: R-1, FR-1 as `ens`, reader only); R3 (e2: `Cond.equals` in `pre`, `post`); e3", None),
    ("E3", ML + 'Sort::=Sort "#And" Sort'): ("CN-3 P1 (e1: R-1, R-2, FR-1, FR-2 as `ens`, C-1 as andBool, reader only); R3 (e2: L-5, L-6 into `Rule.pre`, R-4 into `Rule.post`); e3 (FR-4)", None),
    ("E3", ML + 'Sort::=Sort "#Implies" Sort'): ("CN-3 R3 (e2: L-8 as L-7 and L-1)", OPEN),
    ("E3", ML + 'Sort2::="#Exists" Sort1 "." Sort2'): ("CN-3 P1 (e1: L-3, a variable of the rule, reader only); R2 (A3: R-5 as `?Z`); 4.5 d4 (`Cond.ex` over a confined sort)", OPEN),
    ("E3", ML + 'Sort2::="#Forall" Sort1 "." Sort2'): ("CN-3 4.5 d4 (`Cond.all` over a confined sort)", OPEN),
}
EXIST = ("CN-3 R2 (A3: `Rule.exs`, `has_model_choice`, the reader arm, Emit; fixture e3-vars); F2 (EX: `Clause.exs` at confined sorts)",
         "refused (principle): CN-3 section 5, existentialEquation (an equation's `\\exists` over an unconfined sort)")
SETVAR = ("CN-3 P2 (the fixture for a non-linear `@S` outside `[simplification]`); Reading SV-1 (linear `@S` read as an element variable, reader only); F2 (a non-linear `@S`, with its fixture)",
          "R-b where kompile rejects the shape (CN-3 section 5)")
FORALL = PLANNED[("E3", ML + 'Sort2::="#Forall" Sort1 "." Sort2')]
FLOOR = PLANNED[("E3", ML + 'Sort2::="#Floor" "(" Sort1 ")"')]
UNBOUND = ("CN-3 R1 (A2: open universal variables, `ruleSorted`, `rulesPlain`, `OpenWitnessed`; fixtures e2-unbound, e2-rule); F1 (B1: open variables in clauses)",
           "refused (principle): CN-3 section 5, openRequires (an open condition variable of an unconfined sort, in a rule that is not last or in any clause)")
OPENGEN = ("CN-3 V3 (d1: open generators, `ParamSig.raw`, `ParamSig.assoc`; d3: `assocH`, `OpenLaws`; V4); P2 (d2: the reader; fixtures e2-comm-ctor, e2-open-rule)",
           "openGeneratorPattern (an open generator binding a variable in a left side): refused until d4, then only at an unconfined sort (CN-3 section 5)")
for k in ("KSEQ-SYMBOLIC:#KVariable::=r\"(\\\\!|\\\\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)\"#existential-?",):
    PLANNED[("E3", k)] = EXIST
PLANNED[("E3", "KSEQ-SYMBOLIC:#KVariable::=r\"(\\\\!|\\\\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)\"#set-@")] = SETVAR
for g in C["E4"]:
    if g["group"] == "set-variable":
        for k in g["keys"]: PLANNED[("E4", k)] = SETVAR
    if g["group"] == "forall-floor":
        for k in g["keys"]: PLANNED[("E4", k)] = FORALL if "forall" in k else FLOOR
for k in B["group"]["unbound-variable"]["keys"]: PLANNED[("E2", k)] = UNBOUND
PLANNED[("E2", "ASSOC(assoc)@symbol")] = OPENGEN
PLANNED[("E2", "COMM(comm)@symbol")] = OPENGEN
PLANNED[("E2", "COOL(cool)@equation")] = ("CN-3 F1 (B1: open variables in clauses; fixture e2-cool-eq)", UNBOUND[1])
for g in C["E6"]:
    if g["group"] == "rangemap":
        for k in g["keys"]:
            PLANNED[("E6", k)] = ("CN-3 V1 (c1: the RANGEMAP carrier and its hooks); P2 (c2: the reader's module RANGEMAP, fixture e6-rangemap); V5 (c3: range-map patterns that bind variables)",
                                  "rangeMapPattern: refused until c3 (CN-3 section 5)")
    if g["group"] == "configuration-reflection":
        for k in g["keys"]:
            PLANNED[("E6", k)] = ("CN-3 P1 (B2: `#configuration` as a parameter symbol, ReadingNote.reflectionAsOwn; fixture e6-configuration)", None)
ALSO = {   # (list, key) -> plans for an R-c (or undecided) shape inside a row of another status
    ("E3", ML + 'Sort::=Sort "#Or" Sort'): ["elsewhere (a right side; a function equation): CN-3 R3 (e2: R-5, `t #Or u` as `?Z` with `post`); F2 (FR: three clauses of one priority)"],
    ("E7", "09:resolveHeatCoolAttribute"): ["also_refused (no HOLE): CN-3 R1 (A2: `OpenWitnessed` for HOLE; fixture e2-rule)"],
    ("E2", "COOL(cool)@rule"): ["split (author-written cool): CN-3 R1 (A2: `OpenWitnessed` for HOLE; fixture e2-rule)"],
    ("E2", "IDEM(idem)@symbol"): ["split (a production that is no collection concatenation): CN-3 V3 (d1: open generators); CN-3 names no unit for the idempotence axiom"],
    ("E5", "translateSorts:hooked-#2"): ["case RANGEMAP.RangeMap: CN-3 V1 (c1)",
                                          "case a user sort hooked to a builtin carrier: CN-3 V1 (S; fixture e5-hooked-int)"],
    ("E5", "genOverloadedAxiom:axiom#1"): ["case f a constructor, g a function: CN-3 F2 (D7, in `EvalTerm`), P2 (the D7 fixture)",
                                            "case overloadForm (KCore.OvlSig): no CN-3 unit"],
    ("E5", "convertRule:axiom#1"): ["case non-executable beside [owise]: CN-3 F1 (C1: `aside`; fixture e5-owise-nonexec)"],
    ("E5", "convertRule:axiom#2"): ["case B49 (`?X`): CN-3 R2 (A3)", "case B51 (a variable only under the function): CN-3 R3 (B3: the function cut, `pre := equals V f(X)`)"],
}

# ------------------------------------------------------------------ apply
mismatched, seen, changed = [], {}, []
for l, k, f, ptr in decisions:
    if k not in rows.get(l, {}):
        mismatched.append((l, k, ptr)); continue
    if (l, k) in seen:
        print(f"conflict: {l} {k!r} decided by {seen[(l, k)]} and {ptr}"); sys.exit(1)
    seen[(l, k)] = ptr
    r = rows[l][k]
    old = r["status"]
    if "evidence" in f and r.get("evidence") and r["evidence"] != f["evidence"]:
        r["evidence_seed"] = r["evidence"]
    r.update(f)
    r["triage"] = ptr
    if r["status"] != old:
        if old != "not-handled":
            r.setdefault("was", old); changed.append((l, k, old, r["status"]))
for (l, k), (p, pr) in PLANNED.items():
    r = rows[l][k]
    assert r.get("class") == "R-c", (l, k, r.get("class"))
    r["planned"] = p
    if pr: r["planned_refused"] = pr
for (l, k), a in ALSO.items():
    rows[l][k]["also_planned"] = a
rc = [(l, k) for l in rows for k, r in rows[l].items() if r.get("class") == "R-c"]
unplanned = [x for x in rc if "planned" not in rows[x[0]][x[1]]]

# ------------------------------------------------------------------ write
def v(b):
    if isinstance(b, str): return json.dumps(b, ensure_ascii=False)
    if isinstance(b, bool): return str(b).lower()
    if isinstance(b, list): return "[" + ", ".join(v(x) for x in b) + "]"
    if isinstance(b, dict): return "{ " + ", ".join(f"{a} = {v(c)}" for a, c in b.items()) + " }"
    return str(b)
with open(ROWS, "w") as fh:
    fh.write(open(os.path.join(HERE, "rows-header.toml")).read())
    for l, tab in rows.items():
        fh.write(f"\n[{l}]\n")
        for k, r in tab.items():
            fh.write(f"{v(k)} = {v(r)}\n")

# ------------------------------------------------------------------ report
for l, tab in rows.items():
    c = Counter(r["status"] for r in tab.values())
    cl = Counter(r["class"] for r in tab.values() if r["status"] == "refused" and "class" in r)
    print(f"{l}: {len(tab)} rows; " + ", ".join(f"{s} {n}" for s, n in sorted(c.items()))
          + (f"; refused by class: " + ", ".join(f"{s} {n}" for s, n in sorted(cl.items())) if cl else ""))
tot = Counter(r["status"] for tab in rows.values() for r in tab.values())
print("all: " + ", ".join(f"{s} {n}" for s, n in sorted(tot.items())))
print(f"rows of class R-c: {len(rc)}, without `planned`: {len(unplanned)}")
for l, k, ptr in mismatched: print(f"no row for a decided key: {l} {k!r} ({ptr})")
for l, k, a, b in changed: print(f"status changed from a recorded one: {l} {k!r}: {a} -> {b}")
for l, tab in rows.items():
    for k, r in tab.items():
        if r["status"] == "not-handled": print(f"not-handled: {l} {k!r}")
        if r["status"] == "pending-fixture": print(f"pending-fixture: {l} {k!r} ({r['triage']})")
