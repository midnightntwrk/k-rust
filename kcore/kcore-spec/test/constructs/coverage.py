"""The coverage document of DONE-0 C11, generated: test/constructs/K-coverage.md is written from
test/constructs/rows.toml (the construct table of C1 to C3) and ../core-manifest.toml (the cone's
layers and what each teaches), and from nothing else, so that it states no status the table does not.

The document holds, in this order:
  totals     per list (E1 to E8, C3) the rows by status, the nested entries by status, and the
             refused rows and refused nested entries by class (R-a, R-b, R-c, scope, then any other
             class met); then the supported entries (rows and nested) with an owed fact, counted
             in three groups by their best fixture (below), the first, proved, named apart: the
             entries of status supported whose owed fact the headline statements' hypothesis
             holds on a listed fixture; then the E6 library rows by their `e6_tie`: tied, of no
             direction (counted apart), refuted, uncovered. Nested entries are the tables of a
             row's `cases` (recursively), `also_refused` and `split`, walked as
             test/constructs/units.py walks them, so the class counts are units.py's.
  R-c        every entry (row or nested) of class R-c: its notion, the cone declaration that
             changes (`cone`), the ticket or unit that supports it (`unit`) and the planned lane.
  undecided  the rows of status pending-fixture and not-handled, by list.
  no model   every entry (row or nested) with a `derived` table of form (r), the text's sentences
             having no model (DONE-0 C7, rows-header.toml): its fixture, the sentences and families
             the refutation uses, the theorem, its kind where given, and `owed_refuted`. Such an
             entry's status cell in its list reads "STATUS (no model)".
  owed facts every entry (row or nested) with an `owed_state` (rows-header.toml: per fixture, the
             state of the CondDecided its account lists as owed, or a MatchIndependent proved on
             the text of a fixture of the same shape) or an `owed_refuted`: the count
             of entries by their best fixture (rows-header.toml: proved where one of its states is
             proved, else open where one is, else false; an owed_refuted is false), and each false
             or open owed fact, one line per fixture: the entry's group, the state, and the
             theorem or the reason. Such an entry's status cell reads "STATUS (owed fact proved)",
             "STATUS (owed fact open)" or "STATUS (owed fact false)", its group.
  teaches    every layer of the manifest in its order: id, status, `teaches`, declarations, and the
             status of each `except` entry; then the manifest's not_core items.
  the lists  one table per list, one line per row in rows.toml's order, each nested entry on a line
             of its own after its row: status, class, reason (the row's `reason`, else its `note`),
             cone, unit, fixture, kimp and kore marks, evidence. An erased entry's status is
             followed by the letters of the forms it carries (P pair, S absent, O other_file, C
             carried_by: rows-header.toml), or "no form"; P where it names `pair` or its
             `no_sentence` is of class erased (the fixture's same_as pair, rows-header.toml); the
             verdicts are rest.py's.
Cells are escaped for Markdown (\\ ` * _ ~ | and < in text; a key is a code span) and cut at a fixed
length (CUT characters for reason and evidence, NCUT for a case's text) ending in "…"; rows.toml
holds the whole. The output has no date, commit or path of the machine, so equal inputs give equal
bytes.

Usage (from kcore-spec):
  python3 -I test/constructs/coverage.py [write] [ROWS.toml [MANIFEST.toml [OUT.md]]]
      write the document (defaults test/constructs/rows.toml, ../core-manifest.toml,
      test/constructs/K-coverage.md)
  python3 -I test/constructs/coverage.py check [ROWS.toml [MANIFEST.toml [OUT.md]]]
      exit 1 when OUT.md differs from what write would write (test/constructs.sh runs it); the
      fix is to run write, also after a merge that conflicts in OUT.md.
"""
import collections, os, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ROWS = os.path.join(K, "test/constructs/rows.toml")
MANIFEST = os.path.join(K, "../core-manifest.toml")
OUT = os.path.join(K, "test/constructs/K-coverage.md")
LISTS = ["E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "C3"]
TITLES = {
    "E1": "E1 sentence kinds (Outer.jj)",
    "E2": "E2 attributes (Att.scala; key x KORE sentence class)",
    "E3": "E3 rule-body syntax (the rule grammar)",
    "E4": "E4 KORE grammar (kore-syntax.md; the reader's syntax tree)",
    "E5": "E5 emitted shapes (ModuleToKORE.java)",
    "E6": "E6 builtin library",
    "E7": "E7 compile passes (KoreBackend.steps)",
    "E8": "E8 kompile options",
    "C3": "C3 pairs of meaning-carrying modifiers",
}
STATUSES = ["supported", "parameter", "inert", "erased", "refused", "pending-fixture",
            "not-handled"]
CLASSES = ["R-a", "R-b", "R-c", "scope"]
CUT, NCUT = 300, 120


def text(s, cut=None):
    """A table cell's text: one line, Markdown's active characters escaped, cut at `cut`."""
    s = " ".join(str(s).split())
    if cut is not None and len(s) > cut:
        s = s[:cut].rstrip() + "…"
    for c in "\\`*_~|":
        s = s.replace(c, "\\" + c)
    return s.replace("<", "&lt;")


def code(s):
    """A key as a code span (| escaped, which a table cell needs even there)."""
    s = " ".join(str(s).split()).replace("|", "\\|")
    f = "``" if "`" in s else "`"
    return f"{f} {s} {f}" if f == "``" else f"{f}{s}{f}"


def nested(e):
    """The tables nested in an entry, as units.py walks them: its `cases` (and theirs),
    `also_refused`, `split`; each with its place."""
    for f in ("cases", "also_refused", "split"):
        v = e.get(f)
        for i, c in enumerate(v if isinstance(v, list) else [v]):
            if isinstance(c, dict):
                yield f"{f}[{i}]", c
                for w, d in nested(c):
                    yield f"{f}[{i}].{w}", d


def no_model(e):
    """The `derived` tables of form (r) of an entry."""
    ds = e.get("derived")
    return [d for d in ds if isinstance(d, dict) and d.get("form") == "r"] if isinstance(ds, list) else []


def owed_facts(e):
    """[(fixture, state, theorem or reason)] of an entry: its `owed_state`, then each owed_refuted
    of its form (r) tables, a refuted owed fact of its fixture."""
    out = []
    st = e.get("owed_state")
    for x, v in (st.items() if isinstance(st, dict) else []):
        word, _, rest = str(v).partition(": ")
        out.append((x, "false" if word == "refuted" else word, rest))
    out += [(e.get("fixture", ""), "false", d["owed_refuted"]) for d in no_model(e) if d.get("owed_refuted")]
    return out


def owed_mark(e):
    """The entry's group, its best fixture's state (proved, else open, else false), which
    K-coverage.md prints beside the entry's status; None for an entry with no owed fact."""
    ws = {w for _, w, _ in owed_facts(e)}
    return next((w for w in ("proved", "open", "false") if w in ws), None)


def mark(v):
    return "" if v is None else ("yes" if v is True else "no" if v is False else text(v, 20))


def table(head, rows):
    out = ["| " + " | ".join(head) + " |", "|" + "|".join("---" for _ in head) + "|"]
    out += ["| " + " | ".join(r) + " |" for r in rows]
    return out


def counts_table(first, by_list, keys, total=True):
    """A table of counts: one line per list, a column per key (zero columns dropped where the key
    is not a fixed one), and the total."""
    rows = []
    tot = collections.Counter()
    for l in LISTS:
        c = by_list.get(l, collections.Counter())
        tot.update(c)
        rows.append([l, str(sum(c.values()))] + [str(c.get(k, 0)) for k in keys])
    if total:
        rows.append(["all", str(sum(tot.values()))] + [str(tot.get(k, 0)) for k in keys])
    return table([first, "entries"] + keys, rows)


def erased_letters(e):
    """The letters of the forms of erased an entry carries (rows-header.toml)."""
    ns = e.get("no_sentence")
    pair = "pair" in e or (isinstance(ns, str) and ns.split(":", 1)[0].strip() == "erased")
    return [c for c, ok in [("P", pair), ("S", "absent" in e),
                            ("O", "other_file" in e or "witness" in e), ("C", "carried_by" in e)] if ok]


def e6_state(v):
    """An E6 row's `e6_tie` as one of tied, no direction, refuted, uncovered."""
    if isinstance(v, list):
        return "tied"
    for s in ("no direction", "refuted"):
        if isinstance(v, str) and v.startswith(s + ":"):
            return s
    return "uncovered"


def generate(rows_path, manifest_path):
    t = tomllib.load(open(rows_path, "rb"))
    m = tomllib.load(open(manifest_path, "rb"))
    extra = [l for l in t if l not in LISTS]
    if extra:
        raise SystemExit(f"coverage: tables of rows.toml this script does not know: {extra}")
    st_rows, st_nest = {}, {}
    cl_rows, cl_nest = {}, {}
    rc, undecided, nomodel, owed = [], collections.defaultdict(list), [], []
    for l in LISTS:
        st_rows[l], st_nest[l] = collections.Counter(), collections.Counter()
        cl_rows[l], cl_nest[l] = collections.Counter(), collections.Counter()
        for key, r in t.get(l, {}).items():
            st_rows[l][r.get("status")] += 1
            if r.get("status") == "refused":
                cl_rows[l][r.get("class")] += 1
            if r.get("status") in ("pending-fixture", "not-handled"):
                undecided[l].append((key, r))
            for w, e in [("", r)] + list(nested(r)):
                if w:
                    st_nest[l][e.get("status")] += 1
                    if e.get("status") == "refused":
                        cl_nest[l][e.get("class")] += 1
                if e.get("class") == "R-c":
                    rc.append((l, key, w, e))
                for d in no_model(e):
                    nomodel.append((l, key, w, e, d))
                if owed_mark(e):
                    owed.append((l, key, w, e))
    seen_st = {s for c in list(st_rows.values()) + list(st_nest.values()) for s in c}
    stcols = STATUSES + sorted((s for s in seen_st if s not in STATUSES), key=str)
    seen_cl = {s for c in list(cl_rows.values()) + list(cl_nest.values()) for s in c}
    clcols = CLASSES + sorted((s for s in seen_cl if s not in CLASSES), key=str)

    o = ["# KCore's coverage of K, generated from the construct table", "",
         "Generated by `test/constructs/coverage.py` from `test/constructs/rows.toml` and "
         "`../core-manifest.toml` (paths from `kcore-spec`); do not edit it. "
         "`python3 -I test/constructs/coverage.py` writes it, and `test/constructs.sh` fails "
         "(through `coverage.py check`) when it differs from what the two files give. "
         "Every status, class and count below is read from `rows.toml`; `rows-header.toml` says "
         "what each field means, and `designs/DONE-0-definition-of-done.md` C1 to C3 what the "
         "table must hold.", "",
         "Statuses (DONE-0 C2): **supported** (read, the kernel gives it the meaning named), "
         "**parameter** (numbered, uninterpreted; the theorems hold for every interpretation H), "
         "**inert** (no meaning in the semantics, with the reason), **erased** (kompile leaves no "
         "trace in `definition.kore`), **refused** (the reader, or kompile, stops with a named "
         "reason). Two more mark rows not yet decided: **pending-fixture** (the decision waits for "
         "a fixture) and **not-handled** (no recorded place gives a status); neither is a status at "
         "the release.", "",
         "Refusal classes (DONE-0 C2, rows-header.toml): **R-a** outside the fragment by a recorded "
         "decision; **R-b** the option value or text form is outside the language K's "
         "documentation or the KORE syntax document states; **R-c** the kernel has no notion for "
         "it, naming the cone declaration that would change; **scope** nothing excludes the form, "
         "but no text in scope holds it.", "",
         f"Cells are cut at {CUT} characters (a case's text at {NCUT}) and end in \"…\" where "
         "cut; `rows.toml` holds each field whole. A nested entry (a row's `cases`, "
         "`also_refused` or `split`, as `test/constructs/units.py` walks them) is the line after "
         "its row, named by its place.", ""]

    o += ["## Totals", "", "Rows by status:", ""]
    o += counts_table("list", st_rows, stcols)
    o += ["", "Nested entries by status:", ""]
    o += counts_table("list", st_nest, stcols)
    o += ["", "Refused rows by class:", ""]
    o += counts_table("list", cl_rows, clcols)
    o += ["", "Refused nested entries by class:", ""]
    o += counts_table("list", cl_nest, clcols)
    sup = sum(c["supported"] for c in list(st_rows.values()) + list(st_nest.values()))
    sg = collections.Counter(owed_mark(e) for _, _, _, e in owed if e.get("status") == "supported")
    o += ["", f"Supported entries (rows and nested): {sup}; {sum(sg.values())} of them have an owed fact and "
          f"are counted by their best fixture: **{sg['proved']} proved** (the owed fact proved on a "
          "fixture the entry names: these count as supported under the headline statements), "
          f"{sg['open']} open and {sg['false']} false (counted apart: the headline statements' hypothesis "
          f"is not shown on their fixtures). The other {sup - sum(sg.values())} have no owed fact."]
    e6t = collections.Counter(e6_state(r.get("e6_tie")) for r in t.get("E6", {}).values() if "e6_tie" in r)
    o += ["", f"E6 library rows by their `e6_tie` (test/constructs/e6map.py; rows-header.toml): {sum(e6t.values())}, "
          f"of which {e6t['tied']} tied, {e6t['no direction']} of no direction (the tie's no-direction class, "
          f"owed-sentence rule item 7: never tied, counted apart), {e6t['refuted']} refuted and "
          f"{e6t['uncovered']} uncovered."]

    o += ["", f"## Entries of class R-c ({len(rc)})", "",
          "Each names the notion the kernel lacks, the cone declaration that would change, and the "
          "ticket or unit that supports it (`unit`, checked by `units.py`).", ""]
    o += table(["list", "row", "entry", "status", "notion", "cone", "unit", "planned"], [
        [l, code(key), text(w) if w else "row", text(e.get("status", "")),
         text(e.get("notion", ""), CUT), text(e.get("cone", ""), CUT),
         text(e.get("unit", "no unit")), text(e.get("planned", ""), CUT)]
        for l, key, w, e in rc])

    nund = sum(len(v) for v in undecided.values())
    o += ["", f"## Rows not yet decided ({nund})", ""]
    if not nund:
        o += ["None: every row has one of the five statuses."]
    for l in LISTS:
        for key, r in undecided.get(l, []):
            o.append(f"- {l} {code(key)}: {text(r.get('status'))}"
                     + (f"; pending: {text(r['pending'], CUT)}" if r.get("pending") else ""))

    o += ["", f"## Entries whose text has no model, form (r) ({len(nomodel)})", "",
          "A `derived` table of form (r): a kernel-checked theorem that the premise set form (a) "
          "would use has no model, from the sentences named (by index) and the families named "
          "beside them; `owed_refuted` the theorem refuting the fact the package names as owed. "
          "The entry's status is the reading's, and its list prints \"(no model)\" beside it.", ""]
    if not nomodel:
        o += ["None."]
    else:
        o += table(["list", "row", "entry", "status", "fixture", "sentences", "families", "kind",
                    "theorem", "owed refuted"], [
            [l, code(key), text(w) if w else "row", text(e.get("status", "")), text(e.get("fixture", "")),
             text(", ".join(str(x) for x in d.get("sentences", [])) if isinstance(d.get("sentences"), list) else ""),
             text(d.get("family", ""), CUT), text(d.get("kind", "")), text(d.get("theorem", "")),
             text(d.get("owed_refuted", ""))]
            for l, key, w, e, d in nomodel])

    marks = collections.Counter(owed_mark(e) for _, _, _, e in owed)
    shown = [(l, key, w, e, f) for l, key, w, e in owed for f in owed_facts(e) if f[1] != "proved"]
    o += ["", f"## Entries with an owed fact ({len(owed)}: proved {marks['proved']}, open {marks['open']},"
          f" false {marks['false']})", "",
          "An entry's `owed_state` names, per fixture, the state of the CondDecided its account lists "
          "as owed: proved or refuted by the theorem named, or open with the reason (or, at a fixture "
          "of the same shape whose account owes none, a MatchIndependent proved on its text); an "
          "`owed_refuted` of form (r) is a refuted owed fact of the entry's fixture. An entry is "
          "counted by its best fixture: proved where one of its fixtures' facts is proved, else open "
          "where one is open, else false. An entry with an `owed_state` and no proved fixture "
          "says in a state why no fixture of its shape has the fact proved (`rest.py check`). The status stays "
          "the reading's: where the owed fact is false, the headline statements, whose hypothesis "
          "holds it, state nothing of the step at that text, and the fixture is a recorded limit of "
          "that hypothesis. The list prints the entry's group beside the "
          "status; below, every false or open owed fact, with its entry's group.", ""]
    if not shown:
        o += ["None."]
    else:
        o += table(["list", "row", "entry", "status", "group", "fixture", "owed fact", "theorem or reason"], [
            [l, code(key), text(w) if w else "row", text(e.get("status", "")), text(owed_mark(e)),
             text(f[0]), text(f[1]), text(f[2], CUT)]
            for l, key, w, e, f in shown])

    o += ["", "## What the cone teaches", "",
          "The layers of `core-manifest.toml` in their order, each with its `teaches` field (DONE-0 "
          "C11: the release gate and the completion gate read each against the cone's "
          "definitions) and the declarations it names; then the `except` entries and what the "
          "manifest puts outside the core.", ""]
    layers = sorted(m.get("layer", []), key=lambda x: x.get("order", 0))
    o += table(["order", "layer", "status", "teaches", "declarations"], [
        [str(x.get("order", "")), code(x.get("id", "")), text(x.get("status", "")),
         text(x.get("teaches", "")), text(", ".join(x.get("declarations", [])))]
        for x in layers])
    exc = [(x.get("id", ""), e) for x in layers for e in x.get("except", []) if isinstance(e, dict)]
    if exc:
        o += ["", "Exceptions inside the layers:", ""]
        o += table(["layer", "declaration", "status"], [
            [code(i), text(e.get("declaration", ""), CUT), text(e.get("status", ""))]
            for i, e in exc])
    nc = m.get("not_core", {}).get("items", [])
    if nc:
        o += ["", "Not core:", ""] + [f"- {text(x)}" for x in nc]

    for l in LISTS:
        tab = t.get(l, {})
        o += ["", f"## {TITLES[l]} ({len(tab)} rows)", ""]
        lines = []
        for key, r in tab.items():
            for w, e in [("", r)] + list(nested(r)):
                name = code(key) if not w else (
                    text(w) + (f": {text(e['case'], NCUT)}" if "case" in e else ""))
                st = e.get("status", "")
                if l == "C3" and e.get("core") is True:
                    st += " (core)"
                if st == "erased":
                    fs = erased_letters(e)
                    st += f" ({', '.join(fs)})" if fs else " (no form)"
                if no_model(e):
                    st += " (no model)"
                if owed_mark(e):
                    st += f" (owed fact {owed_mark(e)})"
                lines.append([
                    name, text(st), text(e.get("class", "")),
                    text(e.get("reason", e.get("note", "")), CUT)
                    + (f" Declarations: {text(', '.join(e['declarations']))}."
                       if isinstance(e.get("declarations"), list) else ""),
                    text(e.get("cone", ""), CUT), text(e.get("unit", ""), CUT),
                    text(e.get("fixture", "")), mark(e.get("kimp")), mark(e.get("kore")),
                    text(e.get("evidence", ""), CUT)])
        o += table(["row", "status", "class", "reason", "cone", "unit", "fixture", "kimp",
                    "kk.k", "evidence"], lines)
    return "\n".join(o) + "\n"


def main(argv):
    mode = "write"
    if argv and argv[0] in ("write", "check"):
        mode, argv = argv[0], argv[1:]
    elif argv and argv[0].startswith("-"):
        raise SystemExit(__doc__)
    rows, man, out = (argv + [None] * 3)[:3]
    doc = generate(rows or ROWS, man or MANIFEST)
    out = out or OUT
    if mode == "write":
        with open(out, "w") as f:
            f.write(doc)
        print(f"coverage: wrote {os.path.relpath(out, K)} ({doc.count(chr(10))} lines)")
        return 0
    have = open(out).read() if os.path.exists(out) else None
    if have == doc:
        print(f"coverage: {os.path.relpath(out, K)} is what rows.toml and the manifest give")
        return 0
    if have is None:
        print(f"coverage: no {os.path.relpath(out, K)}; run python3 -I test/constructs/coverage.py")
        return 1
    a, b = have.split("\n"), doc.split("\n")
    i = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    print(f"coverage: {os.path.relpath(out, K)} differs from what rows.toml and the manifest give, "
          f"first at line {i + 1}; run python3 -I test/constructs/coverage.py")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
