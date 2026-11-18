"""The coverage document of DONE-0 C11, generated: test/constructs/K-coverage.md is written from
test/constructs/rows.toml (the construct table of C1 to C3) and ../core-manifest.toml (the cone's
layers and what each teaches), and from nothing else, so that it states no status the table does not.

The document holds, in this order:
  totals     per list (E1 to E8, C3) the rows by status, the nested entries by status, and the
             refused rows and refused nested entries by class (R-a, R-b, R-c, scope, then any other
             class met). Nested entries are the tables of a row's `cases` (recursively),
             `also_refused` and `split`, walked as test/constructs/units.py walks them, so the class
             counts are units.py's.
  R-c        every entry (row or nested) of class R-c: its notion, the cone declaration that
             changes (`cone`), the ticket or unit that supports it (`unit`) and the planned lane.
  undecided  the rows of status pending-fixture and not-handled, by list.
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


def generate(rows_path, manifest_path):
    t = tomllib.load(open(rows_path, "rb"))
    m = tomllib.load(open(manifest_path, "rb"))
    extra = [l for l in t if l not in LISTS]
    if extra:
        raise SystemExit(f"coverage: tables of rows.toml this script does not know: {extra}")
    st_rows, st_nest = {}, {}
    cl_rows, cl_nest = {}, {}
    rc, undecided = [], collections.defaultdict(list)
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
