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
             changes (`cone`), the ticket or unit that supports it (`unit`) and the planned lane,
             in two parts by the `cone` prefix (findings/work/decision-rc-cone.md section 1 (c)):
             the R-c list, entries whose cone names declarations of ../core-cone.txt; and reader
             debt, entries whose cone starts with "none (reader only)" (no cone declaration
             changes, so the release gate requires none). Rows whose cone starts with "none at the
             row" are named after the two parts and counted through their cases.
  undecided  the rows of status pending-fixture and not-handled, by list.
  no model   every entry (row or nested) with a `derived` table of form (r) (DONE-0 C7,
             rows-header.toml: the premise set of its sentences and the families it names has no
             model; of kind "with the reading's families" the table says that a family is one no
             sentence of the text states and that the reading has no model either): the fixture
             whose text the sentences
             are (the table's `fixture`, else the entry's), the sentences and families
             the refutation uses, the theorem, its kind where given, and `owed_refuted`. Such an
             entry's status cell in its list reads "STATUS (no model)", "STATUS (no model with the
             reading's families)" where every such table is of kind "with the reading's families"
             (the text's own sentences are not shown to have none), or "STATUS (a sentence
             against the reading)" where every such table is of kind "sentence against the reading"
             (Γ has a model and refutes one sentence of the text as written; the entry's `family`
             says whether the text's own sentences have a model). The mark is of the text the
             sentences are: tables of a fixture that is not the entry's are marked apart, with their
             fixtures named first, "STATUS (FIXTURE, FIXTURE: MARK)", so that an entry whose own
             fixture has no such table is not marked as if it had.
  owed facts every entry (row or nested) with an `owed_state` (rows-header.toml: per fixture, the
             state of the CondDecided its account lists as owed, or a MatchIndependent proved on
             the text of a fixture of the same shape), an `owed_refuted` (a refuted owed fact of
             its table's fixture, as under no model) or a `match_refuted` table (rows-header.toml:
             a MatchIndependent refuted, false, on a text whose reading has a model; its line
             names both theorems, and where the entry's group is false its status cell reads
             "STATUS (owed fact false; the reading has a model)", the table's fixture named
             before "the reading has a model" where it is not the entry's): the count
             of entries by their best fixture (rows-header.toml: proved where one of its states is
             proved, else open where one is, else false; an owed_refuted is false), and each false
             or open owed fact, one line per fixture: the entry's group, the state, and the
             theorem or the reason. Such an entry's status cell reads "STATUS (owed fact proved)",
             "STATUS (owed fact open)" or "STATUS (owed fact false)", its group. An entry with a
             `tie_premise` table (rows-header.toml: its sentences tied under a premise no sentence
             of the text is shown to state) has its status cell read "STATUS (tied under PREMISE)", the
             tables' premises.
  teaches    every layer of the manifest in its order: id, status, `teaches`, declarations, and the
             status of each `except` entry; then the manifest's not_core items.
  cells      every `cell` entry of the manifest: the scoreboard row and column, the theorem named
             for it with its statement, file and the declarations it goes through, and how it is
             checked.
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
      fix is to run write, also after a merge that conflicts in OUT.md. Also exit 1 when an entry
      of class R-c has a cone that is not well formed (rc_defects): none; "none at the row" on a
      nested entry; or, outside the two "none" prefixes, a leading list (the comma-separated
      names before the first ":" or "(") with a name that is not a declaration of core-cone.txt
      (beside MANIFEST.toml), written short (a cone line ends in "." and the name) or unknown.
      Write does not read core-cone.txt: the document is the same with or without it.
"""
import collections, os, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ROWS = os.path.join(K, "test/constructs/rows.toml")
MANIFEST = os.path.join(K, "../core-manifest.toml")
OUT = os.path.join(K, "test/constructs/K-coverage.md")
LISTS = ["E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "C3"]
# the kind of a form (r) table whose reading has a model, none satisfying one sentence of the text
# as written (rows-header.toml)
AGAINST = "sentence against the reading"
FAMILIES = "with the reading's families"
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
# the prefixes of an R-c entry's `cone` that name no declaration (decision-rc-cone.md section 1 (c))
RC_DEBT, RC_ROW = "none (reader only)", "none at the row"


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


def rc_part(e):
    """The part of the R-c section an entry of class R-c is in, by its `cone` prefix: "debt" (reader
    debt), "row" (counted through its cases), else "list"."""
    c = str(e.get("cone", ""))
    return "debt" if c.startswith(RC_DEBT) else "row" if c.startswith(RC_ROW) else "list"


def rc_names(cone):
    """The leading list of an R-c cone: the comma-separated names before its first ":" or "("."""
    cut = min((i for i in (cone.find(":"), cone.find("(")) if i >= 0), default=len(cone))
    return [n.strip() for n in cone[:cut].split(",")]


def cone_decls(path):
    """The declaration names of core-cone.txt: the third field of its declaration lines."""
    out = set()
    for l in open(path, encoding="utf-8"):
        w = l.split()
        if l.startswith("  ") and len(w) >= 3 and w[0].count("-") == 1 and w[0].replace("-", "").isdigit():
            out.add(w[2])
    return out


def rc_defects(t, decls):
    """[(list, row, place, defect)] of the entries of class R-c whose cone is not well formed (the
    usage of check)."""
    out = []
    for l in LISTS:
        for key, r in t.get(l, {}).items():
            for w, e in [("", r)] + list(nested(r)):
                if e.get("class") != "R-c":
                    continue
                c = " ".join(str(e.get("cone", "")).split())
                if not c:
                    out.append((l, key, w, "no cone"))
                elif c.startswith(RC_ROW):
                    if w:
                        out.append((l, key, w, f"'{RC_ROW}' on a nested entry"))
                elif not c.startswith(RC_DEBT):
                    for n in rc_names(c):
                        if n in decls:
                            continue
                        full = sorted(d for d in decls if d.endswith("." + n))
                        out.append((l, key, w, f"'{n}' is short for {', '.join(full)}" if full and n else
                                    f"'{n}' is not a declaration of core-cone.txt"))
    return out


def no_model(e):
    """The `derived` tables of form (r) of an entry."""
    ds = e.get("derived")
    return [d for d in ds if isinstance(d, dict) and d.get("form") == "r"] if isinstance(ds, list) else []


def table_fixture(e, d):
    """The fixture whose text a `derived` table's sentences are: its own `fixture` (another
    fixture's text than the entry's, rows-header.toml), else the entry's."""
    return d.get("fixture") or e.get("fixture", "")


def no_model_mark(e):
    """The mark beside an entry's status, "" without a form (r) table. A mark is of one text: "no
    model", or "a sentence against the reading" where each form (r) table of that text is of kind
    "sentence against the reading", or "no model with the reading's families" where each is of kind
    "with the reading's families". The tables of the entry's own fixture give the bare mark; those
    of another fixture's text give "FIXTURE, ...: MARK", the fixtures of one mark together, so the
    entry's own fixture is not said to have what another text has."""
    by = {}
    for d in no_model(e):
        by.setdefault(table_fixture(e, d), []).append(d)
    marks = {}
    for x, ds in by.items():
        m = ("a sentence against the reading" if all(d.get("kind") == AGAINST for d in ds) else
             "no model with the reading's families" if all(d.get("kind") == FAMILIES for d in ds) else "no model")
        marks.setdefault(m, []).append(x)
    own = e.get("fixture", "")
    out = []
    for m, xs in marks.items():
        if own in xs:
            out.append(m)
        rest = [x for x in xs if x != own]
        if rest:
            out.append(", ".join(rest) + ": " + m)
    return "; ".join(out)


def premise_mark(e):
    """The mark beside an entry's status for its `tie_premise` tables, "tied under PREMISE" (the
    premises of the tables, in their order, each once), "" without one."""
    tp = e.get("tie_premise")
    ps = [d["premise"] for d in tp if isinstance(d, dict) and isinstance(d.get("premise"), str)] \
        if isinstance(tp, list) else []
    return "tied under " + ", ".join(dict.fromkeys(ps)) if ps else ""


def owed_facts(e):
    """[(fixture, state, theorem or reason)] of an entry: its `owed_state`, then each owed_refuted
    of its form (r) tables, a refuted owed fact of the table's fixture."""
    out = []
    st = e.get("owed_state")
    for x, v in (st.items() if isinstance(st, dict) else []):
        word, _, rest = str(v).partition(": ")
        out.append((x, "false" if word == "refuted" else word, rest))
    out += [(table_fixture(e, d), "false", d["owed_refuted"]) for d in no_model(e) if d.get("owed_refuted")]
    out += [(d.get("fixture", ""), "false", f"{d.get('owed_refuted', '')}; the reading has a model: {d.get('consistent', '')}")
            for d in match_refuted(e)]
    return out


def owed_mark(e):
    """The entry's group, its best fixture's state (proved, else open, else false), which
    K-coverage.md prints beside the entry's status; None for an entry with no owed fact."""
    ws = {w for _, w, _ in owed_facts(e)}
    return next((w for w in ("proved", "open", "false") if w in ws), None)


def match_refuted(e):
    """The tables of an entry's `match_refuted` (rows-header.toml: a table or a list of them)."""
    v = e.get("match_refuted")
    v = [v] if isinstance(v, dict) else v if isinstance(v, list) else []
    return [d for d in v if isinstance(d, dict)]


def model_mark(e):
    """"; the reading has a model" after the group "false" of an entry with a `match_refuted` table
    (its owed MatchIndependent false on a text whose reading has a model), the fixtures of tables
    that are not the entry's own named first; "" otherwise."""
    if owed_mark(e) != "false":
        return ""
    xs = list(dict.fromkeys(d.get("fixture", "") for d in match_refuted(e)))
    if not xs:
        return ""
    own = e.get("fixture", "")
    out = (["the reading has a model"] if own in xs else []) + [x + ": the reading has a model" for x in xs if x != own]
    return "; " + "; ".join(out)


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
    """An E6 row's `e6_tie` as one of tied, no direction, no model, refuted, uncovered (a module row's
    "no direction in a model: " and "refuted (recorded): " counted with no direction and refuted)."""
    if isinstance(v, list):
        return "tied"
    for p, s in (("no direction: ", "no direction"), ("no direction in a model: ", "no direction"),
                 ("no model: ", "no model"), ("refuted: ", "refuted"), ("refuted (recorded): ", "refuted")):
        if isinstance(v, str) and v.startswith(p):
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
                if w and e.get("status") is not None:  # a nested table without status records a shape (rest.py)
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
          f"owed-sentence rule item 7: never tied, counted apart), {e6t['no model']} of a text without a model "
          f"(counted apart), {e6t['refuted']} refuted and "
          f"{e6t['uncovered']} uncovered."]

    parts = {p: [x for x in rc if rc_part(x[3]) == p] for p in ("list", "debt", "row")}
    o += ["", f"## Entries of class R-c ({len(rc)})", "",
          "Each names the notion the kernel lacks, the cone declaration that would change, and the "
          "ticket or unit that supports it (`unit`, checked by `units.py`). They are in two parts by "
          f"the `cone` prefix: the R-c list ({len(parts['list'])}), whose cone names declarations of "
          f"`../core-cone.txt` (`coverage.py check` fails a name that is not one, or is written short); "
          f"and reader debt ({len(parts['debt'])}), whose cone starts with \"{RC_DEBT}\": no cone "
          "declaration changes, the reading is the reader's to write, and the release gate requires "
          f"none. The {len(parts['row'])} rows whose cone starts with \"{RC_ROW}\" are counted "
          "through their cases and named after the two parts.", ""]

    def rc_table(xs):
        return table(["list", "row", "entry", "status", "notion", "cone", "unit", "planned"], [
            [l, code(key), text(w) if w else "row", text(e.get("status", "")),
             text(e.get("notion", ""), CUT), text(e.get("cone", ""), CUT),
             text(e.get("unit", "no unit")), text(e.get("planned", ""), CUT)]
            for l, key, w, e in xs]) if xs else ["None."]
    o += [f"### The R-c list: a cone declaration changes ({len(parts['list'])})", ""]
    o += rc_table(parts["list"])
    o += ["", f"### Reader debt: no cone declaration changes, none at the gate ({len(parts['debt'])})", ""]
    o += rc_table(parts["debt"])
    o += ["", f"Rows counted through their cases ({len(parts['row'])}): "
          + ("; ".join(f"{l} {code(key)}" for l, key, _, _ in parts["row"]) or "none") + "."]

    nund = sum(len(v) for v in undecided.values())
    o += ["", f"## Rows not yet decided ({nund})", ""]
    if not nund:
        o += ["None: every row has one of the five statuses."]
    for l in LISTS:
        for key, r in undecided.get(l, []):
            o.append(f"- {l} {code(key)}: {text(r.get('status'))}"
                     + (f"; pending: {text(r['pending'], CUT)}" if r.get("pending") else ""))

    o += ["", "## Entries with a table of form (r): a text without a model, one without a model with the reading's "
          f"families, or a sentence against the reading ({len(nomodel)})", "",
          "A `derived` table of form (r): a kernel-checked theorem that the premise set form (a) "
          "would use has no model, from the sentences named (by index) and the families named "
          "beside them; `owed_refuted` the theorem refuting the fact the package names as owed. "
          "The fixture is the one whose text the sentences are: the table's `fixture` where they are "
          "another fixture's than the entry's, else the entry's. "
          "The entry's status is the reading's, and its list prints \"(no model)\" beside it. "
          f"Of kind \"{FAMILIES}\": the premise set holds families of the reading that no sentence of the "
          "text states (named under families), and the reading has no model either (`inconsistent`): the text "
          "has no model with those families, which are what K means by its hooked sorts and symbols and by its "
          "constructors, and its own sentences are not shown to have none; `from sentences` names the theorem, "
          "where there is one, of what the sentences and the signature alone give. "
          "Its list prints \"(no model with the reading's families)\". "
          f"Of kind \"{AGAINST}\": the reading has a model (`consistent`), and no model of it satisfies "
          "the first sentence named as written; the sentence-level statement stays owed "
          "(`owed_statement`), and `family` says which of the premises a sentence of the text states: "
          "where one is the reading's alone, the text's own sentences may have a model. "
          "Its list prints \"(a sentence against the reading)\". "
          "A mark is of the text the sentences are: where that is another fixture's than the entry's, "
          "the list names the fixture before the mark.", ""]
    if not nomodel:
        o += ["None."]
    else:
        o += table(["list", "row", "entry", "status", "fixture", "sentences", "families", "kind",
                    "theorem", "owed refuted", "inconsistent", "from sentences"], [
            [l, code(key), text(w) if w else "row", text(e.get("status", "")), text(table_fixture(e, d)),
             text(", ".join(str(x) for x in d.get("sentences", [])) if isinstance(d.get("sentences"), list) else ""),
             text(d.get("family", ""), CUT), text(d.get("kind", "")), text(d.get("theorem", "")),
             text(d.get("owed_refuted", "")), text(d.get("inconsistent", "")), text(d.get("from_sentences", ""))]
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
    if any(match_refuted(e) for _, _, _, e in owed):
        o[-2] += (" A `match_refuted` table is an owed MatchIndependent refuted, for every H, on a text "
                  "whose reading has a model (`consistent`, named beside it): the fact is false and the "
                  "text is no text without a model, so the list prints \"(owed fact false; the reading has a "
                  "model)\" where the entry's group is false, and no \"(no model)\".")
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

    cells = [x for x in m.get("cell", []) if isinstance(x, dict)]
    o += ["", f"## Scoreboard cells the manifest names ({len(cells)})", "",
          "The `cell` entries of `core-manifest.toml`: a row and a column of the release scoreboard "
          "(DONE-0 section 3), the theorem the manifest names for it, its statement and file, and how "
          "it is checked. They are not entries of the cone, and a cell the manifest does not name is "
          "not listed here.", ""]
    if not cells:
        o += ["None."]
    else:
        o += table(["row", "column", "theorem", "statement", "file"], [
            [text(x.get("row", "")), text(x.get("column", "")), code(x.get("theorem", "")),
             text(x.get("statement", "")), text(x.get("file", ""))]
            for x in cells])
        for x in cells:
            o += ["", f"{code(x.get('theorem', ''))} ({text(x.get('row', ''))}, {text(x.get('column', ''))}): "
                  f"{text(x.get('criterion', ''))}", ""]
            o += [f"- through: {text(t)}" for t in x.get("through", [])]
            if x.get("meaning"):
                o += [f"- {text(x['meaning'])}"]
            o += [f"- checked by: {text(c)}" for c in x.get("checked_by", [])]

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
                if no_model_mark(e):
                    st += f" ({no_model_mark(e)})"
                if premise_mark(e):
                    st += f" ({premise_mark(e)})"
                if owed_mark(e):
                    st += f" (owed fact {owed_mark(e)}{model_mark(e)})"
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
    bad = 0
    if mode == "check":
        cone = os.path.join(os.path.dirname(os.path.abspath(man or MANIFEST)), "core-cone.txt")
        if not os.path.exists(cone):
            print(f"coverage: no {os.path.relpath(cone, K)}, which the R-c check reads")
            bad = 1
        else:
            ds = rc_defects(tomllib.load(open(rows or ROWS, "rb")), cone_decls(cone))
            for l, key, w, d in ds:
                print(f"coverage: R-c cone of {l} {key} {w or 'row'}: {d}")
            bad = 1 if ds else 0
    if mode == "write":
        with open(out, "w") as f:
            f.write(doc)
        print(f"coverage: wrote {os.path.relpath(out, K)} ({doc.count(chr(10))} lines)")
        return 0
    have = open(out).read() if os.path.exists(out) else None
    if have == doc:
        print(f"coverage: {os.path.relpath(out, K)} is what rows.toml and the manifest give")
        return bad
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
