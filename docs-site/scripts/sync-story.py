#!/usr/bin/env python3
"""Generate the introduction's mutants and story data, and check them against krs.

`story/story.toml` lists the corpus and the edits the introduction makes to the `plus`
specification in `story/plus/`, whose corpus is `story/plus/kink/` (`FLOW.toml`, the cases it
names, and the edits as K patches in `mutations/plus.toml`). `--write` generates
`story/mutants/<id>/` (the specification with one edit of its Rust source and the same cases),
`src/generated/story.ts` (the data the scene components read), and the story block of
`recorded-outputs.toml`. Without an option, the script fails when any of them is stale.

Neither the rules each test fires nor the tests that catch each edit are written by hand.
A test's rules are the `fired` list of its case in the recorded `krs kink results --output
verdicts` (`story-kink-results`), named by KRS item as a stop names it, `crate::` and the item's
path in the story's package (`crate::plus_zero`), each read as the scenes' rule of that path and
put in the order of the scenes' `ruleNames`; a story test with no case there, a case that is not `comparable`, or a case or a
fired rule the story does not know fails the script, naming it, as does a FLOW.toml that lists
its cases in another order than story.toml's tests. The tests that catch an edit are the
`killed_by` of its mutation in the recorded `krs kink run --full --output verdicts`
(`story-kink-run`), and its misunderstanding, which the scenes quote, is the mutation's own;
an edit whose mutation is neither killed nor survived, a mutation the story does not know, and
a mutations directory with other edits than story.toml's, in its order, fail the script.
The edit's Rust form in story.toml generates the package whose recorded `krs run` outputs the
scenes show per test. The two forms of an edit must be one edit: the script fails unless that
package's recorded `krs emit-k` (`story-emit-k-<id>`) is `kink/definition.k` with the mutation's
patch applied, its package name aside, and unless the tests whose `krs run` result changes there
are exactly the mutation's killers.
Each edit's Rust location, which the mutation scene shows beside its paper notation, is the
first Rust range of its mutation's first edit in the recorded `krs kink check` (`story-kink-check`,
the document's `mutations`); a mutation with none fails the script.
The guide "Mutation testing a KRS specification" runs a second corpus of the package,
`story/plus/guide/`, which must stay the story's corpus plus one case: its `FLOW.toml` lists
`kink/FLOW.toml`'s cases, in order, then `t5`, and each shared case file is the story's.
`--write` needs those recorded outputs; on a fresh corpus run `record-outputs.py --write`
after it and then `--write` again.
"""

from __future__ import annotations

import difflib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

SITE = Path(__file__).resolve().parent.parent
STORY = SITE / "story"
BASE = STORY / "plus"
CORPUS = BASE / "kink"
GUIDE = BASE / "guide"
# The case the guide adds to the story's corpus, to kill a mutation the story's cases miss.
GUIDE_CASE = "t5"
DATA = SITE / "src" / "components" / "story" / "data.ts"
MUTATIONS = CORPUS / "mutations"
# The edits are the mutations of mutations/<TOPIC>.toml; kink qualifies their ids as <TOPIC>/<id>.
TOPIC = "plus"
VERDICTS = "story-kink-results"
RUN = "story-kink-run"
CHECK = "story-kink-check"
OUTPUTS = SITE / "src" / "snippets" / "outputs"
MANIFEST = SITE / "recorded-outputs.toml"
GENERATED = SITE / "src" / "generated" / "story.ts"
START = "# [story:start]"
END = "# [story:end]"


class Failure(Exception):
    """A story check that failed; its message names what to fix."""


def fail(message: str) -> None:
    raise Failure(message)


# A story edit's keys: the tool decides the rest (its misunderstanding is the mutation's own and
# the tests that catch it are its killers), so story.toml may not state them again.
EDIT_KEYS = {"id", "rule", "label", "old", "new", "display_old", "display_new"}


def load() -> dict:
    story = tomllib.loads((STORY / "story.toml").read_text(encoding="utf-8"))
    ids = [mutation["id"] for mutation in story["mutation"]]
    if len(set(ids)) != len(ids) or "base" in ids:
        fail("mutation ids must be unique and must not be `base`")
    for mutation in story["mutation"]:
        unknown = sorted(set(mutation) - EDIT_KEYS)
        if unknown:
            fail(f"edit {mutation['id']}: story.toml may not set {unknown}; an edit's misunderstanding is its "
                 f"mutation's in plus/kink/mutations/{TOPIC}.toml, and the tests that catch it are its killers "
                 f"in the recorded output {RUN}")
        missing = sorted(EDIT_KEYS - set(mutation))
        if missing:
            fail(f"edit {mutation['id']}: story.toml does not set {missing}")
    return story


def misunderstandings(story: dict) -> dict[str, str]:
    """Each story edit's misunderstanding, from its mutation in `mutations/<TOPIC>.toml`.

    The mutations directory must hold that one topic file (kink reads every `<topic>.toml` there,
    and the scenes know no other edit), whose mutations are story.toml's edits in its order,
    every edit of each anchored by the story edit's `rule`.
    """

    topics = sorted(path.name for path in MUTATIONS.iterdir() if path.is_file() and path.name.endswith(".toml")
                    and not path.name.startswith(".")) if MUTATIONS.is_dir() else []
    if topics != [f"{TOPIC}.toml"]:
        fail(f"plus/kink/mutations must hold exactly {TOPIC}.toml, the story's edits; it holds {topics}")
    mutations = tomllib.loads((MUTATIONS / f"{TOPIC}.toml").read_text(encoding="utf-8")).get("mutation", [])
    listed = [mutation.get("id") for mutation in mutations]
    ids = [mutation["id"] for mutation in story["mutation"]]
    if listed != ids:
        fail(f"plus/kink/mutations/{TOPIC}.toml lists the mutations {listed}; story.toml lists the edits {ids}, "
             "and both must list the same, in the same order")
    found = {}
    for edit, mutation in zip(story["mutation"], mutations):
        prose = mutation.get("misunderstanding", mutation.get("note"))
        if not isinstance(prose, str) or not prose:
            fail(f"mutation {TOPIC}/{edit['id']} has no misunderstanding")
        anchors = [part.get("rule") for part in mutation.get("edit", [])]
        if not anchors or any(anchor != edit["rule"] for anchor in anchors):
            fail(f"mutation {TOPIC}/{edit['id']} anchors its edits by {anchors}; story.toml's edit is of "
                 f"{edit['rule']!r}, and every edit of the mutation must be anchored by `rule = {edit['rule']!r}`")
        found[edit["id"]] = prose
    return found


def cases(story: dict) -> dict[str, str]:
    """Each story test's case file, relative to the specification's package (`kink/<file>`)."""

    manifest = tomllib.loads((CORPUS / "FLOW.toml").read_text(encoding="utf-8"))
    files = {program["id"]: program.get("file") for program in manifest.get("program", [])}
    tests = [test["id"] for test in story["test"]]
    missing = [test for test in tests if not files.get(test)]
    if missing:
        fail(f"tests {missing} have no case file in plus/kink/FLOW.toml")
    extra = sorted(set(files) - set(tests))
    if extra:
        fail(f"plus/kink/FLOW.toml has cases {extra} that story.toml has no test for")
    if list(files) != tests:
        fail(f"plus/kink/FLOW.toml lists its cases as {list(files)}; story.toml lists the tests as {tests}, "
             "the order the AI writes them, and FLOW.toml must list them in that order")
    for test in tests:
        if not (CORPUS / files[test]).is_file():
            fail(f"test {test}: its case plus/kink/{files[test]} does not exist")
    return {test: f"kink/{files[test]}" for test in tests}


def tracked(directory: Path) -> list[Path]:
    """The files git tracks under `directory`, which may not exist."""

    if not directory.is_dir():
        return []
    listed = subprocess.run(["git", "ls-files", "-z", "--", "."], cwd=directory, capture_output=True, check=True).stdout
    return [directory / name for name in listed.decode("utf-8").split("\0") if name and (directory / name).is_file()]


def variants(story: dict) -> list[tuple[str, str, str]]:
    """(variant, fixture relative to docs-site, package) for the specification and each mutant."""

    return [("base", "story/plus", "story-plus")] + [
        (m["id"], f"story/mutants/{m['id']}", f"story-plus-mutant-{m['id']}") for m in story["mutation"]
    ]


def mutant_files(mutation: dict, corpus: dict[str, str]) -> dict[Path, str]:
    root = STORY / "mutants" / mutation["id"]
    source = (BASE / "src" / "lib.rs").read_text(encoding="utf-8")
    if source.count(mutation["old"]) != 1:
        fail(f"edit {mutation['id']}: `old` must occur exactly once in plus/src/lib.rs")
    _, rest = source.replace(mutation["old"], mutation["new"]).split("\n", 1)
    header = (
        f"//! Edit {mutation['id'].upper()} of the introduction's specification ({mutation['label']}), "
        "generated from ../../plus by scripts/sync-story.py. Do not edit."
    )
    manifest = (BASE / "Cargo.toml").read_text(encoding="utf-8")
    renamed = manifest.replace('name = "story-plus"', f'name = "story-plus-mutant-{mutation["id"]}"')
    renamed = renamed.replace('path = "../../../krs/', 'path = "../../../../krs/')
    if renamed.count("story-plus-mutant") != 1 or renamed.count("../../../../krs/") != 1:
        fail("plus/Cargo.toml no longer has the package name and krs path the generator rewrites")
    files = {root / "src" / "lib.rs": f"{header}\n{rest}", root / "Cargo.toml": renamed}
    for case in corpus.values():
        files[root / case] = (BASE / case).read_text(encoding="utf-8")
    return files


def manifest_block(story: dict, corpus: dict[str, str]) -> str:
    lines = [START, "# Generated by scripts/sync-story.py from story/story.toml; edit that file instead."]

    def entry(identifier: str, fixture: str, package: str, args: list[str], show: str | None = None,
              select: str | None = None) -> None:
        lines.extend(["", "[[output]]", f"id = {json.dumps(identifier)}", f"fixture = {json.dumps(fixture)}",
                      f"package = {json.dumps(package)}", 'definition = "main"', f"args = {json.dumps(args)}"])
        if show:
            lines.append(f"show = {json.dumps(show)}")
        if select:
            lines.append(f"select = {json.dumps(select)}")

    entry("story-check", "story/plus", "story-plus", ["check"])
    entry("story-parse", "story/plus", "story-plus", ["parse", corpus["t3"]])
    entry("story-search", "story/plus", "story-plus", ["search", corpus["t3"]])
    entry("story-emit-k", "story/plus", "story-plus", ["emit-k", "--output", "target/krs-k"], "target/krs-k/definition.k")
    # Each edited copy's K, which must be the base K with the edit's mutation applied.
    for variant, fixture, package in variants(story)[1:]:
        entry(f"story-emit-k-{variant}", fixture, package, ["emit-k", "--output", "target/krs-k"],
              "target/krs-k/definition.k")
    entry("story-prove", "story", "story-plus-claims", ["prove", "--dependency", "story-plus:main", "--claim", "add-one"])
    # --locked: recording must not write into its fixture, so a stale kink/definition.k is
    # recorded as refused (and fails this script) instead of being rewritten by the recording.
    entry(VERDICTS, "story/plus", "story-plus", ["kink", "results", "--output", "verdicts", "--locked"])
    # The check document's mutations, which give each edit's Rust location; the rest of the
    # document names k-rust's build, which is no function of the fixture.
    entry(CHECK, "story/plus", "story-plus", ["kink", "check", "--locked"], select="mutations")
    # --full: every program runs on every mutant, so killed_by names every test that catches an
    # edit, independently of the order the programs ran in (a first-kill run names none).
    entry(RUN, "story/plus", "story-plus", ["kink", "run", "--full", "--output", "verdicts", "--locked"])
    for variant, fixture, package in variants(story):
        for test in story["test"]:
            entry(f"story-{variant}-{test['id']}", fixture, package, ["run", corpus[test["id"]]])
    lines.extend(["", END])
    return "\n".join(lines)


def output_ids(story: dict) -> list[str]:
    tools = ["story-check", "story-parse", "story-search", "story-emit-k", "story-prove"]
    return tools + [f"story-{v}-{t['id']}" for v, _, _ in variants(story) for t in story["test"]]


def rule_names() -> list[str]:
    """The scenes' `ruleNames` (data.ts): every rule the scenes can show, in their order."""

    found = re.search(r"export const ruleNames: readonly RuleName\[\] = \[([^\]]*)\]", DATA.read_text(encoding="utf-8"))
    if not found:
        fail(f"{DATA.relative_to(SITE)} no longer declares `export const ruleNames: readonly RuleName[] = [...]`")
    return re.findall(r"'([^']+)'", found.group(1))


def recorded_verdicts(identifier: str, verb: str) -> dict:
    """The recorded `krs kink <verb> --output verdicts` of `identifier`, with an admitted spec."""

    path = OUTPUTS / f"{identifier}.txt"
    if not path.is_file():
        fail(f"no recorded output {identifier}; run python3 scripts/record-outputs.py --write")
    command, _, rendering = path.read_text(encoding="utf-8").partition("\n")
    exits = [line for line in rendering.splitlines() if line.startswith("exit status ")]
    if exits:
        fail(f"recorded output {identifier}: krs kink {verb} ended with {exits[-1]}; it reads:\n{rendering}")
    words = command.split()
    if words[:3] != ["$", "krs", "kink"] or verb not in words:
        fail(f"recorded output {identifier} does not start with its `$ krs kink ... {verb}` line")
    try:
        verdicts = tomllib.loads(rendering)
    except tomllib.TOMLDecodeError as error:
        fail(f"recorded output {identifier} is not a verdicts rendering ({error}); it reads:\n{rendering}")
    if verdicts.get("schema") != "kink-flow-verdicts" or verdicts.get("document") != verb:
        fail(f"recorded output {identifier} is not the verdicts rendering of a {verb} document")
    spec = verdicts.get("spec", {})
    if spec.get("outcome") != "admitted":
        fail(f"recorded output {identifier}: the specification is {spec.get('outcome')} "
             f"(stage {spec.get('stage')}, reason {spec.get('reason')})")
    return verdicts


def fired_rules(story: dict) -> dict[str, list[str]]:
    """Each story test's rules: its case's `fired` in the recorded verdicts, in `ruleNames` order."""

    verdicts = recorded_verdicts(VERDICTS, "results")
    recorded = {case["id"]: case for case in verdicts.get("case", [])}
    tests = [test["id"] for test in story["test"]]
    extra = sorted(set(recorded) - set(tests))
    if extra:
        fail(f"recorded output {VERDICTS} has cases {extra} that story.toml has no test for")
    known = rule_names()
    rules = {}
    for test in tests:
        case = recorded.get(test)
        if case is None:
            fail(f"test {test} has no case in the recorded output {VERDICTS}")
        if case.get("class") != "comparable":
            fail(f"test {test}: its case is {case.get('class')}, not comparable, in {VERDICTS}")
        fired = case.get("fired")
        if not isinstance(fired, list):
            fail(f"test {test}: its case in {VERDICTS} has no `fired` list")
        # The story is one package, so each rule is an item of it, `crate::` and its path; the
        # scenes name it by that path.
        paths = [name.removeprefix("crate::") if name.startswith("crate::") else None for name in fired]
        unknown = [name for name, path in zip(fired, paths) if path not in known]
        if unknown:
            fail(f"test {test} fires {unknown}, which are not `crate::` and one of the scenes' "
                 f"ruleNames ({DATA.name})")
        rules[test] = [name for name in known if name in paths]
    return rules


def killers(story: dict) -> dict[str, list[str]]:
    """Each story edit's catching tests: its mutation's `killed_by` in the recorded full run.

    A full run judges every test on every mutation, so `killed_by` is every test whose result
    kink proves differs, in corpus order (story.toml's test order); a survived mutation has none.
    Any other status decides nothing about the edit and fails, naming it.
    """

    verdicts = recorded_verdicts(RUN, "run")
    if verdicts.get("schedule") != "full":
        fail(f"recorded output {RUN} is a {verdicts.get('schedule')} run; the story needs `--full`, "
             "which names every test that catches an edit")
    listing = verdicts.get("mutation_list", {"outcome": "ok"})
    if listing.get("outcome") != "ok":
        fail(f"recorded output {RUN}: the mutation list is {listing.get('outcome')}")
    if "stopped" in verdicts:
        stopped = verdicts["stopped"]
        fail(f"recorded output {RUN}: the run stopped at {stopped.get('mutation')} ({stopped.get('reason')})")
    tests = [test["id"] for test in story["test"]]
    rows = verdicts.get("mutation", [])
    qualified = [f"{TOPIC}/{mutation['id']}" for mutation in story["mutation"]]
    if [row.get("id") for row in rows] != qualified:
        fail(f"recorded output {RUN} judges the mutations {[row.get('id') for row in rows]}; "
             f"the story's edits are {qualified}")
    found = {}
    for mutation, row in zip(story["mutation"], rows):
        status = row.get("status")
        if status == "survived":
            found[mutation["id"]] = []
            continue
        if status != "killed":
            fail(f"edit {mutation['id']}: its mutation {row['id']} is {status} in {RUN}, neither killed nor survived")
        caught = row.get("killed_by")
        if not isinstance(caught, list) or not caught:
            fail(f"edit {mutation['id']}: its mutation {row['id']} is killed with no `killed_by` in {RUN}")
        unknown = [test for test in caught if test not in tests]
        if unknown:
            fail(f"edit {mutation['id']} is killed by {unknown}, which story.toml has no test for")
        found[mutation["id"]] = [test for test in tests if test in caught]
    return found


def rust_locations(story: dict) -> dict[str, str]:
    """Each story edit's Rust location, `<file>:<line>`: the first Rust range of its mutation's
    first edit in the recorded `krs kink check` (`story-kink-check`)."""

    path = OUTPUTS / f"{CHECK}.txt"
    if not path.is_file():
        fail(f"no recorded output {CHECK}; run python3 scripts/record-outputs.py --write")
    command, _, recorded = path.read_text(encoding="utf-8").partition("\n")
    words = command.split()
    if words[:3] != ["$", "krs", "kink"] or "check" not in words or "exit status" in recorded:
        fail(f"recorded output {CHECK} is not a krs kink check that exited 0; it reads:\n{recorded}")
    try:
        rows = json.loads(recorded)
    except json.JSONDecodeError as error:
        fail(f"recorded output {CHECK} is not the check document's mutations ({error})")
    by_id = {row.get("id"): row for row in rows} if isinstance(rows, list) else {}
    found = {}
    for mutation in story["mutation"]:
        qualified = f"{TOPIC}/{mutation['id']}"
        row = by_id.get(qualified)
        if row is None:
            fail(f"edit {mutation['id']}: recorded output {CHECK} has no mutation {qualified}")
        edits = (row.get("krs") or {}).get("edits") or []
        ranges = edits[0].get("rust") if edits else None
        if not ranges or "file" not in ranges[0] or "line" not in ranges[0]:
            fail(f"edit {mutation['id']}: its mutation {qualified} has no Rust location in {CHECK}")
        found[mutation["id"]] = f"{ranges[0]['file']}:{ranges[0]['line']}"
    return found


def check_guide() -> None:
    """The guide's corpus is the story's, in its order, plus one case the guide adds."""

    story = tomllib.loads((CORPUS / "FLOW.toml").read_text(encoding="utf-8")).get("program", [])
    guide = tomllib.loads((GUIDE / "FLOW.toml").read_text(encoding="utf-8")).get("program", [])
    expected = [program["id"] for program in story] + [GUIDE_CASE]
    if [program.get("id") for program in guide] != expected:
        fail(f"plus/guide/FLOW.toml lists the cases {[program.get('id') for program in guide]}; "
             f"the guide's corpus is plus/kink/FLOW.toml's cases, in order, then {GUIDE_CASE}: {expected}")
    files = {program["id"]: program.get("file") for program in guide}
    for case, file in files.items():
        if not isinstance(file, str):
            fail(f"case {case}: plus/guide/FLOW.toml gives it no `file`")
    for program in story:
        shared = GUIDE / files[program["id"]]
        original = CORPUS / program["file"]
        if not shared.is_file() or shared.read_bytes() != original.read_bytes():
            fail(f"case {program['id']}: plus/guide/{files[program['id']]} must be a copy of plus/kink/{program['file']}")
    if not (GUIDE / files[GUIDE_CASE]).is_file():
        fail(f"case {GUIDE_CASE}: plus/guide/{files[GUIDE_CASE]} does not exist")


def generated_data(story: dict, corpus: dict[str, str], rules: dict[str, list[str]],
                   caught_by: dict[str, list[str]], why: dict[str, str], rust: dict[str, str]) -> str:
    ids = output_ids(story)
    tests = [
        {
            "id": test["id"],
            "program": (BASE / corpus[test["id"]]).read_text(encoding="utf-8").strip(),
            "rules": rules[test["id"]],
            "climb": test.get("climb", False),
        }
        for test in story["test"]
    ]
    mutations = [
        {key: mutation[key] for key in ("id", "rule", "label")}
        | {"why": why[mutation["id"]], "displayOld": mutation["display_old"],
           "displayNew": mutation["display_new"], "caughtBy": caught_by[mutation["id"]],
           "rust": rust[mutation["id"]]}
        for mutation in story["mutation"]
    ]
    imports = [f"import output{index} from '../snippets/outputs/{name}.txt?raw'" for index, name in enumerate(ids)]
    table = ",\n".join(f"  {json.dumps(name)}: output{index}" for index, name in enumerate(ids))
    return "\n".join([
        "// Generated by scripts/sync-story.py from story/story.toml, the cases and mutations of",
        f"// story/plus/kink/, and the recorded outputs {VERDICTS} (each test's rules),",
        f"// {RUN} (the tests that catch each edit) and {CHECK} (each edit's Rust",
        "// location). Do not edit.",
        *imports,
        "",
        f"export const storyTests = {json.dumps(tests, indent=2)} as const",
        "",
        f"export const storyMutations = {json.dumps(mutations, indent=2)} as const",
        "",
        "export const storyOutputs: Readonly<Record<string, string>> = {",
        table,
        "}",
        "",
    ])


def run_result(identifier: str) -> str:
    path = OUTPUTS / f"{identifier}.txt"
    if not path.is_file():
        fail(f"no recorded output {identifier}; run python3 scripts/record-outputs.py --write")
    lines = path.read_text(encoding="utf-8").splitlines()
    if "<k>" not in lines:
        fail(f"recorded output {identifier} has no <k> cell")
    return lines[lines.index("<k>") + 1].strip().removesuffix(" ~> .K")


def label_components(label: str) -> list[str]:
    """A K label's components, separated by `--` or `.`, as kink reads an anchor's."""

    return [part for chunk in label.split(".") for part in chunk.split("--")]


def patched(definition: str, mutation: dict) -> str:
    """`definition` with the K patch `mutation` applied, as kink resolves it for the story.

    Each edit is anchored by `rule` (a label or a whole-component suffix of one) and replaces the
    one occurrence of `find` in that rule's sentence, which KRS emits on one line. An edit of
    another form is not one the story writes, and fails.
    """

    lines = definition.split("\n")
    for edit in mutation.get("edit", []):
        if set(edit) != {"rule", "find", "replace"}:
            fail(f"mutation {TOPIC}/{mutation['id']}: an edit of the story is `rule`, `find` and `replace`; "
                 f"it has {sorted(edit)}")
        anchor = label_components(edit["rule"])
        held = []
        for index, line in enumerate(lines):
            found = re.search(r"\[label\(([^)]*)\)\]", line)
            if line.lstrip().startswith("rule ") and found:
                components = label_components(found.group(1))
                if components[-len(anchor):] == anchor:
                    held.append(index)
        if len(held) != 1:
            fail(f"mutation {TOPIC}/{mutation['id']}: `rule = {edit['rule']!r}` names {len(held)} one-line rules "
                 "of plus/kink/definition.k, not one")
        line = lines[held[0]]
        if line.count(edit["find"]) != 1:
            fail(f"mutation {TOPIC}/{mutation['id']}: {edit['find']!r} occurs {line.count(edit['find'])} times "
                 f"in its rule, not once: {line.strip()}")
        lines[held[0]] = line.replace(edit["find"], edit["replace"])
    return "\n".join(lines)


def emitted_k(identifier: str) -> str:
    """The `definition.k` the recorded `krs emit-k` output `identifier` shows."""

    path = OUTPUTS / f"{identifier}.txt"
    if not path.is_file():
        fail(f"no recorded output {identifier}; run python3 scripts/record-outputs.py --write")
    text = path.read_text(encoding="utf-8")
    marker = "\n$ cat target/krs-k/definition.k\n"
    if "exit status" in text.split(marker, 1)[0] or marker not in text:
        fail(f"recorded output {identifier} does not show an emitted definition.k; it reads:\n{text}")
    return text.split(marker, 1)[1]


def check_expectations(story: dict, caught_by: dict[str, list[str]]) -> None:
    proof = (OUTPUTS / "story-prove.txt").read_text(encoding="utf-8")
    if "NAT-CLAIMS-SPEC.add-one: proven" not in proof.splitlines() or "exit status" in proof:
        fail("the introduction's add-one claim must have a recorded proven result")
    # The scenes show each edit in its Rust form, and kink judges its K patch: the Rust edit must
    # emit exactly the K the patch writes. KRS names the package in the K's comments, and the
    # edited copy is another package.
    base = (CORPUS / "definition.k").read_text(encoding="utf-8")
    patches = {mutation.get("id"): mutation for mutation in
               tomllib.loads((MUTATIONS / f"{TOPIC}.toml").read_text(encoding="utf-8")).get("mutation", [])}
    for mutation in story["mutation"]:
        package = f"story-plus-mutant-{mutation['id']}"
        emitted = emitted_k(f"story-emit-k-{mutation['id']}").replace(package, "story-plus")
        expected = patched(base, patches[mutation["id"]])
        if emitted != expected:
            diff = "\n".join(difflib.unified_diff(expected.splitlines(), emitted.splitlines(),
                                                  f"plus/kink/definition.k with {TOPIC}/{mutation['id']}",
                                                  f"story/mutants/{mutation['id']}", lineterm=""))
            fail(f"edit {mutation['id']}: story/mutants/{mutation['id']} emits other K than its mutation "
                 f"{TOPIC}/{mutation['id']} writes; the Rust edit in story.toml and the K patch must be the same "
                 f"edit:\n{diff}")
    # The scenes show each cell's result from the Rust edit's package and mark it caught from
    # kink's verdict on the K patch; the two must agree on every test.
    for mutation in story["mutation"]:
        changed = [
            test["id"] for test in story["test"]
            if run_result(f"story-{mutation['id']}-{test['id']}") != run_result(f"story-base-{test['id']}")
        ]
        if changed != caught_by[mutation["id"]]:
            fail(f"edit {mutation['id']}: krs run of story/mutants/{mutation['id']} changes the result of {changed}, "
                 f"but kink kills its mutation {TOPIC}/{mutation['id']} with {caught_by[mutation['id']]} ({RUN}); "
                 "the Rust edit in story.toml and the K patch must be the same edit")


def sync(write: bool) -> None:
    story = load()
    corpus = cases(story)
    check_guide()
    expected: dict[Path, str] = {}
    for mutation in story["mutation"]:
        expected |= mutant_files(mutation, corpus)
    manifest = MANIFEST.read_text(encoding="utf-8")
    if manifest.count(START) != 1 or manifest.count(END) != 1:
        fail(f"{MANIFEST.name} must contain one {START} / {END} block")
    start, end = manifest.index(START), manifest.index(END) + len(END)
    expected[MANIFEST] = manifest[:start] + manifest_block(story, corpus) + manifest[end:]
    # The rules and the killers come from recorded outputs of the manifest block above, so
    # --write writes the rest first when an output is missing or does not decide them.
    why = misunderstandings(story)
    underived = None
    try:
        expected[GENERATED] = generated_data(story, corpus, fired_rules(story), killers(story), why,
                                             rust_locations(story))
    except Failure as failure:
        if not write:
            raise
        underived = failure

    workspace = tomllib.loads((STORY / "Cargo.toml").read_text(encoding="utf-8"))["workspace"]["members"]
    if workspace != ["plus"] + [f"mutants/{m['id']}" for m in story["mutation"]] + ["claims"]:
        fail("story/Cargo.toml must list plus, every mutants/<id> in story.toml order, and claims")
    generated_mutants = {path.name for path in (STORY / "mutants").iterdir()} if (STORY / "mutants").is_dir() else set()
    extra = sorted(generated_mutants - {m["id"] for m in story["mutation"]})
    if extra:
        fail(f"story/mutants has directories for no edit: {extra}")
    # A generated mutant's tracked files are exactly the files the generator writes (a case that
    # moved or left the corpus must not stay behind as a stale copy). Untracked files (an
    # editor's swap file, notes, build outputs) are not generated files and are left alone.
    leftover = sorted(path for path in tracked(STORY / "mutants") if path not in expected)

    stale = [path for path, text in expected.items() if not path.is_file() or path.read_text(encoding="utf-8") != text]
    if write:
        for path in stale:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected[path], encoding="utf-8")
            print(f"updated {path.relative_to(SITE)}")
        for path in leftover:
            path.unlink()
            print(f"removed {path.relative_to(SITE)}")
        for directory in sorted({path.parent for path in leftover}, key=lambda path: len(path.parts), reverse=True):
            while directory != STORY / "mutants" and directory.is_dir() and not any(directory.iterdir()):
                directory.rmdir()
                directory = directory.parent
        if underived:
            fail(f"src/generated/story.ts not written: {underived} "
                 "(after python3 scripts/record-outputs.py --write, run python3 scripts/sync-story.py --write again)")
        return
    if stale or leftover:
        names = ", ".join(str(path.relative_to(SITE)) for path in stale + leftover)
        fail(f"stale: {names}; run python3 scripts/sync-story.py --write")
    check_expectations(story, killers(story))
    print(f"PASS story: {len(story['mutation'])} edits, {len(story['test'])} tests, the data agree with krs")


def main() -> None:
    if sys.argv[1:] not in ([], ["--write"]):
        raise SystemExit("usage: sync-story.py [--write]")
    try:
        sync(sys.argv[1:] == ["--write"])
    except Failure as failure:
        raise SystemExit(f"story: {failure}") from None


if __name__ == "__main__":
    main()
