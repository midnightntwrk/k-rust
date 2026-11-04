#!/usr/bin/env python3
"""Generate the introduction's mutants and story data, and check them against krs.

`story/story.toml` lists the corpus and the edits the introduction makes to the `plus`
specification in `story/plus/`, whose corpus is `story/plus/kink/` (`FLOW.toml` and the cases
it names). `--write` generates `story/mutants/<id>/` (the specification with one edit and the
same cases), `src/generated/story.ts` (the data the scene components read), and the story
block of `recorded-outputs.toml`. Without an option, the script fails when any of them is
stale, or when an edit's `caught_by` differs from the results krs recorded for the corpus.

The rules each test fires are not written by hand: they are the `fired` lists of the recorded
`krs kink results --output verdicts` (`story-kink-results`), named by KRS item and put in the
order of the scenes' `ruleNames`. A story test with no case there, a case that is not
`comparable`, or a case or a fired rule the story does not know fails the script, naming it,
as does a FLOW.toml that lists its cases in another order than story.toml's tests.
`--write` needs that recorded output; on a fresh corpus run `record-outputs.py --write` after
it and then `--write` again.
"""

from __future__ import annotations

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
DATA = SITE / "src" / "components" / "story" / "data.ts"
VERDICTS = "story-kink-results"
OUTPUTS = SITE / "src" / "snippets" / "outputs"
MANIFEST = SITE / "recorded-outputs.toml"
GENERATED = SITE / "src" / "generated" / "story.ts"
START = "# [story:start]"
END = "# [story:end]"


class Failure(Exception):
    """A story check that failed; its message names what to fix."""


def fail(message: str) -> None:
    raise Failure(message)


def load() -> dict:
    story = tomllib.loads((STORY / "story.toml").read_text(encoding="utf-8"))
    ids = [mutation["id"] for mutation in story["mutation"]]
    if len(set(ids)) != len(ids) or "base" in ids:
        fail("mutation ids must be unique and must not be `base`")
    return story


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

    def entry(identifier: str, fixture: str, package: str, args: list[str], show: str | None = None) -> None:
        lines.extend(["", "[[output]]", f"id = {json.dumps(identifier)}", f"fixture = {json.dumps(fixture)}",
                      f"package = {json.dumps(package)}", 'definition = "main"', f"args = {json.dumps(args)}"])
        if show:
            lines.append(f"show = {json.dumps(show)}")

    entry("story-check", "story/plus", "story-plus", ["check"])
    entry("story-parse", "story/plus", "story-plus", ["parse", corpus["t3"]])
    entry("story-search", "story/plus", "story-plus", ["search", corpus["t3"]])
    entry("story-emit-k", "story/plus", "story-plus", ["emit-k", "--output", "target/krs-k"], "target/krs-k/definition.k")
    entry("story-prove", "story", "story-plus-claims", ["prove", "--dependency", "story-plus:main", "--claim", "add-one"])
    # --locked: recording must not write into its fixture, so a stale kink/definition.k is
    # recorded as refused (and fails this script) instead of being rewritten by the recording.
    entry(VERDICTS, "story/plus", "story-plus", ["kink", "results", "--output", "verdicts", "--locked"])
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


def fired_rules(story: dict) -> dict[str, list[str]]:
    """Each story test's rules: its case's `fired` in the recorded verdicts, in `ruleNames` order."""

    path = OUTPUTS / f"{VERDICTS}.txt"
    if not path.is_file():
        fail(f"no recorded output {VERDICTS}; run python3 scripts/record-outputs.py --write")
    command, _, rendering = path.read_text(encoding="utf-8").partition("\n")
    exits = [line for line in rendering.splitlines() if line.startswith("exit status ")]
    if exits:
        fail(f"recorded output {VERDICTS}: krs kink results ended with {exits[-1]}; it reads:\n{rendering}")
    words = command.split()
    if words[:3] != ["$", "krs", "kink"] or "results" not in words:
        fail(f"recorded output {VERDICTS} does not start with its `$ krs kink ... results` line")
    try:
        verdicts = tomllib.loads(rendering)
    except tomllib.TOMLDecodeError as error:
        fail(f"recorded output {VERDICTS} is not a verdicts rendering ({error}); it reads:\n{rendering}")
    if verdicts.get("schema") != "kink-flow-verdicts" or verdicts.get("document") != "results":
        fail(f"recorded output {VERDICTS} is not the verdicts rendering of a results document")
    spec = verdicts.get("spec", {})
    if spec.get("outcome") != "admitted":
        fail(f"recorded output {VERDICTS}: the specification is {spec.get('outcome')} "
             f"(stage {spec.get('stage')}, reason {spec.get('reason')})")
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
        unknown = [name for name in fired if name not in known]
        if unknown:
            fail(f"test {test} fires {unknown}, which the scenes' ruleNames ({DATA.name}) do not list")
        rules[test] = [name for name in known if name in fired]
    return rules


def generated_data(story: dict, corpus: dict[str, str], rules: dict[str, list[str]]) -> str:
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
        {key: mutation[key] for key in ("id", "rule", "label", "why")}
        | {"displayOld": mutation["display_old"], "displayNew": mutation["display_new"]}
        for mutation in story["mutation"]
    ]
    imports = [f"import output{index} from '../snippets/outputs/{name}.txt?raw'" for index, name in enumerate(ids)]
    table = ",\n".join(f"  {json.dumps(name)}: output{index}" for index, name in enumerate(ids))
    return "\n".join([
        "// Generated by scripts/sync-story.py from story/story.toml, the cases of story/plus/kink/ and",
        f"// the recorded output {VERDICTS} (each test's rules). Do not edit.",
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


def check_expectations(story: dict) -> None:
    proof = (OUTPUTS / "story-prove.txt").read_text(encoding="utf-8")
    if "NAT-CLAIMS-SPEC.add-one: proven" not in proof.splitlines() or "exit status" in proof:
        fail("the introduction's add-one claim must have a recorded proven result")
    for mutation in story["mutation"]:
        caught = [
            test["id"] for test in story["test"]
            if run_result(f"story-{mutation['id']}-{test['id']}") != run_result(f"story-base-{test['id']}")
        ]
        if caught != mutation["caught_by"]:
            fail(f"edit {mutation['id']} is caught by {caught}, but story.toml says {mutation['caught_by']}")


def sync(write: bool) -> None:
    story = load()
    corpus = cases(story)
    expected: dict[Path, str] = {}
    for mutation in story["mutation"]:
        expected |= mutant_files(mutation, corpus)
    manifest = MANIFEST.read_text(encoding="utf-8")
    if manifest.count(START) != 1 or manifest.count(END) != 1:
        fail(f"{MANIFEST.name} must contain one {START} / {END} block")
    start, end = manifest.index(START), manifest.index(END) + len(END)
    expected[MANIFEST] = manifest[:start] + manifest_block(story, corpus) + manifest[end:]
    # The rules come from a recorded output of the manifest block above, so --write writes the
    # rest first when that output is missing or does not decide them.
    underived = None
    try:
        expected[GENERATED] = generated_data(story, corpus, fired_rules(story))
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
    check_expectations(story)
    print(f"PASS story: {len(story['mutation'])} edits, {len(story['test'])} tests, expectations match krs")


def main() -> None:
    if sys.argv[1:] not in ([], ["--write"]):
        raise SystemExit("usage: sync-story.py [--write]")
    try:
        sync(sys.argv[1:] == ["--write"])
    except Failure as failure:
        raise SystemExit(f"story: {failure}") from None


if __name__ == "__main__":
    main()
