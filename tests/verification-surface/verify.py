#!/usr/bin/env python3
"""Verification-surface feature gate: existentials and ensures on rules (KF-040).

The fixture packages are K tutorial lesson 1.21 in both layers:

- `l21`: reference `#[k::rule]` fns. `zero_to_unknown` (`cells!` form)
  rewrites `0` to a fresh `?X` with `ensures ?X =/=Int 0`; `big_to_five`
  rewrites an integer of at least 10 to `5`; `foo_bounded` (term fn form)
  rewrites `foo` to `?X` with `ensures ?X <Int 5`; the claim
  `zero-reaches-nonzero` says every path from `0` reaches some `?Y =/=Int 0`.
- `l21-readable`: the two lesson rules as readable `k::rules!` clauses, whose
  `#[k::exists]` and `#[k::ensures]` helpers `krs expand` keeps verbatim
  before `#[k::rule(..)]`.

Each package is checked, expanded, and emitted with pinned digests; the
emitted `.k` must contain the lesson's rules and a
`// krs-capability: RuleExistential` comment per rule, and `symbols.json`
records the requirements. Programs are then executed symbolically on both
routes: native `krs search` (k-rust with Z3) and Java `krun` on a
`kompile --backend haskell` definition. Each result is normalized to its
final states, a state being the computation cell and its path constraints,
compared up to a bijective renaming of the variables the rules introduced.
Single-variable Int comparisons are summarized as the set of integers each
variable may take, because the engines keep different implied constraints
(k-rust drops `?X =/=Int 0` once `?X >=Int 10` holds; Java keeps it). Program
`0` reaches `<k> ?X </k>` with ?X in [-inf, 9] minus {0} and `<k> 5 </k>`
with ?X in [10, +inf]; `foo` also reaches `?X` below 5 and, through `0`, the
two lesson states.

The claim is not proven on either route: the start `0` already unifies with
the target `?Y`, and K's reachability check stops at such a state when the
ensures condition fails there (Java: WarnStuckClaimState). Both routes report
the claim stuck at depth 0 on `<k> 0 ~> Tail </k>`, which is pinned.

Concrete execution refuses the rules: `krs build --backend llvm` stops with
`krs::capability::unavailable`, Java `kompile --backend llvm` reports "Found
existential variable not supported by concrete backend", and an LLVM build
of a transition with `ensures` alone warns `krs::capability::ignored-ensures`.
Negative fixtures pin the diagnostics for an existential on an equation, an
unused existential, an existential in `requires`, and one that shadows a
subject binding.

Run it from the repository root; `--record` rewrites the measured pins after
every step passes, and `--refresh-reference` reruns Java K instead of
replaying the per-user reference cache.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import itertools
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry  # noqa: E402
from support.fixture_gate import Emitted, Fixture, FixtureGate, diagnostic_lines  # noqa: E402
from support.krs import build  # noqa: E402
from support import krs_gate  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import Key, Pin, Snapshot, add_refresh_argument  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"
FIXTURES = HERE / "fixtures"
JAVA_TOOLS = ("kompile", "krun", "kprove")

L21 = Fixture(MANIFEST, "krs-verification-surface-l21")
L21_READABLE = Fixture(MANIFEST, "krs-verification-surface-l21-readable")
PROGRAMS = {
    L21.package: {"zero": "0", "foo": "foo"},
    L21_READABLE.package: {"zero": "0"},
}
EMITTED_RULES = {
    L21.package: (
        "  // krs-capability: RuleExistential zero-to-unknown\n"
        "  rule [zero-to-unknown]:\n"
        "    <k> 0 ~> Tail:K => ?X:Int ~> Tail:K </k>\n"
        "    ensures ?X:Int =/=Int 0\n",
        "  rule [big-to-five]:\n"
        "    <k> X:Int ~> Tail:K => 5 ~> Tail:K </k>\n"
        "    requires X:Int >=Int 10\n",
        "  // krs-capability: RuleExistential foo-bounded\n"
        "  rule foo => ?X:Int\n"
        "    ensures ?X:Int <Int 5 [label(foo-bounded)]\n",
    ),
    L21_READABLE.package: (
        "  // krs-capability: RuleExistential zero-to-unknown\n"
        "  rule [zero-to-unknown]:\n"
        "    <k> 0 => ?X:Int ... </k>\n"
        "    ensures ?X:Int =/=Int 0\n",
        "  rule [big-to-five]:\n"
        "    <k> N:Int => 5 ... </k>\n"
        "    requires N:Int >=Int 10\n",
    ),
}
REQUIREMENTS = {
    L21.package: [["RuleExistential", "foo-bounded"], ["RuleExistential", "zero-to-unknown"]],
    L21_READABLE.package: [["RuleExistential", "zero-to-unknown"]],
}
READABLE_HELPERS = (
    "#[k::exists(x:Int)]\n#[k::ensures(int::ne(x, 0))]\n"
    '#[k::rule(nondet = lesson, label = "zero-to-unknown")]\n'
)
CLAIM_SPEC_MODULE = "KRS-LESSON-21-SPEC"
CLAIM_LABEL = "zero-reaches-nonzero"
JAVA_LLVM_REJECTION = "[Error] Compiler: Found existential variable not supported by concrete backend."

NEGATIVE = (
    "exists-equation",
    "exists-unused",
    "exists-in-requires",
    "exists-shadows",
)


# --- KAST normalization -------------------------------------------------------


@dataclass(frozen=True)
class Node:
    """One KAST term: an application (`arguments` is a tuple) or a variable or token."""

    label: str
    arguments: tuple["Node", ...] | None = None


class KastParser:
    """A recursive-descent reader of the one-line KAST text `krun`/`krs` print."""

    def __init__(self, text: str) -> None:
        self.text = text
        self.position = 0

    def parse(self) -> Node:
        node = self.term()
        if self.position != len(self.text):
            raise GateError(f"trailing KAST text at {self.position}: {self.text[self.position:][:80]!r}")
        return node

    def term(self) -> Node:
        text = self.text
        if text.startswith("#token(", self.position):
            self.position += len("#token(")
            value = self.string()
            self.expect(",")
            sort = self.string()
            self.expect(")")
            return Node(f"#token({value},{sort})")
        if text[self.position] == "`":
            end = text.index("`", self.position + 1)
            label = text[self.position + 1:end]
            self.position = end + 1
        else:
            start = self.position
            while self.position < len(text) and text[self.position] not in "(){},":
                self.position += 1
            label = text[start:self.position]
        if self.position < len(text) and text[self.position] == "{":
            # Sort parameters are dropped: both routes print them differently.
            depth = 0
            while True:
                character = text[self.position]
                self.position += 1
                depth += {"{": 1, "}": -1}.get(character, 0)
                if depth == 0:
                    break
        if self.position < len(text) and text[self.position] == "(":
            self.position += 1
            arguments = []
            if text[self.position] != ")":
                while True:
                    arguments.append(self.term())
                    if text[self.position] == ",":
                        self.position += 1
                        continue
                    break
            self.expect(")")
            return Node(label, tuple(arguments))
        return Node(label)

    def string(self) -> str:
        match = re.compile(r'"(?:[^"\\]|\\.)*"').match(self.text, self.position)
        if match is None:
            raise GateError(f"expected a KAST string at {self.position}")
        self.position = match.end()
        return match.group(0)

    def expect(self, token: str) -> None:
        if not self.text.startswith(token, self.position):
            raise GateError(f"expected {token!r} at {self.position}: {self.text[self.position:][:80]!r}")
        self.position += len(token)


def flatten(node: Node, label: str) -> list[Node]:
    if node.label == label and node.arguments is not None:
        return [leaf for argument in node.arguments for leaf in flatten(argument, label)]
    return [node]


def variables(node: Node, output: list[str]) -> None:
    if node.arguments is None:
        if not node.label.startswith("#token(") and node.label not in output:
            output.append(node.label)
        return
    for argument in node.arguments:
        variables(argument, output)


def render(node: Node, names: dict[str, str]) -> str:
    if node.arguments is None:
        return names.get(node.label, node.label)
    if node.label == "#Not" and node.arguments:
        return f"not({render(node.arguments[0], names)})"
    if node.label == "#Equals" and len(node.arguments) == 2:
        left, right = (render(argument, names) for argument in node.arguments)
        # `{ true #Equals P }` is the constraint `P`.
        if left == '#token("true","Bool")':
            return right
        return f"{left} == {right}"
    return f"{node.label}({', '.join(render(argument, names) for argument in node.arguments)})"


def k_cell(node: Node) -> Node:
    if node.label == "<k>" and node.arguments is not None and len(node.arguments) == 1:
        return node.arguments[0]
    for argument in node.arguments or ():
        found = k_cell(argument)
        if found is not None:
            return found
    return None  # type: ignore[return-value]


INT_COMPARISONS = {
    "_>=Int_": (">=", False), "_>Int_": (">", False), "_<=Int_": ("<=", False), "_<Int_": ("<", False),
    "_==Int_": ("==", False), "_=/=Int_": ("!=", False),
}
NEGATED = {">=": "<", ">": "<=", "<=": ">", "<": ">=", "==": "!=", "!=": "=="}
MIRRORED = {">=": "<=", ">": "<", "<=": ">=", "<": ">", "==": "==", "!=": "!="}


def int_token(node: Node) -> int | None:
    match = re.fullmatch(r'#token\("(-?\d+)","Int"\)', node.label) if node.arguments is None else None
    return int(match.group(1)) if match else None


def comparison(node: Node) -> tuple[str, str, int] | None:
    """`(variable, operator, literal)` for a single-variable Int comparison, else `None`."""

    negated = False
    while node.label == "#Not" and node.arguments and len(node.arguments) == 1:
        negated = not negated
        node = node.arguments[0]
    if node.label == "#Equals" and node.arguments and len(node.arguments) == 2:
        left, right = node.arguments
        if left.label == '#token("true","Bool")':
            node = right
        elif right.label == '#token("true","Bool")':
            node = left
        else:
            node = Node("_==Int_", (left, right))
    if node.label not in INT_COMPARISONS or not node.arguments or len(node.arguments) != 2:
        return None
    operator = INT_COMPARISONS[node.label][0]
    left, right = node.arguments
    if left.arguments is None and int_token(left) is None and int_token(right) is not None:
        variable, value = left.label, int_token(right)
    elif right.arguments is None and int_token(right) is None and int_token(left) is not None:
        variable, value, operator = right.label, int_token(left), MIRRORED[operator]
    else:
        return None
    assert value is not None
    return variable, NEGATED[operator] if negated else operator, value


def domains(constraints: list[Node]) -> tuple[dict[str, list], list[Node]]:
    """The integer set each variable may take, from its single-variable comparisons.

    Comparing these sets instead of the constraint lists makes the result
    independent of which implied constraints an engine keeps.
    """

    bounds: dict[str, list] = {}
    rest = []
    for constraint in constraints:
        parsed = comparison(constraint)
        if parsed is None:
            rest.append(constraint)
            continue
        variable, operator, value = parsed
        low, high, excluded = bounds.setdefault(variable, [None, None, set()])
        if operator in (">=", ">", "=="):
            floor = value + (operator == ">")
            low = floor if low is None else max(low, floor)
        if operator in ("<=", "<", "=="):
            ceiling = value - (operator == "<")
            high = ceiling if high is None else min(high, ceiling)
        if operator == "!=":
            excluded.add(value)
        bounds[variable] = [low, high, excluded]
    for variable, (low, high, excluded) in bounds.items():
        excluded = sorted(
            point for point in excluded
            if (low is None or point >= low) and (high is None or point <= high)
        )
        bounds[variable] = [low, high, excluded]
    return bounds, rest


def render_domain(variable: str, domain: list) -> str:
    low, high, excluded = domain
    if low is not None and high is not None and low > high:
        return f"{variable} in {{}}"
    if low is not None and low == high:
        return f"{variable} == {low}"
    text = f"{variable} in [{'-inf' if low is None else low}, {'+inf' if high is None else high}]"
    return text + (f" minus {{{', '.join(map(str, excluded))}}}" if excluded else "")


def normalized_states(kast: str) -> list[dict[str, Any]]:
    """The final states of a KAST disjunction: the computation cell and the
    path constraints, canonical up to a bijective renaming of the variables
    the rules introduced, with single-variable Int comparisons summarized as
    the set of integers each variable may take."""

    states = []
    for disjunct in flatten(KastParser(kast.strip()).parse(), "#Or"):
        configuration = None
        constraints = []
        for conjunct in flatten(disjunct, "#And"):
            if conjunct.label == "<generatedTop>":
                configuration = conjunct
            elif conjunct.label != "#Top":
                constraints.append(conjunct)
        if configuration is None:
            raise GateError(f"a final state has no configuration: {kast[:200]!r}")
        k = k_cell(configuration)
        if k is None:
            raise GateError(f"a final state has no <k> cell: {kast[:200]!r}")
        found: list[str] = []
        variables(k, found)
        for constraint in constraints:
            variables(constraint, found)
        bounds, rest = domains(constraints)
        best = None
        for order in itertools.permutations(found):
            names = {name: f"?V{index}" for index, name in enumerate(order)}
            rendered = sorted(
                [render_domain(names.get(variable, variable), domain) for variable, domain in bounds.items()]
                + [render(constraint, names) for constraint in rest]
            )
            candidate = (render(k, names), rendered)
            if best is None or candidate < best:
                best = candidate
        assert best is not None
        states.append({"k": best[0], "constraints": best[1]})
    return sorted(states, key=lambda state: json.dumps(state, sort_keys=True))


# --- routes -------------------------------------------------------------------


def native_states(harness: FixtureGate, fixture: Fixture, program: Path) -> list[dict[str, Any]]:
    stdout = harness.run_command(fixture, "search", "--output", "kast", program)
    solutions = [
        line for line in stdout.splitlines()
        if line and not line.startswith(("solution ", "krs search:"))
    ]
    if not solutions:
        raise GateError(f"{fixture.package}: native search printed no solution:\n{stdout}")
    states = []
    for solution in solutions:
        states.extend(normalized_states(solution))
    return sorted(states, key=lambda state: json.dumps(state, sort_keys=True))


def native_claim(harness: FixtureGate, fixture: Fixture) -> dict[str, Any]:
    process = harness._krs(fixture, "prove", "--claim", CLAIM_LABEL, check=False)
    text = process.stdout
    status = re.search(rf"{re.escape(CLAIM_SPEC_MODULE)}\.{re.escape(CLAIM_LABEL)}: (\w+)", text)
    leaf = re.search(r"leaf 1 \((\w+), depth (\d+)\):\s*<k>\s*(.*?)\s*</k>", text, re.DOTALL)
    if status is None or leaf is None:
        raise GateError(f"{fixture.package}: krs prove printed no claim status and leaf:\n{text}\n{process.stderr}")
    return {
        "proven": status.group(1) == "proven",
        "stuck": leaf.group(1) == "Stuck",
        "depth": int(leaf.group(2)),
        "k": normalize_k_text(leaf.group(3)),
    }


def normalize_k_text(text: str) -> str:
    text = re.sub(r":[A-Z][A-Za-z]*", "", " ".join(text.split()))
    return re.sub(r" ~> \.K$", "", text)


def java_route(
    harness: FixtureGate, emitted: Emitted, programs: dict[str, Path], *, claim: bool,
) -> tuple[dict[str, list[dict[str, Any]]], dict[str, Any] | None, str]:
    inputs = {f"emitted/{emitted.fixture.package}/definition.k": emitted.source}
    k = Snapshot(
        f"verification-surface/{emitted.fixture.package}",
        Key(tools=JAVA_TOOLS, inputs=inputs),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, emitted.fixture.package),
    )
    kompiled = harness.workspace / "kompiled" / emitted.fixture.package
    common = [emitted.source, "--main-module", emitted.main_module, "--syntax-module", emitted.syntax_module]
    process = k.run(
        "kompile/haskell", "kompile",
        [*common, "--backend", "haskell", "--output-definition", kompiled / "haskell"],
        timeout=900,
    )
    if process.returncode != 0:
        raise GateError(f"{emitted.fixture.package}: kompile --backend haskell failed:\n{process.stderr}")
    rejected = k.run(
        "kompile/llvm", "kompile",
        [*common, "--backend", "llvm", "--output-definition", kompiled / "llvm"],
        timeout=900,
    )
    llvm = (rejected.stdout + rejected.stderr).strip().splitlines()
    if rejected.returncode == 0 or not llvm:
        raise GateError(f"{emitted.fixture.package}: Java kompile --backend llvm accepted rule existentials")
    states = {}
    for name, path in programs.items():
        executed = k.run(
            f"krun/{name}", "krun",
            ["--definition", kompiled / "haskell", "--output", "kast", path],
            timeout=300,
        )
        if executed.returncode != 0:
            raise GateError(f"{emitted.fixture.package} {name}: krun failed:\n{executed.stderr}")
        states[name] = normalized_states(executed.stdout)
    proof = None
    if claim:
        proved = k.run(
            f"kprove/{CLAIM_LABEL}", "kprove",
            [
                emitted.directory / "spec.k", "--definition", kompiled / "haskell",
                "--spec-module", CLAIM_SPEC_MODULE, "--claims", f"{CLAIM_SPEC_MODULE}.{CLAIM_LABEL}",
            ],
            timeout=600,
        )
        stuck = re.findall(r"<k>\s*(.*?)\s*</k>", proved.stdout, re.DOTALL)
        proof = {
            "proven": proved.returncode == 0,
            "stuck": "WarnStuckClaimState" in proved.stderr + proved.stdout,
            "depth": 0 if stuck else None,
            "k": normalize_k_text(stuck[0]) if stuck else None,
        }
    print(f"PASS verification-surface {emitted.fixture.package} reference snapshot: {k.finish()}")
    return states, proof, llvm[0]


def compare(
    harness: FixtureGate, emitted: Emitted, native: dict[str, Any], java: dict[str, Any],
) -> dict[str, Any]:
    """Require agreement, or exactly the pinned divergence, per program."""

    known = harness.divergences.get(emitted.fixture.package, {})
    observed = {}
    for name in sorted(native):
        routes = {"native": native[name], "java": java[name]}
        if name in known:
            if routes != known[name]:
                raise GateError(
                    f"{emitted.fixture.package} {name}: pinned divergence changed:\n"
                    f"expected {json.dumps(known[name], indent=1)}\nobserved {json.dumps(routes, indent=1)}"
                )
            observed[name] = routes
            continue
        if routes["native"] != routes["java"]:
            raise GateError(
                f"{emitted.fixture.package} {name}: native {json.dumps(routes['native'])} "
                f"differs from Java K {json.dumps(routes['java'])}"
            )
        observed[name] = routes["native"]
    harness.pins.expect(("outcomes", emitted.fixture.package), observed)
    return observed


# --- fixtures -----------------------------------------------------------------


def materialize(name: str, workspace: Path) -> Path:
    """Copy one negative fixture into the workspace with the facade path filled in."""

    destination = workspace / "fixtures" / name
    shutil.copytree(FIXTURES / name, destination)
    facade = json.dumps(str((ROOT / "crates" / "krs").resolve()))
    for template in sorted(destination.rglob("Cargo.toml.in")):
        manifest = template.read_text(encoding="utf-8").replace("@KRS_CRATE_PATH@", facade)
        template.with_name("Cargo.toml").write_text(manifest, encoding="utf-8")
        template.unlink()
    return destination / "Cargo.toml"


def verify_package(harness: FixtureGate, fixture: Fixture, *, claim: bool) -> None:
    harness.check(fixture)
    expansion = harness.expand(fixture)
    if fixture == L21_READABLE and READABLE_HELPERS not in expansion:
        raise GateError(f"{fixture.package}: krs expand does not keep the clause helpers before #[k::rule]")
    emitted = harness.emit(fixture)
    source = emitted.source.read_text(encoding="utf-8")
    for fragment in EMITTED_RULES[fixture.package]:
        if fragment not in source:
            raise GateError(f"{fixture.package}: emitted K omits:\n{fragment}")
    symbols = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    requirements = sorted([row["feature"], row["symbol"]] for row in symbols.get("capability_requirements") or ())
    if requirements != REQUIREMENTS[fixture.package]:
        raise GateError(f"{fixture.package}: symbols.json records {requirements!r}")
    for route in ("native-rust", "java-haskell-reference", "browser"):
        krs_gate.require_route(harness.gate, emitted.directory, route, environment=harness.environment)

    # Concrete execution refuses the definition before compiling it.
    refused = harness._krs(fixture, "build", "--backend", "llvm", "--output", harness.workspace / "llvm" / fixture.package, check=False)
    refusal = diagnostic_lines(refused.stderr)
    if refused.returncode == 0 or not refusal:
        raise GateError(f"{fixture.package}: krs build --backend llvm accepted rule existentials")
    harness.pins.expect(("capability_refusals", fixture.package), refusal[0])

    directory = harness.workspace / "programs" / fixture.package
    directory.mkdir(parents=True, exist_ok=True)
    programs = {}
    for name, text in PROGRAMS[fixture.package].items():
        programs[name] = directory / f"{name}.pgm"
        programs[name].write_text(text + "\n", encoding="utf-8")
    native = {name: native_states(harness, fixture, path) for name, path in programs.items()}
    java, java_proof, java_llvm = java_route(harness, emitted, programs, claim=claim)
    if java_llvm != JAVA_LLVM_REJECTION:
        raise GateError(f"{fixture.package}: Java kompile --backend llvm reported {java_llvm!r}")
    observed = compare(harness, emitted, native, java)
    print(f"PASS {fixture.package}: symbolic search agrees on {', '.join(sorted(observed))}")
    if claim:
        native_proof = native_claim(harness, fixture)
        if native_proof != java_proof:
            raise GateError(f"{fixture.package}: claim outcome native {native_proof} differs from kprove {java_proof}")
        harness.pins.expect(("claims", fixture.package), native_proof)
        print(f"PASS {fixture.package}: claim {CLAIM_LABEL} agrees with kprove: {native_proof}")


def verify_ignored_ensures(harness: FixtureGate) -> None:
    """An LLVM build of a transition with `ensures` alone warns that LLVM ignores it."""

    manifest = materialize("ensures-llvm", harness.workspace)
    fixture = Fixture(manifest, "krs-verification-surface-ensures-llvm")
    process = harness._krs(fixture, "build", "--backend", "llvm", "--output", harness.workspace / "llvm" / "ensures-llvm", check=False)
    warnings = diagnostic_lines(process.stderr)
    if process.returncode != 0 or not warnings:
        raise GateError(f"ensures-llvm: expected a successful build with a warning:\n{process.stderr}")
    harness.pins.expect(("warnings", "ensures-llvm"), warnings)
    print(f"PASS ensures-llvm: {warnings[0]}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 verification-surface ledger")

    target = checkout_scratch() / "verification-surface-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment, target=target)
    gate = krs_gate.configured_or_build(target)
    check_packages("verification-surface", krs=krs, env=environment, target_dir=target)

    with tempfile.TemporaryDirectory(prefix="krs-verification-surface-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "verification-surface", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
        )
        verify_package(harness, L21, claim=True)
        verify_package(harness, L21_READABLE, claim=False)
        verify_ignored_ensures(harness)
        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-verification-surface-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("verification-surface")
    print("PASS verification-surface")
    return 0


if __name__ == "__main__":
    entry("verification-surface", main, errors=(OSError,))
