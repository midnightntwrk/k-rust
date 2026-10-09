#!/usr/bin/env python3
"""Verification-surface feature gate: existentials and ensures on rules (KF-040), trusted claims (KF-042), SMT translations (KF-044), concrete, symbolic, and smt_lemma (KF-043).

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

Trusted claims (KF-042): `trusted` has a constructor `helper(Int)` with no
rules, the rule `call(I) => helper(I)`, the trusted claim `helper-axiom`
(`helper(I) => I +Int 1`), and `call-spec` (`call(I) => I +Int 1`), which
only `helper-axiom` makes provable. The emitted `spec.k` carries `[trusted]`;
`krs prove` reports `call-spec` proven and `helper-axiom` trusted, exits 0,
and warns `krs::emit::trusted-claim`, as `krs build --backend haskell` does.
Java `kprove` of the emitted spec proves it (`#Top`). The ablation
`trusted-ablation` drops `helper-axiom`: `call-spec` then fails on both
routes. Java prints `#Top` even for a spec of only trusted claims, so the
trusted status is pinned from the native report alone. Negative fixtures in
the macro tests pin `trusted` with `circularity`, twice, and with a value.

SMT translations (KF-044): `hook` declares `myAbs` with
`smt_hook = "(ite (< {value} 0) (- 0 {value}) {value})"` and no equation, the
rule `go(I) => myAbs(I) >=Int 0`, and the claim `abs-nonneg`
(`go(I) => true`). The emitted K carries `smt-hook((ite (< #1 0) (- 0 #1)
#1))`, and `clampSub`, whose template names its fields out of order, shows the
renumbering (`#2` before `#1`). `krs prove` proves the claim with Z3, warns
`krs::emit::smt-only-function` once per function without equations, and Java
`kprove` of the emitted spec proves it too. `hook-ablation` gives `myAbs`
`smtlib = "myAbs"` instead, an uninterpreted symbol: the claim then fails on
both routes. A negative fixture pins two functions with one `smtlib` symbol;
the macro tests pin the syntax diagnostics.

Restrictions on simplifications (KF-043): `conc` declares `h` with
`smtlib = "probeH"` and no equation, the rule `go(I) => h(I) >Int 3`, and the
simplification `h(X) => X +Int 1` restricted by `concrete(x)`, emitted
`[simplification, concrete(X), label(..)]`. The claim `go-concrete`
(`go(5) => true`) is proved on both routes; `go-symbolic` (`go(I) => true`
when `I >Int 2`) fails on both, stuck at `h(I) >Int 3`, because the
simplification never fires on a symbolic argument and Z3 sees only the
uninterpreted `probeH`. `conc-unrestricted` drops the restriction and both
claims are proved; `conc-smt-lemma` keeps `concrete(x)` and adds `smt_lemma`
(`[simplification, concrete(X), smt-lemma, label(..)]`), so Z3 receives
`probeH(x) = x + 1` as an axiom and both claims are proved. Java `kprove`
runs once per claim. Negative fixtures pin a binder `concrete(..)` names that
the left side does not bind, bare `concrete` with bare `symbolic`, an
`smt_lemma` over a function without an SMT translation, and a `concrete`
equation beside an unrestricted one of the same function.

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

TRUSTED = Fixture(MANIFEST, "krs-verification-surface-trusted")
TRUSTED_ABLATION = Fixture(MANIFEST, "krs-verification-surface-trusted-ablation")
TRUSTED_SPEC_MODULE = "KRS-TRUSTED-SPEC"
TRUSTED_CALL_SPEC = (
    "  claim [call-spec]:\n"
    "    <k> call ( I:Int ) ~> Tail:K => I:Int +Int 1 ~> Tail:K </k>\n"
)
TRUSTED_HELPER_AXIOM = (
    "  claim [helper-axiom]:\n"
    "    <k> helper ( I:Int ) ~> Tail:K => I:Int +Int 1 ~> Tail:K </k>\n"
    "    [trusted]\n"
)
TRUSTED_EXPECTED = {
    # package: (emitted claims, native statuses, krs prove exit status, Java kprove proves)
    TRUSTED.package: (
        (TRUSTED_CALL_SPEC, TRUSTED_HELPER_AXIOM),
        {"call-spec": "proven", "helper-axiom": "trusted"},
        0,
        True,
    ),
    TRUSTED_ABLATION.package: ((TRUSTED_CALL_SPEC,), {"call-spec": "disproved"}, 1, False),
}

HOOK = Fixture(MANIFEST, "krs-verification-surface-hook")
HOOK_ABLATION = Fixture(MANIFEST, "krs-verification-surface-hook-ablation")
HOOK_EXPECTED = {
    # package: (spec module, emitted productions, native statuses, krs prove exit status,
    #           Java kprove proves, smt-only-function warnings)
    HOOK.package: (
        "KRS-SMT-HOOK-SPEC",
        (
            '  syntax Int ::= "myAbs" "(" Int ")" [symbol(myAbs), function, total, smt-hook((ite (< #1 0) (- 0 #1) #1))]\n',
            '  syntax Int ::= "clampSub" "(" Int "," Int ")" [symbol(clampSub), function, total, smt-hook((ite (< #2 #1) 0 (- #2 #1)))]\n',
        ),
        {"abs-nonneg": "proven"},
        0,
        True,
        2,
    ),
    HOOK_ABLATION.package: (
        "KRS-SMT-HOOK-ABLATION-SPEC",
        ('  syntax Int ::= "myAbs" "(" Int ")" [symbol(myAbs), function, total, smtlib(myAbs)]\n',),
        {"abs-nonneg": "failed"},
        1,
        False,
        0,
    ),
}

CONC = Fixture(MANIFEST, "krs-verification-surface-conc")
CONC_UNRESTRICTED = Fixture(MANIFEST, "krs-verification-surface-conc-unrestricted")
CONC_SMT_LEMMA = Fixture(MANIFEST, "krs-verification-surface-conc-smt-lemma")
CONC_CLAIMS = ("go-concrete", "go-symbolic")
CONC_EXPECTED = {
    # package: (spec module, emitted simplification prefix, native statuses, krs prove exit status)
    CONC.package: (
        "KRS-CONC-SPEC",
        "  rule h ( X:Int ) => X:Int +Int 1 [simplification, concrete(X), label(",
        {"go-concrete": "proven", "go-symbolic": "failed"},
        1,
    ),
    CONC_UNRESTRICTED.package: (
        "KRS-CONC-UNRESTRICTED-SPEC",
        "  rule h ( X:Int ) => X:Int +Int 1 [simplification, label(",
        {"go-concrete": "proven", "go-symbolic": "proven"},
        0,
    ),
    CONC_SMT_LEMMA.package: (
        "KRS-CONC-SMT-LEMMA-SPEC",
        "  rule h ( X:Int ) => X:Int +Int 1 [simplification, concrete(X), smt-lemma, label(",
        {"go-concrete": "proven", "go-symbolic": "proven"},
        0,
    ),
}

NEGATIVE = (
    "exists-equation",
    "exists-unused",
    "exists-in-requires",
    "exists-shadows",
    "smtlib-duplicate",
    "restriction-unknown-binder",
    "restriction-both-bare",
    "restriction-equation-inconsistent",
    "smt-lemma-untranslatable",
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


def native_trusted_proof(harness: FixtureGate, fixture: Fixture, spec_module: str = TRUSTED_SPEC_MODULE) -> dict[str, Any]:
    """Run `krs prove` on every claim; return statuses, exit status, and warnings."""

    process = harness._krs(fixture, "prove", check=False)
    prefix = re.escape(spec_module)
    statuses = dict(re.findall(rf"^{prefix}\.([\w-]+): ([\w-]+)$", process.stdout, re.MULTILINE))
    if not statuses:
        raise GateError(f"{fixture.package}: krs prove printed no claim status:\n{process.stdout}\n{process.stderr}")
    summary = [line for line in process.stderr.splitlines() if line.startswith("krs prove: ")]
    return {
        "statuses": statuses,
        "exit": process.returncode,
        "summary": summary,
        "warnings": diagnostic_lines(process.stderr),
    }


def java_trusted_proof(harness: FixtureGate, emitted: Emitted, spec_module: str = TRUSTED_SPEC_MODULE) -> dict[str, Any]:
    """Kompile the emitted definition for Haskell and `kprove` its whole spec module."""

    package = emitted.fixture.package
    inputs = {
        f"emitted/{package}/definition.k": emitted.source,
        f"emitted/{package}/spec.k": emitted.directory / "spec.k",
    }
    k = Snapshot(
        f"verification-surface/{package}",
        Key(tools=JAVA_TOOLS, inputs=inputs),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, package),
    )
    kompiled = harness.workspace / "kompiled" / package / "haskell"
    process = k.run(
        "kompile/haskell", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module, "--syntax-module", emitted.syntax_module,
            "--backend", "haskell", "--output-definition", kompiled,
        ],
        timeout=900,
    )
    if process.returncode != 0:
        raise GateError(f"{package}: kompile --backend haskell failed:\n{process.stderr}")
    proved = k.run(
        "kprove/spec", "kprove",
        [emitted.directory / "spec.k", "--definition", kompiled, "--spec-module", spec_module],
        timeout=600,
    )
    result = {"proven": proved.returncode == 0, "top": proved.stdout.strip() == "#Top"}
    print(f"PASS verification-surface {package} reference snapshot: {k.finish()}")
    return result


def verify_trusted(harness: FixtureGate, fixture: Fixture) -> None:
    """A trusted claim is emitted `[trusted]`, reported `trusted`, and applied on both routes."""

    claims, statuses, exit_status, java_proves = TRUSTED_EXPECTED[fixture.package]
    harness.check(fixture)
    emitted = harness.emit(fixture)
    spec = (emitted.directory / "spec.k").read_text(encoding="utf-8")
    for fragment in claims:
        if fragment not in spec:
            raise GateError(f"{fixture.package}: emitted spec.k omits:\n{fragment}")
    if spec.count("[trusted]") != sum("[trusted]" in fragment for fragment in claims):
        raise GateError(f"{fixture.package}: emitted spec.k has an unexpected [trusted] claim:\n{spec}")
    trusted = sum(status == "trusted" for status in statuses.values())

    native = native_trusted_proof(harness, fixture)
    if native["statuses"] != statuses or native["exit"] != exit_status:
        raise GateError(f"{fixture.package}: krs prove reported {json.dumps(native)}")
    if len(native["warnings"]) != trusted or not all("[krs::emit::trusted-claim]" in line for line in native["warnings"]):
        raise GateError(f"{fixture.package}: krs prove warned {native['warnings']!r}")
    harness.pins.expect(("trusted_proofs", fixture.package), native)

    built = harness._krs(fixture, "build", "--backend", "haskell", "--output", harness.workspace / "haskell" / fixture.package, check=False)
    warnings = diagnostic_lines(built.stderr)
    if built.returncode != 0 or warnings != native["warnings"]:
        raise GateError(f"{fixture.package}: krs build --backend haskell warned {warnings!r}:\n{built.stderr}")

    java = java_trusted_proof(harness, emitted)
    if java["proven"] != java_proves or java["top"] != java_proves:
        raise GateError(f"{fixture.package}: kprove reported {json.dumps(java)}, expected proven={java_proves}")
    native_proves = native["statuses"]["call-spec"] == "proven"
    if native_proves != java["proven"]:
        raise GateError(f"{fixture.package}: call-spec native proven={native_proves} differs from kprove {java['proven']}")
    harness.pins.expect(("trusted_kprove", fixture.package), java)
    print(f"PASS {fixture.package}: krs prove {native['statuses']} agrees with kprove proven={java['proven']}")


def verify_hook(harness: FixtureGate, fixture: Fixture) -> None:
    """An `smt_hook` lets Z3 prove a claim about a function without equations; `smtlib` alone does not."""

    spec_module, productions, statuses, exit_status, java_proves, smt_only = HOOK_EXPECTED[fixture.package]
    harness.check(fixture)
    emitted = harness.emit(fixture)
    source = emitted.source.read_text(encoding="utf-8")
    for fragment in productions:
        if fragment not in source:
            raise GateError(f"{fixture.package}: emitted K omits:\n{fragment}")

    native = native_trusted_proof(harness, fixture, spec_module)
    if native["statuses"] != statuses or native["exit"] != exit_status:
        raise GateError(f"{fixture.package}: krs prove reported {json.dumps(native)}")
    if len(native["warnings"]) != smt_only or not all("[krs::emit::smt-only-function]" in line for line in native["warnings"]):
        raise GateError(f"{fixture.package}: krs prove warned {native['warnings']!r}")
    harness.pins.expect(("smt_proofs", fixture.package), native)

    java = java_trusted_proof(harness, emitted, spec_module)
    if java["proven"] != java_proves or java["top"] != java_proves:
        raise GateError(f"{fixture.package}: kprove reported {json.dumps(java)}, expected proven={java_proves}")
    harness.pins.expect(("smt_kprove", fixture.package), java)
    print(f"PASS {fixture.package}: krs prove {native['statuses']} agrees with kprove proven={java['proven']}")


def java_claim_proofs(harness: FixtureGate, emitted: Emitted, spec_module: str, labels: tuple[str, ...]) -> dict[str, bool]:
    """Kompile the emitted definition for Haskell and `kprove` each claim of the spec module alone."""

    package = emitted.fixture.package
    inputs = {
        f"emitted/{package}/definition.k": emitted.source,
        f"emitted/{package}/spec.k": emitted.directory / "spec.k",
    }
    k = Snapshot(
        f"verification-surface/{package}",
        Key(tools=JAVA_TOOLS, inputs=inputs),
        workspace=harness.workspace, refresh=harness.refresh,
        pin=Pin(harness.pins, package),
    )
    kompiled = harness.workspace / "kompiled" / package / "haskell"
    process = k.run(
        "kompile/haskell", "kompile",
        [
            emitted.source, "--main-module", emitted.main_module, "--syntax-module", emitted.syntax_module,
            "--backend", "haskell", "--output-definition", kompiled,
        ],
        timeout=900,
    )
    if process.returncode != 0:
        raise GateError(f"{package}: kompile --backend haskell failed:\n{process.stderr}")
    proofs = {}
    for label in labels:
        proved = k.run(
            f"kprove/{label}", "kprove",
            [
                emitted.directory / "spec.k", "--definition", kompiled, "--spec-module", spec_module,
                "--claims", f"{spec_module}.{label}",
            ],
            timeout=600,
        )
        proofs[label] = proved.returncode == 0 and proved.stdout.strip() == "#Top"
    print(f"PASS verification-surface {package} reference snapshot: {k.finish()}")
    return proofs


def verify_conc(harness: FixtureGate, fixture: Fixture) -> None:
    """`concrete(x)` keeps a simplification off symbolic arguments; `smt_lemma` hands it to Z3."""

    spec_module, simplification, statuses, exit_status = CONC_EXPECTED[fixture.package]
    harness.check(fixture)
    emitted = harness.emit(fixture)
    source = emitted.source.read_text(encoding="utf-8")
    if simplification not in source:
        raise GateError(f"{fixture.package}: emitted K omits:\n{simplification}")

    native = native_trusted_proof(harness, fixture, spec_module)
    if native["statuses"] != statuses or native["exit"] != exit_status or native["warnings"]:
        raise GateError(f"{fixture.package}: krs prove reported {json.dumps(native)}")
    harness.pins.expect(("restriction_proofs", fixture.package), native)

    java = java_claim_proofs(harness, emitted, spec_module, CONC_CLAIMS)
    expected = {label: status == "proven" for label, status in statuses.items()}
    if java != expected:
        raise GateError(f"{fixture.package}: kprove per claim reported {json.dumps(java)}, native {json.dumps(statuses)}")
    harness.pins.expect(("restriction_kprove", fixture.package), java)
    print(f"PASS {fixture.package}: krs prove {native['statuses']} agrees with kprove {java}")


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
        verify_trusted(harness, TRUSTED)
        verify_trusted(harness, TRUSTED_ABLATION)
        verify_hook(harness, HOOK)
        verify_hook(harness, HOOK_ABLATION)
        verify_conc(harness, CONC)
        verify_conc(harness, CONC_UNRESTRICTED)
        verify_conc(harness, CONC_SMT_LEMMA)
        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-verification-surface-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("verification-surface")
    print("PASS verification-surface")
    return 0


if __name__ == "__main__":
    entry("verification-surface", main, errors=(OSError,))
