#!/usr/bin/env python3
"""Verification-surface feature gate: existentials and ensures on rules (KF-040), trusted claims (KF-042), SMT translations (KF-044), concrete, symbolic, and smt_lemma (KF-043), author spec modules (KF-041), and matching-logic predicates (KF-039).

The fixture packages are K tutorial lesson 1.21 in both layers:

- `l21`: reference `#[k::rule]` fns. `zero_to_unknown` (`cells!` form)
  rewrites `0` to a fresh `?X` with `ensures ?X =/=Int 0`; `big_to_five`
  rewrites an integer of at least 10 to `5`; `foo_bounded` (term fn form)
  rewrites `foo` to `?X` with `ensures ?X <Int 5`; the claim
  `foo-reaches-below-five` says every path from `foo` reaches some
  `?Y <Int 5`, and the spec module `KRS-LESSON-21-GOTCHA` holds the
  unprovable `zero-reaches-nonzero` (every path from `0` reaches some
  `?Y =/=Int 0`).
- `l21-readable`: the two lesson rules as readable `k::rules!` clauses, whose
  `#[k::exists]` and `#[k::ensures]` helpers `krs expand` keeps verbatim
  before `#[k::rule(..)]`.

Neither package puts the two lesson rules in a `nondet` group: `krs check`
accepts them because unifying their subjects turns `big_to_five`'s guard into
`0 >=Int 10`, which the overlap check evaluates to false.

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

The claim `foo-reaches-below-five` is proven on both routes (`krs prove`,
and Java `kprove` prints `#Top`): its start `foo` is not an `Int`, so it
cannot match the target before `foo-bounded` steps. The gotcha
`zero-reaches-nonzero` is proven on neither: the start `0` already unifies with
the target `?Y`, and K's reachability check stops at such a state when the
ensures condition fails there (Java: WarnStuckClaimState). Both routes report
it stuck at depth 0 on `<k> 0 ~> Tail </k>`, which is pinned.

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
renumbering (`#2` before `#1`). `krs prove` proves the claim with Z3 without
a warning, `krs build --backend llvm` warns `krs::emit::smt-only-function` once
per function without equations, and Java `kprove` of the emitted spec proves it
too. `hook-ablation` gives `myAbs`
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
uninterpreted `probeH`. The ablation is `conc`'s spec module
`KRS-CONC-UNRESTRICTED`, which adds the lemma without the restriction: its
copies of both claims, `go-concrete-unrestricted` and
`go-symbolic-unrestricted`, are proved on both routes (`--spec-module`).
`conc-smt-lemma` keeps `concrete(x)` and adds `smt_lemma` (`[simplification,
concrete(X), smt-lemma, label(..)]`), so Z3 receives `probeH(x) = x + 1` as
an axiom and both claims are proved. Java `kprove` runs once per claim. Negative fixtures pin a binder `concrete(..)` names that
the left side does not bind, bare `concrete` with bare `symbolic`, an
`smt_lemma` over a function without an SMT translation, and a `concrete`
equation beside an unrestricted one of the same function.

Author spec modules (KF-041): `imp-sum` depends on the IMP language and,
like upstream `imp-verification.k`, its definition module `IMP-VERIFICATION`
adds only a regex token for `$`-prefixed identifiers to `Id`. Its spec module
`IMP-VERIFICATION-LEMMAS` imports the definition (`imports = [crate]`) and
adds a simplification lemma; `IMP-SUM-SPEC` imports the lemmas and holds the
sum loop's circularity, `dollar-sum-spec`, whose identifiers print bare
(`$n`, not `#token("$n","Id")`). The emitted `spec.k` holds the two author
modules in import order and then the generated `IMP-VERIFICATION-SPEC` with
IMP's loose claims; `definition.k` holds neither. `krs prove --spec-module
IMP-SUM-SPEC` proves the claim natively (k-rust proves the spec module's own
proof definition), and Java `kprove --spec-module IMP-SUM-SPEC` of the
emitted files gives `#Top`. An unknown spec module and a spec module without
claims are refused. The language package `l22` holds `LESSON-SPEC`, a spec
module that declares the regex `$`-identifier token itself, so `kompile`
never sees it: `definition.k` has no token, and the claim `dollar-assign`
(`$n = N ; $m = M ;`) is proved natively and by `kprove --spec-module
LESSON-SPEC`. Negative fixtures pin a sort in a spec module, an import
cycle, an identifier no visible token lexes, one lexed only by a private
(non-`pub`) token alias of the definition, an `smt_lemma` lemma in a spec
module, a spec module that never imports the definition, and a spec-module
simplification lemma that names a private (non-`pub`) production, which K's
private syntax hides from every proof module.

Matching-logic predicates (KF-039): `l22` is K tutorial lesson 1.22's
language (assignments to a store, sequencing, a strict `if` and `<`, a `div`
that steps only for a nonzero divisor, and the partial function `pf`), and
`l22-verification` adds the `$`-identifier token and three spec modules.
`KRS-L22-LEMMAS` holds two predicate simplifications, emitted as
`rule { M:Map [ Key:KItem <- V:KItem ] #Equals M:Map [ Key:KItem <- W:KItem ] }
=> { V:KItem #Equals W:KItem }` and `rule #Ceil ( pf ( X:Int ) ) => { true
#Equals X:Int >Int 0 }`. `KRS-L22-CLAIMS` imports them and holds the lesson's
`branch` claim (an `ensures { true #Equals .. }` on an existential), `div-eq`
(`requires #Not ( { B:Int #Equals 0 } )`, `ensures { ?R:Int #Equals A:Int
/Int B:Int }`), and `div-small`, whose postcondition is `#Exists Q:Int . ( ..
)`. Every claim is proved natively (`krs prove --spec-module`) and by Java
`kprove --claims` on the emitted files. `KRS-L22-ABLATION` states `branch`
without the lemmas, and both routes fail to prove it. Negative fixtures pin
each KF-039 diagnostic: a predicate on a transition or equation condition, a
predicate as an object operand, a Bool where a predicate is expected,
`ml::equals` operands without a common sort, a shadowing or untyped
`ml::exists` binder, a closure elsewhere, an unknown `ml::` item, a predicate
simplification not rooted at `ml::equals` or `ml::ceil`, one whose types
disagree, and a predicate subject on a transition.

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
    '#[k::rule(label = "zero-to-unknown")]\n'
)
# (spec module, claim label): (proven, emitted claim). The lesson's claim is
# provable; the gotcha's start already matches its target, so it is stuck.
L21_CLAIMS = {
    ("KRS-LESSON-21-SPEC", "foo-reaches-below-five"): (
        True,
        "  claim [foo-reaches-below-five]:\n"
        "    <k> foo ~> Tail:K => ?Y:Int ~> Tail:K </k>\n"
        "    ensures ?Y:Int <Int 5\n",
    ),
    ("KRS-LESSON-21-GOTCHA", "zero-reaches-nonzero"): (
        False,
        "  claim [zero-reaches-nonzero]:\n"
        "    <k> 0 ~> Tail:K => ?Y:Int ~> Tail:K </k>\n"
        "    ensures ?Y:Int =/=Int 0\n",
    ),
}
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
    #           Java kprove proves, smt-only-function warnings of an LLVM build)
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
    CONC_SMT_LEMMA.package: (
        "KRS-CONC-SMT-LEMMA-SPEC",
        "  rule h ( X:Int ) => X:Int +Int 1 [simplification, concrete(X), smt-lemma, label(",
        {"go-concrete": "proven", "go-symbolic": "proven"},
        0,
    ),
}

# The ablation spec module of `conc`: its emitted lemma and native statuses.
CONC_ABLATION = "KRS-CONC-UNRESTRICTED"
CONC_ABLATION_SIMPLIFICATION = "  rule h ( X:Int ) => X:Int +Int 1 [simplification, label("
CONC_ABLATION_STATUSES = {"go-concrete-unrestricted": "proven", "go-symbolic-unrestricted": "proven"}

IMP_SUM = Fixture(MANIFEST, "krs-verification-surface-imp-sum", dependencies=("krs-imp-definition:main",))
IMP_SUM_SPEC = "IMP-SUM-SPEC"
IMP_SUM_MODULES = ["IMP-VERIFICATION-LEMMAS", "IMP-SUM-SPEC", "IMP-VERIFICATION-SPEC"]
IMP_SUM_TOKEN = '  syntax Id ::= r"\\\\$[a-zA-Z0-9_]+" [token]\n'
IMP_SUM_FRAGMENTS = (
    "module IMP-VERIFICATION-LEMMAS\n  imports BOOL\n  imports IMP-VERIFICATION\n  imports INT\n",
    "  rule Value:Int <Int Value:Int => false [simplification,",
    "module IMP-SUM-SPEC\n  imports BOOL\n  imports ID-SYNTAX\n  imports IMP-VERIFICATION-LEMMAS\n",
    "  claim [dollar-sum-spec]:\n"
    "    <k> while ( ! ($n <= 0) ) { $s = $s + $n ; $n = $n + - 1 ; } ~> Tail:K => .K ~> Tail:K </k>\n"
    "    <env> $n |-> N:Int $s |-> S:Int => $n |-> 0 $s |-> S:Int +Int (((N:Int +Int 1) *Int N:Int) /Int 2) </env>\n"
    "    requires N:Int >=Int 0\n"
    "    [circularity]\n",
)

L22_LANGUAGE = Fixture(MANIFEST, "krs-verification-surface-l22")
LESSON_SPEC = "LESSON-SPEC"
LESSON_SPEC_FRAGMENT = (
    "module LESSON-SPEC\n  imports ID-SYNTAX\n  imports INT-SYNTAX\n  imports KRS-L22\n  imports MAP\n\n"
    + IMP_SUM_TOKEN
    + "\n  claim [dollar-assign]:\n"
    "    <k> $n = N:Int ; $m = M:Int ; ~> Tail:K => .K ~> Tail:K </k>\n"
    "    <store> S:Map => S:Map [ $n <- N:Int ] [ $m <- M:Int ] </store>\n"
    "endmodule\n"
)

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
    "spec-module-sort",
    "spec-module-cycle",
    "spec-module-undeclared-id",
    "spec-module-private-id",
    "spec-module-smt-lemma",
    "spec-module-no-definition",
    "spec-module-private-lemma",
    "ml-transition-requires",
    "ml-equation-requires",
    "ml-object-operand",
    "ml-bool-predicate",
    "ml-equals-sorts",
    "ml-exists-shadows",
    "ml-exists-untyped",
    "ml-closure-elsewhere",
    "ml-unknown-item",
    "ml-simplification-root",
    "ml-simplification-types",
    "ml-predicate-rule",
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


def native_claim(harness: FixtureGate, fixture: Fixture, module: str, label: str) -> dict[str, Any]:
    process = harness._krs(fixture, "prove", "--spec-module", module, "--claim", label, check=False)
    text = process.stdout
    status = re.search(rf"^{re.escape(module)}\.{re.escape(label)}: (\w+)$", text, re.MULTILINE)
    leaf = re.search(r"leaf 1 \((\w+), depth (\d+)\):\s*<k>\s*(.*?)\s*</k>", text, re.DOTALL)
    if status is None or (status.group(1) != "proven" and leaf is None):
        raise GateError(f"{fixture.package}: krs prove printed no claim status and leaf:\n{text}\n{process.stderr}")
    return {
        "proven": status.group(1) == "proven",
        "stuck": leaf is not None and leaf.group(1) == "Stuck",
        "depth": int(leaf.group(2)) if leaf else None,
        "k": normalize_k_text(leaf.group(3)) if leaf else None,
    }


def normalize_k_text(text: str) -> str:
    text = re.sub(r":[A-Z][A-Za-z]*", "", " ".join(text.split()))
    return re.sub(r" ~> \.K$", "", text)


def java_route(
    harness: FixtureGate, emitted: Emitted, programs: dict[str, Path], *, claim: bool,
) -> tuple[dict[str, list[dict[str, Any]]], dict[str, dict[str, Any]], str]:
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
    proofs = {}
    for module, label in L21_CLAIMS if claim else ():
        proved = k.run(
            f"kprove/{label}", "kprove",
            [
                emitted.directory / "spec.k", "--definition", kompiled / "haskell",
                "--spec-module", module, "--claims", f"{module}.{label}",
            ],
            timeout=600,
        )
        stuck = re.findall(r"<k>\s*(.*?)\s*</k>", proved.stdout, re.DOTALL)
        proven = proved.returncode == 0
        if proven and proved.stdout.strip() != "#Top":
            raise GateError(f"{emitted.fixture.package}: kprove {module}.{label} exited 0 without #Top:\n{proved.stdout}")
        proofs[label] = {
            "proven": proven,
            "stuck": "WarnStuckClaimState" in proved.stderr + proved.stdout,
            "depth": 0 if stuck else None,
            "k": normalize_k_text(stuck[0]) if stuck else None,
        }
    print(f"PASS verification-surface {emitted.fixture.package} reference snapshot: {k.finish()}")
    return states, proofs, llvm[0]


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
    java, java_proofs, java_llvm = java_route(harness, emitted, programs, claim=claim)
    if java_llvm != JAVA_LLVM_REJECTION:
        raise GateError(f"{fixture.package}: Java kompile --backend llvm reported {java_llvm!r}")
    observed = compare(harness, emitted, native, java)
    print(f"PASS {fixture.package}: symbolic search agrees on {', '.join(sorted(observed))}")
    if claim:
        verify_l21_claims(harness, fixture, emitted, java_proofs)


def verify_l21_claims(
    harness: FixtureGate, fixture: Fixture, emitted: Emitted, java_proofs: dict[str, dict[str, Any]],
) -> None:
    """The lesson's claim is proven and the gotcha is stuck at depth 0, natively and by kprove."""

    source = emitted.source.read_text(encoding="utf-8")
    spec = (emitted.directory / "spec.k").read_text(encoding="utf-8")
    outcomes = {}
    for (module, label), (provable, fragment) in L21_CLAIMS.items():
        body = spec.partition(f"module {module}\n")[2].partition("endmodule\n")[0]
        if fragment not in body or f"module {module}\n" in source:
            raise GateError(f"{fixture.package}: spec module {module} in spec.k omits:\n{fragment}\n{spec}")
        native = native_claim(harness, fixture, module, label)
        if native != java_proofs[label]:
            raise GateError(f"{fixture.package}: claim {label} native {native} differs from kprove {java_proofs[label]}")
        if native["proven"] != provable or (not provable and not (native["stuck"] and native["depth"] == 0)):
            raise GateError(f"{fixture.package}: claim {label} reported {native}")
        outcomes[label] = native
        print(f"PASS {fixture.package}: claim {module}.{label} agrees with kprove: {native}")
    harness.pins.expect(("claims", fixture.package), outcomes)


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

L22 = Fixture(
    MANIFEST, "krs-verification-surface-l22-verification",
    dependencies=("krs-verification-surface-l22:main",),
)
L22_MODULES = ["KRS-L22-ABLATION", "KRS-L22-LEMMAS", "KRS-L22-CLAIMS"]
# spec module: (claim labels, native statuses and Java kprove outcomes)
L22_EXPECTED = {
    "KRS-L22-CLAIMS": {"branch": "proven", "div-eq": "proven", "div-small": "proven"},
    "KRS-L22-ABLATION": {"branch-ablation": "failed"},
}
L22_FRAGMENTS = (
    "  imports ML-SYNTAX\n",
    "  rule { M:Map [ Key:KItem <- V:KItem ] #Equals M:Map [ Key:KItem <- W:KItem ] }"
    " => { V:KItem #Equals W:KItem } [simplification,",
    "  rule #Ceil ( pf ( X:Int ) ) => { true #Equals X:Int >Int 0 } [simplification,",
    "    ensures { true #Equals (?C:Int ==Int A:Int) orBool (?C:Int ==Int B:Int) }\n",
    "  claim [div-eq]:\n"
    "    <k> div ( A:Int , B:Int ) ~> Tail:K => ?R:Int ~> Tail:K </k>\n"
    "    requires #Not ( { B:Int #Equals 0 } )\n"
    "    ensures { ?R:Int #Equals A:Int /Int B:Int }\n",
    "    requires { true #Equals 0 <=Int A:Int } #And { true #Equals A:Int <Int 10 }\n"
    "    ensures #Exists Q:Int . ( { ?R:Int #Equals Q:Int } #And { true #Equals Q:Int <Int 5 } )\n",
)


def native_trusted_proof(
    harness: FixtureGate, fixture: Fixture, spec_module: str = TRUSTED_SPEC_MODULE, *extra: str
) -> dict[str, Any]:
    """Run `krs prove` on every claim; return statuses, exit status, and warnings."""

    process = harness._krs(fixture, "prove", *extra, check=False)
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
    if native["warnings"]:
        raise GateError(f"{fixture.package}: krs prove warned {native['warnings']!r}")
    harness.pins.expect(("smt_proofs", fixture.package), native)

    # Only concrete execution needs equations, so only an LLVM build warns.
    built = harness._krs(fixture, "build", "--backend", "llvm", "--output", harness.workspace / "llvm" / fixture.package, check=False)
    warnings = diagnostic_lines(built.stderr)
    if built.returncode != 0 or len(warnings) != smt_only or not all("[krs::emit::smt-only-function]" in line for line in warnings):
        raise GateError(f"{fixture.package}: krs build --backend llvm warned {warnings!r}:\n{built.stderr}")
    harness.pins.expect(("smt_llvm_warnings", fixture.package), warnings)

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


def java_module_proofs(
    harness: FixtureGate, emitted: Emitted, modules: dict[str, tuple[str, ...]],
) -> dict[str, dict[str, bool]]:
    """Kompile the emitted definition for Haskell and `kprove` each claim of each spec module alone."""

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
    proofs: dict[str, dict[str, bool]] = {}
    for module, labels in modules.items():
        proofs[module] = {}
        for label in labels:
            proved = k.run(
                f"kprove/{module}/{label}", "kprove",
                [
                    emitted.directory / "spec.k", "--definition", kompiled, "--spec-module", module,
                    "--claims", f"{module}.{label}",
                ],
                timeout=600,
            )
            proofs[module][label] = proved.returncode == 0 and proved.stdout.strip() == "#Top"
    print(f"PASS verification-surface {package} reference snapshot: {k.finish()}")
    return proofs


def verify_ml_predicates(harness: FixtureGate, fixture: Fixture) -> None:
    """Matching-logic claim conditions and predicate simplifications (KF-039), on both routes."""

    harness.check(fixture)
    harness.expand(fixture)
    emitted = harness.emit(fixture)
    spec = (emitted.directory / "spec.k").read_text(encoding="utf-8")
    modules = re.findall(r"^module (\S+)$", spec, re.MULTILINE)
    if modules[: len(L22_MODULES)] != L22_MODULES:
        raise GateError(f"{fixture.package}: spec.k modules {modules}, expected {L22_MODULES} first")
    for fragment in L22_FRAGMENTS:
        if fragment not in spec:
            raise GateError(f"{fixture.package}: emitted spec.k omits:\n{fragment}")
    native = {}
    for module, expected in L22_EXPECTED.items():
        proof = native_trusted_proof(harness, fixture, module, "--spec-module", module)
        if proof["statuses"] != expected or proof["warnings"]:
            raise GateError(f"{fixture.package}: krs prove --spec-module {module} reported {json.dumps(proof)}")
        if proof["exit"] != (0 if all(status == "proven" for status in expected.values()) else 1):
            raise GateError(f"{fixture.package}: krs prove --spec-module {module} exited {proof['exit']}")
        native[module] = proof
    harness.pins.expect(("ml_proofs", fixture.package), native)
    java = java_module_proofs(harness, emitted, {module: tuple(labels) for module, labels in L22_EXPECTED.items()})
    for module, expected in L22_EXPECTED.items():
        agreed = {label: status == "proven" for label, status in expected.items()}
        if java[module] != agreed:
            raise GateError(f"{fixture.package}: kprove {module} reported {json.dumps(java[module])}, native {json.dumps(expected)}")
    harness.pins.expect(("ml_kprove", fixture.package), java)
    print(f"PASS {fixture.package}: KRS-L22-CLAIMS proven and KRS-L22-ABLATION failed, natively and by kprove")


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

    if fixture != CONC:
        java = java_claim_proofs(harness, emitted, spec_module, CONC_CLAIMS)
        expected = {label: status == "proven" for label, status in statuses.items()}
        if java != expected:
            raise GateError(f"{fixture.package}: kprove per claim reported {json.dumps(java)}, native {json.dumps(statuses)}")
        harness.pins.expect(("restriction_kprove", fixture.package), java)
        print(f"PASS {fixture.package}: krs prove {native['statuses']} agrees with kprove {java}")
        return

    # The ablation spec module: the lemma without `concrete(x)`, in spec.k only.
    spec = (emitted.directory / "spec.k").read_text(encoding="utf-8")
    ablation = spec.partition(f"module {CONC_ABLATION}\n")[2].partition("endmodule\n")[0]
    if CONC_ABLATION_SIMPLIFICATION not in ablation or f"module {CONC_ABLATION}\n" in source:
        raise GateError(f"{fixture.package}: spec module {CONC_ABLATION} omits:\n{CONC_ABLATION_SIMPLIFICATION}\n{spec}")
    proof = native_trusted_proof(harness, fixture, CONC_ABLATION, "--spec-module", CONC_ABLATION)
    if proof["statuses"] != CONC_ABLATION_STATUSES or proof["exit"] != 0 or proof["warnings"]:
        raise GateError(f"{fixture.package}: krs prove --spec-module {CONC_ABLATION} reported {json.dumps(proof)}")
    harness.pins.expect(("restriction_ablation_proofs", fixture.package), proof)

    modules = {spec_module: statuses, CONC_ABLATION: CONC_ABLATION_STATUSES}
    java = java_module_proofs(harness, emitted, {module: tuple(labels) for module, labels in modules.items()})
    for module, expected_statuses in modules.items():
        expected = {label: status == "proven" for label, status in expected_statuses.items()}
        if java[module] != expected:
            raise GateError(f"{fixture.package}: kprove {module} per claim reported {json.dumps(java[module])}, native {json.dumps(expected_statuses)}")
    harness.pins.expect(("restriction_kprove", fixture.package), java)
    print(f"PASS {fixture.package}: krs prove {native['statuses']} and {CONC_ABLATION} {proof['statuses']} agree with kprove {java}")


def verify_spec_modules(harness: FixtureGate, fixture: Fixture) -> None:
    """Author spec modules: emitted in import order, proved natively and by `kprove --spec-module`."""

    harness.check(fixture)
    expansion = harness.expand(fixture)
    if "#[k::spec_module(name = \"IMP-SUM-SPEC\", imports = [lemmas])]" not in expansion:
        raise GateError(f"{fixture.package}: krs expand does not keep the spec-module attribute")
    emitted = harness.emit(fixture)
    if emitted.main_module != "IMP-VERIFICATION":
        raise GateError(f"{fixture.package}: the main module is {emitted.main_module}, not the verification package")
    definition = emitted.source.read_text(encoding="utf-8")
    spec = (emitted.directory / "spec.k").read_text(encoding="utf-8")
    if IMP_SUM_TOKEN not in definition:
        raise GateError(f"{fixture.package}: definition.k omits the $-identifier token")
    if any(f"module {module}\n" in definition for module in IMP_SUM_MODULES):
        raise GateError(f"{fixture.package}: definition.k holds a spec module")
    modules = re.findall(r"^module (\S+)$", spec, re.MULTILINE)
    if modules != IMP_SUM_MODULES:
        raise GateError(f"{fixture.package}: spec.k modules {modules}, expected {IMP_SUM_MODULES}")
    for fragment in IMP_SUM_FRAGMENTS:
        if fragment not in spec:
            raise GateError(f"{fixture.package}: emitted spec.k omits:\n{fragment}")

    native = native_trusted_proof(harness, fixture, IMP_SUM_SPEC, "--spec-module", IMP_SUM_SPEC)
    if native["statuses"] != {"dollar-sum-spec": "proven"} or native["exit"] != 0 or native["warnings"]:
        raise GateError(f"{fixture.package}: krs prove --spec-module reported {json.dumps(native)}")
    harness.pins.expect(("spec_module_proofs", fixture.package), native)
    with krs_gate.Session(harness.gate, environment=harness.environment) as session:
        session.load(emitted.definition_ir, emitted.main_module)
        reports = session.exec_prove(module=IMP_SUM_SPEC)
    session_statuses = {report["claim"]: report["verdict"] for report in reports}
    if session_statuses != {f"{IMP_SUM_SPEC}.dollar-sum-spec": "proven"}:
        raise GateError(f"{fixture.package}: the krs-gate session proved {json.dumps(session_statuses)}")
    refusals = {}
    for module in ("IMP-VERIFICATION-LEMMAS", "MISSING-SPEC"):
        refused = harness._krs(fixture, "prove", "--spec-module", module, check=False)
        lines = diagnostic_lines(refused.stderr)
        if refused.returncode == 0 or not lines:
            raise GateError(f"{fixture.package}: krs prove --spec-module {module} was accepted:\n{refused.stderr}")
        refusals[module] = lines
    harness.pins.expect(("spec_module_refusals", fixture.package), refusals)

    java = java_trusted_proof(harness, emitted, IMP_SUM_SPEC)
    if not (java["proven"] and java["top"]):
        raise GateError(f"{fixture.package}: kprove --spec-module {IMP_SUM_SPEC} reported {json.dumps(java)}")
    harness.pins.expect(("spec_module_kprove", fixture.package), java)
    print(f"PASS {fixture.package}: {IMP_SUM_SPEC} proven natively and by kprove --spec-module")


def verify_lesson_spec(harness: FixtureGate, fixture: Fixture) -> None:
    """A spec module that declares its own regex token: the definition never sees it."""

    harness.check(fixture)
    emitted = harness.emit(fixture)
    definition = emitted.source.read_text(encoding="utf-8")
    spec = (emitted.directory / "spec.k").read_text(encoding="utf-8")
    if "[token]" in definition:
        raise GateError(f"{fixture.package}: definition.k holds a token production:\n{definition}")
    if LESSON_SPEC_FRAGMENT not in spec:
        raise GateError(f"{fixture.package}: emitted spec.k omits:\n{LESSON_SPEC_FRAGMENT}")

    native = native_trusted_proof(harness, fixture, LESSON_SPEC, "--spec-module", LESSON_SPEC)
    if native["statuses"] != {"dollar-assign": "proven"} or native["exit"] != 0 or native["warnings"]:
        raise GateError(f"{fixture.package}: krs prove --spec-module {LESSON_SPEC} reported {json.dumps(native)}")
    harness.pins.expect(("spec_module_proofs", fixture.package), native)

    java = java_trusted_proof(harness, emitted, LESSON_SPEC)
    if not (java["proven"] and java["top"]):
        raise GateError(f"{fixture.package}: kprove --spec-module {LESSON_SPEC} reported {json.dumps(java)}")
    harness.pins.expect(("spec_module_kprove", fixture.package), java)
    print(f"PASS {fixture.package}: {LESSON_SPEC} declares its own token and is proven natively and by kprove")


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
        verify_conc(harness, CONC_SMT_LEMMA)
        verify_spec_modules(harness, IMP_SUM)
        verify_lesson_spec(harness, L22_LANGUAGE)
        verify_ml_predicates(harness, L22)
        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-verification-surface-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("verification-surface")
    print("PASS verification-surface")
    return 0


if __name__ == "__main__":
    entry("verification-surface", main, errors=(OSError,))
