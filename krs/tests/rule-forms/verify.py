#!/usr/bin/env python3
"""Rule-forms feature gate: typed binders (KF-009), priority (KF-010), local rewrites (KF-011), nondet (KF-012), heating and cooling (KF-014), contexts (KF-021), anywhere rules (KF-026), fresh values (KF-022), and macros (KF-028).

Each fixture package runs natively through k-rust and through Java K, and
the outcomes must agree:

- `priority`: `#[k::rule(priority = 40)]` beats a default-priority rule on
  the same head, so execution ends in `heads` and native search and
  `krun --search` both reach that one final state; a transition at priority
  250 loses to an `owise` one (priority 200) on both routes; guarded
  equations at priorities 50 to 54, and the same function with an
  `#[k::equation(owise)]` fallback, grade 95/85/75/65/10 identically;
- `nondet`: `#[k::rule(nondet = toss)]` groups two overlapping rules, and
  native search and `krun --search` both reach `heads` and `tails`; bare
  `#[k::strict]` reaches counters 3 and 4 on both routes; two `#[k::rule]`
  fns with complementary guards need no group; the key emits nothing;
- `anywhere`: `#[k::rule(anywhere)]` drops a leading `a` from a right-associative
  `;` sequence at the top, inside `wrap(..)`, and repeatedly on both routes;
  the emitted `reassociate` rule writes its left-nested `(S1 ; S2) ; S3` with
  parentheses, so K reads back the tree KRS lowered; reassociating
  `(b ; c) ; d` is a pinned divergence (k-rust cannot show at load that the
  unrestricted reassociation's self-overlaps join, so it withdraws `;`'s
  value claims and leaves the term unreduced under a residual `#Ceil`; Java
  LLVM reassociates; upstream k-rust/anywhere-nested-own-symbol); each
  emitted rule carries `anywhere` and a
  `// krs-capability: AnywhereRule` comment, `symbols.json` records the
  requirement, and the Java Haskell reference route refuses the definition
  with `krs::capability::unavailable` before anything is kompiled (upstream
  k/anywhere-rules-on-haskell, reviewed, not a request);
- `casts`: typed binder parameters on rule fns. `_e: Exp` narrows the
  `Phrase` argument of `isExpression`, whose `owise` equation declares no
  binders, so `isExpression(1)` and `isExpression(1 + 2)` are `true` and
  `isExpression({})` and `isExpression(true)` are `false`; `i: Int` narrows
  `bar`'s `Exp` field, so `bar(0)` steps through the projection
  `{foo(I +Int 1)}:>Int` to `bar(3)` and `bar(1 + 2)` does not match; the
  emitted rules carry `_E:Exp` and `I:Int`. `baz(12)` projects the block
  `foo(12)` into `Int`, which has no value: a pinned divergence, as for
  KF-013's failing projections (Java K aborts, `undefined`; k-rust ends in a
  stuck leaf and a `#Bottom` leaf; upstream k-rust/undefined-projection-stuck-leaf,
  reviewed, not a request);
- `fresh`: a readable clause with `#[k::fresh(l: Loc)]` and a reference
  `#[k::rule]` fn with `#[k::fresh(t: Int)]` draw from the one shared
  generated counter, so `alloc a; tx; alloc b; tx;` ends with store
  `loc(0) |-> 0 loc(2) |-> 0` and transactions `1 |-> 1 3 |-> 1` natively and
  on Java LLVM; the emitted K declares `freshLoc` as the `freshGenerator` of
  `Loc` and writes `!L:Loc` and `!T:Int`; a fresh binder of a sort without a
  generator, two generators of one sort, and a partial generator each fail
  `krs check` with a pinned diagnostic;
- `macros`: one-way macros and recursive aliases. `#[k::desugar]` emits
  K's `macro`, `#[k::desugar(recursive)]` `macro-rec`, and
  `#[k::alias(recursive)]` `alias-rec`; desugar clauses are plain rules.
  `unless (false) x = 1;` behaves as `if (false) {} else x = 1;` natively
  and on Java LLVM, so program parsing runs the macro expansion on both
  routes; `int x, y, z;` (recursive) declares all three names, while
  `decl x, y, z;` (plain) expands one step to `var x; decl y, z;`, a pinned
  divergence (Java LLVM stops at `decl y, z;`, k-rust refuses to execute a
  state that holds the macro symbol `declareOnce`, by contract: k-rust
  `docs/compatibility.md`, "Macro applications that survive expansion"); and
  `x = nest(1, 2);` stores `pair(1, pair(2, nil))`, which both printers show
  backwards as `nest(1 , 2 , .Ints)`; the desugars `twin` and `anyPair` are
  written in rule patterns, and their clauses list `unbound_variables`
  (K's `unboundVariables(N, Rest)` and `unboundVariables(_)`): `twin`
  matches `pair(3, pair(3, 7))` but not `pair(3, pair(4, 7))`, and `anyPair`
  matches `pair(1, nil)` but not `5`;
- `local-rewrite`: IMP whose `var` and `assign` are single-body
  `#[k::rule]` fns (`k::rewrite!`, K's local `=>`), and `restating-imp`,
  `tests/imp`'s readable IMP. Each runs the IMP corpus natively and on Java
  LLVM, from an initial environment that declares every variable a program
  assigns, and both reach the same final computation and environment on
  every program; the emitted K writes `<k> (Name:Id = Value:Value ; => .K)
  ... </k>` and `<env> Name:Id |-> (_ => Value:Value) ... </env>`. Assigning
  an undeclared variable is the one pinned difference between the two
  definitions: the local form requires the key and is stuck, `map::update`
  adds it; `local-term`'s term-shaped single-body rule
  `pair(k::rewrite!(marked(v) => v), _)` emits `rule pair ( (marked (
  Value:Exp ) => Value:Exp) , _ )` and unmarks `pair(marked(marked(3)),
  marked(4))` to `pair(3, marked(4))` on both routes;
- `heat-cool`: K tutorial lesson 14-A, `+` and `&&` evaluated by
  hand-written `#[k::rule(heat, hole = h)]` and `#[k::rule(cool, hole =
  h)]` rules with KItem freezers (the `&&` rules with `result = Value`), and
  `heat-cool-strict`, lesson 14-D, the same operators with `#[k::seqstrict]`.
  Both run `1 + 2 + 3`, `1 + (2 + 3)`, `true && false`, both `&&`
  bracketings, and the stuck `1 + true` to the same final configuration
  natively and on Java LLVM; the emitted rules carry `HOLE`, `[heat]`,
  `[cool]`, and `result(Value)`; and the native trace of every program has
  the same heat, compute, cool shape in both definitions;
- `contexts`: lesson 14-B, the same operators with term-shaped
  `#[k::context(hole = h)]` fns, K's `context HOLE + _` and
  `context E + HOLE requires isKResult(E)`, runs those programs like
  `heat-cool-strict` natively and on Java LLVM, and its native traces apply
  the `<label>-heat` and `<label>-cool` rules K generates from each context;
  `contexts-lvalue`'s `context ++(HOLE => lvalue(HOLE))` increments a
  variable's location in the store alike on both routes; and
  `contexts-evaluate`'s two context aliases named `translate`, one with
  `<evaluate> false </evaluate>` and one with `<evaluate> true </evaluate>`
  and `result(ExecResult)`, and its `cells!` context on the target of `=`,
  evaluate by the `evaluate` cell's value alike on both routes;
- negative fixtures: `owise` with `priority`, priority 255, the retired
  `#[k::priority(N)]`, `owise` on a simplification, `priority` on an alias
  clause, an unannotated overlap of reference `#[k::rule]` fns, a group with
  one rule, a stale group member, a group mixing priorities, `nondet` on an
  equation, and `anywhere` on a readable clause, on a `cells!` rule, or with
  `priority`, and typed binder lists that declare an unused binder, only some
  binders, or binders out of order, or a declared sort an occurrence cannot
  accept, a desugar clause on an alias production, a desugar or alias
  production without a clause, `requires` on a desugar clause, and `recursive` on a
  desugar clause, and a nested `k::rewrite!`, a right-side name the left
  image does not bind, `k::rewrite!` outside a rule's subject or in a rule
  with a result, and a single-body rule without a rewrite, and a heat rule
  whose hole is not on its left side or is bound there twice, and a context
  whose hole lies outside `k`, whose rewrite does not keep its hole, or
  whose pattern does not bind its hole, each fail
  `krs check` with a pinned diagnostic.

Run it from the repository root; `--record` rewrites the measured pins after
every step passes, and `--refresh-reference` reruns Java K instead of
replaying the per-user reference cache.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError, entry, krs_gate  # noqa: E402
from support.fixture_gate import Fixture, FixtureGate, Program  # noqa: E402
from support.krs import build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import add_refresh_argument  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "Cargo.toml"
PINS = HERE / "pins.json"
FIXTURES = HERE / "fixtures"

PRIORITY = Fixture(MANIFEST, "krs-rule-forms-priority")
PRIORITY_PROGRAMS = (
    Program("toss", "toss", "accepted", "heads", search=("heads",)),
    Program("flip", "flip", "accepted", "high", search=("high",)),
    *(
        Program(f"grade-{percentile}", f"grade({percentile})", "accepted", letter)
        for percentile, letter in (
            (95, "letterA"), (85, "letterB"), (75, "letterC"), (65, "letterD"), (10, "letterF"),
        )
    ),
    *(
        Program(f"grade-owise-{percentile}", f"gradeOwise({percentile})", "accepted", letter)
        for percentile, letter in (
            (95, "letterA"), (85, "letterB"), (75, "letterC"), (65, "letterD"), (10, "letterF"),
        )
    ),
)

CASTS = Fixture(MANIFEST, "krs-rule-forms-casts")
CASTS_PROGRAMS = (
    Program("is-expression-int", "isExpression(1)", "accepted", "true"),
    Program("is-expression-add", "isExpression(1 + 2)", "accepted", "true"),
    Program("is-expression-block", "isExpression({})", "accepted", "false"),
    Program("is-expression-bool", "isExpression(true)", "accepted", "false"),
    Program("bar", "bar(0)", "accepted", "bar(3)"),
    Program("bar-not-int", "bar(1 + 2)", "accepted", "bar(1 + 2)"),
    Program("baz", "baz(4)", "accepted", "4"),
    # A pinned divergence (see pins.json and the module documentation).
    Program("baz-undefined", "baz(12)", "accepted", "undefined"),
)

NONDET = Fixture(MANIFEST, "krs-rule-forms-nondet")
ANYWHERE = Fixture(MANIFEST, "krs-rule-forms-anywhere")
ANYWHERE_PROGRAMS = (
    Program("drop", "a ; b", "accepted", "b"),
    Program("drop-nested", "wrap(a ; b)", "accepted", "wrap(b)"),
    Program("drop-repeated", "a ; a ; c", "accepted", "c"),
    # A pinned divergence: k-rust leaves `(b ; c) ; d` unreduced with a
    # residual `#Ceil(b ; c)`, because the load does not show that the
    # reassociation's self-overlaps join (UnjoinedCriticalPair), so `;` loses
    # its value claims; Java LLVM reassociates. Restricting the first leaf's
    # sort would run natively (upstream k-rust/anywhere-nested-own-symbol).
    Program("reassociate", "(b ; c) ; d", "accepted", "b ; c ; d"),
    Program("reassociate-nested", "wrap((b ; c) ; d)", "accepted", "wrap(b ; c ; d)"),
)
# upstream k/anywhere-rules-on-haskell (reviewed, not a request).
ANYWHERE_REFUSAL = (
    "error[krs::capability::unavailable]: definition contains anywhere rules [drop-a, reassociate]; "
    "K 7.1.337's Haskell backend rejects them (and --allow-anywhere-haskell would drop them); "
    "run this on the LLVM or k-rust route"
)

FRESH = Fixture(MANIFEST, "krs-rule-forms-fresh")
FRESH_PROGRAMS = (
    # One fresh binder per rule: K assigns the counter offsets of several
    # binders of one rule in an unspecified order (k-rust: lexicographic).
    Program(
        "alloc-tx", "alloc a; tx; alloc b; tx;", "accepted", ".K",
        cells=(
            ("env", "a |-> loc(0) b |-> loc(2)"),
            ("store", "loc(0) |-> 0 loc(2) |-> 0"),
            ("txs", "1 |-> 1 3 |-> 1"),
        ),
    ),
)

MACROS = Fixture(MANIFEST, "krs-rule-forms-macros")
MACROS_PROGRAMS = (
    Program("unless-false", "unless (false) x = 1;", "accepted", ".K", cells=(("env", "x |-> 1"),)),
    Program("unless-true", "unless (true) x = 1;", "accepted", ".K", cells=(("env", ".Map"),)),
    Program("if-else", "if (false) {} else x = 1;", "accepted", ".K", cells=(("env", "x |-> 1"),)),
    Program(
        "int-recursive", "int x, y, z;", "accepted", ".K",
        cells=(("env", "x |-> 0 y |-> 0 z |-> 0"),),
    ),
    # A pinned divergence: a plain desugar applies once, so `decl y, z;` is
    # left in the program. Java K runs `var x;` and stops at it; k-rust
    # refuses to execute a state that still holds a macro symbol.
    Program("decl-one-step", "decl x, y, z;", "accepted", "decl y , z , .Ids;"),
    # `nest(1, 2)` runs forward as `pair(1, pair(2, nil))`; both printers
    # apply the alias-rec clauses backwards.
    Program(
        "nest", "x = nest(1, 2);", "accepted", ".K",
        cells=(("env", "x |-> nest(1 , 2 , .Ints)"),),
    ),
    # `twin` and `anyPair` expand into the rules that use them as patterns;
    # `unbound_variables` lets their results name `n` and `_`.
    Program(
        "twin-match", "twin a = pair(3, pair(3, 7));", "accepted", ".K",
        cells=(("env", "a |-> 1"),),
    ),
    Program(
        "twin-mismatch", "twin a = pair(3, pair(4, 7));", "accepted",
        "twin a = pair(3, pair(4, 7));",
    ),
    Program(
        "ispair-match", "ispair b = pair(1, nil);", "accepted", ".K",
        cells=(("env", "b |-> 1"),),
    ),
    Program("ispair-int", "ispair b = 5;", "accepted", "ispair b = 5;"),
)

LOCAL_REWRITE = Fixture(MANIFEST, "krs-rule-forms-local-rewrite")
RESTATING_IMP = Fixture(MANIFEST, "krs-rule-forms-restating-imp")
EXPRESSION_WRAPPER = "result = {expression};"
# The IMP corpus: (program, initial environment, final environment). The
# initial environment declares every variable the program assigns, which
# the local `assign` requires.
LOCAL_REWRITE_CORPUS = (
    ("tests/imp/corpus/expr/accepted/arithmetic-precedence.expr", "result |-> 0", "result |-> 7"),
    ("tests/imp/corpus/expr/accepted/boolean-precedence.expr", "result |-> 0", "result |-> true"),
    ("tests/imp/corpus/expr/accepted/comparison-equality.expr", "result |-> 0", "result |-> true"),
    ("tests/imp/corpus/expr/accepted/division-left.expr", "result |-> 0", "result |-> 1"),
    ("tests/imp/corpus/expr/accepted/division-parenthesized.expr", "result |-> 0", "result |-> 4"),
    ("tests/imp/corpus/expr/accepted/parentheses-override.expr", "result |-> 0", "result |-> 9"),
    ("tests/imp/corpus/expr/accepted/short-circuit-precedence.expr", "result |-> 0", "result |-> true"),
    ("tests/imp/corpus/expr/accepted/subtraction-left.expr", "result |-> 0", "result |-> 3"),
    ("tests/imp/corpus/expr/accepted/unary-binding.expr", "result |-> 0", "result |-> 1"),
    ("tests/imp/corpus/accepted/iterated-unary.expr", "result |-> 0", "result |-> true"),
    ("tests/imp-state/corpus/accepted/initial-environment.calc", "x |-> 41 y |-> 0", "x |-> 41 y |-> 42"),
    ("tests/imp-state/corpus/accepted/lookup-evaluation-order.calc", "x |-> 0 y |-> 0", "x |-> 2 y |-> 8"),
    ("tests/imp-state/corpus/accepted/right-associated-sequence.calc", "x |-> 0 y |-> 0 z |-> 0", "x |-> 1 y |-> 2 z |-> 3"),
    ("tests/imp-state/corpus/accepted/single-assignment.calc", "x |-> 0", "x |-> 1"),
    ("tests/imp-state/corpus/accepted/update-existing.calc", "x |-> 0", "x |-> 5"),
    ("tests/imp-control-flow/corpus/accepted/block-sequence.imp", "x |-> 0 y |-> 0 z |-> 0", "x |-> 1 y |-> 2 z |-> 3"),
    ("tests/imp-control-flow/corpus/accepted/dangling-else.imp", "x |-> 0 y |-> 0", "x |-> 1 y |-> 0"),
    ("tests/imp-control-flow/corpus/accepted/empty-block.imp", ".Map", ".Map"),
    ("tests/imp-control-flow/corpus/accepted/explicit-else.imp", "x |-> 0", "x |-> 2"),
    ("tests/imp-control-flow/corpus/accepted/if-false.imp", "x |-> 0", "x |-> 0"),
    ("tests/imp-control-flow/corpus/accepted/if-true.imp", "x |-> 0", "x |-> 1"),
    ("tests/imp-control-flow/corpus/accepted/nested-control.imp", "x |-> 0", "x |-> 0"),
    ("tests/imp-control-flow/corpus/accepted/while-followed.imp", "x |-> 0 y |-> 0", "x |-> 0 y |-> 1"),
)
# Assigning an undeclared variable: the one difference between the two
# definitions (the register's X14 known divergence, between definitions).
UNDECLARED = "tests/imp-state/corpus/accepted/single-assignment.calc"
UNDECLARED_OUTCOMES = {
    "local-rewrite": ("x = 1;", ".Map"),
    "restating-imp": (".K", "x |-> 1"),
}

LOCAL_TERM = Fixture(MANIFEST, "krs-rule-forms-local-term")
LOCAL_TERM_PROGRAMS = (
    Program("unmark", "pair(marked(1), 2)", "accepted", "pair(1, 2)"),
    Program("unmark-twice", "pair(marked(marked(3)), marked(4))", "accepted", "pair(3, marked(4))"),
    Program("unmarked", "pair(1, 2)", "accepted", "pair(1, 2)"),
)

HEAT_COOL = Fixture(MANIFEST, "krs-rule-forms-heat-cool")
HEAT_COOL_STRICT = Fixture(MANIFEST, "krs-rule-forms-heat-cool-strict")
HEAT_COOL_PROGRAMS = (
    Program("add-left", "1 + 2 + 3", "accepted", "6"),
    Program("add-right", "1 + (2 + 3)", "accepted", "6"),
    Program("and", "true && false", "accepted", "false"),
    Program("and-left", "(true && false) && true", "accepted", "false"),
    Program("and-right", "true && (false && true)", "accepted", "false"),
    Program("stuck", "1 + true", "accepted", "1 + true"),
)

CONTEXTS = Fixture(MANIFEST, "krs-rule-forms-contexts")
CONTEXTS_LVALUE = Fixture(MANIFEST, "krs-rule-forms-contexts-lvalue")
CONTEXTS_LVALUE_PROGRAMS = (
    Program(
        "increment", "++ x", "accepted", "2",
        variables=(("STORE", "x |-> 1"),), cells=(("store", "x |-> 2"),),
    ),
    Program(
        "increment-other", "++ y", "accepted", "6",
        variables=(("STORE", "x |-> 1 y |-> 5"),), cells=(("store", "x |-> 1 y |-> 6"),),
    ),
)
CONTEXTS_EVALUATE = Fixture(MANIFEST, "krs-rule-forms-contexts-evaluate")
CONTEXTS_EVALUATE_PROGRAMS = tuple(
    Program(
        f"{name}-{'translate' if evaluate == 'true' else 'run'}", text, "accepted", run,
        variables=(("EVALUATE", evaluate), ("ENV", "x |-> 2")),
    )
    for name, text, evaluate, run in (
        ("twice-name", "twice(x)", "false", "4"),
        ("twice-name", "twice(x)", "true", "x + x"),
        ("twice-sum", "twice(1 + 2)", "false", "6"),
        ("twice-sum", "twice(1 + 2)", "true", "6"),
        ("assign", "(1 + 2) = x", "false", "1 + 2 = x"),
        ("assign", "(1 + 2) = x", "true", "3 = x"),
    )
)

COUNTER = (("COUNTER", "1"),)
NONDET_PROGRAMS = (
    Program("toss", "toss", "accepted", None, search=("heads", "tails"), variables=COUNTER),
    Program("strict-order", "add(inc, dbl)", "accepted", None, search=("3", "4"), variables=COUNTER),
    Program("div", "div(6, 3)", "accepted", "2", variables=COUNTER),
    Program("div-zero", "div(1, 0)", "accepted", "divByZero", variables=COUNTER),
)

NEGATIVE = (
    "owise-with-priority",
    "priority-out-of-range",
    "retired-priority",
    "owise-simplification",
    "priority-alias",
    "unannotated-overlap",
    "single-member-group",
    "stale-member",
    "mixed-priorities",
    "nondet-equation",
    "anywhere-readable",
    "anywhere-cells",
    "anywhere-priority",
    "binder-unused",
    "binder-partial",
    "binder-misordered",
    "binder-incompatible",
    "fresh-no-generator",
    "fresh-two-generators",
    "fresh-partial-generator",
    "desugar-mode-mismatch",
    "desugar-without-clause",
    "alias-without-clause",
    "desugar-requires",
    "desugar-clause-payload",
    "local-rewrite-nested",
    "local-rewrite-unbound",
    "local-rewrite-outside",
    "local-rewrite-with-result",
    "local-rewrite-unchanged",
    "heat-cool-hole-not-left",
    "heat-cool-hole-twice",
    "context-hole-outside-k",
    "context-bad-rewrite",
    "context-hole-absent",
)


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


def emitted_attributes(emitted, fragments: tuple[str, ...]) -> None:
    source = emitted.source.read_text(encoding="utf-8")
    for fragment in fragments:
        if fragment not in source:
            raise GateError(f"{emitted.fixture.package}: emitted K omits {fragment!r}")


def verify_anywhere(harness: FixtureGate, pins: Ledger) -> None:
    """Anywhere rules run natively and on Java LLVM; the Java Haskell route refuses them."""

    harness.check(ANYWHERE)
    harness.expand(ANYWHERE)
    emitted = harness.emit(ANYWHERE)
    emitted_attributes(emitted, (
        "  // krs-capability: AnywhereRule reassociate\n"
        "  rule (S1:Stmt ; S2:Stmt) ; S3:Stmt => S1:Stmt ; S2:Stmt ; S3:Stmt [anywhere, label(reassociate)]",
        "  // krs-capability: AnywhereRule drop-a\n  rule a ; S:Stmt => S:Stmt [anywhere, label(drop-a)]",
    ))
    symbols = json.loads((emitted.directory / "symbols.json").read_text(encoding="utf-8"))
    requirements = symbols.get("capability_requirements")
    if sorted((row["feature"], row["symbol"]) for row in requirements or ()) != [
        ("AnywhereRule", "drop-a"), ("AnywhereRule", "reassociate"),
    ]:
        raise GateError(f"symbols.json records {requirements!r} as the capability requirements")
    harness.compare(emitted, ANYWHERE_PROGRAMS, sort="Stmt")
    for route in ("native-rust", "native-llvm", "java-llvm-reference"):
        krs_gate.require_route(harness.gate, emitted.directory, route, environment=harness.environment)
    # The Java Haskell reference step stops at the capability check, before kompile.
    try:
        krs_gate.require_route(
            harness.gate, emitted.directory, "java-haskell-reference", environment=harness.environment,
        )
    except GateError as refusal:
        message = str(refusal)
    else:
        raise GateError("the java-haskell-reference route accepted a definition with anywhere rules")
    if message != ANYWHERE_REFUSAL:
        raise GateError(f"java-haskell-reference refusal changed:\n{message}")
    pins.expect(("capability_refusals", "java-haskell-reference"), message)


def verify_fresh(harness: FixtureGate) -> None:
    """Fresh binders draw from the shared generated counter on both routes."""

    harness.check(FRESH)
    harness.expand(FRESH)
    emitted = harness.emit(FRESH)
    emitted_attributes(emitted, (
        'syntax Loc ::= "freshLoc" "(" Int ")" [symbol(freshLoc), function, total, freshGenerator]',
        "<env> E:Map => E:Map [ X:Id <- !L:Loc ] </env>",
        "<store> S:Map => S:Map [ !L:Loc <- 0 ] </store>",
        "<txs> Ts:Map => Ts:Map [ !T:Int <- 1 ] </txs>",
        # `!T:Int` draws from K's `freshInt`, declared in INT, not INT-SYNTAX.
        "  imports INT\n",
    ))
    harness.compare(emitted, FRESH_PROGRAMS, sort="Stmt")


def verify_macros(harness: FixtureGate) -> None:
    """Desugar and recursive alias productions expand programs alike on both routes."""

    harness.check(MACROS)
    harness.expand(MACROS)
    emitted = harness.emit(MACROS)
    emitted_attributes(emitted, (
        '"unless" "(" Expr ")" Stmt [symbol(unless), macro,',
        '"int" Ids ";" [symbol(declareMany), macro-rec,',
        '"decl" Ids ";" [symbol(declareOnce), macro,',
        '"nest" "(" Ints ")" [symbol(nest), alias-rec,',
        "rule unless ( C:Expr ) S:Stmt => if ( C:Expr ) { } else S:Stmt [label(",
        "rule int X:Id , Y:Id , Rest:Ids ; => var X:Id ; int Y:Id , Rest:Ids ; [label(",
        "rule nest ( I:Int , Is:Ints ) => pair ( I:Int , nest ( Is:Ints ) ) [label(",
        "rule twin => pair ( N:Int , pair ( N:Int , Rest:Value ) ) [unboundVariables(N, Rest), label(",
        "rule anyPair => pair ( _ , _ ) [unboundVariables(_), label(",
    ))
    harness.compare(emitted, MACROS_PROGRAMS, sort="Stmt")


def corpus_text(path: str) -> str:
    text = (ROOT / path).read_text(encoding="utf-8").strip()
    return EXPRESSION_WRAPPER.format(expression=text) if path.endswith(".expr") else text


def local_rewrite_programs(definition: str) -> tuple[Program, ...]:
    """The IMP corpus, and the undeclared assignment, with `definition`'s outcome."""

    programs = [
        Program(
            Path(path).stem, corpus_text(path), "accepted", ".K",
            variables=(("ENV", initial),), cells=(("env", final),),
        )
        for path, initial, final in LOCAL_REWRITE_CORPUS
    ]
    run, environment = UNDECLARED_OUTCOMES[definition]
    programs.append(Program(
        "undeclared-assignment", corpus_text(UNDECLARED), "accepted", run,
        variables=(("ENV", ".Map"),), cells=(("env", environment),),
    ))
    return tuple(programs)


def verify_local_rewrite(harness: FixtureGate, pins: Ledger) -> None:
    """Single-body var and assign run the IMP corpus like the restating IMP, except an undeclared assignment."""

    harness.check(LOCAL_REWRITE)
    harness.expand(LOCAL_REWRITE)
    emitted = harness.emit(LOCAL_REWRITE)
    emitted_attributes(emitted, (
        "  rule [assign]:\n"
        "    <k> (Name:Id = Value:Value ; => .K) ... </k>\n"
        "    <env> Name:Id |-> (_ => Value:Value) ... </env>\n",
        "  rule [var]:\n"
        "    <k> (Name:Id => Value:Value) ... </k>\n"
        "    <env> Name:Id |-> Value:Value ... </env>\n",
    ))
    local = harness.compare(emitted, local_rewrite_programs("local-rewrite"), sort="Stmt")
    harness.check(RESTATING_IMP)
    restating = harness.emit(RESTATING_IMP)
    restated = harness.compare(restating, local_rewrite_programs("restating-imp"), sort="Stmt")
    differing = sorted(name for name in local if local[name] != restated[name])
    if differing != ["undeclared-assignment"]:
        raise GateError(f"local and restating IMP differ on {differing}, expected only the undeclared assignment")
    pins.expect(("definition_divergences", "local-rewrite", "undeclared-assignment"), {
        "local-rewrite": local["undeclared-assignment"],
        "restating-imp": restated["undeclared-assignment"],
    })
    harness.check(LOCAL_TERM)
    harness.expand(LOCAL_TERM)
    term = harness.emit(LOCAL_TERM)
    emitted_attributes(term, (
        "  rule pair ( (marked ( Value:Exp ) => Value:Exp) , _ ) [label(unmark-left)]\n",
    ))
    harness.compare(term, LOCAL_TERM_PROGRAMS, sort="Exp")


def step_shape(trace: list[dict]) -> list[str]:
    """A trace's steps as `heat`, `cool`, or the label of the computing rule.

    Hand-written rules are labelled `heat-..` and `cool-..`; the rules K
    generates for strictness are labelled `..-heat` and `..-cool`.
    """

    shape = []
    for step in trace:
        label = step["label"].rsplit(".", 1)[-1]
        if label.startswith("heat-") or label.endswith("-heat"):
            shape.append("heat")
        elif label.startswith("cool-") or label.endswith("-cool"):
            shape.append("cool")
        else:
            shape.append(label)
    return shape


def native_shapes(harness: FixtureGate, emitted, programs: tuple[Program, ...]) -> dict[str, list[str]]:
    with krs_gate.Session(harness.gate, environment=harness.environment) as session:
        session.load(emitted.definition_ir, emitted.main_module)
        return {
            program.name: step_shape(session.exec_run(program=program.text, trace=True)["trace"])
            for program in programs
        }


def verify_heat_cool(harness: FixtureGate, pins: Ledger) -> None:
    """Hand-written heating and cooling run like the seqstrict definition, step for step."""

    harness.check(HEAT_COOL)
    harness.expand(HEAT_COOL)
    emitted = harness.emit(HEAT_COOL)
    emitted_attributes(emitted, (
        "  rule [heat-add-rhs]:\n"
        "    <k> E:Exp + HOLE:Exp => HOLE:Exp ~> freezer1 ( E:Exp ) ... </k>\n"
        "    requires isKResult(E:Exp)\n"
        "    [heat]\n",
        "  rule [cool-add-rhs]:\n"
        "    <k> HOLE:Exp ~> freezer1 ( E:Exp ) ~> Tail:K => E:Exp + HOLE:Exp ~> Tail:K </k>\n"
        "    [cool]\n",
        "    <k> HOLE:Exp && E:Exp => HOLE:Exp ~> freezer4 ( E:Exp ) ... </k>\n"
        "    [heat, result(Value)]\n",
        "[cool, result(Value)]",
    ))
    hand = harness.compare(emitted, HEAT_COOL_PROGRAMS, sort="Exp")
    harness.check(HEAT_COOL_STRICT)
    strict_emitted = harness.emit(HEAT_COOL_STRICT)
    strict = harness.compare(strict_emitted, HEAT_COOL_PROGRAMS, sort="Exp")
    if hand != strict:
        raise GateError(f"hand-written heating and seqstrict differ: {hand} vs {strict}")
    hand_shapes = native_shapes(harness, emitted, HEAT_COOL_PROGRAMS)
    strict_shapes = native_shapes(harness, strict_emitted, HEAT_COOL_PROGRAMS)
    if hand_shapes != strict_shapes:
        raise GateError(f"native trace shapes differ: hand {hand_shapes}, seqstrict {strict_shapes}")
    if hand_shapes["add-left"] != ["heat", "add", "cool", "add"]:
        raise GateError(f"1 + 2 + 3 traced {hand_shapes['add-left']}, expected heat, add, cool, add")
    pins.expect(("trace_shapes", "heat-cool"), hand_shapes)


def native_labels(harness: FixtureGate, emitted, program: Program) -> list[str]:
    with krs_gate.Session(harness.gate, environment=harness.environment) as session:
        session.load(emitted.definition_ir, emitted.main_module)
        trace = session.exec_run(program=program.text, trace=True)["trace"]
        return [step["label"] for step in trace]


def verify_contexts(harness: FixtureGate, pins: Ledger) -> None:
    """Contexts run lesson 14 like seqstrict, rewrite a hole to an lvalue, and follow another cell."""

    harness.check(CONTEXTS)
    harness.expand(CONTEXTS)
    emitted = harness.emit(CONTEXTS)
    emitted_attributes(emitted, (
        "  context [add-lhs]: HOLE:Exp + _\n",
        "  context [add-rhs]: E:Exp + HOLE:Exp\n    requires isKResult(E:Exp)\n",
        "  context [and-rhs]: E:Exp && HOLE:Exp\n    requires isValue(E:Exp)\n    [result(Value)]\n",
    ))
    contexts = harness.compare(emitted, HEAT_COOL_PROGRAMS, sort="Exp")
    strict_emitted = harness.emit(HEAT_COOL_STRICT)
    strict = harness.compare(strict_emitted, HEAT_COOL_PROGRAMS, sort="Exp")
    if contexts != strict:
        raise GateError(f"contexts and seqstrict differ: {contexts} vs {strict}")
    shapes = native_shapes(harness, emitted, HEAT_COOL_PROGRAMS)
    strict_shapes = native_shapes(harness, strict_emitted, HEAT_COOL_PROGRAMS)
    if shapes != strict_shapes:
        raise GateError(f"native trace shapes differ: contexts {shapes}, seqstrict {strict_shapes}")
    labels = native_labels(harness, emitted, HEAT_COOL_PROGRAMS[0])
    generated = [label.rsplit(".", 1)[-1] for label in labels if label.endswith(("-heat", "-cool"))]
    if generated != ["add-lhs-heat", "add-lhs-cool"]:
        raise GateError(f"1 + 2 + 3 applied {labels}, expected the generated add-lhs heat and cool rules")
    pins.expect(("trace_labels", "contexts", "add-left"), labels)

    harness.check(CONTEXTS_LVALUE)
    harness.expand(CONTEXTS_LVALUE)
    lvalue = harness.emit(CONTEXTS_LVALUE)
    emitted_attributes(lvalue, (
        "  context [increment-target]: ++ (HOLE:Exp => lvalue ( HOLE:Exp ))\n",
    ))
    harness.compare(lvalue, CONTEXTS_LVALUE_PROGRAMS, sort="Exp")

    harness.check(CONTEXTS_EVALUATE)
    harness.expand(CONTEXTS_EVALUATE)
    evaluate = harness.emit(CONTEXTS_EVALUATE)
    emitted_attributes(evaluate, (
        "  context alias [translate]:\n    <k> HERE ~> Tail:K </k>\n    <evaluate> false </evaluate>\n",
        "  context alias [translate]:\n    <k> HERE ~> Tail:K </k>\n    <evaluate> true </evaluate>\n"
        "    [result(ExecResult)]\n",
        "  context [assign-target]:\n    <k> HOLE:Exp = _ ... </k>\n    <evaluate> true </evaluate>\n"
        "    [result(ExecResult)]\n",
    ))
    harness.compare(evaluate, CONTEXTS_EVALUATE_PROGRAMS, sort="Exp")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 rule-forms ledger")

    target = checkout_scratch() / "rule-forms-target"
    environment = {**z3_environment(), "CARGO_TARGET_DIR": os.fspath(target), "CARGO_TERM_COLOR": "never"}
    krs = build(environment, target=target)
    gate = krs_gate.configured_or_build(target)
    check_packages("rule-forms", krs=krs, env=environment, target_dir=target)

    with tempfile.TemporaryDirectory(prefix="krs-rule-forms-") as temporary:
        workspace = Path(temporary)
        harness = FixtureGate(
            "rule-forms", pins, workspace, krs, gate, environment,
            refresh=arguments.refresh_reference,
            divergences=pins.get("known_divergences", {}),
        )

        harness.check(CASTS)
        harness.expand(CASTS)
        casts = harness.emit(CASTS)
        emitted_attributes(casts, (
            "rule isExpression ( _E:Exp ) => true [label(",
            "rule isExpression ( _ ) => false [priority(200), label(",
            "rule bar ( I:Int ) => bar ( {foo ( I:Int +Int 1 )}:>Int )\n    requires I:Int <Int 3 [label(",
            "rule baz ( I:Int ) => {foo ( I:Int )}:>Int [label(",
        ))
        harness.compare(casts, CASTS_PROGRAMS, sort="Phrase")
        print("PASS casts: typed binders narrow isExpression and bar, projections step bar(0) to bar(3), baz(12) a pinned divergence")

        harness.check(PRIORITY)
        harness.expand(PRIORITY)
        priority = harness.emit(PRIORITY)
        emitted_attributes(priority, (
            "rule toss => heads [priority(40), label(",
            "rule [flip-low]:",
            "[priority(250)]",
            "[priority(200)]",
            "rule gradeOwise ( _ ) => letterF [priority(200), label(",
            "rule grade ( _ ) => letterF [priority(54), label(",
        ))
        harness.compare(priority, PRIORITY_PROGRAMS, sort="Pgm", search=True)
        print("PASS priority: priority 40 wins, owise (200) beats priority 250, equation priorities and owise grade alike")

        harness.check(NONDET)
        harness.expand(NONDET)
        nondet = harness.emit(NONDET)
        if "nondet" in nondet.source.read_text(encoding="utf-8"):
            raise GateError("the check-only nondet key reached the emitted K")
        harness.compare(nondet, NONDET_PROGRAMS, sort="Exp", search=True)
        print("PASS nondet: toss reaches heads and tails, strictness order reaches 3 and 4, guards separate div")

        verify_anywhere(harness, pins)
        print("PASS anywhere: drop-a at any depth on both routes, reassociation a pinned k-rust divergence, Java Haskell refused before kompile")

        verify_fresh(harness)
        print("PASS fresh: !L:Loc and !T:Int share the generated counter natively and on Java LLVM")

        verify_local_rewrite(harness, pins)
        print("PASS local-rewrite: single-body var and assign run the IMP corpus like the restating IMP natively and on Java LLVM; an undeclared assignment is stuck in the local form; a term-shaped single-body rule unmarks a pair")

        verify_heat_cool(harness, pins)
        print("PASS heat-cool: hand-written heat and cool rules with freezers run lesson 14 like seqstrict natively and on Java LLVM, step for step")

        verify_contexts(harness, pins)
        print("PASS contexts: term-shaped contexts run lesson 14 like seqstrict natively and on Java LLVM through the generated heat and cool rules; an lvalue context increments the store; two translate aliases and a cells! context follow the evaluate cell")

        verify_macros(harness)
        print("PASS macros: unless desugars to if/else, macro-rec expands fully and macro one step, alias-rec prints backwards, unboundVariables desugars match as patterns on both routes")

        for name in NEGATIVE:
            manifest = materialize(name, workspace)
            message = harness.diagnostic(name, Fixture(manifest, f"krs-rule-forms-{name}"))
            print(f"PASS negative {name}: {message.splitlines()[0]}")

    pins.finish("rule-forms")
    print("PASS rule-forms")
    return 0


if __name__ == "__main__":
    entry("rule-forms", main, errors=(OSError,))
