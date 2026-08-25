# R9: Evaluation strategy and static/equational forms

## Decision

The remaining forms do not require a Rust parser fork and do not overturn the
R3 refutable-clause design. They do require KRS to stop treating every
declarative function item as the same kind of rule.

Use this split:

| K concept | KRS surface | Normalized meaning |
|---|---|---|
| `strict`, `seqstrict`, `result`, `hybrid` | typed attributes on a production struct/variant | evaluation-strategy declaration which generates contexts and result-predicate equations |
| explicit `context` | attributed, zero-return refutable function item | one context template with a distinguished hole |
| `context alias` | attributed, zero-return refutable function item with a name and `HERE` binding | reusable context template instantiated by strictness attributes |
| macro / alias rule | attributed refutable clause whose root production carries the same static mode | compile-time term rewrite; alias also reverses for unparsing |
| `anywhere` | `#[k::anywhere]` refutable clause | equation-like rewrite at any occurrence, subject to target capability |
| simplification | R7's `#[k::simplification(...)]` refutable clause | backend simplification lemma, not a transition or ordinary equation |
| anonymous `#fun` | recognized `k::fun(argument, |pattern| term)` term combinator | generated one-clause function with captured variables |
| function context | an explicit `k::Global(...)` pattern parameter on an equation | read-only global-configuration dependency threaded by the K frontend |

Attributes are appropriate when metadata modifies a nominal production.
Refutable function items remain appropriate when one declaration has binders,
a left pattern, and optionally a right term. A compiler-owned term, sequence,
collection, or configuration-fragment macro remains necessary only where the
pattern is not expressible in Rust's pattern grammar. There is no reason to
put all contexts or all static rules inside a large DSL.

The normalized IR must retain these as different sentence kinds until K text
emission. In particular, it must not eagerly turn a context into hand-written
state transitions, a macro into an executable equation, or `#fun` into host
closure execution. R6's initial `.k` target should emit the corresponding
source-level K form and let the pinned K frontend perform freezer generation,
macro expansion, and hidden-configuration threading.

## Production evaluation attributes

Use named Rust fields instead of K's one-based nonterminal positions. The R4
`sequence` spelling remains suitable:

```rust
#[k::syntax("{lhs} + {rhs}")]
#[k::seqstrict(sequence = [lhs, rhs])]
pub struct Add {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::syntax("{condition} && {continuation}")]
#[k::strict(sequence = [condition])]
pub struct And {
    pub condition: Term<dyn Expr>,
    pub continuation: Term<dyn Expr>,
}
```

`strict` creates independently applicable contexts for the selected fields,
so more than one argument may be heated next. `seqstrict` creates the same
contexts but requires every earlier selected field to satisfy the chosen
result predicate before a later field is heated. The list order therefore
matters for `seqstrict`; source order of separate rules still does not.

`#[k::strict]` and `#[k::seqstrict]` select all term fields in declaration
order. KRS should reject a selected grammar terminal, a missing field, an
arity-zero production, a production without a symbol, and a field of sort
`K`. Current K specifically rejects heating sort `K` and recommends `KItem`.

The stopping predicate defaults to the open `KResult` sort selected in R2.
An override is a sort, not a Rust return type:

```rust
#[k::syntax("assert({condition})")]
#[k::strict(sequence = [condition])]
#[k::result(Bool)]
pub struct Assert {
    pub condition: Term<dyn Expr>,
}
```

This causes generated heat/cool conditions to use `isBool(hole)` rather than
`isKResult(hole)`. The named sort must exist, or an explicitly declared
predicate with the expected `isSort(K) -> Bool` contract must exist. `result`
is also legal on an explicit context, a context alias, and an explicit
heat/cool rule.

`hybrid` says that the enclosing production is itself a result when all of its
selected strict arguments are results:

```rust
#[k::syntax("{lhs} || {rhs}")]
#[k::strict(sequence = [lhs])]
#[k::hybrid]
pub struct Or {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::hybrid(results = [KResult, StaticValue])]
#[k::seqstrict(sequence = [callee, argument])]
pub struct Call {
    pub callee: Term<dyn Expr>,
    pub argument: Term<dyn Expr>,
}
```

The empty form means `KResult`; the list form generates one predicate equation
per named sort. K's current frontend considers all fields selected across the
strictness groups collectively. KRS should reject `hybrid` without `strict` or
`seqstrict`, because the current frontend only resolves it while resolving a
strict production.

### Named context-alias groups

K allows one production to use different context aliases for different
positions. Repeated typed attributes are clearer than reproducing K's
semicolon/comma string syntax:

```rust
#[k::seqstrict(using = lookup, sequence = [receiver])]
#[k::seqstrict(using = execute, sequence = [argument])]
pub struct Invoke {
    pub receiver: Term<dyn Expr>,
    pub argument: Term<dyn Expr>,
}
```

KRS combines repeated groups into one target `seqstrict` attribute in their
source order. With `seqstrict`, the second group is constrained by selected
positions in the first group as well as earlier positions in its own group.
With `strict`, groups remain nondeterministic.

Several context aliases may share a name; each produces a context for each
selected field. A result sort on a named context alias controls its generated
context. Current `ResolveStrict` takes that result from the alias, rather than
from the production's default alias, so KRS should diagnose a production-level
`result` combined with named aliases unless every effective alias result is
unambiguous.

## Explicit contexts

A context is not a transition clause with a post-state. Represent it as an
empty-bodied declaration with one existing pattern binding designated as the
hole:

```rust
#[k::context(hole = operand)]
fn evaluate_left(term![Add(operand, _)]: Term<dyn Expr>) {}

#[k::context(hole = operand)]
#[k::requires(is_assignable(operand))]
#[k::result(Value)]
fn assignment_target(
    Machine {
        k: k![Assign(operand, _), _tail @ ..],
        mode: Running,
        ..
    }: Machine,
) {
}
```

This is valid Rust outer grammar but, like an R3 rule clause, it is a KRS
declaration rather than a callable Rust function. The first example emits a K
context without an explicit computation cell; K inserts it into the main cell.
The second emits a configuration context and can constrain other cells.
`#[k::requires]` on a context is a `Term<Bool>` under R7 and is appended to the
generated **heating** rule only. Cooling does not inherit that condition.

K contexts may transform the hole before evaluating it. Rust has no local
rewrite expression, so make the exceptional part explicit without hiding the
whole context:

```rust
#[k::context(hole = operand)]
#[k::heat_as(term![ToLValue(operand)])]
fn evaluate_as_lvalue(term![Deref(operand)]: Term<dyn Expr>) {}
```

This emits the equivalent of `context Deref(HOLE => ToLValue(HOLE))`.
KRS checks that the designated hole is on the left of the sole transformation
and that the transformed term is well sorted. This is preferable to pretending
the context function returns `ToLValue(operand)`, which would incorrectly say
the whole context rewrites to that term.

For configuration bags, dynamic/open terms, K sequences, and associative
collections, the parameter pattern can use the `term!`, `fragment!`, `k!`, and
collection-pattern islands selected by R1/R2/R3/R5. An advanced typed
`k::context!` item island is still reasonable for target-valid contexts that
cannot be represented by one Rust parameter pattern. `k::raw_k!` remains the
last resort, not the normal arbitrary-context form.

The frontend validations that belong in KRS are:

- the context has a designated hole and no post term;
- there is at most one hole transformation, and only the hole is rewritten;
- the hole is not of sort `K`;
- all other names obey the same binding/RHS checks as rule patterns; and
- `result`, `requires`, labels, and source spans survive lowering.

The generated freezer symbol and the heat/cool labels are implementation
details of the pinned K frontend. Do not make their current generated names
part of the KRS language ABI.

## Context aliases

Use the same declaration shape with an explicit alias-group name and a binding
designated as `HERE`:

```rust
#[k::context_alias(name = execute, here = site)]
fn execute_normally(
    fragment![Machine {
        k: k![site, _tail @ ..],
        evaluate: false,
        ..
    }]: k::Fragment<Machine>,
) {
}

#[k::context_alias(name = execute, here = site)]
#[k::result(ExecResult)]
fn execute_during_translation(
    fragment![Machine {
        k: k![site, _tail @ ..],
        evaluate: true,
        ..
    }]: k::Fragment<Machine>,
) {
}
```

Both declarations intentionally share `name = execute`; their Rust item names
remain unique. Instantiating `#[k::strict(using = execute, ...)]` produces both
contexts for every selected field. The `here` name is a placeholder for the
entire production instance, whereas the `hole` name in a context is the term
being evaluated; the IR must not collapse them into one binder kind.

The common alias has just a template and optional Boolean requirement/result
sort. K's `[context(label)]` convenience, which wraps the hole before heating,
can be represented by `#[k::context_wrapper(label)]`. More elaborate alias
templates stay in `fragment!` or the typed context island.

## Macros and aliases

Use `desugar` rather than the Rust keyword-looking name `macro` for the common
surface. Mark both the production and each static clause so an AI reader does
not mistake the clause for an executable transition:

```rust
#[k::syntax("if ({condition}) {then_branch}")]
#[k::desugar]
pub struct IfWithoutElse {
    pub condition: Term<dyn Expr>,
    pub then_branch: Term<Statement>,
}

impl Statement for IfWithoutElse {}

#[k::desugar]
fn add_empty_else(
    term![IfWithoutElse(condition, then_branch)]: Term<Statement>,
) -> Term<Statement> {
    term![IfElse(condition, then_branch, EmptyBlock)]
}
```

`#[k::desugar(recursive)]` maps to K's `macro-rec`. The unqualified form maps
to `macro`, whose expansion does not reapply the same clause inside its own
expansion. Other macros and child terms still expand. Recursive expansion has
no termination check in K and KRS cannot promise one.

An alias uses the same clause shape:

```rust
#[k::alias]
pub struct PrettyEmpty;

impl Statement for PrettyEmpty {}

#[k::alias]
fn pretty_empty(term![PrettyEmpty]: Term<Statement>) -> Term<Statement> {
    term![VerboseEmptyBlock]
}
```

It expands left-to-right during compilation and initial-configuration
processing, then right-to-left before final unparsing. `#[k::alias(recursive)]`
maps to `alias-rec`. This is a presentation round trip, not a bidirectional
runtime equality. KRS must preserve the distinction in both the IR and tests.

Static clauses use R3/R7 patterns and binder analysis, but have a deliberately
narrower contract:

- the left root resolves to a production with the same `desugar`/`alias` mode;
- no `requires` or `ensures` condition is allowed (sort refinements in the
  pattern remain legal);
- no fresh/existential/unbound binder is inferred from ordinary Rust control
  flow; target-supported RHS-only macro variables are represented explicitly
  in static-pattern IR;
- a priority, if supplied, is static-expansion priority and is retained as
  such; and
- macro symbols remaining after expansion are an error, matching the frontend.

The target K frontend actually propagates the production's macro/alias
attribute to ordinary rules rooted at that production. Requiring the repeated
KRS clause marker is intentional semantic punctuation; emission need only put
the target attribute where K expects it.

This section concerns K's syntactic macros and aliases. Matching-logic alias
declarations are a different feature and remain in R7's postponed logic/raw
surface.

## Anywhere rules and simplification equations

The R3 clause shape works for both, but their markers and IR kinds must remain
different:

```rust
#[k::anywhere]
fn reassociate(
    term![Seq(Seq(first, second), third)]: Term<Statement>,
) -> Term<Statement> {
    term![Seq(first, Seq(second, third))]
}

#[k::simplification(priority = 40)]
fn add_zero(term![int::add(value, 0)]: Term<Int>) -> Term<Int> {
    term![value]
}
```

An anywhere rule makes its root symbol constructor-like modulo the declared
equations and can apply at any occurrence. It is not an explicit recursive
tree walk and does not participate in cell completion. KRS should emit the
native `[anywhere]` rule, preserve `requires`/`ensures` as R7 Boolean
conditions, and warn about obvious orientation cycles without claiming to
prove termination or confluence.

A simplification rule is the R7 form: its root must be functional,
`functional`, or a matching-logic operator; matching rather than function-rule
unification is used; its requirement must be implied by the current side
condition; and the optional integer is only a simplifier hint. It may be
applied at any time. KRS rejects transition `priority`, `owise`, and `anywhere`
on the same sentence, as current K does.

The important operational distinction is:

| Sentence | When/where it acts | Root remains constructor? | Portable to current Haskell backend? |
|---|---|---:|---:|
| function equation | when the function is evaluated | no | yes |
| simplification | backend-selected simplification points | depends on declaration | yes |
| anywhere | any occurrence after construction/rewrite | yes, modulo equations | **no** |
| desugar/alias | statically before backend rewriting | removed before execution | yes |

Current K 7.1.337 rejects `anywhere` for the Haskell backend. The hidden
`--allow-anywhere-haskell` switch does not implement it; it strips the rules
with a warning and can change behavior. Therefore a portable KRS profile must
reject `#[k::anywhere]`. An LLVM-only profile may accept it. This is a genuine
target-capability blocker, not a notation problem.

## Anonymous `#fun`

K's `#fun(pattern => result)(argument)` is close enough to a Rust closure to
use one, provided it occurs only inside a compiler-recognized term combinator:

```rust
#[k::rule]
fn update_record(term![Update(record)]: Term<Record>) -> Term<Record> {
    k::fun(
        record,
        |record @ term![Record { field: old, .. }]: Term<Record>| {
            term![Record {
                field: int::add(old, 1),
                ..record
            }]
        },
    )
}
```

`k::fun(argument, |pattern: Sort| result)` is a K term builder. The compiler
does not execute a Rust closure. It lowers to native `#fun`, from which the K
frontend generates a fresh function symbol, one equation, and explicit hidden
arguments for captured outer variables. A variable/cast-of-variable parameter
produces a total generated function; a structural/refutable parameter produces
a partial one and can denote bottom when it does not match.

This preserves the useful Rust intuitions—one parameter, lexical captures,
nesting, and a result expression—while enforcing K's actual restrictions:

- it is not first-class and cannot be stored, injected as a label, or returned
  as a closure value;
- it has one parameter and one clause;
- it has no side condition;
- its body is one restricted K term expression, not host statements; and
- nested `k::fun` is allowed.

The same implementation can later expose `k::let_term(argument, |name| body)`
for K's `#let`, but ordinary Rust `let` inside a rule body must not silently
acquire this meaning. Structural closure patterns use the same `term!` and
collection islands as R3. No new top-level grammar is needed.

## Matching global context in function equations

KEVM uses this feature heavily for functions such as account and transaction
lookups. Make the read effect explicit as a second, specially typed equation
parameter:

```rust
#[k::function(total, reads = Machine)]
pub struct AccountExists(pub Account);

#[k::equation]
fn account_exists_hit(
    term![AccountExists(account)]: Term<Bool>,
    k::Global(Machine {
        accounts: cell_set![AccountCell { id: account, .. }, _rest @ ..],
        ..
    }): k::Global<Machine>,
) -> Term<Bool> {
    term![true]
}

#[k::equation]
#[k::owise]
fn account_exists_miss(
    term![AccountExists(_)]: Term<Bool>,
) -> Term<Bool> {
    term![false]
}
```

The first parameter remains R3/R7's function-application lhs. `k::Global<C>`
is not another object-language function argument: it is a read-only pattern
against configuration `C`. The optional `reads = Machine` on the production
is checked documentation of the effect; KRS can infer it from clauses, but a
public directly context-reading function should spell it.

KRS enforces the current frontend restrictions:

- global context occurs only at the top level of a function equation;
- at most one global configuration fragment is attached to the equation;
- no rewrite/update may occur inside it;
- values bound by it may occur in the result and conditions; and
- `Global` cannot be constructed as an object term on the RHS.

The frontend desugars a context-reading function by appending a hidden
`GeneratedTopCell` argument to its symbol, matching the requested cells into
that argument, and passing the current configuration at every call site.
Dependency analysis propagates that hidden argument through functions which
call a context-reading function. The KRS IR therefore records both the direct
global pattern on an equation and the inferred transitive
`needs_global_configuration` effect on function symbols. It must not expose
the generated top cell as a user-written constructor field.

This feature breaks ordinary Rust's intuition that a visually one-argument
call depends only on that argument. The explicit `Global` parameter and
`reads` effect are the honest boundary; pretending the lookup is an ordinary
pure Rust function would be worse. Since K term applications are declarations
rather than host calls, no Rust ABI promise is lost.

## IR and lowering consequences

R3/R7's `Sentence` and `FunctionSymbol` should be extended approximately as
follows:

```text
EvaluationStrategy {
  symbol,
  mode: Strict | Sequential,
  groups: [StrictGroup { context_alias: Option<Id>, fields: [FieldId] }],
  default_result: Sort,              // KResult unless overridden
  hybrid_results: [Sort],
  source,
}

ContextSentence {
  id,
  template: Pattern,
  hole: BinderId,
  heat_as: Option<Term>,
  requires: Term<Bool>,              // heat only
  result_sort: Sort,
  attributes,
  source,
}

ContextAliasSentence {
  id,
  group: Id,
  template: Pattern,
  here: BinderId,
  requires: Term<Bool>,
  result_sort: Sort,
  context_wrapper: Option<Symbol>,
  attributes,
  source,
}

StaticRewrite {
  id,
  mode: Desugar | Alias,
  recursive: Bool,
  lhs: Pattern,
  rhs: Term,
  selection: StaticPriority,
  source,
}

AnonymousFunctionTerm {
  parameter: Pattern,
  argument: Term,
  result: Term,
  captures: [BinderId],
  inferred_totality: Partial | Total,
  source,
}

Equation {
  lhs,
  requires,
  rhs,
  ensures,
  global_context: Option<Pattern>,
  ...
}

FunctionSymbol {
  ...
  direct_global_configuration: Option<ConfigurationType>,
  needs_global_configuration: Option<ConfigurationType>,
}

Sentence := TransitionRule | Equation | Simplification | Claim
          | AnywhereRule | StaticRewrite
          | ContextSentence | ContextAliasSentence
```

`EvaluationStrategy` belongs beside productions rather than in the executable
rule set. `AnonymousFunctionTerm` is a term node, not a sentence. Static
priority, simplification priority, and transition/equation priority are three
different typed fields even when their target spelling contains an integer.

For the `.k` bootstrap target:

1. emit strictness, result, hybrid, context, and context-alias declarations in
   their source-level K forms;
2. emit the production's `macro`/`macro-rec`/`alias`/`alias-rec` attribute and
   its clause as an ordinary target K rule;
3. emit native `[anywhere]` and `[simplification(...)]` attributes only after
   checking the selected target profile;
4. emit `#fun` rather than generated lambda symbols; and
5. emit native `[[ function rewrite ]] configuration-fragment` syntax rather
   than adding `GeneratedTopCell` parameters itself.

This deliberately delegates version-sensitive generated names and desugaring
details to the source of truth selected by R6. A future direct structured/Kore
target must implement these transformations as explicit lowering passes and
compare their post-frontend output under R8.

## Cross-form validation matrix

The compiler should reject invalid combinations before text generation:

| Form | Reject |
|---|---|
| strictness | missing symbol, bad/duplicate field, sort `K`, unknown alias group |
| hybrid | no strictness declaration, unknown result predicate |
| context | post term, missing hole, more than one hole transformation, rewrite outside hole |
| context alias | missing `here`, post term, unknown wrapper symbol |
| desugar/alias | root mode mismatch, Boolean side conditions, runtime-only binders |
| anywhere | Haskell/portable target, `simplification`, or `symbolic` on the same rule |
| simplification | transition `priority`, `owise`, `anywhere`, or non-functional/non-ML root |
| anonymous `k::fun` | multiple parameters/clauses, host statements/effects, first-class use, side condition |
| global function context | non-equation use, nested context, any update to global state, incompatible configuration types |

R7's binder and condition rules apply throughout. In particular, a context or
static rule attribute cannot silently introduce a name; `hole` and `here`
must reference bindings already present in the parameter pattern. General
matching logic remains in `ml!`, not in a `requires` attribute.

## Rust parser check

The representative forms in this report use only Rust 2024 outer grammar:

- namespaced attributes and their balanced token payloads;
- structs and ordinary fields;
- zero-return function items;
- refutable function and closure parameter patterns;
- `Pat::Macro` for term/configuration/collection patterns; and
- ordinary path calls and closure expressions for `k::fun`.

A combined probe containing strict/result/hybrid attributes, both context
forms, desugar/alias/anywhere/simplification clauses, the `Global` parameter,
and a refutable closure inside `k::fun` was accepted by `rustfmt
1.9.0-stable` under edition 2024 (Rust 1.97.1 toolchain). As in R1, this proves
Rust parsing, not ordinary `rustc` type checking: KRS owns the attributes,
macro payloads, refutable-parameter semantics, and restricted bodies.

No form investigated here requires a grammar extension. A typed item macro is
an escape hatch for an unusually shaped context, not a new outer grammar.

## True blockers and remaining implementation work

There is one semantic blocker to a universal target promise:

1. **`anywhere` is LLVM-only in current K.** Haskell rejects it, and the hidden
   override removes it unsoundly. KRS must expose this as a target capability;
   it cannot claim one portable meaning.

The following are authoring or implementation risks, not unresolved language
designs:

2. Recursive macros, anywhere equations, and simplification rules can diverge
   or be unsound. KRS can detect simple cycles and preserve strong warnings,
   but termination/confluence/soundness are not generally decidable.
3. Reverse alias expansion affects final unparsing rather than execution. R8
   needs a separate parse/expand/unparse oracle; execution traces alone cannot
   validate aliases.
4. Direct Kore emission would have to reproduce freezer generation, hybrid
   predicate equations, macro expansion, anonymous-function closure capture,
   and transitive hidden-configuration threading. The chosen K-text bootstrap
   avoids making those version-coupled passes a v1 blocker.
5. Exact punctuation and formatting for the typed `context!` fallback and
   `fragment!` patterns remain implementation work already covered by the R1
   and R5 macro boundary. They do not change the semantic item shapes above.

With the Haskell `anywhere` capability exception made explicit, the design is
clear enough to implement. No additional conceptual investigation is required
for these forms before a small compiler prototype; corpus-driven syntax polish
can proceed alongside implementation.

## Sources inspected

- K user manual sections “Anonymous function applications”, “Macros and
  Aliases”, “`anywhere` rules”, “`simplification` attribute”, “`strict` and
  `seqstrict` attributes”, “Context Declaration”, “`result` attribute”,
  “`hybrid` attribute”, “Context aliases”, and “Matching global context in
  function rules”
- K tutorial lessons 1.14 and 2.1
- K 7.1.337 frontend `ResolveStrict`, `ResolveContexts`,
  `ResolveHeatCoolAttribute`, `ResolveFun`, `ResolveFunctionWithConfig`,
  `ExpandMacros`, `PropagateMacro`, `CheckHOLE`, and `CheckAtt`
- K 7.1.337 `KoreBackend`/`ModuleToKORE` handling of simplification and
  anywhere equations
- current KEVM global-context equations in `evm.md` and `state-utils.md`
- current KMIR/IMP strictness declarations and KMIR/KEVM/KWasm simplification
  corpora
- K regression cases for context aliases, result predicates, hybrid
  productions, anonymous `#fun`, and invalid strictness
