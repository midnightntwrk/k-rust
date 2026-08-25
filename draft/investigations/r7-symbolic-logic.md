# R7: Symbolic logic, partiality, variables, and claims

## Decision

KRS needs a small first-class matching-logic layer, but it should not make all
terms look like logic formulas. Keep three source categories distinct:

1. `Term<S>` is a symbolic K term of object sort `S`. A `Term<Bool>` is not a
   host Rust `bool`.
2. `MlPattern` is a matching-logic pattern: it can contain `#Top`, `#Bottom`,
   `#And`, `#Or`, `#Not`, `#Equals`, `#Ceil`, and quantifiers as well as
   ordinary K applications.
3. `#[k::requires(...)]` and `#[k::ensures(...)]` accept only an object-level
   `Term<Bool>`, matching the K frontend's rule grammar. General matching logic
   belongs in an `ml![...]` pattern, not behind a condition that looks like a
   Rust boolean.

Use the refutable function-clause shape selected by R3 for rules, equations,
simplifications, and claims. Their marker is their semantics:

```rust
#[k::rule]
fn step(/* pre-pattern */) -> State { /* post-term */ }

#[k::equation]
fn lookup_hit(/* function-pattern */) -> Term<dyn Value> { /* result-term */ }

#[k::simplification(priority = 40)]
fn reassociate(/* term or ML pattern */) -> Term<Int> { /* simpler term */ }

#[k::claim(all_paths)]
fn safety(/* initial pattern */) -> State { /* target pattern */ }
```

These are declarations, not callable Rust functions. One item represents one
relational clause. In particular, do not put function equations or claims in
an ordered Rust `match`.

Partiality must not use `Option`. A partial K function application denotes a
possibly empty pattern; when it is undefined, it is matching-logic bottom.
`None`, if a definition imports or declares an option datatype, remains an
ordinary object-theory constructor. The IR must never translate one into the
other.

## The logic boundary

### Object `Bool`

K's rule grammar parses `requires` and `ensures` at sort `Bool`; the frontend
then lowers these conditions into the backend's logical side condition. Keep
that visible in KRS:

```rust
#[k::requires(k::and_bool![
    int::le(0, index),
    int::lt(index, list::size(values)),
])]
#[k::ensures(int::eq(result, expected))]
#[k::rule]
fn checked_step(/* ... */) -> State { /* ... */ }
```

The attribute payload is a restricted Rust expression parsed by `syn` and
type-checked as `Term<Bool>`. Calls and macros above construct K terms; they do
not execute while KRS is compiling the definition.

Initially reject these spellings:

```rust
#[k::requires(index < values.len())] // host-looking operators are not in v1
#[k::requires(a && b)]               // Rust short-circuiting is the wrong model
#[k::requires(ml![ceil(value)])]      // MlPattern is not Term<Bool>
```

This restriction is deliberately stricter than what Rust can parse. Named
builtin functions such as `int::lt` and explicit `k::and_bool!` make it clear
which object theory supplies the operation. Operator sugar can be added later
only when its sort-directed lowering is unambiguous.

`requires` controls applicability: after matching/unification, the backend
must establish or find a satisfiable instance of the Boolean condition.
`ensures` is conjoined to the successor constraint after application and can
make that successor bottom; concrete backends may ignore it, as K permits.
They stay separate in the IR and in generated K.

### Matching-logic patterns

Use one visibly special macro island for logic which has no honest Rust
expression semantics:

```rust
ml![top::<Int>()]
ml![bottom::<Int>()]
ml![and(ceil(value), holds(int::gt(value, 0)))]
ml![or(equals(left, right), equals(left, fallback))]
ml![exists(x: Int, and(x, holds(int::le(lo, x))))]
```

The initial `ml!` grammar is closed and typed:

| Form | Matching-logic meaning |
|---|---|
| `top::<S>()`, `bottom::<S>()` | universal / empty pattern of sort `S` |
| `and(p, q, ...)`, `or(p, q, ...)`, `not(p)` | pattern connectives; variadic forms associate canonically |
| `implies(p, q)`, `iff(p, q)` | derived logical connectives |
| `equals(p, q)` | matching-logic equality, not object equality |
| `ceil(p)`, `floor(p)` | definedness / totality predicates |
| `holds(b)` | `{ true #Equals b }`, embedding object `Bool` |
| `exists(x: S, p)`, `forall(x: S, p)` | logical binders |
| an ordinary term application | its pattern denotation |

`ml!` is valid in pattern and expression position. In pattern position its
payload parser contributes bindings to the enclosing clause, just as `term!`
does. The normalized IR retains primitive ML nodes; it must not desugar
`bottom` to `false`, `ceil(p)` to `p.is_some()`, or `equals` to a Rust
comparison.

The `holds` conversion is important. These are different formulas:

```rust
term![int::eq(a, b)]        // a K term of sort Bool
ml![holds(int::eq(a, b))]   // an ML predicate saying that term is true
ml![equals(a, b)]           // matching-logic equality of two patterns
```

K's `#And` is also not `andBool`: the former intersects pattern denotations;
the latter is a function in the object `Bool` algebra.

## Variables and quantifier scope

Rust identifiers remain the spelling at use sites. Binder kind is explicit
only where K departs from an ordinary pattern binding:

| KRS binder | Meaning and scope | K lowering |
|---|---|---|
| name bound in the pre-pattern | singleton/element universal; inferred sort; scope is the whole clause | ordinary K variable |
| `#[k::set_vars(p: S, ...)]` | set universal which may denote partial or multi-valued patterns; whole clause | `@P:S` |
| `#[k::exists(x: S, ...)]` | existential symbolic output | `?X:S` |
| `#[k::fresh(x: S, ...)]` | operationally generated globally fresh value | `!X:S` plus K fresh machinery |
| `#[k::forall(x: S, ...)]` | explicit universal absent from the pre-pattern | ordinary RHS-only variable plus `[unboundVariables(X)]` |

### Ordinary and set variables

An ordinary pre-pattern binding means an element variable: its interpretation
is defined and single-valued. A set variable can stand for an arbitrary
matching-logic pattern, including bottom or a nondeterministic pattern. That
distinction is needed by real definedness lemmas:

```rust
#[k::set_vars(account: Account, nonce: Int)]
#[k::simplification]
fn new_address_defined(
    ml![ceil(NewAddress(account, nonce))]: MlPattern,
) -> MlPattern {
    ml![and(ceil(account), ceil(nonce))]
}
```

This is the KEVM lemma
`#Ceil(#newAddr(@ACCT, @NONCE)) => #Ceil(@ACCT) #And #Ceil(@NONCE)`.
The names look ordinary inside the rule, while `set_vars` advertises their
unusual denotation and gives the type checker an explicit binder list.

Do not confuse `set_vars(x)` with `#[k::symbolic([x])]`. The latter is a
simplifier applicability filter saying that the substitution for an ordinary
variable must be symbolic; it does not change the variable into a set
variable. Set-variable support is Haskell-backend-only in current K. KRS should
reject it for a non-Haskell target rather than silently weaken it.

### Existential, fresh, and RHS-only universal variables

The three forms describe materially different relations:

```rust
// Some suitable result may be chosen; the postcondition constrains it.
#[k::exists(choice: Int)]
#[k::ensures(list::contains(items, choice))]
#[k::rule]
fn choose(term![Choose(items)]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![IntValue(choice)]
}

// The runtime fresh-value mechanism supplies a globally unique identifier.
#[k::fresh(id: Id)]
#[k::rule]
fn allocate(term![Allocate]: Term<dyn Command>) -> Term<dyn Command> {
    term![Allocated(id)]
}

// Every satisfying integer is a successor, not merely one witness.
#[k::forall(value: Int)]
#[k::requires(k::and_bool![int::le(lo, value), int::le(value, hi)])]
#[k::rule]
fn random_bounded(term![RandomBounded(lo, hi)]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![IntValue(value)]
}
```

For transition rules and claims, `exists` quantifies at the top of the RHS;
the name may occur in the post-pattern and `ensures`, but not in the
pre-pattern or `requires`. For equations, K quantifies an existential at the
top of the entire equation, so the normalized IR records `EquationScope`
rather than reusing transition lowering mechanically. All ordinary and
explicit `forall` variables are universally quantified outside those
existentials, so existential choices may depend on them.

`fresh` is not an existential plus a disequality constraint. It invokes K's
fresh generator/counter discipline, cannot be constrained in the same local
way as `exists`, and can have a sort-specific `freshGenerator`. V1 permits it
only on executable transition rules; equations, simplifications, and claims
receive a diagnostic until a target-faithful use is demonstrated.

An explicit `forall` is the honest surface for K's `unboundVariables`: it
means every value satisfying the requirement gives a transition. It can need
special enumeration in a concrete engine. KRS should emit a backend-capability
diagnostic instead of treating it as an existential or choosing one value.

Reject every other name first encountered in a post-term, `requires`, or
`ensures`. For v1, even a don't-care RHS value should use a named binding such
as `#[k::exists(_result: Int)]`; this is more explicit than inventing a second
meaning for Rust `_`.

## Partial and total functions

Defined K symbols remain production structs. Functionality is declared on the
symbol, not inferred from Rust return types:

```rust
#[k::function(partial)]
pub struct Range(pub Term<dyn List>, pub Int, pub Int);

impl List for Range {}

#[k::function(total)]
pub struct IsOneOf(pub Int, pub Term<dyn Discriminants>);

impl Bool for IsOneOf {}
```

`partial` means at most one result for each argument tuple. If no defining
equation applies, the application denotes matching-logic bottom. `total` adds
the assertion that at least one result exists for every input, so a total
function has exactly one result. KRS should require one of the two words; the
K target lowers `partial` to `[function]` and `total` to `[function, total]`.
The compiler validates that `total` is used only with `function`, but does not
pretend to prove coverage merely from source patterns.

One defining equation is one clause:

```rust
#[k::equation]
fn range_identity(
    term![Range(list, 0, 0)]: Term<dyn List>,
) -> Term<dyn List> {
    term![list]
}

#[k::equation]
#[k::requires(int::ne(denominator, 0))]
fn divide_word(
    term![WordDiv(numerator, denominator)]: Term<Int>,
) -> Term<Int> {
    term![int::modulo(int::div(numerator, denominator), WORD_MODULUS)]
}
```

Equation clauses may use explicit `#[k::priority(...)]` or `#[k::owise]`.
They are oriented equational simplifications of a functional symbol, not host
calls and not transition steps. Their lhs root must resolve to a declared K
function. Separate clause names provide labels and diagnostics; they do not
declare Rust overloads.

Never write `-> Option<Term<S>>` for a K function. A missing equation is enough
to make a partial application bottom. An explicit logical equation involving
bottom uses `MlPattern` and `ml![bottom::<S>()]`; `None` is never recognized as
special by the KRS compiler.

## Simplification rules

Simplification lemmas are a distinct sentence kind:

```rust
#[k::simplification(priority = 40)]
#[k::symbolic([a, b])]
#[k::concrete([c])]
fn reassociate_add(
    term![int::add(a, int::add(b, c))]: Term<Int>,
) -> Term<Int> {
    term![int::add(int::add(a, b), c)]
}
```

The simplifier matches arguments rather than using function-rule unification,
and applies a lemma only when the current side condition implies its
`requires`. The integer inside `simplification(...)` is a simplification hint;
it is not transition/function `priority`. K permits the backend to apply sound
simplifications at any time and in a different order. Therefore KRS rejects
`#[k::priority]` and `#[k::owise]` on a simplification item and diagnoses an
obvious orientation loop where possible without claiming to establish
soundness or termination.

Matching-logic lemmas use the same item shape with `MlPattern`:

```rust
#[k::simplification]
fn range_defined(
    ml![ceil(Range(list, front, back))]: MlPattern,
) -> MlPattern {
    ml![and(
        ceil(list),
        ceil(front),
        ceil(back),
        holds(int::le(int::add(front, back), list::size(list))),
    )]
}
```

This directly represents KMIR's `#Ceil(range(...))` lemma. In particular,
`ceil` is preserved as definedness logic; it is not an `is_some` test.
Typed attributes such as `preserves_definedness`, `concrete`, `symbolic`,
`comm`, and `smt_lemma` remain orthogonal promises/filters and must survive
lowering.

## Reachability claims

A claim uses the same pre/post clause shape as a transition, but it is proved
against the transition relation and never participates in execution:

```rust
#[k::claim(all_paths)]
#[k::exists(n_after: Int)]
#[k::ensures(k::or_bool![
    int::eq(n_after, 5),
    int::eq(n_after, 6),
])]
fn branching(
    state @ Machine {
        k: k![BranchingProgram(symbolic_condition), tail @ ..],
        env: map![N_ID => 0, env_rest @ ..],
        ..
    }: Machine,
) -> Machine {
    Machine {
        k: k![..tail],
        env: map![N_ID => n_after, ..env_rest],
        ..state
    }
}
```

This is the shape of IMP's `branching` proof: every path through a symbolic
conditional must reach a completed configuration where the final value is
either 5 or 6. The existential is a witness in the destination pattern, not a
fresh runtime allocation.

KRS requires every claim to spell exactly one of `all_paths` and `one_path`.
It does not inherit a command-line or module default silently:

- `#[k::claim(one_path)]` asks for a path from every source instance to a
  destination instance.
- `#[k::claim(all_paths)]` asks that all relevant paths from every source
  instance reach a destination instance.

The IR stores the modality as an enum and lowering emits the corresponding K
claim attribute. Backend details about final/stuck/infinite paths remain the
K version's semantics and belong in the equivalence oracle; KRS must not
compile either modality into an ordinary test or bounded search.

Ordinary source variables are universal. Explicit RHS existentials preserve
K's important difference from RHS-only universals. For example, a one-path
claim `foo => exists x: Bool. x` needs one reachable Boolean, whereas
`foo => forall x: Bool. x` (K `unboundVariables`) requires reachability for
every Boolean instance. Under `all_paths`, the latter is stronger still.

`#[k::trusted]` may decorate a claim but must remain visibly exceptional and
should trigger a warning in proof-oriented builds.

## Normalized IR requirements

R3's relational rule IR should be refined as follows:

```text
Binder {
  id,
  sort,
  kind: ElementUniversal | SetUniversal | Existential
      | Fresh | ExplicitUnboundUniversal,
  scope: WholeClause | TransitionRhs | Equation,
  source,
}

Condition {
  object_bool: Term<Bool>,
  source,
}

MlPattern := Application | Variable(BinderId)
           | Top(sort) | Bottom(sort)
           | And | Or | Not | Implies | Iff
           | Equals | Ceil | Floor | Exists | Forall

FunctionSymbol {
  symbol,
  arguments,
  result_sort,
  functionality: Partial | Total,
}

Sentence := TransitionRule { pre, requires, post, ensures, ... }
          | Equation       { lhs, requires, rhs, ensures, ... }
          | Simplification { lhs, requires, rhs, ensures, hint, ... }
          | Claim          { modality, pre, requires, post, ensures, ... }
```

Required invariants:

1. `requires` and `ensures` contain `Term<Bool>`, never an untyped expression
   or `MlPattern`.
2. `Bottom(sort)` is an explicit IR node. No Rust control-flow or datatype
   node lowers to it implicitly.
3. Every occurrence resolves to a binder with one kind; changing a binder to
   `set_vars`, `exists`, `fresh`, or `forall` cannot be span-local.
4. An existential in a transition/claim cannot occur in `pre` or `requires`.
5. A fresh binder is distinct from existential and from universally unbound.
6. A set variable remains marked through Kore emission; backend capability is
   checked before lowering.
7. Function application does not acquire a host return/effect interpretation.
   Partiality belongs to its pattern denotation.
8. Claim modality and simplification priority are closed enums, not raw K
   attributes.

## What can be postponed

The first useful compiler needs object `Bool` conditions, explicit binder
kinds, partial/total function declarations, equation and simplification
clauses, the listed core `ml!` connectives, and explicit claim modality. Those
cover the IMP proof corpus and the representative KMIR/KEVM lemmas.

The following can be postponed behind a diagnostic or the documented raw K
escape hatch without blocking useful semantics:

- matching-mu fixed points and recursive logical aliases;
- first-class equality axioms for genuinely multi-valued non-function symbols;
- automatic Skolemization of existential function equations;
- anonymous RHS binders (named `exists` is sufficient initially);
- proving total-function coverage, simplifier soundness, or termination;
- fresh variables on equations, simplifications, or claims; and
- backend-independent set-variable execution.

Do not postpone the `Bool`/ML distinction or bottom representation. Recovering
those after an `Option`- or host-boolean-based IR would require changing the
meaning of already accepted programs.

## Parser check

The representative declarations above use only Rust outer grammar: namespaced
attributes, refutable function parameters, macro patterns/expressions, structs,
and impls. A compact file containing the partial/total declarations, equation,
set-variable definedness lemma, IMP claim, and all four binder attributes was
accepted by `rustfmt 1.9.0-stable` under Rust 2024. R1 separately established
that these same outer forms (`ItemFn`, namespaced attributes, `Pat::Macro`, and
`Expr::Macro`) parse with the repository's pinned `syn 2.0.119`. This
establishes Rust parse compatibility, not ordinary `rustc` type checking; KRS
owns the attributes, macro payloads, refutable-clause contract, and symbolic
types.

## Sources inspected

- K user manual sections “Rule Structure”, “`function` and `total`
  attributes”, “Projection and Predicate functions”, “`simplification`
  attribute”, “The `unboundVariables` attribute”, “`all-path` and `one-path`”,
  “Set Variables”, and “Variables occurring only in the RHS of a rule”
- K tutorial lessons on symbolic execution and proof claims
- `imp-semantics/examples/specs/imp-simple-spec.k`
- KMIR `lemmas/kmir-lemmas.md`, especially `#Ceil(range(...))`
- KEVM `lemmas/int-simplification.k` and
  `lemmas/summarization-simplification.k`
- K frontend `AddSortInjections`, which assigns `Bool` as the expected sort of
  `requires` and `ensures`
