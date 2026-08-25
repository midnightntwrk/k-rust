# Candidate language mapping

> Historical sketch: this file supplied notation for the investigations to
> criticize. It is not authoritative. In particular, R3 rejected the
> `Option<State>` rule ABI, R2 refined open sorts and syntactic lists, R4 chose
> a hybrid grammar layer, R5 refined configuration framing, and R7 separated
> object Boolean conditions from matching logic. See
> [`design.md`](design.md) for the authoritative synthesized design and
> [`investigations/`](investigations/) for its evidence.

This file is retained to make the evolution of the design visible. It is not a
grammar or a commitment to exact spellings.

## Modules and builtins

K files and modules form two DAGs; Rust has one module/crate system. KRS should
present one Rust-like module system and let lowering generate the required K
file/module structure.

```rust
mod expr;

use k::builtin::{Bool, Int, Map};
use expr::{Expr, Value};
```

`use` is more than a host-language import: it can make K syntax, equations,
hooks, and generated symbols available. Public/private re-export behavior
should follow Rust as far as K module visibility permits.

## Sorts: traits for openness, enums for closure

A K sort is an extensible category of terms. A marker trait is the closest
Rust concept:

```rust
#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult: KItem {}

#[k::sort]
pub trait Expr: KItem {}

#[k::sort]
pub trait Value: Expr + KResult {}
```

The compiler closes the transitive subsort relation, so an implementation of
`Value` is also an `Expr`, `KResult`, and `KItem`. This automatic closure is a
KRS rule and must be stated plainly because ordinary Rust requires explicit
implementations of supertraits.

Concrete term constructors remain ordinary structs and enums:

```rust
#[k::token(r"[0-9]+")]
pub struct Integer(pub Int);

impl Value for Integer {}

#[k::constructors]
pub enum Boolean {
    True,
    False,
}

impl Value for Boolean {}
```

Another module can extend the open categories without reopening an enum:

```rust
pub struct Address(pub Int);

impl Value for Address {}
```

This is preferable to the alternatives considered so far:

- **reopening enums** looks compact but contradicts a core Rust guarantee and
  creates difficult exhaustiveness and dependency-order questions;
- **`From` implementations** describe conversions, not membership, and would
  make K subsort injection look operational when it is structural; and
- **one universal boxed term enum** preserves openness only by giving up most
  useful Rust type information.

We still need to test whether trait-object spelling (`Box<dyn Expr>`) becomes
too noisy for recursive syntax and whether a KRS-specific unsized-sort rule can
remain intuitive.

## Productions and object-language syntax

Structs and enum variants define the internal term algebra, but they do not by
themselves define how object-language programs are parsed. K supports arbitrary
terminals, lexical productions, precedence, associativity, brackets, syntactic
lists, and pretty-print formats. KRS therefore needs syntax metadata:

```rust
#[k::syntax("{lhs} + {rhs}", precedence = 60, assoc = "left")]
#[k::strict(sequence = [lhs, rhs])]
pub struct Add {
    pub lhs: Box<dyn Expr>,
    pub rhs: Box<dyn Expr>,
}

impl Expr for Add {}
```

Field names naturally lower to K named non-terminals and enable Rust record
patterns. Prefix constructors can receive a default syntax, but infix notation
and an external language's concrete grammar cannot be inferred from Rust type
declarations alone.

## Configuration as nested structs

The shape of a normal fixed cell tree maps well to structs:

```rust
#[k::configuration]
pub struct Machine {
    pub k: KCell<KSequence>,
    pub env: Cell<Map<Id, ValueTerm>>,
}

impl Machine {
    #[k::init]
    pub fn init(program: Program, env: Map<Id, ValueTerm>) -> Self {
        Self {
            k: KCell::new(program),
            env: Cell::new(env),
        }
    }
}
```

An initialization function avoids inventing non-Rust field-default syntax and
can represent K's `$PGM` and other configuration variables. The compiler should
accept only a restricted, constructor-like subset here so initialization stays
declarative.

Repeated or optional K cells are not ordinary struct fields. Candidate standard
wrappers such as `SetCells<T>`, `ListCells<T>`, `MapCells<K, T>`, and
`OptionCell<T>` can expose cell multiplicity and collection matching without
special field syntax.

## Rules as partial state transformers

The closest honest Rust model of one K rule is a partial transformer:

```rust
#[k::rule]
fn assign(state: Machine) -> Option<Machine> {
    match state {
        Machine {
            k: k![Assign { name, value: Value(value) }, rest @ ..],
            env,
        } => Some(Machine {
            k: k![..rest],
            env: env.updated(name, value),
        }),
        _ => None,
    }
}
```

This gives Rust readers useful intuitions:

- the pattern binds values;
- `..` frames unmentioned state;
- the right side constructs an updated state; and
- `None` means this rule does not apply.

The `#[k::rule]` contract then adds the essential relational behavior:

- every rule is considered independently;
- several rules may apply to the same state and yield several successors;
- source order has no meaning unless a priority attribute says otherwise;
- the body must be a restricted declarative match, not arbitrary Rust code;
- symbolic matching/unification may produce constraints rather than a concrete
  yes/no answer; and
- compilation can frame omitted cells and lower simultaneous field updates to
  K local rewrites.

For these reasons, several K rules must not be encoded as arms of one ordinary
Rust `match`. That spelling would falsely promise first-match semantics.

Side conditions and postconditions can initially use typed attributes or
restricted helper calls:

```rust
#[k::rule]
#[k::requires(denominator != 0)]
#[k::ensures(result >= 0)]
fn divide(/* ... */) -> Option<Machine> {
    /* restricted match */
}
```

We should later test whether Rust `if` guards are sufficient for `requires` and
whether an `ensures` attribute is readable for symbolic postconditions.

## Functions and equations

K functions are equations simplified anywhere in a term, not host calls that
run once in statement order. Total deterministic functions can still look like
restricted Rust functions:

```rust
#[k::function(total)]
fn length(xs: &List<ValueTerm>) -> Int {
    match xs {
        [] => 0,
        [_, rest @ ..] => 1 + length(rest),
    }
}
```

Partial K functions need an explicit spelling. Returning `Option<T>` is the
most Rust-like candidate, but K undefinedness is matching-logic bottom, not a
data constructor `None`; lowering must unwrap this distinction rather than
encode `Option` into the object theory accidentally.

Rule priority, `owise`, simplification lemmas, `anywhere` equations, macros,
and backend-preserved-definedness promises all alter equation behavior and
need explicit `k::` attributes.

## Attributes

Common K attributes should be namespaced, parsed, type-checked, and documented:

```rust
#[k::strict(sequence = [lhs, rhs])]
#[k::symbol("add")]
#[k::simplification(priority = 40)]
#[k::concrete([rhs])]
```

An escape hatch should retain exact target behavior while advertising that KRS
cannot validate it fully:

```rust
#[k::raw_attr("preserves-definedness")]
```

Raw attributes must survive lowering byte-for-byte (or as structured K
attribute data), produce a warning by default, and never be silently ignored.

## Rust patterns that transfer well

Several modern K patterns already have close Rust equivalents:

- K `Pattern #as V` maps to `V @ Pattern`;
- K `#Or` patterns map to `A | B` when bindings agree;
- named K non-terminals map to struct fields and record patterns;
- anonymous K variables map to `_`;
- list prefix/suffix matching resembles slice patterns; and
- partial cell-tree matching resembles struct patterns containing `..`.

Map/set associative matching, symbolic functions in keys, cell fragments, and
fresh or existential variables do not have ordinary Rust-pattern semantics and
will require visibly K-specific pattern helpers.
