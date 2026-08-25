# R3: Rule surface and semantics

## Decision

Do **not** expose K rules as functions returning `Option<State>`. Keep that as
an explanatory analogy for one concrete, deterministic fragment only.

The smallest honest surface found in IMP and KMIR is one independently named,
attribute-marked **function clause** per K rule:

```rust
#[k::rule]
#[k::requires(k::and![0 <= i, i < blocks.len(), blocks[i].is::<BasicBlock>()])]
#[k::preserves_definedness]
fn exec_block_idx(
    state @ Machine {
        k: k![ExecBlockIdx(BasicBlockIdx(i)), tail @ ..],
        current_body: blocks,
        ..
    }: Machine,
) -> Machine {
    Machine {
        k: k![ExecBlock(blocks[i].as::<BasicBlock>()), ..tail],
        ..state
    }
}
```

This uses only Rust grammar, although a refutable function-argument pattern is
rejected by Rust's type checker. KRS gives a `#[k::rule] fn` a deliberately
different contract:

- it is a declaration, not a callable Rust function;
- its argument pattern and contracts describe applicability;
- its return expression describes the post-state;
- all declarations at the same priority are independent alternatives; and
- its body is a restricted term expression, not arbitrary host computation.

The `#[k::rule]` marker is essential semantic punctuation. A plain `fn` and a
plain `match` retain ordinary deterministic Rust meaning.

Use Rust patterns for constructors, records, `@`, `|`, `_`, and fixed state
framing. Use visibly special pattern macros for the operations that Rust does
not possess:

```rust
k![head, tail @ ..]                     // K sequence
list![head, rest @ ..]                  // associative list pattern
set![key, rest @ ..]                    // AC set pattern
map![key => value, rest @ ..]           // AC map pattern
```

Keep `requires`, `ensures`, `priority`, and `owise` as typed attributes. They
belong to the clause, not to an ordered `match` arm. Bind symbolic outputs
explicitly:

```rust
#[k::rule]
#[k::exists(i: Int)]
#[k::ensures(!items.contains(i))]
fn choose_fresh(Fresh(items): Expr) -> Expr {
    IntValue(i)
}

#[k::rule]
#[k::fresh(id: Id)]
fn allocate(Allocate: Command) -> Command {
    Allocated(id)
}
```

`exists` denotes existential quantification in the post-pattern. `fresh`
denotes K's generated globally fresh value and is not interchangeable with an
existential plus a constraint.

This recommendation covers all IMP rules and the selected KMIR stress cases.
Collection patterns and symbolic contracts need special semantics, but no
dedicated grammar extension is needed. A `k::rule!` token-tree DSL remains a
reasonable escape hatch for raw matching-logic patterns, not the default rule
surface.

## Why `State -> Option<State>` is too narrow

For a ground state, a rule with a single deterministic match can be explained
as returning `Some(post)` or `None`. That model fails as soon as a backend does
anything relational.

| Feature | Covered by concrete `Option<State>`? | Actual requirement |
|---|---:|---|
| Several local cell rewrites | Yes, after whole-state desugaring | Shared frame variables and one simultaneous pre/post pair |
| K sequence head/tail | Yes, with a special pattern | Associative sequence pattern and continuation frame |
| `requires` | Only if it computes a host `bool` | A logical constraint checked for validity or satisfiability |
| `ensures` | No | A constraint conjoined to the successor path condition |
| `#as` / `#Or` | Mostly | Rust `@` / `|`, with equal-binding checks for alternatives |
| `owise` / priority | No | Selection policy across separately declared clauses |
| Symbolic matching | No | Zero, one, or many substitutions plus residual constraints |
| Existential RHS values | No | A family of post-states under an existential binder |
| Map/set matching | No | Potentially many AC decompositions and a collection frame |
| Nondeterminism | No | A set of successors, including two successors from one schematic rule |

An operational approximation of a rule is closer to:

```text
State -> Set<(State, PathConstraint)>
```

but that is still not the source-level meaning. The normalized form should be
a quantified relational clause:

```text
forall U.
    (Pre(U) #And Requires(U))
      rewrites-to
    exists E. (Post(U, E) #And Ensures(U, E))
```

Matching `Pre` against the subject can itself produce multiple substitutions.
Priority then controls which priority stratum is eligible. `Option` should not
appear in the rule ABI because it would teach readers that applicability is a
host-language boolean and that a clause has at most one result.

Rules are also not necessarily over a complete configuration. IMP's arithmetic
rules rewrite `Expr` terms, while its stateful rules rewrite a completed
configuration pattern. The IR therefore uses a generic `subject_sort`, not a
hard-coded `State` type.

## Proposed normalized IR

The surface should lower before K text generation to a representation along
these lines:

```text
Rule {
  id: Path,
  kind: Transition | Equation | Simplification | Anywhere | ...,
  subject_sort: Sort,
  universals: [Binder],       // inferred from the pre-pattern
  existentials: [Binder],     // explicit #[k::exists]
  fresh: [Binder],            // explicit #[k::fresh]
  pre: Pattern,
  requires: LogicPattern,
  post: Pattern,
  ensures: LogicPattern,
  selection: Priority {
    value: Int,               // default 50; owise lowers to 200
    origin: Default | Explicit | Owise,
  },
  attributes: [TypedOrRawAttribute],
  source: Span,
}
```

Important invariants:

1. `pre` and `post` are complete schematic subjects after cell completion and
   framing. Multiple local rewrites are normalized simultaneously, never as a
   sequence of mutations.
2. Omitted fixed fields, cell bags, K sequence tails, and collection remainders
   become distinct typed frame variables. They must not all be represented by
   one undifferentiated Rust `..` internally.
3. `requires` and `ensures` remain separate fields. In particular, a concrete
   backend may ignore `ensures`, while a symbolic backend adds it to the path
   condition.
4. Default priority, explicit priority, and `owise` retain their origin even
   when they share an integer. This is useful for diagnostics and lossless K
   emission.
5. Source order is absent from selection semantics. It is retained only as
   source metadata for stable output and diagnostics.
6. A variable occurring only in `post` or `ensures` is rejected unless it has
   an explicit existential/fresh binder or a deliberately raw K escape hatch.
7. Or-pattern alternatives must bind the same names at compatible sorts, as in
   Rust.

For example, the IMP assignment rule normalizes to:

```text
Rule assign {
  subject_sort: Machine,
  universals: [name: Id, value: Value, env: Map<Id, Value>, k_tail: KSequence,
               machine_frame: MachineFrame],
  pre:  Machine {
          k = KSeq[Assign(name, Value(value)), *k_tail],
          env = env,
          *machine_frame
        },
  requires: true,
  post: Machine {
          k = k_tail,
          env = update(env, name, value),
          *machine_frame
        },
  ensures: true,
  selection: Default(50),
}
```

This is the same global pre/post relation produced by K when it pulls the two
local rewrites in `<k>` and `<env>` to the top level.

## Candidate surface comparison

### 1. Partial transformer with a one-arm `match`

```rust
#[k::rule]
fn assign(state: Machine) -> Option<Machine> {
    match state {
        state @ Machine { /* pre */ } => Some(Machine { /* post */, ..state }),
        _ => None,
    }
}
```

Advantages: valid Rust grammar, familiar pattern binding, and explicit
non-applicability. Disadvantages: `Option` incorrectly limits the denotation;
the wildcard arm is repetitive; `match` suggests ordered arms; `Some` and
`None` look like object-theory constructors; and contracts do not fit the
return type. Reject as the normative surface.

### 2. Dedicated `k::rule!` DSL

```rust
k::rule! {
    assign:
      Machine { /* pre */ }
      => Machine { /* post */ }
      requires condition
}
```

Advantages: completely honest about being a relation, permits arbitrary K
patterns, and cannot be mistaken for callable Rust. Disadvantages: most of the
important file becomes opaque token trees to Rust tooling; it invents another
item grammar; and agents lose ordinary function, pattern, attribute, and body
cues. Retain only as a raw/advanced escape hatch.

### 3. Attribute-marked refutable function clause

```rust
#[k::rule]
#[k::requires(condition)]
fn assign(state @ Machine { /* pre */ }: Machine) -> Machine {
    Machine { /* post */, ..state }
}
```

Advantages: smallest form; valid Rust parse; exactly one clause, so it cannot
imply arm order; direct Rust pattern transfer; easy extraction of pre and post;
and independent item identity for labels and priorities. The deviation from
Rust is concentrated in the visible `#[k::rule]` contract and refutable
parameter. This is the recommended common form.

The body should initially permit exactly one post-term expression. Do not allow
arbitrary statements, early `return`, loops, mutation, calls with host effects,
or multi-arm `match`. Pure K function-symbol applications and constructor
expressions are terms in the target theory, not operations executed while
declaring the rule.

## Complete IMP encoding

The following is intentionally compact, but contains every rule from
`expr.k`, `calc.k`, and `imp.k`. Constructor names make the inferred sorts
explicit; each function is a separate rule declaration even when presented on
one line here.

```rust
// expr.k: unary and arithmetic
#[k::rule] fn neg(Neg(IntValue(x)): Expr) -> Expr { IntValue(int::sub(0, x)) }
#[k::rule] fn not(Not(BoolValue(b)): Expr) -> Expr { BoolValue(bool::not(b)) }
#[k::rule] fn add(Add(IntValue(x), IntValue(y)): Expr) -> Expr { IntValue(int::add(x, y)) }
#[k::rule] fn sub(Sub(IntValue(x), IntValue(y)): Expr) -> Expr { IntValue(int::sub(x, y)) }
#[k::rule] fn mul(Mul(IntValue(x), IntValue(y)): Expr) -> Expr { IntValue(int::mul(x, y)) }
#[k::rule] fn div(Div(IntValue(x), IntValue(y)): Expr) -> Expr { IntValue(int::div(x, y)) }

// comparisons
#[k::rule] fn ge(Ge(IntValue(x), IntValue(y)): Expr) -> Expr { BoolValue(int::ge(x, y)) }
#[k::rule] fn gt(Gt(IntValue(x), IntValue(y)): Expr) -> Expr { BoolValue(int::gt(x, y)) }
#[k::rule] fn le(Le(IntValue(x), IntValue(y)): Expr) -> Expr { BoolValue(int::le(x, y)) }
#[k::rule] fn lt(Lt(IntValue(x), IntValue(y)): Expr) -> Expr { BoolValue(int::lt(x, y)) }

// overloaded equality and inequality
#[k::rule] fn eq_bool(Eq(BoolValue(x), BoolValue(y)): Expr) -> Expr { BoolValue(bool::eq(x, y)) }
#[k::rule] fn eq_int(Eq(IntValue(x), IntValue(y)): Expr) -> Expr { BoolValue(int::eq(x, y)) }
#[k::rule] fn ne_bool(Ne(BoolValue(x), BoolValue(y)): Expr) -> Expr { BoolValue(bool::ne(x, y)) }
#[k::rule] fn ne_int(Ne(IntValue(x), IntValue(y)): Expr) -> Expr { BoolValue(int::ne(x, y)) }

// short-circuit rules
#[k::rule] fn and_true(And(BoolValue(true), b): Expr) -> Expr { b }
#[k::rule] fn and_false(And(BoolValue(false), _): Expr) -> Expr { BoolValue(false) }
#[k::rule] fn or_true(Or(BoolValue(true), _): Expr) -> Expr { BoolValue(true) }
#[k::rule] fn or_false(Or(BoolValue(false), b): Expr) -> Expr { b }

// calc.k
#[k::rule]
fn step(state @ Machine { k: k![Seq(s1, s2), tail @ ..], .. }: Machine) -> Machine {
    Machine { k: k![s1, s2, ..tail], ..state }
}

#[k::rule]
fn var(state @ Machine {
    k: k![IdExpr(x), tail @ ..],
    env: map![x => value, _env_rest @ ..],
    ..
}: Machine) -> Machine {
    Machine { k: k![value, ..tail], ..state }
}

#[k::rule]
fn assign(state @ Machine {
    k: k![Assign(x, Value(value)), tail @ ..],
    env,
    ..
}: Machine) -> Machine {
    Machine { k: k![..tail], env: env.insert(x, value), ..state }
}

// imp.k
#[k::rule]
fn if_true(state @ Machine { k: k![IfElse(BoolValue(true), s1, _), tail @ ..], .. }: Machine) -> Machine {
    Machine { k: k![s1, ..tail], ..state }
}

#[k::rule]
fn if_false(state @ Machine { k: k![IfElse(BoolValue(false), _, s2), tail @ ..], .. }: Machine) -> Machine {
    Machine { k: k![s2, ..tail], ..state }
}

#[k::rule]
fn if_else(state @ Machine { k: k![If(c, s), tail @ ..], .. }: Machine) -> Machine {
    Machine { k: k![IfElse(c, s, EmptyBlock), ..tail], ..state }
}

#[k::rule]
fn while_loop(state @ Machine { k: k![While(c, s), tail @ ..], .. }: Machine) -> Machine {
    Machine {
        k: k![IfElse(c, Block(Seq(s, While(c, s))), EmptyBlock), ..tail],
        ..state
    }
}

#[k::rule]
fn block(state @ Machine { k: k![Block(s), tail @ ..], .. }: Machine) -> Machine {
    Machine { k: k![s, EmptyBlock, ..tail], ..state }
}

#[k::rule]
fn done(state @ Machine { k: k![EmptyBlock, tail @ ..], .. }: Machine) -> Machine {
    Machine { k: k![..tail], ..state }
}
```

`int::sub`, `bool::eq`, and similar calls above stand for imported K builtin
term operators; their final KRS names are an imports/builtins decision, not an
R3 decision.

### IMP normalization summary

Using `K[head; *tail]` for a K sequence, `M[k -> v; *rest]` for a map
decomposition, and `F` for the untouched configuration frame:

| Rule(s) | Pre-pattern | Post-pattern | Contracts |
|---|---|---|---|
| `neg`, `not` | unary constructor over a value | corresponding builtin term | none |
| `add/sub/mul/div` | binary constructor over two integers | corresponding `Int` builtin term | none |
| `ge/gt/le/lt` | comparison over two integers | corresponding Boolean builtin term | none |
| Boolean/integer `eq/ne` | overloaded operator over two same-kind values | corresponding typed equality term | none |
| `and_true/false`, `or_true/false` | Boolean constant in left operand | selected operand or constant | none |
| `step` | `Machine { k=K[Seq(s1,s2); *t], *F }` | `Machine { k=K[s1;s2;*t], *F }` | none |
| `var` | `Machine { k=K[Id(x);*t], env=M[x->v;*r], *F }` | `Machine { k=K[v;*t], env=M[x->v;*r], *F }` | none |
| `assign` | `Machine { k=K[Assign(x,v);*t], env=e, *F }` | `Machine { k=K[*t], env=update(e,x,v), *F }` | none |
| `if_true/false` | `IfElse` with selected Boolean constant at K head | selected branch at K head | none |
| `if_else` | two-branch `If` at K head | `IfElse(..., EmptyBlock)` | none |
| `while` | `While(c,s)` at K head | unfolded `IfElse` containing `s; while(c,s)` | none |
| `block` | nonempty block at K head | body followed by empty block | none |
| `done` | empty block at K head | framed continuation | none |

No IMP rule needs `Option`, multiple match arms, a grammar extension, an
existential, or an explicit priority.

## Ten KMIR stress cases

The sample below comes from current KMIR (`K 7.1.337`) and was selected to
exercise mechanisms absent from IMP rather than to favor easy rules.

| # | KMIR rule(s) | Stress | Normalized relational IR |
|---:|---|---|---|
| 1 | `#execBlockIdx` | K head rewrite, read-only `currentBody`, list indexing, `requires`, definedness | `pre = Machine{k=K[ExecBlockIdx(i);*t], currentBody=b,*F}`; `req = 0<=i && i<size(b) && isBasicBlock(b[i])`; `post = Machine{k=K[ExecBlock(asBasicBlock(b[i]));*t], currentBody=b,*F}` |
| 2 | nonempty `#execStmts` | K `#as`, associative statement tail, simultaneous span update | `pre = Machine{k=K[ExecStmts(Statements[stmt(_,span) @ s;*ss]);*t], currentSpan=old,*F}`; `post = Machine{k=K[ExecStmt(s);ExecStmts(ss);*t], currentSpan=span,*F}` |
| 3 | `execStmt` / `execStmt.union` | Same structural pre-pattern, complementary symbolic guards, two named alternatives | Both bind assignment `place` and `rval`; one requires `!isUnion(typeOf(local[i]))` and posts `SetLocal(place,rval)`, the other requires `isUnion(...)` and posts `SetLocal(place,EvalUnion(rval))`. They are independent clauses, not ordered arms. |
| 4 | fallback statement intrinsic | `owise` | `pre = K[ExecStmt(Intrinsic(i));*t]`; `post = K[*t]`; `selection = Owise(200)`. Its applicability depends on failure of competing lower-priority rules, not source position. |
| 5 | nonmatching `#selectBlock` branch | associative list tail, local rewrite within a constructor, symbolic guard | `pre = K[SelectBlock(SwitchTargets([Branch(mi,bb);*bs],default),v);*t]`; `req = !SwitchMatch(mi,v) && SwitchCanUse(v)`; `post = K[SelectBlock(SwitchTargets(bs,default),v);*t]` |
| 6 | `termReturnSome` | Consume continuation, update many distant/nested cells, pop list head, restore a saved frame | `pre` binds current function/frame, return local, and `stack = [savedFrame;*stack]`; `post` emits `SetLocal(dest,DecrementRef(val)); ExecBlockIdx(target)`, restores all saved frame fields and sets `stack=*stack`. One simultaneous pre/post pair is essential. |
| 7 | `termCallFunction` | Push old state into stack while replacing current frame fields; negative symbolic guard | `pre` binds caller/frame/locals/stack and call data; `req = !isIntrinsic(func)`; `post` changes K, current function and frame, and sets `stack=[StackFrame(old...);*stack]` simultaneously. |
| 8 | `setupCalleeClosure` | Nested `#as`, multiple list decompositions, complex guard, explicit priority 40 | `pre` binds `blocks @ [first;*_]`, locals, and `callerFrame @ StackFrame(...)`; `req` is the full bounds/type conjunction; `post` reserves locals, marks two caller locals moved, and schedules tuple argument setup; `selection = Explicit(40)`. |
| 9 | moving `#setArgFromStack` | Pattern and rewrite inside the head element of a list-valued stack cell | `pre.stack = [callerFrame @ StackFrame(...callerLocals...);*stack]`; `post.stack = [updateStackLocal(callerFrame,i,Moved);*stack]`; guarded by index and sort checks. This needs a list-pattern macro plus a constructor update, not ordinary slice mutation. |
| 10 | two thunk `#expect` rules | Deliberate nondeterminism | Identical `pre = K[Expect(thunk(x), expected, msg);*t]`; one `post = K[*t]`, the other `post = K[AssertError(msg);*t]`, both default priority. The ruleset yields both successors. An ordered Rust match would erase one. |

All ten fit the refutable-clause form. Cases 1, 5, 8, and 9 demonstrate why
RHS indexing and helper applications are *term construction* whose
definedness is justified by logical requirements; the body must not be run as
host Rust while compiling the definition.

### Representative KMIR surface excerpts

The difficult shapes remain recognizable:

```rust
#[k::rule]
fn exec_stmts(
    state @ Machine {
        k: k![ExecStmts(list![statement @ Statement(_, span), stmts @ ..]), tail @ ..],
        ..
    }: Machine,
) -> Machine {
    Machine {
        k: k![ExecStmt(statement), ExecStmts(stmts), ..tail],
        current_span: span,
        ..state
    }
}

#[k::rule]
#[k::owise]
fn intrinsic_fallback(
    state @ Machine { k: k![ExecStmt(StatementKind::Intrinsic(_)), tail @ ..], .. }: Machine,
) -> Machine {
    Machine { k: k![..tail], ..state }
}

#[k::rule]
fn expect_thunk_ok(
    state @ Machine { k: k![Expect(Thunk(_), _, _), tail @ ..], .. }: Machine,
) -> Machine {
    Machine { k: k![..tail], ..state }
}

#[k::rule]
fn expect_thunk_error(
    state @ Machine { k: k![Expect(Thunk(_), _, msg), tail @ ..], .. }: Machine,
) -> Machine {
    Machine { k: k![AssertError(msg), ..tail], ..state }
}
```

The two `expect` functions make nondeterminism apparent at item level. Their
order has no meaning.

## Pattern decisions

### As-patterns and or-patterns

Map K's `Pattern #as V` to Rust's `V @ Pattern`. Map K's `P1 #Or P2` to
`P1 | P2`. Apply Rust's rule that all alternatives bind the same variables at
compatible types. K forbids an as-pattern on the RHS; KRS should diagnose the
same condition while using Rust terminology.

### K sequences

Use a standard `k![...]` macro in pattern and expression position. Its pattern
form permits at most one sequence frame/splice. This keeps associative
continuation matching distinct from a `Vec` or deque and avoids implying
mutation. `k![..tail]` denotes the tail itself, including the empty sequence.

### Fixed configuration framing

Rust record `..` says fields were omitted, but the IR must synthesize typed
frames for the corresponding configuration fragments. A bound whole-state
as-pattern plus Rust struct update makes post-state framing concise. The
compiler must reject post expressions that accidentally duplicate, discard,
or change a frame outside the allowed K cell semantics.

### Collections

Do not pretend that `HashMap` or `HashSet` supports Rust destructuring. Use
`map!`, `set!`, and `list!` patterns. For example:

```rust
#[k::rule]
fn take(
    state @ Machine {
        k: k![Take(key), tail @ ..],
        store: map![key => value, rest @ ..],
        ..
    }: Machine,
) -> Machine {
    Machine {
        k: k![value, ..tail],
        store: map![..rest],
        ..state
    }
}
```

The pattern is relational: a set/map match may have multiple valid AC
decompositions, and the remainder is a symbolic collection. Map keys with
function symbols are evaluated only under K's collection-pattern restrictions.
Those checks belong in pattern type checking and IR validation.

### `requires` and `ensures`

Prefer attributes to Rust `if` guards. An `if` guard strongly suggests a host
boolean evaluated immediately. Within `k::requires` and `k::ensures`, the
expression grammar is a typed K term/logic expression: comparisons and
predicate applications build constraints. Use explicit combinators such as
`k::and![...]` where Rust's `&&` typing or short-circuit intuition would be
misleading.

Lower a rule as `Pre #And Requires` to `Post #And Ensures`, preserving the
postcondition as a separate IR node and source span. A satisfiable precondition
does not imply that the backend has proved the postcondition; an unsatisfiable
ensures can make the result bottom after application.

### Existential, fresh, and ordinary RHS-only variables

Use explicit item attributes so quantifier scope is visible and all names are
available to contracts:

```rust
#[k::exists(choice: Int)]
#[k::ensures(items.contains(choice))]
#[k::rule]
fn choose(Choose(items): Expr) -> Expr { IntValue(choice) }
```

For transition rules, existential variables are quantified at the top of the
RHS. K function equations scope them differently, so equation/function work
must not reuse the transition lowering blindly. `#[k::fresh]` is separate and
lowers through K's fresh-variable machinery. Reject unmarked RHS-only names;
support for K's `unboundVariables` should begin as an explicit raw/advanced
attribute because concrete backends need a generation strategy.

## Priority and nondeterminism

Each rule is an item. Several items may match, and several matches of one
collection pattern may succeed. The normalized ruleset should group eligible
clauses by numerical priority without imposing source order within a group:

```text
eligible(subject) = matches in the lowest applicable priority stratum
successors(subject) = union of every eligible match's constrained post-pattern
```

The exact backend behavior and K frontend desugaring remain the target oracle;
the point of the IR rule is to avoid compiling priorities prematurely into a
Rust match tree. Defaults lower to priority 50 and `owise` to 200, while
retaining their source spelling. Multiple `owise` clauses remain alternatives.

KRS should reject a multi-arm `match` in a `#[k::rule]` body. Authors express
structural alternatives with one Rust or-pattern, and semantic alternatives as
separately named rule items. This gives reordering the desired no-op behavior
and gives every transition a stable label and source span.

## Scope and remaining dependencies

R3 settles the ordinary transition-rule shape, not the complete logic layer.
The recommended clause surface depends on later work for:

- the exact typed expression API for matching-logic connectives and bottom;
- function/equation rule scoping and partiality;
- raw arbitrary patterns, nested cell fragments, and matching-logic aliases;
- frontend-exact priority/owise validation across backends; and
- concrete grammar/type details of `k!`, `list!`, `set!`, and `map!` patterns.

Those are R5/R7 or lowering questions. They do not block choosing the common
rule form: all evidence here favors independent refutable function clauses,
explicit relational attributes, and a quantified pre/post IR.

## Sources inspected

- `imp-semantics/.../expr.k`, `calc.k`, and `imp.k` (K 7.1.318)
- `mir-semantics/.../kmir.md` and `rt/data.md` (K 7.1.337)
- K user manual sections “Rule Structure”, “As Patterns”, “Collection
  patterns”, “Variables occurring only in the RHS of a rule”, and “`owise`
  and `priority` attributes”
