# Semantic gap inventory

The naive mapping—syntax and configuration as data types, rules as matches,
attributes as Rust attributes, and builtins as imports—is a strong starting
point. This inventory records where it stops being sufficient.

| K concept | Closest Rust concept | Important mismatch | Current direction |
|---|---|---|---|
| Sort and subsort | Marker trait and `impl` | K sorts are open and subsorting is transitive term membership | Use traits for open sorts; compiler closes membership |
| Production | Struct or enum variant | Also defines an object-language parser production and Kore symbol | Use data item plus syntax/symbol attributes |
| Token sort | Validated newtype | K token sorts are domain values with hooks and no constructors | Dedicated `#[k::token]` contract |
| Configuration | Nested structs | Cells have defaults, labels, framing, multiplicity, collection types, and generated top cells | Structs, cell wrappers, restricted initializer, and framing macros |
| Rewrite rule | Refutable function clause | Rules are unordered, relational, possibly nondeterministic, and symbolic | One independent `#[k::rule] fn` pre/post clause per rule |
| Local rewrite | Record update | K can rewrite several distant subterms simultaneously while framing the rest | Infer a whole-state pre/post pattern from field updates |
| K sequence (`~>`) | Queue/deque | It drives evaluation contexts and has special cell behavior | Standard `KSequence` type and `k![...]` patterns |
| Function rule | Refutable equation clause | K functions are equational simplifiers; they may be partial or symbolic | Function symbol plus independent `#[k::equation]` clauses |
| `owise` and priorities | Fallback arm / arm order | K priority is explicit and applies across separate rules | Explicit attributes; never infer from file order |
| Strictness and contexts | Evaluation order / closures | K generates heating/cooling rules around a hole and a result predicate | Typed strategy attributes plus explicit context and context-alias clauses |
| `KResult` | Marker trait | Membership is open and controls when heating stops | Open marker sort; auto-generated predicate lowering |
| Arbitrary concrete syntax | Rust syntax/macros | K defines the parsed object language, which may not resemble Rust | Syntax templates plus precedence/associativity metadata |
| Syntactic lists and overloads | List alias or open sort trait | K overload selection follows the subsort lattice during parsing | Attributed list aliases/traits plus explicit overload metadata |
| Map/set/list patterns | Collection destructuring | K matching may be associative/commutative and bind a collection remainder | K-specific collection pattern helpers |
| Collection cells | `Vec`, `HashMap`, `Option` fields | K cells have structural identity and specialized matching/indexing | Nominal cell wrappers with multiplicity/type attributes |
| Variables and casts | Inferred bindings and `as` | K infers maximal sorts and has semantic, strict, and projection casts | Rust-like annotations where possible; explicit cast families |
| Fresh variables | Generator call | Freshness is supplied by rewriting semantics and can be sort-specific | Explicit `fresh::<T>()` usable only in relational items |
| RHS-only/existential variables | No direct ordinary equivalent | A rule may introduce symbolic/arbitrary values rather than compute them | Explicit existential binder or symbolic constructor |
| `requires` / `ensures` | Contract attribute | Conditions are object `Bool` terms; `ensures` extends the path condition | Typed attributes accepting `Term<Bool>`, not host guards |
| Matching-logic connectives | No ordinary equivalent | Patterns denote sets and may contain bottom, conjunction, disjunction, quantifiers | Typed `MlPattern` with an explicit `ml!` island |
| Reachability claim | Contract-like clause | Claims quantify paths and are proved, not executed as tests | Refutable clause with explicit `#[k::claim(all_paths/one_path)]` modality |
| Macro and alias rule | Macro / bidirectional pretty-printer | K macros rewrite terms statically; aliases reverse before unparsing | Separate restricted compile-time rule kinds |
| `anywhere` rule | Traversal rewrite | Applies below the state focus and is not an ordinary recursive function; K 7.1.337 cannot preserve it on Haskell | Explicit clause kind with termination warnings and backend-capability rejection |
| Simplification lemma | Rewrite lemma | Backend may apply it at any time; soundness is author responsibility | Distinct lemma item/attribute, never ordinary function arm |
| Hooks and builtins | Imports and intrinsics | Hooks connect symbols/sorts to backend implementations and may vary by backend | Versioned stdlib imports plus explicit hook escape hatch |
| Modules and requires | Modules and `use` | K has separate file and module DAGs and syntax visibility | One KRS module model lowered to both layers |
| Generated predicates/projections | `is` checks / field access | K generates logical partial functions from sorts and named fields | Compiler-generated APIs with stable names |
| Record-like KApply patterns | Struct patterns | K patterns can omit named children of prefix productions after lowering | Native record patterns where the production is eligible |
| Backend-specific modules/attributes | `cfg` | K symbolic and concrete backends may deliberately receive different rules | Rust-like `cfg(k_backend = "...")`, used sparingly |

## The highest-risk gaps

### 1. Openness and exhaustiveness

KWasm declares abstract sorts and extends them across modules and formats. This
is not an edge case; it is a core modularity technique. Traits preserve that
shape, but open traits cannot support enum-style exhaustive matching. KRS must
diagnose the difference and perhaps distinguish closed constructor enums from
open semantic sort traits in match exhaustiveness.

### 2. Relational versus ordered matching

Two applicable K rules normally describe two possible transitions. Two
applicable Rust match arms describe one transition chosen by source order.
Pretending these are the same would make even simple concurrency or symbolic
branching definitions misleading. Rule items need independent identity and
explicit priority.

### 3. Object-language grammar versus term data

Rust data declarations describe an AST, not the language that produces it.
IMP alone needs literals, parentheses, unary and binary operators, dangling
`else` handling, precedence groups, associativity, brackets, tokens, and pretty
printing. We cannot claim syntax is “just structs and enums” until this second
layer has a coherent notation.

### 4. Symbolic patterns and undefinedness

In concrete Rust, a guard evaluates to `true` or `false` and a function either
returns or panics. During K symbolic execution, matching and side conditions
produce constraints, and a partial function can denote bottom. KRS therefore
keeps object `Term<Bool>`, matching-logic `MlPattern`, and `Option` datatypes
distinct. The IR retains bottom, definedness, binders, and path conditions
explicitly.

### 5. Evaluation strategy

K's `strict`, `seqstrict`, contexts, context aliases, holes, hybrid results, and
custom result sorts generate heating/cooling rules. Rust's own eager evaluation
does not describe this because K is defining another language's evaluation.
Attributes cover the common case; arbitrary contexts need a first-class form.

### 6. Structural and associative framing

Rust's `..` is a good visual model for omitted fixed fields. K additionally
frames cell bags and matches associative/commutative collections with remainder
variables. Those operations can branch and cannot be reduced to ordinary Rust
destructuring.

## Features that map unusually well

The mismatch list should not obscure the useful overlap. Rust gives us strong
surface forms for nominal constructors, nested record patterns, `@` bindings,
or-patterns, `_`, modules and visibility, generics, marker traits, explicit
imports, namespaced attributes, and restricted pure helper functions. The
project is plausible precisely because these cover most of what authors read
line-by-line in a K definition; the K-specific forms can concentrate around
relational behavior, grammar, and symbolic logic.

## Evidence in the initial corpus

- IMP's `expr.k` reopens `Expr`, builds `Value` and `KResult` through subsorts,
  and uses precedence, associativity, brackets, strictness, and short-circuit
  rules in a very small file.
- IMP's `calc.k` demonstrates that a rule can simultaneously consume the `k`
  cell and update the `env` cell while framing everything else.
- KWasm's `wasm.md` declares deliberately abstract sorts such as `TypeDefn` and
  extends instruction and statement families across modules. Its overloaded
  syntactic lists show why openness affects parsing as well as type checking.
- KMIR's `rt/configuration.md` shows a realistic nested state with defaults and
  static stores, while `kmir.md` uses K sequences, as-patterns, side conditions,
  `owise`, function equations, and definedness attributes in current style.
- The K user manual additionally exposes collection cells, context aliases,
  fresh and existential variables, matching-logic patterns, and reachability
  claims that the small IMP definition does not exercise.
