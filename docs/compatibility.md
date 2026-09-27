# Compatibility decisions

The port follows the combined Booster and Kore backend semantics described in [backend-port.md](backend-port.md).
When the engines, their frontend policies, or their recorded outputs disagree, the contracts below identify the intended Rust behavior and the evidence used to check it.
These contracts do not depend on development notes or local measurement logs.

The K reference is [`runtimeverification/k` at `4a46d1231473b599c699160132fd6e76a5c46406`](https://github.com/runtimeverification/k/tree/4a46d1231473b599c699160132fd6e76a5c46406), version `v7.1.337`, as recorded in [the differential manifest](../scripts/reference-differential.toml).
The backend reference is [`runtimeverification/haskell-backend` at `ad54c7a55085b726c4d3c2728242a7e0695b0439`](https://github.com/runtimeverification/haskell-backend/tree/ad54c7a55085b726c4d3c2728242a7e0695b0439).
Source paths below are relative to these pinned repositories.
Fixture provenance records the commands and pins used for committed outputs; a source explanation alone must not be presented as a live measurement.

## Backend scope

LLVM-specific runtime behavior, the behavior of the external Bison/Flex parser generator, LLVM decision-tree warnings and LLVM coverage instrumentation are outside the Haskell-backend compatibility contract.
The CLI interoperability contract includes rendering parser sources, invoking the system Bison/Flex/C toolchain, installing executable or shared-library parser artifacts, and preserving their parser-output bytes; the Bison implementation itself remains external to Rust.
The conformance expectations retain each affected case or step with its concrete `llvm-only` reason.
An LLVM expected output does not define the behavior of a hook or of a definition that `kore-parser --verify` rejects.
A hook's behavior is defined by the K source that declares it: `domains.md` for K's builtin hooks (see [Hook specification exceptions](#hook-specification-exceptions)), `substitution.md` for the `SUBSTITUTION` hooks, and blockchain-k-plugin `plugin/krypto.md` for the `[crypto]` hooks, at the revision `651a2db5` of the pinned KEVM and at `207ae512`, the revision the hook capability inventory records (the two agree on every hook this section describes, apart from the point productions noted below); a case that needs a hook neither pinned Kore engine evaluates stays `llvm-only` unless k-rust implements that hook as described below.
The [hook capability inventory](../crates/k-rust/tests/fixtures/hook-capabilities.toml) records implemented and unsupported operations for the prelude and `[crypto]` hooks; the `SUBSTITUTION` hooks are classified by the `substitution_hooks_have_an_enforced_external_capability_classification` test beside it.

Among the implemented hooks, four groups have no evaluator in either pinned Kore engine and no `rule` in their declaring K source that defines them.
(The other implemented hooks without a builtin evaluator in those engines, `STRING.ne`, `STRING.le`, `STRING.gt` and `STRING.ge`, are defined by `domains.md` rules in terms of `STRING.eq` and `STRING.lt`.)
The console IO hooks `IO.getc`, `IO.putc`, `IO.read` and `IO.write` are evaluated only by ordinary execution (see the console paragraph below); Kore's IO module registers only `IO.logString` (`kore/src/Kore/Builtin/IO.hs`), and Booster has no IO builtin module.
The `KRYPTO` hooks `bn128add`, `bn128mul`, `bn128ate`, `bn128valid`, `bn128g2valid`, `sha256raw` and `ripemd160raw` are declared in `plugin/krypto.md`; Kore's `Krypto` module registers none of them (`kore/src/Kore/Builtin/Krypto.hs`), and Booster has no `KRYPTO` builtin module.
`SUBSTITUTION.substOne` is declared in `substitution.md`; Kore has no `SUBSTITUTION` builtin module (`kore/src/Kore/Builtin.hs`), and neither has Booster.
k-rust implements these eight hooks because each declaration fixes the hook's value on every input of the domain stated below, independently of any backend.
Where the declaration gives no value, the result is undefined (`#Bottom`), as for other partial hooks.
Where the value depends on a subterm the call cannot see, the application stays unevaluated.
Such a subterm is a variable or an application of a non-constructor symbol, and it may denote any constructor term of its sort.

`KRYPTO.sha256raw` and `KRYPTO.ripemd160raw` return the 32-byte SHA-256 digest and the 20-byte RIPEMD-160 digest of their `Bytes` argument.
`plugin/krypto.md` declares `Sha256raw(Bytes)` and `RipEmd160raw(Bytes)` as "the same hash function as those named above except that they return a raw byte string", and every byte string has a digest.
An argument that is not a `Bytes` literal stays unevaluated.

The BN128 hooks are declared on points of the BN128 curve written `(x, y)` for G1 (`syntax G1Point ::= "(" Int "," Int ")"`) and `(x1 x x2, y1 x y2)` for G2 (`syntax G2Point ::= "(" Int "x" Int "," Int "x" Int ")"`), where `(0, 0)` and `(0 x 0, 0 x 0)` denote the point at infinity.
At plugin `207ae512` the two point productions carry `symbol(g1Point)` and `symbol(g2Point)`; at `651a2db5`, the plugin of the pinned KEVM, they carry no `symbol` attribute and compilation generates their Kore names.
Both revisions declare the same point productions otherwise, so every statement below holds at both.
The Kore name of a point constructor is a property of the compiled definition, not of the declaration, so a BN128 hook takes as the point constructor of G1 the definition's only constructor of result sort `G1Point` with two `Int` arguments, and as that of G2 its only constructor of result sort `G2Point` with four `Int` arguments.
A BN128 hook reads a point only from an application of the point constructor with `Int` literal coordinates.
The coordinates must lie in `[0, p)` for the base field modulus `p`, and must be the point at infinity or satisfy the curve equation; for G2 the point must also lie in the order-`r` subgroup G2 of the twist curve.
A point-constructor term with `Int` literal coordinates that fail these conditions, any other constructor term, and any domain value or collection in a point position is not a point: `isValidPoint` is `false`, and `BN128Add`, `BN128Mul` and `BN128AtePairing` are undefined.
If the definition declares no constructor with the point signature, every constructor term in a point position is not a point.
If it declares several, the declaration does not say which of them writes the point, so an application of one of them is treated like a variable, while a constructor term with another signature is still not a point.
An argument that contains a variable, a conjunction or an unevaluated function application where the reading needs a value leaves the call unevaluated, unless another argument is already not a point, or the two pairing lists have known, different lengths.
Reason: the declarations define the hooks on the points written with the point productions only; constructors are free, so a constructor term with another head denotes no point in any model, while a variable or function application may denote a point or not.
On that domain:

- `KRYPTO.bn128valid` (`isValidPoint(G1Point)`) is `true` for every G1 point. G1 has cofactor 1, so a point on the curve, which the declaration asks for, is a point of G1.
- `KRYPTO.bn128g2valid` (`isValidPoint(G2Point)`, `symbol(isValidG2Point)`) is `true` for every G2 point and `false` for a point on the twist curve outside the subgroup G2. The declaration calls a `G2Point` a point on G2 and defines the pairing through discrete logarithms of G2 points, which exist only in the subgroup, so validity is exactly the domain of the pairing.
- `KRYPTO.bn128add` (`BN128Add(G1Point, G1Point)`) returns the G1 point-constructor term of the sum P + Q in G1, with `(0, 0)` as the identity.
- `KRYPTO.bn128mul` (`BN128Mul(G1Point, Int)`) returns the G1 point-constructor term of n·P for every `Int` n, computed as (n mod r)·P with the non-negative residue. Multiplication by an integer is defined for every integer, and r·P is the identity because G1 has prime order r.
- `KRYPTO.bn128ate` (`BN128AtePairing(List, List)`) on lists of equal length, is `true` iff the product of the pairings e(P_i, Q_i) is 1. With P_i = a_i·G and Q_i = b_i·H for the generators G and H, the product is e(G, H) raised to the sum of a_i·b_i, so it is 1 exactly when that sum is zero modulo r, which is what the declaration states. Two empty lists give `true`, and lists of different lengths give the undefined result.

`SUBSTITUTION.substOne` (`T [ V / X ]`) returns the capture-avoiding substitution of the `KItem` V for the free occurrences of the `KVar` X in T.
A production with the `binder` attribute binds the `KVar` of its first nonterminal in its last nonterminal (`substitution.md`, "The `binder` Attribute"), and a bound `KVar` that would capture a free `KVar` of V is renamed.
A renamed variable gets a fresh name `<name><n>` that occurs nowhere in T, V or X; the hook is `impure`, so the declaration does not fix the fresh name, and any fresh choice denotes the same term up to renaming of bound variables.
The call evaluates only when X is a `KVar` token and every opaque subterm of T and V has a `KVar`-free sort.
An opaque subterm is a variable or an application of a non-constructor symbol, including a collection rest.
k-rust treats a sort as `KVar`-free only when, by the definition's constructors, collection symbols and subsorts, no constructor term of that sort can contain a `KVar` token; such a subterm is copied unchanged, because substitution is the identity on every one of its values.
Otherwise the call stays unevaluated until its arguments are refined, because whether X occurs in an opaque subterm, and which names are free in it, depends on its instance.
A target that is not a `KVar` token also stays unevaluated: the declaration substitutes only for a `KVar`.
When the substitution makes two keys of one `Map` equal, the result is undefined, since a map has no duplicate keys; when it cannot tell whether two such keys are equal, the call stays unevaluated.

The `FLOAT` hooks are pure: Kore registers no `Float` builtin functions (`kore/src/Kore/Builtin.hs`), and Booster has no `FLOAT` builtin module (`booster/library/Booster/Builtin.hs`).
k-rust implements the `FLOAT` hooks because `domains.md` specifies them as IEEE 754 operations, which fixes each result without reference to a backend.
A `Float` is an IEEE 754 value whose precision and exponent width are named by its suffix (`p24x8` is `binary32`, `p53x11` is `binary64`), the arithmetic hooks round to nearest with ties to even (their `smt-hook` attributes), and the comparison hooks are IEEE 754 comparisons (`==Float` is IEEE 754 equality, so `0.0 ==Float -0.0` holds and `NaN ==Float NaN` does not; `=/=Float` has no hook and is the K rule `notBool (F1 ==Float F2)`).
Where `domains.md` names an operation without settling an edge case, k-rust applies the IEEE 754 rule: `Float2Int` rounds ties to even, and `minFloat`/`maxFloat` are IEEE 754-2019 `minimumNumber`/`maximumNumber`, which ignore a NaN operand and order `-0.0` below `0.0`.
The implementation covers `binary32` and `binary64`, with `rootFloat` at degree 2.
A ground value in any other format is a builtin error that names the format; any other root degree and the `FLOAT` hooks the inventory lists as unsupported give the unsupported-hook outcome below.
The divergence is an extension: for every ground `FLOAT` application k-rust evaluates, the pinned Haskell backend has no evaluator and so no value, and k-rust supplies the value `domains.md` specifies.
No pinned Kore engine can serve as an oracle for these hooks, so the differential manifest's excluded `wasm-execution` row names the pinned LLVM execution of the WASM semantics as the alternative oracle.
No gate runs that LLVM execution and no LLVM result is committed; an LLVM result obtained by hand is evidence to check against `domains.md`, not the definition.
The row's only gate is the k-rust-only local gate `krun_executes_float_fixture_to_pinned_kore_results`, which pins k-rust's own results for rounding ties, square root, signed zero, NaN equality, `Float2Int` rounding and `maxValueFloat`.

Ordinary `kcompile --backend rust` output is directly runnable through `krun --definition DIR`.
The runtime validates the artifact identity, schema version, Rust backend identity, and every payload digest before use.
The CLI and Rust library are the compatibility boundary; individual files and their serialization inside the compiled directory may change between releases.
LLVM compilation does not publish a Rust runnable artifact.
The conformance driver retains LLVM output for its frontend comparison and accounts for one explicit, separate Rust compilation when execution steps need a runnable directory.

A hook without an evaluator or applicable K equation must report an unsupported-hook error when every argument is constructor-like.
Symbolic applications remain unevaluated.
This follows the missing-evaluator checks in `kore/src/Kore/Equation/EvaluationStrategy.hs` and the port's completion contract; an exclusion must not turn the unsupported outcome into a successful execution.

Ordinary committed execution implements the console operations `IO.getc` and `IO.read` on descriptor 0 and `IO.putc` and `IO.write` on descriptors 1 and 2.
Their input cursor and ordered descriptor transcript are branch-local, and rolled-back candidates cannot deliver bytes.
Input is pre-buffered before execution; live output is delivered exactly once from the selected `--strategy any` trace.
Other descriptors and IO hooks remain unsupported, pure simplification receives no console state, search rejects `--io on`, and RPC does not perform host IO.

Whenever a run takes console input from standard input, standard input is read to end of file before the first step: under `--io on`, and under `--io off` when the definition declares `$STDIN` and the program is not itself read from standard input.
It is read then because console input is part of the initial state, not a host resource that execution consumes.
Execution evaluates rewrite candidates tentatively and may fork, so a read by a rolled-back candidate or by a sibling branch must not change the bytes another branch reads.
The evaluator therefore holds no process handles: every branch reads one immutable byte sequence through its own cursor, and its reads are a function of that sequence and the cursor.
The result of a run is then a function of its command-line inputs, the files they name, and the bytes of standard input, and not of when those bytes arrive.
Nothing is lost by waiting for end of file: console output is written to the process's standard output and error only after execution, from the selected leaf's transcript, so no run can prompt for input and read a reply.
A run that must terminate on a terminal needs its input ended (Ctrl-D) or redirected, as the CLI notes when standard input is a terminal.

Pre-buffered input is tokenized differently under the two IO modes, because the stream rules generated for a `stream="stdin"` cell (`STDIN-STREAM` in `domains.md`) depend on the mode.
Under `--io on` the `stdinGetc` rule applies only while the stream's `#buffer` holds no delimiter, and moves the pre-buffered bytes into it one `#getc` at a time, so each `#parseInput` sees one token as an interactive stream supplies it: a `String` token together with the delimiter that ends it, and a lone delimiter before an `Int` token, which `stdinTrim` drops.
Under `--io off`, and therefore in search, `stdinGetc` cannot apply and, unless the program itself is read from standard input, the whole input with its trailing newlines replaced by exactly one is the initial `#buffer($STDIN)`.
`stdinParseString` then takes the whole remaining buffer as one `String`, and `stdinParseInt` takes the prefix before the buffer's first delimiter.
When that buffer holds more than one character and begins with a delimiter, because the input does or because two delimiters are adjacent after a token, the prefix is empty, `String2Int("")` is undefined, and the rule produces an undefined result where the interactive stream would have trimmed the delimiter and read the next token.
The two modes therefore agree on a stream program's input only where these forms coincide; this is the input precondition of C9 in the [comparison contract](#comparison-contract).

## Frontend policy

The Rust backend uses K's Haskell policies for existential right-hand-side variables, variables bound through `requires`, and excluded module attributes.
`--backend haskell` is an alias for Rust, `--backend kore` is rejected, and `--backend llvm` uses LLVM frontend policies.
The reference checks are in `kernel/src/main/java/org/kframework/compile/checks/CheckRHSVariables.java` and `kernel/src/main/java/org/kframework/kompile/Kompile.java`.
[Definition checks](../crates/k-rust/tests/definition_checks.rs) exercise these acceptance boundaries.
Anywhere rules have the explicit supported-superset contract below.

## Variable sort annotations

A semantic cast `t:S` requires the sort of `t` to be less than or equal to `S` (K user manual, "Semantic casts"); on a variable this is an upper bound, in both inference engines.
The variable's sort is then inferred like any other variable's: the same sort at every occurrence, maximal among the solutions, so `rule bar(X:Big) => foo(X)` with `foo(Small)` gives `X` the sort `Small` and compiles to a pattern matching `bar` of an injection of a `Small` into `Big`.
To make an annotation exact, so that a narrower occurrence is a sort error, write the strict cast `X::S`.
This is a recorded divergence from the pinned K frontend.
In `semcast3` (`rule bar(X:Big) => foo(X) ~> a(X)`) and `semcast4` (`rule bar(X:Big) ~> foo(X) => a(X)`), `a(X)` is ambiguous between `aS` over `Small` and `aF` over `Foo`.
Under the manual's bound `X` may be any sort at most `Big`, and `foo(X)` requires it to be at most `Small`; `aF` would also need it at most `Foo`, and no sort lies below both, so exactly one reading is well-sorted: `aS`, with `X` at `Small`.
Rust accepts both rules with that reading; the pinned frontend rejects them.
The compile manifest records both as `expect = "port-accepts"` with this reason and with `reference-error = "Unexpected sort Big for variable X"`, the reference diagnostic the divergence is about.
The compile gate runs both compilers on them: it requires the reference to reject with output containing that diagnostic, so a rejection for any other cause (a crash, a failed heap reservation, a different error) fails the gate, and requires Rust to accept with a definition `kore-parser` accepts; it fails when either side changes.

## Sorts of compiled terms

`inj{A, B}` denotes the embedding of `A` in `B`, and the emitted definition declares subsort axioms only along the subsort order and none into `K`, so the compiler builds an injection only when `A <= B` along those axioms, extended with every sort other than a parser sort (`K`, `KItem`, `KConfigVar`, `KBott`, `KLabel`, `KList`, `KString`, `#`-prefixed sorts) below `KItem`.
A `KItem` is placed at a `K` position as a one-element sequence, and at a position above `K` (only a parser sort such as `KList` can be: a user sort is below `KItem`, so a user sort above `K` is a circular subsort) as the injection of that sequence, `inj{K, S}(inj{A, KItem}(t) ~> .K)`; no single injection crosses from below `K` to above it. Semantic-cast resolution accepts a variable's sort under a cast bound by the same placement relation.
The positive `isS(X:S) => true` sort-predicate rule exists only when `S` is placeable at the predicate's `K` argument in its module's subsort order.
An unplaceable sort keeps its predicate production and the `owise` rule `isS(K) => false`; `K` keeps its single positive rule.
The standalone `generate_sort_predicate_rules` API returns `Result` because resolving that order can fail.
A term whose sort is not below the sort of its position (an argument, a rewrite side, a `requires` or `ensures` clause at `Bool`) is rejected at the `add sort injections` stage with the sentence's source location; so is a semantic cast whose target is neither at or above its operand's sort (an upcast) nor strictly below it (a downcast, realized by `project:S`).
A parametric production's sort parameters are instantiated together by one solver: an instantiation fits when every argument's sort is at or below its instantiated argument sort and, when the position's sort is concrete and the result mentions a parameter, the instantiated result is at or below it; the least fitting instantiation in the pointwise order on the instantiated argument sorts is chosen, so `use2(X:MInt{8}, Y:MInt{16})` with `MInt{8} < MInt{16}` is instantiated at `16` and `make(X:MInt{8})` of `{W} R{W} ::= make(MInt{W})` at an `R{16}` position also at `16`. When no instantiation fits the position, the least one fitting the arguments is chosen and the position decides; an argument above every declared instance is rejected, and several incomparable least instantiations are rejected as ambiguous.
A parameter that occurs in no argument sort but in the result is ordered by nothing but its result, so the order then also compares the instantiated result sort. A result that is the parameter itself takes the position's sort. Otherwise the parameter's candidates are the values under which the whole instantiated result is the position or a declared sort below it (so `{W} MInt{MInt{W}} ::= mkn` with only `MInt{MInt{B}}` declared has the single candidate `B`, even when `MInt{A} < MInt{B}`), and the least of those is chosen: with `{W} MInt{W} ::= mk`, unrelated `A` and `B`, `MInt{A} < MInt{B}` and `Wide ::= MInt{B}`, `mk:Wide` is `mk{A}`. Two incomparable least instances that fit, such as `MInt{C}` and `MInt{D}` below `Pair`, are ambiguous. When no instance fits, the parameter stays a sort variable and the position rejects the term.
The position the solver sees is the sort the application is placed at: a cast's target when the application carries a semantic cast, otherwise its argument sort in the enclosing production, the rewrite's sort (a cast on a rewrite gives both sides its sort), or `Bool` for a `requires` or `ensures` clause. So `wrap(Z:A):Wide` with `{S} MInt{S} ::= wrap(S)` and `Wide ::= MInt{B}` is instantiated at `B` although its least instance is `A`, and it is ambiguous when two incomparable instances fit the target. When no instance fits a cast's target, the least instance fitting the arguments is kept and the cast is decided on its result: a target strictly below it is a downcast, whose projection places the operand at `K`, where that same instance is the least, and any other target is an incomparable cast. A larger instance whose result lies above the target does not justify a downcast: the operand inside the projection is instantiated at `K`, so the projection would not contain that instance.
An enclosing parametric production is solved after its arguments, from the arguments' sorts. While it is solved, each argument is placed at its declared sort, with the enclosing result parameter replaced by the enclosing position when the enclosing result sort is a bare parameter, and every other parameter replaced by an unconstrained sort variable. The argument is placed again at the solved instance when it is built. An enclosing position therefore fixes an inner instance in two ways. While the enclosing production is solved, an argument whose declared sort contains the enclosing result parameter, when that result is a bare parameter, is solved at the enclosing position. When the enclosing instance is built, an argument whose own instance was left open while the enclosing production was solved takes it from the instantiated argument sort. Such an argument is one whose parameters no argument of its own and no concrete position constrained. For example, with `{T} MInt{T} ::= inner2`, `{S} MInt{S} ::= outer(MInt{S})` and `MInt{A} < MInt{B}`, `outer(inner2):MInt{B}` is `outer{A}(inner2{A})`: `outer` takes the least instance that fits the cast, and `inner2`, which nothing else constrains, takes the instance of `outer`'s argument. With `{S} S ::= wrap(S)`, `{T} T ::= inner(MInt{T})`, unrelated `A` and `B` and `MInt{A} < MInt{B}`, `wrap(inner(X:MInt{A})):B` is `wrap{B}(inner{B}(inj(X)))`, while `wrap(inner(X))` without the cast is `wrap{A}(inner{A}(X))`.
Label sort parameters are therefore never written: a label in a rule, claim, context, context alias or configuration that carries sort parameters is rejected, naming the label and its parameters, instead of being re-solved: `load_structured` rejects it on the caller's own sentences before configuration expansion (`LoadError::LabelParameters`, since expansion recognizes cell wrappers by name and would drop a parameter on one), `compile_loaded_definition` rejects it in any other `LoadedDefinition` before any pass runs (stage `REJECT_LABEL_PARAMETERS`), and `sentence_typing` rejects it for that sentence. The instance is always the solver's: an upcast on an argument does not raise it (`wrap(s(X):Num)` with `{S} Wrap ::= wrap(S)` is `wrap{Nat}`), a cast on the whole term or its position fixes a parameter that occurs in the result, and an instance above an argument's sort is reached only through a projection (`wrap({X}:>Num)`), exactly as in source text.
A sort parameter that occurs in neither an argument sort nor the result sort (`syntax {S} Int ::= size()`) is constrained by nothing, so every use of the production is universally quantified over it (a sentence sort variable, `Lblsize{#SortParam{Q}}()`); no source or structured term can fix it.
Rejection rather than honouring is deliberate: honouring a supplied parameter would let a caller write terms source text cannot, while silently re-solving it would compile a term other than the one supplied; rejection keeps structured input exactly as expressive as source text and never rewrites it.
The instances this leaves unwritable cannot change behaviour a definition can observe: every rule over a phantom parameter is universally quantified over it, and a rule's own label instance is always the solver's.
Execution terms are unaffected: their KORE symbols carry every instance explicitly.
Honouring a present parameter as an assertion is a compatible later extension, since it only accepts terms that are rejected now; it becomes worth its cost when a consumer needs to write a specific instance source text cannot derive.
A sort that mentions a sort parameter stands for every instance of it, since a sentence's sort parameters are universally quantified, and productions with sort parameters declare no subsorts: `MInt{Q}` is below itself and below `KItem`, and not below `MInt{8}`.
A cast on a K sequence, an injected label, or a sorted variable is compared with the operand's own sort like a cast on an application; a cast on a rewrite or `as` pattern is the sort both sides are injected at; an `as` alias variable with its own sort is placed at that sort like the pattern, and only a sortless alias takes it.
The check applies to every rule-like sentence `compile_loaded_definition` emits, whether parsed from source, supplied through `load_structured`, or edited in a `LoadedDefinition`; a pass that meets an ill-sorted term earlier may reject it first with its own message.
[Sort-injection tests](../crates/k-rust/tests/sort_injections.rs) pin the rejections and their controls.
`kompile::sentence_typing` (or a `SentenceTyper` built once per module) reads the same computation on a loaded rule or claim: it resolves the sentence's semantic casts and projects a body with a rewrite into its left and right branches, as compilation does before injection, and reports for each path (the field, then rewrite sides, as-pattern children, application arguments with casts included, and sequence items) the sort injection places the term at and the sort its position requires, computed by the injector on the resolved and projected term; a path typed differently in the two branches is reported per branch. It returns the compiler's own error for a sentence the checks reject.
It types in the order injection runs in, where every user sort is declared below `KItem`; it reports no sort for `#cells`, `#dots`, `#noDots`, and variables nothing types, places an authored cell's body at its content sort, and reports a cast operand's requirement as the cast's sort (below a downcast the operand's own sort is above it).
[Typing-view tests](../crates/k-rust/tests/sentence_typing.rs) check it on hand-picked positions, on every loaded rule of the prelude, and against the injections the compiled definition contains.

## Resource bounds

Simplification budgets and term nesting depth are k-rust's own resource contracts, specified in [backend-port.md](backend-port.md#simplification-iteration-budgets) and [backend-port.md](backend-port.md#json-depth-policy); this section records how they differ from the reference and why.

The simplification budget bounds the rewrite rounds of one fixed-point lineage: sibling subterms each receive a copy of the current budget, and the terms a rewrite produces inherit that rewrite's reduced budget.
Booster instead counts passes of its whole-term equation loop against `--equation-max-iterations` (`booster/library/Booster/Pattern/ApplyEquations.hs`, `iterateEquations`).
The bounded surfaces of both default to 100 (k-rust's `kore-simplify` command and RPC `simplify` method are unbounded), but equal numbers do not denote the same cut, and k-rust's `--max-simplification-iterations` option and RPC `max-simplification-iterations` parameter are not translations of the Booster option.
The reason is the budget's purpose.
An equation replaces a term with one equal to it, so the budget never decides what a pattern denotes; it guards only against a chain of rewrites that does not terminate.
Non-termination is a property of one chain of rewrites of one subterm, so the count belongs to that chain; a whole-term pass count measures a chain's length only through the evaluation schedule, that is, through how far one pass advances each chain, which does not bear on whether the chain terminates.
Inheriting the reduced budget keeps an expanding equation from resetting its own cap.
Where the budget is exhausted, the retained configuration is still equal to the one being simplified, but it can be less simplified, and a step that needs the missing value may not be taken; the outcome on each surface, and the `SimplificationBudgetExhausted` diagnostic that marks this incompleteness, are specified in backend-port.md.

Term readers and writers impose no nesting-depth cap: depth is not part of what a term means, so a fixed cap would reject well-formed input.
Their capacity is set by the host thread's stack and the process memory, as listed in [backend-port.md](backend-port.md#json-depth-policy).

## Formal parameter preference

A formal sort parameter of a parametric production is not a variable of the sentence (K user manual, "Parametric productions and `bracket` attributes").
Sort inference therefore orders the readings of a sentence only by well-sortedness, by maximality over the sorts of its variables, and then by `prefer`/`avoid`; a sentence with several readings left after these steps is an ambiguous parse error (K user manual, "Variable Sort Inference" and "Symbol priority and associativity").
The `K`/`KItem`/`Bag` preference on formal parameters only chooses how a kept reading is instantiated: it compares parameter vectors that keep the same set of well-sorted readings and never removes a reading that some vector types.
A parameter that the kept readings leave free is instantiated at `K` by that preference.
Alternatives that are equal once bracket nodes are erased are one reading, not several: `rule #Ceil(X:W) => (#Top) [simplification]` has one parse, `#Top{K}`, exactly as without the brackets.
The concrete instances of one parametric production are one production of the parsed term, so they never form separate readings either.
The instance a kept reading was parsed at is not part of the loaded sentence: rule, claim, context, context-alias and configuration bodies are loaded with no label sort parameter, since source text cannot write one, and sort injection instantiates every parametric label from its arguments and position ([Sorts of compiled terms](#sorts-of-compiled-terms)).
Program terms keep the instance the parser chose. Macro expansion runs before sort injection, so where a macro rule's head is parametric it reads instances from the typing view (`SentenceTyper`, the typing compilation gives each position): a head's instance from the typing of its macro rule, and an application's from the typing of the sentence it stands in, taken after its arguments are expanded and after every earlier rewrite of that sentence (a program application keeps its parsed instance until something below it is rewritten; a standalone term is typed as a rule body). The instance is the label's own, as injection instantiates it, not the sort a downcast places the application at. A macro rule applies only to an application whose instance agrees with its head's on every parameter both fix; a parameter the typing leaves open agrees with every value. Where the sentence does not type yet, the instance is unknown and only a head that fixes no parameter applies; such applications are retried after later rewrites until nothing changes, and one still unknown then is left for injection to reject. Every other comparison of a rule's label with a production or term label (the macro table, `anywhere`, and rule-by-label lookups) is by the label's name.

The pinned K frontend also uses the parameter preference to choose between distinct readings, by sending a parameter to `K` where that makes another reading ill-sorted.
Rust does not.
Where this makes the reference pick the non-`prefer` reading, Rust takes the `prefer` reading (`#fun2` over `#fun3` in `#fun(P => B)(A)` when both are well-sorted).
Where no `prefer` or `avoid` separates the readings, Rust reports the ambiguity and the conformance expectations record the step as `port-reports-ambiguity`.
In `issue-2287-simpl-rules-in-kprovex`, the claim `<k> c => 2 #And n +Int n </k>` of `a5-spec.k` reads as `(2 #And n) +Int n` and as `2 #And (n +Int n)`: both are well-sorted, the claim has no variables, and no priority, `prefer`, or `avoid` relates `_+Int_` and `#And`, so the claim is ambiguous.
The two readings have different KORE and different proof behavior; a specification that means one of them states it with brackets.

## Compiler-resolved fresh constants

Within one rule or context, each distinct `!` variable receives a distinct consecutive offset from the generated counter and every occurrence of the same full variable name reuses that offset.
Rust assigns offsets in lexicographic order of the full names and advances the counter by the number of distinct names.
This deterministic association is Rust's stable compiler policy; portable programs must not depend on a particular association between names and offsets.
The policy must not depend on source paths or emulate the iteration order of Java's `HashSet`.

Distinct offsets, consistent reuse, and counter advancement are portable frontend properties.
Generated-value freshness additionally relies on the selected sort's `freshGenerator` contract.
Pinned K assigns names to offsets in unspecified `HashSet` iteration order, so its name-to-offset permutation is not a compiler oracle.
Each backend executes the permutation in its compiled definition; differing concrete values in ordered result positions must remain visible and must not be normalized as alpha-equivalent.
The `fresh-variables` compilation differential checks a case where the permutations happen to agree, while the focused Rust pass regression pins lexicographic allocation and repeated-name reuse.

## Anywhere rules

Rust accepts and executes anywhere rules.
This differs from K's Haskell frontend, which rejects them (`checkAnywhereRules` in `k-frontend/src/main/java/org/kframework/kompile/Kompile.java`) or, under `--allow-anywhere-haskell`, removes them (`removeAnywhereRules` in `k-frontend/src/main/java/org/kframework/backend/kore/KoreBackend.java`).
The reason is the language specification: the [`anywhere` attribute](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md?plain=1#L1322-L1340) instructs "the backends" to apply the rule wherever it matches in the entire configuration, and it names no backend for which the attribute is unavailable.
A definition that uses the attribute is therefore a K definition whose meaning is specified, and a backend implementing that meaning must not reject or silently drop its rules.
Rust emits each anywhere rule as a KORE equation whose left-hand-side symbol carries the `anywhere` attribute, and the backend evaluates it during simplification like a function equation, as the manual's "simplified similarly to a `function`" describes.
Rust's kompile does not add `injective` to the symbol declaration of such a production, but emits a user-written `injective` attribute as written. That attribute is an axiom (equal applications have equal arguments), and an anywhere equation may identify applications with different arguments: `wrap(s(X)) = wrap(X)` gives `wrap(s(z)) = wrap(z)`, and with `s(z) != z` the declared theory would be inconsistent. The same holds for the head of a macro-like rule, whose emitted axiom is an equation of the same kind.
For the same reason Rust's kompile adds neither `constructor` nor `injective` to a production that heads a macro-like rule and emits no no-confusion axioms for it, even when the macro-like attribute sits on the rule and not on the production: the rule `plain(X) => done(X) [macro]` is the equation `plain(X) = done(X)`, which contradicts `plain(X) != done(Y)`. Such a declaration carries no `macro` attribute either, since a rule whose left side does not cover every argument leaves the other applications unexpanded. The definition checks admit macro-like attributes only on productions, so this case reaches emission only through the library functions that emit an unchecked definition (`module_to_kore` and its `_from_resolved` variants).
An overload-greater production keeps `injective` exactly when every production below it in its overload family is a non-function, non-`assoc`/`comm`/`idem` production that heads no anywhere or macro-like rule: its overload equations send each application to the injected normal form of the most specific lesser production that accepts the arguments, or leave it normal, so two argument tuples meet only through the same production at the same arguments. `simplification` rules are lemmas and do not count. This differs from the reference frontend, which declares every such production `injective`; no backend decision in Rust reads the attribute of an anywhere symbol.

The `supported-superset` exclusion applies to expectations that demand frontend rejection or removal of anywhere rules.
It does not exempt their execution from verification or equation tests.
The differential manifest includes anywhere inference fixtures; compiling the reference with its `kore` frontend policy allows the emitted equations to be evaluated with `kore-exec`.
An LLVM execution result may still differ because LLVM matches a normalized anywhere symbol syntactically while Kore can match it through a simplified function equality; the corresponding conformance case records that separate limitation.

After equation normalization reaches a fixed point, the backend treats a term as concrete when every application head is either a constructor or an anywhere-attributed production without the `function` attribute.
This concrete-after-normalization classification is shared by rewrite instantiation, equation matching, overload lowering, and structural predicate simplification.
The simplifier may cache a closed normalized anywhere or overloaded application as evaluated only after a fresh scan has found every compatible equation inapplicable independently of the current path condition.
A symbolic application, a scan with an indeterminate equation, or an equation refuted under the current path condition must remain unevaluated.
An equality from the path condition that can replace any part of a cached term must be applied before the cache can short-circuit simplification.
Rewrite matching decomposes equal rigid heads and rejects a different rigid head, while matches against variables and ordinary function heads remain symbolic.
A subject application of an anywhere production without the `function` attribute is a rigid head, in rewrite, equation and implication matching alike, only when it is normal on every instance (defined below); otherwise the pair stays symbolic, since an anywhere equation such as `wrap(s(z)) = wrap(z)` gives `wrap(s(X))` the value of `wrap(z)` at `X = z` and a rule for `wrap(z)` must not be refuted on it, nor `wrap(X)` decomposed against `wrap(z)` into `X = z` alone.
A ground application that the simplifier has cached as evaluated is such a normal form without the scan. The cache is set only when every equation offered the application fails to match it, as described below for structural equality.
The exception is the root of equation matching: an equation is tried on the application it rewrites as written, and only that application's arguments are compared as the values they denote.
The left-hand side of a rule or equation is matched as written.
The rule index keys a subject's overloaded anywhere head apart from unrelated rigid heads only under the same condition, and keys it as a wildcard otherwise.
Equation matching lowers a concrete overloaded application through `symbol-overload` relations when every argument can lower to the corresponding lesser sort.
The most specific successful lowering supplies sort membership; a concrete application for which every compatible lowering fails refutes membership.
After compatible lowering, equation matching treats different productions in an overload family as distinct rigid heads when the subject is concrete after normalization and its head is rigid in the sense above.
An ambiguous lowering, a variable, or an ordinary function argument remains symbolic.
Structural equality (predicate simplification, the syntactic truth check, and the pairwise disequalities of map keys and set elements) rejects two concrete terms only through heads known to be normal forms: a domain value, a constructor or injection, or an anywhere application the simplifier has cached as evaluated. The simplifier caches an application only when every equation offered it fails to match it. An equation that matches but is set aside because of a `concrete` or `symbolic` attribute still holds, so the application is not cached. Two such heads that differ, an equal such head with structurally distinct arguments, or such an application against a sort injection refute the equality; the `injective` attribute plays no part. Where a definition is at hand (predicate simplification and the collection disequalities), two injections from different source sorts are also separated when the sort graph shows that no value of one injects to a value of the other, and an injection from a subsort is compared with the other side injected to its sort; neither step needs the injected terms to be normal forms. A ground anywhere application without that cache decides nothing, because being concrete after normalization is a shape: `wrap(s(z))` has it and equals `wrap(z)` under the anywhere equation `wrap(s(X)) = wrap(X)`.
Unification replaces an equation between two applications of the same anywhere head by equations between their arguments only when both applications are normal on every instance: every argument is, and every equation that equation selection offers the head, whatever its priority and `requires`, either does not syntactically unify with the application or is refuted on it by equation matching, whose refutation holds for every instance. The scan also runs on ground applications: being concrete after normalization is a shape, not evidence that no equation applies, and the unifier builds terms by substitution that no normalization has seen.
Otherwise the equation stays a residual constraint, because an anywhere equation such as `wrap(s(z)) = wrap(z)` makes `wrap(s(X)) = wrap(z)` true for `X = z`; an overload-greater `f(X) = f(Y)` stays a constraint for the same reason, which is incomplete but never refutes a satisfiable equation.
These rules follow from what the manual makes of the two symbol families.
An anywhere rule leaves its symbol ["still a constructor, even though it is simplified similarly to a `function`"](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md?plain=1#L1338-L1340): once no anywhere equation applies to a normalized application, the application is a constructor value, so it is concrete when its arguments are, and two such values with different heads are different.
A symbol that also carries the `function` attribute is excluded because a function application denotes the value of its equations, not a value of its own.
An [`overload(_)` family](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md?plain=1#L352-L388) groups constructors in which a more specific production is a restriction of a less specific one; after lowering has placed a concrete application at its most specific successful production, different productions of the family are different constructors.

## Concrete rewrite instantiation

When the entire initial term is constructor-like, applying a rewrite rule requires a substitution covering every free variable on its left-hand side.
Unification and `requires` simplification may supply those bindings; an unresolved variable must produce an explicit instantiation failure before applying the right-hand side or `ensures`.
An impossible match or false `requires` remains non-applicable.
The reference is `kore/src/Kore/Log/ErrorRewritesInstantiation.hs::checkSubstitutionCoverage`, called after initial-condition filtering in `kore/src/Kore/Rewrite/RewriteStep.hs::finalizeRule`.
Rust reports this unsupported instantiation as typed indeterminacy, so execution and search retain an incomplete outcome instead of inventing existential successors or treating the rule as non-applicable.

The boundary is concreteness of the whole normalized term.
This includes Kore constructor-like terms and extends them for the supported anywhere superset, so a variable-free normalized anywhere or overloaded application does not make a ground configuration symbolic.
Such an application is a constructor value, as [Anywhere rules](#anywhere-rules) explains.
A variable below such an application keeps the configuration symbolic.
A ground function-headed term can still narrow, and symbolic configurations retain fresh rule arguments and their existentially quantified complementary conditions.
Anywhere equation evaluation, overload lowering, and covered function-equality matching remain supported before this boundary is applied.
The [rewrite coverage fixture](../crates/k-rust-backend/tests/fixtures/rewrite-coverage.kore) and [rewrite tests](../crates/k-rust-backend/tests/backend/rewrite.rs) exercise this boundary, false and binding requirements, equation normalization, and symbolic complements.

## Trivial rule results

A rule whose left-hand side matches and whose `requires` holds has applied even when `ensures false` or a bottom right-hand side makes its result empty.
Its matched region must be removed from the remainder available to lower-priority and `owise` rules.
The K manual fixes both halves: the `requires` clause decides whether a rule applies, while the `ensures` clause is a post-condition that "may cause the entire term to become undefined, but the backend will not stop itself from applying the rule in this case" (`docs/user_manual.md:1153-1164`, "Rule Structure"); an `owise` rule applies "only if all the other rules have been tried and failed", after they have "been shown not to apply" (`docs/user_manual.md:1711-1722`, "`owise` and `priority` attributes").
A rule with an empty result has not failed, so for the matched region the result of the step is empty: `krun` prints `\bottom` and the RPC `execute` answers `vacuous`, never a successor of a lower-priority rule.

This is a recorded divergence from `kore-rpc-booster`, whose Booster rewriter continues with the next priority group when every applicable rule of a group has an empty result (`OnlyTrivial` in `booster/library/Booster/Pattern/Rewrite.hs::rewriteStep`).
The `trivial-result-rpc` differential case compares both answers with the pinned proxy.
Its `execute-trivial` request is krun's depth-0 state, whose initializer functions Booster does not rewrite, so the proxy answers it through its Kore fallback and both sides answer `vacuous`.
Its `execute-trivial-configuration` request sends the evaluated configuration `<k> a </k>`, which Booster rewrites itself: Booster answers `depth-bound` at depth 1 with the `owise` successor `<k> c </k>`, and k-rust answers `vacuous` at depth 0.
That response is the case's `rpc.oracle-exception` row in the [differential manifest](../scripts/reference-differential.toml): the gate fails when k-rust's answer leaves the committed expectation or when the proxy's answer becomes equal to it, and the proxy's measured answer is kept beside the expectation in the [RPC fixtures](../crates/k-rust/tests/fixtures/reference/rpc).
[Rewrite tests](../crates/k-rust-backend/tests/backend/rewrite.rs), including `a_trivial_rule_shadows_lower_priority_rules`, cover concrete and symbolic remainders.

## Hook specification exceptions

The hook contract is K's [`k-distribution/include/kframework/builtin/domains.md`](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/k-distribution/include/kframework/builtin/domains.md).

- `MAP.inclusion` compares complete entries: each included key must have the same value in the other map. Kore follows this contract; Booster's key-only check does not.
- `STRING.find` reports an index in the original haystack. The pinned Kore `kore/src/Kore/Builtin/String.hs` searches the suffix without rebasing the result.
- `BYTES.replaceAt` requires the entire replacement range to fit in the original bytes. The pinned Kore `kore/src/Kore/Builtin/InternalBytes.hs` checks only the start index.

Rust retains the specified behavior for all three operations.
The [hook fixtures](../crates/k-rust/tests/fixtures/reference/hooks) and `execution.oracle-exception` entries in the differential manifest preserve separate Rust and Kore expectations for the two Kore deviations.
Normalization N18 checks both expectations independently; when a pin fixes the deviation, refresh the reference evidence and remove that exception.

## ECDSA recovery on invalid input

`KRYPTO.ecdsaRecover` and `SECP256K1.ecdsaRecover` share one evaluator in [krypto.rs](../crates/k-rust-backend/src/builtin/krypto.rs).
Their hook contract is not in `domains.md`: [`plugin/krypto.md` at blockchain-k-plugin `207ae512`](https://github.com/runtimeverification/blockchain-k-plugin/blob/207ae5121e5178a09742ed746f2d15e34b1750cc/plugin/krypto.md), the revision the [hook capability inventory](../crates/k-rust/tests/fixtures/hook-capabilities.toml) records, declares `ECDSARecover(Bytes, Int, Bytes, Bytes)` as a `function` of sort `Bytes`.
It documents only the successful result, the 64-byte public key that signed a 32-byte message hash with the given `v`, `r` and `s`, and refers to the Ethereum signature form for their meaning; it says nothing about other inputs.

For concrete arguments Rust defines:

- the domain: a 32-byte message hash, `r` and `s` as 32-byte big-endian scalars that form a valid secp256k1 signature, and `v` equal to 27 or 28, which in that signature form encodes the recovery parity as `v - 27`;
- on the domain, the recovered key as its 64 coordinate bytes (the uncompressed SEC1 encoding without its tag byte);
- for every other concrete input, and for an in-domain signature from which no key can be recovered, the empty `Bytes` value.

An application with a non-concrete argument remains unevaluated.

Rust reads the byte-string arguments as fields of fixed width, not as integers of any length.
The hook documentation specifies the message hash as a 32-byte string, and the plugin's own signature form, the result of `ECDSASign`, is 65 bytes in `[r,s,v]` order, so `r` and `s` are 32-byte fields.
A `Bytes` value of another length is a different value that a definition can tell apart (by its length, for one), so Rust does not treat it as that field's 32-byte encoding with zero bytes added or removed.
`v` is restricted to the two values the referenced signature form uses; 29 to 34, which name a recovery with the group order added to `r` or a compressed key, are not part of that form.

The declaration allows either choice outside the documented domain: a `function` without `total` has at most one value ([`docs/user_manual.md`, "`function` and `total` attributes"](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md#function-and-total-attributes)), so both `\bottom` and a single `Bytes` value are consistent with it.
Rust returns a value because a failed recovery must stay observable.
Every recovered key has exactly 64 bytes, so the empty value cannot be mistaken for a key, and a definition can branch on it with ordinary `Bytes` operations.
A `\bottom` result would make every configuration that applies the hook to such an input denote no state: that execution path would vanish from execution and search results, and a claim over it would hold vacuously instead of checking how the definition handles a malformed signature.
Ending the run with an error is not a result either: the inputs are ordinary values of the declared argument sorts, and the unsupported-hook error of [Backend scope](#backend-scope) is for hooks without an evaluator.

The fact this diverges from: Booster has no evaluator for the hook, and the pinned Kore evaluator (`evalECDSARecover` in `kore/src/Kore/Builtin/Krypto.hs`) has no failure value and a wider domain than Rust's.
It reads the hash, `r` and `s` as unsigned big-endian integers of any length, accepts `v` from 27 to 34 (the assertion at `:313`), does not check `r` and `s` against the group order, and appends zero bytes to whatever it encodes up to 64 bytes (`:295`, `:300-304`).
On some inputs outside Rust's domain it therefore returns a value where Rust returns empty `Bytes`: a valid signature whose hash, `r` or `s` has the same integer value in fewer or more than 32 bytes recovers the same key, and by the code a `v` of 29 or 30 recovers a key when `r` plus the group order is still the x-coordinate of a curve point.
On other invalid inputs it ends the backend process, through one of its assertions (`:313`, `:327-331`) or, when recovery yields the point at infinity, the `error` at `:414`; a `v` from 31 to 34 always fails the assertion at `:330`, because the recovery index `v - 27` then adds at least twice the group order to `r`, which exceeds the field prime.
The pinned toolchain thus differs from Rust by a value on part of the invalid inputs and supplies no value on the rest, and the differential manifest's `ecdsa-invalid-execution` entry is a `local-gate` exclusion.
The CLI test `krun_executes_invalid_ecdsa_recovery_to_empty_bytes` pins the terminal KORE for [`ecdsa-invalid.crypto`](../crates/k-rust/tests/fixtures/reference/ecdsa-invalid.crypto), and the unit test `invalid_concrete_recoveries_return_empty_bytes` in `krypto.rs` covers each boundary of the domain.

## RPC behavior

A predicate-free `get-model` request returns `Unknown` without a substitution.
`get-model` first simplifies the predicate, retaining any open definedness constraints.
Truth returns `Sat` without a substitution because every valuation satisfies it; an unconstrained variable is absent from the substitution.
False returns `Unsat`.
When the residual abstracts symbols or sorts, `get-model` returns `Unknown` without a substitution for a solver `Sat` answer.
An uninterpreted function keeps congruence but need not satisfy its K definition, so the solver's model need not be a K valuation.
The `bounded-search` model exception records a distinct-constructor result where the oracle reports `Sat`; `start = done` is `Unsat` because distinct constructors cannot denote the same value.
Both `booster/library/Booster/JsonRpc.hs` and `kore/src/Kore/JsonRpc.hs` contain this no-predicate outcome.
A proxy response of `sat` must not override this contract without establishing whether the proxy classified the same input as carrying a predicate or definedness obligation.

A `cancel` request inside a batch returns `-32601`, `Cancel not supported`, following the shipped proxy; an empty batch returns `-32600` with data `[]`.
The older server API document is not authoritative for these measured wire details.
Execution retains an explicit `aborted` reason for incomplete indeterminate, simplification-error and breadth-bound outcomes because Rust has no fallback engine to hide the failure.
[RPC tests](../crates/k-rust/src/rpc.rs) cover predicate-free models, batch cancellation, and error classification; [RPC fixtures](../crates/k-rust/tests/fixtures/reference/rpc) preserve shipped-proxy responses.
An `execute` response lists `next-states` in application order with the remainder last; the order is not part of the contract and the differential gate compares the array as a multiset (N27).
Backend error `data` is compared by class: code, message, and the `error` sentence; context lines are the port's own diagnostics (N28).
A parameter object with a key the method does not declare is rejected with `-32602`, `Invalid params`, and is not executed: the server cannot apply that key, and the result it would return might differ from the one requested, which is the reason for the [CLI-scope](#cli-scope) rule on unknown flags.
An `implies` request is the statement `A -> \exists E. C` under the universal closure of the free variables of `A` and `C`, with `E` the consequent's leading existentials.
A free variable of the consequent that the antecedent does not mention is therefore universal, not an error: the match binding `u := s` of any universal is an obligation `u = s` that the antecedent's condition must entail.
The universal ranges over the values of its sort in the models of the definition, so the answer is `valid` when every such value the antecedent allows satisfies the obligation: when the antecedent is unsatisfiable, when nothing constrains the variable, or when the definition's no-junk axiom for the variable's sort (its `constructor` axiom) leaves `s` as the only value, as for a sort whose one constructor is nullary.
The solver treats a user sort as uninterpreted and does not see the no-junk axiom, so in that last case it reports a counterexample; when the solver does not answer `valid`, the check simplifies `A /\ u =/= s`, and if `u =/= s` excludes every constructor the axiom lists, that conjunction is a contradiction and the answer is `valid`.
Otherwise a value of `u` that violates the obligation may exist; a sort without a no-junk axiom has such values even if the definition declares a single constructor for it.
The answer is `invalid` only when such a value is shown (below): for a universal of sort `Int` or `Bool` whose counterexample the solver finds on an exact query; for a universal of another sort the solver's counterexample ranges over an uninterpreted sort, so the answer is `indeterminate` with the binding as its condition.
An antecedent existential that shares the consequent universal's name is a different variable and is renamed apart.
The RPC differential records this as the `bounded-search` `implies-consequent-universal` oracle exception (N19): with the ground start configuration as antecedent and its `<k>` item replaced by `X:SortState` as consequent, k-rust answers `indeterminate` with the binding `X = start` as its condition, and the pinned proxy answers error code 4, `Implication check error`, "The RHS must not have free variables not present in the LHS".

`invalid` asserts an instance of the antecedent outside the consequent, so the `implies` method, `krust kore-implies` and `Backend::implies` answer it only where that instance is shown ([`refutation_result`](../crates/k-rust-backend/src/implication.rs)).
A refutation of every instance (a term mismatch, a `\bottom` consequent, or obligations the solver answers `Unsat` under the antecedent) needs an instance of the antecedent; a counterexample (the solver answers both the obligations and their negation satisfiable) needs an instance of the antecedent with the negated obligations.
Such an instance is shown when the antecedent's term contains no conjunction of terms, its constraints, the negated obligations where required, and the term's definedness are true syntactically or satisfiable by a solver query that approximates nothing (`smt::translates_exactly`), and every free variable has a sort the definition shows inhabited.
A pattern with a free variable denotes nothing when the variable's sort has no value; the inhabited sorts are the least fixed point of hooked, domain-value and collection sorts, result sorts of constructors and total functions whose argument sorts are inhabited, and supersorts of inhabited sorts.
A `\not C` consequent is decided on the conjunction of both sides: `A -> \not C` is `valid` when the terms of `A` and `C` do not unify or the unified constraints are unsatisfiable, `invalid` when the unified pattern is shown to have an instance as above, and `indeterminate` otherwise, including for `\exists E. \not C`.
A solver `Unsat` is sound under every approximation of the translation, but a `Sat` for a query with an uninterpreted `smtlib` function, an uninterpreted sort or a partial function made total may come from a model that is no K valuation, and then the antecedent may be empty and the implication vacuously valid.
Such an answer, and a remainder obligation the solver leaves undecided, is `indeterminate` (`unknown` on the CLI and the bindings) with the condition it would otherwise carry.

An `implies` response reports its antecedent and consequent after simplification, the patterns the verdict was decided on ([`simplified_implication_response_syntax`](../crates/k-rust/src/rpc.rs)); a simplification failure is reported as a `simplify` fault rather than as an unsimplified pattern beside a verdict computed from the simplified one.
Simplification replaces a pattern by an equal one, so the payload denotes the requested implication.
The pinned Booster proxy echoes the request's patterns instead; for the IMP request that is an unevaluated `initGeneratedTopCell` application where k-rust reports the configuration it evaluates to.
The `rpc.imp` `oracle-exception` records that difference with `equivalence = "simplified-implication"`, and N19 checks the claimed equality rather than asserting it: the two responses must be equal outside the payload, and both payloads' antecedents and consequents, simplified by `krust kore-simplify` against the reference definition, must print identically.
Like C8, that evidence depends on the port's simplifier.

The `haskell-logging` parameter selects diagnostic entries; it is not an instruction to the computation.
It decides only whether `haskell-log-entries` is attached (for a non-empty list) and which entries it holds; no other result field depends on it.
A name is matched exactly and case-sensitively against a fixed set of names per entry, not against the entry's `context` array (whose segments are lowercase).
Every method returns one proxy entry, first in the list when selected; it is selected by `Proxy` or by its method name: `Execute`, `Simplify`, `Implies`, `AddModule` or `GetModel`.
For `execute`, each step of the trace yields a success entry selected by `Booster`, `Execute`, `Success`, or its kind: `Rewrite` (a rewrite or claim step), `Simplification` or `Remainder`.
A run that halts stuck, indeterminate or on a simplification error yields one failure entry, selected by `Booster`, `Execute` or `Failure`, and also by `Indeterminate` or `Abort` when the halt is indeterminate.
`Rewrite` does not select the failure entry, even when its `context` names the rule in a `rewrite` element.
Any other name selects no entry, in the same way that `Failure` selects none on a run in which no rewrite failed: an empty selection is the answer to the query, not a dropped request.
The CLI-scope rule that an unknown flag must not be silently ignored therefore does not apply: that rule prevents an operation from returning a result that an unapplied option would have changed, and a `haskell-logging` name changes no result field other than `haskell-log-entries`.
Because the emitted names are listed here, an empty selection for a name outside the list carries no information about the event that name denotes elsewhere.
A `haskell-logging` value that is not an array of strings fails parameter decoding and is rejected with `-32602`, `Invalid params`.

## Definition verification

### SMT prelude consistency

The backend builds the SMT prelude when it selects a definition, but it may defer checking whether that prelude is satisfiable until an SMT answer depends on consistency.
Every SMT query includes the whole prelude, so a `sat` answer establishes its consistency without a separate check.
Before using the first `unsat` answer, the backend checks the prelude alone; an `unsat` or `unknown` result from that check fails the operation.
When that check fails, the backend interrupts the active rewrite, search, or proof at its next cancellation point and reports the prelude error; later requests using the same solver report that error at entry.
An `unknown` query answer establishes neither consistency nor inconsistency and does not trigger the prelude check.
This is sound because the prelude constrains SMT answers only: an operation that uses no SMT answer has no result derived from it.

A zero-query run can therefore succeed with an inconsistent prelude.
An RPC server can start with that prelude and report the error on its first dependent request instead of at startup.
With `--io on`, output produced before the first dependent answer can be visible before the error.

The acceptance boundary is the theory of the selected main module, meaning that module and its transitive imports; within it, the boundary includes the sentence, declaration and pattern conditions of KORE validity as the KORE language specification states them, [`docs/kore-syntax.md`, "Validity"](https://github.com/runtimeverification/haskell-backend/blob/ad54c7a55085b726c4d3c2728242a7e0695b0439/docs/kore-syntax.md#validity).
Among its conditions, every sort, symbol and alias an axiom uses is declared, each application agrees with its declaration in sort parameters, arity and argument sorts, and each bound variable agrees in sort with its binder.
It does not include the two module-order conditions on import sentences: an imported module need not appear earlier in the definition (condition 6a), and an import need not precede the other declarations of its module (6b).
Modules are resolved by name, so a definition that violates either condition is accepted and means the same theory as its reordered form.
The reason: imports determine which declarations are in scope, and textual order adds nothing to that scope, as the specification already states for the non-import sentences of a module.
The part of 6a that a topological order implies, that imports form no cycle, is still enforced for the main module's import closure.
Modules outside the main module's import closure are verified only for unique module names and unique sort, symbol and alias names across the whole definition; their sentences are not otherwise checked, so an ill-formed axiom in an unimported module does not stop the definition from loading.
The reason: `-m` selects the theory to execute, and a module outside its import closure contributes no sentence to that theory.
The main module's theory is a matching-logic theory, and every axiom of the modules in its closure belongs to it whether or not the backend later classifies that axiom as a rewrite, an equation or an attribute axiom.
An axiom that is not a valid pattern has no meaning, so a closure containing one does not define a theory, even when execution would never consult that axiom.
Verification therefore checks every sentence of the modules in the closure before classification, including axioms that classification ignores.
This diverges from Booster, which drops some axiom shapes without internalizing them (a `simplification` axiom whose left-hand side is not an application, and a `functional` or `total` existential; `booster/library/Booster/Syntax/ParsedKore/Internalise.hs:629-630,636-641`), so an ill-formed axiom of those shapes does not stop Booster from loading the definition.
Verification also rejects `\dv{S}` on a sort `S` declared without `hasDomainValues`, a condition the specification's Validity list does not state.
Its reason: a `\dv{S}` pattern names a domain value of `S`, and `hasDomainValues` is the declaration that `S` has domain values, so a domain value of a sort declared without it denotes nothing.
The verifier enforces further conditions beyond the specification (among them `BOOL.Bool` literals, subsorts of sorts with domain values, function heads and constructor result sorts, attributes, and claim right-hand-side variables); they are not yet justified in this section.
A subsort axiom `subsort{S, S}` states `S <= S`.
The subsort order is the reflexive-transitive closure of the declared pairs, so it contains `S <= S` for every sort even without a subsort axiom, and the axiom `\exists V:S. V = inj{S, S}(W:S)` is a valid pattern.
A reflexive subsort declaration therefore adds nothing to the order and is not rejected for being reflexive; the other subsort conditions still apply, so `subsort{S, S}` on a sort with `hasDomainValues` is rejected because the verifier does not accept subsorts of a sort with domain values.
The [definition fixture index](../crates/k-rust/tests/fixtures/reference/definition/index.toml) records pinned verification outcomes and diagnostic fragments.

## Search results

Search output uses deterministic structural KORE order; reproducing Kore's internal `MultiOr` ordering is not a compatibility requirement.
The order is `k-rust-kore`'s `Pattern` order (variant declaration rank, then fields in declaration order, byte-wise strings) and may change between releases.
Differential gates compare disjunctions as multisets so ordering is ignored while multiplicity is still checked.
For `--bound N`, selected results must be distinct members of the same query's unbounded solution set, up to the bound; which members are selected is unspecified.
The CLI test `krun_search_bound_returns_a_subset_of_the_unbounded_solutions` checks this property against the port's own unbounded search.
Which successor `--strategy any` follows among equal-priority rules is likewise unspecified; the differential gate checks that the port's any-strategy result is a member of the reference all-strategy set (N26).
The port follows the first applicable rule in priority order, then `definition.kore` declaration order (main module first, imports depth-first in their written order); which rule the reference follows is engine-internal.
Among several collection matches of that rule, the port follows the first candidate in deterministic structural order; which candidate the reference follows is engine-internal.
The RPC `next-states` array is a set of successors and is compared as a multiset (N27).

A depth-bounded execution result covers every path of every input instance up to the bound, so a configuration reached at the bound is a result whatever other branches did; the port keeps such a leaf when another branch halted, where the reference graph traversal drops it.
Normalization N17 limits the corresponding differential exception to marked depth-bounded cases and requires the reference leaves to remain a sub-multiset of the Rust leaves.
[Execution fixtures](../crates/k-rust/tests/fixtures/reference/execution) and the symbolic differential cover branch sets and depth cuts.

## Execution results

An execution or search result is a disjunction; each disjunct denotes the configurations one branch reaches, for a valuation of the initial pattern's free variables.
Those variables are the only names a result shares with the query.
Any other variable free in a disjunct is read as existentially quantified over that disjunct alone: it names a value the rewrite introduced, such as a `?` variable, which K quantifies existentially at the top of a rewrite rule's right-hand side (`docs/user_manual.md:2443-2444`), a rule variable the match left unbound, or a collection frame.
k-rust prints a disjunct as its term conjoined with its constraints and leaves these binders implicit (`constrained_pattern` in [externalize.rs](../crates/k-rust-backend/src/externalize.rs)); it names the variables with `Ex`, `Rule` or `Eq` prefixes or as `Var'Ques'` names, each with a fresh counter.

A remainder disjunct, the branch on which a rule does not apply, carries the negated applicability condition `\not(\exists V. C)`, where `V` are the variables of `C` that are free in neither the state's term nor its constraints (`quantify_introduced_variables` in [predicates.rs](../crates/k-rust-backend/src/rewrite/predicates.rs)).
The applicability condition includes a `requires` Boolean term's definedness at instantiation, so an undefined `requires` instance belongs to the remainder; the [symbolic definedness tests](../crates/k-rust/tests/symbolic_definedness.rs) exercise this split with and without Z3.
A carried right-hand-side definedness obligation or an `ensures` can instead exclude an instance without producing a leaf; the same tests cover the obligations retained on surviving leaves.
A rule's variables are universally quantified over the rule (`docs/user_manual.md:2448-2450`), so the remainder must exclude every instance of the rule: a variable of the match that occurs nowhere else in the disjunct is bound inside the negation.
Reading it at the disjunct level instead would say only that some instance does not apply (`\exists x. \not C` rather than `\not \exists x. C`), which is a different set of configurations.

Under this reading three normalizations of [the register](../scripts/reference-normalisations.toml) are equivalences rather than tolerances:

- N4 renames the result variables that are not free in the initial pattern bijectively, sort-preservingly, and per disjunct; that is renaming bound variables, while the initial pattern's variables are compared by name. This holds when the gate supplies the initial pattern (`K_DIFFERENTIAL_INITIAL_PATTERN`, set by the symbolic and MIR execution gates); without it, N4 selects the variables to rename by generated-name shape, compares every other variable by name, and does not check that no initial-pattern variable has such a shape.
- N16 drops the outer `\exists` binders of a disjunct that bind generated variables (not free in the initial pattern; by the N4 name shapes when no initial pattern is given), which denotes the same disjunct as its body; it stops at a binder of an initial-pattern variable, which is kept and compared. k-rust prints no such prefix.
- N22 adds, inside a negated existential, the binder of a generated variable that is free there and occurs nowhere else in the disjunct, which is where the reading above places it; k-rust already prints that binder, while the pinned Kore prints the unification's collection frame free in that position.

## Observation events

Observed execution and search (`executeObserved` and the `*Observed` search methods of the host API) report three event kinds, a closed union tagged by `kind`.
A `transition` event is a committed transition of the leaf's `branch` (or a witness's `id`); under an allowlist only the admitted ones are reported, always in branch order.
An `evaluation` event is an equation, simplification, or builtin application that normalized a branch state; its `anchor` is the number of branch entries before it, whether or not the allowlist reports them.
An `uncommitted` event is an attempted transition that no surviving branch retains.
A cut-point rule is proposed, not committed: the leaf stays at the state before it, and neither the rule nor its successor's normalization appears in the leaf's events, unless the leaf reports the successor's pattern because its normalization failed or is bottom.
With branch stopping, each candidate successor is normalized after its transition on its own branch: a candidate that continues as the only successor keeps those evaluations, and a candidate reported by a branch or cut-point halt carries them with it (in the backend's `AppliedRule::observations` and `RemainderBranch::observations`; the host wire does not expose halt candidates structurally).
Evaluation events are diagnostics; which ones occur and in which order depends on the simplifier's strategy.

This shape replaced an earlier one at backend schema version 1, without a version change, in line with the other closed-variant changes of that schema:
equation, simplification, and builtin applications were `transition` events with a `TransitionId` and the classes `function-equation`, `simplification`, and `builtin`; `transition.class` is now one of `rewrite`, `remainder`, and `claim`, and those three classes moved to `evaluation.class`.
The event fields are camelCase (`ruleLabel`, `introducedPredicates`), as the TypeScript declarations always stated; the JSON previously spelled them `rule_label` and `introduced_predicates`.
Builtin failure fields now use the camelCase names in the napi and wasm declarations (`thenSort`, `elseSort`, `exponentBits`, `leftPrecision`, `leftExponentBits`, `rightPrecision`, `rightExponentBits`); search instantiation failures use `missingVariables`.
These backend schema version 1 JSON fields previously used snake_case; clients reading serialized failures must accept the camelCase names.

## CLI scope

`krust` retains its source-plus-flags interface.
For source-driven `krun`, the syntax or configuration parser module supplies the concrete grammar and the selected main module supplies the executable production catalog and visible macro sentences.
Parsed applications must rebase into the main catalog before macro expansion, sort injection, and KORE conversion; an absent source-catalog production index may be discarded only from a self-describing token, whose lexical hook is read from the parser module before falling back to the main module.
Macro expansion uses the frontend's KAST-domain expander after rebasing and before conversion to executable KORE; `kast` retains its separate unparsing-module scope.
A macro- or alias-headed term that survives expansion is invalid executable input and must be rejected before the first rewrite step rather than narrowed as an ordinary function application.
The backend also rejects such a head defensively when a direct caller bypasses the CLI validation.
The project provides its own versioned compiled-directory runtime contract rather than K's file format; it does not implement K-derived module defaults, every K flag alias, or K's pretty-output and proof-verdict framing solely for tool interchangeability; its own verdict words are defined under [Proof verdicts](#proof-verdicts).
K tools and pyk serve as differential oracles; the conformance driver translates recipes into supported Rust operations.
An unknown or untranslatable flag must remain explicitly unsupported rather than being silently ignored.
The `declined-capability` category records steps requiring an interface with no Rust equivalent.
Semantic input selection, warning handling, execution status, and configuration initialization remain testable contracts; this policy does not exclude them.
The source-plus-flags interface includes standalone Bison parser generation and executable or shared-library parser artifacts, while relying on the system Bison, Flex, and C compiler rather than implementing those tools in Rust.

`krun --output captured` is an explicit ordinary-execution mode for definition-computed console output.
It uses buffered `--io off` stream semantics with pre-buffered standard input, requires exactly one complete unconstrained terminal execution leaf and exactly one structurally identified stdout stream buffer, writes that buffer to process stdout once, and suppresses KORE rendering.
Bottom, constrained or multiple leaves, incomplete execution, malformed stream state, search, surface result matching, and an explicit `--io on` are errors.
`krun --io on --output none` is the corresponding committed live mode with pre-buffered input and byte-exact descriptor 1/2 delivery.
Default KORE output remains unchanged.

## Proof verdicts

`krust kprove` prints one verdict word per selected claim: `proven`, `disproved`, `failed`, `indeterminate`, `depth bound` or `breadth bound`.
The Node.js and WebAssembly `status` field uses the same words, with `depth-bound` and `breadth-bound`.
The [README kprove section](../README.md) lists them with the leaf listing each word prints.
A word is a statement about the claim; the process exit status is only a summary of several claims: 0 exactly when every selected claim is `proven`, 1 otherwise with `one or more reachability claims were not proven`.

This differs from the pinned `kprove`, which reports only whether the backend proved every claim.
It prints `backend terminated because the configuration cannot be rewritten further` whenever the backend exits with status 1 (`k-frontend/src/main/java/org/kframework/kprove/KProve.java`), and the pinned `kore-exec` exits with status 1 whenever its result lists any claim it did not prove (`kore/app/exec/Main.hs`, `koreProve`).
The message therefore states that a claim was not proven; it does not state that the claim is false.
k-rust separates the two because a consumer acts on the word: a `disproved` claim cannot be proven by any strategy and needs a changed claim or definition, while a `failed` claim may be true, for example a vacuous claim or a one-path claim whose search took a rule that leads nowhere.
Reporting a true claim as false is a wrong result, not a presentation difference.

A claim `φ => ψ` is refuted, under the manual's [one-path](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md#one-path-interpretation) and [all-path](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md#all-path-interpretation) readings ("there exists a path", "all paths ... will reach"), by a configuration of `φ` that, for an all-path claim, has a path ending in a configuration with no successor without passing through `ψ`, or, for a one-path claim, has no path to `ψ`.
`disproved` requires a leaf that shows this, a certified stuck leaf (`Stuck (certified)` in the listing), which must meet all of the following conditions:

- (a) No successor: the rewrite step on the leaf is stuck.
  A state the search stopped without rewriting, such as a stuck-check stop, is stepped once and is certified only if that step is stuck, because a configuration that can still move may reach `ψ` later.
- (b) Every path followed: the claim is all-path, or its one-path trace kept every successor.
  A one-path claim is false only if no path reaches `ψ`, and a trace that took one of several applicable rules says nothing about the others.
  The sequential rewriter does not report whether a step dropped an applicable alternative, so every one-path rewrite step counts as one that may have, and a one-path leaf is certified only when its trace has no rewrite step.
- (c) No claim step: no circularity or trusted claim on the trace.
  Such a step replaces paths by an assumed claim instead of following them, so the leaf shows at most that the assumption and the claim cannot both hold.
- (d) Non-empty outside the destination: the leaf term applies no function symbol (it may hold constructors, domain values and variables) and is not a conjunction of terms at its top, and the leaf constraints together with the definedness of its term hold syntactically, or are satisfiable by an SMT query that approximates nothing (only `Int` and `Bool` variables, no abstracted subterm, no partial function).
  A leaf denoting the empty set refutes nothing, an unevaluated function application may denote no value or a value the destination accepts, and a satisfiable abstraction may be spurious.
  The leaf constraints carry the complement of every destination condition checked on the trace, including the uncovered part of a state that the destination condition covers only in part; the complement places the leaf outside `ψ` only if every destination check on the trace ran and was decided.

Every other stuck leaf, and every empty leaf the vacuity policy rejects (`Trivial`, `Vacuous`), makes the claim `failed`: the search stopped there without establishing that the claim is false.
When leaves disagree, the first of `disproved`, `failed`, `indeterminate`, `depth bound`, `breadth bound` applies.
The conditions are sufficient, not necessary: a false claim whose refutation k-rust cannot certify is reported `failed`, never `disproved` without evidence.
The conformance driver compares kprove recipes only as proven, not proven or error (`kprove_verdicts` in `scripts/conformance/run.py`), so `disproved` and `failed` are the same outcome there.

[reference-proof-differential.sh](../scripts/reference-proof-differential.sh) runs each `[[proof]]` entry's `failure-claim` through both toolchains.
It requires the reference `kprove` to exit with the message above and k-rust to print `claim <failure-claim>: disproved`; N12 omits the counterexample framing from that comparison.
The reference observation supplies only the fact that the claim is not proven.
The `disproved` expectation is k-rust's own stronger statement: it is valid for an entry only when the failure claim is false and k-rust's leaf for it meets (a)-(d), and the gate passing shows the leaf was certified, not that the reference refuted the claim.
`mini-proof`'s `claim-refuted`, the all-path claim `<k> start => stuck </k>` over a definition whose only rules are `start => middle` and `middle => done`, meets them: its leaf is `<k> done </k>` with no constraint, reached by the only path and without a successor.
A failure claim that is not false cannot carry the `disproved` expectation, and its entry must record its own expectation with the reason.

## Driver scope

The conformance driver translates each upstream `ktest` recipe into krust operations and compares their outcomes.
A plain `krun --output none` recipe with a non-empty expected console output runs under `--io off` and compares the stdout stream buffer of its single unconstrained execution leaf with that output under C9; it does not require host console effects from the backend.
An explicit `--io on` recipe compares the committed console stdout bytes directly with its expected output.
When C9 detects that buffered stdin cannot reproduce an implicit recipe's tokenization ([Comparison contract](#comparison-contract) states the one detected symptom), the driver retains the attributed C9 result and re-runs that recipe under pre-buffered `--io on --output none`; only the live bytes decide that step.
A recipe that defines no translatable step supplies no oracle: a `ktest-kdep.mak` or sub-make-only Makefile, a Makefile whose `ktest.mak` include is disabled upstream, a recipe that discards the output it would compare, or an expected kompile failure that leaves no definition for a later step.
The `undriven-recipe` category records such cases with the concrete recipe feature; the skip is not evidence of a Rust pass and must be reconsidered when the driver learns to translate the feature.

Every case whose accepted verdict is not `match` carries exactly one of two dispositions.
A non-empty `exclusion` names the category whose section here justifies leaving the difference, and the inline `reason` states the concrete feature or decision for that case; the justification is complete in this repository.
An empty `exclusion` with a non-empty `reason` records a measured port or driver gap that is pending work; the work itself is tracked outside this repository, and [testing.md](testing.md#manual-conformance-acceptance) describes how a local backlog is audited against the measurements.

## Comparison contract

[reference-normalisations.toml](../scripts/reference-normalisations.toml) is the authority for each permitted equivalence and exclusion.
Normalization identifiers such as N3 are durable names defined in that register, not work-item identifiers.

N3 permits only the counted multi-alias freezer family exclusion.
K's generated suffix assignment depends on unordered Scala context iteration, including `Source` and `Location` attributes; Rust retains deterministic declaration order.
The frontend orders catalogs, emitted sentences, and checks by dependency-first declaration order; no Scala `Ordering` is reproduced.
Sentence identity for deduplication (`sentence_equivalent`) keeps K's `Sentence` equality.
Single-alias identities remain compared.
N23 applies the same limited policy to generated lambda families: `kernel/src/main/java/org/kframework/compile/ResolveFun.java` assigns suffixes in `localSentences` iteration order, whose sentence hashes include the source path.
The pinned `issue-1528`, `let-test` and `record-llvm` cases exhibit different suffix assignments from different checkout paths.
The comparator collapses multi-suffix names consistently in declarations and uses, ignores only the affected UNIQUE_ID attributes, compares the remaining sentence multiset, and prints the collapsed axiom count.
The tradeoff is explicit: a suffix-to-body association is outside this comparison, while signatures and rule bodies remain checked.
N32 applies only to the reference side of the semantic KORE compile comparison.
It removes a generated sort-predicate true equation that places `X:S` at `K` through `inj{S,KItem}` (or `inj{S,K}`) when the KORE definition has no `subsort{S,KItem}` axiom, and removes only that equation's negated applicability disjunct from its matching `owise` false equation.
The predicate symbol, other conditions, and all equations with a declared `subsort{S,KItem}` remain compared; [the sort-placement contract](#sorts-of-compiled-terms) explains why the omitted equation cannot apply.
Variable numbering inside a generated owise competitor disjunction is the port's own; N4 renames it on both sides.
N33 applies only to the reference side of the KORE compile comparisons: it drops `injective` from a reference symbol that carries `anywhere` or a macro-like attribute when the port declares that symbol without it, the divergence [Anywhere rules](#anywhere-rules) states; the port can never gain the attribute through it, and every other attribute stays compared.
The conformance driver's surface-text comparison (`scripts/conformance/run.py` `execution_text_diff`) applies the same N4 reading to kprint's `?Name:Sort` tokens as C7: the rule existentials both engines instantiate through a fresh counter are compared modulo a bijective, sort-preserving renaming by first occurrence per disjunct, applied before the C1 sort.
Every other variable, including the search pattern's own variables and any `?` variable the recipe's `--pattern` text names, and every string literal are compared literally, so lost sharing, a changed sort, or a renamed pattern variable remains a mismatch.
When that text comparison fails, C8 (`compare_simplified_kore`) re-runs the reference recipe with `--output kore`, simplifies that result and the krust result with `krust kore-simplify` against the reference kompiled definition and main module, and compares the two simplified patterns with the structural execution comparator without `K_DIFFERENTIAL_DEFINITION`, so N4 renaming applies and N15 does not.
The pinned reference prints a rewrite result before its own simplification is complete: `no-junk-macro` retains a constraint that the definition's own `smt-lemma` makes valid, and `concrete-function` leaves `foo(inc(sym2(?X)))` unevaluated because the argument's definedness is open, while the port discharges the constraint and applies the equation under a `\ceil` obligation that the surrounding constructor context already entails.
Both pairs are equal patterns; simplifying both with one simplifier makes them comparable.
A step that matches only this way records the C8 comparison label and the text difference, never plain match text; the checked-in `.out` stays the oracle, so the re-run's result must still print as the `.out`.
A simplification or comparison that fails or is unavailable leaves the text mismatch in place; a reference re-run that produces no result records `reference-error` with the reference's stderr, which is an oracle change and not evidence for either side.
C8 is supplementary evidence in the sense of [testing.md](testing.md#comparator-evidence): it depends on the port's simplifier, like N15.

C9 compares the bytes a tutorial definition accumulates in its stdout stream buffer under `--io off` with the checked-in output of the corresponding `--output none` recipe.
The comparison requires exactly one execution leaf in total, that leaf to be unconstrained, and exactly one structurally identified `#ostream(1)`, `"off"`, `#buffer(S)` stream.
Any residual leaf, multiple terminal leaves, and malformed stream configurations are mismatches and remain reported.
The tutorial stream rules append the same strings in both IO modes and make the `on` mode's `IO.write` hook only a transport for those bytes; K itself selects `off` for search and debug executions.
For input programs, C9 applies only where krust's buffered stdin is the piped input and K's stream rules tokenize those bytes as they tokenize the recipe's interactive stream; [Backend scope](#backend-scope) states where the two tokenizations differ.
When krust attributes an undefined result to a `STDIN-STREAM` rule and the input begins with a parse delimiter or contains adjacent parse delimiters, the driver records that C9 precondition failure and drives the implicit recipe under committed pre-buffered `--io on`.
This detection is a sufficient test for one symptom, not a decision procedure: the precondition depends on the sort each `#parseInput` requests and on the input suffix it reads, which the input bytes alone do not determine.
Any other failure of the precondition, for example `stdinParseString` taking the whole remaining buffer under `--io off` where the interactive stream supplies one token, is not detected; it runs to completion and is reported as a C9 stdout-buffer mismatch, to be diagnosed against [Backend scope](#backend-scope), never excluded.
This comparison remains independent of the captured output mode: C9 extracts the KORE result through its own structural helper and does not invoke `krun --output captured`.
C9 also remains independent of live delivery: the normal tutorial measurements continue to use its definition-computed buffer, while only a proved C9 input-precondition failure selects the separate committed transcript path.

A text difference that neither C8 nor N15 can compare stays a mismatch with a measured reason; no prose exclusion category exists for it.
Normalization N15 may prove residual constraints equivalent by checking both implications, subject to the independence limitations in [testing.md](testing.md#comparator-evidence).
Different text or a successful Rust implication check alone must not establish implication correctness.

## Reference evidence

`reference-crash` means the reference supplied no expected behavior; `stale-oracle` means the pinned toolchain did not reproduce an upstream checked-in output.
Both remain visible and must be reconsidered when the reference pin changes.
Neither is evidence of a Rust pass, and locally regenerating an upstream output does not independently establish the contract.
The driver records a reference tool that fails to produce a result as `reference-error` with its stderr, and a reference result that differs from the checked-in output as a stale oracle; the two are never merged.
`both-reject` permits different diagnostic presentation only after both toolchains reject the input; diagnostic classes remain separately recorded to expose rejection for the wrong reason.

The [conformance expectations](../scripts/conformance/expectations.toml) preserve measured revisions, result digests, accepted ranks and stages, and individual case or step reasons.
Historical digests identify measurements; they do not imply that their full temporary logs are distributed with this repository.
A new checkout can seed the versioned floor and measure selected cases using the commands in [testing.md](testing.md#manual-conformance-acceptance).

## Proof gate verdicts

The kprove verdict words are defined in the [README kprove section](../README.md): `disproved` is reserved for a certified refutation, and `failed` covers a failing leaf that does not show the claim false, including an empty leaf that the vacuity policy rejects.
[reference-proof-differential.sh](../scripts/reference-proof-differential.sh) requires every case's failure claim to be rejected by both toolchains, and requires k-rust's verdict word to be the case's `failure-verdict` in [reference-differential.toml](../scripts/reference-differential.toml): `disproved` unless the entry says otherwise, in which case `failure-verdict-reason` states why the claim is not false.

`trivial-proof` expects `failed` for `TRIVIAL-SPEC.ct2`, the all-path claim `<k> t1 => t3 </k>`.
The definition's only rule for `t1` is `t1 => t2 ensures false`; its result is empty, so it states that `t1` has a successor in the empty set, which holds of no configuration.
The claim's left-hand side is therefore empty, and the claim holds vacuously; nothing refutes it.
k-rust reaches a `Trivial` leaf, which the vacuity policy rejects as `failed`, and `--allow-vacuous` proves the claim.
The reference toolchain's rejection of the claim remains checked as the case's oracle observation; k-rust's `failed` verdict records that this rejection is not a refutation.

## Proof oracle incompleteness

A `reference-incomplete-port-proves` exclusion needs a soundness argument for the particular claim: a Rust `proven` result alone cannot justify departing from a reference refutation.
The pinned K cases are under [`k-distribution/tests/regression-new/spec-rule-application`](https://github.com/runtimeverification/k/tree/4a46d1231473b599c699160132fd6e76a5c46406/k-distribution/tests/regression-new/spec-rule-application).
Their `def.k` defines `incPos(X) = X + 1` when `X >= 0`, and the only ordinary transition is `start X => mid X`.

For `def61-spec.k`, after that transition choose trusted-claim variables `Y1 = X1` and `Y2 = X2 - 1`.
The subject requires `X1 >= 0` and `X2 - 1 >= 0`, so `incPos(Y1) - Y1 - 1 = 0` and `incPos(Y2) = X2`.
Both components of the trusted claim's `binop` therefore match the subject, and its right-hand side is exactly the destination `end X1` with the same variable cell.

For `def81-spec.k`, choose `Y1 = X + 1` and `Y2 = X + 2` after the initial transition.
The subject requires `X >= 0`, hence `incPos(Y1) - 1 = X + 1`; also `Y1 - 1 = X`, `Y2 - 1 = X + 1`, and the trusted claim's condition `Y2 = Y1 + 1` holds.
The trusted claim reaches exactly the specified destination without an uncovered remainder.
The upstream test plan's parts 6 and 8 explain evaluation under constraints; the plan also says part 8 passed an older simplification algorithm, so it does not by itself establish the current pinned backend's outcome.
The individual step exclusions retain the observed oracle mismatch separately from these substitution arguments.
