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

A definition may use one parametric sort, `MInt` with one argument, the width of a machine integer.
That argument is a sort parameter of the sentence, a numeral, or a sort of the module.
Every instance notion the frontend builds (declared instances, the instance an operand names, the instances of a parametric production, the recognition placeholder `MInt{K}` and the numerals declared as widths) reads that one argument at depth one, so no other shape names a sort the compiled definition declares.
Any other parametric head or arity (`MInt{A, B}`) is rejected when the definition is loaded with `User-defined parametric sorts are currently unsupported: MInt{A,B}`, a nested parametric sort (`MInt{MInt{W}}`, `MInt{MInt{8}}`) with `Nested parametric sorts are currently unsupported: MInt{MInt{W}}`, and a declared instance with an undeclared argument (`MInt{Foo}`) with `Could not find sorts: [Foo]`.
This is a recorded divergence from the pinned K frontend: it accepts a nested parametric declaration that nothing uses (`syntax {W} MInt{MInt{W}}`), and Rust rejects it by the same rule, since a nested sort names no width wherever it is written.

A production with sort parameters shaped like a subsort declaration is rejected at load with `Parametric subsort declarations are currently unsupported: {parent} ::= {child}; declare the subsort of each instance instead`.
The exceptions are `{S} KItem ::= S` and `{S} S ::= KBott`, which state what K fixes for every sort: every sort of K terms is a KItem, and the parse-time bottom is below every sort.
The definition's order relates sorts, and KORE's subsort axioms relate sorts, so a production with sort parameters states no pair of that order and has no subsort axiom.
Write the subsort of each declared instance instead, for example `syntax Foo ::= MInt{8} | MInt{16}`.
This is a recorded divergence from the pinned K frontend: it accepts such a declaration and writes a definition that its own backend validation refuses.

A sort synonym is a spelling of the sort at the end of its chain in the module's full view, including private imports.
Sorts are named in production positions, casts, sort-valued attributes, and data given to a parser (start sorts and `#token` sort strings); all use that denotation.
An alias must have no second meaning in the grammar views built at load, including views widened by implicit MAP and DEFAULT-CONFIGURATION imports.
Other meanings include visible sort declarations, configuration-expansion cell sorts, injected grammar positions, fixed-role sorts (kernel sorts, `#` sorts and the rigid sort variable), and the fixed `GeneratedTopCell` and `GeneratedCounterCell` names.
A production written with the alias where the synonym is visible is a use of it, as is a temporary cell-sort declaration added for that production's nonterminal.
The sorts compilation later generates around the top wrapper (`GeneratedTopCellFragment` and the `…CellOpt` sorts of its children when the configuration has a single root cell) are not yet excluded.
Production result and nonterminal sorts use that denotation; a production's own sort parameter shadows a synonym of the same spelling.
The `result` and `hybrid` attribute values use the same denotation for each whole sort spelling in the sentence's module's full view, including private imports; a production's own parameter shadows that spelling there too.
The loaded definition shows the denotation in these attributes.
A cycle, or one alias with two denotations in a view, is rejected at load with `InvalidSortSynonym`, whether used or not: those equations name no unique sort.
A synonym inside a sort argument is rejected, because application rewrites whole production sorts and the alias itself declares no sort.
Only rule and configuration casts restrict written aliases to those declared in their grammar's view.
A parser's start sort and `#token` sort strings may name privately imported aliases; a parse error retains the written start spelling.
Generated program parsers use the denoted start sort in their grammar and output name.
The pinned frontend applies one step, so a chain fails backend validation with `Sort 'SortB' not defined`, and rewrites a sort that a production parameter binds; these are recorded divergences.

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

`inj{A, B}` denotes the embedding of `A` in `B`, and the emitted definition declares subsort axioms only along the subsort order and none into `K`, so the compiler builds an injection only when `A <= B` along those axioms, extended with every defined sort and `Bool`, `Bag` and `Cell` below `KItem`.
A `KItem` is placed at a `K` position as a one-element sequence, and at a position above `K` (only a parser sort such as `KList` can be: a user sort is below `KItem`, so a user sort above `K` is a circular subsort) as the injection of that sequence, `inj{K, S}(inj{A, KItem}(t) ~> .K)`; no single injection crosses from below `K` to above it. Semantic-cast resolution accepts a variable's sort under a cast bound by the same placement relation.
The generated axioms follow the same rule.
The no-junk (`constructor`) axiom of a sort `S` lists `inj{A, S}` only for a declared strict subsort `A` from which a chain of subsort axioms leads to `S`, so the no-junk axiom of a sort above `K` (such as `KList ::= K`) lists `inj{K, S}` and no injection from `KItem` or a sort below it: those values are covered, as one-element sequences, by the alternative for `K`.
An overload axiom `f_greater(place(X)) = place(f_lesser(X))` places each argument and the lesser application at the greater production's sorts by the same placement: an injection along subsort axioms, and across `K` the one-element sequence. For `syntax Foo ::= f(K) [overload(f)]` and `syntax Foo ::= f(Int) [overload(f)]`, the argument of the `K` production is `kseq{}(inj{SortInt{}, SortKItem{}}(X), dotk{}())`, not an injection of `Int` into `K`.
An overload pair whose sorts are ordered but cannot be placed this way (a parser sort declared below `K`) is rejected with `InvalidOverloadProduction`.
A definition whose declared subsorts place a sort of K items at or above `KItem` or `K`, or a sort a variable stands at at or below `KBott`, `#KVariable` or `KConfigVar` (`syntax Exp ::= KItem`, `syntax KBott ::= Exp`, also through an intermediate declared sort or a user list), is rejected at load with `KernelSortPosition` on the declaration, before any rule or configuration is parsed: once the kernel positions are added, such an order is circular.
A sort predicate `isS` and a sort projection `project:S` exist only for sorts of K terms: `K`, `KItem`, `Bool`, every defined sort, and `KConfigVar`, which has a predicate and no projection because its tokens (`$PGM`) are written, never computed. The rule grammar offers exactly the helpers compilation declares.
A numeral, a `#`-prefixed parser sort (including a `#Layout` token sort a definition declares itself), `KBott`, `KLabel`, `KList`, `KString`, `Bag` and `Cell` have neither: no compiled K term has such a sort, so the predicate would be false on every argument and the projection defined nowhere.
A rule that writes such a helper does not parse. The projection cast `{T}:>S` lowers to `project:S`, so it exists exactly for the sorts with a projection: `{T}:>Bag`, `{T}:>Cell`, `{T}:>KList`, `{T}:>KLabel`, and a projection cast to a synonym of such a sort, do not parse in a rule, a configuration or a search pattern. The syntactic cast `T::S` and the semantic cast `T:S` lower to no helper. A strict `result` or `hybrid` sort without a predicate is rejected at the strictness stage, and a declared `isS` for such a sort is an ordinary function of the definition that conflicts with no generated predicate.

A numeral sort (`8` in `MInt{8}`) names a width, a natural number, and no term has it as its sort.
A width is written without leading zeros (`MInt{08}` is rejected), while the literal `0p08` has width 8 and keeps its text; the pinned K frontend instead declares `Sort08` beside `Sort8`.
It is spelled with one or more ASCII decimal digits, of any length.
The compiled definition declares it (`sort Sort8{} [nat{}("8")]`) only so that `MInt{8}` is well formed: a width is not a set of terms.
A definition may declare one (`syntax 8`) and use it as a sort argument, as a synonym target or in an attribute.
A production of a numeral sort, an operand of one, a `token` or `hook` declaration of one, a sort synonym spelled as one and a sort parameter spelled as one are rejected at load with `InvalidNumeralSort`.
The pinned K frontend accepts `syntax 8 ::= "eight"` and compiles rules over it whose terms never reach a K position; k-rust rejects that definition because a width has no terms.
A declared numeral, and a synonym of one, has no variable, cast, bracket or KItem position in either grammar, so `X:8` and `$PGM:8` do not parse.

`strict` or `seqstrict` on a production with sort parameters (`syntax {W} Foo ::= pick(MInt{W}, Int) [strict]`) is rejected at the strictness stage with `InvalidStrictness`, in every module of the compiled definition.
Such a production declares one symbol per instantiation, and its evaluation contexts range over all of them.
Compiled rewrite rules bind no sort.
The emitted theory embeds a sort in `KItem` only for each declared sort, and a bare parameter also ranges over `K` and `KItem`, whose placement at `K` is no injection, so no finite set of rules states those contexts.
A `context` written for one instance (`context pick(HOLE:MInt{8}, _)`) is instantiated by the parser and compiles to closed heat and cool rules.

Strictness on a function, macro, bracket or token production is rejected at the strictness stage with `InvalidStrictness` at the production.
A context rooted at such a production or at a macro-like label is rejected at the contexts stage with `InvalidContext` at the context.
A context lowers to heating and cooling rewrite rules that match its term: a function application is evaluated by its equations, a macro-like application is expanded before rewriting, a bracket is erased by every parser, and a token production's terms are domain values, so no rewrite step meets an application of these productions.
A heating or cooling rule applies only when the subterm it matches as `HOLE` is not yet, or is, of its result sort, so a `heat` or `cool` rule whose left-hand side does not match `HOLE` is rejected with `InvalidHeatCool` at the rule, and a context whose `HOLE` is rewritten to a term without `HOLE` is rejected with `InvalidContext`, since its cooling rule matches that term to plug `HOLE` back.

Every other construct that reads a term through the projection into a sort without one (`KConfigVar` included) is rejected where that term would be built, with the location of the construct that asks for it.
A configuration variable cast to such a sort is rejected at configuration expansion, at the configuration: its initial value is read through that sort's projection, and no value of a sort without K terms can be supplied.
A definition's own production labelled `#OuterCast` whose result is such a sort (`syntax #Foo ::= "{" K "}" "asFoo" [symbol(#OuterCast)]`) is a parse error at its use; with a result that has a projection it lowers to that projection like `{T}:>S`.
A semantic cast that is a downcast to such a sort (a K sequence cast to `KConfigVar` where `KItem ::= KConfigVar`, which only structured input can write) is rejected by sort injection, and by `sentence_typing` alike, as `DowncastWithoutProjection`.
In a search pattern (`krun --search --pattern`), each semantic cast, including the one the inner parser puts around every variable at its inferred sort, adds the sort predicate of its sort to the pattern's condition when that sort has one.
A cast to `Bag` adds the cell-fragment test `isBag`, which cell concretization expands into the sort predicates of the fragment's cells.
A cast to any other sort (`KLabel`, `KList`, `KString`, `Cell`) adds nothing: no compiled K term has such a sort, and the cast's sort is already the operand's sort in the compiled pattern, where a variable matches only terms of its sort and sort injection checks any other operand against the cast.
The positive `isS(X:S) => true` sort-predicate rule exists only when `S` is placeable at the predicate's `K` argument in its module's subsort order.
A sort with a predicate that is unplaceable (`KConfigVar` without `syntax KItem ::= KConfigVar`) keeps its predicate production and the `owise` rule `isS(K) => false`; `K` keeps its single positive rule.
The standalone `generate_sort_predicate_rules` API returns `Result` because resolving that order can fail.
A term whose sort is not below the sort of its position (an argument, a rewrite side, a `requires` or `ensures` clause at `Bool`) is rejected at the `add sort injections` stage with the sentence's source location; so is a semantic cast whose target is neither at or above its operand's sort (an upcast) nor strictly below it (a downcast, realized by `project:S`).
A parametric production's sort parameters are instantiated together by one solver: an instantiation fits when every argument's sort is at or below its instantiated argument sort and, when the position's sort is concrete and the result mentions a parameter, the instantiated result is at or below it; the least fitting instantiation in the pointwise order on the instantiated argument sorts is chosen, so `use2(X:MInt{8}, Y:MInt{16})` with `MInt{8} < MInt{16}` is instantiated at `16` and `make(X:MInt{8})` of `{W} R{W} ::= make(MInt{W})` at an `R{16}` position also at `16`. When no instantiation fits the position, the least one fitting the arguments is chosen and the position decides; an argument above every declared instance is rejected, and several incomparable least instantiations are rejected as ambiguous.
A parameter that occurs in no argument sort but in the result is ordered by nothing but its result, so the order then also compares the instantiated result sort. A result that is the parameter itself takes the position's sort. Otherwise the parameter's candidates are the values under which the whole instantiated result is the position or a declared sort below it, and the least of those is chosen: with `{W} MInt{W} ::= mk`, unrelated `A` and `B`, `MInt{A} < MInt{B}` and `Wide ::= MInt{B}`, `mk:Wide` is `mk{A}`. Two incomparable least instances that fit, such as `MInt{C}` and `MInt{D}` below `Pair`, are ambiguous. When no instance fits, the parameter stays a sort variable and the position rejects the term.
The position the solver sees is the sort the application is placed at: a cast's target when the application carries a semantic cast, otherwise its argument sort in the enclosing production, the rewrite's sort (a cast on a rewrite gives both sides its sort), or `Bool` for a `requires` or `ensures` clause. So `wrap(Z:A):Wide` with `{S} MInt{S} ::= wrap(S)` and `Wide ::= MInt{B}` is instantiated at `B` although its least instance is `A`, and it is ambiguous when two incomparable instances fit the target. When no instance fits a cast's target, the least instance fitting the arguments is kept and the cast is decided on its result: a target strictly below it is a downcast, whose projection places the operand at `K`, where that same instance is the least, and any other target is an incomparable cast. A larger instance whose result lies above the target does not justify a downcast: the operand inside the projection is instantiated at `K`, so the projection would not contain that instance.
An enclosing parametric production is solved after its arguments, from the arguments' sorts. While it is solved, each argument is placed at its declared sort, with the enclosing result parameter replaced by the enclosing position when the enclosing result sort is a bare parameter, and every other parameter replaced by an unconstrained sort variable. The argument is placed again at the solved instance when it is built. An enclosing position therefore fixes an inner instance in two ways. While the enclosing production is solved, an argument whose declared sort contains the enclosing result parameter, when that result is a bare parameter, is solved at the enclosing position. When the enclosing instance is built, an argument whose own instance was left open while the enclosing production was solved takes it from the instantiated argument sort. Such an argument is one whose parameters no argument of its own and no concrete position constrained. For example, with `{T} MInt{T} ::= inner2`, `{S} MInt{S} ::= outer(MInt{S})` and `MInt{A} < MInt{B}`, `outer(inner2):MInt{B}` is `outer{A}(inner2{A})`: `outer` takes the least instance that fits the cast, and `inner2`, which nothing else constrains, takes the instance of `outer`'s argument. With `{S} S ::= wrap(S)`, `{T} T ::= inner(MInt{T})`, unrelated `A` and `B` and `MInt{A} < MInt{B}`, `wrap(inner(X:MInt{A})):B` is `wrap{B}(inner{B}(inj(X)))`, while `wrap(inner(X))` without the cast is `wrap{A}(inner{A}(X))`.
Label sort parameters are therefore never written: a label in a rule, claim, context, context alias or configuration that carries sort parameters is rejected, naming the label and its parameters, instead of being re-solved: `load_structured` rejects it on the caller's own sentences before configuration expansion (`LoadError::LabelParameters`, since expansion recognizes cell wrappers by name and would drop a parameter on one), `expand_configurations` rejects it on any configuration it is given, for the same reason (`ConfigurationError::LabelParameters`), every loader route and the `LoadedDefinition::from_loaded_parts` and `with_definition` constructors reject it when they build a `LoadedDefinition` (`LoadError::LabelParameters`), so `compile_loaded_definition` never receives one, and `sentence_typing` rejects it for that sentence. The instance is always the solver's: an upcast on an argument does not raise it (`wrap(s(X):Num)` with `{S} Wrap ::= wrap(S)` is `wrap{Nat}`), a cast on the whole term or its position fixes a parameter that occurs in the result, and an instance above an argument's sort is reached only through a projection (`wrap({X}:>Num)`), exactly as in source text.
Rejection rather than honouring is deliberate: honouring a supplied parameter would let a caller write terms source text cannot, while silently re-solving it would compile a term other than the one supplied; rejection keeps structured input exactly as expressive as source text and never rewrites it.
A rule's label instance is always the solver's; an undetermined instance cannot match a ground symbol instance, because backend matching compares symbol sort arguments by equality.
Execution terms are unaffected: their KORE symbols carry every instance explicitly.
Honouring a present parameter as an assertion is a compatible later extension, since it only accepts terms that are rejected now; it becomes worth its cost when a consumer needs to write a specific instance source text cannot derive.

A value-building production whose result sort is its own sort parameter (`syntax {S} S ::= wrap(S)`) must not be instantiated at a sort whose values its hook or domain values fix (`hooked-sort` or `hasDomainValues` in the emitted declaration), including when an `anywhere` rule heads it: its applications have their own root, which neither the hook nor a literal supplies.
Sort injection checks the instance where it places it in rules, claims, configurations, programs, `-c` values and search patterns, with the sentence's source location when there is one.
`K` and `KItem` are not fixed: the KORE prelude declares them as ordinary sorts.
Function and macro schemas (`ite` included) are unaffected, because their applications denote equation results or expand before rewriting.

A sentence sort variable left by sort injection may occur only as a whole sort argument of a matching-logic connective: the sort of a predicate, which is the whole carrier or empty at every sort alike.
The emitted rule, claim, equation or macro binds exactly those variables.
Any other occurrence is rejected at `add sort injections` with a located `UndeterminedInstance` diagnostic naming the application whose instance neither its arguments nor its position determine; add a sort cast that fixes the instance.
A phantom parameter occurs in neither an argument sort nor the result sort (`syntax {S} Int ::= size()`), so no cast fixes it: its production may be declared, but no rule may use it.
A program, configuration value or search pattern binds no sort variable, so its diagnostic requires every instance, including a predicate's sort, to be determined.
Program and configuration-value syntax has no sort casts, so only a search pattern's diagnostic advises a sort cast.

A program or configuration value is instantiated at the sort it is read at; that position decides only parameters its arguments leave open.
A value read at `K` is instantiated with a `KItem` preference, which fixes only parameters its arguments leave open; an actual fixed `K` result retains its whole value.
A program, configuration value or search-pattern root is macro-expanded and instantiated at one position: the configuration position of its declared or start sort (`KItem` for `K`), or `GeneratedTopCell` and `Bool` for a pattern's body and condition.
Expansion discards the parser's parametric instances and reads each application's instance from the typing of the current value at that position, which is the instance sort injection emits.
A program, configuration value or search pattern whose label instance nothing determines is rejected before KORE conversion, naming the configuration variable or search pattern and the label.
These terms have no sentence binder, so no sentence sort variable may remain in them, even as the sort of a predicate.

The injector's relation admits `MInt{#SortParam{Q}}` below `KItem` for a sort under construction, but a sentence that keeps that sort outside a predicate sort is rejected after injection.
The emitted theory therefore needs no subsort axiom for that open instance; the per-sort KItem subsorts are stated separately.
A cast on a K sequence, an injected label, or a sorted variable is compared with the operand's own sort like a cast on an application; a cast on a rewrite or `as` pattern is the sort both sides are injected at; an `as` alias variable with its own sort is placed at that sort like the pattern, and only a sortless alias takes it.
The check applies to every rule-like sentence `compile_loaded_definition` emits, whether parsed from source, supplied through `load_structured`, or edited and rebuilt with `LoadedDefinition::with_definition` or `from_loaded_parts`; a pass that meets an ill-sorted term earlier may reject it first with its own message.
[Sort-injection tests](../crates/k-rust/tests/sort_injections.rs) pin the rejections and their controls.
`kompile::sentence_typing` (or a `SentenceTyper` built once per module) reads the same computation on a loaded rule or claim: it resolves the sentence's semantic casts and projects a body with a rewrite into its left and right branches, as compilation does before injection, and reports for each path (the field, then rewrite sides, as-pattern children, application arguments with casts included, and sequence items) the sort injection places the term at and the sort its position requires, computed by the injector on the resolved and projected term; a path typed differently in the two branches is reported per branch. It returns the compiler's own error for a sentence the checks reject.
It types in the order injection runs in, where every user sort is declared below `KItem`; it reports no sort for `#cells`, `#dots`, `#noDots`, and variables nothing types, places an authored cell's body at its content sort, and reports a cast operand's requirement as the cast's sort (below a downcast the operand's own sort is above it).
[Typing-view tests](../crates/k-rust/tests/sentence_typing.rs) check it on hand-picked positions, on every loaded rule of the prelude, and against the injections the compiled definition contains.

## Bracket productions

A production with the `bracket` attribute is concrete syntax only: every parser, the generated Bison parsers included, replaces a bracket node by its child before a term exists, so no program, rule, claim, configuration or search-pattern term contains a bracket's symbol.
`definition.kore` therefore declares nothing for a bracket production, whether it is unlabelled, labelled in source (`"(" Exp ")" [bracket, symbol(paren)]`) or labelled in structured input: its symbol occurs nowhere in that file, in no declaration, functional, no-confusion or no-junk axiom.
A no-junk alternative for it would assert that its sort has values no term can build, and the backend reads the no-junk axiom as the sort's finite set of constructors, so a constraint excluding every real constructor would no longer simplify to `\bottom`.
`syntaxDefinition.kore`, the signature of concrete syntax, declares the bracket under its label, or under its `bracketLabel` when it has none, with `bracket` and `format` for unparsing and, when labelled, the priority and associativity relations that use the label as their tag.
There it keeps `constructor`, `functional` and `injective`: in a concrete parse tree a bracket node is a free constructor.
[Structured-definition tests](../crates/k-rust/tests/structured_definition_conformance.rs) check the source and the structured forms, and that the bracket stays out of the backend's constructor domain.

## Generated parser coercions

Generated Bison parsers use the compiler's licensed outer placement plans.
Equal sorts preserve the value, concrete non-reflexive injections require an emitted subsort path, and an item at K becomes `kseq(item,dotk())` with KItem and K node sorts.
A whole K value retains its tail, including when embedded into a declared supersort of K.
Only witnessed injection pairs may flatten; sequence construction is never an injection edge.
An unplaceable grammar coercion fails generation with its production, source location and sort pair.
User-list bridges construct their cons/nil value directly.
Parsing-only recognition bridges for parametric placeholders return the recognized value unchanged and state no injection.

Overload actions return equal-result applications directly and recover narrower arguments only through concrete licensed placements.
A K argument can narrow to an item only when it is a canonical singleton with a dotk tail; empty K, multiple items and arbitrary K-returning applications retain the greater overload.
Dynamic argument sorts select a finite set of witnessed branches, so generated C cannot invent an injection pair at runtime.
These corrections change previously malformed parser output such as `inj{KItem,K}` and reflexive result injections; ordinary constructor and token encodings retain their existing representation.

## Configuration value transport

Every configuration-map value is transported as `#KConfigValue(K):KItem`, an ordinary private constructor generated with the partial function `#unboxKConfigValue(KItem):K` and its sole equation `#unboxKConfigValue(#KConfigValue(KS:K)) => KS`.
The generated module and these labels are reserved.
A nullary cell initializer is declared `total` only when every generated rule has evidently defined configuration content and a trivial `ensures`; initializer dependencies are judged by a least fixed point, so cycles remain unproven.
At least one unconditional equation must cover its only argument tuple.
Generated cell constructors and optional-cell units use the same equation totality judgement as written labels; hooked collection units count as defined only when their own production is configuration-generated and they head no non-simplification rule, including ordinary, anywhere and macro equations.
Before cell closing, the evidence also checks every child unit that closing could insert, conservatively withholding parent totality even when a child with a partial absence unit is already present.
Local-function resolution precedes this judgement and records which generated lambdas cover every argument tuple.
Both early and deferred lambda totality require a variable pattern whose every semantic cast and recorded inferred sort equal the generated parameter sort; a nested cast or inferred sort narrower than the parameter sort loses `total`, even when its body is defined.
The deferred judgement admits those lambdas and nullary initializers in one least fixed point, so a lambda can use a proven initializer while cycles cannot prove themselves; lambdas already proved total retain their declarations.
An initializer reads `project:S(#unboxKConfigValue(Map:lookup(Init,key)))`, retaining its declared projection, including `project:K` for a K variable and `project:KItem` for an uncast variable.
An actual K sequence, empty K or fixed K-returning function remains the whole K payload; a KItem or a value with a licensed embedding into KItem becomes a singleton K sequence.
The outer placement preserves the instance and macro choice made at the existing KItem preference for a K read.
KItem-to-K placement uses `kseq(item,dotk)`, never an injection.

For a binding declared at K, the configuration parser prefers a successful KItem reading and tries its selected module's existing K entry only when there is no item reading or no KItem start sort.
Ambiguity, inference, validation and macro errors are retained.
Explicit program start-sort parsing and grammar visibility remain unchanged.
Compiled metadata now records a K-declared variable as K, while a generated `$PGM` parser still starts at KItem for a K declaration.
Supplied values are still parsed, expanded and checked when no initializer reads the map, then dropped because the top initializer is nullary.

Serialized maps and depth-zero initializer patterns expose the box, which ordinary simplification removes from initialized cells.
Already compiled definitions must be recompiled to use this transport format.
The pinned reference emits an unlicensed K-to-KItem injection for whole K values; k-rust's transport preserves their sequence tails and uses only licensed injections for map keys and item embeddings.
N37 removes only this private protocol from the k-rust side of compile comparisons and translates initializer reads back to the reference's item representation.
A translated initializer's body-derived identifier is aligned with the reference only after the complete translated sentence matches, excluding that identifier and the comparison's existing source metadata.
The parsed-definition comparison removes only the exact private module and its imports and translates the same initializer reads before injection.
It counts all rewrites, rejects a reference declaring or using either private transport symbol, and retains unrelated equations, lookups, projections and no-junk alternatives.

## Domain values

A literal `#token("s", "S")`, emitted as `\dv{S}("s")`, denotes the element of `S` that `s` names in `S`'s literal domain, and the emitted definition declares that domain only by the attribute `hasDomainValues` on the declaration of `S`'s head.
A sort admits domain values exactly when its head has a token declaration (a `token` production or a `token` sort declaration; for a parametric one, the instances of the declared sort), or it is `Bool` or `KConfigVar`.
`Bool` and `KConfigVar` admit them in every module, even a structured definition without their token productions, because the compiler writes their literals itself: a `requires` clause becomes an equation against `true`, and configuration-map keys are `KConfigVar` literals.
A hook alone does not admit domain values: it fixes how the backend computes on a sort's values, not a literal syntax for them, and `MAP.Map` has a hook and no literals.
A literal at any other sort is rejected by the definition checks with `InvalidDomainValue`, and one a compiler pass writes after them is rejected by term conversion with `InvalidToken`.
The emitted declaration of a head carries `hasDomainValues` exactly when that head admits domain values, so `Bool` and `KConfigVar` carry it even without token productions, and every domain value of the emitted definition is at a sort declared with it.
[Token admissibility tests](../crates/k-rust/tests/token_admissibility.rs) pin the admitted sorts and the rejection of a hooked sort's literal.

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
KORE readers, writers, and host and RPC request ingress are bounded by process memory; on a native host the backend runs its recursive passes over a pattern or definition on a stack it sizes for the input's depth, refusing with an ordinary error only input deeper than the largest stack it provides, and the stages still bounded by the host thread's stack are listed in [backend-port.md](backend-port.md#json-depth-policy).

## Formal parameter preference

A formal sort parameter of a parametric production is not a variable of the sentence (K user manual, "Parametric productions and `bracket` attributes").
Sort inference therefore orders the readings of a sentence only by well-sortedness, by maximality over the sorts of its variables, and then by `prefer`/`avoid`; a sentence with several readings left after these steps is an ambiguous parse error (K user manual, "Variable Sort Inference" and "Symbol priority and associativity").
The `K`/`KItem`/`Bag` preference on formal parameters only chooses how a kept reading is instantiated: it compares parameter vectors that keep the same set of well-sorted readings and never removes a reading that some vector types.
A parameter that the kept readings leave free is instantiated at `K` by that preference, also where the module's order leaves `K`, `KItem` and `Bag` unrelated, as a program grammar does: each of the three then meets one preference, and the preference ranks `K` first, then `KItem`, then `Bag`, so a free parameter is one parse, not an ambiguity between its instances.
A parameter is instantiated only at sorts of the module.
A parameter that occurs inside a parametric sort (the `Width` of `MInt{Width}`) ranges over the module's declared instances of that sort, so a width the kept readings leave free takes them: one fitting instance is chosen, several are an ambiguous parse error, and none is a rejection naming the production.
For example, `rule foo(X) => g` over `syntax {W} Foo ::= foo(MInt{W})` is accepted at `MInt{8}` when `MInt{8}` is the only instance.
The pinned K frontend does not terminate on that rule, and picks one of two declared widths where Rust reports the ambiguity.
Alternatives that are equal once bracket nodes are erased are one reading, not several: `rule #Ceil(X:W) => (#Top) [simplification]` has one parse, `#Top{K}`, exactly as without the brackets.
The concrete instances of one parametric production are one production of the parsed term, so they never form separate readings either.
The instance a kept reading was parsed at is not part of the loaded sentence: rule, claim, context, context-alias and configuration bodies are loaded with no label sort parameter, since source text cannot write one, and sort injection instantiates every parametric label from its arguments and position ([Sorts of compiled terms](#sorts-of-compiled-terms)).
A program, configuration value or search-pattern root is macro-expanded and instantiated at one position: the configuration position of its declared or start sort (`KItem` for `K`), or `GeneratedTopCell` and `Bool` for a pattern's body and condition.
Expansion discards the parser's parametric instances and reads each application's instance from the typing of the current value at that position, which is the instance sort injection emits.
Macro expansion runs before sort injection, so where a macro rule's head is parametric it reads instances from the typing view (`SentenceTyper`, the typing compilation gives each position): a head's instance from the typing of its macro rule, and an application's from the typing of the sentence it stands in or of the ground value at its position, taken after its arguments are expanded and after every earlier rewrite of that sentence or value.
The instance is the label's own, as injection instantiates it, not the sort a downcast places the application at.
A macro rule applies only to an application whose instance agrees with its head's on every parameter both fix; a parameter the typing leaves open agrees with every value.
Where the sentence or ground value does not type yet, the instance is unknown and only a head that fixes no parameter applies; one still unknown at the fixpoint is left for injection to reject.
Every application to which no rule applied from a rule set with a parametric head fixing a parameter is retried after later rewrites until nothing changes, since a rewrite elsewhere can change even a known instance.
Every other comparison of a rule's label with a production or term label (the macro table, `anywhere`, and rule-by-label lookups) is by the label's name.

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

Only a rewrite step of the configuration reads and advances the counter cell, so a `!` variable is accepted only in a rule applied as such a step.
It is rejected with `InvalidFreshConstant` at the sentence in a function, simplification, anywhere, macro or alias rule, each an equation applied to the term its left-hand side matches without the configuration, and in a claim, which states which configurations a path reaches and takes no step of its own.
Within a rewrite rule the value exists only once the step applies, so a `!` variable may occur only where the rule builds its result: on the right-hand side of a rewrite and in `ensures`.
It is rejected where the rule matches (the left-hand side of a rewrite, or outside every rewrite), which would compare the subject with a value nothing in it holds yet, and in `requires`, which decides whether the step applies before it allocates anything.
It is also rejected anywhere in a context: the heating step builds the context's term and the cooling step matches it again, and a value one step allocates is not one the other can match.
A local function (`#fun`, `#let`) on the right-hand side of a rewrite rule may mention a `!` variable: its equation receives the value from the enclosing rule as an argument.

## Anywhere rules

Rust accepts and executes anywhere rules.
This differs from K's Haskell frontend, which rejects them (`checkAnywhereRules` in `k-frontend/src/main/java/org/kframework/kompile/Kompile.java`) or, under `--allow-anywhere-haskell`, removes them (`removeAnywhereRules` in `k-frontend/src/main/java/org/kframework/backend/kore/KoreBackend.java`).
The reason is the language specification: the [`anywhere` attribute](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/docs/user_manual.md?plain=1#L1322-L1340) instructs "the backends" to apply the rule wherever it matches in the entire configuration, and it names no backend for which the attribute is unavailable.
A definition that uses the attribute is therefore a K definition whose meaning is specified, and a backend implementing that meaning must not reject or silently drop its rules.
Rust emits each anywhere rule as a KORE equation whose left-hand-side symbol carries the `anywhere` attribute, and the backend evaluates it during simplification like a function equation, as the manual's "simplified similarly to a `function`" describes.
Because that equation sees only its left-hand side, an anywhere rule that needs the configuration around it is rejected at the rule: a fresh variable `!X` draws its value from the counter cell, which the equation can neither read nor advance ([Compiler-resolved fresh constants](#compiler-resolved-fresh-constants)), and a left-hand side of several sibling cells is a fragment of their parent's children with no head of its own (the parent cell written around them is a term, and such a rule compiles).
A symbol that carries `anywhere` or a macro-like attribute and neither `constructor`, `functional`/`total` nor `function` is a partial function evaluated by its equations, and its applications carry definedness obligations.
When the frontend withholds `functional` from a value production, it emits the declaration attribute `value-production{}()` alongside its equation marker.
The Rust/Haskell target also emits `function{}()` so that KORE verifiers admit equations headed by the symbol.
`value-production` states that an application no equation reduces is a value of its sort; it asserts neither totality nor freeness.
The LLVM target emits neither `function{}()` nor `functional{}()` for such a production.
The external LLVM backend reads `function` to mean that an irreducible application is a computed application rather than a value, and does not read `value-production` to restore the value reading.
Withholding `function` therefore preserves the value production's irreducible applications while its anywhere equations can still reduce other applications.
Rust's backend sets `declared_function` only for `function` without `value-production`, so an anywhere head (the head of an anywhere rule, or an overload-greater) stays an `EquationHead` and a macro-like head stays `Residual`.
Both load as `Function(Partial)` and retain definedness obligations.
For a `value-production` head the obligation is discharged where the marker decides it: an application that no equation reduces on any valuation (the simplifier's certificate on a ground normal form, or instance normality: every equation that could be offered it fails to unify with it or to match it) is a value, so its `\ceil` is that of its arguments.
So FUN's `\ceil(k -> 7)` is `\top` (the currying equation needs an application `P1 P2` as first argument), while `\ceil(wrap(Y))` stays an obligation when an equation reaches an instance of `wrap(Y)`, and a plain `anywhere` head without the marker claims nothing about its irreducible applications.
The marker is emitted from the production kind and totality judgement, not read from a K source attribute.
A source function carries no such marker: an application its equations leave unevaluated remains a computed application.
Any other symbol without one of those claims is rejected (`Invalid type for symbol`).
A non-function value production carries compiler-added `functional` and its functional axiom exactly when it heads no anywhere, macro-like or overload equation, or every such equation has a trivially true `ensures` and a right-hand side evidently defined by declared-total symbols and heads admitted earlier.
A label heads a rule equation only through a rule that is not a simplification lemma, so a simplification lemma or a macro label that heads no rule makes no production an equation head.
On a value production, the frontend discards a deprecated source `functional` before emitting the judgement's claims in both the semantic and syntax definitions.
It restores `functional` only when the judgement establishes totality, keeping the declaration and its functional axiom consistent with the definedness reading used for generated lambdas.
To state totality as an author axiom instead, use `function, total`; that declaration remains trusted.
A deprecated `functional` on a `function` production states the same claim and is read exactly as `function, total`: the declaration carries `functional` and its functional axiom.
An equation equates the head with its right-hand side wherever its condition holds, so an undefined right-hand side contradicts an unconditional totality claim; conditions and left-hand-side patterns restrict applicability but do not establish definedness.
The judgement uses a least fixed point: neither a head nor a dependency cycle may establish its own totality.
A stage that still sees the self-referential equations `foo(a => b)` (whose right-hand side is `foo(b)`) or `(5 => 6) : _` cannot use the head itself as totality evidence.
The judgement reads each stage's terms: macro expansion can remove a circular dependency before emission, while constructor-only overload chains and macros with defined expansions retain `functional`.
Normalization N36 drops the reference declaration's `functional` and its functional axiom only when the port carries the same equation-head attribute and withholds both claims.
For a matching value-production declaration it also drops the port's `value-production{}()` and any extra `function{}()`, counting each removal separately.
It accepts both the Rust target's marked function and the LLVM target's marked value declaration.
It preserves a source function's `function{}()` and every unrelated attribute and axiom.
For the kore/llvm pairing, normalization N38 adds `function{}()` only to marked value-production declarations in a separate copy used for reference-tool verification, and prints the number changed.
It refuses a marked LLVM declaration that already carries `function` or `functional`.
The verifier requires a function or functional equation head, so this copy lets it check the remaining KORE without asserting evidence-free totality or changing the definition the LLVM backend executes.
The Rust/Haskell pairing verifies the original definition without N38.
Rust's kompile does not add `injective` to the symbol declaration of such a production, but emits a user-written `injective` attribute as written. That attribute is an axiom (equal applications have equal arguments), and an anywhere equation may identify applications with different arguments: `wrap(s(X)) = wrap(X)` gives `wrap(s(z)) = wrap(z)`, and with `s(z) != z` the declared theory would be inconsistent. The same holds for the head of a macro-like rule, whose emitted axiom is an equation of the same kind.
For the same reason Rust's kompile adds neither `constructor` nor `injective` to a production that heads a macro-like rule and emits no no-confusion axioms for it, even when the macro-like attribute sits on the rule and not on the production: the rule `plain(X) => done(X) [macro]` is the equation `plain(X) = done(X)`, which contradicts `plain(X) != done(Y)`. The same holds for a production whose label another, macro-like production also has, since every rule headed by that label is then a macro-like rule. Such a declaration carries no `macro` attribute either, since a rule whose left side does not cover every argument leaves the other applications unexpanded. The definition checks admit macro-like attributes only on productions, so this case reaches emission only through the library functions that emit an unchecked definition (`module_to_kore` and its `_from_resolved` variants).
An overload-greater production keeps `injective` exactly when every production below it in its overload family is a non-function, non-`assoc`/`comm`/`idem` production that heads no anywhere or macro-like rule: its overload equations send each application to the injected normal form of the most specific lesser production that accepts the arguments, or leave it normal, so two argument tuples meet only through the same production at the same arguments. `simplification` rules are lemmas and do not count. This differs from the reference frontend, which declares every such production `injective`; no backend decision in Rust reads the attribute of an anywhere symbol.
An overload-greater production `g` never carries `constructor`, because its overload equations evaluate it; it has the injectivity axiom and the no-confusion axioms (`\not(g(X) ∧ c(Y))` against every other symbol `c` of its sort that has them) exactly when it heads no anywhere or macro-like rule itself and two conditions hold, and otherwise has neither. Condition (a) is the one above: every production below `g` is locally injective. Condition (b): no other production related to `g` in the overload order, whether above it, below it, or sharing a lesser production with it, has `g`'s result sort head. The overload order is transitive, so both conditions cover chains of lowerings. Under (b) every value an application of `g` reaches is either that application in normal form or an injection `inj{T,S}(v)` from a strictly smaller sort, which differs from every application of another no-confusion symbol of `S`; under (a) two such values coincide only through the same production at the same arguments. Without (a) the injectivity axiom is false: with a lesser `abs(Int) : Int [function]`, `g(inj(1)) = inj(abs(1)) = inj(abs(-1)) = g(inj(-1))`. Without (b) a disjointness axiom is false: for `asInt(Int) : Value` below `asNumber(Number) : Value`, the overload equation `asNumber(inj(X)) = asInt(X)` instantiates `\not(asInt(X) ∧ asNumber(Y))` at `Y := inj(X)` to `\not(asInt(X))`, which denies a functional application, so the theory has no model; two greaters of one sort that share a lesser `l` both equal `inj(l(x))` in the same way. The withheld axioms are therefore false in every model of the emitted equations, not merely unproved. A greater that satisfies (a) but not (b) keeps the `injective` attribute, and one that fails (a) carries neither the attribute nor any of the axioms. Normalization N34 drops the corresponding axioms from the reference side of the compile comparison.

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

## Anywhere heads in equation arguments

A function rule whose left-hand side contains an anywhere production is emitted as a function equation whose argument pattern contains that production's symbol, declared `anywhere` and, when its anywhere equations can identify applications with different arguments, neither `constructor` nor `injective` ([Anywhere rules](#anywhere-rules)).
The pinned reference `kore-parser --verify` rejects such a definition with `Found invalid subterm in argument of function equation`: it admits in an equation argument only applications of `constructor` symbols, sort injections, symbols declared both `anywhere` and `injective`, and the concatenation, element and unit symbols of the builtin collections.
No declaration Rust could emit meets that check and stays true. `constructor` and `injective` both state that equal applications have equal arguments, the symbol is not a sort injection, and it is not a collection symbol.
In FUN (`pl-tutorial/2_languages/3_fun/1_untyped/1_environment`) the anywhere rule `F P = E => F = fun P -> E` equates `(f x) = e` with `f = fun x -> e`, and `[E1,E2,Es|T] => [E1|[E2,Es|T]]` equates two `[_|_]` applications with different arguments, so the equations of `names`, `exps` (argument `X:Name = E and Bs`) and `getMatching` (argument `[H | T]`) cannot be accepted by the check under any true declaration.

Such an equation is still a sentence of a consistent theory, and Rust evaluates it as the rule specifies.
An equation `f(p(X)) = r(X)` holds in a model when every value that is an instance of `p(X)` gets the value of `r` at that instance; it can contradict the rest of the theory only if two instances that denote the same value give different right sides.
In the intended model every value is the value of a normal form and distinct normal forms are distinct values.
When the argument pattern is normal on every instance, meaning no anywhere equation of a head in it applies at any instance of its variables, two instances denote the same value only when they are equal, so the equation assigns each argument value at most one result.
The three FUN patterns are normal on every instance: the `_=_` equation applies only when its first argument is an application `F P`, and an injected `Name` is never one (an `F P` value is an application of that production or an injected `Val` constructor application); the `[_|_]` equation needs at least two elements before `|`, and `[H | T]` has one.
A value that equals an instance only through an anywhere equation, such as the binding `(f x) = e` for the `exps` equation, is still matched: arguments are normalized before the enclosing equation is tried, giving `f = fun x -> e`, and matching decides an anywhere subject application only when it is normal on every instance, so an `owise` equation such as `getMatching(_, _) => matchFailure` never applies to an argument an earlier equation matches modulo the anywhere equations.

The `verifier-anywhere-argument` exclusion covers exactly this rejection: a `kore-verify` step whose first diagnostic is `Found invalid subterm in argument of function equation:`.
The conformance driver records a `kore-verify` rejection as its own step after all other steps of the case and still runs the `definition.kore` comparison, so the exclusion leaves the comparison and every program step of the case ranked.
Its limit is the verifier's: it reports only the first rejected sentence, so a later, different rejection of the same definition stays hidden until the first is resolved. The Rust verifier (`k-rust-backend` `verify.rs`) does not make this check and loads the definition.

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

## Set concatenation is nilpotent

k-rust implements one theory of `_Set_`, in concrete and in symbolic evaluation: concatenation is nilpotent.
`S1 S2` is the disjoint union, defined only when `S1` and `S2` share no element; `SetItem(X) SetItem(X)` is `\bottom`.
The union of sets that may overlap is `|Set`, which `domains.md` defines as `S1 (S2 -Set S1)` and which is unchanged.
This is the theory the `domains.md` prose states ([`domains.md`](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/k-distribution/include/kframework/builtin/domains.md), "Set concatenation": "the concatenation of two sets containing elements in common is `#False`").
It is also the theory AC matching of sets rests on: a pattern `SetItem(X) R` decomposes a set in one way per element because `X` is not in `R`.

So a concrete run that concatenates sets sharing an element ends in an undefined step, like any rule whose right-hand side is undefined ([Undefined steps in proofs](#undefined-steps-in-proofs), [Trivial rule results](#trivial-rule-results)).
`krun` warns that the rule "applied with an undefined result" and prints `\bottom`; a hooked function applied to such a set, such as `size`, is `\bottom` too.
Concatenating disjoint sets and `|Set` give the same results as before.
A cell collection declared with `type="Set"` is such a set too: a step that adds a cell equal to one the collection holds, or makes two of its cells equal, is undefined, where it used to merge them.
The `STAR-CELL-HEATING-SET` fixture shows it: its two tasks complete to the same cell, so `two.pgm` ends in an undefined step at depth 10.

The reason is that concrete and symbolic evaluation are two evaluators of one definition and must agree on every ground instance.
The symbolic side already reads concatenation as nilpotent: the definedness of `S SetItem(I)` is `I` not in `S`.
Before this rule, the concrete side merged the shared element, so `start(1)` with the set `SetItem(1)` reached a successor that the symbolic step, specialised to that instance, says does not exist; a ground claim was proven while its symbolic generalisation failed.
The concrete check costs nothing extra: concatenation inserts every element of one set into the other, which is where a shared element shows.
Internally, `Term::set` keeps a repeated element (sorted, adjacent), as `Term::map` keeps a repeated key, so definedness (`\not(X = X)`), matching (no match), the hooks (`\bottom`) and the simplifier see it.
The simplifier reports a set holding a syntactically repeated element as `\bottom` where it is built, as it reports a builtin's undefined result such as `10 /Int 0`: in a rule's right-hand side, in the result of a function equation, or after a substitution.

This diverges from the reference concrete execution, which merges overlapping sets; `domains.md` notes that overlap "may be silently allowed during concrete execution".
A definition whose concrete runs rely on that merge gets an undefined step in k-rust at the step that concatenates; writing `|Set` there states the union it means.

The `_Set_` production in `domains.md` also carries `idem`, which states `S S = S`.
That contradicts nilpotency for every `S` except `.Set`.
k-rust accepts the attribute and does not honour it: `kcompile` still translates it into its KORE axiom `_Set_(K, K) = K`, as for any `idem` production, so the compiled KORE is unchanged; the backend evaluates and matches by no `assoc`, `comm`, `unit` or `idem` axiom (a hooked collection implements its algebra in its representation), and the `SET.concat` hook fixes concatenation as nilpotent.
A `total` function whose equation concatenates overlapping sets is not total; k-rust trusts the attribute, as for any `total` function, but a syntactic repeat in the function's result is `\bottom` all the same, because the repeat itself is undefined, whatever the attribute of the function that built it.
So `tAdd(SetItem(1), 1)`, with `tAdd(S, I) => S SetItem(I)` declared `total`, is an undefined step in `krun` and fails a ground claim, as `10 /Int 0` does.
Elements that are not syntactically equal, such as `1` and `I` in `tAdd(SetItem(1), I)`, may denote one element; that stays the set's definedness condition (`\not(1 = I)`), which a trusted `total` application does not raise, so a symbolic claim over it can still be proven.

The `set_concatenation_is_nilpotent_in_krun_and_kprove` CLI test, `spawning_a_duplicate_ground_cell_is_an_undefined_step` and `a_set_holding_an_element_twice_matches_nothing` in the [backend tests](../crates/k-rust-backend/tests/backend), and the unit tests of [set.rs](../crates/k-rust-backend/src/builtin/set.rs) cover this.

## Map concatenation binds each key once

A map binds each key once, so `_Map_` is defined only on maps whose keys are disjoint: `(K |-> V1) (K |-> V2)` is `\bottom`, whether `V1` and `V2` are equal or not.
Overwriting a binding is `M[K <- V]` (`MAP.update`) or `updateMap`, not concatenation.
k-rust applies this in concrete and symbolic evaluation alike, as for sets ([Set concatenation is nilpotent](#set-concatenation-is-nilpotent)).
`Term::map` keeps a key bound twice, with the same value or not, and does not merge two identical bindings.
Definedness emits `\not(K = K)` for the repeat, matching fails on it, a `MAP` hook with such an argument is `\bottom`, and the simplifier reports the map as `\bottom` where it is built.
So a step whose right-hand side builds such a map, directly or through a function equation (`total` or not), is an undefined step, and a ground claim over it fails.
Keys that are not syntactically equal stay a definedness condition, as for sets.
The condition that a key `K` is not a key of an opaque rest `M` uses the definition's `MAP.in_keys` function at the key and map sorts, as `\not(in_keys(K, M) = true)`.
Without one, it is the pattern `\exists V. \ceil(K |-> V M)`, which states that `K` and `M` are defined and `K` is not a key of `M`, whatever value the entry has; for a set without `SET.in` it is `\ceil(SetItem(K) S)`.
The backend keeps the map and the set form alike as one atom of `K` and `M` (`rule::Absence`), so a step that only changes the value bound to `K` restates the condition its path already holds; responses print it as that pattern, and a request that sends the same pattern back states the same atom.

The reason is the same as for sets: a map value is a finite function, and concrete and symbolic evaluation must agree on every ground instance.
The symbolic side reads `M (K |-> V)` as defined only when `K` is not a key of `M`; merging `(1 |-> 2) (1 |-> 2)` into `1 |-> 2` made a ground instance reach a successor that the symbolic step, specialised to it, says does not exist.
Before this, k-rust merged two identical bindings everywhere, in a rule's right-hand side too, while it kept two bindings of one key to different values (so a `total` function producing them left both in the configuration).

This diverges from reference concrete execution in form, not in outcome: the reference toolchain also treats a repeated key as undefined, but the LLVM backend aborts with an exception ("Duplicate keys in map concatenation") and the Haskell backend's `krun` prints `#Bottom`, or reports a `total` function that evaluated to `\bottom`, where k-rust ends in an undefined step.
The `a_repeated_set_element_or_map_key_is_bottom_where_it_is_built` CLI test, `a_map_binding_a_key_twice_simplifies_to_bottom_where_it_is_built` in the [backend tests](../crates/k-rust-backend/tests/backend) and `a_map_argument_binding_a_key_twice_makes_the_hook_bottom` in [map.rs](../crates/k-rust-backend/src/builtin/map.rs) cover this.

## A contradicted `total` attribute is named, not repaired

k-rust's backend takes an emitted symbol's `total` (or `functional`) attribute as an axiom: an application of it to defined arguments is defined, so a rule whose right-hand side holds only total applications carries no definedness obligation, and a symbolic claim through such an application can be proven.
The frontend derives value productions' `functional` claims from their equations, including when the source carries deprecated `functional`, as [Anywhere rules](#anywhere-rules) describes.
For a source `function, total`, the attribute is the author's claim, and deciding it is undecidable in general, so k-rust neither checks nor derives it, and a false attribute makes the definition inconsistent on the inputs where it is false; any verdict about those inputs then follows from the definition as written.
When evaluation observes the contradiction, an equation of such a symbol whose result, on arguments that were defined when it fired, simplifies to `\bottom` (a builtin's undefined result such as `10 /Int 0`, or a set or map with a repeated element or key), k-rust names it and changes nothing else:
`krun` follows its no-successor warning with ``warning: the `total` attribute of <K label> is contradicted on this input: its equation <label or id> at <file:line:column> reduces <application> to bottom (undefined at <term>); ...``, `kprove` prints the same line under the failed claim's `Vacuous` or `Trivial` leaf; the symbol is named by the K label its KORE name encodes (`tDiv(_)_M_Int_Int`, or the name a `symbol(...)` attribute gives), while the application and the undefined term are printed as KORE, and the backend's execution leaves carry it as `contradictedTotal` (`ExecutionLeaf.contradicted_total`, `HaltReason::Trivial`/`Vacuous`, `ProofLeaf.contradicted_total`).
The innermost such equation is named; an argument that is already `\bottom` before the equation fires names none.
A contradiction that evaluation does not observe, such as the symbolic `tAdd(SetItem(1), I)` of [Set concatenation is nilpotent](#set-concatenation-is-nilpotent), is not reported, and the kore-rpc protocol, which has no field for it, is unchanged.
The `a_contradicted_total_attribute_is_named_without_changing_the_outcome` CLI test and `a_ground_undefined_step_through_a_total_function_names_the_contradicted_attribute` in [undefined_step_coverage.rs](../crates/k-rust/tests/undefined_step_coverage.rs) cover this.

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
A `rule-substitution` binds the applied rule's variables, which k-rust prints with their escaped `Rule#` marker (`Rule-hX`, see [variable names](#variable-names)) so that the predicate keeps them apart from state variables of the same name; the gate compares a rule variable by its name in the definition, whatever marker spelling an engine prints (N40).
Only a request variable spelled like that escape, such as one named `Rule-hX`, prints like a rule variable; when a variable of the request, of the next state or of a bound value does, the rule variable is renamed apart to `Rule#X!apart{N}` (`Rule-hX-bapart0`), whose rule name is still the part before the `!` (`project_rule_substitution` in [rpc.rs](../crates/k-rust/src/rpc.rs)).
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
Such an instance is shown when the antecedent's term contains no conjunction of terms, its constraints, the negated obligations where required, and the term's definedness are true syntactically or satisfiable by a solver query whose translation is exact (`smt::translation_exactness`), and every free variable has a sort the definition shows inhabited.
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

### Sort injections at load

`inj{A, B}` denotes the embedding of `A` in `B` licensed by a chain of declared subsort axioms; a closed pair outside that order denotes no licensed value.
The backend therefore checks sort injections when it loads a definition or an added module.
An axiom that writes an unlicensed closed injection in a rewrite or equation right-hand side, an `ensures` clause, or a `requires` clause outside a membership's pattern operand is refused with `UnlicensedInjection`, naming the source sort, target sort and axiom.
An unlicensed injection in a matched position makes that alternative dead: rewrite left-hand alternatives, simplification left-hand sides, function argument binder alternatives and ceil arguments containing one are not loaded.
No licensed value can match such an alternative, and dropping it also prevents unification from binding a variable to an unlicensed value.
Within an axiom's condition (outside a predicate simplification's left-hand side, where the axiom is dead), membership `\in(X, P)` is false when its pattern operand `P` contains an unlicensed closed injection, because no licensed value belongs to that pattern.
A sort-variable pair is accepted inside a definition axiom as a schema, including the injection composition axiom whose licensed instances follow from transitivity.

Requests and claims must contain only licensed injections; krun's initial configuration is checked like a request.
Requests and claims also refuse injection pairs containing sort variables.
An unlicensed alternative of a no-junk axiom prevents that axiom from establishing a finite domain.
A dead axiom remains in the written rule catalog with its executable attribute, but contributes no loaded rule and cannot be selected in an observation allowlist (`UnknownRule`).
These load checks license closed injection pairs in loaded patterns, and rewriting preserves that condition by substituting licensed values and composing licensed embeddings.
Instances of sort-parametric axioms remain the residual: they are not checked closed at load.
Applicable instances arise only from the injection composition schema, whose instances are licensed by transitivity; sort-parametric equations do not match closed subjects.

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

The order is over closed sorts: `subsort{SortMInt{Sort8{}}, SortKResult{}}` places `MInt{8}` below `KResult` and says nothing about `MInt{16}`.
No pair is derived from a sort's arguments: `A <= B` does not place `S{A}` below `S{B}`, because no axiom makes a sort constructor monotone.
A sort that mentions a sort variable is below another only if every instance is; the backend answers no when no instance of its head is below the other's head, and otherwise reports the variable.
A collection sort (one with `unit`, `element` and `concat` attributes) has no sort parameters, because those attributes name one symbol each and so describe one sort.
Such a declaration with parameters is rejected at load.

The [definition fixture index](../crates/k-rust/tests/fixtures/reference/definition/index.toml) records pinned verification outcomes and diagnostic fragments.

## Search results

Search output uses deterministic structural KORE order; reproducing Kore's internal `MultiOr` ordering is not a compatibility requirement.
The order is `k-rust-kore`'s `Pattern` order (variant declaration rank, then fields in declaration order, byte-wise strings) and may change between releases.
Differential gates compare disjunctions as multisets so ordering is ignored while multiplicity is still checked.
For `--bound N`, selected results must be distinct members of the same query's unbounded solution set, up to the bound; which members are selected is unspecified.
The CLI test `krun_search_bound_returns_a_subset_of_the_unbounded_solutions` checks this property against the port's own unbounded search.
A state, a solution (a match of the target), and a leaf of a state-set execution is reported once up to the names of the variables the request does not name.
Such a variable is quantified over its own result (see [Result variables](#result-variables)), so two results that differ only by an injective renaming of those variables, with the request's names fixed, denote the same configurations or the same instances of the target; reporting both would take a `--bound` slot from a different result.
The comparison (`RequestNames::state_key` and `RequestNames::solution_key` in [fresh.rs](../crates/k-rust-backend/src/fresh.rs)) renames those variables by first occurrence and compares the constraints as a set.
Map and set elements and the constraints are visited in the order of a label that sees a renamed variable only through its kind, its sort and the number it already has, so elements that differ only in such names wait until the numbers their variables receive elsewhere (a list, a cell) tell them apart.
Where nothing tells them apart, the comparison tries each variable of the first such group as the next one numbered, skipping one whose exchange with a tried one leaves the result unchanged, and keeps the least renamed result, so every renaming of a result gets one key.
That search stops after 32 complete numberings; the rest of the numbering then follows stored order, which compares names, so two renamings of one such result can both be reported.
Two different results are never merged.
Which successor `--strategy any` follows among equal-priority rules is likewise unspecified; the differential gate checks that the port's any-strategy result is a member of the reference all-strategy set (N26).
The port follows the first applicable rule in priority order, then `definition.kore` declaration order (main module first, imports depth-first in their written order); which rule the reference follows is engine-internal.
Among several collection matches of that rule, the port follows the first candidate in deterministic structural order; which candidate the reference follows is engine-internal.
The RPC `next-states` array is a set of successors and is compared as a multiset (N27).
A search given no target pattern matches every reached configuration against one variable, spelled `VarResult` as reference krun spells its target, and reports each match as a binding of that variable.
That variable belongs to the request, so when a variable of the initial pattern is already spelled `VarResult` (for example the K variable `Result`), the target is `VarResult0`, or the next `VarResultN` no initial variable spells: sharing the name would identify the two variables in the match, or print one name at two sorts.

A depth-bounded execution result covers every path of every input instance up to the bound, so a configuration reached at the bound is a result whatever other branches did; the port keeps such a leaf when another branch halted, where the reference graph traversal drops it.
Normalization N17 limits the corresponding differential exception to marked depth-bounded cases and requires the reference leaves to remain a sub-multiset of the Rust leaves.
[Execution fixtures](../crates/k-rust/tests/fixtures/reference/execution) and the symbolic differential cover branch sets and depth cuts.

## Execution results

### Variable names

k-rust keeps a variable name read from KORE verbatim, and accepts only a KORE identifier there: `[A-Za-z][A-Za-z0-9'-]*` for an element variable, `@` followed by one for a set variable.
The textual and JSON readers cannot spell anything else; binary KORE and patterns handed over in process can, and the backend refuses such a name with `DefinitionError::VariableName`.
Every name the backend makes from another one adds a `#` provenance marker (`Rule#`, `Eq#`, `Ex#`) or a `!` counter (`X!0`, `X!apart1`, `X!binder0`), so no name read from a request or a definition is ever a rule variable or a mint of the backend, whatever it is spelled.

A name that is a KORE identifier prints unchanged.
Any other name is escaped, with `-` as the only escape character:

| Internal character | Printed form |
| --- | --- |
| letters, digits, `'`, a leading `@` | unchanged |
| `-` | `--` |
| `#` | `-h` |
| `!` | `-b` |
| `@` after the first position | `-a` |
| any other character | `-u`, its code point in lowercase hexadecimal, and `-` |

For example, `Ex#Frame!0` prints as `Ex-hFrame-b0`, `X!apart1` as `X-bapart1`, and `@Rule#M` as `@Rule-hM`.
The escape is injective, so two names the backend made never print alike, and two names read from KORE never do either.
A name read from KORE and an escaped name print alike only when the former is spelled like the escape of the latter, such as a query variable named `Ex-hFrame-b0` next to the mint `Ex#Frame!0`.
k-rust keeps such a pair out of every response: the names a rewrite mints skip every spelling of the request, and a printed binder whose spelling is the spelling of another variable free in its body is renamed to a `!binder` name (`apart_binders` in [externalize.rs](../crates/k-rust-backend/src/externalize.rs)), so the printed pattern binds what the internal one binds.
An RPC `rule-substitution`, a predicate that equates rule variables with terms over the state's variables, renames a rule variable apart when a variable it can be equated with prints like it (see [RPC behavior](#rpc-behavior)); the host API's observation `bindings` keep each rule variable in a field of its own, apart from the value's variables.

An implication check renames each existential `X` of the consequent to a local name `X!exists{N}`, spelled like no variable of either side.
Its condition prints that name as `X`, the consequent's own binder, unless a free variable of either side or a leading existential of the antecedent is also named `X`: that is another variable the condition can mention, so the binding then keeps the escaped local name, such as `X-bexists0` (`ImplicationSides` in [implication.rs](../crates/k-rust/src/backend/implication.rs)).

Reading a printed result back gives the internal pattern up to a renaming of its escaped names into names of the new request: `Ex-hFrame-b0` is read as a variable of that name, not as the mint `Ex#Frame!0`.
That renaming is a bijection and the identity on the names the request already had, so identity decisions within one response, and across requests on the request's own names, are unaffected.
`term::names::decode_variable_name` inverts the escape for tools that classify printed names.
The contract is versioned by `term::names::VARIABLE_IDENTITY`, which is 3 since names are read verbatim; versions 1 and 2 decoded `-h` and `-b` back into the markers on reading, and its documentation in [names.rs](../crates/k-rust-backend/src/term/names.rs) states what each version promises.

Printing a mint under the spelling of a query variable would identify two variables: map-selection narrowing mints `Ex#Frame!0`, and printed as `ExFrame0` next to a query frame named `ExFrame0`, a leaf stated `ExFrame0 = mapConcat(mapItem(ExKEY1,ExVALUE2), ExFrame0)` about what are two different variables.
The escaped spelling of generated names therefore differs from the spelling the reference engines print (normalizations N4 and C7), and pattern digests, which hash the printed KORE, change with it.

### Result variables

An execution or search result is a disjunction; each disjunct denotes the configurations one branch reaches, for a valuation of the initial pattern's free variables.
Those variables are the only names a result shares with the query.
Any other variable free in a disjunct is read as existentially quantified over that disjunct alone: it names a value the rewrite introduced, such as a `?` variable, which K quantifies existentially at the top of a rewrite rule's right-hand side (`docs/user_manual.md:2443-2444`), a rule variable the match left unbound, or a collection frame.
k-rust prints a disjunct as its term conjoined with its constraints and leaves these binders implicit (`constrained_pattern` in [externalize.rs](../crates/k-rust-backend/src/externalize.rs)).
Every variable a rewrite introduces receives the `Ex#` marker and a `!N` suffix from one counter for the request (`FreshCounter` in [fresh.rs](../crates/k-rust-backend/src/fresh.rs)): a right-hand-side existential `Var'Ques'X` prints as `Ex-hVar'Ques'X-bN`, a rule variable the left-hand side does not bind, `X`, prints as `Ex-hX-bN`, and so does a narrowed rule variable or collection frame.
The counter grows through the whole request and skips every spelling of the request's variables, free or bound, so one name denotes one variable along a path and across the response: reusing a name after its previous variable left the state would identify the values of two rule applications.
A request is an execution or search with its initial patterns and target, or a proof with the proved claim and every circularity and trusted lemma; a claim variable a proof renames to apply a claim (`!claim`) takes its counter from the same request counter.
The spellings are those of the patterns as the client sent them: a search target may apply an alias that ignores an argument, whose variables then do not occur in the internalized target, and the facades, the CLI, and the RPC server pass the spellings of the received patterns to the operation (`RequestNames::of_received`, `ExecutionOptions::request_names`, `SearchOptions::request_names`).

A remainder disjunct, the branch on which a rule does not apply, carries the negated applicability condition `\not(\exists V. C)`, where `V` are the variables of `C` that are free in neither the state's term nor its constraints (`quantify_introduced_variables` in [predicates.rs](../crates/k-rust-backend/src/rewrite/predicates.rs)).
The applicability condition includes a `requires` Boolean term's definedness at instantiation, so an undefined `requires` instance belongs to the remainder; the [symbolic definedness tests](../crates/k-rust/tests/symbolic_definedness.rs) exercise this split with and without Z3.
A carried right-hand-side definedness obligation or an `ensures` can instead exclude an instance without producing a leaf; the same tests cover the obligations retained on surviving leaves.
A rule's variables are universally quantified over the rule (`docs/user_manual.md:2448-2450`), so the remainder must exclude every instance of the rule: a variable of the match that occurs nowhere else in the disjunct is bound inside the negation.
Reading it at the disjunct level instead would say only that some instance does not apply (`\exists x. \not C` rather than `\not \exists x. C`), which is a different set of configurations.

Under this reading three normalizations of [the register](../scripts/reference-normalisations.toml) are equivalences rather than tolerances:

- N4 renames the result variables that are not free in the initial pattern bijectively, sort-preservingly, and per disjunct; that is renaming bound variables, while the initial pattern's variables are compared by name. This holds when the gate supplies the initial pattern (`K_DIFFERENTIAL_INITIAL_PATTERN`, set by the symbolic and MIR execution gates); without it, N4 selects the variables to rename by generated-name shape, compares every other variable by name, and does not check that no initial-pattern variable has such a shape.
- N16 drops the outer `\exists` binders of a disjunct that bind generated variables (not free in the initial pattern; by the N4 name shapes when no initial pattern is given), which denotes the same disjunct as its body; it stops at a binder of an initial-pattern variable, which is kept and compared. k-rust prints no such prefix.
- N22 adds, inside a negated existential, the binder of a generated variable that is free there and occurs nowhere else in the disjunct, which is where the reading above places it; k-rust already prints that binder, while the pinned Kore prints the unification's collection frame free in that position.

### Unbound equation variables

An equation (a function, simplification, ceil or predicate equation) is an axiom closed over all its variables: `l = r requires R ensures E` states `l = r` for every value of every variable that satisfies `R` and `E`.
A variable `Y` of `r` or `E` that `l` does not bind is not fixed by matching `l`.
Such an equation can be consistent and meaningful: `f(X) = Y requires Y = X + 1` says `f(X) = X + 1`.
But the evaluator has no witness for `Y`, and the instance of `r` with the equation's own `Y` left free would name no value of the request.
Minting a new variable at each application would not model the equation either, since it would make `f() = f()` false for `f() = Y`.

The definition is loaded, and the backend records these variables per equation.
An instance of such an equation is never used.
Its `requires` is decided with the variables free, as for any equation: refuted, it holds for no value of them, and the equation says nothing about the subject.
Otherwise the attempt is indeterminate (`ConditionIndeterminacy::UnboundResultVariables`, wire kind `unbound-result-variables`, naming the variables as the definition spells them).
When no other equation rewrites the subject, the attempt is reported as an `UndecidedCondition` diagnostic of the equation with that reason and the decided `requires`, so a simplification that leaves the application unevaluated says why; `krust krun` prints it as a warning naming the variables as the K source writes them.
A subject that another equation evaluates (one of the same priority, or a lower-priority simplification) has nothing to explain, and the attempt is not reported.
Nor is one made while the condition of an enclosing equation attempt was simplified, when that attempt was refuted or superseded: the subject was then part of a condition the result does not depend on.
That is the same outcome as an equation whose `requires` is open: the subject is kept, and a function's lower-priority and `owise` equations do not apply in its place, while a simplification is passed over.
The static definedness analysis does not use such a ceil equation.

A variable that occurs only in an equation's `requires` never reaches a result.
It is decided with the rest of the `requires`: the `requires` holds only if it holds for every value of the variable, and it is refuted only if it holds for none.
In the predicates of an `UndecidedCondition` diagnostic, such a variable keeps the equation's marker and prints escaped (`Eq-hVarY`, or `Eq-hVarY-bapartN` when it was renamed apart from the subject or from a request variable spelled like it); the wire form lists each one in `ruleVariables` with the name the definition gives it (`definitionName`, here `VarY`).
Such a variable can also reach the subject of another equation while the `requires` is simplified; there it is a variable of that subject, and a diagnostic of the other equation does not list it.
Kompile accepts a function or simplification rule whose right-hand-side variable occurs in its `requires` or is listed in `unboundVariables`; the backend loads it as above.
Rewrite rules are not equations: a variable that the left-hand side of a rewrite rule does not bind is minted per application (see [Result variables](#result-variables)).

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
A `Trivial` leaf of a step is the set of instances on which the step is undefined: some rule applies, its result is empty there because its `ensures` or the definedness of its right-hand side fails, and no applied rule of the same priority gives them a defined result.
This covers a condition the step could not decide as well as a refuted one, so a symbolic claim is never proven while one of its instances fails: `apart(X, Y) => halt` under `rule apart(A, B) => halt ensures A =/=Int B` fails like its instance `apart(0, 0) => halt`.
The leaf is dropped only when its constraint is refuted, for example when `ensures ?X >Int 0` always has a witness.
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
N34 applies only to the reference side of the semantic KORE compile comparison: it drops the injectivity and pairwise no-confusion axioms that mention an overload-greater the port declares `anywhere` and states none of those axioms for, the two conditions [Anywhere rules](#anywhere-rules) states; the no-junk axiom and every axiom that mentions no such symbol stay compared, and a port that states one of those axioms for the symbol leaves the reference untouched.
N36 applies to semantic and syntax KORE compile comparisons: it drops the reference's `functional` and the symbol's functional axiom when both declarations carry the same anywhere or macro-like attribute and the port withholds both claims, the evidence-based totality contract [Anywhere rules](#anywhere-rules) states.
For those matching value productions it drops `value-production{}()` and any extra `function{}()` on the k-rust side, accepting both the Rust target's marked function and the LLVM target's marked value declaration and printing separate counts for both attributes and the withheld functional declarations.
A source function's `function{}()` and every unrelated attribute or axiom stay compared.
Every other attribute and axiom stays compared, and a declaration without the matching equation-head marker is ineligible.
N38 applies only to reference-tool verification of the k-rust LLVM-target definition (the kore/llvm compile pairing, and the conformance driver's `kore-verify` step of a `--backend llvm` recipe): it adds `function{}()` to exactly the declarations carrying `value-production{}()` in a separate verification copy, counts the changed declarations, and refuses any marked declaration that already carries `function` or `functional`.
The verifier requires a function or functional equation head; the external LLVM backend must instead receive the original declaration so that an irreducible value-production application remains a value, the per-target contract [Anywhere rules](#anywhere-rules) states.
The Rust/Haskell pairing verifies the original definition without this normalization.
N35 applies only to the reference side of the semantic and syntax KORE compile comparisons, after N32: it drops the sort predicate of a sort without a `subsort{S,KItem}` axiom, with its functional axiom and its then unconditional `owise` false equation, when the port declares no symbol of that name and no other sentence or attribute mentions it, the divergence [the sort-placement contract](#sorts-of-compiled-terms) states.
A predicate the port declares, a remaining true equation, and any use of the predicate stay compared; the comparison prints the number of predicates dropped.
The pinned WASM semantics, whose main closure declares `syntax #Layout [token]`, is the case it covers.
N39 applies only to reference parsed definitions: it removes `total` from configuration-generated symbols whose evidence is established during compilation.
A cell-map key projection is identified through the local `MAP.concat` cell collection, its `wrapElement` cell production, the cell's first key field, and the projection's exact generated signature.
A nullary initializer is identified through the configuration that generates it: a local cell production (with `cell` and `cellName` attributes, label `<name>`, the cell sort, and opening and closing cell terminals) determines the initializer label `init<CellSort>` and its result sort, which is the cell sort, or for `multiplicity="*"` the local cell-collection sort whose `cellCollection` production wraps that cell with the matching `concat` hook; the production must also carry the `initializer` marker, the `function` attribute, and the exact nullary signature.
The parsed artifact precedes compilation's `SoleGenerator` judgement for projections and its judgement of all initializer equations with the complete main-module equations and a least fixed point over child initializers.
The normalization requires each corresponding k-rust parsed production to differ only by lacking `total` and the sibling `definition.kore` to declare exactly one matching symbol with the same argument/result signature and `total{}()`.
It refuses per symbol if the parsed claim is already present, another parsed difference exists, or the final totality claim is absent; a genuinely partial initializer therefore refuses normalization, and an already present parsed claim on a projection requires removing N39.
A source-written nullary `[initializer, function, total]` production that no local cell generates is not recognised and stays compared unchanged; a recognised initializer whose k-rust parsed counterpart already carries `total` refuses with a message saying that it may be source-written. After rewriting, each module's sentences are sorted and deduplicated, so a module that held a production both with and without `total` keeps one copy.
It prints the number of removed attributes; every other parsed attribute and production remains compared, and the semantic KORE comparison still compares the final totality claim.
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

## Undefined steps in proofs

A step is undefined on a configuration when a rule applies to it but has an empty result there, and no rule of the same priority gives it a defined result.
The rule applies: it matches and its `requires` holds.
The result is empty because its `ensures` fails, or because its right-hand side is undefined, for example a partial function such as `/Int` by zero, or a `Set` or `Map` concatenation whose operands share an element or key ([Set concatenation is nilpotent](#set-concatenation-is-nilpotent), [Map concatenation binds each key once](#map-concatenation-binds-each-key-once)).
Such a configuration is not stuck, because the applying rule also shuts out the lower priorities.
It is not empty either: it exists, and the path to it is real.
It simply has no successor.

A claim `φ => ψ` states something about every configuration of `φ`.
A configuration of `φ` whose path reaches an undefined step outside `ψ` never reaches `ψ`, so under both the one-path and the all-path reading the claim is false for that configuration.
k-rust therefore reports the step's undefined instances as a `Trivial` leaf.
This holds whether the step decided the condition or only carried it symbolically.
The leaf's constraint is the condition under which the step is undefined, restricted by every applied sibling rule of the same priority.
The leaf is dropped only when that constraint is shown unsatisfiable, and otherwise it makes the claim `failed`.
`--allow-vacuous` accepts such leaves, like the other empty branches.

The other reading takes the rule as an axiom: `σ(l ∧ R) → •(r ∧ E)`, with an empty result for `σ`, makes `σ` itself impossible.
The branch then counts as vacuous, and its configurations are dropped as if they did not exist.
For a functional left-hand side that axiom is false: the configuration can be written down, and it reaches the rule by defined steps.
So pruning it proves claims that have false instances, and a rule's wrong `ensures` then vanishes silently instead of showing up as a failing configuration.
It also makes a symbolic claim hold while one of its ground instances fails.
The `reference-prunes-undefined-step` category records conformance cases where the reference toolchain proves a claim only in that way.

In `set_unification` (`a-spec.k`, claim #1), the claim is `<k> start(I) => end ...</k> <set>... (.Set => SetItem(I +Int 1) ?_:Set) ...</set>`.
Its only step is `<set>... .Set => SetItem(I) ...</set>`, which rewrites the set cell `S` to `S SetItem(I)`.
`Set` concatenation of sets with a common element is undefined ([`domains.md`](https://github.com/runtimeverification/k/blob/4a46d1231473b599c699160132fd6e76a5c46406/k-distribution/include/kframework/builtin/domains.md), "Set concatenation").
So on every configuration whose set already contains `I`, the step is undefined, for example `start(1)` with the set `SetItem(1)`.
Such a configuration never reaches `end`, so the claim does not hold for it.
k-rust reports `failed` with a `Trivial` leaf under `I in S`, and proves the claim with `--allow-vacuous`.
The ground instance fails in the same way: the claim `<k> start(1) => end ...</k> <set> SetItem(1) (.Set => SetItem(2) ?_:Set) </set>` has the undefined step `SetItem(1) SetItem(1)` and is `failed`, because concrete concatenation is nilpotent too.

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
