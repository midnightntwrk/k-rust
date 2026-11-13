# KORE in K

`kore.k` is a K definition whose configuration holds an encoded KORE object definition and an encoded initial term, and whose rules compute every configuration reachable from that term to which no rule of the object definition applies: the final configurations that `krun --search` returns.
Its job is to be mutated.
Each mutant of `kore.k` is a wrong reading of KORE, and a set of cases that kills the mutants is a set of small object definitions that tell those readings apart.
The cases are an external test suite for any implementation of KORE's semantics.

The expected result of each case comes from the reference backends run on the object definition itself, never from `kore.k`; `kore.k`'s result is only checked against it.

`kore.k` is written in K, not KRS; [Why K and not KRS](#why-k-and-not-krs) gives the reason and what a KRS port takes.

## The reading of KORE

`kore.k`'s header states the reading it implements; in short:

- a function application is evaluated innermost: arguments first; an undefined argument (`\bottom`) makes the application undefined; a constructor application is a value;
- an equation applies when its argument patterns match and its `requires` evaluates to `true`; among the applicable equations one of the least priority gives the result (`[owise]` is priority 200, no attribute is 50); an application no equation applies to stays as it is;
- a rewrite rule applies when its left side matches and its `requires` evaluates to `true`; the successors are the defined results of the applicable rules of the least priority; a rule whose result is undefined still blocks the rules of larger priority;
- a configuration is final when no rule applies to it; one to which rules apply, all with undefined results, has no successor and is not final;
- matching is syntactic up to injections: `inj{A,B}(P)` matches `inj{C,B}(V)` when `C = A` (`P` against `V`) or `C < A` in the reflexive-transitive closure of the stated subsorts (`P` against `inj{C,A}(V)`); a variable seen twice must be bound to equal values; an as-pattern `\and(P, V)` matches what `P` matches and binds `V` to it; `inj{A,B}(inj{C,A}(V))` is `inj{C,B}(V)`;
- hooks are strict: an undefined operand makes the operation undefined; `/Int` and `%Int` are undefined on a zero divisor.

### The fragment

Covered: sorts, subsorts and injections, constructors, as-patterns, non-linear left sides, function equations with priorities, `requires` and `[owise]`, rewrite rules with priorities, `requires` and `[owise]`, the hooks `+Int -Int *Int /Int %Int <Int <=Int >Int >=Int ==Int =/=Int andBool orBool notBool #if_#then_#else_#fi`, and undefinedness propagating strictly.

Not covered: collections (`Map`, `Set`, `List`) and their hooks, and therefore AC matching with frame variables and cell collections; any hook outside the list above; `ensures`; configurations of more than one cell (an object definition has the one cell `<k> $PGM:S </k>`); symbolic terms (an initial term is ground); conditions on results.

## Layout

| Path | Content |
| --- | --- |
| `kore.k` | The interpreter: module `KORE`, syntax module `KORE-SYNTAX`; 313 lines, 141 rules and equations (11 rewrite rules for the search, the rest equations of 44 functions). |

## Why K and not KRS

The other packages of `krs/semantics` are KRS crates whose K is emitted by `krs`.
`kore.k` stays K source because a port is not small, although every construct it uses has a KRS spelling (constructor enums with `#[k::syntax]` templates, `k::equations!` tables with `#[k::equation(owise)]` and `#[k::equation(priority = N)]`, `k::rules!` over a one-cell configuration, `kequal` guards):

- The definition: its 15 sorts as constructor enums whose syntax templates must reproduce exactly the program syntax the committed `kore.pgm` files are written in (`pgm(def(…), …)`, `T ; Ts`, `.Ts`, `bot`); the 130 equations of 44 functions as equation tables; the 11 rewrite rules of the search in `k::rules!`.
  Each sentence is judged by KRS's checks on the assembled definition (overlapping equations, catch-all rows that need `owise`, complementary guards of rules), which `kore.k` has never been put through; whatever they refuse is a change of the definition to be argued, not a transcription.
- The corpus: `krs kink` reads a corpus in its own layout, `kink/` beside the crate's `Cargo.toml`: `kink/FLOW.toml` naming the package (`[spec] krs = { package = …, definition = … }`), the cases as program files that bind the `#[k::init]` parameter, `kink/mutations/<topic>.toml`, and a committed `kink/definition.k`.
  The emitted K has KRS's module names, rule labels and spelling of each rule, so all 38 mutations are re-anchored (each edit's `rule` and `find`), the three argued obligations renamed, and the coverage and kill numbers re-measured.
- The evidence that the port is the same definition: `krs run` of every case's `kore.pgm` gives the result `kore.k` gives, and the kill matrix is the same up to the renaming of mutations' anchors.

By the size of the existing ports (the KWasm slice is 294 lines of Rust for 16 sentences), that is on the order of a thousand lines of Rust and a re-authored mutation list, a unit of its own.
A half port, part of the definition in KRS and part in K, would leave two definitions of one reading; it is not done.

## Status

Done: the definition.
Next: the encoder and the cases with their reference results, the kink corpus, and the command that reruns the cases.
