# KORE in K

`kore.k` is a K definition whose configuration holds an encoded KORE object definition and an encoded initial term, and whose rules compute every configuration reachable from that term to which no rule of the object definition applies: the final configurations that `krun --search` returns.
Its job is to be mutated.
Each mutant of `kore.k` is a wrong reading of KORE, and a set of cases that kills the mutants is a set of small object definitions that tell those readings apart.
The cases are an external test suite for any implementation of KORE's semantics.

The expected result of each case is its ruling, derived from the K and KORE texts and written by hand in the case's `entry.toml`, with the sentences it rests on quoted by file and line (`SCHEMA.md`); where the text does not settle a point, the case is unsettled and names one reading per answer. Every implementation, the reference backends and `kore.k` itself among them, is evidence checked against the ruling: a result that is not the ruling, or no reading, is recorded with its reason, and is no failure.

`kore.k` is written in K, not KRS; [Why K and not KRS](#why-k-and-not-krs) gives the reason and what a KRS port takes.

## The reading of KORE

`kore.k`'s header states the reading it implements; in short:

- a function application is evaluated innermost: arguments first; an undefined argument (`\bottom`) makes the application undefined; a constructor application is a value;
- an equation applies when its argument patterns match and its `requires` evaluates to `true`; among the applicable equations one of the least priority gives the result (`[owise]` is priority 200, no attribute is 50); an application no equation applies to is given no value (`bot`): the text leaves such a point open (the unsettled entry `kk:t13-fn-no-equation`), and `kore.k` computes its reading `closure-none`; where a hook's text states no value, `op-undef` gives none (for two sets with a common element, the settled entry `kk:t35-set-concat-overlap`), and where it leaves a point open, `op-undef` gives no value too, a reading of that point's entry;
- a rewrite rule applies when its left side matches and its `requires` evaluates to `true`; the successors are the defined results of the applicable rules of the least priority; a rule whose result is undefined still blocks the rules of larger priority;
- equations and rules are tried by ascending priority, the equations of one priority in the order of the text: an equation (a rule) of a larger priority applies only where none of a smaller priority does, so its `requires` and right side are evaluated only there, and one without a value (a `requires` whose evaluation does not terminate, an undefined right side) does not affect a result decided at a smaller priority (c45, c46, c48);
- a configuration is final when no rule applies to it; one to which rules apply, all with undefined results, has no successor and is not final;
- a rule's `ensures` is part of its result: `r ensures E` is `r` where `E` evaluates to `true` and undefined otherwise, so a rule whose `ensures` is false has applied with an empty result and blocks the rules of larger priority: the K manual ("Rule Structure") gives a rule's transition the result `RHS #And ENS` and says that an `ensures` that makes it undefined does not stop the rule from applying (`kk:t05-rule-ensures-result`; c43, c44). The axiom kompile writes for `l => r requires P ensures E` is `\rewrites(\and(l, P = true), \and(r, E = true))`, whose successor is empty where `E` is false;
- an equation's `ensures` is part of its right side in the same way: kompile writes `f(p) = r ensures E` as `f(p) = \and(r, E = true)`, the `ensures` on the right of the equality, so where the equation applies and `E` is not true the application has no value; the `ensures` does not decide whether the equation applies, so an equation of larger priority or an `[owise]` one does not apply there (the premise kompile writes for an `[owise]` equation negates the other equations' argument patterns and `requires`, not their `ensures`). The encoder writes the right side as `en(r, E)`, as for a rule, and `ev-en` evaluates it (c50, c51);
- a function declared `total` is evaluated as any other: where no equation applies its application has no value, so a `requires` that is such an application does not hold; kompile states that a `total` function has a value there, so at such a point `kore.k` computes none of the readings of the unsettled entry `kk:t14-total-no-equation` (`value-true`, `value-false`, `rest`) and its result is outside what the text admits (c42 records the backends' answers);
- matching is syntactic up to injections: `inj{A,B}(P)` matches `inj{C,B}(V)` when `C = A` (`P` against `V`) or `C < A` in the reflexive-transitive closure of the stated subsorts (`P` against `inj{C,A}(V)`); a variable seen twice must be bound to equal values; an as-pattern `\and(P, V)` matches what `P` matches and binds `V` to it; `inj{A,B}(inj{C,A}(V))` is `inj{C,B}(V)`;
- hooks are strict: an undefined operand makes the operation undefined; `/Int` and `%Int` are undefined on a zero divisor;
- `==K` and `=/=K` compare two values, and equal values are equal terms, since a value's injections are composed and its collections are canonical (K's `KEQUAL` module declares `_==K_` a total function hooked `KEQUAL.eq`, and `domains.md` calls it the equality between two terms: `kk:t32-keq-ite`, `kk:c37-keq`); `==K` is a function of its two arguments, so an undefined operand makes it undefined;
- a domain value of `String` is a value of that sort, its text; `==String` is the equality of texts, `<String` their lexicographic order and `==Bool` the equality of Bool values (the three operations `kore.k` itself uses beside those of `Int`, so that `kore.k` can read its own definition);
- a domain value of a token sort is a value of that sort; a sort predicate `isS` is an ordinary function whose equations kompile writes (`isS(inj{S,KItem}(X)) = true`, `[owise]` false), so it holds of a value of `S` or of a sort below `S` by matching through injections;
- a `Map` is a finite map, a `Set` a finite set, a `List` a finite sequence, and a value of each is canonical (a map's entries ordered by key, a set's elements by value, no key or element twice), so that equal collections are equal terms; `_Map_` and `_Set_` are partial, defined on disjoint maps (sets) and undefined where keys (elements) overlap; `_List_` is total, associative and not commutative; a lookup of a missing key is undefined; a collection is strict in its elements;
- a collection pattern of element patterns and at most one frame variable matches every split of its subject: for `Map` and `Set` each element pattern takes any element, for `List` the element at its position, and the frame the rest; matching gives a set of substitutions, a rewrite rule gives one result for each substitution whose `requires` holds, and an equation the result of the first such substitution (on a consistent definition every such substitution gives the same result);
- a configuration is a term like any other: a cell is an application of its constructor, and a cell collection (`multiplicity="*"`, `type="Map"`) is a `Map` from its key cell to its instances, since kompile gives its sort the `MAP.concat`, `MAP.unit` and `MAP.element` hooks; so an instance is found by its key, the instances a rule does not mention are its frame, and two instances of one key are a concatenation of maps with a common key, which K's `MAP` module states to be `#False`, so undefined.

### The fragment

Covered: sorts, subsorts and injections, constructors, as-patterns, non-linear left sides, function equations with priorities, `requires` and `[owise]`, rewrite rules with priorities, `requires` and `[owise]`, the hooks `+Int -Int *Int /Int %Int <Int <=Int >Int >=Int ==Int =/=Int andBool orBool notBool ==Bool #if_#then_#else_#fi ==K =/=K ==String <String` with domain values of `String`, and undefinedness propagating strictly.
`ensures` on rewrite rules and on function equations; functions declared `total`.
Token sorts (`syntax Id ::= r"…" [token]`) and their literals; the sort predicates `isS` with the equations kompile generates for them; as-patterns written with `#as`, beside the ones kompile writes for literals in left sides.
Configurations: one cell `<k>`, or several cells under a top cell, with cell collections of `type="Map"`.
Collections: the sorts `Map`, `Set` and `List` with their concatenation, unit and element symbols (in terms and in patterns, with a frame variable), and the hooks `Map:lookup`, `Map:lookupOrDefault`, `Map:update`, `_[_<-undef]`, `_in_keys(_)`, `size(Map)`, `Set:in`, `size(Set)`, `|Set` and `size(List)`.

Not covered: the other collection hooks (`keys`, `values`, `choice`, `-Map`, `-Set`, `intersectSet`, `List:get`, `List:set`, `range` and the rest); a `Map` or `Set` pattern with more than one frame; cell collections of `type="Set"` or `type="List"`, cells of multiplicity `?`, and a `<k>` cell holding more than one item; any hook outside the lists above; symbolic terms (an initial term is ground); conditions on results (`kore.k`'s results carry none: where the haskell backend keeps a result under a condition such as `\ceil(half(3))` in c11, `kore.k` reads the application as having no value); a `total` function that no equation applies to (c42), whose value the definition leaves open; projections such as `{M[K]}:>Int`, whose equations kompile writes in K's own modules (a case keeps a lookup's result in `KItem`); the other `String` hooks (`+String`, `lengthString`, `substrString`, …) and the other equality hooks (`=/=Bool`, `=/=String`, …).
The encoder stops with an error naming the construct when it meets one outside the fragment that it recognizes: a hook outside the list, a domain value of a sort that is not `Int`, `Bool`, `String` or a token sort, a function declared outside the object definition that kompile did not generate for it, a matching-logic connective in a term, a rule or an equation with a variable its left side does not bind (in its `requires`, its `ensures` or its right side), a right side under `\exists`, a `requires` or an `ensures` that is not a term equal to `true`, an axiom marked `simplification` or `non-executable`, a symbol marked `macro`, `macro-rec`, `alias`, `alias-rec`, `anywhere` or `symbol-overload`, any attribute of a selected axiom or an applied symbol that it neither reads nor ignores with a stated reason (`COVERAGE.toml`), a configuration of another shape, an initializer that is not one equation of variable arguments, a `Map` or `Set` pattern with two frames.

## Layout

| Path | Content |
| --- | --- |
| `kore.k` | The interpreter: module `KORE`, syntax module `KORE-SYNTAX`; 559 lines, 249 rules and equations (11 rewrite rules for the search, the rest equations of 72 functions). |
| `tools/korek.py` | The KORE text reader; the encoder of kompile's `definition.kore` and the initial term's KORE into a program of `kore.k`; the decoders of `krun --search`'s and `kore.k`'s results into one canonical text. |
| `tools/test_korek.py` | Tests of the encoder's attribute checks (a `simplification` or `non-executable` axiom, a `macro` symbol, an unknown attribute refused) and of its shape checks (a variable the left side does not bind, a right side under `\exists`, a predicate that is not a term equal to `true`, each refused by name); needs no K. |
| `tools/case.py` | Writes the tool-written files of an entry (`evidence.json`, `kompile.txt`, `kore.txt`, and a case's encoded program), never its `entry.toml`; checks the quotes of the entries' bases against a K checkout (needs K; `--verify-quotes` needs only the checkout). |
| `tools/test_case.py` | Tests of `case.py` on hand-built text entries, with kompile stood in for: what `kore.txt` holds, a refusal recorded as a result, the refusal to build without `entry.toml`, the `kcore` import, the reading of `kast`'s output, the quote check; needs no K. |
| `tools/check.py` | Checks each entry's record (`SCHEMA.md`, section 5) and runs `kore.k` on every case (needs only `krust`; `--no-run` needs only Python). |
| `tools/test_check.py` | Tests of `check.py`'s pass rule on hand-built entries; needs no K and no `krust`. |
| `SCHEMA.md` | The schema of an entry: `entry.toml`, the evidence, and what `tools/check.py` checks. |
| `COVERAGE.toml` | One row per attribute the encoder reads of a selected axiom or an applied symbol: `refused`, with the reason, or `ignored`, with the reason it has no meaning in `kore.k`. |
| `cases/<id>/` | One case, below. |
| `texts/<id>/` | One text entry: its K text (`<id>.k`, or a KORE text, or none for a quoted declaration), `entry.toml`, and, written by `tools/case.py`, `evidence.json`, `kompile.txt` and `kore.txt` as for a case (`SCHEMA.md`). |
| `FLOW.toml`, `MUTATIONS.toml` | The kink corpus: every case's `kore.pgm`, the argued coverage obligations, and the 69 mutations of `kore.k`. |
| `kink.lock` | kink-flow's verdict record of the corpus: each mutation's status and recorded killer, and the coverage verdicts. |
| `kill-matrix.json` | For each mutation, its status, every case that kills it and the cases on which its run gave no comparable result. |
| `tools/test_mutations.py` | Checks that every mutation is killed or marked equivalent with its argument, and names the premises it breaks; needs no K and no kink. |
| `tools/killmatrix.py` | Reduces `kink-flow run --full`'s JSON document to `kill-matrix.json`. |

### A case

| File | Content |
| --- | --- |
| `def.k` | The object definition: module `CASE`, syntax module `CASE-SYNTAX`, `configuration <k> $PGM:S </k>` (or a top cell holding `<k> $PGM:S </k>` and other cells), rewrite rules on the closed `<k>` cell (`<k> L => R </k>`). Its first comment says what the case tests. |
| `pgm` | The initial term, in `CASE-SYNTAX`. |
| `entry.toml` | The entry (`SCHEMA.md`), written by hand: the subject, the ruling (settled with its final configurations, or unsettled with its readings and the reading `kore.k` computes), its reason with the quoted sentences and the entries it rests on, and a `[[disposition]]` with its reason for each implementation whose result is not the ruling. No tool writes it. |
| `pgm.kore` | `kast pgm --output kore` against `def.k` kompiled for the haskell backend: the initial term of sort `S`. The initial configuration is the value of kompile's `initGeneratedTopCell` at the map `$PGM \|-> PGM`: for the one cell `<k>`, `<generatedTop>(<k>(kseq(inj{S,KItem}(PGM), dotk())), <generatedCounter>(0))`; the encoder unfolds kompile's initializer equations to build it, and keeps the item `inj{S,KItem}(PGM)` of a one-cell configuration or the top cell of a configuration of several cells. |
| `kore.pgm`, `symbols.json` | The encoded program for `kore.k` (start sort `Pgm`) and the encoder's numbering of symbols and sorts; for a case with collections, `collections` names each collection sort's kind and its concatenation, unit and element symbols. |
| `evidence.json` | The evidence (`SCHEMA.md`, section 4). `inputs`: the SHA-256 of `def.k`, of `pgm` and of the answer fields of `entry.toml`. `kompile`: the release, command and exit code of the haskell kompile, and the SHA-256 of `kore.txt`. `ruling_canonical`: the finals of the ruling and of its readings in the canonical text below. `implementations`: for each backend (`haskell`, and `llvm` kompiled with `--enable-search`), `version`, the K release and backend that produced the result, and `finals`: the item `inj{S,KItem}(X)` the `<k>` cell holds in each final configuration of `krun --search` (for a configuration of several cells, the top cell `Lbl'-LT-'t'-GT-'(…)`, whose `<k>` cell holds `kseq(item,dotk())`), as canonical text (`Lbl…(args)`, integers, `true`/`false`, `inj{SortA,SortB}(v)`; a collection as `SortMap{k|->v,…}` and `SortSet{x,…}` with its elements' texts sorted, `SortList[x,…]` in order, whatever order a backend prints them in; a result under a condition carries it, ` if defined(…)`, ` if A=B`, ` if not(…)`, joined by ` and `), sorted; or `error`, the backend's failure without its temporary paths; and, where one was imported, the `kcore` row. |
| `kompile.txt` | The haskell kompile's command, release, exit code and messages, with the case's and the build's directories and K's store paths replaced by names. |
| `kore.txt` | The sentences `def.k` adds to an empty module: those of the kompiled text's main module that come from no builtin file of K and that the main module of an empty module, kompiled alike, does not hold; each after a line `//@ N`, N its index among the main module's sentences, without its `Source` and `Location` attributes and with the variables kompile generates renumbered. |

The kompiled object definition is not committed.
`kompile` writes the absolute path of `def.k` and of K's own installation into the `Source` attributes of `definition.kore`, and a case's `definition.kore` is about 250 KB, almost all of it K's builtin modules.
`def.k` and `pgm` are the sources; `tools/case.py` rebuilds the kompiled text in its build directory, and the encoder selects the object definition's axioms by that build's `Source` path.
What a harness needs without K is committed: `pgm.kore` (which names no path), `kore.pgm`, `symbols.json`, `evidence.json`, and `kore.txt`, the case's own sentences.
A harness that reads KORE definitions kompiles `def.k` itself, as `tools/case.py` does.

## Building a case

From this directory, with the pinned K toolchain (`k/result/bin` at the repository root):

```sh
export K_KOMPILE=$PWD/../../../k/result/bin/kompile
python3 tools/case.py --all                  # every case
python3 tools/case.py cases/<id> texts/<id>  # named entries
python3 tools/case.py --no-backends --all    # kompile, kast and the encoder only
python3 tools/case.py --refresh --all        # also rerun the backends whose inputs did not change
python3 tools/case.py --import kcore=FILE cases/<id>    # add the kcore row (format: the script's docstring)
python3 tools/case.py --verify-quotes ../../../k --all  # each basis's quote at its locator in the K checkout (cases and texts)
```

A new case is a directory `cases/<id>/` with `def.k`, `pgm` and a hand-written `entry.toml`; `tools/case.py cases/<id>` writes the rest, and stops at an entry without `entry.toml`, which it never creates or changes.
A text entry is built the same way: its K file is kompiled (`kompile --backend haskell FILE`, in a copy of the entry's directory), and a refusal of kompile is recorded as the result (exit code and message, no `kore.txt`); an exit code other than the one `[text].kompile` states is reported, and `tools/check.py` fails the entry on it.
`ruling_canonical` is computed with `kast` against the haskell-kompiled `def.k`, in module `CASE`: each final of a one-cell configuration is the term the `<k>` cell holds, parsed by the program parser at sort `KItem`; each final of a configuration of several cells is the top cell, parsed by the rule parser with no compilation step. A final that does not parse stops the entry with an error naming it. `kast` parses neither a cell collection of two or more instances (`Invalid sort predicate`) nor one of none (it gives the cell no argument), so the finals of c35 and c36 are to be written as `finals_canonical`, the canonical text itself.
The reference runs are cached in `evidence.json` by the SHA-256 of `def.k` and `pgm`; with unchanged inputs only the haskell kompile (itself cached in the build directory by the same hashes), `kast` and the encoder run again, and `--no-backends` never runs a backend.
A case costs about 15 to 80 s of reference runs (two kompiles, two searches; an llvm search that fails takes up to a minute), each under a 120 s timeout and a 12 GiB memory scope.
Keep the object search finite: on a cycle the haskell backend's search does not stop, and only the timeout ends it.

## Cases

52 cases, each a small object definition for one point of the reading above; beside them, 124 text entries under `texts/`, each a ruling on a K text, a KORE text or a quoted declaration (`SCHEMA.md`, section 3), on which the cases' rulings rest.
A case's ruling is its final configurations, derived in its `entry.toml` from the K text and the entries it rests on; where the text does not settle a point, the case is unsettled, names the entry whose question it is, gives one reading per answer, and names the reading `kore.k` computes.
The last column gives, for a settled case, the implementations whose result is not the ruling (`differs`); for an unsettled one, the reading each implementation's result is (`reading:<name>`), `coincides:<name>` where its finals equal a reading's by a route the text does not admit, or `differs` where it is no reading. `kore.k` is named there only where its result is not the ruling or the reading the ruling column names for it. The reason of each is the `[[disposition]]` of the case's `entry.toml`.

| case | what it tests | status | ruling | implementations not at the ruling |
| --- | --- | --- | --- | --- |
| c01-fn-prio | equations of three priorities, an `[owise]` equation, failing `requires` | settled | `out(3, 3, 4)` | none |
| c02-rule-prio | rules of several priorities: a rule whose `requires` fails does not block a larger priority | settled | `d(6)` | none |
| c03-nondet | rules of one priority give several successors; paths meet again and end in several final configurations | settled | `fin(0)`, `fin(1)`, `fin(10)`, `fin(20)` | none |
| c04-subsort | the subsort chain `Int < Num < Val < Exp` and `Bool < Val`: matching through the transitive closure | settled | `pair(-5, 1)` | none |
| c05-hooks | the Int and Bool hooks of the fragment, on negative operands too | settled | `q(false, false, false, false, false, true, false, true, true)` | none |
| c06-nonlinear | a variable seen twice in an equation's and a rule's left side | settled | `same` | none |
| c07-strict-args | a function's argument is evaluated before its equations are matched | settled | `res(30)` | none |
| c08-undef-rhs-blocks | a rule that applies with an undefined right side, beside a rule of larger priority number: whether it blocks that rule | unsettled | on `kk:t03-applied-rule-blocks`: readings `applied-blocks`, `undefined-rhs-does-not-block`; `kore.k` computes `applied-blocks` | haskell reading:applied-blocks, llvm differs |
| c09-undef-requires | an undefined `requires` is not true: the rule does not apply | settled | `c(0)` | llvm differs |
| c10-strict-ite | `#if` is strict in its three arguments: an undefined branch makes it undefined | unsettled | on `kk:t03-applied-rule-blocks`: readings `applied-blocks`, `undefined-rhs-does-not-block`; `kore.k` computes `applied-blocks` | haskell reading:applied-blocks, llvm differs |
| c11-fn-no-equation | an application of a partial function that no equation applies to, in a rule's right side | unsettled | on `kk:t13-fn-no-equation, kk:t03-applied-rule-blocks`: readings `closure-none+applied-blocks`, `closure-none+undefined-rhs-does-not-block`, `any-member`, `rest`; `kore.k` computes `closure-none+applied-blocks` | haskell reading:rest, llvm differs |
| c12-undef-init | an undefined initial term has no final configuration | settled | none | llvm differs |
| c13-inj-bool | composed injections of a function's result; an undefined result under an injection; Bool literals and a Bool-sorted pattern against injected values | settled | `out(0)`, `false`, `true` | llvm differs |
| c14-fn-undef-requires | an equation whose `requires` is undefined does not apply; the `[owise]` one does | settled | `res(2)` | llvm differs |
| c15-nonlinear-rule | a variable seen twice in a rule's left side does not match distinct values | settled | `diff` | none |
| c16-bool-pattern | a Bool domain value in a left side matches only itself | settled | `b(false)` | none |
| c17-init-function | the initial term applies a function, evaluated before the first step | settled | `yes` | none |
| c18-div-signs | `/Int` truncates toward zero and `%Int` takes the sign of the dividend | settled | `r(3, 1, -3, -1, -3, 1, 3, -1)` | none |
| c19-map-choice | `K \|-> V M` with a frame variable matches every entry: one successor per entry, the rest bound to `M` | settled | `out(1, 10, 2 \|-> 20 3 \|-> 30)`, `out(2, 20, 1 \|-> 10 3 \|-> 30)`, `out(3, 30, 1 \|-> 10 2 \|-> 20)` | none |
| c20-map-key-fixed | an entry pattern with a fixed key (a domain value, a variable bound earlier), an entry chosen under a `requires`, a pattern without a frame | settled | `r(20, 1 \|-> 10 3 \|-> 30)`, `r(30, 1 \|-> 10 2 \|-> 20)`, `r(2, .Map)`, `r(3, .Map)`, `d(1 \|-> 10 2 \|-> 20 3 \|-> 30)` | none |
| c21-map-concat | `_Map_` is undefined on a common key, the union on disjoint keys; `M .Map` is `M` | settled | `r(2, 1 \|-> 2 2 \|-> 3 7 \|-> 8)`, `r(3, 1 \|-> 2 7 \|-> 8)` | llvm differs |
| c22-map-hooks | `Map:lookup`, `lookupOrDefault`, update of a present and of a new key, removal, `in_keys`, `size` | settled | `r(2, 2, 0, 1 \|-> 7 3 \|-> 4, 1 \|-> 2 2 \|-> 9 3 \|-> 4, 3 \|-> 4, 1 \|-> 2 3 \|-> 4, true, false, 2)` | none |
| c23-map-lookup-missing | a lookup of a missing key is undefined | settled | `b(2)` | llvm differs |
| c24-map-fn-pattern | equations whose argument pattern is `K \|-> V M`; the substitution whose `requires` holds is not the first | settled | `r(30, 2)` | none |
| c25-map-equal | `A B` and `B A` are one map: a variable seen twice matches them | settled | `same(1 \|-> 2 3 \|-> 4)` | none |
| c26-map-strict | a map with an undefined entry is undefined | settled | `r(2, 1 \|-> 2 5 \|-> 1)` | llvm differs |
| c27-set-choice | `SetItem(X) S` matches every element, and only where `S` does not hold `X` (the settled entry `kk:t35-set-concat-overlap`) | settled | `out(1, SetItem(2) SetItem(3) SetItem(11))`, `out(2, SetItem(1) SetItem(3) SetItem(12))`, `out(3, SetItem(1) SetItem(2) SetItem(13))` | none |
| c28-set-overlap | `_Set_` on a common element has no value (`#False` in the `SET` module's prose, the settled entry `kk:t35-set-concat-overlap`; the declaration's `idem` states no value there); `\|Set` is total | settled | `r(2, SetItem(1) SetItem(2))`, `r(3, SetItem(1))` | llvm differs |
| c29-set-hooks | `Set:in`, `size(Set)`, `\|Set` with an element below, between, above and equal to the present ones | settled | `r(true, false, 2, SetItem(0) SetItem(1) SetItem(3), SetItem(1) SetItem(2) SetItem(3), SetItem(1) SetItem(3) SetItem(9), SetItem(1) SetItem(3))` | none |
| c30-list-positions | `ListItem(X) L` takes the first element, `L ListItem(X)` the last; a pattern without a frame matches only its length | settled | `r(1, ListItem(2) ListItem(3))`, `r(3, ListItem(3) ListItem(1) ListItem(2))`, `d(ListItem(1) ListItem(2) ListItem(3))` | none |
| c31-list-concat | `_List_` is associative and not commutative; an element may occur twice; `size(List)` | settled | `p(ListItem(1) ListItem(2), ListItem(2) ListItem(1))`, `assoc(ListItem(1) ListItem(2) ListItem(1))`, `n(3)` | none |
| c32-elem-strict | a set or list with an undefined element is undefined | settled | `c(2)` | llvm differs |
| c33-list-middle-frame | `ListItem(X) L ListItem(Y)`: elements on both sides of a frame | settled | `r(1, 4, ListItem(2) ListItem(3))` | haskell differs |
| c34-cells-several | rules that read and rewrite cells besides `<k>`, a `requires` over another cell, the cells a rule does not mention kept, the cells' declared initial values | settled | `<t> <k> done(4) </k> <acc> 13 </acc> <cnt> 4 </cnt> </t>` | none |
| c35-cell-map | a cell collection keyed by `<id>`: an instance added beside the others, the instance of a key removed, a child of one instance among three rewritten | settled | 1 final configuration(s), in canonical text | none |
| c36-cell-key-twice | an instance added under a key already present, whose concatenation is undefined; a rule matching any instance gives one successor each | unsettled | on `kk:t03-applied-rule-blocks`: readings `applied-blocks`, `undefined-rhs-does-not-block`; `kore.k` computes `applied-blocks` | haskell reading:applied-blocks, llvm differs |
| c37-keq | `==K` and `=/=K`: a value reached through a subsort against itself at its own sort, values of two sorts, maps built in two orders and maps differing in one value | settled | `r(true, false, false, false, true, false, false)` | none |
| c38-keq-strict | `==K` with an undefined operand is undefined: that rule has no successor | settled | `ok(0)` | llvm differs |
| c39-tokens-preds | a token literal in a left side matches only itself; tokens of two sorts with one text differ under `==K`; `isS` on a value of `S`, of a sort below it and of another sort | settled | `r(true, false, true, false, false, false)`, `z` | none |
| c40-as-patterns | `#as` on a `Map` pattern with a frame (the whole map, once for each entry taken); `#as` in a function's argument whose variable the left side binds earlier | settled | `got(1, 1 \|-> 10 2 \|-> 20)`, `got(2, 1 \|-> 10 2 \|-> 20)`, `r(3, 0)` | none |
| c41-total-requires | a `total` function in a `requires`: its equation decides the rule, the `[owise]` rule the rest | settled | `yes(3)`, `no(12)` | none |
| c42-total-no-equation | a `total` function that no equation applies to, in a `requires`: the text states that it has a value, not which | unsettled | on `kk:t14-total-no-equation`: readings `value-true`, `value-false`, `rest`; `kore.k` computes none of them (`outside`) | haskell reading:rest, kore.k coincides:value-false, llvm differs |
| c43-ensures | an `ensures` that holds gives the right side; one that is false leaves `a(0)` without successor and not final | settled | `b(1)` | llvm differs |
| c44-ensures-priority | c43 with an overlapping rule of larger priority number: it does not apply where the `ensures` is false | settled | `b(1)` | llvm differs |
| c45-fn-owise-recursion | `f(0) => 0`, `f(N) => f(N -Int 1) [owise]`: the `[owise]` right side is evaluated only where the equation of priority 50 does not apply, so `f(2)` ends | settled | `b(0)` | none |
| c46-prio-nonterm-requires | a rule of priority 50 applies; the rule of priority 60 beside it, whose `requires` does not terminate, is not tried | settled | `b(1)` | none |
| c47-undef-rhs-same-prio | two rules of one priority apply, one with an undefined right side: the other's successor is kept | settled | `c(1)` | llvm differs |
| c48-fn-undef-requires-larger | an equation of priority 60 with an undefined `requires`: not evaluated where the equation of priority 40 applies, and not holding where it is | settled | `b(1, 3)` | llvm differs |
| c49-string-bool-eq | `==String`, `<String` and `==Bool` on `String` domain values sharing a first character, and a `String` literal in a left side | settled | `b(false, true, false, true, false, true)`, `c("ac")` | none |
| c50-fn-ensures | an equation with an `ensures` (`half(N) => N /Int 2 ensures N >=Int 0`): `half(4)` is 2, `half(-4)` has no value; whether `run(-4)`, whose rule then has an undefined result, is final | unsettled | on `kk:t03-applied-rule-blocks`: readings `applied-blocks`, `undefined-rhs-does-not-block`; `kore.k` computes `applied-blocks` | haskell reading:applied-blocks, llvm differs |
| c51-fn-ensures-owise | c50 beside `half(_) => 0 [owise]`: the first equation decides at -4, so the `[owise]` one does not apply and `half(-4)` has no value, not 0 | unsettled | on `kk:t03-applied-rule-blocks`: readings `applied-blocks`, `undefined-rhs-does-not-block`; `kore.k` computes `applied-blocks` | haskell reading:applied-blocks, llvm differs |
| c52-subsort-one-entry | one stated subsort `Int < Val` and a sort `Other` with none: an `Int` matches `V:Val` through the subsort and not `X:Other`, a walk of the subsort table as long as the table | settled | `done(3)` | none |

Counted by `tools/check.py` on this tree: 176 entries, 136 settled and 40 unsettled; of the 52 cases 45 are settled and 7 unsettled, of the 124 text entries 91 settled and 33 unsettled.
Recorded differences: llvm 21 (14 settled cases, where it aborts, does not evaluate an `ensures`, or gives `_Set_` a value on a common element (c28), and 7 unsettled ones, where its result is no reading), haskell 1 (c33, where its search stops with an error), and, counted apart, `kore.k` 1 (c42: its finals are those of `value-false`, reached by giving the `total` function no value, which the text excludes). No `kcore` row is recorded.
Both backends' results are kept in each case's `evidence.json`, labelled with the K release and backend that produced them.

## Rerunning the cases

One command checks every entry's record and runs `kore.k` on every case; no K reference tool runs, since `evidence.json` holds the cached reference results.
It needs a release `krust` (the repository's `k-rust` command-line tool) built from this tree:

```sh
with-z3-static-5.3.3 cargo +stable build --release -p k-rust --no-default-features --features cli --locked
python3 tools/check.py             # every entry; or name entries: tools/check.py cases/<id> texts/<id> ...
python3 tools/check.py --no-run    # the records only, without kore.k; needs nothing but Python
```

`tools/check.py` takes `krust` from `$KRUST`, else `$CARGO_TARGET_DIR/release/krust`, else the repository's `target/release/krust`, and exits 2 when there is none.
It kompiles `kore.k` once with `krust kcompile` (cached in its build directory by the SHA-256 of `kore.k` and of `krust`), runs each case's `kore.pgm` with `krust krun --sort Pgm`, and decodes the result with the case's `symbols.json`: `kore.k`'s result is one more implementation beside the recorded ones.
An entry passes when its record is consistent with itself (`SCHEMA.md`, section 5), and fails for one of three causes:

- a schema fault: `entry.toml` does not parse or does not have the form of `SCHEMA.md` (among others, a reason that names an implementation, a settled entry resting on an unsettled one, an unsettled case without the reading `kore.k` computes);
- stale evidence: a hash `evidence.json` records is not the present one (the answer fields of `entry.toml`, the K text, `kore.txt`), or there is no `evidence.json`;
- an unrecorded or outlived difference: an implementation's result, `kore.k`'s included, is not the settled ruling (at an unsettled case, no reading's finals) and no `[[disposition]]` names it; or a disposition names an implementation whose result is the ruling, or another than it says.

An implementation that differs from the ruling under a disposition is not a failure, whichever implementation it is.
It prints one line per entry, its status and how each implementation stands (`=`, `reading:<name>`, `coincides:<name>`, `differs`), and a `PASS` or `FAIL` summary that counts the entries, settled and unsettled, and the recorded differences per implementation, `kore.k`'s apart; it exits 0 only when every entry passes.

Measured in this tree: 176 of 176 entries pass (136 settled, 40 unsettled); recorded differences haskell 1, llvm 21, `kore.k` 1; each `krust krun` process takes 45 to 125 ms, the whole command about 4 s warm.

## The kink corpus

The corpus is a kink-flow corpus of a K definition, as `kink/examples/imp` is: `FLOW.toml` names `kore.k` and its modules, and its programs are the cases' `kore.pgm` (start sort `Pgm`).
Each mutation of `MUTATIONS.toml` is a wrong reading of KORE, stated in its `misunderstanding` and written as text edits of `kore.k`'s labelled rules.
Each `misunderstanding` ends with `[premise: …]`, the premises of the reading above that the mutation breaks, by the names `MUTATIONS.toml`'s header gives the 16 of them; a mutation no case kills is marked equivalent (`expect = "survive"`) with its argument. `python3 tools/test_mutations.py` checks both against `kill-matrix.json` and `kink.lock`, without kink.
A case kills a mutation when the mutant's result on it, every final configuration of the object definition, differs from `kore.k`'s.

Build kink-flow in a target directory of its own (the portable profile, no Z3), then run from this directory:

```sh
export CARGO_TARGET_DIR=/tmp/kore-in-k-target   # any directory of its own
cargo +stable build --release -p kink-flow --no-default-features --locked
KF=$CARGO_TARGET_DIR/release/kink-flow
$KF check FLOW.toml --mutations MUTATIONS.toml
$KF coverage FLOW.toml --lock kink.lock              # obligations of kore.k; records [coverage]
$KF run FLOW.toml MUTATIONS.toml --lock kink.lock    # survivors; records [run]
$KF run FLOW.toml MUTATIONS.toml --full | python3 tools/killmatrix.py > kill-matrix.json
$KF run FLOW.toml MUTATIONS.toml --lock kink.lock --locked   # exit 1 when kink.lock is not current
```

Run kink-flow under a memory bound, for example `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0`.
Its caches are in `.kink-flow/`, which is not committed.

### Results

Measured in this tree with kink-flow built from it (portable profile):

- Coverage: 442 obligations covered (246 of 249 rules, 150 of 154 requirements, 46 of 46 syntax productions), 7 argued, 0 open, over 52 comparable cases.
  The argued obligations are `rule:KORE.ins-dup` and its requirement `requirement:KORE.ins-dup:held` (no `insert` receives a configuration its list already holds: a configuration is inserted into `seen` only when it is not a member, and into the finals only when taken from the frontier, which holds each configuration once), and `rule:KORE.tag-other` (configurations are values; `vr`, `hk`, `as`, `cb` and `bot` never reach `cmp` under `kore.k`, and `kv` and `el` are compared only with their own kind, since a collection holds elements of one kind; the rule is kept so that a mutant that makes `bot` a configuration still compares it), and `requirement:KORE.m-tok:…:false` (a token pattern of sort `S` stands at a position of sort `S`, where the value is a token of `S` itself: one of a sort below `S` stands under an injection, which matching compares by sort first; so `m-tok` never meets tokens of two sorts), and `rule:KORE.leq-refl` with the requirements `requirement:KORE.leq-refl:held` and `requirement:KORE.leq-up:refuted` (`leq` is applied only in the `requires` of `m-inj-sub`, which is tried only where `m-inj-same`, before it in the text, does not apply, so only at two different sorts).
  `rule:KORE.above-dry` is reached only where a path of the subsort table from the sort `leq` starts at has as many entries as the table; c52 has a table of one entry, `Int < Val`, and matches an injected `Int` against `X:Other`, where that rule's `false` decides the match.
- Mutations: 69, of which 68 are killed and 1 survives as expected: `fn-last-of-priority` (`expect = "survive"`).
  Two equations of one priority that both apply with different values state that the function has two values, an inconsistent definition; on a consistent object definition the first and the last applicable equation of a priority agree, so no case kills it.
  The 15 mutations of collections are wrong readings of matching (`subst-first-only`, `fn-first-subst-only`, `frame-dropped`, `col-pattern-open`, `col-first-split-only`, `list-match-commutative`, `list-split-at-head`), of collection values (`map-duplicate-keys`, `map-concat-overrides`, `set-idempotent`, `list-as-set`, `col-unordered`) and of hooks (`map-lookup-missing-defined`, `map-update-duplicates`, `set-union-partial`).
  The 38 earlier mutations keep their verdicts (their killing cases only gain collection cases); two of them were re-anchored on the rules that now carry a list of results (`rule-rhs-unevaluated` on `fire-holds`, `undefined-result-does-not-block` on `add-some`).
  The 3 mutations of cell collections are wrong readings of a `Map` that a cell collection's rules tell apart: `map-entry-by-position` (an instance found only at its position, not by its key), `col-frame-not-rebuilt` (the instances a rule does not mention dropped from the collection it builds) and `map-keyed-by-entry` (two instances of one key kept when they differ).
  The cell cases kill all three, and so do the plain `Map` cases: a cell collection needs no rule of its own in `kore.k`, so the cell cases are evidence that the encoder reads kompile's cells and initializers as terms and maps, not a sharper test of `kore.k`.
  They also kill the earlier collection mutations `col-first-split-only`, `frame-dropped`, `map-duplicate-keys` and `map-concat-overrides`; since c36 shares the last two with c21, c21 no longer kills a mutation alone.
  The 5 mutations of equality, tokens and as-patterns are `keq-undefined-false` (an undefined operand of `==K` gives `false`; c38 alone), `token-any-value` (a token literal matches any token of its sort; c39 alone), `token-sort-ignored` (a token is its text, whatever the sorts of the token and of its injections; c39 alone), `as-first-subst-only` (an alias of a collection pattern bound under its first split only; c36, c40) and `as-alias-rebinds` (an alias variable the left side has bound is bound afresh instead of compared; c40 alone).
  Ignoring the sort of a token alone changes nothing on a well-sorted definition, since tokens of two sorts reach a comparison only under injections from their sorts, which differ; so `token-sort-ignored` also ignores the injections' sorts, the reading of a formalization that erases sorts from values.
  `subsort-walk-out-holds` (a walk of the subsort table that has taken as many entries as the table holds read as having reached the sort sought) is killed by c52 alone: there `X:Other` would match the `Int` 3. Deleting `above-dry` instead is no mutation kink can kill: it removes an equation of a function, so every model of `kore.k` is a model of the result (kink's weakening); it is not in the corpus.
  Sort predicates need no rule of their own: kompile's `isS` equations match through injections, and c39 kills the subsort mutations `subsort-dropped`, `subsort-reversed` and `subsort-unchecked` with c04 and c13.
  The 3 mutations of `ensures` are its other readings: `ensures-ignored` (the right side whatever the `ensures`, of a rule or an equation, which is what the llvm backend computes) and `ensures-false-not-applied` (a rule's false `ensures` read as a false `requires`: the rule has not applied, a rule of larger priority number may, and a configuration only such rules apply to is final), which c43, c44, c50 and c51 kill; and `ensures-as-requires` (an equation whose `ensures` is not true read as not applying, so that the next equation, a larger priority or the `[owise]` one gives the value; rules keep their reading), which c51 alone kills: in c50 no other equation applies, so the mutant's `half(-4)` has no value as well. A `total` function needs no rule of its own, so no mutation reads it; c42 also kills `rule-undefined-requires-holds`, which c09 killed alone.
  The priority mutations are anchored on the walk by ascending priority: `rule-priority-reversed`, `fn-priority-reversed` (a priority read as its negation, which reverses the walk), `rule-priority-ignored`, `fn-first-applicable` (every priority read as 0), `rule-owise-ignored`, `fn-owise-ignored` (on `rprio` and `cprio`, a rule's and an equation's priority), `fn-last-of-priority` (on `else-some`), `nondeterminism-first-match` (on `drop-keep`), `undefined-result-does-not-block` and `ensures-false-not-applied` (an undefined or false-`ensures` result dropped before the priority is chosen, on `fa-take`), `bottom-is-configuration` (on `step-some`); their verdicts are unchanged. `undefined-result-empties-step` (an undefined result among the rules of a priority drops the other rules' successors) is new; c47 and the cases with an undefined right side beside a defined one kill it.
  The reading that evaluates the `requires` and right sides of every priority and then keeps the least priority's results differs from this one only where an evaluation at a larger priority does not terminate (c45, c46): the mutant then has no result, which kink does not count as a kill, so it is not in the corpus; c45 and c46 are the cases that tell the two apart (`kore.k` before the walk ran out of stack on both).
  The 3 mutations of `String` and `Bool` equality are `string-lt-reversed`, `string-eq-prefix` (texts sharing their first character read as equal) and `bool-eq-as-and` (two false operands read as unequal); c49 alone kills each.
  On c34 the mutant `rule-requires-ignored` descends through `step(-1)`, `step(-2)`, … and gives no comparable result within the budget; c03 kills it.
- Cost: `run --full` 39 to 50 s after a change of `kore.k`; `coverage` and `run --locked` about 1 s warm.

15 cases kill some mutation that no other case kills:

| case | mutations it alone kills |
| --- | --- |
| c04-subsort | subsort-not-transitive |
| c10-strict-ite | ite-lazy |
| c11-fn-no-equation | no-equation-kept |
| c12-undef-init | undefined-init-is-final |
| c16-bool-pattern | bool-dv-any-value |
| c18-div-signs | tdiv-as-ediv, tmod-as-emod |
| c23-map-lookup-missing | map-lookup-missing-defined |
| c24-map-fn-pattern | fn-first-subst-only |
| c28-set-overlap | set-idempotent |
| c38-keq-strict | keq-undefined-false |
| c39-tokens-preds | token-any-value, token-sort-ignored |
| c40-as-patterns | as-alias-rebinds |
| c49-string-bool-eq | bool-eq-as-and, string-eq-prefix, string-lt-reversed |
| c51-fn-ensures-owise | ensures-as-requires |
| c52-subsort-one-entry | subsort-walk-out-holds |

c14's lone kill (`fn-undefined-requires-holds`) is shared with c48. c07, c15 and c17, which alone killed `dv-any-value`, `fn-owise-ignored`, `nonlinear-ignored` and `init-unevaluated` among the 18 cases, now share those kills with collection cases; c21's two lone kills (`map-concat-overrides`, `map-duplicate-keys`) are shared with c36, c13's three (`inj-composed-outer-source`, `inj-not-composed`, `subsort-unchecked`) with c37 and c39, and c04's `subsort-dropped` and `subsort-reversed` with c39; the other cases each kill mutations that another case also kills.

## Next

Configurations of several cells, `Map` cell collections, `==K`, token sorts, sort predicates, `#as`, `total` functions and `ensures` are done (above). What remains:

- Conditions on results: a `total` function's value that the definition leaves open (c42) has no value in `kore.k`; carrying the condition the haskell backend reports needs symbolic terms in `kore.k`.
- Cell collections of `type="Set"` and `type="List"`, and cells of multiplicity `?`.
- Other collection hooks as small definitions meet them (`keys`, `values`, `-Map`, `-Set`, `List:get` with its negative indices, `range`), and the other `String` and equality hooks.

## Why K and not KRS

The other packages of `krs/semantics` are KRS crates whose K is emitted by `krs`.
`kore.k` stays K source because a port is not small, although every construct it uses has a KRS spelling (constructor enums with `#[k::syntax]` templates, `k::equations!` tables with `#[k::equation(owise)]` and `#[k::equation(priority = N)]`, `k::rules!` over a one-cell configuration, `kequal` guards):

- The definition: its 16 sorts as constructor enums whose syntax templates must reproduce exactly the program syntax the committed `kore.pgm` files are written in (`pgm(def(…), …)`, `T ; Ts`, `.Ts`, `bot`); the 237 equations of 72 functions as equation tables; the 11 rewrite rules of the search in `k::rules!`.
  Each sentence is judged by KRS's checks on the assembled definition (overlapping equations, catch-all rows that need `owise`, complementary guards of rules), which `kore.k` has never been put through; whatever they refuse is a change of the definition to be argued, not a transcription.
- The corpus: `krs kink` reads a corpus in its own layout, `kink/` beside the crate's `Cargo.toml`: `kink/FLOW.toml` naming the package (`[spec] krs = { package = …, definition = … }`), the cases as program files that bind the `#[k::init]` parameter, `kink/mutations/<topic>.toml`, and a committed `kink/definition.k`.
  The emitted K has KRS's module names, rule labels and spelling of each rule, so all 69 mutations are re-anchored (each edit's `rule` and `find`), the four argued obligations renamed, and the coverage and kill numbers re-measured.
- The evidence that the port is the same definition: `krs run` of every case's `kore.pgm` gives the result `kore.k` gives, and the kill matrix is the same up to the renaming of mutations' anchors.

By the size of the existing ports (the KWasm slice is 294 lines of Rust for 16 sentences), that is on the order of a thousand lines of Rust and a re-authored mutation list, a unit of its own.
A half port, part of the definition in KRS and part in K, would leave two definitions of one reading; it is not done.

## Status

Done: the definition, with `Map`, `Set` and `List`; the encoder and the case builder, with configurations of several cells and `Map` cell collections, `==K`, token sorts, sort predicates, `ensures` and `String` values; 52 cases and 124 text entries, each with its ruling and its evidence; the kink corpus with this tree's coverage and kill matrix; and `tools/check.py`, which checks each entry's record and runs `kore.k` on every case.

Not verified here: `kore.k` is checked against the rulings of these 52 cases, with the two backends' results recorded beside them; that a ruling follows from the sentences it quotes is a reader's check, and `tools/case.py --verify-quotes` checks only that each quote stands at its locator; no case exercises a definition outside the fragment, so the encoder's refusals are untested; this tree's encoder was rerun on every case from its kompiled text and reproduces every committed `kore.pgm` and `symbols.json` (c41's were re-encoded: the committed ones came from the encoder before the `ensures` change and differed only in the numbers of two symbols); a `Map` or `Set` value's canonical order is `cmp`'s, which the decoders replace by the order of the elements' texts, so the order itself is checked only through `kore.k`'s own equalities (c25); kink's verdicts rest on k-rust's execution of `kore.k`, which is the same engine `tools/check.py` uses.

Next: conditions on results and the other cell multiplicities (above); a KRS port of `kore.k`, if wanted, as a unit of its own (above); and feeding the cases to a harness that runs other KORE implementations on `def.k` (kompiled) and `pgm.kore`, comparing with the `implementations` of `evidence.json`.
