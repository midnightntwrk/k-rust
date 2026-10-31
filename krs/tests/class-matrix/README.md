# Class-test expectations

`expected.toml` states the expected outcome of every case that `krs_test_support::class_matrix`
generates: one construct in one slot of an accepted base, for readable records and claims, `cells!`
rules, initializers, the strict-subsort axis, every term shape at the term positions of every
sentence form, the module-import axis, every sentence attribute on every sentence form, and the
readable records and `cells!` rules again on the run base, which K7 runs (the run families, K7
below). `pending.toml` lists the cases known not to conform.
The schema and the rules that read both files are documented in the `class_matrix` module.

For the term families (`terms/..`, `import/..`, `notation/..`) and the attribute axis (`attrs/..`,
K8 below), the outcome comes from the oracle (`class_matrix::oracle`, `class_matrix::attributes`),
not from refusal rules. Each term case carries its position (the form,
the slot, what a term there means: matched, evaluated, built or a guard, its root role and its
nesting) and its construct's nodes as data, and the oracle states, per construct, where the
construct means something and which mistake it is elsewhere. The precedence for a term case:

1. a refusal the oracle tells from the spelling and its position decides;
2. otherwise the most specific refusal rule of `expected.toml` decides: the rules left for these
   families name a term's sort and names (`condition-sort`, `let-sort`, `unbound-name`,
   `record-update-base`, `binder-sort`, `list-notation-sort`, `matches-pattern-binder`, ..), never
   its position;
3. otherwise a refusal the oracle tells by what a path resolves to or an operand's sort decides
   (a function in a pattern, a predicate as an operand), since a name or sort mistake is met first;
4. otherwise the case is accepted, with the K its accept entry records.

The term family's positions (`class_matrix::terms`) are of three kinds, each a path of openings
from a slot's root, so a case's position is data the oracle reads, never parsed from its ID:

- the argument positions of the 17 sentence forms (`terms/rule/subject/..`), a readable record's
  collection entries among them: a map read's key and value, and the elements of a List cell, a
  cons list (`terms/readable/cons-element/..`) and a List collection's instances
  (`terms/readable/collection-child/..`), which a pattern matches (decision D1), and an
  initializer's computation item, in an initializer that binds no name (`terms/init/item/..`, where
  a spelling's `x` is unbound) and in one whose configuration variable `x` the computation cell
  reads (`terms/init/variable-item/..`);
- the slots' roots: a fn's, an equation's, a simplification's, a context's and a static clause's
  whole subject, a `for KItem` clause's bare and in `k::term!` (`terms/sort-rule/subject-root-term/..`),
  a result's, a constant's and a computation item's (`terms/readable/item-root/..`);
- depth 2, a construct inside a position another construct opens (a set's element among them), at
  one host per kind (matched,
  evaluated, built, guard): `terms/sort-rule/result/let-body/Size(x)` is `Size(x)` as a `let`
  block's result in a `for Stmt` clause's result.

Besides the constructs of the product's table, the catalog applies the terms base's two static
productions, `Cmd::Dz()` (marked `#[k::desugar]`, expanding to `Cmd::Pair(2, 3)`) and `Cmd::Az()`
(marked `#[k::alias]`, to `Cmd::Pair(4, 5)`), at the matched positions of depth 1 below a subject's
root (`terms/desugar/subject/Cmd::Dz()`): the construct of NT-8-4 and NT-8 M2. A desugar's or an
alias's result root whose sort is not below its production's (a Bool, a String, a map, a `KItem`
term at a `Stmt` production) is the mistake `static-result-sort`, which `expected.toml` refuses
by the spelling's sort. The oracle reads
their application as the value it expands to (decision NT-14: a static application below a
desugar's or an alias's subject root expands when the expansion needs no value, as a ground
one's never does), KRS writes the expansion in the clause, and K7 runs it on a program writing
the application; `cargo test -p krs-test-support --test k7` names a static production the base
gains without a spelling. Below a static subject's root, which static expansion matches as
written, a construct that computes (a function's application, a collection literal that builds,
an index, a method, a sort test) would stand for its spelling rather than its value, and the
oracle refuses it with the class a pattern's has (decision NT-11-5); a collection of two or more
parts (a set's concatenation, a list of an element and a rest) is one of its spellings, since
static expansion neither reorders nor regroups parts (`collection-in-static-subject`).

The static subjects (`terms/{desugar,alias}/subject/..`) also hold spellings of their own
(`static_subject_spellings`): applications of the base's static productions whose expansion its
clauses decide, `Cmd::Dn(1)` (two clauses, one matching), `Cmd::Rc(1)` (recursive), `Cmd::Qb(..)`
and `Cmd::Tw(x)`, `Cmd::Tw(Cmd::Hold(x))`, `Cmd::Tw(y @ Cmd::Hold(x))` (one clause copying a plain
name), each with its expansion as its value and a counter-witness whose copies differ, and those
that stand for no one term (`Cmd::Dn(x)`, `Cmd::Tw(_)`, `Cmd::Dn(2)`, `Cmd::Lp(0)`, which never
ends, and `Cmd::Pb(Cmd::Go())`, whose expansion would apply a clause that is not recursive twice
on one path), the class `unexpandable-static-application`; alternatives at two arguments; and
Bytes tokens holding each character K escapes. Openers at depth 2 put the static applications
below a constructor, an alias and an alternative there (`terms/desugar/subject/or-branch/..`), and
`set-concat` a set's concatenation. Two slots of their own: `subject-typed`, a binder a typed
parameter restricts, the form `sort-test-in-pattern` advises there; and `subject-written`, where a
rule of the case's own writes the clause's production applied to the witness (`drive(N) =>
cNAME(1, w)`, `N` the case's own number), which kompile expands as it expands every rule, so a
term KRS writes must meet the subject KRS writes, or the definition does not build (K6). A static
subject's counter runs are programs its subject does not match, whose expansion must leave the
case's production unexpanded ("survived expansion", the status `unexpanded`); and the Bytes
witness `b"ab"` is also written `b"\x61\x62"`, one value, which the subject should meet and
does not, since static expansion compares token text (finding NT-14-2). The slot `terms/cells/result-map-framed/..` writes one key under two
spellings over the map a framed `cells!` subject leaves (`map![x -> 1, (x) -> HOLE, ..rest]`); the
slot `terms/cells/result-map-whole/..` writes an entry over a map the subject binds whole
(`map![x -> HOLE, ..m]` over `Cell(m)`, the form the class `framed-map-unmatched-key` advises),
and `terms/cells/result-map-framed-key/..` writes a key the framed subject does not match over the
remainder it leaves (`map![HOLE -> 1, ..rest]` over `map![x -> v, rest @ ..]`, finding NT-9-1 at a
key other than `x`).

A map key reads by its parent (decision D2): a key of a map in a pattern is evaluated, and a
pattern-only construct there selects an entry by matching the map's evaluated keys while a computed
one is looked up; a key of a map that is built is built. A position keeps every collection entry it
lies in (D4). The catalog covers every construct of the product's table, every notation form, and
the collection forms; `cargo test -p krs-test-support --test positions` fails, naming what is
missing, when a form of the table has no position, a slot of a form no root or argument case (but
the listed exceptions), or a construct, notation form or builtin operator no spelling.

The oracle is written independently of the product's position table (`krs_syntax::positions`),
which is written per position; `cargo test -p krs-test-support --test positions` compares the two
on every term case, and a case they disagree on must be pending.

A refusal of the oracle lies at the spelling, or at the entry (the outer construct's text) when the
refused construct is the one a depth-2 case's construct stands in.

**Size.** The term family is 5,063 cases, the import axis 172 and the attribute axis (`attrs/..`,
18 forms × 26 attributes, 26 malformed attributes and 20 extra cases, in the first shard of the
fast tier) 514, the run families (`readable-run/..` 194 and `cells-run/..` 193, in the first shard
of the fast tier too) 387, of 6,974 in all, and
the notation family (`notation/..`: the term family's positions, templates and oracle for the
collection notation, `m[k]`, `s.contains(x)`, `map![k -> v]` and `set![x]`, and the calls it
denotes) 2,862. The generator caps
each shard of the fast tier at `FRONT_CASE_CAP` (6,000), whose documentation argues the fast tier's
budget (7.5 ms a case single-threaded); the notation family and the term family are shards of
their own (`FRONT_SHARDS`), one test of `class_front` each. The full tier's `terms` shard takes about 5
minutes with 22 workers, its `notation` shard about 3, and its `attrs` shard about one. The accept
entries of the families the oracle judges (the term families and the attribute axis) are most of
the table, so they live in `accepted-terms.toml`, in `expected.toml`'s accept schema and written by
the same record mode; `expected.toml` keeps the classes, the refusal rules and the other families'
accept entries, and holds none of theirs (`class_matrix::table`).

The generator's own tests check that every base expands, that every case's ranges point at its
construct, and that both files parse:

```sh
cargo test -p krs-test-support --test class_matrix
```

## The full tier: gate `krs-class`

`scripts/krs-class.sh` runs every case through Cargo, rustc, the collector, and `emit-k`'s lowering
(`krs/crates/krs-cli/tests/class_matrix.rs`). The rule-level cases of one base share batch packages,
one command constructor per case; a rustc or collector error is attributed to the case whose text
holds it, a failure no case owns is bisected, and once a batch collects, each case is lowered from
the descriptors of the base and its own. A case is judged by

- K2: when refused, exactly one error, with a registered KRS code of the author kind (the registry's
  `CodeKind`; a rustc error forwarded as `krs::rust-expansion::uncoded-error` does not count), located (its
  primary range or one of its labels) inside the site the table's rule names (the entry by default), without a panic or an internal error;
  and the table's outcome: accepted with the K the table records, or refused with the code of the
  case's mistake class. The table covers every case: a new case needs its entry.
  At a position rustc parses as Rust before any KRS macro reads it (a `#[k::rule]`,
  `#[k::equation]` or `#[k::simplification]` result, a `#[k::function]` shorthand's body, a
  `#[k::constant]` value; the generator marks these slots), a construct rustc's parser refuses
  (`y @ P`) is reported by rustc whatever KRS does. There the refusal conforms with rustc's parse
  error (an uncoded rustc error) beside KRS's one error, both inside the construct, and K2 judges
  KRS's error alone. The front stops at the same parse error (`krs::expand::parse`) and leaves the
  case to the full tier. No other position has this rule (`class_matrix::invariants`);
- K1, once collected: every anchor of the case's descriptors lies inside the case's text, and no
  semantic key is found twice during lowering;
- K3, once accepted (initializers aside): each case emits the K of every case its `same_k_as`
  names, the documented equal spellings; and the accepted cases of a batch are printed together by
  `krs expand`, the printed source is collected again, and each case's own K sentences must be
  emitted again, byte for byte or after the normalization of `class_matrix/closure.rs`
  (alpha-renaming, `... </k>` for an explicit computation rest, `...` for a frame variable used
  once or `_` there, and the digest of a generated label). Each shard prints, per form, how many cases are byte-identical, equal after
  normalization, different, or refused in the printed source. `KRS_CLASS_CLOSURE=0` skips it;
- K6, once accepted (initializers included) and not refused by the table: the definition the case
  emits, its base and the case alone, passes the judgement `krs check` makes without `--backend`
  (`krs_cli::CollectedDefinition::check`, the function `krs check` itself runs): `emit-k`'s
  emission, every native route's capability table, `krs build`'s native compile on both backends,
  and on the `native-rust` route the definition load of `krs run`, `krs search` and `krs prove`.
  K6 asks whether any `krs` command can use the K KRS wrote: a case KRS accepts but a native
  route refuses cannot be built, run or proved, however good its K. A refusal or a panic is a
  deviation keyed `k6/<case ID>`. A refusal's signature is the refusing route or command, as the
  note `krs check` adds names it (`native-rust`, `native-llvm`, `every native route`, `load` for
  the definition load, `emit-k`), and the code of each error, for example `every native route
  IllegalFunctionOnLhs`. `krs check` reports a panic of one of its route workers as the uncoded
  error "a check worker panicked", before any route note, so its signature is `uncoded: a check
  worker panicked` and names no route (a panic in the definition load is reported, and signed,
  under the `native-rust` and `load` notes); a panic on the harness's own thread (lowering,
  emission, the capability tables) is `panic: <message>`. The TSV's `k6-refusal` lines hold each
  refusal's messages.

  The native compile of a base costs far more than a case adds to it (on 2026-10-30, about 2 s a
  check for the machine base, the case's lowering under 0.01 s), so the accepted cases of a batch
  are judged together, as one definition, when it is exactly theirs: its emitted sentences are the
  base's and each case's own, as each emits alone. A refusal is bisected, as a collection failure
  is, down to the case whose definition alone is refused; a batch whose cases lower otherwise
  together is judged case by case. Each shard prints how many cases K6 judged, in how many checks,
  and the workers' time they took. `KRS_CLASS_NATIVE=0` skips K6, and `KRS_CLASS_NATIVE=alone`
  judges every case alone, which must give the same verdicts. K6 compiles natively, so the tier
  links the Z3 release `Krs.lock` pins (`KRS_Z3_LIB`, or the Nix store);
- K7, once K6 accepts the case: the case runs, and its sentence applies, with the value the
  generator states. Accepted K is K some command can load; K7 asks whether it does anything, and
  the right thing: a rule that never applies, a program that cannot be expanded and a built term
  with another value all look accepted to K1 to K6.

  *The printed state is the state* (NT-23): K7 reads values structurally, so it also reads a
  conforming run's state back as `krs run` prints it: the computation cell's first item and every
  other leaf cell, each printed, parsed with the definition's grammar at the cell's sort with its
  aliases expanded again, must be the term the state holds, value for value, tokens by their text
  (`printed_reads_back`). The printer is the one the case has alone, the base's aliases and its
  own, so a verdict does not depend on the batch (`KRS_CLASS_NATIVE=alone` gives the same). A print
  with a KAST fallback is not read back, nor one that does not parse where the term printed without
  reversal does not parse either (the grammar has no syntax for part of it, `$x`). The terms base
  holds aliases for printing of each shape of clause (`ah`, `am`, `av`, `ac`, `bp`, `bq`, `ak`; see
  `DRIVER_BASE` in `class_matrix/terms.rs`).

  *Witnesses and values* (`class_matrix::k7`, the spellings in `class_matrix/terms.rs`) are
  generator data, stated from what each construct denotes, never from what KRS emits or runs,
  with the templates' binders at fixed values (`x` is 1): a spelling's *witness* is a ground term
  it matches (`Cmd::Hold(x)` matches `Cmd::Hold(1)`, `_` matches `0`), its *value* what it denotes
  where it is built (`x + 1` is 2, `map![x -> 1, 2 -> 3]` the map `{1 ↦ 1, 2 ↦ 3}`,
  `set![x, 1]` the set `{1}`, `k::matches!(x, Cmd::Hold(_))` false). A spelling with none says
  why (a computed term matches no evaluated term; a pattern builds nothing; `{ let y @
  Cmd::Hold(_) = x; y }` has no value at `x` = 1), and the openers compose them: the witness of
  `y @ HOLE` is the hole's, of `set::item(HOLE)` the set of it, the value of `Size(HOLE)` the
  unevaluated `Size` of the hole's (`Size` has no equation, so it serves as a wrapper the run
  shows the hole's value in; `Size(x)` itself has no stated value). A spelling a pattern reads
  also has *counter-witnesses* where they exist, ground terms it must not match (`Cmd::Hold(x)`
  must not match `Cmd::Pair(0, 0)`, `y @ Cmd::Hold(_)` neither): its case runs a program on each,
  which must stop before the case's sentence, so a pattern lowered too loosely is caught. A
  collection a pattern reads exactly has a counter-witness with an item more (`set::item(x)` must
  match neither `{}` nor `{1, 2}`, `map![]` not `{1 ↦ 1}`), and one it reads with `..` a witness
  with an item more than it writes (`[x, ..]` matches `[1, 2]`): so is the collection the hole
  stands in, where the slot leaves it open (a map read's `..`: the driver writes `{k ↦ 0, 99 ↦ 0}`;
  a list's, `[w, 99]`; a collection's other instances, added first) or reads it exactly (a set's
  singleton around the hole: a counter run on `{w, 99}`). So a lowering that reads an exact
  collection as open, or an open one as exact, does not run as stated
  (`every_term_collection_spelling_follows_the_rule`, the plans pinned beside it). A
  disagreement with KRS is a finding, triaged as an oracle or a product bug.

  *Drivers* (`class_matrix/terms/drivers.rs`), one per slot, write the program that applies the
  case's sentence and state the cells the run ends with. A rule's command is applied to the
  witness (`Cmd::NAME(x, HOLE)` takes `cNAME(1, w)` and ends with `hold(1)`) or read for its
  value (`cNAME(1, 0)` ends with `hold(v)`); a condition's value decides whether the rule
  applies, and a condition with no value at `x` = 1 (`{ let Cmd::Hold(_) = x; true }`) does not
  hold; a map key and a set's element, a Set collection's instance included, read as decision D2
  reads them: a computed one is looked up by its value (`set::item(int::add(x, 1))` takes
  `sone(2)`), a selection by its witness; a map key, a list or cons element and a collection's instance are first set up by the
  terms base's driver commands (`then(setenv(..), cNAME(1, 0))`), one step each at priority 10,
  so that no driver rule overlaps a case's; an equation's function is applied from the base's
  rules `call(a, b) => hold(probe(a, b))` and `sizeof(a) => hold(size(a))`; a context heats the
  token `word`, which is no `KResult`; a desugar's or an alias's subject is written in the program,
  which the run's parse expands, and its result read in the expansion; an initializer, of the
  term family or of the configuration families' `init` (the machine and typed bases, with `$PGM`
  bound to `go` and `-c ANY=1`), is read before any step, each cell's stated value compared. Values the program grammar cannot write (a map, a set, a list, `$x`,
  `Wrap::<KItem>(..)`) are written through the base's makers, functions that build exactly them,
  which a static clause's expansion meets unevaluated, so a witness only a maker writes is no
  witness for a desugar's or an alias's subject. Claims and simplifications need a prover (L4
  keeps claims in the fixture gates); a context alias acts only through a production strict in
  it, which neither the base nor a case declares; a `#[k::function(internal)]` shorthand and a
  constant have no program syntax and no base sentence can name the case's: these have no driver.
  Nor have the readable, claim and `cells!` families on the machine and typed bases, whose cells
  start at fixed values and which have no driver commands; the run families run the readable
  records and the `cells!` rules instead (claims stay a prover's).
  `cargo test -p krs-test-support --test k7` lists the spellings without a witness, a value or a
  counter-witness and the slots without a driver, with their reasons, counts every case's K7
  status (each skip reason, and the counter runs), and pins a plan of each driver kind.

  *The run families* (`readable-run/..`, `cells-run/..`, the shard `runs`) are the readable
  records' and the `cells!` rules' slot templates and spellings instantiated again on the run base
  (`Base::Run`, `class_matrix::machine::run_base`): the machine base's cells under the same names
  and declarations, a Set collection `shelf.bag` whose instances hold a map cell (`Obj { key: Int,
  m: Map }`), and driver commands that each set one cell up in one step, at priority 10, apart from
  the cases': `then(a, b)`, `skip`, `setpc`, `setstack`, `setenv`, `setret`, `setcounter` (one rule
  for a present optional cell and one, at 11, that creates an absent one, so the plans do not
  depend on how the cell starts), `dropcounter`, `addjob`, `addobj` and `pushjob` (a `Job` cell
  record as the computation's first item, as a readable result writes one), with the terms base's map
  and list makers. One slot list is instantiated twice rather than copied: each template writes
  the same item on both bases, so a spelling the family gains reaches the run base by
  construction, and the machine base's cases, and the K they record, stay as they are. A run
  case's *twin* is the machine-base case of the same slot and spelling: the table matches the
  twin's ID against the refusal rules (`table::twin`), so twins are refused alike, and each run case
  has an accept entry of its own, whose K is its twin's byte for byte (`cargo test -p
  krs-test-support --test class_matrix every_run_case_is_expected_what_its_twin_is` checks both);
  a twin of a pending case is pending under its twin's finding. The Set collection's spellings
  have no twin (the machine base has no Set collection): an instance whose map cell is exact
  (`map![1 -> 2]` in a readable record, a literal there; `k::map![1 -> 2]` in a `cells!` fragment,
  the cell's map), one whose key is computed, two whose exact map computes its value or its key,
  each looked up as the set's element (decision D1a, NT-10's review M1), one whose map reads an
  entry and leaves the others open (`{ 1 -> 2, .. }`, `k::map![1 -> 2, ..]`) and an instance record
  with `..` (`Obj { key: 1, .. }`), which select, and in a readable record the literal
  `map![1 -> 2, ..]`, whose anonymous rest names no map (the class `anonymous-rest-in-map-literal`,
  which advises the `{ 1 -> 2, .. }` case); on the result side, an instance written with each.

  Their plans (`class_matrix::config_drivers`) state what each spelling denotes in its cell. A
  subject case's witness is written by the driver commands before the case's command
  (`then(setpc(0), cNAME)`, three steps that leave the computation cell empty), or is the start
  configuration where every value is one (a binder, `_`, a group record of binders); each
  counter-witness, run apart, must stop before the command (`then(setpc(1), cNAME)` takes two
  steps). Exact and open, the rule: a spelling that reads a collection whole (`[]`, the map of
  `Obj { key: 1, m: map![1 -> 2] }`) has a counter-witness with one item more, and one whose `..`
  leaves items open a witness with more than it writes (`[x, ..]` on `[0, 0]`, `{ y -> x, .. }` on
  `{1 ↦ 0, 2 ↦ 0}`, `KCell(x, ..)` after `then(go, go)`, two jobs, the object 9 beside the one an
  instance spelling reads, and for `Obj { key: 1, .. }` a map that is not the template's): each
  subject plan states the collections it reads (`class_matrix::Reading`), and `cargo test -p
  krs-test-support --test k7 every_run_spelling_reads_its_collections_by_the_rule` checks the rule
  on the items its programs write (`RUN_READS`), listing the spellings that read no collection
  (`RUN_UNREAD`: a binder, `_`, a leaf, an optional cell, a one-child group's record). The
  machine base's groups and instances have one child, so a record's `..` is tested on
  `Obj { key: 1, .. }` alone. A result case's program first writes a value the subject's `old` matches and no result
  writes, then applies its command with `x` = 1 and `y` = 2 (`y` = 1 for a map whose two keys may be
  equal, whose later entry is the map's): `then(setpc(5), cNAME(1, 2))` ends with `pc = 1`. The
  computation cell's subject case holds no command, so its program is the witness (`go`, a
  computation with an item; `skip`, which empties it) and the run ends with `pc = 1`; its result
  case writes the computation after `then(cNAME(1, 2), go)`, whose `go` is the rest. A run reads a
  leaf by its path (`frame.ret`), a repeated cell by its instances' children (`queue.job[payload]`
  a List collection's in order, `shelf.bag{key,m}` a Set collection's as a set, each instance named
  after the collection), and an optional cell the state does not hold as `absent`. Claims stay
  without a driver (a prover's), and a spelling written in another kind's notation than its cell's
  denotes nothing there. `cargo test -p krs-test-support --test k7` pins each run family's statuses
  by reason and count (`RUN_STATUSES`), the cases without a witness, a value or a counter-witness
  (`RUN_UNSTATED`: a cell record behind the computation's first item, which no driver command
  writes, and one as a List cell's element, which a readable result reads as instances; `_` and an
  anonymous rest in a result whose subject reads the cell whole; `x`, an `Int`, at a cell of another
  sort; a map literal's anonymous rest; a binder, `_`, `..` alone or a record of binders, which
  every value matches), and a plan of each kind (`the_run_drivers_write_their_programs_and_cells`).

  The run families are a shard of their own, so the `readable` and `cells` shards hold the cases
  they held before. On 2026-10-31, at 15 workers under a load of 11 to 85 from other work, `runs`
  (387 cases, 77 accepted, 74 judged by K6 in 14 checks) took 61 s, with K7 (72 programs and their
  counter runs in 0.3 s of worker time) and without it alike, while `readable` took 64 s and
  `cells` 55 s, as before (66 s and 56 s). No case of the run families deviates at K7; their reds
  are their twins' (each pending under its twin's finding) and the Set collection's, NT-19-1 (a
  `cells!` result's map literal with an anonymous rest answers another code than a readable
  record's) and NT-19-2 (a readable record cannot read an instance's map cell with `..`, which the
  literal's refusal advises: K2 and K8). A lowering that reads an exact map cell as open, or an
  open one as exact, is caught by K7: forcing every exact instance map open turns the 4 exact-map
  instances red, at their counter-witness with an entry more; dropping every subject map's `..`
  turns red the 3 open maps of the `runs` shard's map and instance subjects and all 73 runnable
  `terms/{readable,cells}/{map-key,map-value}/..` cases (2026-10-31, in a scratch worktree).

  *Running*: where K6's check loads the definition the run commands load (on the `native-rust`
  route, `krs_cli::CollectedDefinition::check_visiting`), each accepted case's program is
  configured and run there exactly as `krs run` reads a file (`Semantics::configure`, then
  `Semantics::run`), on the compile K6 judged, and the run's verdicts are kept when the check
  passes; a case K6 refuses is not run. The run is bounded by the driver's step count, so a
  sentence that applies again to what it wrote is observed after its application, and by a time
  limit per program (`KRS_CLASS_RUN_SECONDS`, 60 by default), enforced by cancelling the
  backend's request: the program's configuration (its parse, the expansion of its desugars and
  aliases) and its run are one cancellable request (`k7_bounds_a_program_whose_expansion_or_run_does_not_end`
  shows an initializer that does not end giving a deviation at the limit). A panic of a run is its
  case's verdict, and the cases after it run on a definition apart. Each case's command is its own, so only its sentence can take its program;
  a sentence that holds no command of its own (a subject's root: a context's, an equation's, a
  simplification's) could take another case's, so where one shares K6's check with other cases,
  it and the others are run on definitions apart. The final cells are decoded
  (`StateView::value`) and compared with the plan's terms. A deviation is keyed `k7/<case ID>`:
  `not applied: N of M steps, then HALT; CELLS`, `no defined result: ..` (a sentence matched and
  its result has no value), `applied where it should not`, `counter-witness `PROGRAM`: ..` (the
  counter run's deviation), `failed: ERROR`
  (the program's parse or expansion, or the run), `time limit: ..`, `no configuration
  (\bottom)`, or `another value: CELLS, where the plan states CELLS`. Each shard prints how many
  programs K7 ran, in how much worker time, and what it checked of each case K6 accepted: a
  stated `value`, `liveness` only (a witness, or a value the generator does not state), or why
  nothing (`no driver`, `no witness`, `no value`). `KRS_CLASS_RUN=0` skips K7; without K6
  (`KRS_CLASS_NATIVE=0`) it does not run, and says so.

  *The twin check* (`class_matrix::twins`, keyed `twin/<case ID>`). A static clause's result is
  the term a program's expansion writes in place of the clause's production, which then evaluates
  as the same term in a rule's result does. So each case at a desugar's or an alias's result (its
  root, ground or not, or a constructor's argument there) has a twin, the case of the same family,
  openings and construct at a `#[k::rule]` fn's result, and where K7 ran both and the twin's run
  conforms, the static case's run must build the twin's value at the hole (the computation's item,
  or that item's last field: `hold(v)`, `pair(1, v)`), whatever the generator states: K7 judges
  each case against its own plan, so a construct whose static result is lowered or read otherwise
  shows there only where its plan states a value the static run misses (NT-12-1 and NT-12-2 each
  needed one), and a `liveness` plan (`Size(x)`) shows nothing; the twin check states the class
  once. A static run that deviates is a disagreement too. `cargo test -p krs-test-support --test
  k7 every_static_result_has_a_rule_twin_that_k7_runs_alike` checks that every static result case
  has its twin and that K7 runs both or neither, and pins the pairs neither runs by reason (a
  construct with no value at `x` = 1).

  K7 runs on K6's compile, so it costs its programs' runs (a few milliseconds each) and the
  checks apart: on 2026-10-30, 1,489 programs in the `terms` shard took 9.5 s of worker time and 2
  checks apart 4.1 s, 870 in `notation` 5.2 s, 99 in `import` 0.6 s and 1 check apart 2.2 s; each
  shard's wall time with and without K7 was within the noise of a loaded host (`terms` 356 s and
  364 s, `notation` 206 s and 205 s, at 15 workers).
- K8, the attribute axis and the advice check (`class_matrix::attributes`, `class_matrix::advice`).

  *Attributes × forms.* The `attrs` family (`attrs/FORM/ATTRIBUTE`, a shard of its own) writes
  every attribute an author can write on a sentence on every sentence form: each key of a
  sentence's marker (`#[k::rule(owise)]`, `#[k::equation(concrete)]`, `concrete(x)`,
  `#[k::claim(all_paths, trusted)]`, `#[k::desugar(unbound_variables = [y])]`, `heat, hole = x,
  result = Word`, ..) and each helper beside it (`#[k::requires(..)]` and `#[k::ensures(..)]`,
  each holding and failing, `#[k::exists(..)]`, `#[k::fresh(..)]`, the retired
  `#[k::priority(..)]`), each with a representative well-formed value, on each of the term
  family's 18 slot forms, written on the form's subject slot template with the marker's own keys
  removed; a few malformed values (a value of the wrong shape or range, a key written twice, an
  unknown key, a missing key) and keys that cannot stand together (`owise` with `priority`,
  `heat` with `cool`, ..); and 20 extra cases (`attributes::EXTRAS`, named by what they write): a
  helper before its marker, two conditions on one sentence, `#[doc]`, `#[cfg(all())]` and
  `#[cfg(any())]` on a clause, `recursive` on a static production's own marker, and `smt_lemma`
  on an equation, a table row and a simplification of a function the case declares with
  `smtlib`. The attribute list is read from the product: `cargo test -p krs-test-support --test
  attributes` scans every function of `krs-syntax/src/attribute/` for the literals it compares a
  key with (a match arm, `==`, `matches!`, directly or through a `&str` constant) and fails on a
  key no attribute of the axis writes (or the other way round), the functions that parse a
  declaration's keys listed apart; reads the attribute names the clause macros' takers
  (`k::rules!`, `k::claims!`, `k::equations!`) recognize, each a sentence macro the axis writes on
  a clause; and checks that the sentence macros of `krs_syntax::surface::AttributeMacro` are
  exactly the forms' markers and the axis's helpers, each written where the axis says. What each
  pair means is the oracle's statement (`attributes::means`), from what the attribute denotes on
  that kind of sentence; a refused pair is judged by K2 like any case (one author error, at the
  attribute), with the class the oracle states (`attributes::expected`), which names the mistake
  whatever the form it is made on (an order on a sentence chosen against none, `owise` on a
  simplification apart, a restriction outside a function, a key the marker does not take, ..).
  An accepted pair runs by K7 where its form has a driver, and the run shows what the attribute
  does: a condition or a postcondition that does not hold, and `symbolic` on concrete values,
  leave the sentence unapplied; `owise` beside a sibling at `priority = 60` applies where the
  sibling does not, and its counter run, where both match, shows the sibling's result; beside a
  sibling at `priority = 30`, `priority = 20` wins where both match and `priority = 40` loses
  there, opposite winners, so a key dropped from both sentences shows whichever way the tie
  breaks (`owise` has no such pair: an `owise` sentence never wins where its sibling matches);
  `heat` applies where its hole is no result (`word`) and not at `1`, `cool` the other way round,
  and `result = Word` turns that round (it heats `1`, no `Word`, and leaves `word`); an anywhere
  rule applies below `hold(..)` as the configuration is built; a clause under `#[cfg(any())]`
  does not apply; a label, `nondet` (beside a sibling of its group), a restriction, `ensures`
  that holds, an existential or a fresh value leave the sentence applying as its slot's driver
  states (`concrete` runs on concrete values only: what it restricts needs a symbolic run, which
  K7 does not make). The terms base's driver rules have priority 10, before every case's (20,
  40) and sibling's (30, 60), and match only the driver commands, which no case's sentence does:
  a case's priority neither shares a priority with them nor is applied after one of them at the
  case's command.

  *Advice.* Every class carries `advice`, reviewed against its messages: `"none"` where its
  refusal advises no rewrite, otherwise the cases that write what it advises, each an ID the
  table must accept or a template whose `{form}` is the refused case's form
  (`attrs/{form}/priority = 20`: the retired `#[k::priority(N)]` is advised, on each form, that
  form's own key), a list where the refusal advises different forms at different sites. What a
  refusal advises is read mechanically (`class_matrix::advice`), from its message and help lines:
  an advice verb in the imperative at a clause's start (`write`, `use`, `mark`, `replace ..
  with`, `move`, `drop`, `remove`, `state`, `split`, .., read whatever its case) and the code span
  of its clause (not one after `instead of`, `rather than`, `not`, or a `where` or `if` clause),
  an imperative after `or` being an alternative of the one before; the form a construct `is
  written` or `is written as`; how something `writes` a thing `as` a form; a help line's form
  after a colon at its end. The registry's summaries are read the same way (`--test attributes`
  fails on a class marked `none` whose code's summary advises a form). K8 judges, keyed
  `k8/<case ID>`: each case a class advises, on the forms where the table accepts it, which must
  be accepted, pass K6 and run as K7 states where it ran (`advice of CLASS: refused: ..`, `..
  K6: ..`, `.. K7: ..`); and every refused case, pending ones included, by what its KRS errors
  advise: a class marked `none` whose refusal advises a form (`CLASS advises none, and its
  refusal advises ..`, the backstop of the reviewed field); a class whose advised case does not
  exist or is refused on the refused case's form while the refusal advises (`CLASS advises ID,
  which the table refuses`); an advised case that does not write the form the refusal proposes
  (or writes the one it says to drop), compared up to whitespace, with `..` and one-letter names
  as placeholders, where some generated case writes that form (`CLASS's refusal advises `F`,
  which ID does not write`); a form no generated case writes is left to the reviewed field and
  printed `unchecked`, as is advice in prose; and a case the table accepts whose refusal advises a
  form (`refused where the table accepts, advising ..`). The unchecked refusals are pinned per
  shard and class (`UNCHECKED` in `krs-cli/tests/class_matrix.rs`; 480 on 2026-10-31, 440 of
  them in `terms`, and 484 and 444 since NT-14 refuses a sort test in a static subject, whose
  advice writes `where x: Sort`), and the case shards with none are listed (`NO_UNCHECKED`: `attrs`, `cells`,
  `import`, `readable`, `runs`): a shard whose counts differ, or that neither lists, fails, so a
  new class, or a message that adds advice no generated case writes, is reviewed before it is
  pinned.

  K8 costs its own shard and a scan: on 2026-10-31, under a load of about 20 to 80 from other
  work, `attrs` (514 cases, 139 accepted) took 85 s at 15 workers, K6 54 checks in 66 s of worker
  time; the advice check reads each refused case's errors and builds, once a shard, the own text
  of every accepted case to look a form up in, below measurement beside a shard's builds. The
  shards took `init` 75 s, `readable` 66 s, `cells` 56 s, `import` 65 s, `notation` 203 s and
  `terms` 351 s at 15 workers. Of the advice verdicts, 849 refusals follow their class's advised
  case and 480 propose only forms no generated case writes (`unchecked`, 440 of them in `terms`,
  mostly `notation-in-pattern`'s calls such as `int::bit_and(..)`). The optional cell written
  present that `none-in-initializer` advises has a base of its own (`Base::Initial`, the machine
  base with `counter` declared `initial`), so no other case's K moves.

The `k4` shard compares KRS's sort judges with k-rust's subsort relations of each base's emitted
definition; its disagreements are keyed `lattice/class-BASE/JUDGE~JUDGE/CLASS`, and those about
`KItem ≤ K` or a list's element are only counted.

The `k5` shard checks `class_matrix::entry_points`: one package that uses all 53 entry points of
`krs-macros`, and one mutation per entry point that breaks its header and keeps every dependent.
Each mutation must give exactly one diagnostic, an error, under `krs check --message-format json`,
and exactly one error under plain `cargo check`, whose warnings are counted and not judged: a
failed item leaves its imports unused (`unused_imports`), which no proc macro can avoid without a
second error, and which `krs check` relays away. Its entry is keyed by the mutation,
`entry/attribute/cell`.

Run one shard (`readable`, `cells`, `runs`, `init`, `terms`, `import`, `notation`, `attrs`, `k4`, `k5`), and choose the worker count yourself
when the default (from the available memory, 3 GiB per worker) does not suit:

```sh
scripts/krs-class.sh --shard cells --workers 4
```

To iterate on a few cases, run the test directly with a glob over case IDs, and write one TSV line
per case and verdict to a directory:

```sh
z3=${KRS_Z3_LIB:-$(ls -d /nix/store/*-z3-4.12.5-lib/lib | head -n 1)}
LIBRARY_PATH=$z3 LD_LIBRARY_PATH=$z3 KRS_CLASS_FILTER='readable/result/pc/*' KRS_CLASS_OUT=/tmp/class \
  cargo test -p krs-cli --no-default-features --features z3-inference --test class_matrix -- --ignored readable
```

K6 judges with the sort inference `krs check` uses, Z3's, so the test refuses to judge K6 when it
was built without `z3-inference`; `KRS_CLASS_NATIVE=0` runs the other checks without it.

## Recording the accepted K

An accepted case's K, the sentences it adds to its base after K3's normalization with the case's
tag written `TAG` (for an initializer, its `configuration`), is written by the record mode, never by
hand:

```sh
scripts/krs-class.sh --record --shard readable --shard cells --shard runs --shard init --shard terms --shard import --shard notation
```

It writes `k` for every accepted case that the table does not refuse (the oracle included),
creating its `[accept."ID"]` entry if needed, and keeps `same_k_as`. Review the change to
`expected.toml` as a diff: a changed K is a changed emission.

## Pending entries

A case that deviates fails the suite until `pending.toml` records it, keyed by the test and the case
(`readable/result/pc/None` for K2, `k1/..`, `k3/..`, `k6/..`, `k7/..` and `k8/..` for K1, K3, K6, K7 and K8), with the finding that owns it (`unassigned` while none does) and the
deviation exactly as the harness prints it. `KRS_CLASS_OUT` writes the entries of every unrecorded
deviation to `<shard>.pending.toml`, with `finding = "unassigned"`, for review. A pending case that
conforms, or deviates differently, also fails: remove its entry, or record the new deviation.
