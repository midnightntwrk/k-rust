# DONE-0: the definition of done for KCore and KORE in K, and the order of the remaining work

Fable design agent, 2026-11-15; revised twice the same day after the cold review `findings/REVIEW-DONE-0.md` (27 findings, then its section 8 re-check with N1 to N7; section 7 answers each). After this round the document is the plan.
Read-only; nothing was built or run (no lean, lake, kompile, jj or git change).
Written for a reviewer who has not followed the history: every claim names its place, and section 6 lists what was not read.

Marks: **shown** = by reading the quoted place; **suspected** = follows from text read but rests on something not read or not run; **proposed** = a name or file that does not exist yet and that this document asks for.
Criterion numbers C1 to C13 are those of the first version; C14 is new.

## 0. Trees, paths, vocabulary

| Name | What | Where it is recorded |
|---|---|---|
| `T_R1` | released tree `c68b1a1a` | `core-manifest.toml` `[tree].commit` (shown) |
| `T_INT` | integrated, not released: workspace `kcore-merge` at `296a2aeb` | ticket file, `[resume].found`, entry "PICK UP HERE (written 2026-11-15" |
| `T_HLC` | workspace `kcore-kinds` at `1e306534` (HL-B, HL-C); lane CE runs on it | `[resume].found`, entry "2026-11-15 HL-C done and reviewed" |
| `T_R2` | the freeze tree; does not exist yet | to be `[tree].commit` after node R2; `[tree].frozen_at` (proposed) lists it and every later re-freeze (section 2.6) |
| `T_DONE` | the tree at which section 1 is checked; does not exist yet | `[tree].commit` at completion |
| `KS` | the library: `<worktree:kcore-merge>/draft-personal/k-semantics-core-2026-11/kcore-spec` | `core-manifest.toml` `[tree].path` |
| `KK` | `krs/semantics/kore/` on k-rust git `main` (`38cac354e` today): `kore.k`, `README.md`, `cases/`, `MUTATIONS.toml`, `kill-matrix.json`, `kink.lock` | |
| `K` | K 7.1.337: `k/result` (installed), `k/` (source checkout, `4a46d12314`) | |

Every Lean, lake or kompile command runs under the wrapper of the scratchpad `RULES.md` (`LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout <secs> …`, through `test/lake-serial.sh`).

`H` is a hook interpretation (`HookParams`); `c.withHooks H` the semantics at it; `HookParams.none` the member that gives nothing.
A **failing-clause point** is an argument list at which every clause of a function fails; a **silent point** a hook argument list keyed in `silentTable`. At both, `Γ (c.withHooks H)` states H's value (`findings/REVIEW-RN-reading-notes.md` section 0).
`k` is a KORE text as a Lean value (`Kore.Definition`), `d` the reader's result (`Parse.parse k = .ok d`), `c := d.sem`.
`tr s` is the translation of a sentence `s` of `k` as written (`KoreAML.trAxiom`, `KcoreSpec/Kore/Translate.lean`: "The translation of a KORE definition into an AML theory Γ_D", shown). `Γ c` "reads no presentation and no KORE text" (`KcoreSpec/Faithful.lean` header, shown). So `tr s` and `Γ c` are two independent routes from the text to matching logic; C14 compares them.

**The defect this document is built against** (REVIEW-RN findings 1, 8, 15): a reader reading (`ensuresAsRequires`) was justified by a fact a later change removed; a test proved the wrong value `half(-4) = 7` as its expectation; every statement of the reading's justification was made at the parsed `c`, where the change is invisible by `rfl`; coverage was measured on what `kore.k` contains. The cone was right and every check was green.
Each criterion carries the way it can be green while KCore is wrong and the check that closes that way. Where nothing closes it, the text says "not closed, stated limit".

**Trusted base, stated once.** (1) Lean's kernel and its three axioms. (2) The KORE text parser (`kore-lean`), which gives `k`. (3) kompile 7.1.337 for K-level rows: KCore's anchor is "what the KORE text states" (RULES "Correctness"), so that a K construct has the manual's meaning *in KORE* rests on kompile, with the row's fixture as evidence. (4) The builtin files' prose for hooks, which have no defining KORE sentence (C2), the prose also where a KORE sentence about a hook contradicts it: builtin prose over attribute where they conflict. The one known case is the text's set idempotence sentence (`_Set_(K, K) = K`, attribute `idem`) against `domains.md`'s "the sets are nilpotent"; Γ refutes the sentence (`idem_refuted`), which is recorded, not a failing C14 theorem (TIE-1 D5, owner direction 2026-11-15). The reader (`Parse`) is in the trusted base only where C14 says the tie is not established.

## 1. DONE

Fourteen criteria. C1 to C4 coverage, C5 to C8 robustness, C14 the tie to the text, C9 and C10 the two rows, C11 to C13 coherence and hand-over.
"Met" means: at `T_DONE`, by the stated check, re-run in the completion gate (C13).

### C1. The enumeration of K constructs is complete by extraction

**Scope (reading R-1).** A *K construct* is anything a K author writes in a module, or an option the author kompiles with, that kompile turns into, or uses to change, a sentence of `definition.kore`: that is, anything that can change the theory `Γ` or the relation `Step` of the kompiled definition. It includes what backends use only symbolically when it is or changes a sentence of the theory: `[simplification]`, `smt-lemma`, `concrete`/`symbolic`, `non-executable`, `?X`, `ensures`, `#Ceil` and the other matching-logic syntax in rule bodies.
Outside the scope, as one class `use` with status `inert` and one stated reason each ("a use of a definition, not part of its meaning"): proof tasks (`claim` as a sentence to prove, `trusted`, `one-path`/`all-path`, prover options), solver encodings (`smt-hook`, `smtlib`), and parsing or unparsing of programs (`prefer`, `avoid`, `format`, `color`, parser-generation options). These keys are still rows (so the extraction stays total); their status is `inert` or `erased` with evidence as any row.
A claim is therefore `inert` in a definition, as the reader has it (`InertReason.claim`, `Parse.lean:185`), and separately is the input language of the consumer, checked by C9 part 5.
Reason: the headline statements are about `Γ c` and `Step c`; a C2 status for proof tasks would need KCore to define validity of reachability, which no row needs and no cone root holds.
Reverse when: the owner asks KCore itself to state what a claim means; then `Reachability.lean`'s definition becomes a root before R2 and `claim` × {`trusted`, `one-path`, `all-path`} become `supported` rows.

**The eight lists.** K-level lists (E1 to E3, E7, E8) say what an author can write or switch on; KORE-level lists (E4, E5) say what the reader can meet; E6 is the library. Each alone misses a known class.

| List | Authority | Extraction unit |
|---|---|---|
| E1 sentence kinds | `k/k-frontend/src/main/javacc/Outer.jj` | the alternatives of `Sentence` (lines 741 to 765), `Production`, `ProductionItem`, `PriorityBlock`, `Require`, `Tag`, `imports` with `public`/`private`, by a pattern named in `extract.sh` |
| E2 attributes | `k/k-frontend/src/main/scala/org/kframework/attributes/Att.scala` (91 `Key.builtin` + 49 `Key.internal`; each with `onlyon[…]` and a `KeyRange`) | key × KORE sentence class as `ModuleToKORE` emits it (rewrite rule, function equation, simplification, symbol, sort, …), restricted by `onlyon` and `KeyRange.WholePipeline`; a key whose parameter kompile matches against a closed set (`multiplicity`, `type`, `stream`, …) has one row per value; a key with an open parameter (`strict(n)`, `priority(n)`, `simplification(n)`) has one row whose fixture set names the cases the reading distinguishes (for `priority(n)` and `simplification(n)`: below, at and above the defaults 50 and 200); `FrontendOnly` keys are rows with status `erased` |
| E3 rule-body syntax | the inner grammar kompile builds for a rule (`RuleGrammarGenerator.java`), for one module importing every builtin module; `kast.md`'s 62 `syntax` lines are part of it, not all of it | one row per production, including the generated ones (casts `makeCasts`, sort predicates, record productions, list terminators); a token production whose regular expression has alternatives of different meaning (`kast.md:206`: `!X`, `?X`, `@X`, `_`) is split into named rows and the split is recorded so it can be recounted |
| E4 KORE grammar | `haskell-backend/docs/kore-syntax.md` | one row per production; and the constructors of the reader's KORE syntax tree |
| E5 emitted shapes | `k/k-frontend/src/main/java/org/kframework/backend/kore/ModuleToKORE.java` | every `sb.append` site that writes `axiom`, `claim`, `alias`, `symbol`, `sort`, `hooked-`, by line; sites merged into one row only by a recorded statement |
| E6 builtin library | every file of `k/result/include/kframework/builtin/` | from the kompiled text of one module importing all of them, sentences grouped by builtin `Source`: every hooked sort and symbol (unit: the hooked **declaration**, keyed by hook name then symbol or sort name, so two symbols sharing a hook name are two rows; `smt-hook` excluded; the review counts 318 occurrences and 316 distinct names, K-coverage 317: the unit is fixed here so the recount can agree), every unhooked symbol, rule and lemma, one row per library module saying how the registry stands for its text, one row per token sort for its literal forms and how a `\dv` string is read |
| E7 compile passes | `KoreBackend.steps` (the composed pass names; `k/k-frontend/src/main/java/org/kframework/compile/`, 45 files) | one row per pass in pipeline order, naming the E1 to E3 rows it consumes and the E5 shapes it produces; a pass that consumes no row (cell concretization, implicit `<k>`, constant folding) is a row of its own |
| E8 kompile options | `KompileOptions.java` and the option classes it includes | one row per `@Parameter` name; `inert` with two equal kompiled texts, or a row with status |

**Option set (reading R-12).** The rows are stated for kompile 7.1.337 with default options and `--backend haskell`. A text kompiled otherwise is not what DONE speaks of unless an E8 row supports that value.

**Check.** (proposed) `KS/test/constructs/extract.sh` writes the eight key lists from `K`; `KS/test/constructs/rows.toml` is the table; `KS/test/constructs.sh` fails unless the key sets are equal, list by list, and prints the eight counts. E4 has a second check in Lean: a function from the KORE syntax tree's constructors to a row key with no wildcard case.

**Green while wrong.** (a) The script extracts less than the file holds. (b) A meaning carried by a combination of rows. (c) A construct in no list.
**Closed by.** (a) the gate recounts each list by a second method: E2 by counting `final val` declarations in `Att.scala` (one-line and multi-line) against the `Key.builtin|Key.internal` count, and the manual's "Attributes Reference" used the other way, as a list of keys that must each be in E2; E6 by `grep` of `hook(` in the source files against the kompiled text; E5 by K-coverage Part B's 58 rows each mapping to a site; E7 by the directory listing of `compile/` (a file used by no step is explained). (b) C3. (c) C13's duty to draw three constructs from K's sources, not from `rows.toml`. Beyond that: not closed, stated limit; and DONE is per K version (R-10).

### C2. Every row has a status with evidence, and none is "not handled"

**Statuses.** `supported`, `parameter` (numbered, uninterpreted, theorems for every H), `inert` (no meaning in the semantics, with the reason), `erased` (kompile leaves no trace in `definition.kore`), `refused` (the reader stops with a named reason). A K-level row names the E4/E5 rows its KORE consists of. K-coverage's `not handled` (128 of 441 rows at 2026-11-13) is not a status at `T_DONE`.

**Refusal reasons, two headings.**
- *Refused on principle*: (R-a) outside the fragment by a recorded decision, with its place (sort-parametric symbols, Q11); (R-b) the option value or text form is outside R-12.
- *Not supported at this freeze*: (R-c) the kernel has no notion for it, naming the notion **and the cone declaration that would change**. R-c is admissible only where a named cone declaration would change: a construct readable with no cone change cannot be refused by R-c (reading R-11). The count of R-c rows is compared by the gate with TRIAGE's list.

**Evidence per status** (proposed `KS/test/constructs/fixtures/<row>/`):

| Status | Evidence |
|---|---|
| `supported` | a minimal K text, its kompiled KORE `k`, `kcore account` with nothing refused, and the tie of C14 on `k`: every sentence of `k` in the direction its class has, for every H. The fixture's value or step theorem, where one is stated, is **derived**: its expected side is a consequence of the `tr s` named by sentence index (a Lean proof from them, C7), not a value somebody wrote. Floor: where layer 2 of C14 is not established for the row's class (decision point TIE-decision, section 2.1), a value or step theorem is mandatory for the row |
| `supported` hook (E6) | three statements: one in-domain value; for each region the builtin file's prose excludes or leaves unstated, the `param_undetermined` shape at a point of it; and the statement that the hook's silent predicate in `silentTable` is that region. A hook with no silent key says why the prose covers every argument list. The expectation here is from prose (trusted base 4), cited by file and line |
| `parameter` | the `param_undetermined` shape (REVIEW-RN section 3, G6): over all H, Γ entails neither ⊥ nor a value |
| `inert` | the reason, and C14's statement for its class (`Γ c ⊧ tr s`: reading it would add nothing), or for class `use` the reason of C1 |
| `erased` | two kompiled texts, with and without the construct, equal after removing `Source`/`Location` |
| `refused` | a minimal K text whose `kcore account` prints exactly the named reason; the reason sentence |

**Check.** `KS/test/constructs.sh`: for every row the status is one of the five, the evidence files exist, the fixture's `kcore account` output equals the recorded one, the named theorems are in a module built by `test/integration.sh` and covered by C5 part 2.

**Green while wrong.** (a) The guard is written by the lane that wrote the reading. (b) A `refused` fixture hits the refusal while another shape of the construct is silently read. (c) Everything refused. (d) One fixture per row misses the case that matters.
**Closed by.** (a) C14 and C7: the expected side is the translated text, not an author's belief; C8's reader mutants are run. (b) C4. (c) R-11's rule on R-c, the floor of C9 and C10, and the count in the completion report. (d) for hooks the three statements above; for E7 passes one fixture per case the pass distinguishes (named in the row); otherwise not closed, stated limit, with C13's draws as the sample.

### C3. Interactions of meaning-carrying modifiers are enumerated, not remembered

**Definition.** The unit is an unordered pair over (symbol attributes ∪ sentence attributes ∪ body features) of one symbol's sentences. The set of modifiers is **computed from the text**, not from the reader: a row is a modifier when the kompiled KORE of its fixture differs from the fixture without it in any user-module sentence after removing `Source`/`Location`, or when the generated `Semantics` differ in a field of `Clause`, `Rule` or `Fn` (native diffs; no judgement). A text difference with no `Semantics` difference is a visible row that must be `inert` with a reason or a finding: it is the case of an attribute the reader drops silently, which a `Semantics`-only diff would compute as "not a modifier".

**Check.** `rows.toml` holds one row per pair, with a C2 status and evidence, or `independent` with the two declarations that read them. For the **core pairs** no `independent` is accepted and each has a fixture: the ten pairs among {`requires`, `ensures`, `priority`, `[owise]`, `[total]`} for equations, the same five for rules where they exist, and hook × equation (a hooked symbol with equations: `hooksApart`'s comment in `Tie.lean`, "Evaluation reads such a name as the hook … whatever the definition declares", shown), `[owise]` × `[simplification]`, `simplification` × `priority`, `anywhere` rule × constructor.

**Green while wrong.** `independent` is asserted; triples are not covered. **Closed by.** The core pairs; for the rest and for triples: not closed, stated limit; the gate samples three triples.

### C4. The reader is closed-world

**Check, three parts.**
1. Every constructor of `RefusalReason`, `InertReason`, `UnreadReason`, `ReadingNote` in `KS/KcoreSpec/Parse.lean` is named by at least one row, and every row's reason is such a constructor.
2. The reader holds an enumeration of the E2 keys whose `KeyRange` reaches KORE and a function from (KORE sentence class × that enumeration) to {read, inert with reason, refuse} written with **no wildcard case**; an attribute name outside the enumeration is refused with a reason naming it. `constructs.sh` checks the enumeration equals the E2 rows. Today a rule's attributes other than five are kept as pairs, neither classified nor refused (`Parse.lean:1053-1057` at `1e306534`, per the review; shown there). kompile rejects an unknown key (`CheckAtt.java:81-85`), so a made-up key is a test of hand-written KORE only; it is kept as that.
3. Over the corpus `~/.cache/k-rust/reference-outputs/v1` (381 texts), natively: `unaccounted` = 0; `inertMismatch` = 0, or the row key of each mismatch is printed and the gate reads all of them; every refusal's reason maps to a row.

**Green while wrong.** A catch-all reason stands for constructs never decided. **Closed by.** A row may cite a catch-all only with its own reason sentence and fixture; the script lists the rows per catch-all and the gate reads the list.

### C5. Statements pinned; axioms checked everywhere; the cone frozen at R2 with the right roots

**Check.**
1. (proposed additions; work, node PINS) `KS/test/Pins.lean` pins by text, beside what it pins at `1e306534` (`SoundC`, `CompleteC`, `StepIs`, `StepFn`, `FnHyp`, `coreOK`, the types of `sound_hyp`, `complete_hyp`): `sound_at`, `complete_at`, `consistent_of`, `StepDecided`, `FnDet`, `FnSolves`, `Consistent`, `run_exact`, the C14 statements, and the row statements of C9 part 5 and C10 part 2.
2. The `collectAxioms` loop of `KS/test/Axioms.lean` (today restricted to modules named `KcoreSpec.*`, shown by the review) also ranges over `test/Guards.lean`, every fixture module and every declaration of both row packages: no axiom beyond `propext`, `Classical.choice`, `Quot.sound`. The grep for `sorry`, `native_decide`, `axiom` is kept as a tripwire, not as the check.
3. Roots (node ROOTS, before R2): the root list is computed by `#review_cone` from **every statement C9, C10 and C14 require**, decided once. Whatever is deliberately left out is named with its reason in the manifest: `Parse.parse`, `Definition.emit` and `wf` are left out (R-15: the tie is re-proved by the kernel on each text at `T_DONE`); candidate: the executor behind `run_exact`, if it is to stay a convenience. `core-cone.txt` at `T_DONE` equals the last entry of `frozen_at` **by text of the declarations** (today `test/integration.sh:12-13` compares names and line counts).
4. `core-manifest.toml` has no `status = "provisional"` row (nine today: lines 44, 45, 46, 74, 75, 76, 112, 133, 134). A row that is relabelled rather than resolved carries what a `refused` row carries: the `rows.toml` keys it leaves `refused` or `parameter`, or the sentence "no construct depends on it" checked by the gate. `constructs.sh` checks each relabelled row names a key or that sentence.

**Green while wrong.** (a) A pinned statement is vacuous (false hypothesis, or `Γ c` without a model: `Sound.lean:59`, "true vacuously when `Γ c` has no model"). (b) A definition under a pinned statement changes meaning. (c) A hypothesis stronger than needed excludes definitions the text gives a model (REVIEW-FA findings 4, 5).
**Closed by.** (a) C9 part 3 and C10 part 8 require `Consistent` for both rows; C8 part 2. (b) part 3. (c) for the two rows: C9 part 3 and C10 part 8, found before R2 by node KK-spike; in general: not closed, stated limit.

### C6. Every reading that is not the written sentence has a guard stated for every H

**Definition.** A *reading*: every constructor of `ReadingNote`, `InertReason`, `UnreadReason`, and the four un-noted ones of REVIEW-RN finding 7 (the rule axiom's `⌈rhs ∧ ens⌉` premise, a key function read as a `requires`, the priority form of a function's equations, `[owise]` as priority 200), each given a `ReadingNote` or a table entry. The plain `read` path is C14's.

**Check.** (proposed) `KS/test/Guards.lean` with a table from reading to theorem; each theorem quantifies over `H`, **uses it** (the statement mentions `c.withHooks H`), and has a companion showing the point is reached: an H at which the unguarded reading differs (the `gamma_H7` shape). A reading with no value at stake names the reader test that guards it. The invariant each guard cites is named, so weakening it breaks the guards. Minimum content from REVIEW-RN section 3: G1/G2, G3 or the finding that voids it, G4 per inert lemma class, G5, G6, G7, `rest_undetermined`. A script checks every constructor has an entry.

**Green while wrong.** (a) A guard on one fixture, the reading wrong on another shape. (b) A reading added without a constructor.
**Closed by.** (a) the library-level form where the kernel can state it (`eval_noValue_of_ens_fails`) and C14 on every fixture of the reading's rows. (b) C14 on every fixture: a reading that is not the sentence fails `tr s` in its class's direction whether or not it has a constructor.

### C7. No expectation is taken from a run, or from a memory of runs

**Rule.** The expected side of a fixture is a **derivation from the translated text**, in one of three forms recorded in the row:
- (a) the sentences of `k` that determine it, by index, and a Lean proof of the statement from a premise set made of (i) sentences as written, for the classes whose direction is E by equality; (ii) for a W-class sentence, Γ's item together with the W1 theorem that the sentence entails it and the equality of the item minus the added premise with the sentence (`rule_text`); (iii) families, each named in the row; with a model of the whole premise set (TIE-1 D6). The row records which kind its expectation is: **from sentences** (a defined value, a step that exists; the rule enters as the instance of the written sentence at the matched values), or **through the reading** (no value where an `ensures` fails, no successor, an exact successor set: these use `Γstep` or the premise `⌈rhs ∧ ens⌉` and cannot follow from the text's sentences); the second kind is form (a) counted apart, naming its family. No form (a) theorem is stated under `FnShape` or a hypothesis of that kind;
- (b) where (a) is not feasible for a fixture: the derivation written step by step in matching logic, each step checkable by the gate, marked `by hand` in the row and counted;
- (c) "the text's sentences entail no value here", with the pair of models that shows it (`param_undetermined` shape).
The manual is cited for K-level rows only, to say which KORE the construct should become. Hook rows cite the builtin prose (C2). A run of KCore, of `kore.k` or of a backend is evidence with implementation and version, never the expectation.

**Check.**
1. Lint (proposed `KS/test/provenance.sh`): a theorem under `KS/test` whose statement mentions `Eval`, `Step` or `⊧` at a concrete definition and is named as a row's evidence must use `H` in its statement and carry form (a), (b) or (c). A theorem in a namespace or file named `AtNone` is allowed to exist and is **never** a row's evidence. REVIEW-RN section 2's theorems are restated (8a, 8b) or moved to `AtNone` (9a to 9c, 10).
2. `kcore agree` prints per case whether the run read the interpretation (`Cert.evalTC` beside `evalT`); flagged verdicts are `agree-at-none` / `differ-at-none`, outside the totals (D-RN-1).
3. For what stays hand-derived (form (b), hook prose, the consumer's expected statement of C9 part 5): written by a review agent before the implementing lane's proof, in a separate commit.

**Green while wrong.** Form (b) and hook prose are still an agent's derivation and can carry a shared belief. **Closed by.** Their count is reported; the gate re-derives three. Not closed beyond that, stated limit. Whether form (a) is feasible is node TIE-spike's result, and what follows from it is a **named decision point before R2** (TIE-decision, a Fable design, not an owner question): form (a) throughout; or (a) for named sentence classes and (b) for the rest; or (b) throughout, in which case R-14's reversal fires there, `[goal].statement` is reworded to name the reader and the hand derivations as trusted base before any FIX-core lane starts, and a value or step theorem becomes mandatory for every `supported` row (C2).

### C8. The checks themselves are tested

**Check.**
1. Reader mutants are **run**: for each core pair of C3 and each `ReadingNote`, a named change of the reader (first: `ensures` read as a `requires` conjunct), built natively, on the row's fixture, must change `kcore account`'s output, or the row's theorem module is checked against the regenerated fixture and **must fail**, the failing declaration being recorded (a fixture is minimal, so this is one small kernel run per mutant). The refutation instance at an H other than `none` stays as the explanation. Only kernel mutants (a change of `Eval`, `Step`) are shown by argument, through the refutation instance. (proposed `KS/test/constructs/mutants.toml`)
2. Hypothesis witnesses, **before R2**: for each conjunct of `coreOK` and each of `FnDet`, `FnSolves`, a kernel-checked definition that meets the others and whose Γ has no model, or the conjunct is removed (a cone change, hence before R2). The manifest names four witnesses and two conjuncts without one (lines 131, 133, 134).
3. `KK/MUTATIONS.toml`: every mutant killed, or marked equivalent with the argument; each names the premise it breaks. Today 66 of 67.

**Green while wrong.** The mutant list is drawn from known defects. **Closed by.** Its minimum is tied to C3's core pairs; the gate adds three reader mutants of its own, run as in part 1. Otherwise not closed.

### C14. The tie: what a package's `Semantics` says is what the KORE text says

No other criterion relates `c` to `k`: C2, C6, C9, C10 are theorems about the reader's output, and the reader is outside the cone, the pins and `Axioms.lean` (manifest `[not_core]`: "the reader (Parse) and the tie to the KORE text: trusted only when a definition is read without the tie"; `[goal].scoreboard_state`: imp "untied"; shown).

**Check, two layers.**
1. *Layer 1 (amended by TIE-1 D2).* For a text whose print-back is not the text up to order (every kompile text): (i) `wf d = true`, or `coreOK` with the failing `wf` conjunct named, kernel-checked on the literal `d`; (ii) **the account**: one kernel decision per text that the class lists of the tie file partition the user module's sentences, each class then having its theorem over its own list or being a remainder class with its count; (iii) **attribute agreement** `attrsAgree k d = true` by `decide +kernel` (a new pinned statement reading neither `parse` nor `emit`: `constructor`, `function` with read equations, `hook`, a hooked sort's `unit`/`element`/`concat`, and every rule's and equation's `priority`/`owise` agree with `d`); (iv) `Tied k` stays the form for a text where it holds (krust-written texts marked `exact`) and is not required of a row. `Parse.parse k = .ok d` is not stated. The text below is the earlier layer 1, kept for the `exact` texts: *Syntactic.* `Tied k` (`KcoreSpec/Tie.lean:193`: `parse k = .ok d`, `wf d`, `Reordered d.emit k`) is kernel-checked for every C2 fixture and for both rows' texts. Where `wf d` fails on a conjunct `coreOK` does not ask (K-coverage: 5 corpus texts meet `coreOK` without `wf`), the failing conjunct is named and `parse k = .ok d ∧ Reordered d.emit k` is stated without it; `constructs.sh` compares the named conjunct against `coreOK`'s conjunct list by script and fails if `coreOK` asks it. `Tied` is re-proved by the kernel on each text at `T_DONE`; that is what makes the reader need no trust and no freeze (reading R-15: `Parse.parse`, `emit`, `wf` are left out of the roots). This layer certifies `emit ∘ parse`, not meaning: a reading "not as written" is tied whenever `emit` prints the written form back.
2. *Semantic.* For every sentence `s` of `k`'s user module, by its class, one of the following holds **for every H** (the class-to-direction table is node TIE-design's product and is pinned):
   - *entailed*: `Γ (c.withHooks H) ⊧ tr s` (KCore states at least the sentence). Default direction for function equations, constructor and subsort axioms, collection laws, and for every `inert` class (that is what "inert" claims);
   - *weaker, with its note*: `tr s` entails the item `Γ` holds for `s` (the rule axiom with its added premises, REVIEW-RN finding 7), named by a `ReadingNote`;
   - *more, with its note*: what `Γ` adds that no sentence states (priority negations, `Γstep`, `ΓFallback`, the domain axioms): each is a C6 reading with its guard, and at an open point the `undetermined` statement shows `Γ` over all H entails nothing there.
   Stated **per text on the literal `d`** (the generated `Semantics` value), never as a theorem quantified over `parse`: a statement that mentions `Parse.parse` would put the whole reader in the frozen cone while reader lanes still run after R2 (R-15).
   - *Converse, over Γ's content*: for every item of `fnItems c` and `ruleItems c` (`ΓFns` and `ΓRules` are `itemsPremises` of these lists, `Faithful.lean:518`, `:553`): the translated sentences of `k` entail it, or it belongs to a family of the pinned table with its `ReadingNote` and C6 guard. For the parts defined by predicates (`ΓSig`, `ΓCons`, `ΓDomains`, `ΓColls`, `ΓFallback`) the families are rows of the table, and the R2 gate reads the table against `Γ`'s seven parts (`Faithful.lean:561`), so that the list of what `Γ` adds is the definition's, not an author's. Whether the converse is statable is TIE-design's to find; if not, it is the stated limit (d) below.
   On the defect: the sentence `half(N) = N /Int 2 ∧ (N >=Int 0 = true)` is not entailed by `Γ (c.withHooks H7)`, which holds `half(-4) ≡ 7` (`gamma_H7`): the *entailed* check fails without anyone having to know the right value.
3. *For the rows.* Layer 2 for every sentence of kimp's and `kore.k`'s user modules, per sentence class with the count of sentences covered; what is not covered is listed, and for that remainder the reader is trusted base and `[goal].statement` says so.

**Feasibility is not known.** REVIEW-RN G4 writes one statement of this shape (`KoreAML.itemsPremises [KoreAML.trAxiom [] [] ⟨0, "lemma", ax⟩] φ → Γ (c.withHooks H) ⊧ φ`), not run. `trAxiom` "reads declarations only for the sort of an application at the top of an axiom, and aliases only at an alias application" (`Faithful.lean` header), so translating the text's own sentence may need its declarations. Hence two nodes before R2: TIE-design (Fable) and TIE-spike (one fixture, `ens.k`, every sentence).

**Green while wrong.** (a) `Γ c` has no model and entails everything. (b) `tr` is wrong in the same way as `Γ` (both use `trAxiom`). (c) The direction table puts a class under "weaker" or "more" to make it pass. (d) `Γ` says something extra where the text is silent, in a part no family lists: every per-sentence check passes.
**Closed by.** (a) per fixture, `Consistent (c.withHooks H)` is proved at every H for which `FnDet` and `FnSolves` hold, and at least one such H reaches each failing-clause or silent point of the fixture (C6's "point is reached" companion, reused); a layer-2 entailment counts only at such H. (b) `Translate.lean` is in the cone and reviewed as such (it is the manifest's theory layer); that the two routes share `trAxiom` is a stated limit, smaller than sharing the reader. (c) the table is pinned, each non-default class has a `ReadingNote` and a C6 guard, and the gate reads the table. (d) the converse of part 2; if TIE-design finds it not statable: not closed, stated limit, named in `[goal].statement`.

### C9. Row imp

At `T_DONE`, for `kimp` read from kompile's own KORE (package `ref-kimp`):
1. read: `kcore account` refuses nothing; the reading notes it uses are listed; the "one constructor the text does not declare" (`[goal].scoreboard_state`) is gone or is a row (triaged before R2, node IMP-ctor). The row records the kompile command that produced its `definition.kore`, checked by script against R-12.
2. `coreOK_defn` kernel-checked; the text tied per C14 parts 1 and 3.
3. Stated and kernel-built in the release run (`test/release.sh` without KEVM and mir builds; it has them today, `test/release.sh:13-17`): `consistent`, `sound_at`, `complete_at`, `run_exact`, each concluding `Consistent c ∧ …` for every H, under the **unsuffixed** names (REVIEW-FA D3: no hypothesis on the functions). `sound_hyp`, `complete_hyp` remain stated.
4. Every `[total]` function of the definition has `Total (c.withHooks H)` for every H. An exception is admissible only as: a kernel-checked H at which the function has no value, together with the text sentence that admits that H; anything else fails the criterion.
5. consumer: (i) the expected Lean statement of one K claim is written from the claim's text by a review agent before the generator runs; (ii) the statement **k2lean generates** from that claim equals it by text; (iii) it is proved about the package's `Step` using `complete_at`/`sound_at` and not `FnHyp`; (iv) a concrete initial configuration satisfying its hypotheses is exhibited; (v) every definition the statement mentions is pinned and is a cone root or is named as left out (C5 parts 1, 3). `ImpWrites`, stated by hand, does not meet the cell (R-5).
6. readings pending for this text: none.

**Green while wrong.** `Step` is wrong for imp where the tested programs do not reach; the row says nothing of constructs imp does not use. **Closed by.** C14 part 3 on every sentence of kimp; `run_exact`; for constructs imp lacks, C1 to C4 and C14 on fixtures.

### C10. Row KORE in K

At `T_DONE`, with `K := kk.sem` the reader's result on the pinned `definition.kore` of `KK/kore.k` (SHA-256 recorded; the pin moves once more, node KK-pin):
1. read (with its kompile command checked against R-12), `coreOK_defn`, tied, readings pending none: as C9 parts 1, 2, 6.
2. `kk_step` kernel-checked: `succs_sound`, `succs_stuck`, `succs_complete` as in `designs/KK-1-update-2026-11-17.md` (superseding `designs/KK-1-simulation-statement.md` section 1.4), **at `d₀ := d.withHooks HookParams.none`** with no hypothesis on `d.hooks` (D-RN-1). Hypotheses, complete: `hr : CExec.execReady d = true`, `hE : encDef d = some E`, and for completeness only `hco` (coherence of `d₀`, in the form `Eval.functional` takes at `T_R2`; node KK-stmt writes it before R2) and `hdef`. `KK.coherent` is a theorem. `encDef`'s conditions: C1 to C5, C7, C8, C10 to C12 of `designs/KK-1-update-2026-11-17.md` section 2 (C6 and C9 dropped; C11 covers a clause's `ens`; C12, new, on the fields: no rule or clause has `opens`, `exs`, a `pre` or `post` other than top, or `aside`, each refused with its reason). `kore.k`'s side is `K₀ := K.withHooks HookParams.none`. C2 (a parameter without `impl`) is refused, not mirrored: both readings are sound and complete at `d₀`, and the mirror only adds points where the `none` member is not the text's meaning (KK-stmt.update, 2026-11-17).
3. Pinned (C5 part 1); the definitions the three statements mention (`execReady`, `NotApplies`, `Config`, …) are roots or named as left out (C5 part 3).
4. Not vacuous: `encDef d = some E` by computation for `d := ref-kimp`'s semantics, and one concrete imp configuration with `succs` evaluated and `succs_sound` giving a named `Step` (the consumer cell, R-6).
5. Uncovered constructs: (proposed) `KK/COVERAGE.toml` with one entry per `rows.toml` row that is `supported` or `parameter`: `covered` with its case, or `refused` with the encoder's refusal and reason. None absent. Equation `ensures` is `covered` (cases from `ens.k`, `ens-owise.k`; mutant `ensures-as-requires` killed).
6. Cases: expectations per C7; agree totals exclude flagged cases; the flagged count is reported (it decides D-RN-1's reversal (b), and is measured before KK-pin).
7. Wording: `kore.k`'s header and `op-undef` note say `bot` at an open point is the `none` member's value.
8. `consistent` for `kk.sem` at `HookParams.none`, by `consistent_of` with `FnDet` and `FnSolves` proved for `kk`. Whether `FnSolves kk` is provable is not known (it is REVIEW-FA finding 4's case on a row); node KK-spike finds out **before R2**. If it is not, either `FnSolves` changes before R2, or this part is replaced by the sentence "the row's claim is about `Step kk.sem` only; `kore.k`'s own theory is not shown to have a model" in `[goal].statement`; the choice is a reading for a Fable design at that point, not left silent. KK-pin re-runs the spike's statements on the pinned text; a failure there (the text changed, not a cone defect) falls to the sentence above, not to section 2.6.

**Green while wrong.** (a) `kk_step` holds at `none` and the text's meaning differs wherever a run reads a rest or silent point. (b) `hdef` never satisfiable. (c) `encDef` encodes wrongly. (d) `COVERAGE.toml` refuses most rows.
**Closed by.** (a) **not closed, stated limit**: parts 6 and 7 label it; `succs_sound_everyH` (D-RN-1) is the only route to the text and is off the critical path. (b) part 4. (c) soundness cannot be wrong through `E` (it concludes a `Step d₀`); completeness can be vacuous, excluded at one definition by part 4. (d) the count is reported; floor: every construct kimp uses is `covered`.

### C11. One table, no stale statement of meaning

`findings/K-coverage.md` is replaced by a file generated from `rows.toml`; the manifest's layer prose is true of `T_DONE`. At `T_R1` it says "no result where every clause fails" (line 70) and "function equations in priority form with the closure axiom" (line 109): true of `T_R1`, false after group C, so both change at R2. REVIEW-RN finding 12's stale comments are gone.
**Green while wrong.** A grep finds wording, not meaning. **Closed by.** The R2 gate and the completion gate read each `teaches` field against the cone's definitions.

### C12. `[goal]` says what is checked

`[goal]` is section 3's text, replaced **first** (node GOAL), since lanes are briefed against it. **Green while wrong.** A cell marked met by a report. **Closed by.** C13.

### C13. Completion gate

A Fable review agent, cold, re-runs or has re-run every check at `T_DONE`, and beyond the criteria:
- the recounts of C1; the catch-all list (C4); the manifest prose (C11); three reader mutants run (C8); three triples (C3); three hand derivations redone (C7);
- **outside the table**: it chooses three K constructs from K's sources, not from `rows.toml` (one compile pass, one builtin rule, one option), writes each a fixture with its expectation by C7, and reports where the table had them;
- **per row, whole text**: tied in both layers, or the remainder and its reason;
- every reopening of the cone after R2 (section 2.6), with its ticket.
It writes `findings/GATE-DONE.md`. Only then is the single message sent to the doc owner session; it **leads with** every reopening of the cone (section 2.6), then the R-c list and count, each with its declaration.
**Green while wrong.** The gate inherits the criteria's blind spots. **Closed by.** The three draws from K's sources; otherwise not closed.

## 2. DAG of the remaining work

**In** = what it needs; **Moves** = criteria; cone declarations named where a node changes one.
Everything in 2.1 precedes R2. The rule for what must: (i) it changes or may change a cone definition or the root set; (ii) it is a check built to find a cone defect (the tie, guards, core fixtures, reader mutants, witnesses), since freezing first only protects proofs about untested definitions; (iii) it is a statement the frozen definitions must be able to carry (the rows' statements).

### 2.1 Before R2

| Node | Work | In | Moves | Cone declarations |
|---|---|---|---|---|
| GOAL | replace `[goal]` by section 3's text | none (orchestrator edit) | C12 | none |
| CE | lane CE, running: `Clause.ens` (REVIEW-FA D1), `ensuresPriority` removed, tests restated, `[total]` with a failing `ensures` makes `FnHyp` false; guards G0 to G7; `projectionDomain` G3; stale comments; a `ReadingNote` for the rule premise | `T_HLC` | C6, C7, C11 | `Clause`, `Eval`, `clauseEquation`, `competingEquation`, `FnSolves`, `Coherent`, the clause conjunct of `sortedOK` |
| F-CE | Fable review of CE: cone diff against D1's table; re-read `StepDecided`, `FnSolves`, the rest graph with both `ens` fields; D1's "to run" statements | CE | C5, C6 | none |
| TIE-design | Fable: C14's statements on the literal `d`; the class-to-direction table; the converse over `fnItems`/`ruleItems` and the families of Γ's seven parts; what `trAxiom` needs of the text's declarations; confirms `Parse.parse`, `emit`, `wf` are left out of the roots (R-15) | `T_HLC` (`Tie.lean`, `Kore/Translate.lean`, `Faithful.lean`) | C14, C7 | none (decides roots) |
| TIE-spike | one fixture (`ens.k`): `Tied`, and layer 2 for every sentence, both directions; measures form (a) of C7 | TIE-design, CE | C14, C7 | none; a failure is a cone or reader defect, fixed here |
| TIE-decision | Fable decision point on the spike's result: form (a) throughout, by class, or not at all; in the last case `[goal].statement` is reworded now and C2's floor applies (C7) | TIE-spike | C7, C14, C12 | none |
| ENUM | `extract.sh`, the eight lists, `rows.toml` with today's status per row | `T_INT`, `K` | C1, C4 part 3 | none |
| KFIX | for every E1 to E3, E7, E8 row: a K text, its kompiled KORE and `kcore account` output (no theorem), so that TRIAGE reads KORE and not memory; one K text may serve several rows, each row naming its sentence (otherwise this is several hundred reference kompiles); kimp's and `kore.k`'s rows marked | ENUM | C2 | none |
| IMP-ctor | what the constructor in imp's reading that the text does not declare is, as a row | KFIX | C9 part 1 | to determine |
| TRIAGE | Fable, binding: per row not yet settled, support or refuse with reason, reversal criterion, and "cone declaration that changes, or none"; applies R-11; produces the R-c list | KFIX, IMP-ctor, SIMP | C2, C3 | none (decides) |
| SIMP | native corpus count of `[simplification]` axioms that speak at a failing-clause point (REVIEW-RN finding 4) | ENUM tooling | C2, C6 | none if the condition stays outside Γ and `FnHyp` |
| K8 | kompile experiment: does an `[owise]` exclusion name a competitor's `ensures` or right side (D1 reversal criterion 2) | none | C6 | if positive: `AppliesAt` |
| PROJ | print the projection-domain axiom's right side; G3 | CE | C6 | possibly `Fn` |
| FD-C | Fable verdict: does Γ entail the collection laws read as inert (C14's *entailed* direction for `collectionLaw`) | `T_INT` | C14, C6 | `ΓColls` if not |
| WIT | witnesses for **every** conjunct of `coreOK`, `FnDet`, `FnSolves` (W-c's two provisional ones included; HL-C unit 3's model half), or removal, on the definitions as CE leaves them | CE | C8 part 2, C5 part 4 | `overloadsOK`, `itesApart`, others if removed |
| PROV | the six other provisional manifest rows (KN-4 at 44, 45, 75, 112; KN-5 at 46; Bool strictness at 76) per R-3, each naming its `rows.toml` keys | TRIAGE | C5 part 4 | none if relabelled |
| CONE-n | one lane per TRIAGE row decided "support, cone changes" (at most three units). Candidates, none confirmed: `registrySortName` for a user sort named `Id`, `?X` on a right side, cell multiplicity, a function symbol in a left side | TRIAGE | C2 | named by TRIAGE |
| FIX-core | fixtures with C14 layer 2 and derived expectations for every row whose reading lands in a cone definition: C3's core pairs, every `ReadingNote`, the four un-noted readings, every `supported` hook row's three statements (the interpretations in `Hooks.lean` are cone definitions, manifest lines 74, 75; a hook with no silent key that should have one is a cone defect too; `parameter` hooks stay in FIX-rest), CONE-n's rows | TIE-decision, CE, CONE-n | C2, C3, C7, C14 | none; a failure is a cone defect, fixed before R2 |
| GUARD | `test/Guards.lean` complete over every constructor, with the "point is reached" companions | CE, FIX-core | C6 | as FIX-core |
| MUT-core | reader mutants for the core pairs and reading notes, run natively | FIX-core, GUARD | C8 part 1 | none |
| KK-fix | `kore.k`: equation `ensures`, cases from `ens.k`/`ens-owise.k`, mutant, D-RN-1 wording, `COVERAGE.toml` skeleton | D1 (decided) | C10 parts 5, 7; C8 part 3 | none (K text) |
| KK-stmt | Fable update of KK-1 and the three statements written out in Lean against `T_HLC`+CE definitions (no proof): at `d₀`, C6 dropped, C11 for clauses, `hco`'s form; reported "no statement it could not write" (REVIEW-ORDER section 5's freeze condition) | F-CE | C10 part 2 | none (may find one) |
| KK-spike | `KK.coherent`, the inversion of one clause of `eval` (KK-1 K-1's reversal measure), `FnDet kk`, `FnSolves kk` attempted; the tie (C14) run on `kore.k`'s text as KK-fix leaves it | KK-stmt, KK-fix, TIE-decision | C10 parts 2, 8 | `Coherent`, `FnDet`, `FnSolves` if the spike shows a need |
| CS-stmt | the consumer's expected statement for one imp claim, written from the claim; checked statable against the package's `Step` | F-CE | C9 part 5 | none (may add roots) |
| IMP | ref-kimp regenerated: unsuffixed theorems, `Total` for every H, its kompile command recorded (at `1e306534` the package already states `consistent`, `sound_at`, `complete_at`, `run_exact` for every H, `RefKimp/FnHyp.lean:71-98` per the review) | CE, IMP-ctor | C9 parts 1 to 4 | none; a failure is a finding about `Γ`, `FnDet`, `FnSolves` or `Total` |
| TIE-kimp | C14 part 3 for kimp, the largest fixture | TIE-decision, IMP | C14, C9 part 2 | as IMP |
| LINT | `provenance.sh`; REVIEW-RN section 2 rewording; `kcore agree` flag and the flagged count | CE | C7, C10 part 6 | none |
| ROOTS | the root list computed from every statement of C9, C10, C14; what is left out, named | TIE-design, KK-stmt, CS-stmt | C5 part 3 | extends the cone's extent |
| PINS | `test/Pins.lean` additions; `Axioms.lean` over guards, fixtures, packages | ROOTS, GUARD | C5 parts 1, 2 | none |
| INT | integrate `kcore-kinds` and all lanes into `kcore-merge`; `test/integration.sh`; the unbuilt User modules | all of the above but KK-fix | C5 | none |
| R2 | `test/release.sh` once (example packages only); Fable gate: cone recomputed from ROOTS, statements, axioms; the silent table against the hook rows' third statements, entry by entry; the `KFloat` NaN code at `e = 1`; manifest prose and provisional rows; `core-cone.txt` stored by text. No message to the doc owner | INT, PROV, PINS | C5, C11 | **freeze** |

Parallel branches before R2, meeting at INT: {CE → F-CE → PROJ}; {TIE-design → TIE-spike}; {ENUM → KFIX → IMP-ctor, SIMP → TRIAGE → CONE-n, PROV}; {K8}; {FD-C}; {WIT}; {KK-fix ∥ KK-stmt → KK-spike}; {CS-stmt}; {LINT}; {IMP → TIE-kimp}. TIE-decision follows TIE-spike and gates FIX-core, TIE-kimp and KK-spike's tie. FIX-core, GUARD, MUT-core need the first three branches. ROOTS and PINS are last before INT.

### 2.2 After R2, KCore track (no cone change except by 2.6)

The reader is not in the cone (R-15), so reader lanes run here; every text's tie is re-proved on the reader as it is at `T_DONE`.

| Node | Work | In | Moves |
|---|---|---|---|
| RDR-n | reader lanes per TRIAGE row "support, no cone change" or "refuse": specific reasons replacing catch-alls; the total attribute function (C4 part 2); the 28 corpus refusals as rows; the `+.5` float literal as a row of its token sort (E6) | R2, TRIAGE | C2, C4 |
| FIX-rest | fixtures and evidence for the remaining rows: reader-only rows, `parameter` hooks, `erased` and `inert` rows, non-core pairs; by list, in parallel | R2, RDR-n per row | C2, C3, C14 |
| TIE-kk | C14 part 3 for `kore.k` on the pinned text (kimp's is before R2); kimp's tie re-proved after the last reader lane | R2, KK-pin, RDR-n | C14, C10 |
| MUT-rest | reader mutants for the remaining reading-bearing rows | FIX-rest | C8 |
| OV-6.3 | emit of overloading symbols, deciding functions with overloading heads | R2 | none unless TRIAGE says a row's evidence needs it: off the critical path |
| TABLE | generate the coverage document from `rows.toml` | FIX-rest | C11 |

### 2.3 After R2, k2lean track

| Node | Work | In | Moves |
|---|---|---|---|
| KK-pin | the pin of `kore.k` moves, once; re-runs KK-spike's statements on the pinned text (C10 part 8) | KK-fix, TRIAGE binding (every row's status final), LINT's flagged count (R-7), `COVERAGE.toml` complete for every `supported`/`parameter` row | C10 |
| KK-3…7 | KK-1's stages: mirrors and embeddings, `eval` inversion, match completeness, `succs_char`, the three theorems; `consistent` for `kk` | R2, KK-pin, KK-spike | C10 parts 2, 3, 8 |
| KK-inst | `encDef` at ref-kimp, one concrete step | KK-3…7, IMP | C10 part 4 |
| CS | CS-3/CS-4: the generator emits the statement CS-stmt fixed; proved for imp; the non-vacuity instance | R2, CS-stmt | C9 part 5 |

### 2.4 End

GATE: completion gate (C13), then the single message. In: everything.

**Critical path:** GOAL → CE → F-CE → (TIE-design → TIE-spike → TIE-decision ∥ ENUM → KFIX → TRIAGE → CONE-n ∥ KK-stmt → KK-spike ∥ IMP → TIE-kimp) → FIX-core → GUARD → MUT-core → ROOTS → PINS → INT → R2 → KK-pin → KK-3…7 → KK-inst → GATE.
R2 is later than in the first version; total work is not larger, since FIX-core, GUARD and the statement nodes were post-R2 work moved forward.

**Off the critical path:** OV-6.3; moving KCore to a top-level `kcore/` (before FIX-core starts or after GATE, never between: it changes every path here); stale documents outside C11; `succs_sound_everyH`, `succs_defined`; an `open` third outcome in `kore.k`; interpreting the 16 uninterpreted Float operations (`parameter` rows); OD-13, W5.
**Dropped by the owner:** every KEVM, mir, wasm item.

### 2.5 Departures from the pick-up entry

1. ENUM, KFIX and TRIAGE precede R2 (the entry lists the per-construct table after R2): they decide which cone changes exist.
2. The tie, the core fixtures (every `supported` hook included), guards, reader mutants, witnesses, and the imp row's regeneration and tie precede R2 (rule (ii) above).
3. The rows' statements are written before R2 (KK-stmt, CS-stmt, KK-spike), as REVIEW-ORDER section 5's freeze conditions already asked ("KK-a and CS-2 reported with no statement they could not write").
4. `registrySortName` is a cone question (REVIEW-ORDER section 5 row 9 lists it under `Lib` / the registry): TRIAGE decides before R2.
5. K8 is required, not "if cheap": it is the reversal check of D1.
6. The `kore.k` pin is final before KK-3 and needs every row's status final.

### 2.6 Reopening the cone after R2: defects only (owner direction 2026-11-15, recorded here as R-13)

A cone declaration found, after R2, to state something the text does not (a failing C14, C6 or C2 theorem with the row named) is fixed without the owner, through a ticket that names the declaration and the failing row, and a Fable gate. The gate reviews the change, recomputes the cone, lists the proofs redone, and **re-runs the pre-R2 checks that read the changed declaration** (its FIX-core rows, their guards and reader mutants, the witnesses of the conjuncts it touches, TIE-kimp), so that the re-freeze is of a definition as tested as the first freeze was. The freeze is recorded as reopened and re-frozen (`frozen_at` gains an entry), and every reopening is listed first in the completion message.
**New support is never a reason to reopen.** A failure caused by a change of a text (the `kore.k` pin) is not a cone defect and does not come here (C10 part 8).

## 3. Corrected `[goal]` text

TOML text only; the ticket file is not edited here.

```toml
statement = "KCore (semantics-agnostic): every K construct of K 7.1.337 (default options, --backend haskell), enumerated by extraction from kompile's grammars, attribute registry, compile pipeline, options, emitter and builtin library and from KORE's grammar, is supported or is refused by the reader with a stated reason; a construct is what can change the theory or the step relation of a kompiled definition, proof tasks being uses of a definition and not part of it. What a package's semantics states is tied to the KORE text sentence by sentence through the translation of the text, for every hook interpretation; where the tie is not established the reader is named as trusted. The headline statements are pinned and axiom-free, and the review cone is frozen at release R2, reopened only for a defect, through a ticket and a Fable gate, each reopening recorded. Rows (semantics-specific, k2lean): imp and KORE in K each get, from kompile's own KORE, a tied Lean package kernel-built in a release run, stating Consistent; imp's states sound_at, complete_at and run_exact for every interpretation with no hypothesis on its functions, and the statement k2lean generates from one K claim, fixed beforehand from the claim's text, is proved about its Step; for KORE in K, kk_step (succs_sound, succs_stuck, succs_complete) is kernel-checked at the interpretation HookParams.none, hypotheses listed. kompile's translation of K into KORE and the builtin files' prose for hooks are trusted. Checked by designs/DONE-0-definition-of-done.md, criteria C1 to C14, at the tree named in core-manifest.toml."
statement_reworded = "2026-11-15, replaced after the owner's directions of that day (every construct; upstream semantics dropped; review at completion), the decisions REVIEW-FA D1, D3 and REVIEW-RN D-RN-1, and findings/REVIEW-DONE-0.md. The 2026-11-14 statement was: every K definition we care about, read from kompile's own KORE, gets a Lean package, kernel-built in a release run, that states sound and complete under coreOK and listed obligations, none known false; and, for imp first, a theorem generated by k2lean is proved about that package's Step"
scoreboard_rows = ["imp (kimp from kompile's own KORE, package ref-kimp)", "KORE in K (krs/semantics/kore/kore.k at its pinned SHA-256)"]
scoreboard_columns = [
  "read (C9.1, C10.1): kcore account refuses no sentence of the row's text; the reading notes it uses are listed",
  "tied (C14): Tied for the text; every sentence of the user module in its class's direction against the translated text, for every interpretation, or the remainder listed with the reader named as trusted for it",
  "coreOK (C9.2, C10.1): coreOK_defn kernel-checked in the package",
  "owed facts (C9.3): names with counts discharged / open, none known false; the unsuffixed theorem names only when none is open",
  "statements (C9.3, C10.2, C10.8): imp: consistent, sound_at, complete_at, run_exact, each concluding Consistent, for every interpretation, kernel-built in a release run. KORE in K: succs_sound, succs_stuck, succs_complete at d.withHooks HookParams.none, hypotheses exactly execReady d, encDef d = some E, and for completeness coherence of d and the one call having a value; consistent for kore.k's own semantics at HookParams.none, or the sentence that it is not shown; all pinned, their definitions cone roots or named as left out",
  "admitted interpretations (C9.4): every [total] function has a value for every interpretation; an exception is a kernel-checked interpretation with no value and the text sentence that admits it",
  "consumer (C9.5, C10.4): imp: the statement k2lean generates from one K claim equals the statement fixed beforehand from the claim, is proved about the package's Step, and has a concrete instance. KORE in K: encDef at ref-kimp by computation and one concrete step obtained through succs_sound",
  "evidence (C7, C10.5, C10.6): expectations derived from the translated text, hand derivations counted; agree verdicts that read the interpretation counted apart; for KORE in K the uncovered-constructs list has no absent entry and the mutants are killed or shown equivalent",
  "readings pending for this text: listed; empty from R2",
]
construct_table = "kcore-spec/test/constructs/rows.toml: one row per K construct (lists E1 to E8 of DONE-0 C1) and per pair of meaning-carrying modifiers (C3); statuses supported / parameter / inert / erased / refused; no row not handled; refusals on principle (R-a, R-b) counted apart from not supported at this freeze (R-c, each naming the cone declaration that would change)"
scoreboard_state = "2026-11-15: no cell is met as worded here. imp: read and coreOK met at T_R1 with one undeclared constructor in the reading; untied; statements in the suffix-free form on example packages at kcore-kinds 29927590, not released; no generated consumer theorem. KORE in K: kore.k at 38cac354e, 49 cases, 66 of 67 mutants killed; no stage of kk_step proved; equation ensures not covered; untied. Construct table: not started; the 2026-11-13 measurement (findings/K-coverage.md) has 128 of 441 rows not handled and holds only lists E4 to E6, E6 for hooks only"
```

## 4. Readings and questions

### 4.1 Readings decided here (reason; reverse when)

| # | Reading | Reason | Reverse when |
|---|---|---|---|
| R-1 | Scope of "K construct": what can change `Γ` or `Step` of a kompiled definition; proof tasks, solver encodings and program parsing are one class `use`, `inert` (C1) | the headline statements are about `Γ c` and `Step c`; see C1 | the owner asks KCore to state what a claim means: `Reachability` becomes a root before R2 |
| R-2 | "Refused with a stated reason" needs R-a, R-b or R-c; a bare catch-all or "no decision recorded" is not a reason | the owner's words separate refused-with-reason from unsupported | the owner accepts a listed backlog |
| R-3 | No provisional row after R2. KN-4 and KN-5 are dropped; their five rows are relabelled stable and each names the `rows.toml` keys left `refused` or `parameter` because of it (C5 part 4); Bool strictness stays strict; `MInt` is `refused` R-a | an exemption that leaves a cone declaration changeable contradicts the freeze; the keys keep the label from outrunning the table | TRIAGE under R-11 supports a row that needs hook domains or sort parameters: a CONE-n before R2 |
| R-4 | A reference backend's run is evidence and a tripwire, never an expectation | RULES "Other implementations are insight" | never for expectations |
| R-5 | The imp consumer cell needs the generator's output; `ImpWrites` by hand is evidence | "generated by k2lean" in the goal's words | the owner says the demo suffices |
| R-6 | The KORE-in-K consumer cell is `kk_step` used once at ref-kimp | without an instance `kk_step` can be vacuous | `designs/CS-0` (not read) defines the cell otherwise |
| R-7 | No `open` third outcome in `kore.k` now | the brief fixes `kk_step` at `HookParams.none`; D-RN-1 prices it | D-RN-1 (b), measured by LINT before KK-pin |
| R-8 | A text-admits predicate is not a criterion; C9 part 4 asks its content for the rows | scope; checkable per row today | packages are handed to users who instantiate H |
| R-9 | No message to the doc owner at R2 | owner direction 2026-11-15 is later than the pick-up entry | — |
| R-10 | DONE is per K version (7.1.337) | the lists are extracted from one installation | another version is named: re-run `extract.sh` and diff |
| R-11 | A construct whose support needs a cone change and that neither row uses is refused with R-c naming the declaration. Exception: TRIAGE supports it before R2 when it is in R-1's scope, a K author meets it without a special option, and the lane is within CONE-n's size (three units). R-c is not admissible where no cone declaration would change | direction 2026-11-15: "supported or refused with a stated reason" asks that every construct be decided; direction 2026-11-14: after R2 a cone change "must name the scoreboard cell it unblocks", and such a construct unblocks none. The exception keeps the floor from being the two rows by default of effort | TRIAGE's R-c list holds a construct the K tutorial or the manual's first-level sections present as ordinary (`?X`, cell multiplicity, `strict`) that the exception could not take: then it is asked once, with the list, before R2 (section 4.2) |
| R-12 | Rows are stated for default options and `--backend haskell` | the corpus (370 of 381 texts with `--backend haskell`, K-coverage section 4) and the reference toolchain | a row needs an LLVM-backend text |
| R-13 | Not a reading: owner direction 2026-11-15. After R2 a cone defect is fixed through a ticket naming the declaration and a Fable gate, without the owner; the freeze is recorded as reopened and re-frozen; the affected pre-R2 checks are re-run; reopenings lead the completion message (2.6) | the owner's | the owner's |
| R-14 | The semantic tie (C14 layer 2) is the criterion; `Tied` is required beside it but is not the meaning-level check | `Reordered d.emit k` certifies a print-back; `Γ c` and `tr s` are two routes to matching logic from one text | at the decision point TIE-decision, before R2, if TIE-spike shows form (a) infeasible or layer 2 costlier than the rows: the limit is written into `[goal].statement` then (reader trusted, by class), and C2's floor applies |
| R-15 | `Parse.parse`, `Definition.emit` and `wf` are left out of the cone roots; C14 is stated per text on the literal `d`, with no library theorem quantified over `parse`; reader lanes (RDR-n) stay after R2 | `Tied k` unfolds to `Parse.parse k` and `d.emit` (`Tie.lean:193`), and the cone enters values of reached definitions, so a root mentioning it would freeze the reader; a per-text kernel check is what makes the reader untrusted, so freezing it buys nothing | TIE-design obtains the library theorem cheaply and its proof is long enough to be worth protecting: then the reader lanes that touch what it unfolds go before R2, by name |

### 4.2 Owner questions

None. Q1 of the first version is reading R-11, which becomes a question before R2 only under its reversal criterion. The outcome of TIE-spike is a Fable decision point (TIE-decision), not an owner question. Reopening for defects is the owner's direction (2.6).

## 5. Findings made while writing

1. K-coverage is at `57f851ec`, 2026-11-13; rows it calls `not handled` or `refused` are read at `T_INT` per the resume entries. No count in it is the state of C2.
2. `ensuresAsRequires` shows 0 corpus sentences in K-coverage (line 320): the corpus never exercised the reading that was wrong. A corpus count of 0 on a `supported` row is a warning.
3. The manifest's layer prose becomes false at R2 unless changed (lines 70, 109).
4. KK-1's `hco : CoherentAll d` predates HL-B; node KK-stmt settles its form.
5. KK-1's `Cl` mirror has no `ens` and its C11 speaks of rules only.
6. `test/release.sh` builds KEVM and mir today.
7. `test/Pins.lean` and `test/Axioms.lean` do not yet cover what C5 names (the review's F15, F22, shown there).

## 6. Not read, and what rests on it

- Lean: only the headers of `KcoreSpec/Tie.lean` (and its declaration lines), `Kore/Translate.lean`, `Kore/Gamma.lean` (declaration lines), `FaithfulTr.lean`, `Faithful.lean`, at `1e306534`, for C14. No proof, no test, no script, no `kore.k`. Whether C14 layer 2 is statable per sentence class, and at what cost, is not known: TIE-design and TIE-spike exist for that.
- K sources: nothing beyond existence checks; the line numbers and counts for `Outer.jj`, `Att.scala`, `CheckAtt.java`, `RuleGrammarGenerator.java`, `KompileOptions.java`, `KoreBackend`, `kast.md`, `prelude.md` are the review's (`findings/REVIEW-DONE-0.md` section 2 and F8 to F14), taken as shown there and not re-read. That `KoreBackend.steps` lists the passes by name in a form a script can extract is suspected.
- Ticket file: `[goal]` and the eight resume entries of the brief only.
- `REVIEW-ORDER.md` sections 0 to 4; `HL-0` sections 0 to 4 and 6; `KK-1` sections 2 to 6 (stage sizes unknown); REVIEW-FA findings beyond the Decisions; `core-cone.txt`; `designs/CS-0`, `RE-0`, `SP-0`; `findings/GATE-R1.md`.
- What imp and `kore.k` use, construct by construct: KFIX measures it.

## 7. Resolution of REVIEW-DONE-0

First round: accepted 27 of 27 (three with a modification, marked), rejected 0. Second round (the review's section 8): accepted 7 of 7 (N1 to N7) and the 9 smaller changes, rejected 0; table 7.2.

| # | Verdict | Where the change is |
|---|---|---|
| F1 | accepted, modified | New criterion C14 with both layers; C9 part 2, C10 part 1 require the tie; nodes TIE-design, TIE-spike, FIX-core, TIE-kimp before R2, TIE-kk after. Modification: `Tied` needs `wf d`, which asks more than `coreOK`; where `wf` fails on a conjunct `coreOK` does not ask, the conjunct is named and compared by script against `coreOK`'s conjunct list (C14 part 1). The semantic layer is the criterion (R-14). Reverse the modification when TIE-design shows `wf` holds on every fixture |
| F2 | accepted | C7 rewritten: the expected side is a derivation from the translated text, forms (a), (b), (c); the lint requires `H` used, and `AtNone` theorems are never row evidence; the separation rule is kept only for what stays hand-derived. Feasibility: node TIE-spike on `ens.k` |
| F3 | accepted, modified | C2 evidence row "`supported` hook": three statements; R2 gate reads the silent table against them, per hook. Modification: a hook has no defining KORE sentence, so its expectation is from the builtin prose (trusted base 4), not from `tr s`; stated as a limit |
| F4 | accepted | C8 part 1: reader mutants are built natively and run on the fixture; the refutation instance stays as the explanation; the gate's three mutants are run. Nodes MUT-core (before R2), MUT-rest |
| F5 | accepted | C9 part 5 (i) to (v): statement fixed beforehand, equality by text, non-vacuity instance, definitions pinned or roots. Node CS-stmt before R2 |
| F6 | accepted | C10 part 8 (`consistent` for `kk` at `none`, or the stated sentence); C5 closure (c) corrected; node KK-spike before R2 |
| F7 | accepted | C1 "Scope (reading R-1)": the review's proposed decision adopted with its reason and reversal; claims are `inert` (class `use`) and the consumer's input; kompile in the trusted base (section 0) |
| F8 | accepted | C1 list E7 (compile passes from `KoreBackend.steps`); C2 closure (d) asks a fixture per case a pass distinguishes |
| F9 | accepted | C1 list E3 redefined on the generated rule grammar; token productions split into named, recorded rows |
| F10 | accepted | C1 list E8; reading R-12 fixes the option set; R-b covers other values |
| F11 | accepted | C1 list E6 widened to every production and rule of the builtin files, a row per module for the registry, a row per token sort; `+.5` now has a list (node RDR-n) |
| F12 | accepted | C1 list E2: key × KORE sentence class, restricted by `onlyon` and `KeyRange`; one row per value of closed-set parameters |
| F13 | accepted | C3: the unit is the pair over symbol attributes, sentence attributes and body features; hook × equation and three more join the core pairs |
| F14 | accepted | C4 part 2: a total function with no default case, key set equal to the E2 rows reaching KORE; the made-up key kept as a test of hand-written KORE |
| F15 | accepted | C5 part 2: `collectAxioms` over guards, fixtures and every declaration of the row packages; grep demoted to tripwire. Node PINS |
| F16 | accepted | C5 part 4 and R-3: a relabelled row names its `rows.toml` keys or the gate-checked sentence |
| F17 | accepted, modified | (a) section 2.1's rule (ii): the tie, FIX-core, GUARD, MUT-core, WIT, KFIX precede R2. (b) section 2.6 and R-13: reopening for defects only. Since made an owner direction (2026-11-15): no longer flagged; the gate also re-runs the affected pre-R2 checks |
| F18 | accepted | C5 part 3 and node ROOTS: roots computed from every statement of C9, C10, C14; what is left out is named |
| F19 | accepted | C1 table: extraction units for E1 (named alternatives) and E5 (`sb.append` sites by line) |
| F20 | accepted | C1 closure (a): E2 recounted by `final val` declarations; the manual used as a list that must be included |
| F21 | accepted | C3 modifier set computed by native diff; C4 part 3 prints every mismatch's row and the gate reads all; C9 part 4 defines an admissible exception |
| F22 | accepted | C5 part 1 marked proposed work; node PINS before R2 |
| F23 | accepted | C13: three constructs drawn from K's sources, and the whole-text tie duty per row |
| F24.1 | accepted | Nodes KK-stmt and CS-stmt before R2, inputs of ROOTS and INT |
| F24.2 | accepted | Node KK-spike before R2 (`KK.coherent`, one `eval` inversion, `FnDet kk`, `FnSolves kk`) |
| F24.3 | accepted | LINT is an input of KK-pin |
| F24.4 | accepted | KK-pin needs TRIAGE binding for every row and `COVERAGE.toml` complete |
| F24.5 | accepted | Node IMP-ctor before TRIAGE |
| F24.6 | accepted | GOAL is the first node |
| F25 | accepted | C10 closure (a) now reads "not closed, stated limit"; WIT covers every conjunct and is before R2 |
| F26 | accepted | Q1 removed; reading R-11 with the reviewer's text, C2's two headings and the rule that R-c needs a named cone declaration; section 4.2 |
| F27 | accepted | `prelude.md` dropped as a source (E3); `--for-proving` removed (E8 is extracted, not named from memory); claims `inert` (C1); C5 closure (c) corrected; section 6 no longer calls the `Att.scala` facts suspected |

F24 is one finding with six items; each is answered so that none is lost.

### 7.2 Second round (REVIEW-DONE-0 section 8)

| # | Verdict | Where the change is |
|---|---|---|
| N1 | accepted, the reviewer's reading (i) | R-15; C5 part 3 (`Parse.parse`, `emit`, `wf` left out of the roots); C14 parts 1 to 3 (per text on the literal `d`, no theorem over `parse`); TIE-design's row; the note heading 2.2; RDR-n stays after R2 and kimp's tie is re-proved after the last reader lane (TIE-kk's row) |
| N2 | accepted | C3: the modifier set is computed from the kompiled text, or from the `Semantics`; a text difference with no `Semantics` difference is a visible row |
| N3 | accepted | C14 part 2 "Converse, over Γ's content"; green-while-wrong (d) and its closure; TIE-design and TIE-spike cover both directions; the R2 gate reads the families against Γ's seven parts |
| N4 | accepted | FIX-core takes every `supported` hook row's three statements; `parameter` hooks stay in FIX-rest; 2.5 item 2 |
| N5 | accepted | Nodes IMP and TIE-kimp before R2; KK-spike runs the tie on `kore.k` as KK-fix leaves it; TIE-kk after KK-pin |
| N6 | accepted | C14 closure (a): `Consistent` at every H with `FnDet` and `FnSolves`, at least one reaching each open point |
| N7 | accepted | Node TIE-decision before R2 (Fable, not the owner); C7's last paragraph; C2's floor; R-14's reversal fires there; section 4.2 |
| F4 half | accepted | C8 part 1: the theorem module is checked against the regenerated fixture and must fail; "argued" only for kernel mutants |
| F12 wording | accepted | E2: closed-set values a row each; open parameters one row with the distinguished cases |
| F10 gap | accepted | C9 part 1 and C10 part 1: the row's kompile command recorded and checked against R-12 |
| F1 addition | accepted | C14 part 1: the failing `wf` conjunct compared against `coreOK`'s list by script |
| F17(b) addition | accepted; R-13 is now an owner direction | 2.6 rewritten: affected pre-R2 checks re-run, freeze recorded as reopened and re-frozen, reopenings first in the completion message (C13); the flag is removed from 4.1 and 4.2 |
| WIT input | accepted | WIT's input is CE |
| KK-spike and the pin | accepted | C10 part 8 and KK-pin: the spike's statements are re-run on the pinned text; a failure falls to part 8's sentence, not to 2.6 |
| KFIX size | accepted | KFIX: one K text may serve several rows, each naming its sentence |
| E6 unit | accepted | E6: the unit is the hooked declaration, keyed by hook name then symbol |
| C4 part 2 | accepted | C4 part 2: a function over an enumeration of the E2 keys with no wildcard; a name outside it refused |
