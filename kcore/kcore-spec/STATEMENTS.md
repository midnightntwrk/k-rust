# The statements of the specification (M1.3)

State: **frozen 2026-11-07**: Sebastien approved the statements ("looks good to me"), with the recommendations of section 10 (Q1–Q19) as written. M1.3 output, 2026-11-06, revised after the independent reviews `../findings/M1.3-astra-review.md` and `../findings/M1.3-astra-rereview.md` (section 11), and with F0 redefined as a typed structure with a generator (decision `Q-f0-shape`, section 1). Changing a statement now is a decision recorded in ../VISION.md.
Decisions D1–D4 ([../VISION.md](../VISION.md)) are taken as given.
This document is F0's. F1, the M2 fragment, landed beside F0 on 2026-11-07; its specification is the companion [F1-SPEC.md](F1-SPEC.md) (theory audit [F1-AUDIT.md](F1-AUDIT.md)). Nothing here changed for it.
Names (renamed 2026-11-06): the typed definition is `KCore.Definition`, with parts `Semantics`, `Presentation` and `Certificates` (fields `sem`, `pres`, `cert`); F0 names only the fragment, the definitions `wf` accepts. "The core" in the prose below means the `Semantics` part.

Code: `KcoreSpec/{Prelude,Definition,Emit,Fragment,Parse,Curate,Closure,Statements,PeanoSpec,Witnesses,SpecChecks}.lean` and `prelude/f0-prelude.kore`; the printed Γ_cons, Γ_closure and lemmas for peano are in [GAMMA_CONS.txt](GAMMA_CONS.txt) (`lake exe gammad --spec`).

Status of a rule, as in [TRANSLATION.md](TRANSLATION.md): SOURCE (transcribed from the cited text), CHOICE (not dictated by a source; alternatives listed), GAP (not covered).

## Sources

The keys of TRANSLATION.md ([Thesis], [AML-TR], [FoSSaCS], [kore-syntax]), and:

| Key | Document | Where |
|---|---|---|
| [MLE] | X. Chen, G. Roşu, *Matching Logic Explained*, TR 2020 | §8.2 BPA, (Transition), pp. 27–28: predecessors defined by an equation `•_u y = …`, "the ML specification … defines the exact set of transitions" |
| [OOPSLA23] | Lin et al., *Generating Proof Certificates for a Language-Agnostic Deductive Program Verifier*, OOPSLA 2023 | p. 13: `◦φ ≡ ¬•¬φ`; p. 26: the Step axiom, "the only way to make an execution step is to use one of the semantic rules", absent from kompile's theory |
| [TCS26] | Chen, Lucanu, Roşu, *A unifying logical foundation for initial algebra semantics and induction*, TCS 2026 | Fig. 6 NOCONFUSION and Lemma 40 (ground terms are equal iff identical), p. 11; Thm. 44, p. 12; App. A, Defs. 62–65 (standard model), pp. 20–21 |
| [syn-A], [syn-D] | `../papers/A-k-denotation/SYNTHESIS.md` §1 item 8, `../papers/D-reachability-certificates/SYNTHESIS.md` §1 | the closure proposal and the step-soundness/step-completeness pair (reading notes, inferences marked there) |

## Overview

For a well-formed F0 definition d = (c, p, z) (section 1: core, presentation, certificate), whose KORE is D = `emit c p`, and a step function `f : Kore.Pattern → List Kore.Pattern`:

| Statement | Mathematics | Lean |
|---|---|---|
| fragment | a KORE text k is in F0 iff k = emit c p for a well-formed d found by parsing; decidable | `F0 k`, `wf d` |
| ground configuration | t is a ground constructor term of the configuration sort | `GroundConfig c t` |
| step soundness | ∀c ground. ∀c' ∈ f c. Γ_D ⊧ c → •c' | `StepSound c p f` |
| step completeness | ∀c ground. Γ_D ∪ Γ_closure ⊧ c → ◦(c'₁ ∨ … ∨ c'ₙ), f c = [c'₁,…,c'ₙ]; for n = 0, c → ¬•⊤ | `StepComplete c p f` |
| outputs ground | ∀c ground. ∀c' ∈ f c. c' ground | `OutputsGround c f` |
| a model exists | ∃M. M ⊧ Γ_D ∪ Γ_closure ∪ DV-Fun | `StdModelOK c p` |
| no degenerate model | in every model of Γ_D ∪ DV-Fun: ⟦t⟧ is one element; skel t ≠ skel t' (same sort) ⇒ ⟦t⟧ ∩ ⟦t'⟧ = ∅ | `ModelsStandard c p` |
| Soundness and completeness | ∀d. wf d ⇒ all five above for `refStep c` | stated as `KCore.Sound` and `KCore.Complete`, with `sound` and `complete` proved from `wf` and `Obligations` (`KcoreSpec/Sound.lean`); the library has no `sorry` |
| Soundness and completeness for KORE | k ∈ F0 ⇒ ∃d. emit c p = k ∧ all five for `refStep c` | for a KORE text, through the tie (`Tied k`: `parse k = .ok d`, `wf d`, `Reordered d.emit k`) and `sound`, `complete` |
| Step equivalence | ∀c ground. set(cand c) = set(ref c) | `StepEquiv c ref cand` |
| transfer | soundness and completeness ∧ step equivalence ∧ wf d ⇒ the candidate is sound, complete, ground-valued | `stepEquiv_transfer` (proved) |

Γ_D is the curated theory of decision D2 for `emit c p`, with the arity axiom of every domain-value literal; Γ_closure is one axiom; DV-Fun says each domain value denotes one element. The Lean statements take the core c; those that read Γ_D or Γ_closure also take the presentation p, because Γ_D is the theory of the KORE text `emit c p` (section 5, "What the presentation can affect"). None reads the certificate.
`⊧` is aml-port's `entails`: true in every model (`Interpretation` over any inhabited `M : Type`) of the premises.

## 1. The fragment F0

Decision `Q-f0-shape` (2026-11-06): F0 is not a validator over arbitrary KORE (the M1.3 `Fragment.lean`, about 1,000 lines, whose two review rounds each found a new class of defect: shapes recognized instead of contents; then capture, sort-blind alpha-equivalence, a fuel cutoff counted as success, unvalidated duplicate declarations, a discarded sort annotation). It is a typed source structure, a generator, and a round-trip check:

    F0 k  :=  parse k = some d  ∧  wf d  ∧  Reordered (emit d.sem d.pres) k         (d = (c, p, z); `d.emit` in Lean)

`Reordered e k` (since 2026-11-07, decision 3 of `../findings/M1.6-scale-probe.md`; before, `e = k`) is equality of kore-lean's syntax trees except for the order of the sentences inside each module: the same attributes, the same modules in the same order with the same names and attributes, and each module's sentences a permutation of the other's, repetitions counted (`List.Perm`). No renaming, no other normalization. The order of a module's sentences has no meaning in KORE (a module declares a set of sorts and symbols and states a set of axioms); our translation reads it in three places (the G-sorts disjunction, the first declaration of a symbol's name, and which axiom's sort variables a G-next-arity item takes), and `reordered_sameModels` (section 5, proved) states that the theory of k has the same models as that of `emit c p` when no name is declared twice. Equality up to order is possible because everything kompile writes that a generator cannot recompute (the `UNIQUE'Unds'ID` hashes, source locations, the variable names kompile mints such as `_Gen4` and `_DotVar0`, and the names and binder order of the `owise` exclusions) is carried in the presentation part of `Definition`. The translation reads no attribute except `[simplification]` (TRANSLATION.md, D-attributes), so ids and locations do not affect Γ_D.

`Definition` has three parts (following `../findings/T5-k2lean-alignment.md` §4):

| Part | Holds | Read by |
|---|---|---|
| `Semantics` | user sorts; constructors and functions in declaration order (signatures, clauses with variable sorts and index terms, catch-all clauses); subsorts; rules; the sort of `$PGM` | `emit`, `wf`, and every statement: Γ_cons, ground configurations, `refStep`, `OutputsGround`, step equivalence read only the core |
| `Presentation` | source path, module name and location; the ids of each sort's helper equations; the interleaving of constructors, functions and subsorts; `symbol(…)` keywords and locations; variable names (user and minted) and exclusion names; ids and locations of clauses and rules; the configuration's location and `initKCell` id | `emit` only, and `wf`'s check that names keep variables apart |
| `Certificates` | for each function, the argument position on which its self calls decrease | `wf` only |

`emit : Semantics → Presentation → Kore.Definition` reads the presentation's lists position by position against the core's, so every item of the core is emitted whatever the presentation. Γ_D and Γ_closure are translations of the emitted text, so the statements that read them take (c, p); section 5 states what of p they can depend on.
Deviations from T5 §4: symbols stay strings (fine at F0's size); the interleaving is a list of kinds rather than a permutation; `Term.as` stays in the core.

What is reviewed and what is not:

| Part | File | Reviewed | Lines (code, without comments) |
|---|---|---|---|
| `Definition` (core, presentation, certificate), the signature the core induces, the conditions of `wf` per part | `KcoreSpec/Definition.lean` | yes | 456 (269) |
| `emit : Semantics → Presentation → Kore.Definition` | `KcoreSpec/Emit.lean` | yes | 391 (257) |
| the prelude constant: the fixed KORE text, and Lean data naming its sorts and constructors | `prelude/f0-prelude.kore`, `KcoreSpec/Prelude.lean` | yes (the text is krust's output, cut verbatim) | 2,227 KORE; 123 (57) |
| `wf` (conjunction per part, plus "names declared once" over `emit c p`), `F0`, `F0.sound` | `KcoreSpec/Fragment.lean` up to "Diagnostics" | yes | 67 (37) |
| `parse : Kore.Definition → Option Definition` | `KcoreSpec/Parse.lean` | **no** | 272 (214) |

What is reviewed: the core and its conditions, `emit`, the certificate check, and the presentation check (names distinct). The presentation's values are not reviewed: they are inert text, and exact equality with k checks them.
The reviewed Lean is 1,037 lines (620 of code; 926 and 567 before the split), plus the 2,227 lines of fixed KORE text copied from krust; the old validator was 1,003 lines (684 of code), all logic over arbitrary input. `parse` needs no review: `F0.sound : F0 k → ∃ d, wf d ∧ Reordered d.emit k` (proved), so a wrong parse can only reject. Its correctness matters for coverage only.

### Definition

| Field | Part | Content | Emitted as |
|---|---|---|---|
| `userSorts`; `sortUids` | core; pres | the user's sorts; the ids of their generated `projectX`/`isX` equations | `sort SortX{} []`, `isX`, `projectX` declarations, axioms, equations |
| `ctors`, `fns`, `userSubsorts`; `order`, `ctors`, `fns` | core; pres | constructors (label, argument sorts, result sort) and functions in declaration order, subsorts `A < B`; their interleaving, `symbol(…)` and locations | symbol declarations; functionality, injectivity, distinctness, subsort axioms |
| `Fn.clauses`; `FnPres.clauses` | core; pres | ordered clauses `f(p̄) = rhs`: variable sorts, argument patterns, right-hand side; variable names, id/location, exclusion names | kompile's equation `\implies(\and(\top, X̄ ∈ p̄), \equals(f(X̄), \and(rhs, \top)))` |
| `Fn.owise`; `FnPres.owise` | core; pres | optional catch-all clause `f(x̄) = rhs [owise]`, one variable per argument; names, id/location | the equation with the premise `¬(∃ȳ₁. X̄ ∈ p̄₁ ∨ … ∨ ⊥)` |
| `decreasing` | cert | per function, the argument position on which recursive calls decrease | (not emitted) |
| `pgmSort`; `configLoc`, `initUid` | core; pres | the sort of `$PGM` in `configuration <k> $PGM:S </k>`; its location, the id of `initKCell` | the `<k>` cell declaration and axioms, `initKCell` |
| `rules`; `rules` | core; pres | `lhs => rhs` between configurations: variable sorts, terms; names, id/location | `\rewrites{C}(\and{C}(lhs, \top), \and{C}(rhs, \top))` |
| `source`, `moduleName`, `moduleLoc` | pres | metadata | attributes, module name |

A `Term` is a variable (an index into the clause's or rule's variable list), an application of a symbol by name, `inj{A,B}`, or an as-pattern `\and(t, xᵢ)`. Sorts are names; `emit` writes `Sort` + name.

Made impossible by the types (each the root of a past defect or a scope boundary):

| Excluded | How |
|---|---|
| requires/ensures, rule priorities, `owise` on rules | no field holds them; `emit` writes `\top` and no priority attribute |
| hooks, domain values, collections in clauses and rules | `Term` has no `\dv`; `wf` resolves application heads only among constructors and the user's functions |
| repeated or misnamed formals (review 2, finding 7) | `emit` generates the formals `X0, X1, …` |
| capture between formals, pattern variables and generated binders (review 2, finding 4) | every user variable is emitted as `Var` + name; generated names (`X…`, `Val`, `K…`, `From`, `SelectorInput`) never start with `Var`; exclusions bind renamed copies; selector-domain axioms exist only for the helper sorts, with fixed names |
| sort annotations disagreeing with declarations (review 2, findings 2 and 5) | `emit` writes every sort annotation from declared sorts |
| constructor, functionality and no-junk axioms with arbitrary content (review 1, finding 6; review 2, finding 1) | `emit` generates them from the declarations |
| loose hooked axioms beyond a fixed set (review 1, finding 6c) | they are exactly the prelude constant's |
| mutual recursion | a function's right-hand sides may call only functions declared before it, and itself |

The conditions of `wf` (each a short structural function, no fuel):

| Condition | Lean | Why |
|---|---|---|
| every sort and every symbol or alias that `emit c p` declares is declared once (a condition on the core's names, read off the text) | `namesOK` | a duplicate generator would get a distinctness axiom against itself (review 2, finding 8a); a user name equal to a fixed or generated one would redefine it |
| constructors and functions take user sorts, K or KItem and build user sorts; `$PGM` has a user sort | `declsOK` | sorts are declared and well-formed (review 2, finding 8b); no hooked sort in the operational part |
| subsorts between distinct user sorts, at most one supersort each, no supersort is a subsort | `subsortsOK` | no diamonds, also through KItem, so Cons-Dist and Cons-Coh decide when injections overlap |
| clauses: argument patterns of the declared sorts (constructors, injections, as-patterns), linear, binding every variable; right-hand side of the result sort | `clauseOK` | the equation is well-sorted and its exclusion binds exactly the clause's variables (review 1, finding 5) |
| catch-all clause: one variable per argument, of its sort | `owiseOK` | it applies wherever no other clause does (review 1, finding 4; review 2, finding 7) |
| total: a catch-all clause, or a single clause of variables | `fnOK` | evaluation is defined on every ground argument |
| deterministic: the other clauses pairwise do not overlap (different constructors, a constructor and an injection, or injections from incomparable sorts never overlap) | `overlap` | at most one equation applies |
| certificate: every recursive call passes, at the designated position, a variable bound strictly inside that clause's pattern there; the traversal is structural over the whole right-hand side | `Certificates.ok`, `decreasingOK` | the argument at the position strictly decreases, so evaluation terminates (with calls to earlier functions only) (review 1, finding 3; review 2, finding 6) |
| presentation: every clause, catch-all clause, exclusion and rule names each of its variables, all names distinct | `Presentation.ok` | the emitted KORE keeps the core's variables apart |
| rules: left-hand side of the configuration sort over constructors, injections, as-patterns, linear, binding every variable; right-hand side of the configuration sort over constructors and the user's functions | `ruleOK` | the step matches and evaluates (review 1, finding 8) |

`wf d = namesOK d ∧ Semantics.ok c ∧ Certificates.ok z c ∧ Presentation.ok p c`; `Semantics.ok` is the conjunction of `declsOK`, `subsortsOK`, `fnsOK` (clauses, catch-all, totality, overlap) and `ruleOK`. The conditions are those of the unsplit `wf`, regrouped; the presentation check also requires each name list to have one name per variable, which the unsplit structure (names stored with the variables) guaranteed by construction.
Every function must satisfy these, not only the ones the rules reach.
No sort is required to have a value: a user sort without a ground term (`Semantics.valueless`, the least fixpoint `valueSorts` misses) has no value, Γ has a model all the same (its sorts hold the values), and `Step` and the statements over `coreOK` ask no sort to be inhabited. The account prints those sorts; the text's G-nonempty for them is not in Γ (as for every sort, `sigItems`).

### The prelude constant

Every krust output carries the same prelude modules (BASIC-K, KSEQ, INJ, K) and, inside the user module, the same declarations and axioms of the builtin sorts (Bool, Int, KConfigVar, List, MInt, Map, Set: 7 sort declarations, 48 hooked symbols with their `assoc`/`unit`/`idem`/functional axioms and two hooked equations), of the helpers `#KConfigValue`, `isK`, `project:Int`, …, of the generated top cells, and the Map `\ceil` simplification. They are not generated and not validated: `prelude/f0-prelude.kore` holds them verbatim (the four modules and eight `F0-*` slices of `milestone-1/kore/definition.kore`), and `emit` places each slice at a fixed position of the user module. So the loose hooked axioms of an F0 definition are a fixed finite set (plus the `⊤ ∨ ⊥` no-junk axioms of Bool, Int and KConfigVar, which `emit` writes), whose satisfiability in the witness model is argued once (section 5). The kompile-generated hook-related declarations of the configuration (`initKCell(Map)`, `initGeneratedTopCell(Map)`, `<generatedCounter>(Int)`) are part of this text or of `emit`'s fixed lines. `SpecChecks.lean` checks that the Lean data naming the text's sorts and constructors agrees with its declarations.

### What F0 leaves out, and where it comes back

| Out of F0 | Why | When |
|---|---|---|
| requires/ensures, domain values and hooked symbols in clauses and rules | need Bool and Int domain theories | M2 |
| rule `priority`/`owise` | not in Γ_D (Q3) | when a corpus case needs it |
| collections modulo A/AC in clauses and rules | matching modulo AC | M3 |
| mutual recursion; totality other than a catch-all or a single variable clause; recursion needing a lexicographic order | `fnOK` is a syntactic sufficient condition | Q9 |
| existential right-hand variables, `#fresh` | not in the closure's simple form (Q8) | later |
| configurations other than `<k> $PGM:S </k>` | the cells are fixed text | Q15 |
| subsort chains among user sorts, two supersorts for one sort | depth one, no diamonds | Q11, Q16 |
| kompile output `emit` does not reproduce (rules before equations in the source, `[function, total]`, productions without `symbol(…)`, other attributes) | the generator follows peano's shape | Q14 |

### Peano, the regressions, and the review witnesses

Peano is in F0. `PeanoSpec.lean` writes it as an `Definition` (`peano = ⟨peanoCore, peanoPres, ⟨[none]⟩⟩`); `test/F0Check.lean` proves `wf peano = true`, `peano.emit = kore` (kore-lean's AST of `milestone-1/kore/definition.kore`) and `F0 kore` by `decide +kernel` (timings in section 8); `SpecChecks.lean` checks the same by compiled evaluation in the build. Its axioms: propext, Classical.choice, Quot.sound.

Every earlier mutation and every witness of both reviews is rejected; `SpecChecks.lean` records the mechanism (`diagnose`, not reviewed), `test/F0Check.lean` proves `¬ F0 w` for each in the kernel. Witnesses are built from peano, as `emit` of an `Definition` variant or as a mutation of KORE text (`Witnesses.lean`).

| Definition | Rejected by |
|---|---|
| peano without `pred(s(N)) = N` | emit differs (the owise premise lists a competitor no clause gives) |
| peano with a second, overlapping `pred` equation | wf: functions (overlap) |
| peano with `pred(s(N)) = pred(s(N))` | wf: certificate (no decreasing argument) |
| peano with an `owise` attribute on a rule | emit differs |
| peano with Nat's no-junk axiom missing `z` | emit differs |
| peano with the hooked `.Map` as a rule's right-hand side | wf: rules (no such head) |
| review 1, finding 3: decreasing position changes between calls | wf: certificate |
| review 1, finding 4: only `f(s x) = z [owise]` | emit differs (a catch-all has variable patterns) |
| review 1, finding 5: exclusion sharing a variable | wf: functions (parse yields an ill-formed clause) |
| review 1, finding 6: `[constructor]` `s(X) ∧ s(X) → s(z)`; `[functional]` `∃y. y = s(y)`; `[assoc]` `⊤Bool = ⊥Bool` | emit differs (each) |
| review 1, finding 7: selector domain constraining a fresh `Y` | emit differs |
| review 1, finding 8: rule right-hand side `z` | wf: rules |
| review 2, finding 1: `[constructor]` distinctness of `inj{Nat,KItem}`, `inj{Val,KItem}` | emit differs |
| review 2, finding 2: functional axiom whose `Val` changes sort | emit differs |
| review 2, finding 3: `hooked-sort B{y}` | emit differs (and the translator bug is fixed, section 11) |
| review 2, finding 4: formal `A` with an unbound exclusion; selector capturing `SelectorInput` | parse fails (each) |
| review 2, finding 5: `\equals{Nat, Bool}` in an equation, with `b1 = b2` | emit differs |
| review 2, finding 6: `f(x) = s¹⁰⁰⁰(f(x))` | wf: certificate |
| review 2, finding 7: `f(X0, X0) = z` | emit differs |
| review 2, finding 8: `z` declared twice; `c(B{})` for `hooked-sort B{S}` | wf: names declared once; wf: declarations over declared sorts |

With the split, the three termination rejections moved from "wf: functions" to "wf: certificate"; every other mechanism is unchanged (same diagnoses, same sentence numbers).
Positive controls, accepted: review 1's finding 3 with structural recursion on the first argument, finding 4 with a variable fallback, finding 5 with an exclusion over independent variables (each `emit` of an `Definition`).

## 2. Γ_D, curated (decision D2)

    Γ_D = Γ^AML ∪ (AML(Γ) without [simplification]) ∪ Γ_cons ∪ DV-Arity

Lean: `ΓD c p : Premises Sym` (`Curate.lean`); `curate c p` keeps the listed parts apart: Γ^AML and AML(Γ) are the translation of `emit c p`, Γ_cons is generated from the core's constructors and subsorts. DV-Arity (`dvArityAll`) is G-dv-arity, `s ∈ ⟦Sort⟧ → dv"v" s ⊆ ⟦s⟧`, for every literal string v: an infinite schema, possible because `Premises` is a predicate. Γ^AML lists it only for the literals occurring in D, but a ground configuration may contain any literal (`\dv{SortInt{}}("5")`), and without its arity axiom the literal could denote an element outside its sort, making soundness and completeness incompatible (review 1). It adds no functionality and no distinctness, so decision D1 (arity only) stands. The alternative, restricting ground configurations to the literals D mentions, would make peano's counter values beyond `"0"` unusable.
Peano: Γ^AML 141 axioms (unchanged from M1.2), AML(Γ) 184 of 202 (the 18 `[simplification]` axioms removed), Γ_cons 194.
As in M1.2, aml-port's `definedness` is in the premises at every variable, so `HasDefinedness (ΓD c p)` holds.

### Γ_cons

Generated from the core (`Cons.items c`, over `Semantics.ctorSorts`, `Semantics.gens`, `Semantics.subsorts`: the fixed text's constructors and cells and the user's): for each constructor sort N with generators g (constructors c : s̄ → N and injections `inj{A,N}`), in the papers' notation, free variables guarded by their sorts:

| Rule | Axiom | Status, source |
|---|---|---|
| Cons-Fun | `x̄ ∈ ⟦s̄⟧ → ∃y:N. g x̄ = y` | SOURCE: [FoSSaCS] §4.1 item 4, p. 208 (every non-subsorting production is total and functional). Repeats kompile's `[functional]`/`[subsort]` axioms where it emitted them; adds the missing ones for `kseq`, `dotk` (F4) |
| Cons-Inj | `x̄, ȳ ∈ ⟦s̄⟧ → g x̄ = g ȳ → x̄ = ȳ` (for g with arguments) | SOURCE: [FoSSaCS] §4.2 item 1, p. 210; for `inj{A,N}`: injective because a subsort is a subset ([Thesis] (7.25)) |
| Cons-Dist | `¬(g x̄ = g' ȳ)` for two generators of N, except two injections `inj{A,N}`, `inj{B,N}` with A, B comparable | SOURCE for two constructors: [FoSSaCS] §4.2 item 2, p. 210. CHOICE for injections (decision D2 asks for distinct injections into a common supersort): KORE keeps subsorts as coercions, and two incomparable sorts have no common element in the intended model; comparable ones overlap by Cons-Coh |
| Cons-Coh | `x ∈ ⟦A⟧ → inj{B,C}(inj{A,B}(x)) = inj{A,C}(x)` for declared A < B < C | CHOICE: the triangle [AML-TR] §6 (pp. 16–17) says coercion-based subsorting needs; with inclusions ([Thesis] (7.25)) it holds trivially. It is F1 restricted to subsort chains. Alternative: omit it; then a ground KItem has two representations whose elements may differ |
| Cons-NoJunk | `⟦N⟧ = μX. ⋁_g g Ȳ`, `Yⱼ = X` where g's argument sort is N, `⟦sⱼ⟧` otherwise; `inj{A,N}` contributes `inj A N ⟦A⟧` | SOURCE: [FoSSaCS] §4.2 item 3, p. 210; [AML-TR] App. F, Prop. 24; the subsort disjunct `⊤_A` of [FoSSaCS] becomes the injection's image. GAP for mutually recursive sorts (Q1) |

Not in Γ_cons: distinctness of sort names, disjointness of sorts, functionality of `append` (F4; Q10), functionality of domain values (decision D1).
Peano's Γ_cons by rule: Cons-Fun 31, Cons-Inj 27, Cons-Dist 122 (117 of them for the 16 generators of KItem), Cons-NoJunk 11, Cons-Coh 3. Generated from `peano : Definition` it is the M1.3 Γ_cons (read from the KORE) up to the order of the items, the orientation of 34 distinctness pairs and the order of the disjuncts of KItem's no-junk axiom (injections now in string order of their sources). A sample from GAMMA_CONS.txt:

```
[Cons-Fun]    ∃y:SortNat. z = y
[Cons-Fun]    x1 ∈ ⟦SortNat⟧ → (∃y:SortNat. s x1 = y)
[Cons-Inj]    x1 ∈ ⟦SortNat⟧ ∧ y1 ∈ ⟦SortNat⟧ → s x1 = s y1 → x1 = y1
[Cons-Dist]   y1 ∈ ⟦SortNat⟧ → ¬(z = s y1)
[Cons-Dist]   x1 ∈ ⟦SortNat⟧ ∧ y1 ∈ ⟦SortVal⟧ → ¬(run x1 = done y1)
[Cons-Dist]   x1 ∈ ⟦SortNat⟧ ∧ y1 ∈ ⟦SortState⟧ → ¬(inj SortNat SortKItem x1 = inj SortState SortKItem y1)
[Cons-Dist]   x1 ∈ ⟦SortKItem⟧ ∧ x2 ∈ ⟦SortK⟧ → ¬(kseq x1 x2 = dotk)
[Cons-Coh]    x ∈ ⟦SortNat⟧ → inj SortVal SortKItem (inj SortNat SortVal x) = inj SortNat SortKItem x
[Cons-NoJunk] ⟦SortNat⟧ = (μX. z ∨ s X)
[Cons-NoJunk] ⟦SortState⟧ = (μX. run ⟦SortNat⟧ ∨ done ⟦SortVal⟧)
[Cons-NoJunk] ⟦SortVal⟧ = (μX. inj SortNat SortVal ⟦SortNat⟧)
[Cons-NoJunk] ⟦SortK⟧ = (μX. kseq ⟦SortKItem⟧ X ∨ dotk)
```

### The simplification lemmas

`(curate D).lemmas` are the translated `[simplification]` axioms. They are not in Γ_D; each is a claim to check. Peano has 18 (`PeanoSpec.lean`, statements with `sorry`):

| Axiom | Lemma | Expected verdict | Lean |
|---|---|---|---|
| 112, 115, …, 183 (16) | selector inverse: `⌈project:S(x)⌉ → kseq(inj{S,KItem}(project:S(x)), dotk) = x` | consequence of Γ_D (from the selector-domain axiom and the selector's equation) | `selectorInverse_hold` |
| 3 (F1) | `inj{S2,S3}(inj{S1,S2}(T)) = inj{S1,S3}(T)` for all sorts | false in every model of Γ_D: at S1 = State, S2 = Nat, S3 = KItem it puts `inj{State,KItem}(t)` in the image of `inj{Nat,KItem}`, against Cons-Dist. Restricted to chains S1 < S2 < S3 it is Cons-Coh, so true | `F1_false` |
| 202 (F2) | `⌈K0 \|-> K1 Rest⌉ = (K0 in_keys Rest = false) ∧ ⌈K1⌉`, set variables | independent of Γ_D (hooks are loose): true where Map, Bool and `dv"false"` are single elements, false where `dv"false"` is empty, false for finite maps (TRANSLATION.md F2). With element variables in place of the set variables it is true for finite maps | `F2_independent` |

## 3. The closure axiom

    Γ_closure = { ∀y. •y ⊆ ⋁_r ∃x̄_r:s̄_r. (L_r ∧ y ∈ R_r) }

over the rules r of the core c, with axiom `\rewrites{C}(\and{C}(lhs, req), \and{C}(rhs, ens))`, with `L_r = AML2(\and(lhs, req))`, `R_r = AML2(\and(rhs, ens))` (the same translation as the rule axiom), and x̄_r the rule's variables with their sorts. Lean: `closureItem c p`, `Γclosure c p` (`Closure.lean`), from `rulePatterns c p` (the patterns of the rule axioms in `emit c p`, whose variable names come from p).

In words: `•y` is the set of elements that step to y. The rule axioms of Γ_D, `L_r → •R_r`, say that every instance of a rule is a step (a lower bound on `•`). The closure axiom says the converse: if x steps to y, then some rule r and some values of its variables make x an instance of its left-hand side and y an element of its right-hand side. Nothing else steps; in particular an element that is not a configuration has no predecessor.
Together they make "c has exactly the successors the rules give" a consequence, which is what stuck states, `owise` and exhausted searches rest on (`Q-negative-facts`).

| Part | Status, source |
|---|---|
| an axiom bounding `•` from above, separate from Γ_D | SOURCE: [OOPSLA23] p. 26 (the Step axiom, missing from kompile's theory); [MLE] §8.2 (Transition) defines transitions exactly; [syn-A] item 8, [syn-D] §1 |
| inclusion `•y ⊆ …`, not the equation `•y = …` of [MLE] | CHOICE: the lower bound is already the rule axioms. The two forms agree on the ground instances the statements use, where under DV-Fun each right-hand side instance denotes one element; they need not agree for all valuations: per-sort no-junk admits cyclic junk elements (Q1) and a reachable function has no functionality axiom, so a right-hand side may denote several elements at a junk argument, where the equation would force a step to each of them and the inclusion does not (review 9). No statement depends on the equation form (Q8) |
| `y` ranges over all elements, not only `⟦C⟧` | CHOICE: "the only way to make a step" ([OOPSLA23]) covers every step; non-configurations have no predecessor, so the unsorted and sorted all-path next agree on configurations (section 5) |
| no fixpoint | SOURCE-inference: [syn-A] item 8, one step is not recursive; [MLE] needs μ because its transitions are defined by induction on process terms |
| priorities: not represented | GAP: F0 has no rule priorities (section 1); a rule with priority would need `¬(⋁ higher-priority L)` inside its disjunct ([syn-A] item 8) and in its rule axiom (Q3) |

Peano's closure axiom (GAMMA_CONS.txt):

```
∀y. •y ⊆ ((∃VarN:SortNat. ∃Var_Gen4:SortNat. ∃Var_DotVar0:SortGeneratedCounterCell.
             (<generatedTop> (<k> (kseq (inj SortState SortKItem (run (s VarN ∧ Var_Gen4))) dotk)) Var_DotVar0 ∧ ⊤[SortGeneratedTopCell])
           ∧ y ∈ (<generatedTop> (<k> (kseq (inj SortState SortKItem (run (pred Var_Gen4))) dotk)) Var_DotVar0 ∧ ⊤[SortGeneratedTopCell]))
        ∨ (∃Var_Gen4:SortNat. ∃Var_DotVar0:SortGeneratedCounterCell.
             (<generatedTop> (<k> (kseq (inj SortState SortKItem (run (z ∧ Var_Gen4))) dotk)) Var_DotVar0 ∧ ⊤[SortGeneratedTopCell])
           ∧ y ∈ (<generatedTop> (<k> (kseq (inj SortState SortKItem (done (inj SortNat SortVal Var_Gen4))) dotk)) Var_DotVar0 ∧ ⊤[SortGeneratedTopCell])))
```

(`s VarN ∧ Var_Gen4` is the as-pattern `\and{SortNat}(s(VarN), Gen4)` of the KORE, T-and.)

## 4. Ground configurations

`isGroundTerm c t` (`groundSort c t` is its sort; both read the core only): t is built from generators (constructors without sort arguments, `inj{A,B}` for declared A < B) and domain values `\dv{b}("v")` whose sort is a well-formed instance of a base sort (its constructor declared and applied to as many well-formed sorts as it has parameters: `\dv{SortMInt{SortInt{}}}("0")` is ground, `\dv{SortMInt{}}("0")` is not; review 2); it is well-sorted (every argument has its declared sort, every sort argument is well formed); it is injection-normal (no `inj` directly under `inj`). Any literal string is allowed: Γ_D has the arity axiom of each (section 2).
`GroundConfig c t`: t is a ground term of the configuration sort `SortGeneratedTopCell`. Decidable.
Denotation: `den c = AML2(c)` (T-app, T-dv), a pattern with no free variable; `denIn I c` is its interpretation.

CHOICE: configurations are constructor terms, not terms with function symbols. A rule's right-hand side as written, `run(pred(s(z)))`, and its constructor form `run(z)` denote the same element in every model of Γ_D (`pred_s_z`), so the step statements say the same thing for either. The injection-normal constructor term is the canonical representation step equivalence compares syntactically. The comparison keeps literal spelling significant: `ModelsStandard` separates terms with different skeletons, not terms that differ only in a literal (`"0"` and `"00"`, or `"0"` and `"1"` in a model with a one-element `SortInt`), so syntactic equality of canonical terms implies, but is not implied by, equality of the elements denoted (review 10).
Injection normal form is needed for the same reason: `inj{Val,KItem}(inj{Nat,Val}(z))` and `inj{Nat,KItem}(z)` are one element (Cons-Coh), so only one of them is canonical.

## 5. The statements

### Step soundness

    StepSound c p f  :=  ∀t. GroundConfig c t → ∀t' ∈ f t.  Γ_D(c,p) ⊧ t → •t'

`c → •c'` holds in a model when every element c denotes steps to some element c' denotes; with ground terms denoting single elements (DV-Fun), when the one steps to the other. c and c' are closed, so no sort guard is needed: their sorts are carried by the terms' well-sortedness.
Rules out: a function that returns a configuration the rules do not reach in one step. Does not rule out: returning nothing.

### Step completeness

    StepComplete c p f  :=  ∀t. GroundConfig c t →  Γ_D(c,p) ∪ Γ_closure(c,p) ⊧ t → ◦(t'₁ ∨ … ∨ t'ₙ)     where f t = [t'₁, …, t'ₙ],  ◦φ ≡ ¬•¬φ

For `f c = []` the disjunction is `⊥` and `◦⊥` is `¬•⊤` (literally: `⊤` is `¬⊥` in aml-port): c has no successor.
`◦` is the unsorted all-path next of [OOPSLA23] p. 13. [AML-TR] App. J sorts it (`¬_Cfg • ¬_Cfg φ`). They are not equal as patterns: a non-configuration has no successor under Γ_closure, so it satisfies the unsorted `¬•¬φ` and not the sorted form, whose outer negation intersects with `⟦Cfg⟧`. They agree after intersection with `⟦Cfg⟧`, which is all StepComplete uses: its antecedent c denotes configurations (review 11).
Rules out: a function that returns nothing, or too few successors, where the rules give one. Does not rule out: extra wrong successors (soundness does).
It needs Γ_closure: without it, `done(z)` is not stuck in every model of Γ_D (`stuck_c₂_needs_closure`).

### Ground outputs

    OutputsGround c f  :=  ∀t. GroundConfig c t → ∀t' ∈ f t. GroundConfig c t'

The reference returns canonical (injection-normal constructor) terms; step equivalence compares them syntactically, literal spelling included (section 4).

### A model, and no degenerate models

    StdModelOK c p      :=  ∃M. M ⊧ Γ_D ∪ Γ_closure ∪ DV-Fun
    ModelsStandard c p  :=  ∀M ⊧ Γ_D ∪ DV-Fun.  (∀t ground. ⟦t⟧_M is one element)
                                            ∧ (∀t, t' ground of one sort. skel t ≠ skel t' → ⟦t⟧_M ∩ ⟦t'⟧_M = ∅)

`DV-Fun` (`dvFunctional`) is `s ∈ ⟦Sort⟧ → ∃y:s. dv"v" s = y` for every literal v; it is not part of Γ_D (D1 keeps T-dv's arity-only reading in milestone 1). `skel t` erases domain-value literals, since two literals may denote the same element (F5).

Choice (the task's "standard model" question): the statement is the existence of a model plus `ModelsStandard`, not satisfaction by an explicitly defined M_D. Reasons:

1. StepSound and StepComplete quantify over every model; what makes them non-vacuous is that a model exists (`StdModelOK`) and that in no model do the configurations collapse (`ModelsStandard`). The second is what excludes the degenerate model the task names: a one-element carrier for a constructor sort with two generators violates Cons-Dist (for Nat, `z ≠ s(x)`), so it is not a model of Γ_D. F2's one-element `SortMap` is a model of Γ_D, and allowed: hooks are loose (decision of milestone 1), and F0's operational part does not use them.
2. `ModelsStandard` is the many-sorted, ground form of [TCS26] Lemma 40 (NOCONFUSION: ground terms are equal iff identical), which Γ_cons is built to give. It is a theorem about Γ_cons, checkable once per fragment.
3. An explicit M_D would make its definition part of the reviewed layer, a large one ([TCS26] App. A calls the carrier with curried partial applications the most tedious part), while it only witnesses consistency. With the existential form, M_D is part of the proof (M1.4b) and does not need review.
4. The proved theorems `not_complete_of_step` and `not_sound_of_complete` (section 7) use exactly these two statements.

The intended witness, for M1.4b, following [TCS26] App. A, Defs. 62–65: elements are the sort constants, the symbol tokens and their curried partial applications, a definedness token, the injection-normal ground constructor terms of the constructor sorts, and one element for each base sort; application builds terms (collapsing `inj` of `inj` by Cons-Coh); non-hooked functions are interpreted by evaluating their equations (∅ where no equation applies); hooked functions are the constant functions into the base sorts' single elements, and into some fixed ground term for constructor-sort results; every domain value of a base sort is that sort's element; `•y` is the set of x such that some rule instance has x on its left and y on its right.
Why each axiom holds there. The axioms `emit` generates from declarations (functionality, injectivity, distinctness of constructors, subsorts, no-junk) hold in a term algebra; `namesOK` makes each generator distinct, `subsortsOK` keeps injections from comparable sorts out of Cons-Dist's reach; a sort without a ground term is empty there. The user's equations hold because each function is total, deterministic and terminating (`fnOK`): on every ground argument exactly one equation's premise holds (the catch-all's premise is the negation of the others'), and evaluation terminates by the decreasing position and the declaration order. The selector and `isX` equations hold by their definitions. The prelude constant's axioms are a fixed set: its `assoc`/`unit`/`idem` and hooked-function equations relate terms of base sorts, each a single element, and its functional axioms of hooked symbols hold for constant functions; the Map `\ceil` axiom is a simplification, not in Γ_D. DV-Fun holds since each base sort is one element. Γ_closure holds by the definition of `•`.

### Soundness and completeness

    Conclusion c p ref  :=  StdModelOK c p ∧ ModelsStandard c p ∧ OutputsGround c ref ∧ StepSound c p ref ∧ StepComplete c p ref
    SoundAndComplete d ref  :=  wf d → Conclusion d.sem d.pres ref
    sound    : wf d = true → Obligations d → Sound d                 -- proved (KcoreSpec/Sound.lean)
    complete : wf d = true → Obligations d → Complete d ref          -- proved (KcoreSpec/Sound.lean)
    reordered_sameModels : namesOK d → Reordered d.emit k → SameModels (Theory.ofDefinition d.emit) (Theory.ofDefinition k)   -- proved (ReorderTheory.lean)

Lean: `KCore.Sound`, `KCore.Complete`, `sound`, `complete` (`KcoreSpec/Sound.lean`, over the theory `Γ d.sem` and the step's closure `Γstep d.sem`, no `sorry`), `reordered_sameModels`. The statements that read Γ_D or Γ_closure read the KORE `emit c p`; for a KORE text k in F0, `emit c p` is k up to the order of each module's sentences, and the theories of the two have the same models (`reordered_sameModels`), so they are statements about k (with Γ_cons of the constructors k declares). `reordered_sameModels` is proved in the checked layer (`ReorderTheory.lean`, Lean's three axioms): the declarations, aliases, axioms and literals of k are permutations of `emit c p`'s; a symbol's declaration is unique by `namesOK`, so the lookup by name finds the same one; G-sorts' disjunctions in two orders have the same interpretation; and every axiom of `emit c p` with a `\rewrites` or `\next` has no sort variables (by the shape of each generated axiom, and decided on the fixed text), so the G-next-arity items do not depend on which axiom comes first. The certificate is read by `wf` only.
`refStep : Semantics → StepFn` was declared `opaque` at the freeze, to be implemented; since M1.4 (2026-11-07) it is `def refStep := referenceStep` (`Encoding.lean`), the generic `successors` read through the KORE encoding of ground terms, with the same type (../VISION.md). It reads from the core: the rules; the clauses of the functions, with their catch-all clauses; and the subsort order (to match an injection pattern such as `inj{Val,KItem}(V)` against `inj{Nat,KItem}(n)`, and to put `inj` of `inj` into normal form after substitution). Reading the typed clauses rather than KORE equations removes the need to recognize kompile's premise shapes in the reference step.

### Step equivalence

    StepEquiv c ref cand  :=  ∀t. GroundConfig c t →  ∀x. x ∈ cand t ↔ x ∈ ref t

Equal as finite sets: order and repetitions are ignored, because StepSound depends on each element and StepComplete on the disjunction, neither on order or multiplicity. The comparison is syntactic agreement on canonical representations, literal spelling included. It is stricter than equality of the denoted elements in every model (two literals may denote one element, review 10); a candidate that respells a literal fails step equivalence although its successors may be the same elements. The transfer theorem does not depend on this.

    stepEquiv_transfer : SoundAndComplete d ref → StepEquiv c ref cand → wf d →
                          OutputsGround c cand ∧ StepSound c p cand ∧ StepComplete c p cand      -- proved (d = (c, p, z))

Step equivalence and `refStep` read the core only, so a bridge from a generated library (goal `G-k2lean-generic`) never sees ids, locations or names.

### What the presentation can affect

Ground configurations, `refStep`, `OutputsGround`, step equivalence and Γ_cons take the core only. Γ^AML, AML(Γ) and Γ_closure are translations of the text `emit c p`, so they read p. Exact equality of the translated items across presentations does not hold in general (item labels and name lists differ; the order of AML(Γ) follows the interleaving), and Γ_D is not stated over a canonical presentation, because then soundness and completeness for k would rest on an unproved invariance (section 9). What is invariant, stated in `Statements.lean`:

    PresInert c p p'   :=  Γ_D(c,p) and Γ_D(c,p') have the same models, and so have Γ_closure(c,p) and Γ_closure(c,p')
    PresentationInert  :=  ∀c p p' z. wf (c,p,z) → wf (c,p',z) → PresInert c p p'          -- stated, open (a Prop, not a theorem)
    conclusion_of_presInert : PresInert c p p' → Conclusion c p ref → Conclusion c p' ref   -- proved

Why it should hold: the translation reads no attribute but `[simplification]`, which `emit` never writes from p; premises are sets, so sentence order does not matter; and a variable's name enters the translated pattern only through which occurrences share it, which `Presentation.ok` fixes (distinct names, user names prefixed `Var`, generated names not). Evidence: `SpecChecks.lean` gives peano's core a presentation with every name, id, location, keyword, the source and the interleaving changed; `wf` accepts it and Γ^AML, AML(Γ), Γ_cons, the lemmas (as sets of patterns) and Γ_closure come out identical.

## 6. The peano instance

Rules: `<k> run(s(N)) => run(pred(s(N))) </k>` and `<k> run(z) => done(z) </k>`, with `pred(s(N)) = N`, `pred(_) = z [owise]`.
As an F0 definition (`peano = ⟨peanoCore, peanoPres, ⟨[none]⟩⟩`, `PeanoSpec.lean`; the certificate is empty since `pred` does not recurse): sorts Nat, State, Val; productions `z`, `s`, `Nat < Val`, `pred` (one clause and a catch-all, no recursion), `run`, `done`; `$PGM : State`; the two rules as kompile compiled them (`run(s(N) #as Gen4) => run(pred(Gen4))`, `run(z #as Gen4) => done(Gen4)`, the counter cell a variable `DotVar0`).
Configurations (`PeanoSpec.lean`): `cfg(st) = <generatedTop>(<k>(kseq(inj{State,KItem}(st), dotk)), <generatedCounter>(\dv{Int}("0")))`, and `c₀ = cfg(run(s(z)))`, `c₁ = cfg(run(z))`, `c₂ = cfg(done(inj{Nat,Val}(z)))`. All three are ground configurations, checked by `decide`; `cfg(run(pred(s(z))))` is not (it applies a function).

Working out the successors: c₀ matches rule 1 with N = z; the right-hand side is `run(pred(s(z)))`, and `pred(s(z)) = z` by the first equation (Γ_D ⊧ `pred(s z) = z`; the owise equation does not apply since its premise excludes `s(_)`). So the successor element is the one `run(z)` denotes. c₁ matches rule 2 only. c₂ matches no rule.

| Lean (all `sorry`, proofs in M1.4a) | Statement |
|---|---|
| `step_c₀` | Γ_D ⊧ c₀ → •c₁ |
| `pred_s_z` | Γ_D ⊧ cfg(run(pred(s(z)))) = c₁ |
| `complete_c₀` | Γ_D ∪ Γ_closure ⊧ c₀ → ◦c₁ |
| `step_c₁`, `complete_c₁` | Γ_D ⊧ c₁ → •c₂;  Γ_D ∪ Γ_closure ⊧ c₁ → ◦c₂ |
| `stuck_c₂` | Γ_D ∪ Γ_closure ⊧ c₂ → ¬•⊤ |
| `stuck_c₂_needs_closure` | ¬(Γ_D ⊧ c₂ → ¬•⊤) |

## 7. The statements are not vacuous

Proved for every d (no `sorry`; axioms propext, Classical.choice, Quot.sound):

- `not_complete_of_step`: StdModelOK c p → ModelsStandard c p → t, t' ground → (Γ_D ⊧ t → •t') → ¬ StepComplete c p (fun _ => []).
- `not_sound_of_complete`: StdModelOK c p → ModelsStandard c p → t, t' ground → (Γ_D ∪ Γ_closure ⊧ t → ◦(⋁ l)) → (every t'' ∈ l is ground with skel t'' ≠ skel t') → ¬ StepSound c p (fun x => if x = t then [t'] else []).

Instantiated for peano (resting on `step_c₁`/`complete_c₁`):
`empty_not_complete : wf peano → ¬ StepComplete peanoCore peanoPres (fun _ => [])`, and `loop_not_sound : wf peano → ¬ StepSound peanoCore peanoPres (fun x => if x = c₁ then [c₁] else [])` (run(z) does not step to itself).
`test/F0Check.lean` discharges the hypothesis by kernel evaluation (`wf_peano`, `peano_empty_not_complete`).

## 8. Status

| | Declarations |
|---|---|
| proved | `stepEquiv_transfer`, `not_complete_of_step`, `not_sound_of_complete` and their lemmas `interpret_disjList`, `interpret_allNext_congr`, `groundConfig_sort`; `conclusion_of_presInert` with `satisfiesAll_union`, `SameModels.union`, `SameModels.entails`; `F0.sound`; `reordered_sameModels` (ReorderTheory.lean, 2026-11-07); `Witnesses.fresh_literal_has_arity` (`#print axioms`: propext, Classical.choice, Quot.sound, checked in `SpecChecks.lean`); in `test/F0Check.lean` by `decide +kernel`: `wf_peano`, `emit_peano`, `peano_F0`, the 24 `*_not_F0` (six mutations, eight review-1 and ten review-2 witnesses) and the three positive controls (propext, Classical.choice, Quot.sound) |
| proved from `wf` and `Obligations` | `sound`, `complete` (`KcoreSpec/Sound.lean`, no `sorry` in the library) |
| `sorry` | peano: `step_c₀`, `pred_s_z`, `complete_c₀`, `step_c₁`, `complete_c₁`, `stuck_c₂`, `stuck_c₂_needs_closure`, `selectorInverse_hold`, `F1_false`, `F2_independent` |
| depend on `sorry` | `empty_not_complete`, `loop_not_sound`, `peano_empty_not_complete` |
| stated, open (a `Prop`, used by no theorem) | `PresentationInert` |
| `opaque` | `refStep` |

Timings (host load 25–65 on 32 CPUs): elaboration of `Prelude` 0.9 s, `Definition` 0.9 s, `Emit` 0.7 s, `Parse` 0.7 s, `Fragment` 0.5 s, `Curate` 0.5 s, `Statements` 1.4 s, `PeanoSpec` 1.8 s, `Witnesses` 0.6 s, `SpecChecks` 1.0 s (compiled checks of peano and all witnesses included); `lake build` after the redesign under 10 s incremental. Kernel (`test/F0Check.lean`, 608 s wall in all): `wf peano` about 4 s, `emit peano = kore` about 19 s, `F0 kore` (with `parse`, about 11 s) 45–50 s; the 27 witness and control decisions about 500 s together. `gammad --spec` under 0.1 s. `GAMMA_D.txt` regenerates byte-identical after the translator fix. After the core/presentation/certificate split (2026-11-06, host load 55 falling to 15): `lake build` green; `GAMMA_D.txt` byte-identical and `GAMMA_CONS.txt` identical except the two new report lines; `test/F0Check.lean` 575 s wall: `wf peano` 6 s, `peano.emit = kore` 28 s, `F0 kore` 67 s, the 27 witness and control decisions about 506 s, all proved. That run flagged one stale statement (`peano_empty_not_complete` still said `StepComplete peano`). It is fixed, and the fixed statement was typechecked on its own; the file has not been run again.

## 9. CHOICEs and GAPs of this step

| Id | Status | Summary |
|---|---|---|
| Cons-Fun, Cons-Inj, Cons-NoJunk (single sort) | SOURCE | [FoSSaCS] §4.1–4.2 |
| Cons-Dist for constructors | SOURCE | [FoSSaCS] §4.2 item 2 |
| Cons-Dist for injections | CHOICE | decided in D2; comparable pairs omitted |
| Cons-Coh | CHOICE | coercion triangle; F1 on chains |
| Cons-NoJunk, mutual recursion | GAP | Q1 |
| closure: separate axiom | SOURCE | [OOPSLA23] p. 26, [MLE] §8.2 |
| closure: inclusion, all y | CHOICE | Q8 |
| configurations as injection-normal constructor terms | CHOICE | section 4 |
| ◦ unsorted | CHOICE | [OOPSLA23] p. 13; agrees with [AML-TR] App. J on configurations, under Γ_closure |
| ∃-model + ModelsStandard instead of M_D | CHOICE | section 5, Q2 |
| DV-Arity for every literal in Γ_D | CHOICE | section 2; review 1 |
| F0 as `Definition` + `emit` + exact round trip; kompile's hashes, locations and minted names carried in the presentation part | CHOICE (decision `Q-f0-shape`) | section 1; alternative: a canonical pass erasing ids on both sides, rejected because soundness and completeness for k would then need Γ_D's invariance under it |
| the round trip up to the order of each module's sentences (2026-11-07) | CHOICE | section 1; `../findings/M1.6-scale-probe.md` §1.2 limits 3–4: krust's sentence order depends on module names; the invariance this needs is one statement, `reordered_sameModels`, about order only; alternative: `emit` reproducing krust's name-dependent order, rejected as more reviewed text for no meaning |
| `Definition` split into core, presentation, certificate; statements reading Γ_D or Γ_closure take (core, presentation), the others the core; `PresentationInert` stated, not proved | CHOICE | sections 1 and 5; alternative: Γ_D over a canonical presentation, rejected as above |
| the prelude constant: krust's fixed text, not generated or validated | CHOICE | section 1; Q18 |
| configuration fixed to `<k> $PGM:S </k>`; subsorts of depth one; functions call earlier functions | CHOICE | section 1; Q15–Q17 |
| DV-Fun only in StdModelOK/ModelsStandard | CHOICE | D1 kept; Q5 |
| Step equivalence as set equality of canonical terms, literal spelling significant | CHOICE | Q6 |
| the conditions of `wf` | CHOICE | the boundary itself; each condition's reason in section 1 |
| rule priorities | GAP | Q3 |

## 10. Open questions for Sebastien

Q1. No-junk for mutually recursive sorts. Per-sort `⟦N⟧ = μX. …` ([FoSSaCS]) leaves cyclic junk across K, KItem, KCell, KCellOpt and the top cells (e.g. an element j with j = `#KConfigValue(kseq(j, dotk))` is not excluded). Options: (a) keep the per-sort form; (b) one joint fixpoint over all constructor sorts, which needs sort disjointness as an extra axiom; (c) Bekić-nested fixpoints, one formula per sort, large; (d) [Thesis] Def. 5.4's product-sort form. Recommendation: (a) for M1. No M1 statement needs no-junk: ground steps need only no-confusion. Revisit with symbolic statements.

Q2. Standard model: ∃-model + `ModelsStandard` (chosen, section 5) or an explicit M_D in the reviewed layer. Recommendation: ∃-model.

Q3. Rule priorities and `owise` on rules. kompile emits them as attributes only, so Γ_D (attributes ignored, D-attributes) treats an `owise` rule as always applicable. Recommendation: keep them out of F0 now; when a case needs them, add the priority premise `¬⋁_{r' ≻ r} ∃x̄'. L_r'` to the rule axiom and to its closure disjunct ([syn-A] item 8), as a translation CHOICE.

Q4. Requires and ensures (Bool terms) are out of F0 until the Bool domain theory (M2). Recommendation: as planned.

Q5. Domain values: D1 keeps them arity-only, so a configuration containing `\dv{Int}("0")` may denote ∅ or several elements in some models of Γ_D. The step statements stay true there; non-vacuity uses DV-Fun as an extra premise. Recommendation: add DV-Fun (and distinctness of literals) to Γ_D in M2 with the domain theories.

Q6. Step equivalence compares successor lists as sets (chosen). Alternatives: as multisets or lists, which would also constrain order and repetition, which no statement depends on. Recommendation: sets.

Q7. Successors as injection-normal constructor terms, i.e. configurations taken up to function evaluation (chosen, section 4), rather than the right-hand side as written. Recommendation: constructor terms.

Q8. Closure as inclusion (chosen) or as [MLE]'s equation. They agree on the ground instances the statements use; for all valuations they can differ wherever a right-hand side denotes several elements (junk arguments, Q1; existential variables, outside F0). Recommendation: inclusion; reconsider with `?X` variables or when Q1 is settled.

Q9. Totality (a catch-all clause, or a single clause of variables) and termination (calls only to earlier functions, self calls decreasing at one fixed position) are sufficient, not necessary. They exclude `owise` clauses with constructor patterns, functions total by exhaustive non-owise clauses, mutual recursion, and recursion needing a lexicographic or size-change order. Recommendation: keep them for M1.4; add an exhaustiveness check and a lexicographic order when T3's census shows which corpus cases they exclude.

Q10. kompile emits no `(Function)` axiom for `append` although it is declared `functional` (F4); Γ_cons covers constructors only. Recommendation: under `G-theory-audit`, add `(Function)` for every `functional`/`total` symbol that lacks one, as a separate reviewed list; not needed by F0's operational part.

Q11. F0's subsort condition forbids diamonds. A diamond would need distinctness "outside the common subsort", which Γ_cons cannot state with Cons-Dist alone. Recommendation: keep the restriction until a corpus definition has one.

Q12 (resolved by `Q-f0-shape`). The tolerance of the alpha-equivalence comparison is gone: F0 compares exactly. A kompile that orders binders or disjuncts differently, or nests `\or` differently, is outside F0 until `emit` reproduces it.

Q13 (resolved by `Q-f0-shape`). Loose hooked axioms are no longer admitted by shape: they are exactly the prelude constant's.

Q14. Coverage of `emit`. It reproduces krust's output for peano exactly; it generalizes peano's shape (declaration order of productions, functionality/injectivity/distinctness per constructor against later ones, no-junk generators as constructors then injections in string order of their sources, binary `\or` chains ending in `\bottom` for `owise` competitors, all equations before all rules). For other definitions in T3's F0 class krust may differ: rules and equations interleaved in source order, `[function, total]` functions (functional axioms), productions without `symbol(…)` (mangled labels, no `symbol'Kywd'`), extra attributes (`format`, `left`, …), several subsorts into one sort. Recommendation: run `parse`/`diagnose` (compiled, `lake exe gammad FILE --spec`) over T3's 10 F0-class definitions before M1.4b and extend `emit` where they fail, each extension reviewed like the rest.

Q15. The configuration is fixed to `<k> $PGM:S </k>` (the generated top, counter and option cells are fixed text). Recommendation: keep for M1.4; generalize the cell structure (cells as `Definition` data, their declarations and helpers generated) when a corpus case in F0 needs another configuration. Closed: the configuration is the presentation's cell tree; the leaf holding `$PGM` is the one the text's initializer equations give it (`Presentation.pgmCell`, `<k>` or another), of content K or `$PGM`'s sort, and no cell named `k` is required (`Presentation.cellsOK`).

Q16. Subsorts among user sorts have depth one and each sort at most one supersort, so that no two incomparable sorts share a subsort (also through KItem, which is above every sort). Recommendation: keep until a case needs chains; chains need kompile's transitive subsort axioms and no-junk injections reproduced, and diamonds need Q11.

Q17. A function may call only functions declared before it (and itself). This is stricter than "no mutual recursion" when the source declares a callee after its caller. Recommendation: keep (it is the simplest acyclicity argument); replace by a topological check if T3 finds such a case.

Q18. kompile's equation ids are hashes `emit` cannot compute. The user's sorts, clauses, rules and `initKCell` carry theirs in the presentation (`Presentation`); those of the k cell's and the generated cells' helper equations are fixed in `Prelude.lean`, on the assumption (from one kompile run) that they do not depend on the definition. Recommendation: confirm with a second kompile output (any T3 case); if they vary, move them into the presentation.

Q19. Kernel cost. `F0 kore` takes 45–50 s in the kernel (of which `parse` about 11 s and the comparison `peano.emit = kore` about 19 s), against 12 s for the old validator; the 27 witness and control decisions take about 500 s together (61 s for the old eight). Recommendation: acceptable outside the default build; where M1.4 needs `F0 k` for a corpus definition, give d explicitly and prove `wf d` and `d.emit = k` (as for peano), which skips `parse`.

## 11. Review responses

### Round 1 (2026-11-06, `../findings/M1.3-astra-review.md`)

The fixes below were made in the old validator; with the redesign (round 2 below) the witnesses of findings 3–8 are rejected as listed in section 1, and the conditions named here (F0-8 … F0-14) no longer exist.

| Finding | Response |
|---|---|
| 1. literals outside D had no arity axiom | Fixed. Γ_D contains G-dv-arity for every literal string (`dvArityAll`; section 2). Check: `Witnesses.fresh_literal_has_arity`, and `cfgLit "review-fresh"` is a ground configuration |
| 2. ill-formed sorts of domain values accepted | Fixed. Sorts are checked recursively, including parameter counts (`wfSort`), for domain values, variables and sort arguments; instantiated base sorts are supported. Checks in `SpecChecks.lean`: `\dv{SortMInt{}}` rejected, `\dv{SortMInt{SortInt{}}}` accepted |
| 3. F0-14 did not establish termination | Fixed. One argument position must decrease in every self call of a function (F0-14). Witness rejected by F0-14; positive control accepted |
| 4. `owise` need not cover the remaining arguments | Fixed. An `owise` equation's arguments must be distinct variables of the declared sorts (F0-10); with the exact exclusion it covers every argument the others do not. Exhaustiveness checking is deferred (Q9). Witness rejected by F0-10 |
| 5. exclusion could add variable sharing | Fixed. Each exclusion disjunct is compared with the regenerated one by binding-aware alpha-equivalence over the whole tuple, with exact binding (F0-10). Witness rejected; control accepted |
| 6. recognized kinds could hold contradictions | Fixed structurally. `[functional]`/`[subsort]` and `[constructor]` axioms are regenerated from declarations and compared by alpha-equivalence (F0-8); structural and hooked-equation axioms are restricted to hooked-term equations at a base sort, which hold in the witness model (F0-9, F0-10). Premises of equations are regenerated too. The three witnesses are rejected by F0-8, F0-8, F0-9 |
| 7. selector-domain axiom ignored the constrained variable | Fixed. The axiom is regenerated from the selector's equation and compared by alpha-equivalence (F0-11). Witness rejected |
| 8. rule operands not checked against the configuration sort | Fixed. Rule operands must have the configuration sort and requires/ensures be `\top{C}`; equation result and argument sorts must be the declared ones (F0-12, F0-10). Witness rejected by F0-12 |
| 9. inclusion and equation closure need not coincide | Accepted. The claim is restricted to ground instances (section 3, Q8). No Lean statement depended on it |
| 10. syntactic and semantic equality of successors | Accepted. Step equivalence is described as syntactic agreement on canonical representations with literal spelling significant (sections 4, 5). The Lean definitions are unchanged: `StepEquiv` was already syntactic, and the transfer theorem holds as proved |
| 11. sorted and unsorted ◦ agree only on configurations | Accepted. The claim now says they agree after intersection with `⟦Cfg⟧`, which is all StepComplete uses (section 5). No Lean change |

Not changed in round 1: the reviewer's model arguments for findings 1–8 were not mechanized. The fixes are checked by rejecting each witness. Soundness and completeness are `KCore.Sound` and `KCore.Complete`, with `sound` and `complete` proved from `wf` and `Obligations` (`KcoreSpec/Sound.lean`).

### Round 2 (2026-11-06, `../findings/M1.3-astra-rereview.md`), with the redesign `Q-f0-shape`

The re-review found that validating arbitrary KORE kept producing new defect classes. The response is the redesign of section 1, not a patch per finding: F0 is `emit` of a typed `Definition` that `wf` accepts, compared exactly. Each finding:

| Finding | Response |
|---|---|
| 1. constructor-axiom validation admitted distinctness of comparable injections | Eliminated by construction: no `[constructor]` axiom is read; `emit` generates them from the declarations (kompile emits no injection distinctness; Γ_cons's Cons-Dist still omits comparable pairs). Witness: emit differs |
| 2. alpha-equivalence allowed variable sorts to change | Eliminated: there is no comparator; exact equality compares every variable with its sort. Witness: emit differs |
| 3. a sort parameter named `y` captured by `sortConstantItem` (M1.2 translator bug) | Fixed in `Translate.lean`: the binder takes index `params.length + 1`, independent of names (and prints as `y'` if a parameter is named `y`); checked in `SpecChecks.lean`. `GAMMA_D.txt` regenerates byte-identical (no peano sort parameter is named `y`). A hooked sort outside the prelude constant is not in F0. Witness: emit differs |
| 4. regeneration captured names across equations and in selector domains | Eliminated by construction: formals are generated, user variables are emitted as `Var` + name, exclusions bind renamed copies with distinct names, selector-domain axioms are generated only for helper sorts with fixed names. Witnesses: parse fails (both) |
| 5. equation parsing discarded the predicate sort | Eliminated: `emit` writes every sort annotation; nothing is parsed into the reviewed layer. Witness: emit differs |
| 6. a fuel cutoff let deep self calls pass | Eliminated: `callsOf` is structural over the whole right-hand side; no function in the reviewed layer has fuel (`valueSorts` iterates as many rounds as there are sorts, which reaches the fixpoint). Witness: wf fails (functions) |
| 7. repeated formals passed the totality check | Eliminated by construction: formals are generated; a catch-all clause has one variable per argument with distinct names. Witness: emit differs |
| 8. signature validation admitted duplicate and malformed declarations | Fixed: `namesOK` (every sort, symbol and alias of the emitted text declared once) and `declsOK` (argument sorts user sorts, K or KItem; hooked sorts only from the prelude constant). Witnesses: wf fails (names), wf fails (declarations) |

Soundness and completeness are `KCore.Sound` and `KCore.Complete`, with `sound` and `complete` proved from `wf` and `Obligations` (`KcoreSpec/Sound.lean`). The redesign removes the validator from the reviewed layer; what remains to review is `Definition`, `wf`, `emit` and the prelude constant.
