# TIE-1: decision on the spike's result (node TIE-decision; C7, C14, R-15) and on the no-junk fixed point

Fable decision node, 2026-11-15. Read-only; nothing was built or run. Lean text marked **to run** is for the orchestrator.
Read: the spike's report; `test/TieEns.lean` at `kcore-kinds 1db4467e` (whole); `designs/TIE-0-semantic-tie.md` (whole); DONE-0's C7, C14, R-14, R-15, section 2.1, section 3; `findings/REVIEW-F-CE.md` finding 8 to 10 and D-CE-3; in the tree at `1db4467e`: `Tie.lean:150-215`, `FaithOK.lean:30-50`, `Faithful.lean:85-200`, `Kore/Gamma.lean:60-135`, `Kore/Translate.lean:336-354`, `test/Guards.lean:280-292`, four doc comments of `Parse.lean`, the header of `ModelSortsWitness.lean`, declaration lines only of `ModelCons.lean`; `f2-examples/ens.kompile.kore` lines 20-62, 77, 131, 272-275, 327-337, 1370-1385.
"Shown" is shown by reading the quoted text; "suspected" is argued, not checked.

## 0. Decisions in one paragraph

Outcome: **by class** (D1). `Tied` is given up for kompile's texts and replaced by a kernel-checked per-sentence account on the literals `k` and `d`, with an attribute agreement check; no parse certificate (D2). Sentences that apply a symbol Γ does not have are a principled limit under a checked side condition, in four groups; a generated function that a read sentence applies and that the reader takes as a parameter is a reader defect (D3). ΓSig's surplus is a named family, admitted only with a per-text check that it does not reach the text's sorts (D4). Set idempotence: Γ follows K's prose for `SET.concat` against the text's sentence 61; this is a contradiction between two parts of the trusted base, kept and recorded, and it is the one decision here that amends the trusted base, so it needs the orchestrator's confirmation (D5). C7: a positive value or step is derived from the sentences as written; a negative one (no value, no successor) is derived through the rule's reading and `Γstep` and is counted apart (D6). The per-sort least fixed point of `Cons.noJunkItem` states more than the text and nothing found uses it: replaced before R2 by the text's sentence (D7).

## 1. D1. Outcome: by class

**Decision.** Form (a) for the classes below marked A; the rest are tied natively before R2 and by kernel after it, or are a listed remainder.

| Class (TIE-0 row) | ens | Outcome | Before R2 |
|---|---|---|---|
| function equations (2, 3, 4, 6 for `isX`) | 30 | A: E and the converse by equality of `pat` (`fn_shape`), once D-CE-3 lands | yes |
| rewrite rule (1) | 1 | A: W1 proved (`rule_from_text`); W2 at instances where the right side is defined, to do | yes |
| `priority(n)` equation not `owise` (5) | 0 | A: W1 by the weakening lemma, on a fixture | yes |
| constructor `functional`, subsort, injectivity, distinctness, no junk (8, 11 to 14) | 38 | A: E; no junk by equality after D7 | yes |
| declarations (19) | 141 | A: E by equality, and the converse `sig_origin` (D4) | yes |
| function `functional` (10) | 17 | not in Γ: read into `FnHyp` (TIE-0 F4); row and note | row only |
| hooked `functional` for symbols Γ has (9) | 47 | Ev; native probe before R2, kernel proof after | probe |
| collection laws (15) | 9 | Ev (FD-1 stands); as row 9 | probe |
| library equations and lemmas over Γ's symbols (17, 18) | 82 | Ev, one proof per library sentence, shared by every text; as row 9 | probe |
| set idempotence (16) | 1 | refuted, recorded (D5) | done (`idem_refuted`) |
| sentences applying a symbol outside Γ | 36 | no direction; listed with the side condition (D3) | check |

**Reason.** TIE-0 section 6.3's own test for "by class" fires on two counts the spike measured: the first library sample cost 85 lines against the 40-line bound, and row 9 has no table lemma (7 of its 54 sentences have no symbol in Γ at all). "Not at all" does not fire: the only failure of pattern equality is the `∧ ⊤` wrapper, which D-CE-3 removes, and no item of `fnItems` or `ruleItems` lacks an origin (`gamma_origin`). "Throughout" is not available at any cost: 36 sentences have no statement in Γ's language and one is refuted.
Why the hooked classes may wait although `Hooks.lean` is in the cone: their proofs are per library sentence and the library is one text for every definition, so the cost is paid once, after R2, and a failure reopens the cone through DONE-0 section 2.6. To keep that from being the first time the graphs meet the library's sentences, node LIB-probe evaluates every such sentence natively on a grid of values before R2; a counter-example found there is a cone defect fixed before the freeze.

**`[goal].statement` must be reworded**: it says the tie is sentence by sentence with the reader trusted for the rest, which does not say that hooked sentences hold at values only, that some sentences have no direction, that one is refuted, or that `Tied` fails. Text, replacing the sentence "What a package's semantics states is tied … the reader is named as trusted.":

> What a package's semantics states is tied to the KORE text sentence by sentence through the translation of the text, for every hook interpretation and by sentence class. Function equations, rewrite rules, constructor, subsort and no-junk axioms and declarations are kernel-checked against their translated sentences: equal to them, entailed, or a named weakening that the sentence entails; and every premise of the package's theory is a translated sentence, a consequence of one, or a member of a named family. Sentences about hooked symbols (their functional axioms, the collection laws, the library's equations and lemmas) are stated at values only, kernel-checked where the row lists them and otherwise resting on the hook interpretations. A sentence that applies a symbol the theory does not have (cell initialisers, projections and hooked symbols that no read sentence applies) has no direction and is listed; the initial configuration rests on the reader. Set idempotence is the one sentence the theory refutes: the builtin prose for SET.concat is followed against it. The print-back check (Tied) is stated only for a text the emitter writes back up to order, which kompile's texts are not.

and "the builtin files' prose for hooks are trusted" gains ", the prose also where the text's set idempotence sentence contradicts it". Column "tied (C14)" becomes: "the per-sentence account of the user module is kernel-checked (every sentence in exactly one class); per class the count proved, the count stated at values, the count without direction, the count refuted; attribute agreement; `Tied` where it holds".

**Reverse when.** To "throughout" for the hooked classes: a library lemma gives Ev for every total hook from the table at under 40 lines a sentence. To "not at all": after D-CE-3 the equality `(fnItems c).map (·.pat) = fnText.map …` fails on ens, ens-owise or kimp for a reason other than binder keys, or kimp's per-sentence file does not check under the cap.

## 2. D2. Layer 1: the per-sentence account replaces `Tied` for kompile's texts

**Finding (shown).** `Tied k := parse k = .ok d ∧ wf d ∧ Reordered d.emit k` (`Tie.lean:194`). `not_reordered` is proved (433 emitted sentences against 405); the spike reports 189 text sentences not emitted and 217 emitted ones not in the text, and the same state for every `*.kompile.kore` (27 marked `differs`). `Parse.parse kore = .ok defn` is beyond the kernel at 12 GiB.

**Decision.** C14 part 1 becomes, for a text whose print-back is not the text up to order:

1. `wf d = true` (or `coreOK` with the failing `wf` conjunct named, as C14 already allows), kernel-checked on the literal `d`.
2. **The account**: one kernel decision per text that the class lists of the tie file partition the user module. To run:
   ```lean
   -- to run. `classes : List (String × List Nat)`: per class of D1's table, the indices of its sentences.
   theorem account : (classes.flatMap (·.2)).mergeSort = (userAxioms.map (·.index)).mergeSort := by decide +kernel
   theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl      -- exists in TieEns
   ```
   Each class then has its theorem over its own list (as `fns_entailed` is over `fnText`), or is a remainder class with its count. A sentence can no longer be left out by not being mentioned.
3. **Attribute agreement**: what `tr` does not translate and the reader reads from attributes (TIE-0 T1 to T3). To run, a Bool over `k` and `d` that reads neither `parse` nor `emit`:
   ```lean
   -- to run. For every symbol declaration of k's user module: `constructor{}` iff the name is a constructor of d.sem;
   -- `function{}` with read equations iff a member of d.sem.allFns; `hook{}(h)` iff a member of hookSigs or d.sem.params
   -- with `regHookOf h`; for every hooked sort its `unit`/`element`/`concat` are d.sem.colls' symbols;
   -- for every rule and equation its `priority`/`owise` attribute is the priority of the Rule or Clause at its index.
   theorem attrs_agree : attrsAgree k d = true := by decide +kernel
   ```
   `attrsAgree` is a new definition, a statement, pinned with C14's; it does not unfold the reader.
4. `Tied k` stays the form for a text where it holds (krust-written texts marked `exact`); it is not required of a row.

`Parse.parse k = .ok d` is not stated. Not the reader "trusted for layer 1": with the account and the class theorems nothing rests on `d` being the reader's output; what rests on the reader is exactly the remainder classes and, without item 3, T1 to T3. Not a staged parse certificate: it would certify where `d` came from, which no statement of layer 2 uses, at the cost of putting reader stages under kernel evaluation per text.

**Reason.** `Reordered d.emit k` certifies a print-back. Layer 2 relates `d` to `k` directly (R-15, confirmed by TIE-0 section 4 and by the spike's file: only the section "Layer 1" mentions `emit`). What `Tied` gave beyond layer 2 was two things: that no sentence of `k` is silently dropped, and that attributes are read as written. Items 2 and 3 state those two things without the reader.

**Is the gap a defect?** Not a cone defect, and not shown to be a reader defect. The emitter writes the library's and the generated sentences from the registry in its own form; once `Tied` is not required of these texts the emitter's form carries no claim. The part of the gap that matters is the sentences the reader holds no reading for, which is D3's list, and the account makes that list exact. Node GAP classifies the 189 and 217 natively by cause before R2, because one cause would be a defect if present: a text sentence of a class that has a direction (a constructor axiom, a function equation, a rule) that the reader's `d` does not hold. The spike's partition does not exclude it for the 157 sentences not attempted.

**Reverse when.** GAP finds such a sentence: reader defect, named by its class, fixed before the row's tie. Restore `Tied` as the requirement if the emitter is made to write kompile's library sentences back and `Parse.parse` is checked by parts (`Tied.of_parts`) under the cap; nothing here needs it.

## 3. D3. Sentences that apply a symbol absent from Γ

**Principle.** Γ is a theory over `kernelSyms c` (`FaithOK.lean:41`: constructors, functions, parameters, `hookSigs`, overloads). A sentence with a symbol outside it has no statement in Γ's language. That is a limit and not a weakening that matters when the symbol is applied by no sentence that has a direction: then every model of Γ extends to the symbol (suspected; not proved, and not required). The side condition is a kernel decision and is required per text. To run:
```lean
-- to run. `absent : List Nat`: the indices of the no-direction class.
theorem absent_closed :
    (userAxioms.filter (fun ad => !absent.contains ad.index)).all
      (fun ad => (symbolsOf ad.ax.pattern).all (fun n => (kernelSyms c).any (fun k => c.symName k.name == n))) = true := by
  decide +kernel
```
(`symbolsOf`: the applied symbol names of a pattern, to write.) It says: every sentence outside the listed class is over Γ's symbols, so no sentence with a direction applies an absent symbol.

| Group | ens | Decision | Reason |
|---|---|---|---|
| cell initialisers, counter getter (82, 210, 212 to 214) | 5 | principled limit; the initial configuration is the presentation's and is named as reader-trusted in `[goal]` (D1's text) | they define where a run starts, not the theory of rules and functions; no rule applies them. A later node (INIT, after R2, no cone) may state that the presentation's initial configuration is the value the text's initialiser equations give |
| projection equations (250 to 263) | 14 | principled limit while no read sentence applies the projection; when one does, the projection is in Γ as a function with the text's equation, direction E by equality, and where the text holds the domain axiom it is F-CE finding 8's clause | finding 8 and lane FX already read a library sort's projection so (`Parse.lean:1990`: "a function with the text's equation"). TIE-0 row 7 is corrected: the direction is row 2's, or none |
| `functional` of hooked symbols Γ lacks (36, 40, 42, 73, 75, 113, 114) | 7 | principled limit under `absent_closed`; such a symbol enters Γ only through its hook row of the construct table | Γ without an unused total symbol is weaker on that symbol only. TIE-0 row 9's count is 47, not 54 |
| library sentences over a symbol Γ lacks (171 and nine others) | 10 | as the row above; each is listed with the absent symbol | a sentence such as 171 speaks of `<<Int` alone |

**Reader defect named here (suspected, F-CE finding 8's last paragraph).** `isGenFn`'s doc (`Parse.lean:476`): a generated function "a user axiom may apply" is numbered "as parameter symbols without interpretation". For a symbol the text defines by an equation (a user sort's projection, an initialiser, `append`), Γ then states H's value where the text states the equation's. Defect `genFnAsParameter`: such a symbol is read as a function with the text's equations, as `libProjNames` does. Reader only; the tie of a text whose rule applies one is the check (`absent_closed` passes, and the sentence then has row 2's direction, which fails for a parameter).

**Reverse when.** A sentence with a direction is found to apply an absent symbol (`absent_closed` false): the symbol must enter Γ or the sentence is refused. The initial configuration becomes part of a headline statement: INIT moves before that statement's pin.

## 4. D4. ΓSig's arity items for symbols the text does not declare

**Finding (shown for the definition, native for the count).** `sigItems` ranges over `kernelSorts` (every registry sort) and `kernelSyms`, which holds all of `hookSigs`, whatever the text imports. `ΓDomains` states the graphs of the same symbols. So Γ speaks of Float, String and Bytes symbols in a text that declares none.

**Decision.** A named family, `registrySignature`: "the registry's sorts and interpreted hooked symbols, with their arities and graphs, whether or not the text declares them". Not a defect as long as the surplus does not reach a sort of the text. Required per text, before R2 for ens and the rows:
```lean
-- to run. The converse for ΓSig: each item is a declaration's item, or its symbol or sort is not declared by k.
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true := by decide +kernel
-- to run. The surplus does not reach the text's sorts: KItem's no-junk sentence (text line 337) is Γ's item.
example : (consItemsK c).any (·.pat == (trS U.axKItemNoJunk).pat) = true := by decide +kernel   -- after D7
```
The second is the test that matters: if `c.gens Srt.kitem` lists an injection from an undeclared registry sort, Γ's KItem has a disjunct the text's sentence lacks, the equality fails, and values of that sort are KItem elements the text's sentence excludes. That would be a defect: `gens` (or `kernelSorts`) must then be cut to the sorts the text declares. Not known today: the spike did not attempt the constructor no-junk class.

**Reason.** An assertion about names the text does not have is outside what the text can contradict; the families of TIE-0 section 2.2 are of the same kind, and this one was missing from its table (`dvArityAll` is the only ΓSig family there).

**Reverse when.** The second statement fails on any text, or a headline theorem is found to use an arity item of an undeclared symbol.

## 5. D5. Set idempotence

**What is shown.**
- Text: `axiom{R} \equals{SortSet{}, R}(_Set_(K:SortSet{}, K:SortSet{}), K:SortSet{}) [idem{}()]` (ens line 273; sentence 61). `_Set_` is declared `function{}`, `hook{}("SET.concat")`, `idem{}`, with no `functional{}` (line 131).
- Γ: `hook setConcat [s, s] = some none` at a non-empty `s`, not silent (`setIdem_bot`, G7), so `ΓDomains` states `_Set_(s, s) = ⊥`; `idem_refuted`: for every H, no model of Γ satisfies sentence 61.
- The text alone does not state that `_Set_` is undefined at a common member: ens holds no sentence that says so (searched: the Set sentences are 272 to 275, three `functional` axioms and the `|Set` rule at 1383). The KORE sentences about Set have a model in which `_Set_` is union. So the contradiction is not inside the KORE text.
- Γ's side comes from the builtin prose (trusted base (4)): `domains.md:706` "The sets are nilpotent, i.e., the concatenation of two sets containing elements [in common …]", fifteen lines above the production that carries `idem` (`:721`). I read these two lines only, outside my set, because the decision cannot be made without them.

**Verdict.** Neither of the two the question offers. It is a contradiction between the two parts of the trusted base: kompile's sentence (3) and the hook's prose (4), both from the same upstream file. Γ takes the prose. From the hook's graph on disjoint sets, sentence 61 and the text's associativity one derives `_Set_` = union at all values; so the two readings are whole and differ in `Step`: under union `SetItem(X) REST` also matches a set S with REST = S.

**Decision.** Keep Γ's set model for R2. Record, do not repair:
1. Row 16 of the direction table is its own class, "refuted, recorded", with three statements: `idem_refuted` (exists); the guarded sentence `⌈_Set_(K, K)⌉ → _Set_(K, K) = K` entailed at values (to write; W1 from the sentence is immediate); G7 cited as the reason no H rescues it.
2. DONE-0's trusted base (4) reads "the builtin files' prose for hooks, which have no defining KORE sentence". Sentence 61 is a KORE sentence about a hook, and Γ sides against it. The wording is amended as in D1, and `[goal]` names the sentence. **This amends the trusted base and DONE-0 section 2.6 as written would call `idem_refuted` a failing C14 theorem: it needs the orchestrator's confirmation, not only this node's.**
3. The upstream list gains: `domains.md` gives `_Set_` the attribute `idem` and describes it as nilpotent.
4. C7: sentence 61 is never a premise of a derivation (as sentence 155 is not, D6).

**Reason for keeping the prose side.** (i) Every statement Γ makes about `_Set_` off the diagonal also rests on the prose, since the text gives the hook no graph; taking the sentence at the diagonal and the prose elsewhere yields union, which the prose says the hook is not. One source has to be dropped at the common-member points under either choice. (ii) The text's own `|Set` rule (line 1383) writes union as `S1 (S2 -Set S1)`, which is the form needed when concatenation is undefined on a common member, and the text does not state `_Set_` total while it does state `|Set` total (evidence from the text, not a proof). (iii) The union reading has no model construction, no `sound`/`complete` and no matching proofs in the tree; it cannot be called a reading that passes.

**What each makes provable.** Prose side (today): unique decomposition of a set pattern; `Γ ⊧ _Set_({a},{a}) = ⊥`; sentence 61 refuted on every text that holds it. Union side: sentence 61 at values; a non-removing match, so more successors for every rule with a set pattern; the prose's sentence false.

**Reconciliation.** FD-1 (TIE-0 section 5) stands: the nine stated laws at values, no `ΓColls` change; FD-C's "idempotence is refuted" is `idem_refuted` on a text. G7 is the same fact at the hook: the point is not silent, so `ΓFallback` gives no H a say. `UnreadReason.setIdempotence`'s doc is accurate except "part of no reading": it is the one sentence Γ denies, and the doc should say so.

**Reverse when.** The orchestrator rules that a KORE sentence outranks the prose at a hook: node SET-union (cone: `hook` at `setConcat`, the set members of `collAxioms`, the set pattern matcher and `ModelColls`), before R2 if ruled before the lanes of stage 4 start, else a section 2.6 reopening. Or a text is found whose own sentences state the undefinedness (for instance a library lemma with `ensures notBool (X in S)` beside `in`'s `functional` axiom): then the text contradicts itself, the prose side needs no exception, and item 2 is withdrawn.

## 6. D6. C7: what "derived from the translated text" means

**Finding (shown).** `Pre H := TextFns ∪ ΓRules (cH H) ∪ Families H` (`TieEns.lean:435`): the 30 function sentences as written, Γ's rule item, the five predicate parts. `half_4` and `half_neg4` are `Pre H ⊧ …`; `run_neg4` is `Pre H ∪ Γstep ⊧ …`. `pre_model` gives a model. No sentence of the text says a configuration has no other successor (TIE-0 L6), and the text's rule sentence with Γ has no model (F3).

**Decision.**
1. Form (a) is: a Lean proof from a premise set made of (i) sentences as written, for the classes whose direction is E by equality; (ii) for a W-class sentence, Γ's item together with the W1 theorem that the sentence entails it and the equality of the item minus the added premise with the sentence (`rule_text`); (iii) families, each named in the row; with a model of the whole premise set. C7's wording "from their `tr s`" is amended to this.
2. A row records which of two kinds its expectation is. **From sentences**: a defined value, or a step that exists; the rule enters as the instance of the written sentence at the matched values (sentence 155 at N = 4 is consistent with Γ), to do in ens as `run_4`. **Through the reading**: no value where an `ensures` fails with no sentence but the equation's, no successor, an exact successor set; these use `Γstep` or the premise `⌈rhs ∧ ens⌉`, and cannot be had from the text's sentences at all. They are form (a), counted apart, and the row names the family.
3. `run_neg4` as proved is acceptable as the second kind. `half_neg4` is the first kind: its premise holds sentence 211 as written. The direct derivation without the cut is not required: the cut is sound and the premise set has a model; the indices "that determine it" are the row's record, not a kernel-checked minimality.
4. Every form (a) theorem is stated without `FnShape` after D-CE-3; a theorem under a hypothesis of that kind is not evidence.

**Reason.** What form (a) is for is that a misreading cannot be its own expectation. For a function equation that holds: the sentence is the premise. For the rule it holds through `rule_text`, a kernel equality between the item without `⌈rhs ∧ ens⌉` and sentence 155: a wrong right side or condition in `d` fails it. What stays an assumption is the meaning of the two additions, which are readings with C6 guards (`ruleRightDefined`, the closure), and saying "through the reading" in the row is the honest account of that.

**Reverse when.** A second fixture shows a misread rule passing `rule_text` (then the rule premise must be the written sentence at instances everywhere); or the count "through the reading" is most of a row's expectations and the gate asks for form (c) pairs for them.

## 7. D7. `Cons.noJunkItem`: the least fixed point states more than the text

**Check (shown).**
- Definition (`Kore/Gamma.lean:123`): `pat := inhOf (sortP N) ≡ .mu X (disjList (gs.map fun g => genPat N g (g.argSorts.map arg)))`, `arg s := if s == N then .svar X else inhOf (sortP s)`. It is in Γ for every sort of `consSorts` (`Faithful.lean:160`), K and KItem among them.
- Text (ens line 328): `axiom{} \or{SortCmd{}}(\exists{SortCmd{}}(X0:SortInt{}, Lbldone{}(X0:SortInt{})), \exists{SortCmd{}}(X0:SortInt{}, Lblrun{}(X0:SortInt{})), \bottom{SortCmd{}}()) [constructor{}()]`: every element of the sort is a generator applied to elements of the argument sorts. One unfolding; no `\mu` occurs in the file.
- The CN-3 author's claim is true. For a sort none of whose generators takes the sort itself (every sort of ens: Cmd, the cells, KItem) the two say the same, since X does not occur. For a sort with a generator over itself the text states a fixed point and Γ the least one: Γ excludes an element such as ω = s(ω), the text does not.
- For the sort K the text holds no no-junk sentence at all (no `\or{SortK{}}` in the file; module KSEQ, lines 20 to 49, holds `append`'s equations). Γ's item for K has no sentence in either form; it rests on the `constructor` attributes of `dotk` and `kseq` (TIE-0 T3).
- Users of the item at `1db4467e` (searched `KcoreSpec/` and `test/` for the name and for "no junk"): `ModelCons.noJunk_pat`, `ModelCons.sat_noJunk` and its caller at `:1140` (the model satisfies it), `ModelSortsWitness` (`noJunkAx_eq`, `noJunkAx_mem`, the refutation at `:111`, on a sort with one constant). Suspected from that search: no proof of a `Γ ⊧ …` statement uses the item, so nothing rests on leastness.
- TIE-0 already lists it (`Family.consNoJunk`, "Γ says more"). So it is known and named, not hidden; what was missing is a reason to keep it.

**Decision.** A defect in the sense of RULES ("asserts no more than K's text states") with no user: fix before R2. It is not an unsoundness: the intended model satisfies both forms, and every released `sound`/`complete` statement stays true, the completeness ones becoming stronger (fewer premises).

Text. The item is the translation of the sentence the text writes, as `fnItems` are since D-CE-3, so that the tie is an equality:
```lean
/-- Cons-NoJunk, the text's sentence: every element of N is a generator applied to elements of its
argument sorts, `\or{N}(\exists … g(x̄), …, \bottom{N}())`. -/
def noJunkAx (N : String) (gs : List Gen) : Kore.Axiom :=
  ⟨[], .or (srt N) (noJunkDisjuncts N [] gs ++ [.bottom (srt N)]), []⟩     -- `Build.noJunkDisjuncts`, as Emit writes it
def noJunkItem (N : String) (gs : List Gen) : Item :=
  { trAxiom [] [] ⟨0, "kernel", noJunkAx N gs⟩ with label := s!"cons-nojunk Sort{N}", rule := "Cons-NoJunk" }
-- to run, ens: sentence 328's index i
example : (consItemsK c).any (·.pat == (trS U.ax_i).pat) = true := by decide +kernel
```
If the n-ary `\or` or the binder names make `sat_noJunk` cost more than the direct form, the fallback is `pat := inhOf (sortP N) ≡ disjList (gs.map fun g => genPat N g (g.argSorts.map fun s => inhOf (sortP s)))` with one lemma that it and `tr` of the sentence entail each other; the lane reports which. For K the item stays, in the same form, as a family (`kNoJunk`, from the `constructor` attributes; T3), since the text has no sentence for it.

What changes.
- Cone: `KoreAML.Cons.noJunkItem` only (`consItemsK` and `ΓCons` keep their text).
- Model construction: the carrier does not change. `sat_noJunk` no longer interprets a `μ`: left to right is `consSort_shape` (a value of N is a generator applied to values), right to left is the arity of the generators. `noJunk_pat` is restated. The induction over values that proved inclusion in the least fixed point goes.
- `ModelSortsWitness`: `noJunkAx_eq` restated (`⟦Sort⟧ = u`); the refutation is unchanged in content.
- Theorems that use `μ` elsewhere and do not change: `collNoJunk` (`Faithful.lean:182`), `RunsSound.eventually`, `Signature.lean:145`, `Translate.sortsItem` (not in Γ).
- TIE-0's family table: `consNoJunk` goes; `kNoJunk` enters; row 14 becomes E by equality.
- `collNoJunk` is the same question for the collection sorts, for which the text has no sentence at all. It stays a named family (the sort's `unit`/`element`/`concat` attributes, T2): unlike the constructor item it has no text form to fall back to, and TIE-0's ω model reads it. The lane reports whether any `Γ ⊧ …` proof uses its leastness; if none does, replacing it by its one unfolding is a second, separate cone change for the R2 gate to decide.

**Reverse when.** A headline proof or a package theorem is found to use the least fixed point and has no proof from the one unfolding: then the `μ` stays, as the family `consNoJunk`, with a fifth trusted-base entry in `[goal]` ("a constructor sort holds finite terms only"), which is K's intent but no sentence of the text.

## 8. Nodes for the DAG

| Node | Work | Moves | When | Cone declarations |
|---|---|---|---|---|
| GOAL-2 | D1's `[goal]` text; trusted base (4) wording; C7's form (a) wording (D6); C14 part 1 as D2; TIE-0 table corrections (row 7, row 9's count, row 16's class, families `registrySignature`, `kNoJunk`) | C12, C7, C14 | now, before FIX-core | none |
| SET-confirm | orchestrator confirms or reverses D5 item 2 | C14, trusted base | now, before stage 4 | none; if reversed: SET-union (`hook` at `setConcat`, `collAxioms`, set matching, `ModelColls`) |
| NJ | D7: `noJunkItem` as the text's sentence; `sat_noJunk`, `noJunk_pat`, `ModelSortsWitness` restated; report on `collNoJunk`'s users | C14 row 14 | before R2; own cone lane, with stage 4 (touches `Kore/Gamma.lean`, `ModelCons.lean` only) | `KoreAML.Cons.noJunkItem` |
| TIE-ens-2 | on ens after FX (D-CE-3) and NJ: `FnShape` discharged and removed from every statement; `account`, `absent_closed`, `attrs_agree`, `sig_origin`; rows 8, 11 to 14, 19; rule W2 at instances; `run_4` from sentence 155 at N = 4; the guarded idempotence at values; `ens-owise` for binder keys (TIE-0 risk 1) | C14, C7 | before R2; gates FIX-core, TIE-kimp, KK-spike's tie | none; new statement definitions `AtValues`, `EntailsAtValues`, `attrsAgree`, `symbolsOf`, `surplusItem` go to ROOTS; a failure of rows 8 to 14 or 19 is a cone defect in `consItemsK`, `sigItems`, `gens` |
| GAP | native classification of the 189 unemitted and 217 emitted-only sentences by cause, with counts; any text sentence of a class with a direction that `d` does not hold is reported as a reader defect | C14 part 1 | before R2 (native, cheap) | none |
| LIB-probe | native evaluation of every row 9, 15, 17, 18 sentence over Γ's symbols on a grid of values against `hook`; a counter-example is a cone defect | C14, C2 hook rows | before R2 | `Hooks.lean` interpretations, `silentTable` if a counter-example is found |
| RDR-genfn | `genFnAsParameter`: a generated function a read sentence applies is a function with the text's equations (D3); fixture: a rule applying a user sort's projection | C14, C6 | with RDR-1 (reader only; before the tie of any row whose rules apply one) | none |
| TIE-kimp, KK-spike's tie | as DONE-0, in D1's classes with D2's account | C9, C10 | before R2, after TIE-ens-2 | as IMP |
| LIB-ev | kernel proofs at values for rows 9, 15, 17, 18, once for the library; a factored lemma per total hook first | C14 | after R2 | none; a failure reopens by section 2.6 |
| INIT | the presentation's initial configuration against the text's initialiser equations (D3) | C14 remainder | after R2 | none |
| EMIT-lib | optional: the emitter writes kompile's library and generated sentences back, so `Tied` holds again | none required | after R2 | none |

## 9. Findings by kind, and what was not read

Decisions: 7 (D1 to D7). Defects named: 1 cone (`noJunkItem`, D7, shown), 1 reader (`genFnAsParameter`, D3, suspected), 1 trusted-base contradiction (D5, shown). Checks required whose result is not known: KItem's no-junk equality (D4), `absent_closed` (D3), GAP's classification (D2), LIB-probe.

Not read: every proof body outside `TieEns.lean`; `Emit.lean`, `Build.lean` (the form of `noJunkDisjuncts`' caller is assumed from its doc line); `ModelCons.lean` beyond declaration lines, so "nothing uses leastness" rests on a name search; `Hooks.lean`, `CollExec*`, `ModelColls`; lane FX's tree (`kcore-fix`); `roundtrip.expected`; any text but ens; `domains.md` beyond lines 706 and 721 (the end of the nilpotence sentence is from memory); the ticket file beyond the two resume lines that say what lane FX is.
Resting on it: D5 reason (iii) ("no model construction for union in the tree") rests on TIE-0's search; D3's conservativity claim is argued, not proved; the three line counts of D1's last column are the spike's and TIE-0's.
