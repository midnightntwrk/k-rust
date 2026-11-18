/-
  The tie (C14) on `f2-examples/ens.kompile.kore`, sentence by sentence, against the translation of
  the text as written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), stated on the literal
  `defn` for every interpretation H. Nothing here reads `Parse.parse`, `emit` or `wf` except layer 1.
  Run from the package root: `lake env lean test/TieEns.lean` (about 100 s, `wf_defn` 54 s).

  Layer 1.
  - `wf_defn`: `wf defn = true` (kernel).
  - `not_reordered`: `Reordered defn.emit kore` is false: the emitted user module has 433 sentences,
    the text's 405 (the emitted writes the library's and kompile's generated sentences in its own
    form). So `Tied kore` does not hold, whatever `Parse.parse kore` is. `Parse.parse kore = .ok defn`
    is not kernel-checked here: one kernel evaluation of it exceeds 12 GiB.

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (30: `half`'s 211 and the 29 `isX` equations 215 to 243, 14 of them
    `[owise]`): `fn_shape` shows that each of the 30 items of `fnItems` is the translation of one
    text sentence, in the order `fnText` lists them (`FnShape`, a kernel decision); variable names
    and the `[owise]` exclusions' binders give equal patterns. The entailments `fns_entailed` (E)
    and `fns_from_text` (the converse) follow.
  - The rule (155): Γ's item (`prioRuleK`, with the premise `⌈rhs ∧ ens⌉`) is a consequence of the
    text's sentence (`rule_from_text`, W1, every H).
  - No junk of Bool, Int, KConfigVar (115, 121, 124), `\or{S}(\top{S}(), \bottom{S}())`: entailed
    by Γ, for every H (`nojunk_trivial_entailed`): they are logical truths.
  - No junk of Cmd and the cells (116 to 120, 122, 123): each translation is one of Γ's constructor
    items (`nojunk_items`, E by equality). KItem's (125) is Γ's item with its disjuncts in the text's
    order (`nojunk_kitem_order`): `Semantics.gens` lists the same generators in another order, and
    Γ entails the sentence, for every H (`nojunk_kitem_entailed`).
  - Constructor sentences (30: `functional` of the 8 constructors, the 15 `subsort` sentences, 6
    no-confusion sentences of one constructor, 1 of two): entailed by Γ, for every H
    (`cons_entailed`), each from the constructor items `consItemsK` holds for its generators
    (`cons_checked`).
  - Set idempotence (61): Γ with it has no model, for every H (`idem_refuted`).
  - Set-variable lemmas (126 to 130, 266: the definedness lemmas of `/Int`, `%Int`, `modInt`,
    `<<Int`, `>>Int` and kompile's `#Ceil(@K0 |-> @K1 @Rest)`): Γ with any of them has no model, for
    every H, and each holds at sets of at most one value (test/LibEvCeilEns.lean, `sN_refuted`,
    `sN_one`).
  - Library sample, 166 (`I -Int 0 = I`, a `simplification`): holds at every value of `I` in every
    model of Γ, for every H (`lib166`, direction Ev, from `ΓDomains`' graph of `-Int`).
  - Sentences applying a symbol Γ does not have (`absent_syms` for four of them): the cell
    initializers and the counter's getter, the 14 projections, seven hooked symbols' `functional`
    sentences, two library sentences (157 and 189) over symbols without a hook here, and the three
    sentences over instances of `ite` (99, `ite{Sort}`'s `functional` sentence, and 244, 245,
    `ite{K}`'s equations; `ite_absent`): no direction. The six sentences over the shifts (128, 129, 171, 172, 178, 179; 171 is `X <<Int 0 = X`)
    apply symbols Γ interprets: 171, 172, 178, 179 are of the class library, 128 and 129 of the
    class set-variable lemma. The equations of `bitRangeInt` and `signExtendBitRangeInt` (208, 265)
    apply symbols Γ interprets and are of the class library.

  Γ's content (the converse). `gamma_origin`: each premise of Γ (cH H) is a function sentence's
  translation, a rule item entailed by sentence 155, or one of the five parts Γ defines by
  predicates (`Families`), or definedness.

  The fixture's expectations (C7 form (a)), from `Pre H` (the 30 function sentences as written, Γ's
  rule item, the families; it has a model with the step's closure, `pre_model`, from `consistent`),
  each by the cut from Γ's theorem (`cutΓ`, `gamma_from`): `half_4`
  (`half(4) = 2`), `half_neg4` (`half(-4) = ⊥`), `run_neg4` (`run(-4)` has no successor, with the
  step's closure). The text's rule sentence 155 itself is not a premise: with Γ it has no model.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "ENS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 263 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-- `Reordered` keeps the length of each module. -/
theorem reordered_lengths {e k : Kore.Definition} (h : Reordered e k) :
    (e.modules.zip k.modules).all (fun mm => mm.1.sentences.length == mm.2.sentences.length) = true :=
  List.all_eq_true.mpr fun mm hm => beq_iff_eq.mpr (h.2.2 mm hm).2.2.length_eq

theorem lengths_differ :
    (defn.emit.modules.zip kore.modules).all (fun mm => mm.1.sentences.length == mm.2.sentences.length) = false := by
  decide +kernel

theorem user_lengths : (defn.emit.modules.getLast?.map (·.sentences.length), kore.modules.getLast?.map (·.sentences.length)) =
    (some 433, some 405) := by decide +kernel

/-- **`defn` does not print back to the text up to order**, so `Tied kore` fails at its last
conjunct. -/
theorem not_reordered : ¬ Reordered defn.emit kore := fun h => by
  have := reordered_lengths h
  rw [lengths_differ] at this
  exact Bool.false_ne_true this

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))
theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)

/-! ## Function equations (30 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 30 equations, in `fnItems`'s order: `half` (211), then the sort
predicates' (`isX`'s plain equation, then its `[owise]` one). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax211, U.ax229, U.ax237, U.ax236, U.ax235, U.ax234, U.ax241, U.ax240, U.ax243, U.ax242, U.ax239,
   U.ax238, U.ax216, U.ax215, U.ax228, U.ax227, U.ax224, U.ax223, U.ax226, U.ax225, U.ax231, U.ax230,
   U.ax233, U.ax232, U.ax220, U.ax219, U.ax222, U.ax221, U.ax218, U.ax217]

/-- Γ's equations are the text's sentences' translations, pattern for pattern. -/
def FnShape : Prop := (fnItems c).map (·.pat) = fnText.map (trS · |>.pat)

theorem fnShape_of_eq (h : ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat)) :
    FnShape := by
  unfold FnShape; rw [fnItems_eq, List.map_map]; exact h

/-- Each of Γ's equations is the translation of its text sentence (kernel). -/
theorem fn_shape : FnShape :=
  fnShape_of_eq (by decide +kernel)

/-- **E for the 30 equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-- **The converse for `fnItems`**: each item is a text sentence's translation, the j-th's
`fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl
  rw [fn_shape, List.getElem?_map] at h1
  cases hf : fnText[j]? with
  | none => rw [hf] at h1; cases h1
  | some ad =>
    rw [hf] at h1
    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩
    have he : (trS ad).pat = it.pat := Option.some.inj h1
    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)

/-! ## The rule (sentence 155): W1 -/

/-- A rule axiom `\rewrites{C}(\and{C}(l, t, x), r)`, read as its parts. -/
def ruleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, x]) r => some (C, l, t, x, r)
  | _ => none

/-- The rule axiom without its left side's third conjunct. -/
def dropThird (p : Kore.Pattern) : Kore.Pattern :=
  match ruleParts p with
  | some (C, l, t, _, r) => .rewrites C (.and C [l, t]) r
  | none => p

theorem ruleParts_eq {p : Kore.Pattern} {C : Kore.KSort} {l t x r : Kore.Pattern}
    (h : ruleParts p = some (C, l, t, x, r)) : ∃ C', p = .rewrites C (.and C' [l, t, x]) r ∧ dropThird p = .rewrites C (.and C [l, t]) r := by
  unfold dropThird; rw [h]
  unfold ruleParts at h
  split at h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

/-- **A conjunct more on a rule's left side gives a consequence**: in a model of definedness, the
rule axiom with the left side `l ∧ t` entails the one with the left side `l ∧ t ∧ x`, where the
two have one variable table and one list of free variables. -/
theorem rewrite_weaken {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {p : Kore.Pattern}
    {C : Kore.KSort} {l t x r : Kore.Pattern} (hq : ruleParts p = some (C, l, t, x, r))
    (ht : tableOf [] p = tableOf [] (dropThird p))
    (hf : (freeOf [] p).eraseDups = (freeOf [] (dropThird p)).eraseDups)
    (h : I ⊧ᴵ (trAxiom [] [] (kAx (dropThird p))).pat) : I ⊧ᴵ (trAxiom [] [] (kAx p)).pat := by
  obtain ⟨C', hp, hd⟩ := ruleParts_eq hq
  intro e m
  have h1 := h e m
  simp only [trAxiom, kAx, List.map_nil, List.nil_append] at h1 ⊢
  rw [ht, hf]
  rw [hd] at h1 ⊢
  rw [hp] at ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  simp only [sortOf, tr, trAndList, sRewrites, interp_sImp, interp_sAnd] at h3 ⊢
  exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 ⟨hl.1, hl.2.1⟩⟩⟩

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0))] := by kernel_rfl
theorem rule_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel

/-- Γ's rule axiom without its premise `⌈rhs ∧ ens⌉` is the text's sentence 155. -/
theorem rule_text : (trS U.ax155).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel

/-- **W1 for the rule, and the converse for `ruleItems`**: Γ's one rule item is a consequence of
the text's sentence 155, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), itemsPremises [trS U.ax155] ⊧ it.pat := by
  intro it hit M _ I hI
  rw [ruleItems_withHooks, ruleItems_eq, List.mem_singleton] at hit
  subst hit
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule_table rule_free ?_
  rw [← rule_text]
  exact hI _ (Or.inl ⟨trS U.ax155, List.mem_singleton_self _, rfl⟩)

/-! ## No junk of the sorts without constructors (115, 121, 124) -/

/-- `\or{S}(\top{S}(), \bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/
def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)

theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}
    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by
  intro e m
  unfold orTopBot
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  rw [interp_sOr, interp_sTop hD hS]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩

theorem nj115 : (trS U.ax115).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj121 : (trS U.ax121).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj124 : (trS U.ax124).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for 115, 121, 124**: entailed by Γ (by any theory with definedness), for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax115, U.ax121, U.ax124], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj115]; exact orTopBot_valid hD rfl
  · rw [nj121]; exact orTopBot_valid hD rfl
  · rw [nj124]; exact orTopBot_valid hD rfl

/-- **No junk of the sorts with generators** (116 to 120, 122, 123: Cmd and the cells): the
translation of each text sentence is the pattern of one of `Γ`'s constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax116, U.ax117, U.ax118, U.ax119, U.ax120, U.ax122, U.ax123],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

/-- KItem's (125) is the item over KItem's generators in the text's order (`gensInOrder`, the
injections by their source sort's name), the same generators as `Semantics.gens` lists (by sort
number), in another order: `Γ`'s item is the text's disjunction with its disjuncts permuted. -/
theorem nojunk_kitem_order : (trS U.ax125).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel
theorem nojunk_kitem_not_gens_order :
    (c.gens Srt.kitem).map (Gen.toK c) ≠ (gensInOrder c defn.pres Srt.kitem).map (Gen.toK c) := by decide +kernel

/-- **E for 125**: Γ entails KItem's no-junk sentence, for every H. Γ's item is the sentence over
the same generators in another order, and a no-junk item entails the one over any list that holds
its generators (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax125).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax61.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax61).pat = (trAxiom [] [] U.ax61).pat := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- No rule or clause has an open variable or a condition with a binder. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- `0` as a KItem, and the set `SetItem(0)`. -/
def a0 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))
def s1 : GroundTerm := .set Srt.set [a0]

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_none : hook setConcat [s1, s1] = some none := by decide +kernel
theorem concat_heard : silent setConcat [s1, s1] = false := by decide +kernel
theorem set_numbered : Srt.set < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.set < nRegSorts + c.sortNames.length)
theorem set_name : (cH H).sortName Srt.set = "Set" := (by decide +kernel : c.sortName Srt.set = "Set")
theorem idem_vars : (U.ax61.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax61.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax61.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 61 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax61).pat) := by
  intro M _ I hI hax
  rw [idem_trS] at hax
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI (set_numbered H)
  rw [set_name] at hσS1
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (s1_sort H) KoreAML.val0
  rw [set_name] at hesort
  let a := elemOf (cH H) I s1
  have ha : KoreAML.Inh I σS a := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hesort
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax61.ax.sortVars U.ax61.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax61.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax61.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m
    rw [idem_vars] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσS2
    · rw [List.mem_singleton.mp hk, KoreAML.interp_guard_evar hD, trSort_srt, hKv]
      exact hesort
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    rw [idem_sort]
    show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' a
    rw [KoreAML.interp_inhOf_of hRv]; exact ha)
  have hP : (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar)).interpret
      I e' a := by
    have := hP; simp only [tbl] at this ⊢; rw [idem_pattern] at this ⊢; exact this
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.set)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [show c.sortName Srt.set = "Set" from set_name H, trSort_srt]; exact hσS1 b
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hK : ∀ b, (KoreAML.tr ⟨tbl, []⟩ kVar).interpret I e' b ↔ b = a := fun b => by
    unfold kVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) ↔ b = a
    rw [hKv]
  have happ := (hall a ha).mpr ((hK a).mpr rfl)
  rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at happ
  have hden : (KoreAML.den (symApp (cH H) setConcat (GroundTerm.koreList (cH H) [s1, s1]))).interpret I KoreAML.val0 a := by
    unfold KoreAML.den
    rw [symApp_withHooks, tr_symApp]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp happ
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    refine KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, ?_, (hes b0).mpr ((hK b0).mp hb0), h0⟩,
      (hes b1).mpr ((hK b1).mp hb1), h1⟩
    exact (sym_congr (e := KoreAML.val0) (e' := e') _ f0).mpr hf0
  have hgraph := sat_dom hI (Or.inl ⟨_, [s1, s1], none, concat_sig, concat_args H, concat_none,
    fun _ => concat_heard, rfl⟩)
  exact ((KoreAML.interp_equal hD).mp (hgraph KoreAML.val0 default) a).mp hden

end Idem

/-! ## Consistency for every H -/

kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed
/-- `evalFC` reads no interpretation where no parameter is raw. -/
theorem evalFC_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (n : Nat) (f : Sym)
    (vs : List GroundTerm) : Cert.evalFC (c.withHooks H) n f vs = Cert.evalFC c n f vs :=
  Cert.evalFC_withHooks c H hr n f vs

def callOrder : List Nat := [364]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Unit 2: the converse over Γ's content -/

/-- The function sentences as written, with definedness. -/
def TextFns : Premises KoreAML.Sym := fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The premises of the derivations: the function sentences as written, Γ's rule item (the reading
of sentence 155, a consequence of it by `rule_from_text`), and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym := TextFns ∪ ΓRules (cH H) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text sentence; a rule item is a consequence of
sentence 155 (and is the reading `ruleRightDefined`); everything else is one of the five parts
defined by predicates (`Families`). -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ (ΓRules (cH H) φ ∧ (itemsPremises [trS U.ax155] ⊧ φ)) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
  · exact hI _ (Or.inl (Or.inr hr))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inl (Or.inr hx)))

/-- The cut: what Γ entails, a theory entailing each premise of Γ entails. -/
theorem cutΓ {G T : Premises KoreAML.Sym} {ψ : P} (h : ∀ φ, G φ → T ⊧ φ) (hψ : G ⊧ ψ) : T ⊧ ψ :=
  fun hT => hψ fun φ hφ => h φ hφ hT

/-- **`Pre` with the step's closure has a model, for every H**: every model of Γ
with the step's closure is one, the function sentences being entailed (`fns_entailed`). The
derivations below are therefore not vacuous; the text's own rule sentence is not in `Pre`, since
with Γ it has no model (TIE-0 F3: `run(-4)` would need a successor in the empty set). -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with ((h | h) | h) | h
  · rcases h with ⟨ad, had, rfl⟩ | ⟨x, rfl⟩
    · exact fns_entailed H ad had hΓ
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
  · exact hΓ _ (mem_Γ_rules h)
  · rcases h with (((h | h) | h) | h) | h
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact hΓ _ (Or.inr h)
  · exact hI _ (Or.inr h)

/-! ## Unit 3: the fixture's expectations, derived from `Pre` (C7 form (a)) -/

/-- **A defined result is a theorem of Γ**, for a semantics with `HypSoundCore`: where `f` has the
value `v` at `vs`, `Γ` entails `f(vs) = v` (as `eval_none_sound_core`, `eval_den4`). -/
theorem eval_some_sound_core (c : Semantics) (h : HypSoundCore c)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {v : GroundTerm} (hE : Eval c f vs (some v)) (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ den c v) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro M _ I hI e m
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop hok hfn hcl)
        (Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfn hcl hp') hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  rw [eval_den4 hI hnn hsc hok hbc hph (fun fn hfn cl hcl _ => hex fn hfn cl hcl) hE hfn hvs e a]
  rfl

def half : Sym := 387
def run : Sym := 386
def kCell : Sym := 383
def cmd : Srt := 32

theorem names : c.symName half = "Lblhalf" ∧ c.symName run = "Lblrun" ∧ c.sortName cmd = "Cmd" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel

theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hsrH (H : HookParams) : (cH H).srReady = true := (Semantics.srReady_withHooks c H).trans hsr
theorem hmrH (H : HookParams) : (cH H).matchReady = true := (Semantics.matchReady_withHooks c H).trans hmr
theorem hfnH (H : HookParams) : (cH H).lookupFn half = some fn := by
  rw [Semantics.lookupFn_withHooks]; rfl
theorem hvsH4 (H : HookParams) : (cH H).sortsOf [int 4] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
theorem hvsHm4 (H : HookParams) : (cH H).sortsOf [int (-4)] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel

theorem eval_of_evalFC {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args) {n : Nat} {r : Option GroundTerm}
    (h : Cert.evalFC c n half vs = some r) (H : HookParams) : Eval (cH H) half vs r :=
  Exec.evalF_sound (sortCtx_of (hokH H) (hsrH H) (Exec.ovlCase_of (hmrH H))) (Exec.clauseCtx_of (hokH H))
    (Exec.matchCtx_of (hmrH H)) n (Cert.evalFC_sound n (by rw [evalFC_withHooks _ _ noRaw]; exact h)) (hfnH H)
    (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)

theorem coherent (H : HookParams) : CoherentAll (cH H) :=
  Det.coherentAll_of_nil (hokH H) (hsrH H) (hmrH H) ((clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

/-- `⟦half(n)⟧`. -/
noncomputable def halfAt (H : HookParams) (n : Int) : P := KoreAML.den (symApp (cH H) half (GroundTerm.koreList (cH H) [int n]))

/-- **`half(4) = 2`, derived from `Pre`**: from the 30 function sentences as written (sentence 211
among them), the rule's reading, and the families (here the graphs of `/Int` and `>=Int`), for
every H; `Pre` has a model (`pre_model`). -/
theorem half_4 (H : HookParams) : Pre H ⊧ (halfAt H 4 ≡ den (cH H) (int 2)) :=
  cutΓ (gamma_from H) (eval_some_sound_core _ (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H))
    (eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel) H) (hfnH H) (hvsH4 H))

/-- **`half(-4)` has no value, derived from `Pre`**, for every H. -/
theorem half_neg4 (H : HookParams) : Pre H ⊧ (halfAt H (-4) ≡ ⊥) :=
  cutΓ (gamma_from H) (eval_none_sound_core _ (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H))
    (eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel) H) (hfnH H) (hvsHm4 H))

/-- The configuration with `it` in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmd Srt.kitem it, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def X : Config c := ⟨cfg (.ctor run [int (-4)]), by decide +kernel⟩
def XH (H : HookParams) : Config (cH H) := ⟨X.val, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact X.property⟩

theorem run_stuck (H : HookParams) : ∀ y, ¬ Step (cH H) (XH H) y :=
  Cert.stuckCheck_sound hok hsr hmr H (coherent H) (n := 100) (x := XH H)
    (show Cert.stuckCheck c 100 X.val = true by decide +kernel)

/-- **`run(-4)` has no successor, derived from `Pre` with the step's closure**, for every H:
`⟦run(-4)⟧ → ◦⊥`. The closure (`Γstep`) is a family with no sentence (TIE-0 L6),
and the rule enters as its reading (Γ's item), not as the text's sentence 155. -/
theorem run_neg4 (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (XH H).val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  cutΓ (fun φ h => by
      rcases h with h | h
      · exact fun hT => gamma_from H φ h (fun ψ hψ => hT ψ (Or.inl hψ))
      · exact fun hT => hT φ (Or.inr h))
    (complete_at_step _ (coreOKH H) ((Semantics.readsConfined_withHooks c H).trans readsConfined_c) (XH H)
      (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
      fun y hy => absurd hy (run_stuck H y))

/-! ## Library sample: sentence 166, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax166).pat = (trAxiom [] [] U.ax166).pat := by decide +kernel
theorem s166_pattern : U.ax166.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax166.ax.sortVars.map sortVarKey ++ freeOf [] U.ax166.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax166.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 166 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax166.ax.sortVars U.ax166.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax166).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax166.ax.sortVars U.ax166.ax.pattern = t at he ⊢
  rw [s166_pattern]
  rw [interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  have hIg := (interp_guard_evar hD).mp hg.2
  rw [interp_equal hD]
  intro a
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  have hS : ∀ b, (trSort t (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) := fun b => by
    rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) e
  obtain ⟨hes0, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int 0) = some Srt.int from rfl) e
  have hgraph := sat_dom hI (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int n, KCore.int 0], some (KCore.int (n - 0)),
    by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
  have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
  simp only [Int.sub_zero] at hg2
  -- the left side at `e` is the graph's application
  have hL : ∀ b, (tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])).interpret I e b ↔
      (KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0]))).interpret I e b := by
    intro b
    have h1 : tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ .evar (t.ev kI)) ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt")) := rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int n)) ⬝ den (cH H) (KCore.int 0) := by
      unfold symApp; rw [(sub_name H).1, (sub_name H).2]; rfl
    rw [h1, h2]
    refine interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m) (fun m => ?_) b
    · rw [interp_evar, he, hes]
    · rw [den_int0]
  simp only [sortOf]
  rw [KoreAML.tr, interp_sImp]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hR]
    refine ⟨(interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [hL b, hg2 b, hes b]
    rw [KoreAML.tr]
    show _ ↔ (sAnd (tr ⟨t, []⟩ vI) (tr ⟨t, []⟩ (.top (KoreAML.srt "Int")))).interpret I e b
    rw [interp_sAnd, KoreAML.tr]
    show _ ↔ (Pattern.evar (t.ev kI)).interpret I e b ∧ (sTop (trSort t (KoreAML.srt "Int"))).interpret I e b
    rw [interp_evar, he, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of hS]
    exact ⟨fun h => ⟨h, hb⟩, And.left⟩

/-! ## Symbols the text's sentences apply that Γ has no symbol for

The cell initializers and the counter's getter (82, 210, 212 to 214), the projections (250 to 263),
seven hooked symbols' `functional` sentences (36, 40, 42, 73, 75, 113, 114) and two library
sentences (157, 189) apply a symbol that is not among
Γ's symbols (`kernelSyms`): Γ states nothing of it, so no direction holds for these sentences.
The same holds of 99 (`ite{Sort}`'s `functional` sentence, at the sort variable `Sort`) and 244,
245 (`ite{K}`'s two equations): a symbol with sort parameters is one symbol at each instance, and
Γ applies its `ite`, the registry's `kIte` at KItem, at no sort argument (`ite_absent`).
`<<Int` and `>>Int` are symbols of Γ (interpreted hooks), so the sentences over them alone are
not of this kind (`shift_syms`, `account_absent`); nor are the equations of the two bit ranges
(208, 265), also interpreted hooks. -/

theorem absent_syms : ["LblinitKCell", "LblgetGeneratedCounterCell", "Lblproject'Coln'Int",
    "Lbl'UndsAnd-'Int'Unds'"].all (fun n => (kernelSyms c).all (fun k => c.symName k.name != n)) = true := by
  decide +kernel

theorem ite_absent : [U.ax99, U.ax244, U.ax245].all (fun ad =>
      (appHeadsOf ad.ax.pattern).any (fun h => h.1 == "Lblite" && !gammaHasHead c h)) = true ∧
    gammaHasHead c ("Lblite", []) = true := by
  decide +kernel

theorem shift_syms : ["Lbl'Unds-LT--LT-'Int'Unds'", "Lbl'Unds-GT--GT-'Int'Unds'"].all
    (fun n => (kernelSyms c).any (fun k => c.symName k.name == n)) = true := by
  decide +kernel

/-! ## The account: every sentence of the user module is in exactly one class

The classes are those of the tie's directions. The lists are checked for one thing here, that they
partition the 263 sentences; what holds of a class is its own theorem, stated over its list. -/

/-- Per class, the indices (`AxiomDecl.index`) of its sentences.
- function equation: the 30 of `fnText`, equal to Γ's items;
- rewrite rule: 155, of which Γ's item is a consequence;
- priority equation: an equation with `priority(n)` that is not `owise` (none here);
- constructor functional, subsort, injectivity, distinctness, no junk: the constructor sentences;
- function functional: the `functional` sentence of a function of the definition (the 15 sort
  predicates), which Γ does not hold;
- hooked functional: the `functional` sentence of a symbol Γ states by its graph (`freshInt`'s
  among them, 83: the registry interprets it);
- collection law: associativity and the two units of `_List_`, `_Map_`, `_Set_`;
- library: an equation or a lemma of the builtin library over symbols Γ has;
- set idempotence: 61, refuted;
- set-variable lemma: 126 to 130 and 266, refuted at sets of values;
- no direction: a sentence that applies a symbol Γ does not have. -/
def classes : List (String × List Nat) :=
  [("function equation", [211, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232,
      233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243]),
   ("rewrite rule", [155]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 78, 103, 104, 108]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 79, 109]),
   ("distinctness", [80]),
   ("no junk", [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125]),
   ("function functional", [84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
      56, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 76, 77, 81, 83, 100, 101, 102, 105, 106, 107, 110, 111, 112]),
   ("collection law", [53, 54, 55, 57, 58, 59, 60, 62, 63]),
   ("library", [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
      148, 149, 150, 151, 152, 153, 154, 156, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
      174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198,
      199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 246, 247, 248, 249, 264, 265]),
   ("set idempotence", [61]),
   ("set-variable lemma", [126, 127, 128, 129, 130, 266]),
   ("no direction", [36, 40, 42, 73, 75, 82, 99, 113, 114, 157, 189, 210, 212, 213,
      214, 244, 245, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 30), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 8),
     ("subsort", 15), ("injectivity", 6), ("distinctness", 1), ("no junk", 11), ("function functional", 15),
     ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1),
     ("set-variable lemma", 6), ("no direction", 31)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The class lists agree with the lists the class theorems are stated over: the function
equations are `fnText`'s, the rule is 155, the no-junk sentences are the three trivial ones and
the eight over generators, the refuted ones are 61 and the six set-variable lemmas. -/
theorem account_lists : (classOf "function equation").isPerm (fnText.map (·.index)) = true ∧
    classOf "rewrite rule" = [U.ax155.index] ∧
    classOf "no junk" = [U.ax115, U.ax116, U.ax117, U.ax118, U.ax119, U.ax120, U.ax121, U.ax122, U.ax123, U.ax124,
      U.ax125].map (·.index) ∧
    classOf "set idempotence" = [U.ax61.index] ∧
    classOf "set-variable lemma" = [U.ax126, U.ax127, U.ax128, U.ax129, U.ax130, U.ax266].map (·.index) := by
  decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]; decide +kernel

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` (`coreOK` keeps the name from them) and is Γ's all the same at each subsort pair,
where the constructor items state it (`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The sentences of the four classes, in text order. -/
noncomputable def consText : List AxiomDecl := U.all.filter fun ad =>
  (classOf "constructor functional" ++ classOf "subsort" ++ classOf "injectivity" ++ classOf "distinctness").contains
    ad.index

theorem consText_length : consText.length = 30 := by decide +kernel

/-- Each of the 30 is a constructor sentence Γ's constructor items entail (`tieConsB`): for a
constructor sort and generators of it, the sentence has the form of the generator's `functional`
or `subsort` sentence, or of a no-confusion sentence, and `consItemsK c` holds the items it follows
from (Cons-Fun; Cons-Fun and Cons-Inj; two Cons-Fun and Cons-Dist). -/
theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := by decide +kernel

/-- None of the 30 reads a declaration or an alias: its translation with the text's declarations
is its translation with none. -/
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each of the 30, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

/-! ## The tie's statement definitions on this text

`AtValues` and `EntailsAtValues` at sentence 166, `symbolsOf` at the rule, `surplusItem` at two sort
constants, `attrsAgree` at the whole text, with the pairing of the function sentences' priorities. -/

theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      KoreAML.srt (c.sortName S) = KoreAML.srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)
/-- **Sentence 166 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax166 (trS U.ax166).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m

/-- The symbols the rule's sentence applies. -/
theorem symbolsOf_155 : symbolsOf U.ax155.ax.pattern =
    ["Lbl'-LT-'generatedTop'-GT-'", "Lbl'-LT-'k'-GT-'", "kseq", "inj", "Lblrun", "dotk",
     "Lbl'-LT-'generatedTop'-GT-'", "Lbl'-LT-'k'-GT-'", "kseq", "inj", "Lbldone", "Lblhalf", "dotk"] := by
  decide +kernel

/-- The text declares no sort `Float`, so Γ's sort constant of Float is surplus; it declares `Int`,
whose sort constant is not. -/
theorem surplus_float : surplusItem kore (KoreAML.sortConstantItem (sortDeclOf c Srt.float)) = true ∧
    surplusItem kore (KoreAML.sortConstantItem (sortDeclOf c Srt.int)) = false := by decide +kernel

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation (`fn_shape`), item by item in `fnItems`'s order: `attrsAgree`
compares a function's priorities up to order, this pairs them. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The registry family: a String literal's value item

The text declares no sort `String` and `defn` names none; Γ holds, for each String literal, that
it denotes one element of String. That premise is a member of the registry family at the detached
name `SortString`. -/

def Dstring : KoreAML.Sym → Prop := fun σ => σ = .sort "SortString"

theorem string_undeclared : kore.sortDecls.all (·.name != "SortString") = true := by decide +kernel

/-- No symbol with a signature in `defn`'s own lists (constructors, functions, parameter symbols,
overloading symbols) has String among its sorts. -/
theorem string_unnamed : (c.ctorSigs ++ c.allFns.map Fn.sig ++ c.params.map (·.sig) ++ c.ovlSigs).all
    (fun k => !(k.result :: k.args).contains Srt.string) = true := by decide +kernel

/-- The value item of the String literal `"abc"`. -/
noncomputable def strItem (H : HookParams) : KoreAML.P :=
  KoreAML.sExists ⟨1⟩ (sortP ((cH H).sortName Srt.string)) (den (cH H) (.dv Srt.string (.tok "abc")) ≡ .evar ⟨1⟩)

theorem str_sort (H : HookParams) : (cH H).sortOf (.dv Srt.string (.tok "abc")) = some Srt.string := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- The item is a premise of Γ, for every H. -/
theorem strItem_mem (H : HookParams) : Γ (cH H) (strItem H) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, Srt.string, str_sort H, rfl⟩)))))))

/-- **The item is a `RegistryItem` at the name `SortString`**, for every H. -/
theorem strItem_registry (H : HookParams) : RegistryItem (cH H) Dstring (strItem H) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, Srt.string, ⟨by decide, (by decide +kernel : c.sortName Srt.string = "String") ▸ rfl⟩,
    str_sort H, rfl⟩))))

/-- The item names the detached symbol, so it is not a premise of the theory without the family. -/
theorem strItem_not_own (H : HookParams) : ¬ Γown (cH H) Dstring (strItem H) := fun h =>
  h.2 (.sort "SortString") (by
    have : strItem H = KoreAML.sExists ⟨1⟩ (sortP "String") (den c (.dv Srt.string (.tok "abc")) ≡ .evar ⟨1⟩) := rfl
    rw [this]; decide +kernel) rfl

/-! ## The statements for a definition, their `RightHeld` argument decided -/

/-- `sound`, `sound_withHooks` and `exact` at `defn`, the argument `RightHeld` left to its default
(`rightHeld_of_valued`, decided). -/
example (hob : Obligations defn) : Sound defn := KCore.sound defn wf_defn hob
example (H : HookParams) (hob : Obligations { defn with sem := defn.sem.withHooks H }) :
    Sound { defn with sem := defn.sem.withHooks H } := KCore.sound_withHooks defn wf_defn H hob
example (hob : Obligations defn) : Exact defn := KCore.exact defn wf_defn hob

end KCore.TieEns

open KCore.TieEns in
#print axioms wf_defn
open KCore.TieEns in
#print axioms not_reordered
#print axioms KCore.TieEns.fn_shape
#print axioms KCore.TieEns.fns_entailed
#print axioms KCore.TieEns.fns_from_text
#print axioms KCore.TieEns.rule_from_text
#print axioms KCore.TieEns.nojunk_trivial_entailed
#print axioms KCore.TieEns.nojunk_items
#print axioms KCore.TieEns.nojunk_kitem_order
#print axioms KCore.TieEns.idem_refuted
#print axioms KCore.TieEns.consistent
#print axioms KCore.TieEns.gamma_origin
#print axioms KCore.TieEns.pre_model
#print axioms KCore.TieEns.half_4
#print axioms KCore.TieEns.half_neg4
#print axioms KCore.TieEns.run_neg4
#print axioms KCore.TieEns.lib166
#print axioms KCore.TieEns.absent_syms
#print axioms KCore.TieEns.lib166_at_values
#print axioms KCore.TieEns.attrs_agree
#print axioms KCore.TieEns.fn_prios
#print axioms KCore.TieEns.absent_closed
#print axioms KCore.TieEns.strItem_registry
#print axioms KCore.TieEns.account
#print axioms KCore.TieEns.account_absent
#print axioms KCore.TieEns.nojunk_kitem_entailed
#print axioms KCore.TieEns.cons_entailed
