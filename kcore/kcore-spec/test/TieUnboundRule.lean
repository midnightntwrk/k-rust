/-
  The rule of `f2-examples/unbound.kompile.kore` (fixture e2-unbound,
  `<k> a() => b(X) ... </k> [unboundVariables(X)]`, sentence 154), whose variable X no left side
  binds, and the theory `Γc` it is read in, for every interpretation H. Run from the package root:
  `lake env lean -j1 test/TieUnboundRule.lean`.

  - The rule's item against its sentence (`rule_from_text`, W1, every H): Γ's item for the rule
    (`prioRuleK`) is the text's sentence 154 with a third conjunct `⌈rhs⌉` on its left side, the two
    with one variable table and one list of free variables (X among them, universal over the whole
    sentence in both), so the item is a consequence of the sentence (`rewrite_weaken`).
  - The origin of `Γc`'s premises (`gamma_origin`): the definition reads a confined sort
    (`readsConfined_c`), so `Γc = Γ ∪ Γcl`. A premise is a function sentence's translation (the 29
    sort-predicate equations, `fn_shape`), the rule's item (a consequence of 154), one of the five
    parts Γ defines by predicates (`Families`), definedness, or the one item of `Γcl` here,
    `boolClosed` (`gammaCl_eq`: every element of Bool is `true` or `false`), which no sentence states:
    a family of the reading of a definition that reads a confined sort.
  - `Pre H`: the function sentences as written, the rule's item, the families and `Γcl`; every
    premise of `Γc` is a consequence of it (`gamma_from`), and it has a model with the step's closure
    (`pre_model`, from `consistent`, by `FnHyp` for every H: the obligations' lists are empty).
  - The steps, for every H: `<k> a() </k>` steps to `<k> b(i) </k>` for every Int i, X := i
    (`stepBy`, `step`); in every model of `Γc` each `b(i)` is a successor (`sound_b`); every `Step`
    successor is some `b(i)` (`step_inv`); `refU` lists the outcomes (`outIs`), one family at
    `<k> a() </k>` (`refU_A`), and `complete_A` is `complete_hyp` there; `exact_b`: y is a successor
    of `<k> a() </k>` in some model of `Γc` with the step's closure exactly where y is some `b(i)`.
  - The expectations (C7 form (a)), by the cut: `b_step`, `a()` steps to `b(i)` for every i, from
    `PreS` (the sentences as written, 154 among them, the families and `Γcl`; `gamma_fromS` by W1);
    `a_succs`, every successor of `a()` is in the rule's family, from `Pre` with the step's closure.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieUnboundRule

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/unbound.kompile.kore"
definition_of defn from "f2-examples/unbound.kompile.kore"
user_axioms U from "f2-examples/unbound.kompile.kore" module "E2-UNBOUND"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The rule leaves a variable open: the definition reads a confined sort, so its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

/-! ## The function equations (29 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 29 equations, in `fnItems`'s order: the sort predicates' (`isX`'s
plain equation, then its `[owise]` one). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax227, U.ax235, U.ax234, U.ax233, U.ax232, U.ax239, U.ax238, U.ax241, U.ax240, U.ax237,
   U.ax236, U.ax214, U.ax213, U.ax226, U.ax225, U.ax222, U.ax221, U.ax224, U.ax223, U.ax229, U.ax228,
   U.ax231, U.ax230, U.ax218, U.ax217, U.ax220, U.ax219, U.ax216, U.ax215]

/-- Each of Γ's equations is the translation of its text sentence (kernel). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]; exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- **E for the 29 equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))))

/-! ## The rule (sentence 154): W1 -/

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

theorem rules_eq : c.rules = [r0] := by
  have h : c.rules.length = 1 := by decide +kernel
  match hr : c.rules, h with
  | [r], _ => simp only [r0, hr, List.getElem_cons_zero]

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0))] := by
  unfold ruleItems; rw [rules_eq]; rfl
theorem rule_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel

/-- Γ's rule axiom without its premise `⌈rhs ∧ ens⌉` is the text's sentence 154. -/
theorem rule_text : (trS U.ax154).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel

/-- **W1 for the rule, and the converse for `ruleItems`**: Γ's one rule item is a consequence of
the text's sentence 154, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), itemsPremises [trS U.ax154] ⊧ it.pat := by
  intro it hit M _ I hI
  rw [ruleItems_withHooks, ruleItems_eq, List.mem_singleton] at hit
  subst hit
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule_table rule_free ?_
  rw [← rule_text]
  exact hI _ (Or.inl ⟨trS U.ax154, List.mem_singleton_self _, rfl⟩)

/-! ## The origin of `Γc`'s premises -/

/-- Bool holds only its literals here, and the definition reads a confined sort: `Γcl` holds its
one item, `boolClosed`. -/
theorem gammaCl_eq (H : HookParams) (φ : P) : Γcl (cH H) φ ↔ φ = boolClosed (cH H) :=
  ⟨fun h => h.2.2, fun h => ⟨readsConfined_c, (by decide +kernel : c.litSort Srt.bool = true), h⟩⟩

/-- The function sentences as written, with definedness. -/
def TextFns : Premises KoreAML.Sym := fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The premises of the derivations: the function sentences as written, Γ's rule item (the reading
of sentence 154, a consequence of it by `rule_from_text`), the families, and the closure of Bool. -/
def Pre (H : HookParams) : Premises KoreAML.Sym := TextFns ∪ ΓRules (cH H) ∪ Families H ∪ Γcl (cH H)

/-- **The origin of each premise of `Γc`**: a function equation is the translation of a text
sentence; a rule item is a consequence of sentence 154; definedness; one of the five parts defined
by predicates (`Families`); or `boolClosed`, the item of `Γcl`. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γc (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ (ΓRules (cH H) φ ∧ (itemsPremises [trS U.ax154] ⊧ φ)) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∨ φ = boolClosed (cH H) := by
  intro φ h
  rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((gammaCl_eq H φ).mp h))))

/-- Every premise of `Γc` is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γc (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx | hb
  · exact hI _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩))))
  · exact hI _ (Or.inl (Or.inl (Or.inr hr)))
  · exact hI _ (Or.inl (Or.inr hf))
  · exact hI _ (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  · exact hI _ (Or.inr ((gammaCl_eq H φ).mpr hb))

/-- The cut: what `Γc` entails, a theory entailing each premise of `Γc` entails. -/
theorem cutΓ {G T : Premises KoreAML.Sym} {ψ : P} (h : ∀ φ, G φ → T ⊧ φ) (hψ : G ⊧ ψ) : T ⊧ ψ :=
  fun hT => hψ fun φ hφ => h φ hφ hT

/-! ## The rule's parts -/

def sExp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386

theorem rulesH (H : HookParams) : (cH H).rules = [r0] := rules_eq
theorem r0_vars : r0.vars = [Srt.k, 19, Srt.int] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symA []), .var 0]], .var 1] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symB [.var 2]), .var 0]], .var 1] := rfl
theorem r0_req : r0.req = none := rfl
theorem r0_ens : r0.ens = none := rfl
theorem r0_pre : r0.pre = .top := rfl
theorem r0_post : r0.post = .top := rfl
theorem r0_exs : r0.exs = [] := rfl

/-- The rule's open variable is X (variable 2), under the constructor b of the right side; the
definition has no function but the sort predicates. -/
theorem arm_A : r0.opens = [2] ∧ (ctorOccs c r0.rhs).contains 2 = true ∧ c.rulePlainOpen r0 = true ∧
    r0.needsWitness c = false ∧ c.fns = [] := by
  decide +kernel
theorem fnsH (H : HookParams) : (cH H).fns = [] := arm_A.2.2.2.2

/-! ## Consistency for every H -/

theorem term_named : c.rankObligations [] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- The obligations, for every H: none is named, the rule needs no witness (its open variable is
under a constructor of the right side) and no parameter is an open generator. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) [] [] := by
  have h1 : (cH H).rankObligations [] ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP [] [] = [] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun p hp => ?_, openDecided_of_plain ?_ ?_,
    openLaws_of_plain noRaw⟩
  · rw [h1] at hf; exact absurd hf List.not_mem_nil
  · rw [h2] at hf; exact absurd hf List.not_mem_nil
  · rw [h3] at hf; exact absurd hf List.not_mem_nil
  · rw [h4] at hp; exact absurd hp List.not_mem_nil
  · intro r hr; rw [rulesH, List.mem_singleton] at hr; subst hr; exact arm_A.2.2.2.1
  · intro fn hfn; rw [fnsH] at hfn; cases hfn

/-- **`FnHyp` for every H**: no function of the definition but the sort predicates, every
obligation list empty. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **`Γc` with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-- **`Pre` with the step's closure has a model, for every H**: every model of `Γc` with the step's
closure is one, the function sentences being entailed (`fns_entailed`). -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with (((h | h) | h) | h) | h
  · rcases h with ⟨ad, had, rfl⟩ | ⟨x, rfl⟩
    · exact fns_entailed H ad had hΓ
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
  · exact hΓ _ (Or.inl (Or.inr h))
  · rcases h with (((h | h) | h) | h) | h
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact hΓ _ (Or.inr h)
  · exact hI _ (Or.inl (Or.inr h))
  · exact hI _ (Or.inr h)

/-! ## The steps, for every H -/

section Steps
variable (H : HookParams)

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" := by
  decide +kernel

theorem shapesOK : c.shapesOK = true := by decide +kernel
theorem varOccs_lhs : varOccs r0.lhs = [0, 1] := by decide +kernel

theorem syms_ok : (cH H).isCtor topLabel = true ∧ (cH H).isCtor kCell = true ∧ (cH H).isCtor kseq = true ∧
    (cH H).isCtor symA = true ∧ (cH H).isCtor symB = true ∧ (cH H).isCtor dotk = true ∧
    (cH H).isCtor counterLabel = true :=
  (by decide +kernel : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symA = true ∧ c.isCtor symB = true ∧ c.isCtor dotk = true ∧ c.isCtor counterLabel = true)
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symA = false := by
  decide +kernel

/-- The configuration `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

theorem sortOf_ctor_congr {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr {t t0 : GroundTerm} {ts : List GroundTerm} (h : c.sortOf t = c.sortOf t0) :
    c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congr {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symB).isSome = true := by
  decide +kernel

/-- `<k> b(v) </k>` is a configuration for every v of sort Int. -/
theorem sortOf_cfgB {v : GroundTerm} (hv : c.sortOf v = some Srt.int) :
    c.sortOf (cfg (.ctor symB [v])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symB [int 0])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congr lookups_ok.1 (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.1
    (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.2.1 (sortsOf_head_congr (sortOf_inj_congr
      (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hv, sortOf_int]))) rfl))))))

theorem sortOfH (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

/-- `<k> a() </k>`. -/
def A : Config (cH H) := ⟨cfg (.ctor symA []), by rw [sortOfH]; decide +kernel⟩
/-- `<k> b(i) </k>`. -/
def B (i : Int) : Config (cH H) := ⟨cfg (.ctor symB [int i]), by rw [sortOfH]; exact sortOf_cfgB (sortOf_int i)⟩

/-- **What the left side denotes**: `<k> a() ~> w </k>` with the counter cell u, w and u the values
σ gives the variables 0 and 1. -/
theorem lhs_inv {σ : Subst} {x : GroundTerm} (h : PatVal (cH H) σ r0.lhs x) :
    ∃ w u, x = .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symA []), w]], u] ∧
      σ.lookup 0 = some w ∧ σ.lookup 1 = some u := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h (syms_ok H).1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨u, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  cases hvs2.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 (syms_ok H).2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 (syms_ok H).2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hooks_ok.2.2.2 ha (syms_ok H).2.2.2.1
  cases has.nil_inv
  exact ⟨w, u, rfl, PatVal.var_inv hz2, PatVal.var_inv h2⟩

def σA : Subst := [(0, .ctor dotk []), (1, .ctor counterLabel [.dv Srt.int (.int 0)])]
def σ (i : Int) : Subst := σA ++ [(2, int i)]

theorem hmatchA (τ : Subst) (h0 : τ.lookup 0 = some (.ctor dotk []))
    (h1 : τ.lookup 1 = some (.ctor counterLabel [.dv Srt.int (.int 0)])) : PatVal (cH H) τ r0.lhs (A H).val := by
  rw [r0_lhs]
  exact .ctor (syms_ok H).1 (.cons (.ctor (syms_ok H).2.1 (.cons (.ctor (syms_ok H).2.2.1
    (.cons (.inj (.ctor (syms_ok H).2.2.2.1 .nil)) (.cons (.var h0) .nil))) .nil)) (.cons (.var h1) .nil))

/-- **`a()` steps to `b(i)`**, X := i, for every H. -/
theorem stepBy (i : Int) : StepBy (cH H) r0 (σ i) (A H) (B H i) where
  mem := by rw [rulesH]; simp
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact sortOf_int i⟩
  hmatch := hmatchA H _ rfl rfl
  hreq := fun t ht => by rw [r0_req] at ht; cases ht
  hpre := by rw [r0_pre]; exact .top
  heval := by
    rw [r0_rhs]
    exact .ctor (syms_ok H).1 (.cons (.ctor (syms_ok H).2.1 (.cons (.ctor (syms_ok H).2.2.1
      (.cons (.inj (.ctor (syms_ok H).2.2.2.2.1 (.cons .var .nil))) (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_ens] at ht; cases ht
  hpost := by rw [r0_post]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rulesH] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

theorem step (i : Int) : Step (cH H) (A H) (B H i) := step_iff_by.mpr ⟨r0, σ i, stepBy H i⟩

/-- **In every model of `Γc`, `<k> a() </k>` has `<k> b(i) </k>` as a successor**, for every Int i
and every H. -/
theorem sound_b (i : Int) : Γc (cH H) ⊧ (den (cH H) (A H).val ⇒ KoreAML.sNext (den (cH H) (B H i).val)) := by
  have hc : ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = true → cl.CondDecided (cH H) := by
    intro fn hfn; rw [fnsH] at hfn; cases hfn
  obtain ⟨h1, -⟩ := sound_at (cH H) (coreOKH H) (A H) (B H i) r0 (σ i) (stepBy H i)
    (fun r' hr' hlt _ _ => by
      rw [rulesH] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact absurd hlt (Nat.lt_irrefl _)) hc
  have hcl : Γc (cH H) ⊧ (famEx (cH H) r0 (σ i) ≡ den (cH H) (B H i).val) :=
    famEx_closed (cH H) (coreOKH H) (stepBy H i) r0_exs hc
  intro M _ I hI e m
  have hst := h1 hI e m
  rw [interpret_impl] at hst ⊢
  intro hx
  exact sNext_congr ((KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))).mp (hcl hI e m)) (hst hx)

/-- **Every `Step` successor of `<k> a() </k>` is a `<k> b(i) </k>`**, for every H. -/
theorem step_inv {y : Config (cH H)} (hs : Step (cH H) (A H) y) : ∃ i : Int, y = B H i := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hr := hb.mem
  rw [rulesH] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  obtain ⟨w, u, hx, h0, h1⟩ := lhs_inv H hb.hmatch
  simp only [A, cfg, GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨v, h2, hv⟩ := hb.hσ 2 Srt.int (by rw [r0_vars]; rfl)
  rw [sortOfH] at hv
  obtain ⟨i, rfl⟩ := shape_int shapesOK hv
  refine ⟨i, Subtype.ext ?_⟩
  have h := hb.heval
  rw [r0_rhs] at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv (syms_ok H).1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  cases hrs2.nil_inv
  rw [hq2.var_inv, h1] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv (syms_ok H).2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  obtain ⟨ks, hks, rfl⟩ := EvalTerm.ctor_inv (syms_ok H).2.2.1 hp1
  obtain ⟨k1, ks1, rfl, hk1, hks1⟩ := hks.cons_inv
  obtain ⟨k2, ks2, rfl, hk2, hks2⟩ := hks1.cons_inv
  cases hks2.nil_inv
  rw [hk2.var_inv, h0] at he
  obtain ⟨b1, hb1, rfl⟩ := EvalTerm.inj_inv hk1
  obtain ⟨bs, hbs, rfl⟩ := EvalTerm.ctor_inv (syms_ok H).2.2.2.2.1 hb1
  obtain ⟨d1, ds1, rfl, hd1, hds1⟩ := hbs.cons_inv
  cases hds1.nil_inv
  rw [hd1.var_inv, h2] at he
  simp only [allSome, Option.bind, Option.map, injNormal, Option.some.injEq] at he
  exact he

open Classical in
/-- The outcomes at x: the family of r0 at a match no rule blocks, where there is one; none
otherwise (the rule leaves X open, and no rule binds every variable). -/
noncomputable def refU (x : GroundTerm) : List Outcome :=
  if h : ∃ τ, Unblocked (cH H) r0 τ x then [.fam r0 h.choose] else []

theorem unblockedA : Unblocked (cH H) r0 σA (A H).val :=
  ⟨fun j hj s hs => by
    rw [varOccs_lhs] at hj
    rw [r0_vars] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
    · cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩,
   hmatchA H _ rfl rfl,
   fun r' hr' hlt => by
     rw [rulesH] at hr'
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
     subst hr'
     exact absurd hlt (Nat.lt_irrefl _)⟩

/-- **`refU` lists the outcomes** (`OutIs`), for every H. -/
theorem outIs : OutIs (cH H) (refU H) := by
  intro x
  refine ⟨fun y => ?_, fun r τ hm => ?_, fun r hr _ τ hu => ?_⟩
  · constructor
    · intro hm
      unfold refU at hm
      split at hm <;> simp at hm
    · rintro ⟨hy, r, τ, hop, hb⟩
      have hr := hb.mem
      rw [rulesH] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [arm_A.1] at hop
      cases hop
  · unfold refU at hm
    split at hm
    · rename_i h
      simp only [List.mem_cons, Outcome.fam.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨by rw [rulesH]; simp, by rw [arm_A.1]; simp, h.choose_spec⟩
    · simp at hm
  · rw [rulesH] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have h : ∃ τ, Unblocked (cH H) r0 τ x.val := ⟨τ, hu⟩
    refine ⟨h.choose, fun j hj => ?_, by simp only [refU, h, ↓reduceDIte, List.mem_singleton]⟩
    obtain ⟨w, u, hx, h0, h1⟩ := lhs_inv H hu.2.1
    obtain ⟨w', u', hx', h0', h1'⟩ := lhs_inv H h.choose_spec.2.1
    rw [hx] at hx'
    simp only [GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    rw [varOccs_lhs] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [h0, h0']
    · rw [h1, h1']

/-- At `<k> a() </k>`, `refU` lists one family. -/
theorem refU_A : ∃ τ, refU H (A H).val = [.fam r0 τ] :=
  ⟨_, by simp only [refU, (⟨σA, unblockedA H⟩ : ∃ τ, Unblocked (cH H) r0 τ (A H).val), ↓reduceDIte]; rfl⟩

/-- **Completeness at `<k> a() </k>`, for every H**: with the step's closure, every successor is in
the one family. -/
theorem complete_A :
    (Γc (cH H) ∪ Γstep (cH H)) ⊧ (den (cH H) (A H).val ⇒ KoreAML.allNext (KoreAML.disjList ((refU H (A H).val).map (Outcome.pat (cH H))))) :=
  complete_hyp (cH H) (refU H) (coreOKH H) (fnHypH H) (outIs H) (A H)

/-- **By `ExactC`, for every H**: a configuration y is a successor of `<k> a() </k>` in some model
of `Γc` with the step's closure exactly where y is some `<k> b(i) </k>`. -/
theorem exact_b (y : Config (cH H)) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H))) ∧ ¬ (I ⊧ᴵ (den (cH H) (A H).val ⇒ ∼ KoreAML.sNext (den (cH H) y.val)))) ↔
    ∃ i : Int, y = B H i := by
  rw [← exact_hyp (cH H) (coreOKH H) (fnHypH H) (A H) y]
  exact ⟨step_inv H, fun ⟨i, hi⟩ => hi ▸ step H i⟩

end Steps

/-! ## The fixture's expectations (C7 form (a)) -/

/-- The function sentences as written, the rule's sentence 154 as written, the families, and the
closure of Bool. -/
def PreS (H : HookParams) : Premises KoreAML.Sym :=
  TextFns ∪ (fun φ => φ = (trS U.ax154).pat) ∪ Families H ∪ Γcl (cH H)

/-- Every premise of `Γc` is a consequence of `PreS`: the rule's item by W1 (`rule_from_text`). -/
theorem gamma_fromS (H : HookParams) : ∀ φ, Γc (cH H) φ → PreS H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨-, hent⟩ | hf | hx | hb
  · exact hI _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩))))
  · exact hent fun ψ hψ => by
      rcases hψ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
      · rw [List.mem_singleton] at hit
        subst hit
        exact hI _ (Or.inl (Or.inl (Or.inr rfl)))
      · exact hI _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))
  · exact hI _ (Or.inl (Or.inr hf))
  · exact hI _ (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  · exact hI _ (Or.inr ((gammaCl_eq H φ).mpr hb))

/-- **`a()` steps to `b(i)`, from the rule's sentence as written**, for every H and every Int i:
derived from `PreS` (sentence 154 among the sentences as written) by the cut from `sound_b`. -/
theorem b_step (H : HookParams) (i : Int) :
    PreS H ⊧ (den (cH H) (A H).val ⇒ KoreAML.sNext (den (cH H) (B H i).val)) :=
  cutΓ (gamma_fromS H) (sound_b H i)

/-- **Every successor of `a()` is in the rule's one family** (some `b(X)`), for every H: derived
from `Pre` with the step's closure; `Pre` with it has a model (`pre_model`). -/
theorem a_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (A H).val ⇒
      KoreAML.allNext (KoreAML.disjList ((refU H (A H).val).map (Outcome.pat (cH H))))) :=
  cutΓ (fun φ h => by
      rcases h with h | h
      · exact fun hT => gamma_from H φ h (fun ψ hψ => hT ψ (Or.inl hψ))
      · exact fun hT => hT φ (Or.inr h))
    (complete_A H)

end KCore.TieUnboundRule

#print axioms KCore.TieUnboundRule.fn_shape
#print axioms KCore.TieUnboundRule.rule_from_text
#print axioms KCore.TieUnboundRule.gammaCl_eq
#print axioms KCore.TieUnboundRule.gamma_origin
#print axioms KCore.TieUnboundRule.gamma_from
#print axioms KCore.TieUnboundRule.consistent
#print axioms KCore.TieUnboundRule.pre_model
#print axioms KCore.TieUnboundRule.stepBy
#print axioms KCore.TieUnboundRule.sound_b
#print axioms KCore.TieUnboundRule.step_inv
#print axioms KCore.TieUnboundRule.outIs
#print axioms KCore.TieUnboundRule.complete_A
#print axioms KCore.TieUnboundRule.exact_b
#print axioms KCore.TieUnboundRule.gamma_fromS
#print axioms KCore.TieUnboundRule.b_step
#print axioms KCore.TieUnboundRule.a_succs
