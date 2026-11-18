/-
  The tie (C14) of the reading `andAtBool` on its construct fixture e3-ml-req-and-var:
  `rule <k> go(B) => done ... </k> requires true #And B`, a `requires` that is the conjunction
  `\and{SortBool{}}(true, B)` of two Bool terms, equated with `true`, read as their strict
  conjunction: Γ's `requires` is `true ~> B ~> . ==K true ~> true ~> .`. The text is
  `f2-examples/mlreqv.kompile.kore` (as test/Guards.lean's `DevAndBool` reads it). Run from the
  package root: `lake env lean -j1 test/NoteAndBool.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations,
  the constructor sentences and the rule sentence are sentences of the user module, apart, with
  the count of the rest.

  Layer 2. Function equations (the sort predicates'): Γ's items pattern for pattern (`shape`),
  entailed for every H (`fns_entailed`). Constructor sentences: `cons_entailed`.
  The rule, sentence 113, at values (`EntailsAtValues`, `rule113_at_values`): the sentence is the
  item of the text's left side at the table of Γ's axiom (`trS113`, kernel), and at a valuation
  that sends B, the rest of the K cell and the counter cell to values (`AtValues`), the sentence
  holds in every model of Γ. Where B is `false`, `{true} ∩ {false}` is empty, so the text's
  `requires` and left side hold nothing (`TieReqBool.eqTrue_empty`). Where B is `true`, every
  element of the text's left side is one of Γ's (`ltext_sub`): Γ's `==K` denotes `true` there
  (`eqK_den`, the graph of `==K` in `ΓDomains`, at the value `true ~> true ~> .` twice), and Γ's
  `⌈r⌉` is all of the configuration sort, the right side denoting the element of the value
  `<generatedTop>(<k>(done ~> v1), v2)` at the values `v1`, `v2` of the two variables; Γ's item
  then gives the sentence (`TieRuleLhs.lhs_entails`). At an element of Bool that is no value
  nothing constrains `==K`, so the sentence is not entailed at every valuation: the class takes
  the weakening at values. `consistent` for every H.

  The expectations (C7 form (a), through the reading), from `Pre H`
  (the function equations as written, Γ's rule item, the families; it has a model, `pre_model`):
  `and_true`: `go(true)` steps to `done`; `and_false`: `go(false)` has no successor (with the
  step's closure).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteAndBool

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mlreqv.kompile.kore"
definition_of defn from "f2-examples/mlreqv.kompile.kore"
user_axioms U from "f2-examples/mlreqv.kompile.kore" module "E3-ML-REQ-AND-VAR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-ML-REQ-AND-VAR")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` (`attrsAgree`). -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [157, 165, 164, 163, 162, 169, 168, 171, 170, 167, 166, 144, 143, 156, 155, 152, 151, 154, 153, 159, 158, 161, 160, 148, 147, 150, 149, 146, 145] := by
  decide +kernel

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for every function equation**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun _ had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-! ## The constructor sentences -/

noncomputable def consText : List AxiomDecl := U.all.filter fun ad => tieConsB c ad.ax

theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.mem_filter.mp had).2) ad.index ad.module hI

/-! ## The rule (sentence 113) at values -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

theorem names : c.symName 383 = "Lbl'-LT-'k'-GT-'" ∧ c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" ∧
    c.sortName 32 = "Exp" := by decide +kernel

/-- Γ's variables: B, the rest of the K cell, the counter cell. -/
def xB : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Bool")
def xK : Kore.EVar := KoreAML.evar "VarV1" (KoreAML.srt "K")
def xC : Kore.EVar := KoreAML.evar "VarV2" (KoreAML.srt "GeneratedCounterCell")

/-- Γ's `requires` and the definedness of its right side, the conjuncts after the term. -/
noncomputable def reqG : Kore.Pattern := (TieRuleLhs.andTail q0.2.1).headD (.top KoreAML.R)
noncomputable def defG : Kore.Pattern := ((TieRuleLhs.andTail q0.2.1).drop 1).headD (.top KoreAML.R)

kernel_rfl l0_eq : q0.2.1 = .and q0.1 [TieRuleLhs.andHead q0.2.1, reqG, defG]

/-- The Bool term of Γ's `requires`. -/
noncomputable def kq : Kore.Pattern := match reqG with
  | .equals _ _ p _ => p
  | _ => .top KoreAML.R

kernel_rfl req_eq : reqG = .equals (KoreAML.srt "Bool") q0.1 kq (.dv (KoreAML.srt "Bool") "true")

/-- `<generatedTop>(<k>(done ~> q1), q2)`. -/
def rForm (q1 q2 : Kore.Pattern) : Kore.Pattern :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] [.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] [.app ⟨⟨"kseq"⟩⟩ []
    [KoreAML.injP "Exp" "KItem" (.app ⟨⟨"Lbldone"⟩⟩ [] []), q1]], q2]

kernel_rfl def_eq : defG = .ceil q0.1 q0.1 q0.2.2

-- Γ's right side, the text's: the term and `\top`.
kernel_rfl r_eq : q0.2.2 = .and q0.1 [rForm (.var (.evar xK)) (.var (.evar xC)), .top q0.1]

/-- The left side of the rule as the text writes it: the `requires` is
`\and{SortBool{}}(true, B)` equated with `true`, and no conjunct follows. -/
noncomputable def Ltext0 : Kore.Pattern :=
  .and q0.1 [TieRuleLhs.andHead q0.2.1,
    .equals (KoreAML.srt "Bool") q0.1 (.and (KoreAML.srt "Bool") [.dv (KoreAML.srt "Bool") "true", .var (.evar xB)])
      (.dv (KoreAML.srt "Bool") "true")]

noncomputable def fT0 : List VarKey := (freeOf [] (.rewrites q0.1 Ltext0 q0.2.2)).eraseDups

/-- **The rule sentence is the item of `\rewrites{C}(Ltext, r)` at the table of Γ's axiom**
(kernel). -/
theorem trS113 : (trS U.ax113).pat = TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 q0.2.2 := by
  have h : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 q0.1 Ltext0 q0.2.2) [] = some (trS U.ax113).pat := by
    decide +kernel
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- Γ's free variables are the sentence's. -/
theorem free_sub : ∀ k ∈ (freeOf [] p0).eraseDups, k ∈ fT0 := by decide +kernel

/-- The sentence's three variables are free in it and have the indices of Γ's. -/
theorem idx :
    (KoreAML.VarKey.evar "VarB" (KoreAML.srt "Bool") ∈ (freeOf [] U.ax113.ax.pattern).eraseDups ∧
      (tableOf U.ax113.ax.sortVars U.ax113.ax.pattern).ev (.evar "VarB" (KoreAML.srt "Bool")) = (tableOf [] p0).ev (evarKey xB)) ∧
    (KoreAML.VarKey.evar "Var'Unds'DotVar1" (KoreAML.srt "K") ∈ (freeOf [] U.ax113.ax.pattern).eraseDups ∧
      (tableOf U.ax113.ax.sortVars U.ax113.ax.pattern).ev (.evar "Var'Unds'DotVar1" (KoreAML.srt "K")) = (tableOf [] p0).ev (evarKey xK)) ∧
    (KoreAML.VarKey.evar "Var'Unds'DotVar0" (KoreAML.srt "GeneratedCounterCell") ∈ (freeOf [] U.ax113.ax.pattern).eraseDups ∧
      (tableOf U.ax113.ax.sortVars U.ax113.ax.pattern).ev (.evar "Var'Unds'DotVar0" (KoreAML.srt "GeneratedCounterCell")) =
        (tableOf [] p0).ev (evarKey xC)) := by decide +kernel

/-- A sort is the one of its name. -/
theorem sort_of_name {n : String} {S0 : Srt}
    (hd : ∀ S ∈ List.range (nRegSorts + c.sortNames.length), KoreAML.srt (c.sortName S) = KoreAML.srt n → S = S0)
    (hn : n ≠ "") (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt n) : S = S0 := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact hd S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    unfold KoreAML.srt at h
    injection h with h; injection h with h; injection h with h
    exact hn (by simpa using h.symm)

theorem bool_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Bool") : S = Srt.bool :=
  sort_of_name (by decide +kernel) (by decide) S h
theorem k_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "K") : S = Srt.k :=
  sort_of_name (by decide +kernel) (by decide) S h
theorem cnt_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "GeneratedCounterCell") : S = 19 :=
  sort_of_name (by decide +kernel) (by decide) S h

/-- The successor `<generatedTop>(<k>(done ~> v1), v2)`. -/
def yOf (v1 v2 : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor 383 [.ctor kseq [.inj 32 Srt.kitem (.ctor 385 []), v1]], v2]

theorem y_kore : (fun (H : HookParams) (v1 v2 : GroundTerm) => GroundTerm.kore (cH H) (yOf v1 v2)) =
    (fun H v1 v2 => rForm (v1.kore (cH H)) (v2.kore (cH H))) := by
  kernel_rfl

theorem y_sort {v1 v2 : GroundTerm} (h1 : c.sortOf v1 = some Srt.k) (h2 : c.sortOf v2 = some 19) :
    c.sortOf (yOf v1 v2) = some topCellSort := by
  have hd : c.sortOf (.inj 32 Srt.kitem (.ctor 385 [])) = some Srt.kitem := by decide +kernel
  have hq : c.sortOf (.ctor kseq [.inj 32 Srt.kitem (.ctor 385 []), v1]) = some Srt.k :=
    sortOf_ctor_of (k := ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩) (by decide +kernel) ⟨hd, h1, trivial⟩
  have hk : c.sortOf (.ctor 383 [.ctor kseq [.inj 32 Srt.kitem (.ctor 385 []), v1]]) = some 30 :=
    sortOf_ctor_of (k := ⟨383, [Srt.k], 30⟩) (by decide +kernel) ⟨hq, trivial⟩
  exact sortOf_ctor_of (k := ⟨topLabel, [30, 19], 17⟩) (by decide +kernel) ⟨hk, h2, trivial⟩

/-- `rForm` at the variables, with the variables replaced. -/
def ρK (q1 q2 : Kore.Pattern) : Kore.EVar → Option Kore.Pattern :=
  fun y => if y = xK then some q1 else if y = xC then some q2 else none

theorem rForm_subst : (fun q1 q2 => TieReqBool.substAt (ρK q1 q2) (rForm (.var (.evar xK)) (.var (.evar xC)))) = rForm := by
  kernel_rfl

/-- B replaced by `true`. -/
def ρB : Kore.EVar → Option Kore.Pattern := fun y => if y = xB then some (.dv (KoreAML.srt "Bool") "true") else none

/-- `true ~> true ~> .`. -/
def uTT : GroundTerm := .ctor kseq [.inj Srt.bool Srt.kitem (KCore.bool true), .ctor kseq [.inj Srt.bool Srt.kitem (KCore.bool true), .ctor dotk []]]

kernel_rfl kq_subst : TieReqBool.substAt ρB kq = GroundTerm.kore c (.ctor kEq [uTT, uTT])
theorem kEq_den : (fun H : HookParams => KoreAML.den (symApp (cH H) kEq (GroundTerm.koreList (cH H) [uTT, uTT]))) =
    fun _ => den c (.ctor kEq [uTT, uTT]) := by
  kernel_rfl

theorem uTT_sort (H : HookParams) : (cH H).sortOf uTT = some Srt.k := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

kernel_rfl C_eq : q0.1 = KoreAML.srt "GeneratedTopCell"
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")
theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = KoreAML.sym (.dv "false") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool false) = _; decide +kernel
theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool true) = _; decide +kernel

theorem tr_dv {t : VarTable} (n : String) :
    tr ⟨t, []⟩ (.dv (KoreAML.srt "Bool") n) = KoreAML.sym (.dv n) ⬝ KoreAML.sym (.sort "SortBool") := by
  rw [tr, trSort_srt]; rfl

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
include hI

omit [Inhabited M] in
/-- **Γ's rule item**, at its table and free variables. -/
theorem gamma_item : I ⊧ᴵ TieRuleLhs.itemAt (tableOf [] p0) (freeOf [] p0).eraseDups q0.1 q0.2.1 q0.2.2 := by
  have hm : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat := sat_rules hI (Or.inl ⟨_, hm, rfl⟩)
  have hpat : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat =
      TieRuleLhs.itemAt (tableOf [] p0) (freeOf [] p0).eraseDups q0.1 q0.2.1 q0.2.2 := by
    rw [TieRuleLhs.rwParts_eq q0_eq]; exact TieRuleLhs.trAxiom_rule _ _ _
  rw [hpat] at h
  exact h

/-- **Where B is `true`, every element of the text's left side is one of Γ's**, at values `v1`,
`v2` of the other two variables. -/
theorem ltext_sub (e : Valuation M) {v1 v2 : GroundTerm} (h1 : c.sortOf v1 = some Srt.k) (h2 : c.sortOf v2 = some 19)
    (hB : (den (cH H) (KCore.bool true)).interpret I e (e.evalEvar ((tableOf [] p0).ev (evarKey xB))))
    (hK : (den (cH H) v1).interpret I e (e.evalEvar ((tableOf [] p0).ev (evarKey xK))))
    (hC : (den (cH H) v2).interpret I e (e.evalEvar ((tableOf [] p0).ev (evarKey xC)))) (a : M)
    (h : (tr ⟨tableOf [] p0, []⟩ Ltext0).interpret I e a) : (tr ⟨tableOf [] p0, []⟩ q0.2.1).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  have hsK : (cH H).sortOf v1 = some Srt.k := by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact h1
  have hsC : (cH H).sortOf v2 = some 19 := by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact h2
  obtain ⟨σC, hσC1, hσC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσC1
  have hSC : ∀ b, (trSort (tableOf [] p0) q0.1).interpret I e b ↔ b = σC := by
    rw [C_eq, trSort_srt]; exact hσC1
  obtain ⟨σB, aF, aT, hSB, hσB, haf, hat, hne, hif, hit⟩ :=
    TieReqBool.boolTwo hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H) (tableOf [] p0) e
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have hterm := h _ (List.mem_cons_self ..)
  have heqT := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hTe : ∀ (p q : Kore.Pattern), tr ⟨tableOf [] p0, []⟩ (.equals (KoreAML.srt "Bool") q0.1 p q) =
      sEquals (trSort (tableOf [] p0) (KoreAML.srt "Bool")) (trSort (tableOf [] p0) q0.1)
        (tr ⟨tableOf [] p0, []⟩ p) (tr ⟨tableOf [] p0, []⟩ q) := fun p q => by rw [tr]
  rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2] at heqT
  have haC : Inh I σC a := heqT.1
  rw [l0_eq, interp_and (List.cons_ne_nil _ _)]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hterm
  rcases List.mem_cons.mp hp with rfl | hp
  · -- Γ's `requires`: its `==K` denotes `true`
    rw [req_eq, hTe, interp_sEquals hD hc hSB hSC hσB hσC2]
    refine ⟨haC, fun x _ => ?_⟩
    have hρ : ∀ y q, ρB y = some q → ∀ m, (tr ⟨tableOf [] p0, []⟩ q).interpret I e m ↔
        m = e.evalEvar ((tableOf [] p0).ev (evarKey y)) := by
      intro y q hy m
      unfold ρB at hy
      split at hy
      · next hyB =>
        cases hy; subst hyB
        rw [tr_dv, ← den_true H]
        obtain ⟨a0, ha0, -⟩ := den_single hI (sortOf_true H) e
        rw [ha0 m, (ha0 _).mp hB]
      · cases hy
    rw [← TieReqBool.substAt_iff hρ kq x, kq_subst, tr_ground_den, tr_dv, ← den_true H]
    have hk := eqK_den (c := cH H) hI (uTT_sort H) (uTT_sort H) e x
    have hcmp : (GroundTerm.cmp uTT uTT == .eq) = true := by decide +kernel
    rw [hcmp, congrFun kEq_den H] at hk
    exact hk
  rw [List.mem_singleton.mp hp]
  · -- Γ's `⌈r⌉`: the right side denotes the element of a value of the configuration sort
    have hyH : (cH H).sortOf (yOf v1 v2) = some topCellSort := by
      rw [Semantics.sortOf_withHooks _ _ noRaw]; exact y_sort h1 h2
    obtain ⟨a1, ha1, hin⟩ := den_single hI hyH e
    rw [top_name] at hin
    have hρ : ∀ y q, ρK (v1.kore (cH H)) (v2.kore (cH H)) y = some q → ∀ m, (tr ⟨tableOf [] p0, []⟩ q).interpret I e m ↔
        m = e.evalEvar ((tableOf [] p0).ev (evarKey y)) := by
      intro y q hy m
      unfold ρK at hy
      split at hy
      · next hyK =>
        cases hy; subst hyK
        rw [tr_ground_den]
        obtain ⟨a0, ha0, -⟩ := den_single hI hsK e
        rw [ha0 m, (ha0 _).mp hK]
      · split at hy
        · next hyC =>
          cases hy; subst hyC
          rw [tr_ground_den]
          obtain ⟨a0, ha0, -⟩ := den_single hI hsC e
          rw [ha0 m, (ha0 _).mp hC]
        · cases hy
    have hr0 : ∀ b, (tr ⟨tableOf [] p0, []⟩ (rForm (.var (.evar xK)) (.var (.evar xC)))).interpret I e b ↔ b = a1 := by
      intro b
      rw [← TieReqBool.substAt_iff hρ, congrFun (congrFun rForm_subst (v1.kore (cH H))) (v2.kore (cH H)),
        ← congrFun (congrFun (congrFun y_kore H) v1) v2, tr_ground_den]
      exact ha1 b
    have hsC : (trSort (tableOf [] p0) q0.1).isFreeEvar topVar = false := by rw [C_eq, trSort_srt]; rfl
    have hr : ∀ b, (tr ⟨tableOf [] p0, []⟩ q0.2.2).interpret I e b ↔ b = a1 := by
      intro b
      rw [r_eq, tr_and2, interp_sAnd, hr0]
      have hT : tr ⟨tableOf [] p0, []⟩ (.top q0.1) = sTop (trSort (tableOf [] p0) q0.1) := by rw [tr]
      rw [hT, interp_sTop hD hsC]
      constructor
      · exact fun h => h.1
      · intro h; subst h
        exact ⟨rfl, by rw [C_eq, trSort_srt]; exact hin⟩
    have hTc : tr ⟨tableOf [] p0, []⟩ (.ceil q0.1 q0.1 q0.2.2) =
        sCeil (trSort (tableOf [] p0) q0.1) (trSort (tableOf [] p0) q0.1) (tr ⟨tableOf [] p0, []⟩ q0.2.2) := by rw [tr]
    rw [def_eq, hTc, interp_sCeil hD hc hSC hSC hσC2 hσC2 (fun b hb => by
      rw [(hr b).mp hb]; exact (interp_inhOf_of (S := sortP "GeneratedTopCell") hσC1).mp hin) a]
    exact ⟨⟨a1, (hr a1).mpr rfl⟩, haC⟩

end

/-- **The rule sentence 113 is entailed at values** (`EntailsAtValues`, the reading's direction),
for every H. Where B is `false` the text's left side holds nothing; where it is `true` it is in
Γ's (`ltext_sub`), and Γ's item gives the sentence. -/
theorem rule113_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax113 (trS U.ax113).pat := by
  intro M _ I hI e hat m
  have hD := defOK hI
  rw [trS113]
  obtain ⟨⟨iB, eB⟩, ⟨iK, eK⟩, ⟨iC, eC⟩⟩ := idx
  obtain ⟨v0, S0, hS0, hv0, hd0⟩ := hat _ _ iB
  obtain ⟨v1, S1, hS1, hv1, hd1⟩ := hat _ _ iK
  obtain ⟨v2, S2, hS2, hv2, hd2⟩ := hat _ _ iC
  rw [eB] at hd0; rw [eK] at hd1; rw [eC] at hd2
  have := bool_of_name S0 hS0; subst this
  have := k_of_name S1 hS1; subst this
  have := cnt_of_name S2 hS2; subst this
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hv0 hv1 hv2
  obtain ⟨b, rfl⟩ := shape_bool (by decide +kernel : c.shapesOK = true) hv0
  cases b with
  | false =>
    refine TieReqBool.ruleItem_of_empty hD (fun a ha => ?_) m
    haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
    have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
    have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
    obtain ⟨σC, hσC1, hσC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
    rw [top_name] at hσC1
    obtain ⟨σB, aF, aT, -, -, haf, hat', hne, -, -⟩ :=
      TieReqBool.boolTwo hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H) (tableOf [] p0) e
    have hxB : e.evalEvar ((tableOf [] p0).ev (evarKey xB)) = aF :=
      (haf _).mp (by rw [tr_dv, ← den_false H]; exact hd0)
    unfold Ltext0 at ha
    rw [interp_and (List.cons_ne_nil _ _)] at ha
    refine TieReqBool.eqTrue_empty hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
      (by rw [C_eq, trSort_srt]; exact hσC1) hσC2 (fun _ _ _ x y _ _ => ?_) a
      (ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hF : ∀ z, ¬ (tr ⟨tableOf [] p0, []⟩ (.and (KoreAML.srt "Bool")
        [.dv (KoreAML.srt "Bool") "true", .var (.evar xB)])).interpret I e z := by
      intro z hz
      rw [tr_and2, interp_sAnd] at hz
      have h1 := (hat' z).mp hz.1
      have h2 : z = e.evalEvar ((tableOf [] p0).ev (evarKey xB)) := hz.2
      exact hne (hxB ▸ h2 ▸ h1 ▸ rfl)
    exact ⟨fun hx => absurd hx (hF x), fun hy => absurd hy (hF y)⟩
  | true =>
    exact TieRuleLhs.lhs_entails hD free_sub (gamma_item H hI) e m
      (fun _ a ha => ltext_sub H hI e hv1 hv2 hd0 hd1 hd2 a ha)

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index) ++ [113]

/-- **The account**: the function equations, the constructor sentences and the rule sentence are
sentences of the user module, each once and none in two classes, with the sizes of the three
classes and of the rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, [113].length, U.all.length - tiedIdx.length) = (29, 29, 1, 127) := by decide +kernel

/-! ## The facts the deciders leave -/

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectations (C7 form (a)) -/

/-- **The premises of the derivations**: every function equation as written, Γ's rule items (the
reading of the rule sentence 113, which entails the sentence at values by `rule113_at_values`), and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem hrcH (H : HookParams) : (cH H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c

/-- The configuration with `it` of sort Exp in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor 383 [.ctor kseq [.inj 32 Srt.kitem it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- A step the rules' check accepts on the data, as a consequence of `Pre H`: `⟦x⟧ → •⟦y⟧`. -/
theorem step_from {x y : Config c} (h : c.rules.any (fun r => Cert.checkStep c 50 r x.val y.val) = true) (H : HookParams) :
    Pre H ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (den (cH H) y.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (TieRuleLhs.step_everyH hok hsr hmr noRaw h H))

theorem clausesFixed_c : c.clausesFixed = true := by decide +kernel
theorem agreeObligations_c : c.agreeObligations = [] := by decide +kernel
theorem asideFree_c : c.asideFree = true := by decide +kernel

/-- A configuration `stuckCheck` accepts on the data has no successor, as a consequence of `Pre H`
with the step's closure: `⟦x⟧ → ◦⊥`. -/
theorem stuck_from {x : Config c} (h : Cert.stuckCheck c 50 x.val = true) (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) x.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H) (complete_at_step _ (coreOKH H) (hrcH H) (TieRuleLhs.cfgH noRaw x H)
    (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
    fun y hy => absurd hy (TieRuleLhs.stuck_everyH hok hsr hmr noRaw clausesFixed_c agreeObligations_c asideFree_c h H y))

def GoT : Config c := ⟨cfg (.ctor 386 [.dv Srt.bool (.bool true)]), by decide +kernel⟩
def GoF : Config c := ⟨cfg (.ctor 386 [.dv Srt.bool (.bool false)]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor 385 []), by decide +kernel⟩

/-- **`go(true)` steps to `done`, derived from `Pre`**, for every H. -/
theorem and_true (H : HookParams) : Pre H ⊧ (den (cH H) GoT.val ⇒ KoreAML.sNext (den (cH H) Done.val)) :=
  step_from (x := GoT) (y := Done) (by decide +kernel) H

/-- **`go(false)` has no successor, derived from `Pre` with the step's closure**, for every H. -/
theorem and_false (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) GoF.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  stuck_from (x := GoF) (by decide +kernel) H

end KCore.NoteAndBool

#print axioms KCore.NoteAndBool.wf_defn
#print axioms KCore.NoteAndBool.defs_attrsAgree
#print axioms KCore.NoteAndBool.account
#print axioms KCore.NoteAndBool.shape
#print axioms KCore.NoteAndBool.fns_entailed
#print axioms KCore.NoteAndBool.cons_entailed
#print axioms KCore.NoteAndBool.trS113
#print axioms KCore.NoteAndBool.ltext_sub
#print axioms KCore.NoteAndBool.rule113_at_values
#print axioms KCore.NoteAndBool.consistent
#print axioms KCore.NoteAndBool.pre_model
#print axioms KCore.NoteAndBool.and_true
#print axioms KCore.NoteAndBool.and_false
