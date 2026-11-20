/-
  KCore, checked layer: a rewrite axiom the reader leaves inert because its left side is empty in
  every model of Γ (`Parse.InertReason.vacuousLeftAtBool`), entailed by `Γ c` for every semantics
  with `OvlOK`.

  - `den_boolLit`: the denotation of each Bool literal is the domain value of its text at
    `SortBool{}`, for every semantics (the two `den` hypotheses of `TieReqBool.boolTwo`).
  - `floorVar_none`: `\floor{SortBool{}, S}(x)` of an element variable holds of no element where
    Bool has two elements and S is a sort: x denotes one element, so some element of Bool is
    outside it, and the `\ceil` of x's complement in Bool is all of S.
  - `vacuousAtBool_none`: a pattern `Parse.vacuousAtBool` accepts holds of no element there; an
    application or a conjunction one of whose operands is empty is empty.
  - `vacuousLeftAtBool_entailed`: a rewrite axiom whose left side `Parse.vacuousAtBool` accepts
    holds in every model of `Γ c`. It reads `ΓSig` (definedness, `⌈_⌉`'s definition, Bool one sort)
    and `ΓDomains` (the two literals, each one element of Bool, and apart), through
    `TieReqBool.boolTwo`; it does not hold in every model of matching logic, where Bool may have one
    element.
-/
import KcoreSpec.InertEv
import KcoreSpec.TieReqBool

set_option autoImplicit false

namespace KCore

namespace InertEv

open ML Faithful KoreAML

/-- **The denotation of a Bool literal**, for every semantics: `\dv{SortBool{}}` of its text. -/
theorem den_boolLit (c : Semantics) (b : Bool) :
    den c (KCore.bool b) = sym (.dv (if b then "true" else "false")) ⬝ sym (.sort "SortBool") := by
  cases b <;> (unfold den KCore.bool; rw [GroundTerm.kore, sortName_bool]; rfl)

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **`\floor{SortBool{}, S}(x)` of an element variable is empty** where Bool is a sort with two
elements and S is a sort: the complement of x in Bool holds one of the two, so the `\ceil` of that
complement is all of S, and the `\floor` is its complement in S. -/
theorem floorVar_none [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable}
    {e : Valuation M} {S : Kore.KSort} {σS σB aF aT : M} (hS : ∀ a, (trSort t S).interpret I e a ↔ a = σS)
    (hσS : IsSort I σS) (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) (hσB : IsSort I σB)
    (hne : aF ≠ aT) (hF : Inh I σB aF) (hT : Inh I σB aT) (x : Kore.EVar) (m : M) :
    ¬ (tr ⟨t, []⟩ (.floor (srt "Bool") S (.var (.evar x)))).interpret I e m := by
  have hTr : tr ⟨t, []⟩ (.floor (srt "Bool") S (.var (.evar x))) =
      sFloor (trSort t (srt "Bool")) (trSort t S) (.evar (t.ev (evarKey x))) := by rw [tr]; rfl
  have hin : ∀ a, (sNot (trSort t (srt "Bool")) (.evar (t.ev (evarKey x)) : P)).interpret I e a → Inh I σB a :=
    fun a ha => (interp_inhOf_of hSB).mp (interp_sNot.mp ha).2
  rw [hTr]
  unfold sFloor
  rw [interp_sNot, interp_sCeil hD hc hSB hS hσB hσS hin, interp_inhOf_of hS]
  rintro ⟨hn, hm⟩
  apply hn
  refine ⟨?_, hm⟩
  by_cases h : aF = e.evalEvar (t.ev (evarKey x))
  · refine ⟨aT, interp_sNot.mpr ⟨fun h' => hne ?_, (interp_inhOf_of hSB).mpr hT⟩⟩
    rw [interp_evar] at h'
    rw [h, h']
  · exact ⟨aF, interp_sNot.mpr ⟨fun h' => h (interp_evar.mp h'), (interp_inhOf_of hSB).mpr hF⟩⟩

mutual
  /-- **A pattern `Parse.vacuousAtBool` accepts is empty** where Bool is a sort with two elements. -/
  theorem vacuousAtBool_none [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable}
      {e : Valuation M} {σB aF aT : M} (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB)
      (hσB : IsSort I σB) (hne : aF ≠ aT) (hF : Inh I σB aF) (hT : Inh I σB aT) : ∀ (p : Kore.Pattern),
      Parse.vacuousAtBool p = true → ∀ (m : M), ¬ (tr ⟨t, []⟩ p).interpret I e m
    | .floor s s' p, hv, m => by
      cases p with
      | var v =>
        cases v with
        | evar x =>
          rw [Parse.vacuousAtBool, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hv
          obtain ⟨rfl, rfl⟩ := hv
          exact floorVar_none hD hc hSB hσB hSB hσB hne hF hT x m
        | svar _ => simp [Parse.vacuousAtBool] at hv
      | _ => simp [Parse.vacuousAtBool] at hv
    | .app h ss ps, hv, m => by
      rw [Parse.vacuousAtBool] at hv
      rw [tr]
      simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
      exact anyVacuousAtBool_none hD hc hSB hσB hne hF hT ps hv _ m
    | .and s ps, hv, m => by
      rw [Parse.vacuousAtBool] at hv
      rw [tr]
      exact anyVacuousAtBool_and_none hD hc hSB hσB hne hF hT ps hv _ m
    | .var _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .bottom _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .string _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .top _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .not _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .or _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .exist _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .implies _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .iff _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .forall _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .mu _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .nu _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .ceil _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .equals _ _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .in _ _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .next _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .rewrites _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .dv _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .leftAssoc _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
    | .rightAssoc _ _ _, hv, _ => by simp [Parse.vacuousAtBool] at hv
  termination_by structural p => p
  /-- An application one of whose arguments is empty there is empty. -/
  theorem anyVacuousAtBool_none [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable}
      {e : Valuation M} {σB aF aT : M} (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB)
      (hσB : IsSort I σB) (hne : aF ≠ aT) (hF : Inh I σB aF) (hT : Inh I σB aT) : ∀ (ps : List Kore.Pattern),
      Parse.anyVacuousAtBool ps = true → ∀ (acc : P) (m : M), ¬ (trArgs ⟨t, []⟩ acc ps).interpret I e m
    | [], hv, _, _ => by simp [Parse.anyVacuousAtBool] at hv
    | p :: ps, hv, acc, m => by
      rw [Parse.anyVacuousAtBool, Bool.or_eq_true] at hv
      rw [trArgs_cons]
      rcases hv with hv | hv
      · exact trArgs_empty (fun m' hm' => by
          obtain ⟨_, b, _, hb, _⟩ := interp_app.mp hm'
          exact vacuousAtBool_none hD hc hSB hσB hne hF hT p hv b hb) ps m
      · exact anyVacuousAtBool_none hD hc hSB hσB hne hF hT ps hv _ m
  termination_by structural ps => ps
  /-- A conjunction one of whose operands is empty there is empty. -/
  theorem anyVacuousAtBool_and_none [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable}
      {e : Valuation M} {σB aF aT : M} (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB)
      (hσB : IsSort I σB) (hne : aF ≠ aT) (hF : Inh I σB aF) (hT : Inh I σB aT) : ∀ (ps : List Kore.Pattern),
      Parse.anyVacuousAtBool ps = true → ∀ (s : P) (m : M), ¬ (trAndList ⟨t, []⟩ s ps).interpret I e m
    | [], hv, _, _ => by simp [Parse.anyVacuousAtBool] at hv
    | p :: ps, hv, s, m => by
      rw [Parse.anyVacuousAtBool, Bool.or_eq_true] at hv
      intro h
      obtain ⟨h1, h2⟩ := trAndList_cons_of h
      rcases hv with hv | hv
      · exact vacuousAtBool_none hD hc hSB hσB hne hF hT p hv m h1
      · rcases h2 with rfl | h2
        · simp [Parse.anyVacuousAtBool] at hv
        · exact anyVacuousAtBool_and_none hD hc hSB hσB hne hF hT ps hv s m h2
  termination_by structural ps => ps
end

end

/-- **A rewrite axiom whose left side is empty in every model of Γ is entailed**
(`InertReason.vacuousLeftAtBool`): where the left side of `\rewrites{s}(\and{s'}(l, q), r)` is one
`Parse.vacuousAtBool` accepts (the condition of `classifyAxiom`), the translation of the axiom, with
any declarations and no alias, holds in every model of `Γ c`. It reads definedness, `⌈_⌉`'s
definition and Bool's sort item from `ΓSig`, and the items of the literals `false` and `true` and
their distinctness from `ΓDomains` (`TieReqBool.boolTwo`, its hypotheses discharged for every
semantics by `sortOf_bool` and `den_boolLit`). No hook, rule or function is read. -/
theorem vacuousLeftAtBool_entailed (c : Semantics) [OvlOK c] {a : Kore.Axiom}
    (hv : (match a.pattern with
      | .rewrites _ (.and _ [l, _]) _ => Parse.vacuousAtBool l
      | _ => false) = true)
    (decls : List KoreAML.SymbolDecl) (i : Nat) (mod : String) :
    Γ c ⊧ (KoreAML.trAxiom decls [] ⟨i, mod, a⟩).pat := by
  intro M _ I hI e m
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig c := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains c := fun φ hφ => sat_dom hI hφ
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := c), rfl⟩))
  split at hv
  · rename_i s s' l q r hp
    unfold KoreAML.trAxiom
    dsimp only
    rw [interpret_impl]
    intro _
    rw [hp]
    simp only [KoreAML.sortOf]
    rw [KoreAML.interp_equal hD]
    intro b
    rw [KoreAML.tr]
    unfold KoreAML.sRewrites
    rw [KoreAML.interp_sImp]
    refine ⟨fun h => h.1, fun hb => ⟨hb, fun hl => ?_⟩⟩
    rw [KoreAML.tr] at hl
    obtain ⟨σB, aF, aT, hSB, hσB, -, -, hne, hF, hT⟩ := TieReqBool.boolTwo hD hSig hDom
      (sortOf_bool false) (sortOf_bool true) (den_boolLit c false) (den_boolLit c true) _ e
    exact (vacuousAtBool_none hD hc hSB hσB hne hF hT l hv b (trAndList_cons_of hl).1).elim
  · cases hv

end InertEv

end KCore
