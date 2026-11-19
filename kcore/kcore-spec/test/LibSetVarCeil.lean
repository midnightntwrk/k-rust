/-
  A library lemma over set variables that Γ refutes at values: sentence 126 of
  `f2-examples/ens.kompile.kore`, the `#Ceil` lemma of `%Int` (domains.md 1393),

      #Ceil(@I1 %Int @I2) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)

  For every interpretation H of the hooks and in every model of Γ, the sentence fails at the
  valuation `@I1 = @I2 = {0, 1}` (the elements of the Int values 0 and 1), every sort variable at
  Int (`ceil126_at`): the left side holds, since `0 %Int 1 = 0`, and `@I2 =/=Int 0` holds the element
  of `false` (`0 =/=Int 0 = false`), which `true` does not hold. The valuation meets `AtValues` (the
  sentence has no free element variable) and `SetVarsAtValues`. So Γ with the sentence has no model
  (`ceil126_refuted`), and where Γ has a model the sentence is neither `EntailsAtValues`
  (`ceil126_not_at_values`) nor `EntailsAtSetValues` (`ceil126_not_at_set_values`).

  The proof reads three facts of Γ: `0 %Int 1` has a value, `0 =/=Int 0` is `false`, and `false` and
  `true` share no element. It reads no point where `%Int` is undefined and no silent point.

  Axioms guarded. Run from kcore-spec: `lake env lean -j1 test/LibSetVarCeil.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibSetVarCeil

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The valuation: every element variable at `σ`, every set variable at the set `{a, b}`. -/
def eV {M : Type} (σ a b : M) : Valuation M := ⟨fun _ => σ, fun _ m => m = a ∨ m = b⟩

def Q0 : Kore.KSort := .var ⟨⟨⟨"Q0"⟩⟩⟩
def X1 : Kore.Pattern := .var (.svar ⟨⟨⟨"VarI1"⟩⟩, KoreAML.srt "Int"⟩)
def X2 : Kore.Pattern := .var (.svar ⟨⟨⟨"VarI2"⟩⟩, KoreAML.srt "Int"⟩)
def k1 : VarKey := .svar "VarI1" (KoreAML.srt "Int")
def k2 : VarKey := .svar "VarI2" (KoreAML.srt "Int")
def modN : String := "Lbl'UndsPerc'Int'Unds'"
def neN : String := "Lbl'UndsEqlsSlshEqls'Int'Unds'"

/-- The text of sentence 126. -/
def PAT : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0 KoreAML.R (.ceil (KoreAML.srt "Int") Q0 (.app ⟨⟨modN⟩⟩ [] [X1, X2]))
      (.and Q0 [.and Q0 [.and Q0 [.equals (KoreAML.srt "Bool") Q0
            (.app ⟨⟨neN⟩⟩ [] [X2, .dv (KoreAML.srt "Int") "0"]) (.dv (KoreAML.srt "Bool") "true"),
          .ceil (KoreAML.srt "Int") Q0 X1], .ceil (KoreAML.srt "Int") Q0 X2], .top Q0]))

theorem s126_pattern : U.ax126.ax.pattern = PAT := by decide +kernel
theorem s126_trS : (trS U.ax126).pat = (trAxiom [] [] U.ax126).pat := by decide +kernel
theorem s126_sort : KoreAML.sortOf [] U.ax126.ax.pattern = some KoreAML.R := by decide +kernel
/-- The sentence's variables: sort variables and set variables of sort Int, no element variable. -/
theorem s126_free : ((U.ax126.ax.sortVars.map sortVarKey ++ freeOf [] U.ax126.ax.pattern).eraseDups.all fun k =>
    match k with
    | .sortVar _ => true
    | .evar _ _ => false
    | .svar _ s => decide (s = KoreAML.srt "Int")) = true := by decide +kernel
theorem s126_noEvar : ((freeOf [] U.ax126.ax.pattern).eraseDups.all fun k =>
    match k with
    | .evar _ _ => false
    | _ => true) = true := by decide +kernel

def Lp (t : VarTable) : KoreAML.P := (KoreAML.sym (.symbol modN) ⬝ .svar (t.sv k1)) ⬝ .svar (t.sv k2)
def NEp (t : VarTable) : KoreAML.P :=
  (KoreAML.sym (.symbol neN) ⬝ .svar (t.sv k2)) ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt"))
def TRUEp : KoreAML.P := KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool")
def TR (t : VarTable) : KoreAML.P := .evar (t.ev (.sortVar "R"))
def TQ (t : VarTable) : KoreAML.P := .evar (t.ev (.sortVar "Q0"))
def TI : KoreAML.P := KoreAML.sym (.sort "SortInt")
def TB : KoreAML.P := KoreAML.sym (.sort "SortBool")

theorem tr_PAT (t : VarTable) : tr ⟨t, []⟩ PAT =
    sImp (TR t) (sTop (TR t)) (sEquals (TQ t) (TR t) (sCeil TI (TQ t) (Lp t))
      (sAnd (sAnd (sAnd (sEquals TB (TQ t) (NEp t) TRUEp) (sCeil TI (TQ t) (.svar (t.sv k1))))
        (sCeil TI (TQ t) (.svar (t.sv k2)))) (sTop (TQ t)))) := rfl

/-- The semantic core, for any table: at a valuation that sends every sort variable to the sort
`σ` of Int and every set variable to `{a0, a1}`, where the left side's application holds an element
`r` of Int and `_=/=Int_(@I2, 0)` holds an element `f` of Bool that `true` does not, the sentence's
pattern does not hold at `a0`. -/
theorem core {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (t : VarTable) {σ σB a0 a1 r f : M}
    (hσ : IsSort I σ) (hσB : IsSort I σB)
    (hSI : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σ)
    (hSB : ∀ a, I.evalSymb (.sort "SortBool") a ↔ a = σB)
    (ha0 : Inh I σ a0) (hr : Inh I σ r) (hL : (Lp t).interpret I (eV σ a0 a1) r)
    (hf : Inh I σB f) (hNE : (NEp t).interpret I (eV σ a0 a1) f)
    (hT : ¬ TRUEp.interpret I (eV σ a0 a1) f) :
    ¬ (tr ⟨t, []⟩ PAT).interpret I (eV σ a0 a1) a0 := by
  intro hP
  rw [tr_PAT] at hP
  have hRv : ∀ b, (TR t).interpret I (eV σ a0 a1) b ↔ b = σ := fun b => Iff.rfl
  have hQv : ∀ b, (TQ t).interpret I (eV σ a0 a1) b ↔ b = σ := fun b => Iff.rfl
  have hIv : ∀ b, TI.interpret I (eV σ a0 a1) b ↔ b = σ := fun b => hSI b
  have hBv : ∀ b, TB.interpret I (eV σ a0 a1) b ↔ b = σB := fun b => hSB b
  have himp := (interp_sImp.mp hP).2
  have htop : (sTop (TR t)).interpret I (eV σ a0 a1) a0 :=
    (interp_sTop hD (isFree_R (tbl := t)) a0).mpr ((interp_inhOf_of hRv).mpr ha0)
  have hE := (interp_sEquals hD hc hQv hRv hσ hσ a0).mp (himp htop)
  have hceil : (sCeil TI (TQ t) (Lp t)).interpret I (eV σ a0 a1) a0 :=
    interp_sCeil_raw.mpr ⟨σ, σ, r, (hIv σ).mpr rfl, (hQv σ).mpr rfl, hL, (ceilE_of hD hc hσ hσ hr a0).mpr ha0⟩
  have hx := (hE.2 a0 ha0).mp hceil
  have hEQ := (interp_sAnd.mp (interp_sAnd.mp (interp_sAnd.mp hx).1).1).1
  have hEQ2 := (interp_sEquals hD hc hBv hQv hσB hσ a0).mp hEQ
  exact hT ((hEQ2.2 f hf).mp hNE)

theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem bool_numbered (H : HookParams) : Srt.bool < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.bool < nRegSorts + c.sortNames.length)
theorem bool_name (H : HookParams) : (cH H).sortName Srt.bool = "Bool" := (by decide +kernel : c.sortName Srt.bool = "Bool")
theorem mod_name (H : HookParams) : (cH H).symName intTMod = modN ∧ instDecode? modN = none :=
  (by decide +kernel : c.symName intTMod = modN ∧ instDecode? modN = none)
theorem ne_name (H : HookParams) : (cH H).symName intNe = neN ∧ instDecode? neN = none :=
  (by decide +kernel : c.symName intNe = neN ∧ instDecode? neN = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = TRUEp := by
  show den c (KCore.bool true) = _; decide +kernel

/-- The two points of the hooks' graphs the refutation reads. -/
theorem mod_0_1 : hook intTMod [KCore.int 0, KCore.int 1] = some (some (KCore.int 0)) := by decide +kernel
theorem ne_0_0 : hook intNe [KCore.int 0, KCore.int 0] = some (some (KCore.bool false)) := by decide +kernel

theorem s126_svars : ((freeOf [] U.ax126.ax.pattern).eraseDups.all fun k =>
    match k with
    | .svar _ s => decide (s = KoreAML.srt "Int")
    | _ => true) = true := by decide +kernel

/-- **In every model of Γ, for every H, sentence 126 fails at a valuation at values**: with
`@I1 = @I2 = {0, 1}` (the elements of the values 0 and 1) the left side `⌈@I1 %Int @I2⌉` holds
(`0 %Int 1 = 0`), and `@I2 =/=Int 0` holds `false` (`0 =/=Int 0 = false`), which `true` does not,
so the right side does not hold. -/
theorem ceil126_at (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax126.ax ∧ SetVarsAtValues (cH H) I e U.ax126.ax ∧
      ¬ (trS U.ax126).pat.interpret I e default := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσ1
  obtain ⟨σB, hB1, hB2⟩ := sortSing hI (bool_numbered H)
  rw [bool_name] at hB1
  let a0 := elemOf (cH H) I (KCore.int 0)
  let a1 := elemOf (cH H) I (KCore.int 1)
  let f := elemOf (cH H) I (KCore.bool false)
  obtain ⟨h0, h0s⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int 0) = some Srt.int from rfl) (eV σ a0 a1)
  obtain ⟨h1, h1s⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int 1) = some Srt.int from rfl) (eV σ a0 a1)
  obtain ⟨hff, hfs⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.bool false) = some Srt.bool from rfl) (eV σ a0 a1)
  rw [int_name] at h0s h1s
  rw [bool_name] at hfs
  have ha0 : Inh I σ a0 := (interp_inhOf_of (S := KoreAML.sym _) hσ1).mp h0s
  have ha1 : Inh I σ a1 := (interp_inhOf_of (S := KoreAML.sym _) hσ1).mp h1s
  have hf : Inh I σB f := (interp_inhOf_of (S := KoreAML.sym _) hB1).mp hfs
  -- the guards
  have hg : ∀ k ∈ (U.ax126.ax.sortVars.map sortVarKey ++ freeOf [] U.ax126.ax.pattern).eraseDups, ∀ m,
      (guardOf (tableOf U.ax126.ax.sortVars U.ax126.ax.pattern) k).interpret I (eV σ a0 a1) m := by
    intro k hk m
    have hk' := List.all_eq_true.mp s126_free k hk
    cases k with
    | sortVar n => exact (interp_guard_sortVar hD).mpr hσ2
    | evar n s => exact absurd hk' (by simp)
    | svar n s =>
      have hs : s = KoreAML.srt "Int" := of_decide_eq_true hk'
      subst hs
      unfold guardOf
      refine (interp_included hD).mpr fun a ha => ?_
      rw [trSort_srt]
      refine (interp_inhOf_of (S := KoreAML.sym _) hσ1).mpr ?_
      rcases (ha : a = a0 ∨ a = a1) with rfl | rfl
      · exact ha0
      · exact ha1
  have hsrt : srtOf (cH H) Srt.int = KoreAML.srt "Int" := by unfold srtOf; rw [int_name]
  refine ⟨eV σ a0 a1, ?_, ?_, ?_⟩
  · intro n s hn
    exact absurd (List.all_eq_true.mp s126_noEvar _ hn) (by simp)
  · intro n s hn m hm
    have hs : s = KoreAML.srt "Int" := of_decide_eq_true (List.all_eq_true.mp s126_svars _ hn)
    subst hs
    rcases (hm : m = a0 ∨ m = a1) with rfl | rfl
    · exact ⟨KCore.int 0, Srt.int, hsrt, rfl, (h0 _).mpr rfl⟩
    · exact ⟨KCore.int 1, Srt.int, hsrt, rfl, (h1 _).mpr rfl⟩
  · intro hax
    rw [s126_trS] at hax
    have hP : (tr ⟨tableOf U.ax126.ax.sortVars U.ax126.ax.pattern, []⟩ U.ax126.ax.pattern).interpret I
        (eV σ a0 a1) a0 := by
      have h1 := hax
      unfold trAxiom at h1
      dsimp only at h1
      have h2 := h1 (interp_conjList fun w hw => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
        exact hg k hk default)
      rw [interp_equal hD] at h2
      refine (h2 a0).mpr ?_
      rw [s126_sort]
      exact (interp_inhOf_of (S := TR _) (fun b => Iff.rfl)).mpr ha0
    rw [s126_pattern] at hP
    -- the left side's application holds 0 %Int 1 = 0
    have hgm := (interp_equal hD).mp (sat_dom hI (Or.inl ⟨⟨intTMod, [Srt.int, Srt.int], Srt.int⟩,
      [KCore.int 0, KCore.int 1], some (KCore.int 0), by decide +kernel, rfl, mod_0_1, fun h => absurd h (by simp), rfl⟩)
        (eV σ a0 a1) default) a0
    have hm2 : KoreAML.den (symApp (cH H) intTMod (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 1])) =
        (KoreAML.sym (.symbol modN) ⬝ den (cH H) (KCore.int 0)) ⬝ den (cH H) (KCore.int 1) := by
      unfold symApp; rw [(mod_name H).1, (mod_name H).2]; rfl
    rw [hm2] at hgm
    have hL : (Lp (tableOf U.ax126.ax.sortVars PAT)).interpret I (eV σ a0 a1) a0 := by
      obtain ⟨g, b, hg1, hb, happ⟩ := interp_app.mp (hgm.mpr ((h0 a0).mpr rfl))
      obtain ⟨g', b', hg', hb', happ'⟩ := interp_app.mp hg1
      exact interp_app.mpr ⟨g, b, interp_app.mpr ⟨g', b', hg', Or.inl ((h0 b').mp hb'), happ'⟩,
        Or.inr ((h1 b).mp hb), happ⟩
    -- `@I2 =/=Int 0` holds `false`
    have hgn := (interp_equal hD).mp (sat_dom hI (Or.inl ⟨⟨intNe, [Srt.int, Srt.int], Srt.bool⟩,
      [KCore.int 0, KCore.int 0], some (KCore.bool false), by decide +kernel, rfl, ne_0_0, fun h => absurd h (by simp), rfl⟩)
        (eV σ a0 a1) default) f
    have hn2 : KoreAML.den (symApp (cH H) intNe (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 0])) =
        (KoreAML.sym (.symbol neN) ⬝ den (cH H) (KCore.int 0)) ⬝ den (cH H) (KCore.int 0) := by
      unfold symApp; rw [(ne_name H).1, (ne_name H).2]; rfl
    rw [hn2] at hgn
    have hNE : (NEp (tableOf U.ax126.ax.sortVars PAT)).interpret I (eV σ a0 a1) f := by
      obtain ⟨g, b, hg1, hb, happ⟩ := interp_app.mp (hgn.mpr ((hff f).mpr rfl))
      obtain ⟨g', b', hg', hb', happ'⟩ := interp_app.mp hg1
      exact interp_app.mpr ⟨g, b, interp_app.mpr ⟨g', b', hg', Or.inl ((h0 b').mp hb'), happ'⟩,
        by rw [← den_int0 H]; exact hb, happ⟩
    -- `true` does not hold `false`'s element
    have hmem : Srt.bool ∈ distinctSorts (cH H) := List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    have hT : ¬ TRUEp.interpret I (eV σ a0 a1) f := fun h => by
      rw [← den_true H] at h
      exact dom_apart hI (List.contains_iff_mem.mpr hmem) (v := KCore.bool false) (w := KCore.bool true) rfl rfl
        (by simp [KCore.bool]) (eV σ a0 a1) f ⟨(hff f).mpr rfl, h⟩
    exact core hD hc _ hσ2 hB2 hσ1 hB1 ha0 ha0 hL hf hNE hT hP

/-- **Sentence 126 is refuted, for every H**: Γ with it has no model. -/
theorem ceil126_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax126).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := ceil126_at H hI
  exact hn (hax e default)

/-- The sentence is not entailed at values (`EntailsAtValues` as it is defined) by a Γ that has a model. -/
theorem ceil126_not_at_values (H : HookParams)
    (hm : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H)) :
    ¬ EntailsAtValues (cH H) U.ax126 (trS U.ax126).pat := by
  intro h
  obtain ⟨M, inst, I, hI⟩ := hm
  obtain ⟨e, hav, -, hn⟩ := ceil126_at H hI
  exact hn (h M inst I hI e hav default)

/-- Nor is it entailed at set values (`EntailsAtSetValues`): the counterexample is at values. -/
theorem ceil126_not_at_set_values (H : HookParams)
    (hm : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H)) :
    ¬ EntailsAtSetValues (cH H) U.ax126 (trS U.ax126).pat := by
  intro h
  obtain ⟨M, inst, I, hI⟩ := hm
  obtain ⟨e, hav, hsv, hn⟩ := ceil126_at H hI
  exact hn (h M inst I hI e hav hsv default)

end KCore.LibSetVarCeil

#check @KCore.LibSetVarCeil.core
#check @KCore.LibSetVarCeil.ceil126_at
#check @KCore.LibSetVarCeil.ceil126_refuted
#check @KCore.LibSetVarCeil.ceil126_not_at_values
#check @KCore.LibSetVarCeil.ceil126_not_at_set_values
/-- info: 'KCore.LibSetVarCeil.ceil126_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibSetVarCeil.ceil126_at
/-- info: 'KCore.LibSetVarCeil.ceil126_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibSetVarCeil.ceil126_refuted
/-- info: 'KCore.LibSetVarCeil.ceil126_not_at_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibSetVarCeil.ceil126_not_at_values
/-- info: 'KCore.LibSetVarCeil.ceil126_not_at_set_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibSetVarCeil.ceil126_not_at_set_values
