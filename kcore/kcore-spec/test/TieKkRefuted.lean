/-
  Row KORE in K, the refuted classes on kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`), for every interpretation H, on
  the generated package's semantics `RefKk.defn.sem` with its `coreOK` (`RefKk.coreOK_defn`).
  Run from the package root with the package built (test/kk-tie-atvalues.sh does both).

  - Set idempotence, 104 (`_Set_(K, K) = K`): Γ with it has no model (`idem_refuted`). At
    `K = SetItem(0)` the sentence says `_Set_(K, K)` denotes `K`'s element, and the graph of `_Set_`
    (the two sets share a member, a point that is not silent) says it denotes nothing.
  - Set-variable lemmas: 379 (`%Int`, domains.md 1393), 380 (`/Int`, 1392), 383 (`modInt`, 1394):
    `#Ceil(@I1 f @I2) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)`, at
    `@I1 = {0}`, `@I2 = {1, 0}`; 381 (`<<Int`, 1396), 382 (`>>Int`, 1395), the same with
    `@I2 >=Int 0`, at `@I1 = {0}`, `@I2 = {0, -1}`; 837, kompile's lemma
    `#Ceil(@K0 |-> @K1 @Rest) => {@K0 in_keys(@Rest) #Equals false} #And #Ceil(@K1)`, at
    `@K0 = @K1 = {0}` (the KItem injection of 0), `@Rest = {.Map, 0 |-> 0}`. For each sentence `n`:
    `sn_at` (in every model of Γ the sentence fails at a valuation meeting `AtValues` and
    `SetVarsAtValues`), `sn_refuted` (Γ with it has no model) and `sn_one` (it holds at every
    valuation at values whose set variables hold at most one element).
-/
import RefKk.CoreOK

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKkRefuted

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := RefKk.defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## Set idempotence (104): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax104.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax104).pat = (trAxiom [] [] U.ax104).pat := by decide +kernel

theorem coreOKH : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans RefKk.coreOK_defn

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
theorem idem_vars : (U.ax104.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax104.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax104.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 104 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax104).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax104.ax.sortVars U.ax104.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax104.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax104.ax.pattern).eraseDups,
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

/-! ## The set-variable lemmas -/

section Ceil

theorem coreOKH' (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans RefKk.coreOK_defn
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- What a refutation at values gives: Γ with the sentence has no model. -/
theorem refuted_of_at {c' : Semantics} {ad : AxiomDecl} {φ : KoreAML.P}
    (hat : ∀ (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' →
      ∃ e : Valuation M, AtValues c' I e ad.ax ∧ SetVarsAtValues c' I e ad.ax ∧ ¬ φ.interpret I e default) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' → ¬ (I ⊧ᴵ φ) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := hat M I hI
  exact hn (hax e default)

/-! ## The Int lemmas -/

theorem t379 : (trS U.ax379).pat = (trAxiom [] [] U.ax379).pat := by decide +kernel
theorem t380 : (trS U.ax380).pat = (trAxiom [] [] U.ax380).pat := by decide +kernel
theorem t381 : (trS U.ax381).pat = (trAxiom [] [] U.ax381).pat := by decide +kernel
theorem t382 : (trS U.ax382).pat = (trAxiom [] [] U.ax382).pat := by decide +kernel
theorem t383 : (trS U.ax383).pat = (trAxiom [] [] U.ax383).pat := by decide +kernel

theorem s379_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax379.ax ∧ SetVarsAtValues (cH H) I e U.ax379.ax ∧
      ¬ (trS U.ax379).pat.interpret I e default := by
  rw [t379]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTMod intNe (by decide +kernel) (by rfl) 0 1 0
    ⟨_, LibEv.hv_intTMod (by decide)⟩ (by rw [LibEv.hv_intNe]; rfl) U.ax379 (by decide +kernel) (by decide +kernel) hI
theorem s380_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax380.ax ∧ SetVarsAtValues (cH H) I e U.ax380.ax ∧
      ¬ (trS U.ax380).pat.interpret I e default := by
  rw [t380]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTDiv intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_tdiv 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax380
    (by decide +kernel) (by decide +kernel) hI
theorem s383_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax383.ax ∧ SetVarsAtValues (cH H) I e U.ax383.ax ∧
      ¬ (trS U.ax383).pat.interpret I e default := by
  rw [t383]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intEMod intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_emod 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax383
    (by decide +kernel) (by decide +kernel) hI
theorem s381_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax381.ax ∧ SetVarsAtValues (cH H) I e U.ax381.ax ∧
      ¬ (trS U.ax381).pat.interpret I e default := by
  rw [t381]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShl intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shl 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax381
    (by decide +kernel) (by decide +kernel) hI
theorem s382_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax382.ax ∧ SetVarsAtValues (cH H) I e U.ax382.ax ∧
      ¬ (trS U.ax382).pat.interpret I e default := by
  rw [t382]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShr intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shr 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax382
    (by decide +kernel) (by decide +kernel) hI

theorem s379_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax379).pat) := refuted_of_at (s379_at H)
theorem s380_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax380).pat) := refuted_of_at (s380_at H)
theorem s381_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax381).pat) := refuted_of_at (s381_at H)
theorem s382_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax382).pat) := refuted_of_at (s382_at H)
theorem s383_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax383).pat) := refuted_of_at (s383_at H)

theorem s379_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax379 (trS U.ax379).pat := by
  rw [t379]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tmod U.ax379 (by decide +kernel) (by decide +kernel)
theorem s380_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax380 (trS U.ax380).pat := by
  rw [t380]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTDiv intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tdiv U.ax380 (by decide +kernel) (by decide +kernel)
theorem s381_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax381 (trS U.ax381).pat := by
  rw [t381]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShl intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shl U.ax381 (by decide +kernel) (by decide +kernel)
theorem s382_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax382 (trS U.ax382).pat := by
  rw [t382]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShr intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shr U.ax382 (by decide +kernel) (by decide +kernel)
theorem s383_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax383 (trS U.ax383).pat := by
  rw [t383]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intEMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_emod U.ax383 (by decide +kernel) (by decide +kernel)

/-! ## The Map lemma -/

theorem t837 : (trS U.ax837).pat = (trAxiom [] [] U.ax837).pat := by decide +kernel

/-- The KItem injection of 0. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel

theorem s837_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax837.ax ∧ SetVarsAtValues (cH H) I e U.ax837.ax ∧
      ¬ (trS U.ax837).pat.interpret I e default := by
  rw [t837]
  exact LibEv.ceilMap_refuted_at (coreOKH' H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H) (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax837 (by decide +kernel) (by decide +kernel) hI

theorem s837_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax837).pat) := refuted_of_at (s837_at H)

theorem s837_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax837 (trS U.ax837).pat := by
  rw [t837]
  exact LibEv.ceilMap_one (coreOKH' H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax837 (by decide +kernel) (by decide +kernel)

end Ceil

/-- The sentences of the two refuted classes. -/
theorem idem_indices : [U.ax104].map (·.index) = [104] := by decide +kernel
theorem setvar_indices : [U.ax379, U.ax380, U.ax381, U.ax382, U.ax383, U.ax837].map (·.index) =
    [379, 380, 381, 382, 383, 837] := by decide +kernel

end KCore.TieKkRefuted

/-- info: 'KCore.TieKkRefuted.idem_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.idem_refuted
/-- info: 'KCore.TieKkRefuted.s379_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s379_refuted
/-- info: 'KCore.TieKkRefuted.s380_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s380_refuted
/-- info: 'KCore.TieKkRefuted.s381_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s381_refuted
/-- info: 'KCore.TieKkRefuted.s382_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s382_refuted
/-- info: 'KCore.TieKkRefuted.s383_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s383_refuted
/-- info: 'KCore.TieKkRefuted.s837_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s837_refuted
/-- info: 'KCore.TieKkRefuted.s379_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s379_one
/-- info: 'KCore.TieKkRefuted.s380_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s380_one
/-- info: 'KCore.TieKkRefuted.s381_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s381_one
/-- info: 'KCore.TieKkRefuted.s382_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s382_one
/-- info: 'KCore.TieKkRefuted.s383_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s383_one
/-- info: 'KCore.TieKkRefuted.s837_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkRefuted.s837_one
