/-
  Row imp, the refuted classes on kimp's text as kompile wrote it
  (`examples/ref-kimp/RefKimp/definition.kore`, user module `IMP`), for every interpretation H, on
  the generated package's semantics `RefKimp.defn.sem` with its `coreOK` (`RefKimp.coreOK_defn`).
  Run from the package root with the package built (test/imp-tie-atvalues.sh does both).

  - Set idempotence, 573 (`_Set_(K, K) = K`): Γ with it has no model (`idem_refuted`). At
    `K = SetItem(0)` the sentence says `_Set_(K, K)` denotes `K`'s element, and the graph of `_Set_`
    (the two sets share a member, a point that is not silent) says it denotes nothing.
  - Set-variable lemmas: 671 (`%Int`, domains.md 1393), 672 (`/Int`, 1392), 675 (`modInt`, 1394):
    `#Ceil(@I1 f @I2) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)`, at
    `@I1 = {0}`, `@I2 = {1, 0}`; 673 (`<<Int`, 1396), 674 (`>>Int`, 1395), the same with
    `@I2 >=Int 0`, at `@I1 = {0}`, `@I2 = {0, -1}`; 904, kompile's lemma
    `#Ceil(@K0 |-> @K1 @Rest) => {@K0 in_keys(@Rest) #Equals false} #And #Ceil(@K1)`, at
    `@K0 = @K1 = {0}` (the KItem injection of 0), `@Rest = {.Map, 0 |-> 0}`. For each sentence `n`:
    `sn_at` (in every model of Γ the sentence fails at a valuation meeting `AtValues` and
    `SetVarsAtValues`), `sn_refuted` (Γ with it has no model) and `sn_one` (it holds at every
    valuation at values whose set variables hold at most one element).
-/
import RefKimp.Sound

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimpRefuted

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
user_axioms U from "examples/ref-kimp/RefKimp/definition.kore" module "IMP"

noncomputable abbrev c : Semantics := RefKimp.defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## Set idempotence (573): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax573.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax573).pat = (trAxiom [] [] U.ax573).pat := by decide +kernel

theorem coreOKH : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans RefKimp.coreOK_defn

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
theorem idem_vars : (U.ax573.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax573.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax573.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 573 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax573).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax573.ax.sortVars U.ax573.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax573.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax573.ax.pattern).eraseDups,
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

theorem coreOKH' (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans RefKimp.coreOK_defn
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

theorem t671 : (trS U.ax671).pat = (trAxiom [] [] U.ax671).pat := by decide +kernel
theorem t672 : (trS U.ax672).pat = (trAxiom [] [] U.ax672).pat := by decide +kernel
theorem t673 : (trS U.ax673).pat = (trAxiom [] [] U.ax673).pat := by decide +kernel
theorem t674 : (trS U.ax674).pat = (trAxiom [] [] U.ax674).pat := by decide +kernel
theorem t675 : (trS U.ax675).pat = (trAxiom [] [] U.ax675).pat := by decide +kernel

theorem s671_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax671.ax ∧ SetVarsAtValues (cH H) I e U.ax671.ax ∧
      ¬ (trS U.ax671).pat.interpret I e default := by
  rw [t671]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTMod intNe (by decide +kernel) (by rfl) 0 1 0
    ⟨_, LibEv.hv_intTMod (by decide)⟩ (by rw [LibEv.hv_intNe]; rfl) U.ax671 (by decide +kernel) (by decide +kernel) hI
theorem s672_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax672.ax ∧ SetVarsAtValues (cH H) I e U.ax672.ax ∧
      ¬ (trS U.ax672).pat.interpret I e default := by
  rw [t672]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTDiv intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_tdiv 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax672
    (by decide +kernel) (by decide +kernel) hI
theorem s675_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax675.ax ∧ SetVarsAtValues (cH H) I e U.ax675.ax ∧
      ¬ (trS U.ax675).pat.interpret I e default := by
  rw [t675]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intEMod intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_emod 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax675
    (by decide +kernel) (by decide +kernel) hI
theorem s673_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax673.ax ∧ SetVarsAtValues (cH H) I e U.ax673.ax ∧
      ¬ (trS U.ax673).pat.interpret I e default := by
  rw [t673]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShl intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shl 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax673
    (by decide +kernel) (by decide +kernel) hI
theorem s674_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax674.ax ∧ SetVarsAtValues (cH H) I e U.ax674.ax ∧
      ¬ (trS U.ax674).pat.interpret I e default := by
  rw [t674]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShr intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shr 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax674
    (by decide +kernel) (by decide +kernel) hI

theorem s671_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax671).pat) := refuted_of_at (s671_at H)
theorem s672_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax672).pat) := refuted_of_at (s672_at H)
theorem s673_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax673).pat) := refuted_of_at (s673_at H)
theorem s674_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax674).pat) := refuted_of_at (s674_at H)
theorem s675_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax675).pat) := refuted_of_at (s675_at H)

theorem s671_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax671 (trS U.ax671).pat := by
  rw [t671]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tmod U.ax671 (by decide +kernel) (by decide +kernel)
theorem s672_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax672 (trS U.ax672).pat := by
  rw [t672]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTDiv intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tdiv U.ax672 (by decide +kernel) (by decide +kernel)
theorem s673_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax673 (trS U.ax673).pat := by
  rw [t673]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShl intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shl U.ax673 (by decide +kernel) (by decide +kernel)
theorem s674_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax674 (trS U.ax674).pat := by
  rw [t674]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShr intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shr U.ax674 (by decide +kernel) (by decide +kernel)
theorem s675_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax675 (trS U.ax675).pat := by
  rw [t675]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intEMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_emod U.ax675 (by decide +kernel) (by decide +kernel)

/-! ## The Map lemma -/

theorem t904 : (trS U.ax904).pat = (trAxiom [] [] U.ax904).pat := by decide +kernel

/-- The KItem injection of 0. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel

theorem s904_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax904.ax ∧ SetVarsAtValues (cH H) I e U.ax904.ax ∧
      ¬ (trS U.ax904).pat.interpret I e default := by
  rw [t904]
  exact LibEv.ceilMap_refuted_at (coreOKH' H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H) (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax904 (by decide +kernel) (by decide +kernel) hI

theorem s904_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax904).pat) := refuted_of_at (s904_at H)

theorem s904_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax904 (trS U.ax904).pat := by
  rw [t904]
  exact LibEv.ceilMap_one (coreOKH' H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax904 (by decide +kernel) (by decide +kernel)

end Ceil

/-- The sentences of the two refuted classes. -/
theorem idem_indices : [U.ax573].map (·.index) = [573] := by decide +kernel
theorem setvar_indices : [U.ax671, U.ax672, U.ax673, U.ax674, U.ax675, U.ax904].map (·.index) =
    [671, 672, 673, 674, 675, 904] := by decide +kernel

end KCore.TieKimpRefuted

/-- info: 'KCore.TieKimpRefuted.idem_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.idem_refuted
/-- info: 'KCore.TieKimpRefuted.s671_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s671_refuted
/-- info: 'KCore.TieKimpRefuted.s672_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s672_refuted
/-- info: 'KCore.TieKimpRefuted.s673_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s673_refuted
/-- info: 'KCore.TieKimpRefuted.s674_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s674_refuted
/-- info: 'KCore.TieKimpRefuted.s675_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s675_refuted
/-- info: 'KCore.TieKimpRefuted.s904_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s904_refuted
/-- info: 'KCore.TieKimpRefuted.s671_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s671_one
/-- info: 'KCore.TieKimpRefuted.s672_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s672_one
/-- info: 'KCore.TieKimpRefuted.s673_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s673_one
/-- info: 'KCore.TieKimpRefuted.s674_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s674_one
/-- info: 'KCore.TieKimpRefuted.s675_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s675_one
/-- info: 'KCore.TieKimpRefuted.s904_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpRefuted.s904_one
