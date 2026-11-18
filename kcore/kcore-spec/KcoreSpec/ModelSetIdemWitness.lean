/-
  KCore. `Γ` refutes the idempotence axiom that K's text states of set concatenation: `Γ c` has a
  model (`has_model`), and `Γ c` with the axiom `_Set_(K, K) = K` has none (`not_model_idem`).

  Every semantics has the library's `Set` (`builtinColls`). `ΓDomains` gives `_Set_` the graph of
  its interpretation (`concatS`): the union of two sets with no member in common, undefined where
  they share one, so `_Set_(SetItem(a), SetItem(a))` denotes nothing. The axiom `[idem]` of the text,
  `\equals{Set, R}(_Set_(K, K), K)`, says at `K = SetItem(a)` that it denotes the element of
  `SetItem(a)`. The semantics is the configuration `<k> K </k>` with the generated counter and
  nothing else. The decidable facts are kernel decisions.
-/
import KcoreSpec.ModelHas

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace SetIdemWitness

open ML

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 2, no := some (nRegSyms + 3) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem okAll : c.okAll = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem idsOK : c.idsOK = true := by decide +kernel
theorem names_plain : c.ctorSigs.all (fun k => (iteSort? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_fns : c.allFns.all (fun fn => (iteSort? (c.symName fn.label)).isNone &&
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun o ho g hg => ?_, fun fn hfn s hs => ?_⟩
  · exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp names_plain k hk)
  · have h : c.ovls.all (fun o => o.over.all fun g => (iteSort? (c.symName g)).isNone) = true := by
      decide +kernel
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp (List.all_eq_true.mp h o ho) g hg)
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true (List.all_eq_true.mp this.2 s hs)

/-- `c` has no function of its own, so the semantic conditions of `Hyp` hold vacuously. -/
theorem hyp : Hyp c :=
  ⟨okAll, srReady, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, namesNumbered⟩

theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, inferInstance⟩

set_option maxHeartbeats 1000000 in
theorem hypModel : Model.HypModel c :=
  ⟨hyp, hypSound, by decide +kernel, by decide +kernel, idsOK, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`Γ c` has a model.** -/
theorem has_model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  Model.has_model hypModel (Semantics.rulesTop_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))

/-! ## The idempotence axiom -/

/-- The set variable `K` of the axiom. -/
def kVar : Kore.Pattern := KoreAML.ev "VarK" (srtOf c Srt.set)

/-- The axiom `[idem]` of `_Set_`, as kompile writes it: `\equals{Set, R}(_Set_(K, K), K)`. -/
def idemAxiom : Kore.Axiom :=
  { sortVars := [KoreAML.Rv]
    pattern := .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar
    attributes := [] }

def idemItem : KoreAML.Item := KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxiom⟩

/-- `Γ c` with the idempotence axiom. -/
def ΓIdem : Premises KoreAML.Sym := Γ c ∪ fun φ => φ = idemItem.pat

/-- `{.K}` as a KItem, and the set `SetItem(.K)`. -/
def a0 : GroundTerm := .inj nRegSorts Srt.kitem (.ctor kIds.label [.ctor dotk []])
def s1 : GroundTerm := .set Srt.set [a0]

theorem s1_sort : c.sortOf s1 = some Srt.set := by decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : c.sortsOf [s1, s1] = some [Srt.set, Srt.set] := by decide +kernel
/-- `SetItem(.K) SetItem(.K)` is undefined: the two sets share a member. -/
theorem concat_none : hook setConcat [s1, s1] = some none := by decide +kernel
theorem concat_heard : silent setConcat [s1, s1] = false := by decide +kernel
theorem set_numbered : Srt.set < nRegSorts + c.sortNames.length := by decide
theorem set_name : c.sortName Srt.set = "Set" := by decide +kernel
theorem concat_plain : iteSort? (c.symName setConcat) = none := by decide +kernel

theorem idem_vars : (idemAxiom.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] idemAxiom.pattern).eraseDups =
    [.sortVar "R", .evar "VarK" (KoreAML.srt "Set")] := by decide +kernel

theorem idem_sort : KoreAML.sortOf [] idemAxiom.pattern = some KoreAML.R := by decide +kernel

/-- **`Γ c` with the idempotence axiom has no model**: at `K = SetItem(.K)`, the axiom says that
`_Set_(K, K)` denotes the element of `SetItem(.K)`, and `ΓDomains` says it denotes nothing. -/
theorem not_model_idem : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP ΓIdem) := by
  intro M _ I hI'
  have hI : I ⊧ᴵP Γ c := fun φ h => hI' φ (Or.inl h)
  have hax : I ⊧ᴵ idemItem.pat := hI' _ (Or.inr rfl)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI set_numbered
  rw [set_name] at hσS1
  obtain ⟨hes, hesort⟩ := elemOf_spec hI s1_sort KoreAML.val0
  rw [set_name] at hesort
  let a := elemOf c I s1
  have ha : KoreAML.Inh I σS a := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hesort
  let tbl : KoreAML.VarTable := KoreAML.tableOf idemAxiom.sortVars idemAxiom.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "VarK" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "VarK" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (idemAxiom.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] idemAxiom.pattern).eraseDups,
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
  change (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar)).interpret
    I e' a at hP
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.set)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [set_name, trSort_srt]; exact hσS1 b
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hK : ∀ b, (KoreAML.tr ⟨tbl, []⟩ kVar).interpret I e' b ↔ b = a := fun b => by
    unfold kVar KoreAML.ev srtOf
    rw [set_name, KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar "VarK" (KoreAML.srt "Set"))) ↔ b = a
    rw [hKv]
  -- `_Set_(K, K)` at `K = a` holds `a`
  have happ := (hall a ha).mpr ((hK a).mpr rfl)
  rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at happ
  -- so does `_Set_(SetItem(.K), SetItem(.K))`
  have hden : (KoreAML.den (symApp c setConcat (GroundTerm.koreList c [s1, s1]))).interpret I KoreAML.val0 a := by
    unfold KoreAML.den
    rw [tr_symApp]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp happ
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    refine KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, ?_, (hes b0).mpr ((hK b0).mp hb0), h0⟩,
      (hes b1).mpr ((hK b1).mp hb1), h1⟩
    exact (sym_congr (e := KoreAML.val0) (e' := e') _ f0).mpr hf0
  -- and `ΓDomains` says it holds nothing
  have hgraph := sat_dom hI (Or.inl ⟨_, [s1, s1], none, concat_sig, concat_args, concat_none,
    fun _ => concat_heard, rfl⟩)
  have := ((KoreAML.interp_equal hD).mp (hgraph KoreAML.val0 default) a).mp hden
  exact this

end SetIdemWitness

end Faithful

end KCore
