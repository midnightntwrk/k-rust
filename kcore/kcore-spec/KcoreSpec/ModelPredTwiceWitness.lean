/-
  KCore. A semantics that meets every condition of `coreOK` but `predsApart`, whose `Γ` has no
  model because two of its functions bear one label, and which meets `FnHyp`: so `SoundC` fails of
  it (`not_sound`), and `coreOK` needs `predsApart`'s distinct labels of the functions.

  The configuration `<k> K </k>` with the generated counter, and two functions of `c.fns`, both
  labelled as the predicate of the own sort KCell and both `K → Bool` of one clause `X ↦ b`, one
  with `b = true` and one with `b = false`. `sortPreds` builds no function under a label of
  `c.fns`, so `idsOK` accepts the semantics, and `predsApart` refuses it: the label is listed
  twice in `allFns`.

  Each clause's equation is a sentence of `Γ`: the predicate's application to `dotk` equals `true`,
  and it equals `false`. In a model the application then denotes the element of `true` and that of
  `false`, which are distinct since `true` and `false` are distinct values of Bool
  (`values_apart`). `FnHyp` holds (`fnHyp`): evaluation reads the label as the function giving
  `true`, which has that value at every K, and each clause is the only one of its function, binds
  its variable and reads none. The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound
import KcoreSpec.FaithfulNeg
import KcoreSpec.ModelPrioTextWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace PredTwiceWitness

open ML

/-- The clause `X ↦ b`, X of sort K. -/
def clTw (b : Bool) : Clause :=
  { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool b), ens := none }

/-- A function of `K` to `Bool` under the label `l`, of one clause giving `b`. -/
def predFnTw (l : Sym) (b : Bool) : Fn :=
  { label := l, args := [Srt.k], result := Srt.bool, clauses := [clTw b], total := true }

/-- The functions giving `true` and `false`, both under the predicate number of KCell. -/
def fnT : Fn := predFnTw nRegSyms true
def fnF : Fn := predFnTw nRegSyms false

def c : Semantics :=
  { PrioTextWitness.c with fns := [fnT, fnF], symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"] }

/-- `predsApart` refuses `c`: `allFns` lists the label twice. -/
theorem not_predsApart : c.predsApart = false := by decide +kernel

/-- The label's own sort is KCell, whose predicate `sortPreds` does not build. -/
theorem pred_label : predOf nRegSorts = some nRegSyms := by decide +kernel
theorem no_sortPred : (c.sortPreds.map (·.label)).contains nRegSyms = false := by decide +kernel

/-- The label names the function giving `true`. -/
theorem lookup_T : c.lookupFn nRegSyms = some fnT := rfl

theorem fnT_mem : fnT ∈ c.allFns := List.mem_append_left _ (List.mem_cons_self ..)
theorem fnF_mem : fnF ∈ c.allFns := List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- A clause's equation reads its function's label, argument sorts and result sort only. -/
theorem clauseAxiom_congr (c : Semantics) {fn fn' : Fn} (hl : fn.label = fn'.label) (ha : fn.args = fn'.args)
    (hr : fn.result = fn'.result) (cl : Clause) : clauseAxiom c fn cl = clauseAxiom c fn' cl := by
  unfold clauseAxiom clausePrem clauseConcl clauseRight
  rw [hl, ha, hr]

/-- The subsorts of `c` are closed under composition. -/
theorem subsorts_trans : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := by
  have h : (c.subsorts.all fun (a, b) => c.subsorts.all fun (b', d) => b != b' || c.subsorts.contains (a, d)) = true :=
    by decide +kernel
  simp only [List.all_eq_true] at h
  intro a b d hab hbd
  have := h (a, b) hab (b, d) hbd
  simp only [bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at this
  exact this

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem namesNumbered : NamesNumbered c := namesNumbered_spec (by decide +kernel)

/-- The term `dotk`, of sort K. -/
def dotkG : GroundTerm := .ctor dotk []

theorem dotk_sorts : c.sortsOf [dotkG] = some [Srt.k] := by decide +kernel

theorem sg_sorted : c.WellSorted [Srt.k] [(0, dotkG)] := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨dotkG, rfl, by decide +kernel⟩
  | succ i => simp at hs

theorem bool_sort (b : Bool) : c.sortOf (bool b) = some Srt.bool := by cases b <;> decide +kernel

/-! ## `FnHyp` -/

theorem sg_sorted_at {w : GroundTerm} (hw : c.sortOf w = some Srt.k) : c.WellSorted [Srt.k] [(0, w)] := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨w, rfl, hw⟩
  | succ i => simp at hs

/-- The label's application to a K `w` is `true`, by the clause of `fnT`. -/
theorem eval_T {w : GroundTerm} (hw : c.sortOf w = some Srt.k) : Eval c nRegSyms [w] (some (bool true)) :=
  .clause (fn := fnT) (cl := clTw true) (σ := [(0, w)]) lookup_T (List.mem_singleton_self _) (sg_sorted_at hw)
    (.cons (.var rfl) .nil) (fun _ ht => nomatch ht) .top
    (fun cl' h _ hlt => by rw [List.mem_singleton.mp h] at hlt; exact absurd hlt (Nat.lt_irrefl _)) rfl .dv
    (fun _ ht => nomatch ht) .top

theorem mem_fns {fn : Fn} (h : fn ∈ c.fns) : fn = fnT ∨ fn = fnF := by simpa [c] using h

theorem args_inv {fn : Fn} (h : fn ∈ c.fns) {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args) :
    ∃ w, vs = [w] ∧ c.sortOf w = some Srt.k := by
  have ha : fn.args = [Srt.k] := by rcases mem_fns h with rfl | rfl <;> rfl
  rw [ha] at hvs
  cases vs with
  | nil => rw [sortsOf_nil] at hvs; cases hvs
  | cons w vs =>
    obtain ⟨s, ss, hw, hss, he⟩ := sortsOf_cons.mp hvs
    cases he
    cases vs with
    | nil => exact ⟨w, rfl, hw⟩
    | cons v vs => obtain ⟨_, _, _, _, h⟩ := sortsOf_cons.mp hss; cases h

/-- `FnHyp` holds: each function has the value `true` at every K (the label names `fnT`), the two
clauses are each of one function, have no existential variable and read no variable on their
right side. -/
theorem fnHyp : FnHyp c := by
  have hlab : ∀ fn ∈ c.fns, fn.label = nRegSyms := fun fn h => by rcases mem_fns h with rfl | rfl <;> rfl
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn _ vs hvs => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩
  · obtain ⟨w, rfl, hw⟩ := args_inv hfn hvs
    exact ⟨_, hlab fn hfn ▸ eval_T hw⟩
  · obtain ⟨w, rfl, hw⟩ := args_inv hfn hvs
    exact ⟨_, hlab fn hfn ▸ eval_T hw⟩
  · intro cl cl' hp _
    rcases mem_fns hfn with rfl | rfl <;> exact absurd hp (by simp [fnT, fnF, predFnTw, pairs])
  · have hcl' : ∃ b, cl = clTw b := by
      rcases mem_fns hfn with rfl | rfl
      · exact ⟨true, List.mem_singleton.mp hcl⟩
      · exact ⟨false, List.mem_singleton.mp hcl⟩
    obtain ⟨b, rfl⟩ := hcl'
    exact (matchIndependent_iff_noExs rfl).mpr fun vs σ σ' _ _ _ _ _ _ _ =>
      Or.inl ⟨rfl, rfl, rfl, rfl, fun i hi => (by simp [clTw, varOccs] at hi), fun t ht => (by simp [clTw] at ht)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `predsApart` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ FnHyp c :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fnHyp⟩

section NoModel

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A clause's equation at `dotk`**: in a model of `Γ c`, the predicate's application to `dotk`
denotes what the clause's right side `b` denotes, the clause being the one of `fnT` or of `fnF`. -/
theorem eq_at_dotk (hI : I ⊧ᴵP Γ c) {fn : Fn} (hfn : fn ∈ c.allFns) (hl : fn.label = nRegSyms)
    (ha : fn.args = [Srt.k]) (hr : fn.result = Srt.bool) (b : Bool)
    (hcl : clTw b ∈ fn.clauses) (hlow : lowerClauses fn (clTw b) = [])
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c nRegSyms (GroundTerm.koreList c [dotkG]))).interpret I e0 m ↔
      Res c I e0 (some (bool b)) m := by
  have hax0 := sat_fns hI (Or.inl ⟨_, clause_item_mem hfn hcl hlow rfl rfl, rfl⟩)
  have hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fnT (clTw b)⟩).pat := by
    rw [clauseAxiom_congr c (fn' := fn) (by rw [hl]; rfl) (by rw [ha]; rfl) (by rw [hr]; rfl) (clTw b)]
    exact hax0
  have hrv : ∀ v, some (bool b) = some v → c.sortOf v = some fnT.result := fun v hv => by
    cases hv; exact bool_sort b
  exact PrioTextWitness.clause_eq_ax hI namesNumbered subsorts_trans lookup_T (cl := clTw b) hax (ws := [dotkG])
    dotk_sorts (σ' := [(0, dotkG)]) sg_sorted (.cons (.var rfl) .nil) (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide) (fun _ h => by cases h) (fun _ h => by simp [clTw, varOccs] at h) (fun _ h => by cases h)
    (r := some (bool b)) hrv (fun _ _ _ _ h => by cases h)
    (fun tbl e _ => right_iff hI namesNumbered fnT_mem hrv
      (fun m => by
        show (KoreAML.tr ⟨tbl, []⟩ (GroundTerm.kore c (bool b))).interpret I e m ↔ (den c (bool b)).interpret I e m
        rfl)
      (fun _ ht => by cases ht))
    e0 m

end NoModel

/-- **`Γ c` has no model**: the predicate's application to `dotk` would denote the element of
`true` and that of `false`, two distinct values of Bool. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have heqT := eq_at_dotk hI fnT_mem rfl rfl rfl true (List.mem_singleton_self _) rfl
  have heqF := eq_at_dotk hI fnF_mem rfl rfl rfl false (List.mem_singleton_self _) rfl
  have hT := (elemOf_spec hI (bool_sort true) KoreAML.val0).1
  have hF := (elemOf_spec hI (bool_sort false) KoreAML.val0).1
  have he : elemOf c I (bool true) = elemOf c I (bool false) :=
    (hF _).mp ((heqF KoreAML.val0 _).mp ((heqT KoreAML.val0 _).mpr ((hT _).mpr rfl)))
  have := values_apart hI (by decide +kernel : genWf c = true) subsorts_trans
    (by decide +kernel : apartSort c Srt.bool = true) (bool_sort true) (bool_sort false) he
  cases this

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `predsApart`, and
`FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end PredTwiceWitness

end Faithful

end KCore
