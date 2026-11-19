/-
  KCore. A semantics that meets every condition of `coreOK` but the fourth leaf of `itesApart`, and
  `FnHyp`, whose `Γ` has no model: a parameter of no arguments plainly named `Lblsel` beside a
  parameter named `Lblsel{Int}`, an instance of the head `Lblsel` at `Int`. So that leaf (no symbol
  of no arguments is plainly named by the head of an instance-named symbol) cannot be left out of
  `coreOK`.

  `Γ` writes the instance as the head `Lblsel` applied to the sort `SortInt` (`symApp`), and the
  constant as the symbol `Lblsel`: one symbol of the theory. The constant has no implementation, so
  its graph (`ΓDomains`) says `Lblsel` is ⊥; the instance is `_+Int_`, so its graph says
  `Lblsel SortInt 1 1` is `2`. An application of ⊥ is ⊥, and `2` denotes an element. The
  first three leaves of `itesApart` hold (`leaves_123`). The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace InstConstWitness

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

/-- `Lblsel`, a constant of Int with no implementation. -/
def pc : ParamSig := { sig := ⟨nRegSyms + 4, [], Srt.int⟩ }
/-- `Lblsel{Int}`, implemented by `_+Int_`. -/
def p1 : ParamSig := { sig := ⟨nRegSyms + 5, [Srt.int, Srt.int], Srt.int⟩, impl := some intAdd }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblsel", "Lblsel{Int}"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [pc, p1] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

/-- Every condition of `coreOK` but `itesApart` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.collsNotCtors c = true ∧ Model.kindsApart c = true ∧
    Model.ctorsOnce c = true ∧ Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, fnHyp⟩

/-- The first three leaves of `itesApart` hold of every symbol with a signature: the one instance
name `Lblsel{Int}` is at the numbered sort `Int`, the one instance of its head, and its head is not
`inj`. -/
theorem leaves_123 : ((kernelSyms c).all fun k =>
    (match instDecode? (c.symName k.name) with
      | some (_, xs) => xs.all fun x => (kernelSorts c).any fun s => c.sortName s == x
      | none => true) &&
    (match instDecode? (c.symName k.name) with
      | some (h, xs) => (kernelSyms c).all fun k' =>
          match instDecode? (c.symName k'.name) with
          | some (h', xs') => h' != h || xs'.length == xs.length
          | none => true
      | none => true) &&
    (match instDecode? (c.symName k.name) with
      | some (h, _) => h != "inj"
      | none => true)) = true := by decide +kernel

/-- `itesApart` fails, at its fourth leaf: the constant `pc` is plainly named by the head of `p1`. -/
theorem not_itesApart : Model.itesApart c = false := by decide +kernel

theorem pc_plain : instDecode? (c.symName pc.sig.name) = none := by decide +kernel
theorem pc_name : c.symName pc.sig.name = "Lblsel" := by decide +kernel
theorem p1_inst : instDecode? (c.symName p1.sig.name) = some ("Lblsel", ["Int"]) := by decide +kernel

/-- The values `1` and `2` of Int. -/
def v1 : GroundTerm := .dv Srt.int (.int 1)
def v2 : GroundTerm := .dv Srt.int (.int 2)

theorem v2_sort : c.sortOf v2 = some Srt.int := by decide +kernel
theorem nil_sort : c.sortsOf [] = some pc.sig.args := by decide +kernel
theorem args_sort : c.sortsOf [v1, v1] = some p1.sig.args := by decide +kernel
theorem pc_val : c.paramVal pc.sig.name [] = none := by decide +kernel
theorem p1_val : c.paramVal p1.sig.name [v1, v1] = some v2 := by decide +kernel

/-- Where an application of a head to arguments holds an element, the head does. -/
theorem appList_head_inh {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} :
    ∀ (ψs : List KoreAML.P) (h : KoreAML.P) (m : M), (KoreAML.appList h ψs).interpret I e m →
      ∃ a, h.interpret I e a
  | [], _, m, hm => ⟨m, hm⟩
  | ψ :: ψs, h, m, hm => by
    obtain ⟨a, ha⟩ := appList_head_inh ψs (h ⬝ ψ) m hm
    obtain ⟨a0, -, ha0, -⟩ := KoreAML.interp_app.mp ha
    exact ⟨a0, ha0⟩

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  -- the constant's graph: `Lblsel` is ⊥
  have hax0 := sat_dom hI (Or.inr (Or.inl ⟨pc, [], List.mem_cons_self .., nil_sort, rfl⟩))
  simp only [pc_val] at hax0
  have h0 := (KoreAML.interp_equal hD).mp (hax0 KoreAML.val0 default)
  -- the instance's graph: `Lblsel SortInt 1 1` is `2`
  have hax1 := sat_dom hI (Or.inr (Or.inl ⟨p1, [v1, v1], List.mem_cons_of_mem _ (List.mem_cons_self ..),
    args_sort, rfl⟩))
  simp only [p1_val] at hax1
  have h1 := (KoreAML.interp_equal hD).mp (hax1 KoreAML.val0 default)
  -- `2` denotes an element, so the instance's application holds one, and so does its head
  have hv := (elemOf_spec hI v2_sort KoreAML.val0).1
  have hm : (KoreAML.den (symApp c p1.sig.name (GroundTerm.koreList c [v1, v1]))).interpret I KoreAML.val0
      (elemOf c I v2) := (h1 _).mpr ((hv _).mpr rfl)
  unfold KoreAML.den at hm
  rw [symApp_inst p1_inst, tr_instApp, trArgs_appList] at hm
  obtain ⟨a, ha⟩ := appList_head_inh _ _ _ hm
  have ha' : (KoreAML.sym (.symbol "Lblsel") ⬝ KoreAML.sym (.sort ("Sort" ++ "Int"))).interpret I
      KoreAML.val0 a := ha
  obtain ⟨a0, -, ha0, -⟩ := KoreAML.interp_app.mp ha'
  -- the head is the constant
  have hc0 : (KoreAML.den (symApp c pc.sig.name (GroundTerm.koreList c []))).interpret I KoreAML.val0 a0 := by
    unfold KoreAML.den
    rw [symApp_noInst pc_plain, pc_name, KoreAML.tr_app0, trArgs_appList]
    exact ha0
  exact (h0 a0).mp hc0

end InstConstWitness

end Faithful

end KCore
