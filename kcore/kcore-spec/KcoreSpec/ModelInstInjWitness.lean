/-
  KCore. A semantics that meets every condition of `coreOK` but the third leaf of `itesApart`, and
  `FnHyp`, whose `Γ` has no model: a parameter named `inj{KCell,KCellOpt}`, an instance of the head
  `inj` at the sorts of a subsort pair, with no implementation. So that leaf (no instance name has
  the head `inj`) cannot be left out of `coreOK`.

  `Γ` writes the instance as the head `inj` applied to the sorts `SortKCell` and `SortKCellOpt`
  (`symApp`), which is how a value writes the injection from `KCell` to `KCellOpt`
  (`GroundTerm.kore`): the parameter's application to the cell `<k> .K </k>` and the value that
  injects that cell are one pattern (`app_eq_inj`). The parameter has no implementation, so its graph
  (`ΓDomains`) says that pattern is ⊥, and the value denotes an element. The first, second and
  fourth leaves of `itesApart` hold (`leaves_124`). The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace InstInjWitness

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

/-- `inj{KCell,KCellOpt}`, from `KCell` to `KCellOpt`, with no implementation. -/
def p : ParamSig := { sig := ⟨nRegSyms + 4, [nRegSorts], nRegSorts + 1⟩ }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "inj{KCell,KCellOpt}"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [p] }

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

/-- The first, second and fourth leaves of `itesApart` hold of every symbol with a signature: the
one instance name is at the numbered sorts `KCell` and `KCellOpt`, the one instance of its head, and
no symbol is plainly named `inj`. -/
theorem leaves_124 : ((kernelSyms c).all fun k =>
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
      | some (h, _) => (kernelSyms c).all fun k' => !k'.args.isEmpty || c.symName k'.name != h
      | none => true)) = true := by decide +kernel

/-- `itesApart` fails, at its third leaf: the parameter is an instance of the head `inj`. -/
theorem not_itesApart : Model.itesApart c = false := by decide +kernel

theorem p_inst : instDecode? (c.symName p.sig.name) = some ("inj", ["KCell", "KCellOpt"]) := by decide +kernel

/-- The cell `<k> .K </k>`, a value of `KCell`, and its injection into `KCellOpt`. -/
def w : GroundTerm := .ctor (nRegSyms + 2) [.ctor dotk []]
def wi : GroundTerm := .inj nRegSorts (nRegSorts + 1) w

theorem wi_sort : c.sortOf wi = some (nRegSorts + 1) := by decide +kernel
theorem args_sort : c.sortsOf [w] = some p.sig.args := by decide +kernel
theorem p_val : c.paramVal p.sig.name [w] = none := by decide +kernel

/-- The parameter applied to the cell is written as the injection of the cell is. -/
theorem app_eq_inj : symApp c p.sig.name (GroundTerm.koreList c [w]) = GroundTerm.kore c wi := by
  rw [symApp_inst p_inst]
  simp only [wi, GroundTerm.kore, GroundTerm.koreList, KoreAML.injP, List.map]
  decide +kernel

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  -- the parameter's graph: `inj SortKCell SortKCellOpt (<k> .K </k>)` is ⊥
  have hax := sat_dom hI (Or.inr (Or.inl ⟨p, [w], List.mem_cons_self .., args_sort, rfl⟩))
  simp only [p_val] at hax
  have h0 := (KoreAML.interp_equal hD).mp (hax KoreAML.val0 default)
  -- the injected cell denotes an element, and is that pattern
  have hv := (elemOf_spec hI wi_sort KoreAML.val0).1
  have hm : (den c wi).interpret I KoreAML.val0 (elemOf c I wi) := (hv _).mpr rfl
  have hc0 : (KoreAML.den (symApp c p.sig.name (GroundTerm.koreList c [w]))).interpret I KoreAML.val0
      (elemOf c I wi) := by
    rw [app_eq_inj]; exact hm
  exact (h0 _).mp hc0

end InstInjWitness

end Faithful

end KCore
