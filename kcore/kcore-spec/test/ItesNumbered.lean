/-
  The first half of `itesApart` (every symbol named like `ite` is named at a numbered sort): no
  witness was found, that is, no semantics that meets every other condition of `coreOK` and
  `FnHyp`, fails only that half, and whose `Γ` has no model. Run from the package root:
  `lake env lean -j1 test/ItesNumbered.lean`.

  Kernel-checked here:
  - `itesApart_split`: `itesApart` is the conjunction of its two halves, `itesNumbered` (the first)
    and `itesOnce` (no two at one sort), for every semantics.
  - `iteNamed_param`: under `namesNumbered` and `overloadsOK`, a symbol of `kernelSyms` named like
    `ite` at a sort is a parameter: `namesNumbered` excludes the constructors and functions,
    `overloadsOK` the overloading symbols, and no interpreted hook is so named (`hooks_plain`).
  - `c`, one parameter `Lblite{Foo}` (`ite` at `Foo`, which names no sort), implemented by `_+Int_`:
    every other condition of `coreOK` and `FnHyp` hold (`meets_others`), `itesOnce` holds and
    `itesNumbered` does not (`not_itesNumbered`). So the first half is not implied by the others.
  - `graph_head`: `Γ`'s graph of the parameter (`ΓDomains`, through `symApp`) is about `Lblite`
    applied to the sort symbol `SortFoo`; `foo_unnamed`: no numbered sort is named `Foo`.

  Argued, not kernel-checked: `Γ` of such a semantics has a model. The only symbols named like
  `ite` at an unnumbered X are parameters (`iteNamed_param`), and `Γ` writes each application of
  one as `Lblite ⬝ SortX ⬝ …` (`symApp`, `symArityItem`, `Term.kore`). The sort symbol `SortX` occurs
  in `Γ` nowhere else: the signature names the sort symbols of the numbered sorts only
  (`sigItems`, `sortConstantItem` over `kernelSorts`); every other sort `Γ` writes is
  `sortName` of a numbered sort (`srtOf`, `sortP`), or the fixed `Bool` of `reqPat`;
  `dvArityItem` quantifies over the elements of `⟦Sort⟧` (`sortGuard`), not over names; and the sort
  of sorts is the constructor `Sym.sortSort`, not a `Sym.sort` name. So `Lblite ⬝ SortX` is
  constrained only by the parameter's own arity and graph, which a fresh head satisfies (the
  graph's value lies in the result sort by `paramVal`'s implementation, and an undefined point
  has the graph `⊥`). The registry's `Lblite` (`kIte`, without a sort in its name) is applied to a
  Bool's element first, and nothing equates `SortX` with one. A model of the same semantics
  with the parameter renamed plainly (which meets `coreOK`) therefore gives one of `Γ`, with
  `Lblite ⬝ SortX` read as the renamed symbol on a fresh element for `SortX`; building it in the
  kernel is the canonical model's construction (`stdI`) without `HypModelCore.ites`. That
  construction reads the first half only through `HypModelCore.iteSorted` (ModelDomains.lean),
  used in ModelDomains.lean and ModelAtT.lean (`find_ite`, ModelSig.lean, reads the second half).
  Its interpretation sends a sort symbol of no numbered sort to nothing (`evalSymb` at `.sort n`:
  `sortOfName`), so there `Lblite ⬝ SortX ⬝ …` is empty and a defined graph would be false of
  `stdI`. The `itesApart` docstring's reason ("would leave a parameter's graph without an
  element") is about `stdI`, not about every model.

  The step is unaffected as well: a rule's or clause's application of the parameter is written
  with the same head as its graph (`Term.kore` and `symApp` both apply `Lblite` to `SortX`), so an
  entailed value of the application is the parameter's value.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.ItesNumbered

open ML

/-- The first half of `itesApart`: every symbol named like `ite` is named at a numbered sort. -/
def itesNumbered (c : Semantics) : Bool :=
  (kernelSyms c).all fun k =>
    match iteSort? (c.symName k.name) with
    | some X => (kernelSorts c).any fun s => c.sortName s == X
    | none => true

/-- The second half of `itesApart`: no two symbols are named like `ite` at one sort. -/
def itesOnce (c : Semantics) : Bool :=
  (kernelSyms c).all fun k => (kernelSyms c).all fun k' =>
    (iteSort? (c.symName k.name)).isNone || iteSort? (c.symName k.name) != iteSort? (c.symName k'.name) || k == k'

/-- `itesOnce` from its pairs among the entries of `kernelSyms` that may be named like `ite`
(`iteSyms`, the entries whose name's code is listed by `iteIdx`): an entry not among them is named
like `ite` at no sort. -/
theorem itesOnce_of_codesX8 {c : Semantics} {sym : List Nat}
    (hc : (allSymNames c).map KoreAML.Distinct.strCode = sym)
    (h : (Model.iteSyms c (iteIdx sym)).all (fun k => (Model.iteSyms c (iteIdx sym)).all fun k' =>
      (iteSort? (c.symName k.name)).isNone || iteSort? (c.symName k.name) != iteSort? (c.symName k'.name) ||
        k == k') = true) :
    itesOnce c = true := by
  simp only [List.all_eq_true] at h
  have hmem : ∀ k ∈ kernelSyms c, iteSort? (c.symName k.name) ≠ none → k ∈ Model.iteSyms c (iteIdx sym) :=
    fun k hk hn => List.mem_filter.mpr ⟨hk, by simpa using mem_iteIdx hc hn⟩
  simp only [itesOnce, List.all_eq_true]
  intro k hk k' hk'
  by_cases hn : iteSort? (c.symName k.name) = none
  · simp [hn]
  by_cases hn' : iteSort? (c.symName k'.name) = none
  · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, hn', beq_iff_eq]
    exact Or.inl (Or.inr hn)
  · exact h k (hmem k hk hn) k' (hmem k' hk' hn')

/-- `itesApart` is its two halves. -/
theorem itesApart_split (c : Semantics) : Model.itesApart c = (itesNumbered c && itesOnce c) := by
  rw [Bool.eq_iff_iff]
  simp only [Model.itesApart, itesNumbered, itesOnce, List.all_eq_true, Bool.and_eq_true]
  exact ⟨fun h => ⟨fun k hk => (h k hk).1, fun k hk => (h k hk).2⟩,
    fun h k hk => ⟨h.1 k hk, h.2 k hk⟩⟩

/-- No interpreted hook is named like `ite` at a sort: their names are the registry's. -/
theorem hooks_plain_dec :
    hookSigs.all (fun k => decide (k.name < nRegSyms) && (iteSort? (regSymNames.getD k.name "")).isNone) = true := by
  decide_cheap 20

theorem hooks_plain (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) : iteSort? (c.symName k.name) = none := by
  have h := List.all_eq_true.mp hooks_plain_dec k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  unfold Semantics.symName
  simp only [h.1, ↓reduceIte]
  exact h.2

/-- **Under `namesNumbered` and `overloadsOK`, a symbol named like `ite` at a sort is a
parameter.** -/
theorem iteNamed_param {c : Semantics} (hn : namesNumbered c = true) (ho : c.overloadsOK = true)
    {k : CtorSig} (hk : k ∈ kernelSyms c) {X : String} (hi : iteSort? (c.symName k.name) = some X) :
    k ∈ c.params.map (·.sig) := by
  simp only [namesNumbered, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at hn
  obtain ⟨⟨hctor, hfn⟩, -⟩ := hn
  unfold kernelSyms at hk
  simp only [List.mem_append] at hk
  rcases hk with (((hk | hk) | hk) | hk) | hk
  · rw [hctor k hk] at hi; cases hi
  · obtain ⟨fn, hfn', rfl⟩ := List.mem_map.mp hk
    have := hfn fn hfn'
    simp only [Fn.sig] at hi
    rw [this] at hi; cases hi
  · exact hk
  · rw [hooks_plain c hk] at hi; cases hi
  · obtain ⟨o, hmem, rfl⟩ := List.mem_map.mp hk
    obtain ⟨i, hlt, he⟩ := List.getElem_of_mem hmem
    simp only [Semantics.overloadsOK, Bool.and_eq_true] at ho
    replace ho := ho.1; simp only [List.all_eq_true] at ho
    have hoi := ho (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hlt] using he)
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hoi
    rw [hoi.1.1.1.1.1.2] at hi; cases hi

/-! ## A semantics that fails the first half only -/

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 2, no := some (nRegSyms + 3) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- `Lblite{Foo}`, two Ints to an Int, implemented by `_+Int_`. -/
def p : ParamSig := { sig := ⟨nRegSyms + 4, [Srt.int, Srt.int], Srt.int⟩, impl := some intAdd }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblite{Foo}"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [p] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide_cheap

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

/-- Every condition of `coreOK` but `itesApart` holds, the second half of `itesApart` holds, and
`FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.kindsApart c = true ∧ Model.ctorsOnce c = true ∧
    Model.fnsApart c = true ∧ itesOnce c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, itesOnce_of_codesX8 (symCodesCD_eq c) (by decide +kernel), fnHyp⟩

/-- The first half of `itesApart` fails. -/
theorem not_itesNumbered : itesNumbered c = false := by decide +kernel

theorem not_itesApart : Model.itesApart c = false := by
  rw [itesApart_split, not_itesNumbered, Bool.false_and]

theorem ite_p : iteSort? (c.symName p.sig.name) = some "Foo" := by decide +kernel

/-- No numbered sort is named `Foo`. -/
theorem foo_unnamed : (kernelSorts c).all (fun s => c.sortName s != "Foo") = true := by decide +kernel

/-- `Γ` writes an application of the parameter as `Lblite` applied to the sort symbol `SortFoo`. -/
theorem graph_head (args : List Kore.Pattern) :
    symApp c p.sig.name args = .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "Foo"] args := by
  unfold symApp; rw [ite_p]

end KCore.Faithful.ItesNumbered
