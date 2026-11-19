/-
  The first leaf of `itesApart` (every sort name of an instance name names a numbered sort): no
  witness was found, that is, no semantics that meets every other condition of `coreOK` and
  `FnHyp`, fails only that leaf, and whose `Γ` has no model. Run from the package root:
  `lake env lean -j1 test/ItesNumbered.lean`.

  Kernel-checked here:
  - `itesApart_split`: `itesApart` is the conjunction of its three leaves, `itesNumbered` (the
    first), `itesArity` (one number of sorts per head) and `itesNotInj` (no head `inj`), for every
    semantics.
  - `instNamed_param`: under `namesNumbered` and `overloadsOK`, a symbol of `kernelSyms` whose name
    the decoder reads as an instance (`instDecode?`) is a parameter or a function: `namesNumbered`
    excludes the constructors, `overloadsOK` the overloading symbols, and no interpreted hook is so
    named (`hooks_plain`).
  - `c`, one parameter `Lblite{Foo}` (`ite` at `Foo`, which names no sort), implemented by `_+Int_`:
    every other condition of `coreOK` and `FnHyp` hold (`meets_others`), `itesArity` and
    `itesNotInj` hold and `itesNumbered` does not (`not_itesNumbered`). So the first leaf is not
    implied by the others.
  - `graph_head`: `Γ`'s graph of the parameter (`ΓDomains`, through `symApp`) is about `Lblite`
    applied to the sort symbol `SortFoo`; `foo_unnamed`: no numbered sort is named `Foo`.

  Argued, not kernel-checked, for a semantics whose symbols named like `ite` at an unnumbered X
  are parameters (`instNamed_param` leaves parameters and functions; a function so named, whose
  equations `Γ` writes at the same head, is not examined here): `Γ` of such a semantics has a model.
  `Γ` writes each application of such a parameter as `Lblite ⬝ SortX ⬝ …` (`symApp`, `symArityItem`,
  `Term.kore`). The sort symbol `SortX` occurs
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
  construction reads the leaf only through `HypModelCore.iteSorted` (ModelDomains.lean),
  used in ModelDomains.lean and ModelAtT.lean. Its interpretation sends a sort symbol of no
  numbered sort to nothing (`evalSymb` at `.sort n`: `sortOfName`), so there
  `Lblite ⬝ SortX ⬝ …` is empty and a defined graph would be false of `stdI`. The `itesApart`
  docstring's reason ("would leave the instance's graph without an element") is about `stdI`,
  not about every model. An instance name at a head other than `Lblite`, or at several sorts, is
  written plainly by `symApp`, so a semantics failing a leaf only there has the model of the
  same semantics with that symbol renamed.

  The step is unaffected as well: a rule's or clause's application of the parameter is written
  with the same head as its graph (`Term.kore` and `symApp` both apply `Lblite` to `SortX`), so an
  entailed value of the application is the parameter's value.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.ItesNumbered

open ML

/-- The first leaf of `itesApart`: every sort name of an instance name names a numbered sort. -/
def itesNumbered (c : Semantics) : Bool :=
  (kernelSyms c).all fun k =>
    match instDecode? (c.symName k.name) with
    | some (_, xs) => xs.all fun x => (kernelSorts c).any fun s => c.sortName s == x
    | none => true

/-- The second leaf of `itesApart`: all instance names of one head are at one number of sorts. -/
def itesArity (c : Semantics) : Bool :=
  (kernelSyms c).all fun k =>
    match instDecode? (c.symName k.name) with
    | some (h, xs) => (kernelSyms c).all fun k' =>
        match instDecode? (c.symName k'.name) with
        | some (h', xs') => h' != h || xs'.length == xs.length
        | none => true
    | none => true

/-- The third leaf of `itesApart`: no instance name has the head `inj`. -/
def itesNotInj (c : Semantics) : Bool :=
  (kernelSyms c).all fun k =>
    match instDecode? (c.symName k.name) with
    | some (h, _) => h != "inj"
    | none => true

/-- `itesApart` is its three leaves. -/
theorem itesApart_split (c : Semantics) :
    Model.itesApart c = (itesNumbered c && itesArity c && itesNotInj c) := by
  rw [Bool.eq_iff_iff]
  simp only [Model.itesApart, itesNumbered, itesArity, itesNotInj, List.all_eq_true, Bool.and_eq_true]
  exact ⟨fun h => ⟨⟨fun k hk => (h k hk).1.1, fun k hk => (h k hk).1.2⟩, fun k hk => (h k hk).2⟩,
    fun h k hk => ⟨⟨h.1.1 k hk, h.1.2 k hk⟩, h.2 k hk⟩⟩

/-- No interpreted hook is named like an instance: their names are the registry's. -/
theorem hooks_plain_dec :
    hookSigs.all (fun k => decide (k.name < nRegSyms) && (instDecode? (regSymNames.getD k.name "")).isNone) = true := by
  decide_cheap 20

theorem hooks_plain (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) : instDecode? (c.symName k.name) = none := by
  have h := List.all_eq_true.mp hooks_plain_dec k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  unfold Semantics.symName
  simp only [h.1, ↓reduceIte]
  exact h.2

/-- **Under `namesNumbered` and `overloadsOK`, a symbol named like an instance is a parameter or
a function.** -/
theorem instNamed_param {c : Semantics} (hn : namesNumbered c = true) (ho : c.overloadsOK = true)
    {k : CtorSig} (hk : k ∈ kernelSyms c) {p : String × List String} (hi : instDecode? (c.symName k.name) = some p) :
    k ∈ c.params.map (·.sig) ∨ k ∈ c.allFns.map (·.sig) := by
  simp only [namesNumbered, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at hn
  obtain ⟨⟨hctor, -⟩, -⟩ := hn
  unfold kernelSyms at hk
  simp only [List.mem_append] at hk
  rcases hk with (((hk | hk) | hk) | hk) | hk
  · rw [hctor k hk] at hi; cases hi
  · exact .inr hk
  · exact .inl hk
  · rw [hooks_plain c hk] at hi; cases hi
  · obtain ⟨o, hmem, rfl⟩ := List.mem_map.mp hk
    obtain ⟨i, hlt, he⟩ := List.getElem_of_mem hmem
    simp only [Semantics.overloadsOK, Bool.and_eq_true] at ho
    replace ho := ho.1; simp only [List.all_eq_true] at ho
    have hoi := ho (o, i) (by simpa [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hlt] using he)
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hoi
    rw [hoi.1.1.1.1.1.1.2] at hi; cases hi

/-! ## A semantics that fails the first leaf only -/

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

set_option maxHeartbeats 2000000 in
/-- Every condition of `coreOK` but `itesApart` holds, the second and third leaves of `itesApart`
hold, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.kindsApart c = true ∧ Model.ctorsOnce c = true ∧
    Model.fnsApart c = true ∧ itesArity c = true ∧ itesNotInj c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

/-- The first leaf of `itesApart` fails. -/
theorem not_itesNumbered : itesNumbered c = false := by decide +kernel

theorem not_itesApart : Model.itesApart c = false := by
  rw [itesApart_split, not_itesNumbered, Bool.false_and, Bool.false_and]

theorem ite_p : iteSort? (c.symName p.sig.name) = some "Foo" := by decide +kernel

/-- No numbered sort is named `Foo`. -/
theorem foo_unnamed : (kernelSorts c).all (fun s => c.sortName s != "Foo") = true := by decide +kernel

/-- `Γ` writes an application of the parameter as `Lblite` applied to the sort symbol `SortFoo`. -/
theorem graph_head (args : List Kore.Pattern) :
    symApp c p.sig.name args = .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "Foo"] args := by
  unfold symApp; rw [ite_p]

end KCore.Faithful.ItesNumbered
