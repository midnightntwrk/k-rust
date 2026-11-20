/-
  The first leaf of `itesApart` (every sort name of an instance name names a numbered sort): no
  witness was found, that is, no semantics that meets every other condition of `coreOK` and
  `FnHyp`, fails only that leaf, and whose `Γ` has no model. The second, third and fourth leaves
  have one each (KcoreSpec/ModelInstArityWitness.lean, ModelInstInjWitness.lean,
  ModelInstConstWitness.lean). Run from the package root:
  `lake env lean -j1 test/ItesNumbered.lean`.

  Kernel-checked here:
  - `itesApart_split`: `itesApart` is the conjunction of its four leaves, `itesNumbered` (the
    first), `itesArity` (one number of sorts per head), `itesNotInj` (no head `inj`) and
    `itesConstApart` (no constant plainly named by a head), for every semantics.
  - `instNamed_param`: under `namesNumbered` and `overloadsOK`, a symbol of `kernelSyms` whose name
    the decoder reads as an instance (`instDecode?`) is a parameter or a function: `namesNumbered`
    excludes the constructors, `overloadsOK` the overloading symbols, and no interpreted hook is so
    named (`hooks_plain`).
  - `c`, one parameter `Lblite{Foo}` (`ite` at `Foo`, which names no sort), implemented by `_+Int_`:
    every other condition of `coreOK` and `FnHyp` hold (`meets_others`), `itesArity`,
    `itesNotInj` and `itesConstApart` hold and `itesNumbered` does not (`not_itesNumbered`). So the first leaf is not
    implied by the others.
  - `graph_head`: `Γ`'s graph of the parameter (`ΓDomains`, through `symApp`) is about `Lblite`
    applied to the sort symbol `SortFoo`; `foo_unnamed`: no numbered sort is named `Foo`.
  - `c3`: `c` with `Foo` an own sort of no constructor (its name and its predicate's name added,
    the later symbols numbered one further). It meets `coreOK` (`c3_core`) and `FnHyp`, its value
    model is a model of its theory (`model3`), and it writes the parameter's applications as `c`
    does (`c3_graph_head`).

  Argued, not kernel-checked: `Γ c` has a model, the value model of `c3`. `Γ` names a semantics'
  sorts and symbols by their names, and those of `c` keep their names in `c3`. Reading `sigItems`,
  `consItemsK`, `fnItems`, `ΓDomains` and `ΓFallback`: `Γ c3` holds the items of `Γ c` but KItem's
  no-junk item, and besides them the items of `Foo` (its sort constant, its predicate's arity,
  equations and graphs, and its injection into KItem as a generator). KItem's no-junk item in
  `Γ c3` has one more disjunct than in `Γ c`, the injection of an element of `Foo`; `Foo` has no
  value, so the value model of `c3` holds no element of it, and there the two items hold of the
  same elements. For a semantics failing the leaf alone at another head, at several sorts, or with
  a function so named, the same construction is the argument (each sort name that names no sort
  made an own sort of no constructor); nothing of it is kernel-checked beyond `c3`.
  The value model of `c` itself is none: it sends a sort symbol of no numbered sort to nothing
  (`evalSymb` at `.sort n`: `sortOfName`), so an instance's application at such a sort is empty
  there and a defined graph is false. The model construction reads the leaf for that reason
  (`instSorts_numbered` in ModelSig.lean, `HypModelCore.iteSorted` in ModelDomains.lean); the
  `itesApart` docstring's "would leave the instance's graph without an element" is about that
  interpretation, not about every model.

  The step is unaffected as well: a rule's or clause's application of the parameter is written
  with the same head and sorts as its graph (`Term.kore` and `symApp`), so an entailed value of the
  application is the parameter's value.
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

/-- The fourth leaf of `itesApart`: no symbol of no arguments is plainly named by the head of an
instance name. -/
def itesConstApart (c : Semantics) : Bool :=
  (kernelSyms c).all fun k =>
    match instDecode? (c.symName k.name) with
    | some (h, _) => (kernelSyms c).all fun k' => !k'.args.isEmpty || c.symName k'.name != h
    | none => true

/-- `itesApart` is its four leaves. -/
theorem itesApart_split (c : Semantics) :
    Model.itesApart c = (itesNumbered c && itesArity c && itesNotInj c && itesConstApart c) := by
  rw [Bool.eq_iff_iff]
  simp only [Model.itesApart, itesNumbered, itesArity, itesNotInj, itesConstApart, List.all_eq_true,
    Bool.and_eq_true]
  exact ⟨fun h => ⟨⟨⟨fun k hk => (h k hk).1.1.1, fun k hk => (h k hk).1.1.2⟩, fun k hk => (h k hk).1.2⟩,
      fun k hk => (h k hk).2⟩,
    fun h k hk => ⟨⟨⟨h.1.1.1 k hk, h.1.1.2 k hk⟩, h.1.2 k hk⟩, h.2 k hk⟩⟩

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
    rw [hoi.1.1.1.1.1.2] at hi; cases hi

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
/-- Every condition of `coreOK` but `itesApart` holds, the second, third and fourth leaves of
`itesApart` hold, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.kindsApart c = true ∧ Model.ctorsOnce c = true ∧
    Model.fnsApart c = true ∧ itesArity c = true ∧ itesNotInj c = true ∧ itesConstApart c = true ∧
    FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

/-- The first leaf of `itesApart` fails. -/
theorem not_itesNumbered : itesNumbered c = false := by decide +kernel

theorem not_itesApart : Model.itesApart c = false := by
  rw [itesApart_split, not_itesNumbered, Bool.false_and, Bool.false_and, Bool.false_and]

theorem ite_p : instDecode? (c.symName p.sig.name) = some ("Lblite", ["Foo"]) := by decide +kernel

/-- No numbered sort is named `Foo`. -/
theorem foo_unnamed : (kernelSorts c).all (fun s => c.sortName s != "Foo") = true := by decide +kernel

/-- `Γ` writes an application of the parameter as `Lblite` applied to the sort symbol `SortFoo`. -/
theorem graph_head (args : List Kore.Pattern) :
    symApp c p.sig.name args = .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "Foo"] args :=
  symApp_inst ite_p

/-! ## The same semantics with `Foo` numbered -/

section Numbered

open Model

/-- `c` with `Foo` an own sort of no constructor: its name after the two cell sorts', its predicate's
name after theirs, and the symbols after the predicates numbered one further. -/
def c3 : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "Foo"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisFoo", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblite{Foo}"]
    userSorts := cellSorts ++ [nRegSorts + 2]
    ctors :=
      [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
       ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
       ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [{ sig := ⟨nRegSyms + 5, [Srt.int, Srt.int], Srt.int⟩, impl := some intAdd }] }

theorem c3_core : c3.coreOK = true := by decide_cheap

theorem c3_fnHyp : FnHyp c3 :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

theorem c3_ite : instDecode? (c3.symName (nRegSyms + 5)) = some ("Lblite", ["Foo"]) := by decide +kernel

/-- `c3` writes the parameter as `c` does, at the head `Lblite` and the sort `SortFoo`. -/
theorem c3_graph_head (args : List Kore.Pattern) :
    symApp c3 (nRegSyms + 5) args = .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "Foo"] args :=
  symApp_inst c3_ite

/-- The value model of `c3` is a model of its theory. -/
theorem model3 : stdI c3 ⊧ᴵP (Γc c3 ∪ Γstep c3) :=
  stdI_modelOpen c3 c3_core
    (hypModel_of_fn c3_core (fnModel_of_fnHyp c3_core c3_fnHyp).1 (fnModel_of_fnHyp c3_core c3_fnHyp).2)
    c3_fnHyp.2.2.2.2.2 (fun _ h => absurd h List.not_mem_nil)
    (satFnsGoal_decided
      (hypModel_of_fn c3_core (fnModel_of_fnHyp c3_core c3_fnHyp).1 (fnModel_of_fnHyp c3_core c3_fnHyp).2)
      (Semantics.fnsNoExs_of_all (by decide +kernel)) (clausePreDecided_of_fnHyp c3_core c3_fnHyp))

end Numbered

end KCore.Faithful.ItesNumbered
