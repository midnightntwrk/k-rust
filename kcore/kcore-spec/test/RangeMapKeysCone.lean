/-
  What interpreting RANGEMAP's `keys` (`rmKeys`, `rmKeysHook`) changes in what `coreOK` and
  `srReady` accept. Run from the package root: `lake env lean -j1 test/RangeMapKeysCone.lean`.
  Kernel-checked (`decide +kernel`, `rfl`).

  ## The tables

  `hookSigs` holds fifteen range-map rows, the last `keys : RangeMap → Set`; `hookTable` holds the
  fourteen of `rangeMapHooks` and then `rangeMapKeysHooks`' one, `(rmKeys, rmKeysHook)`; the two
  tables name the same symbols in one order (`tables`).

  ## What `srReady` newly refuses, and `coreOK` does not

  `srReady` holds `rangeKeysOK`: Range is below KItem, or `rangeCtor` is no constructor and no
  overloading symbol of result sort Range. So it refuses the semantics where `rangeCtor` is a
  constructor or overloading symbol of result Range and Range is not below KItem, whether a range
  term has that sort (`cx`) or none has (`cy`: the constructor takes one Bool, no range term is
  its application). `rangeKeysOK` is strictly stronger than `RangeBelow`, which is what `keys`'
  value needs (every range term of sort Range is a KItem): `cy` has `RangeBelow` and not
  `rangeKeysOK` (`cy_below`, `refused`).
  `coreOK` refuses none of them newly: it gives `rangeKeysOK` (`rangeKeysOK_of_core`), and both
  instances fail `genWf`, a conjunct of `faithCoreOK` (`refused`). With Range below KItem (`c1`)
  and with no Range constructor (`c0`), `coreOK` and `srReady` hold (`accepted`).

  ## `hooksApart` at the fifteenth row

  `hooksApart` asks that no constructor and no function of the semantics is numbered as a row of
  `hookSigs`, now `rmKeys` among them. `idsOK` already leaves none numbered `rmKeys`
  (`ids_not_rmKeys`: an own constructor is numbered `nRegSyms` or above or in `genSyms`, a
  function from `symBase`, and `rmKeys` is a registry number outside `genSyms`). So a semantics
  `idsOK` accepts meets `hooksApart` exactly where it meets `hooksApart` without the row
  (`hooksApart_row`): the row refuses nothing `coreOK` accepted.

  ## A parameter row numbered `rmKeys`

  `kindsApart`, a conjunct of `faithCoreOK`, asks that no parameter is an interpreted hook. `rmKeys`
  is one (`isHook`), so `coreOK` refuses every semantics whose `params` hold a row numbered
  `rmKeys` (`param_rmKeys`), as it refuses a row numbered as any other row of `hookSigs`; `cp`,
  `c1` with the row `keys : RangeMap → Set`, is such a semantics (`param_row`). The reader puts
  no such row in a definition it builds: the imported modules' parameters it lists leave out
  every row of `hookSigs` (`libParams_not_rmKeys`).

  ## Kernel-checked

  Each fact is a kernel decision or a proof from one; `coreOK` of `c1`, `c0` is decided
  conjunct by conjunct with `itesApart` on the names' codes (`rmkCoreOK`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RangeMapKeysCone

open KCore Faithful

/-! ## The tables -/

/-- The fifteen range-map rows of `hookSigs`, `keys` the last; `hookTable` ends with the fourteen
of `rangeMapHooks` and `rangeMapKeysHooks`' one; the two tables name the same symbols in order. -/
theorem tables :
    (hookSigs.filter fun k => k.args.contains Srt.rangeMap || k.result == Srt.rangeMap).length = 15 ∧
    hookSigs.getLast? = some ⟨rmKeys, [Srt.rangeMap], Srt.set⟩ ∧
    rangeMapHooks.length = 14 ∧ rangeMapKeysHooks.map (·.1) = [rmKeys] ∧
    (hookTable.map (·.1)).getLast? = some rmKeys ∧
    hookTable.map (·.1) = hookSigs.map (·.name) := by
  decide +kernel

/-! ## What `srReady` newly refuses -/

/-- `rangeCtor` a library constructor of result Range, Range not below KItem: a range term has
sort Range. -/
def cx : Semantics :=
  { sortNames := [], symNames := [], userSorts := [], ctors := [], fns := [], userSubsorts := [],
    pgmSort := Srt.int, rules := []
    lib := { sortsBelowKItem := [Srt.int], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] } }

/-- The same with the constructor taking one Bool: no range term is its application. -/
def cy : Semantics :=
  { cx with lib := { sortsBelowKItem := [Srt.int], ctors := [⟨rangeCtor, [Srt.bool], Srt.range⟩] } }

/-- Range below KItem. -/
def c1 : Semantics :=
  { cx with pgmSort := Srt.k
            lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] } }

/-- No Range constructor. -/
def c0 : Semantics := { cx with pgmSort := Srt.k, lib := { sortsBelowKItem := [Srt.int] } }

/-- Both refused instances: `rangeKeysOK` and `srReady` false, the other two conjuncts of
`srReady` true; `genWf` false, so `coreOK` was false of them before `srReady` read `rangeKeysOK`.
A range term has sort Range in `cx`. -/
theorem refused :
    cx.rangeKeysOK = false ∧ cx.srReady = false ∧ cx.predsApart = true ∧ cx.idsOK = true ∧
    genWf cx = false ∧ cx.faithCoreOK = false ∧ cx.coreOK = false ∧
    cx.sortOf (rangeT 0 1) = some Srt.range ∧
    cy.rangeKeysOK = false ∧ cy.srReady = false ∧ cy.predsApart = true ∧ cy.idsOK = true ∧
    genWf cy = false ∧ cy.faithCoreOK = false ∧ cy.coreOK = false := by
  decide +kernel

/-- `cx` has a Range value that is no KItem. -/
theorem cx_not_below : ¬ RangeBelow cx :=
  fun h => absurd (h 0 1 (by decide +kernel)) (by decide +kernel)

/-- `cy` has no range term of sort Range, so `RangeBelow` holds of it though `rangeKeysOK` does
not: the decided form is strictly stronger. -/
theorem cy_below : RangeBelow cy := by
  intro a b hs
  exfalso
  have hk' : lookupSig cy.ctorSigs rangeCtor = some ⟨rangeCtor, [Srt.bool], Srt.range⟩ := by decide +kernel
  rcases cy.sortOf_ctor_iff.mp hs with ⟨k, hk, hargs, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · rw [hk'] at hk; cases hk
    have := sortsOf_length hargs
    simp at this
  · rw [hk'] at hn; cases hn
  · rw [hk'] at hn; cases hn

/-- `coreOK` gives `rangeKeysOK`: the conjunct refuses no semantics `coreOK` accepts. -/
example (c : Semantics) (h : c.coreOK = true) : c.rangeKeysOK = true := rangeKeysOK_of_core h

open Faithful.Model in
/-- `coreOK` from its conjuncts, `itesApart` decided on the names' codes (`itesApart_of_codes`): a
direct decision of `itesApart` compares every pair of symbols' names, the interpreted ones among
them. -/
theorem rmkCoreOK {c : Semantics} {I : List Nat} (hI : instIdx ((allSymNames c).map KoreAML.Distinct.strCode) = I)
    (hite : itesApartC c I ((allSymNames c).map KoreAML.Distinct.strCode)
      ((allSortNames c).map KoreAML.Distinct.strCode) = true) (hs : c.sortedOK = true)
    (h1 : namesNumbered c = true) (h2 : genWf c = true) (h3 : collSortsOK c = true)
    (h4 : collsOK c = true) (h5 : patHeadsOK c = true) (h6 : namesApartK c = true)
    (h7 : LitsApart c = true) (h8 : sortsNumbered c = true) (h11 : kindsApart c = true)
    (h12 : ctorsOnce c = true) (h13 : fnsApart c = true) (hha : c.hooksApart = true)
    (hpa : c.predsApart = true) (hids : c.idsOK = true) (hov : c.overloadsOK = true) :
    c.coreOK = true := by
  have hfa := Semantics.faithCoreOK_of_partsK h1 h2 h3 h4 h5 h6 h7 h8
    (itesApart_of_codes rfl rfl hI hite) h11 h12 h13
  simp only [Semantics.coreOK, hs, hfa, hha, hpa, hids, hov, Bool.and_self]

set_option maxHeartbeats 4000000 in
theorem c1_coreOK : c1.coreOK = true :=
  rmkCoreOK (I := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem c0_coreOK : c0.coreOK = true :=
  rmkCoreOK (I := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- With Range below KItem, and with no Range constructor, `coreOK` and `srReady` hold. -/
theorem accepted : c1.coreOK = true ∧ c1.srReady = true ∧ c1.sortOf (rangeT 0 3) = some Srt.range ∧
    c0.coreOK = true ∧ c0.srReady = true ∧ c0.subsorts.contains (Srt.range, Srt.kitem) = false :=
  ⟨c1_coreOK, by decide_cheap, by decide_cheap, c0_coreOK, by decide_cheap, by decide_cheap⟩

/-! ## `hooksApart` at the fifteenth row -/

theorem rmKeys_reg : rmKeys < nRegSyms ∧ genSyms.contains rmKeys = false := by decide +kernel

/-- `idsOK` leaves no own constructor and no function numbered `rmKeys`. -/
theorem ids_not_rmKeys {c : Semantics} (hids : c.idsOK = true) :
    (∀ k ∈ c.ctors, k.name ≠ rmKeys) ∧ (∀ f ∈ c.fns, f.label ≠ rmKeys) := by
  unfold Semantics.idsOK at hids
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hids
  obtain ⟨⟨-, -, hfns⟩, ⟨-, hct⟩, -⟩ := hids
  refine ⟨fun k hk he => ?_, fun f hf he => ?_⟩
  · rcases hct k hk with h | h
    · rw [he] at h; exact absurd h (by decide)
    · rw [he] at h; exact absurd h (by decide)
  · have h3 : rmKeys < nRegSyms := rmKeys_reg.1
    have h4 : f.label < nRegSyms := he ▸ h3
    exact absurd (hfns f hf) (Nat.not_le.mpr h4)

/-- `hooksApart` over the rows of `hookSigs` but `keys`'. -/
def hooksApartLess (c : Semantics) : Bool :=
  let sigs := hookSigs.filter (·.name != rmKeys)
  c.ctors.all (fun k => !sigs.any (·.name == k.name)) && c.fns.all (fun f => !sigs.any (·.name == f.label))

/-- A symbol other than `rmKeys` is a row of `hookSigs` exactly where it is one of the others. -/
theorem any_less {n : Sym} (h : n ≠ rmKeys) :
    (hookSigs.filter (·.name != rmKeys)).any (·.name == n) = hookSigs.any (·.name == n) := by
  rw [List.any_filter]
  congr 1
  funext k
  by_cases hk : k.name = n
  · simp [hk, h]
  · simp [hk]

/-- `List.all` of two tests that agree on the members of the list. -/
theorem rmkAllCongr {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **Under `idsOK` the row of `keys` refuses nothing**: `hooksApart` is `hooksApart` without it. -/
theorem hooksApart_row {c : Semantics} (hids : c.idsOK = true) : c.hooksApart = hooksApartLess c := by
  obtain ⟨hc, hf⟩ := ids_not_rmKeys hids
  unfold Semantics.hooksApart hooksApartLess
  rw [rmkAllCongr (q := fun k => !(hookSigs.filter (·.name != rmKeys)).any (·.name == k.name))
      (fun k hk => by rw [any_less (hc k hk)]),
    rmkAllCongr (l := c.fns) (q := fun f => !(hookSigs.filter (·.name != rmKeys)).any (·.name == f.label))
      (fun f hf' => by rw [any_less (hf f hf')])]

/-! ## A parameter row numbered `rmKeys` -/

open Faithful.Model in
/-- **`coreOK` refuses a parameter row numbered `rmKeys`**: `kindsApart`, a conjunct of
`faithCoreOK`, asks that no parameter is an interpreted hook, and `rmKeys` is one. -/
theorem param_rmKeys {c : Semantics} (h : ∃ kp ∈ c.params, kp.sig.name = rmKeys) :
    kindsApart c = false ∧ c.coreOK = false := by
  obtain ⟨kp, hkp, hn⟩ := h
  have hka : kindsApart c = false := by
    apply Bool.eq_false_iff.mpr
    intro hk
    simp only [kindsApart, Bool.and_eq_true, List.all_eq_true] at hk
    have h2 := hk.2 kp hkp
    rw [hn] at h2
    exact absurd h2.2 (by decide +kernel)
  refine ⟨hka, Bool.eq_false_iff.mpr fun hc => ?_⟩
  have hfa := (Semantics.coreOK_parts hc).2.1
  simp only [Semantics.faithCoreOK, Bool.and_eq_true] at hfa
  rw [hka] at hfa
  exact Bool.false_ne_true hfa.1.1.2

/-- The imported modules' parameters the reader lists hold no row numbered `rmKeys`. -/
theorem libParams_not_rmKeys (imports : List Nat) : ∀ k ∈ libParams imports, k.sig.name ≠ rmKeys := by
  intro k hk he
  simp only [libParams, List.mem_flatMap, List.mem_map, List.mem_filter] at hk
  obtain ⟨m, -, k', ⟨-, hn⟩, rfl⟩ := hk
  rw [he] at hn
  exact absurd hn (by decide +kernel)

/-- `c1` with the parameter row `keys : RangeMap → Set` numbered `rmKeys`. -/
def cp : Semantics := { c1 with params := [{ sig := ⟨rmKeys, [Srt.rangeMap], Srt.set⟩ }] }

/-- `cp` is refused; `rmKeys` is a parameter of it and interpreted. -/
theorem param_row : cp.coreOK = false ∧ cp.isParam rmKeys = true ∧ isHook rmKeys = true :=
  ⟨(param_rmKeys ⟨_, List.mem_singleton_self _, rfl⟩).2, by decide +kernel, by decide +kernel⟩

end KCore.RangeMapKeysCone

/-- info: 'KCore.RangeMapKeysCone.tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.tables
/-- info: 'KCore.RangeMapKeysCone.refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.refused
/-- info: 'KCore.RangeMapKeysCone.cy_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.cy_below
/-- info: 'KCore.RangeMapKeysCone.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.accepted
/-- info: 'KCore.RangeMapKeysCone.hooksApart_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.hooksApart_row
/-- info: 'KCore.RangeMapKeysCone.param_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.param_row
/-- info: 'KCore.RangeMapKeysCone.param_rmKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.param_rmKeys
/-- info: 'KCore.RangeMapKeysCone.libParams_not_rmKeys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms KCore.RangeMapKeysCone.libParams_not_rmKeys
