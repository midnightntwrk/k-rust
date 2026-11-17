/-
  The fixtures of rules with existential variables (CN-4 §4.8, R2 fixture table), read from
  K 7.1.337 kompile's KORE. Run from the package root: `lake env lean -j1 test/ExFixtures.lean`.

  - `Vars` (e3-vars, `test/constructs/fixtures/e3-vars/kore.txt:185-191`, the text copied to
    `f2-examples/exrhs.kompile.kore`): `rule <k> c(_, _Y) => d(?Z:Int) ... </k>`, kompiled as
    `\rewrites(\and(lhs, \top), \exists(Var'Ques'Z:SortInt, \and(rhs, \top)))`. The account has
    `stage refusals (of sentences classified read): 0` (test/constructs/fixtures/e3-vars/account.txt)
    and the text has `coreOK` (`coreOK`, by the kernel). The rule is the text's third (`r2`), Z its
    existential variable 5. At `x = <k> c(1, 2) </k>` (`X`): `Step` to `d(i)` for every Int i
    (`step`), built by hand with Z := i; in every model of `Γc`, x has a successor among the
    instances of the application (`Γc ⊧ den x ⇒ •famEx`) and `d(i)` is one of them
    (`Γc ⊧ den d(i) ⇒ famEx`) (`sound_x`, `sound_d`), by the pinned `sound_at`. These are the
    instances at a concrete step by an existential rule that test/ExRules.lean's `cX` section takes
    as a hypothesis.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace ExFixtures

namespace Vars

definition_of defn from "f2-examples/exrhs.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 34
def kCell : Sym := 385
def nCell : Sym := 387
def symC : Sym := 391
def symD : Sym := 392

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName nCell = "Lbl'-LT-'n'-GT-'" ∧ c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide +kernel

noncomputable def r2 : Rule := c.rules[2]'(by decide +kernel)

theorem r2_mem : r2 ∈ c.rules := List.getElem_mem _

theorem r2_vars : r2.vars = [Srt.int, Srt.int, Srt.k, 32, 19, Srt.int] := by decide +kernel
theorem r2_lhs : r2.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC [.var 0, .var 1]),
    .var 2]], .var 3, .var 4] := rfl
theorem r2_rhs : r2.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symD [.var 5]),
    .var 2]], .var 3, .var 4] := rfl
theorem r2_shape : r2.req = none ∧ r2.ens = none ∧ r2.pre = .top ∧ r2.post = .top ∧ r2.exs = [5] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `c(_, _Y) => d(?Z:Int)`: Z (variable 5) is existential, held by the constructor d (arm A),
`rulePlainEx` and `ruleSorted` hold; every rule of the text has the priority 50 and the text
declares no function. -/
theorem facts : c.ruleSorted r2 = true ∧ c.rulePlainEx r2 = true ∧ (ctorOccs c r2.rhs).contains 5 = true ∧
    (∀ r ∈ c.rules, r.prio = 50) ∧ c.fns = [] := by
  decide +kernel

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symC = true ∧ c.isCtor symD = true := by
  decide +kernel

/-! ## The configurations -/

/-- `<k> st ~> . </k> <n> 0 </n>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]],
    .ctor nCell [int 0], .ctor counterLabel [int 0]]

theorem sortOf_ctor_congr {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr {t t0 : GroundTerm} {ts : List GroundTerm} (h : c.sortOf t = c.sortOf t0) :
    c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congr {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symD).isSome = true := by
  decide +kernel

/-- `<k> d(v) </k>` is a configuration for every v of sort Int, layer by layer from `d(0)`'s. -/
theorem sortOf_cfgD {v : GroundTerm} (hv : c.sortOf v = some Srt.int) :
    c.sortOf (cfg (.ctor symD [v])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symD [int 0])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congr lookups_ok.1 (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.1
    (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.2.1 (sortsOf_head_congr (sortOf_inj_congr
      (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hv, sortOf_int]))) rfl))))))

/-- `<k> c(1, 2) </k>`. -/
def X : Config c := ⟨cfg (.ctor symC [int 1, int 2]), by decide +kernel⟩
/-- `<k> d(i) </k>`. -/
def D (i : Int) : Config c := ⟨cfg (.ctor symD [int i]), sortOf_cfgD (sortOf_int i)⟩

/-! ## `Step` from `c(1, 2)` to `d(i)`, for every Int i -/

def σ (i : Int) : Subst :=
  [(0, int 1), (1, int 2), (2, .ctor dotk []), (3, .ctor nCell [int 0]), (4, .ctor counterLabel [int 0]),
    (5, int i)]

/-- **`c(1, 2)` steps to `d(i)` by the existential rule**, Z := i. -/
theorem stepBy (i : Int) : StepBy c r2 (σ i) X (D i) where
  mem := r2_mem
  hσ := fun j s hs => by
    rw [r2_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 1⟩
    | 1, hs => cases hs; exact ⟨_, rfl, sortOf_int 2⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 3, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 4, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 5, hs => cases hs; exact ⟨_, rfl, sortOf_int i⟩
  hmatch := by
    rw [r2_lhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.1 (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) (.cons (.var rfl) .nil)))
  hreq := fun t ht => by rw [r2_shape.1] at ht; cases ht
  hpre := by rw [r2_shape.2.2.1]; exact .top
  heval := by
    rw [r2_rhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.2 (.cons .var .nil))) (.cons .var .nil))) .nil))
      (.cons .var (.cons .var .nil)))
  hens := fun t ht => by rw [r2_shape.2.1] at ht; cases ht
  hpost := by rw [r2_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [facts.2.2.2.1 r' hr', show r2.prio = 50 from facts.2.2.2.1 r2 r2_mem] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

theorem step (i : Int) : Step c X (D i) := step_iff_by.mpr ⟨r2, σ i, stepBy i⟩

/-- **In every model of `Γc`, `<k> c(1, 2) </k>` has a successor among the instances of the
application, and `<k> d(i) </k>` is one of them**, for every Int i (`sound_at`; no competitor, no
function). -/
theorem sound_xd (i : Int) :
    (Γc c ⊧ (den c X.val ⇒ KoreAML.sNext (famEx c r2 (σ i)))) ∧ (Γc c ⊧ (den c (D i).val ⇒ famEx c r2 (σ i))) :=
  sound_at c coreOK X (D i) r2 (σ i) (stepBy i)
    (fun r' hr' hlt _ _ => by
      rw [facts.2.2.2.1 r' hr', show r2.prio = 50 from facts.2.2.2.1 r2 r2_mem] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    (fun fn hfn => by rw [facts.2.2.2.2] at hfn; cases hfn)

theorem sound_x (i : Int) : Γc c ⊧ (den c X.val ⇒ KoreAML.sNext (famEx c r2 (σ i))) := (sound_xd i).1
theorem sound_d (i : Int) : Γc c ⊧ (den c (D i).val ⇒ famEx c r2 (σ i)) := (sound_xd i).2

/-- The rule has an existential variable: the step above is not one `famEx_closed` covers. -/
theorem r2_exs_ne : r2.exs ≠ [] := by rw [r2_shape.2.2.2.2]; exact List.cons_ne_nil _ _

/-- info: 'ExFixtures.Vars.sound_xd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_xd

end Vars

end ExFixtures
