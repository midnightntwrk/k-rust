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
  - `Two` (e3-vars-two, the text copied to `f2-examples/exvarstwo.kompile.kore`):
    `rule <k> c() => d(?Y:Int, ?Z:Int) ... </k>`, the text's one rewrite axiom, kompiled with the
    right side under `\exists(?Y, \exists(?Z, …))` (`text_binders`: the binders of the kernel's
    parse of the text, outermost first). The rule read has `exs = [2, 3]`, the variables named
    `?Y` and `?Z` (`exs_order`): the text's order of nesting. The sentence `Definition.emit`
    writes for the rule is the text's: the one rewrite axiom of the emitted definition has the
    pattern of the text's (`emitted_eq`), binders included.
  - `Bool` (e3-vars-bool, the text copied to `f2-examples/exvarsbool.kompile.kore`):
    `rule <k> c() => d(?Z:Bool) </k>`, the text's one rule, Z its existential variable 1. The text
    declares no function and no open generator, so `FnHyp` holds (`fnHyp`). `<k> c() </k>` steps
    to `d(true)` and to `d(false)` (`step`), and to nothing else (`step_inv`). `choice`: by the
    pinned `has_model_choice` at the steps of `Step` less the one from `c()` to `d(false)`, a
    model of `Γc` with the step's closure in which `den c() ⇒ ¬•den d(false)` holds and
    `den c() ⇒ ¬•den d(true)` does not; so no single instance of the rule is entailed as a
    successor. `outcomes`: by the pinned `famOpen_values`, in every model of `Γc` the family of the
    rule at `c()` is within `d(true) ∨ d(false)`.
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

theorem coreOK : c.coreOK = true := by decide_cheap

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

namespace Two

kore_term kore from "f2-examples/exvarstwo.kompile.kore"
definition_of defn from "f2-examples/exvarstwo.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The patterns of a definition's rewrite axioms, in text order. -/
def rewritesOf (k : Kore.Definition) : List Kore.Pattern :=
  k.axiomDecls.filterMap fun ad => match ad.ax.pattern with
    | .rewrites s l r => some (.rewrites s l r)
    | _ => none

/-- The names of the `\exists` binders heading a rewrite axiom's right side, outermost first. -/
def bindersOf : Kore.Pattern → List String
  | .rewrites _ _ r => go r
  | _ => []
where
  go : Kore.Pattern → List String
    | .exist _ v p => v.var.ident.name :: go p
    | _ => []

/-- The text has one rewrite axiom, and its right side is under `?Y`, then `?Z`. -/
theorem text_binders : (rewritesOf kore).map bindersOf = [["Var'Ques'Y", "Var'Ques'Z"]] := by
  decide +kernel

/-- **`exs` is in the text's order of nesting**: the one rule read has the existential variables
2 and 3, named `?Y` and `?Z`. -/
theorem exs_order : c.rules.map (·.exs) = [[2, 3]] ∧
    ((defn.pres.rules.getD 0 default).names.getD 2 "", (defn.pres.rules.getD 0 default).names.getD 3 "") =
      ("'Ques'Y", "'Ques'Z") := by
  decide +kernel

/-- **The emitted sentence is the text's**: the rewrite axioms `Definition.emit` writes have the
patterns of the text's, the binders in the same order. -/
theorem emitted_eq : rewritesOf defn.emit = rewritesOf kore := by decide +kernel

/-- info: 'ExFixtures.Two.emitted_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emitted_eq
/-- info: 'ExFixtures.Two.exs_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms exs_order
/-- info: 'ExFixtures.Two.text_binders' depends on axioms: [propext] -/
#guard_msgs in #print axioms text_binders

end Two

namespace Bool

definition_of defn from "f2-examples/exvarsbool.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 32
def kCell : Sym := 383
def symC : Sym := 385
def symD : Sym := 386

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

theorem r0_vars : r0.vars = [19, Srt.bool] := by decide +kernel
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC []),
    .app dotk []]], .var 0] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symD [.var 1]),
    .app dotk []]], .var 0] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [1] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `c() => d(?Z:Bool)`: Z (variable 1) is existential, under the constructor d and of the
confined sort Bool; every rule has the priority 50. -/
theorem facts : c.ruleSorted r0 = true ∧ c.rulePlainEx r0 = true ∧ c.confined Srt.bool = true ∧
    (∀ r ∈ c.rules, r.prio = 50) := by
  decide +kernel

/-- The text declares no function and no open generator, and no rule needs a witness. -/
theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel
theorem shapesOK : c.shapesOK = true := by decide +kernel
theorem opens_confined : ∀ i ∈ r0.opens, (r0.vars[i]?.map c.confined).getD false = true := by
  decide +kernel
theorem lhs_vars : ∀ j ∈ varOccs r0.lhs, j = 0 := by decide +kernel
theorem rhs_vars : ∀ j ∈ varOccs r0.rhs, j < 2 := by decide +kernel

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor dotk = true ∧ c.isCtor symC = true ∧ c.isCtor symD = true := by
  decide +kernel

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and no
parameter is an open generator. -/
theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-! ## The configurations -/

def ctr : GroundTerm := .ctor counterLabel [int 0]

/-- `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]], ctr]

/-- `<k> c() </k>`. -/
def X : Config c := ⟨cfg (.ctor symC []), by decide +kernel⟩
/-- `<k> d(b) </k>`. -/
def D (b : Bool) : Config c := ⟨cfg (.ctor symD [bool b]), by cases b <;> decide +kernel⟩

theorem D_ne : D true ≠ D false := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)

/-! ## `Step` from `c()` to `d(true)` and to `d(false)` -/

def σ (b : Bool) : Subst := [(0, ctr), (1, bool b)]

theorem prio_none {r' : Rule} (hr' : r' ∈ c.rules) (hlt : r'.prio < r0.prio) : False := by
  rw [facts.2.2.2 r' hr', facts.2.2.2 r0 r0_mem] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

/-- **`c()` steps to `d(b)` by the existential rule**, Z := b. -/
theorem stepBy (b : Bool) : StepBy c r0 (σ b) X (D b) where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, rfl, sortOf_bool b⟩
  hmatch := by
    rw [r0_lhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.2.1 .nil)) (.cons (.ctor syms_ok.2.2.2.1 .nil) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.2.2 (.cons .var .nil))) (.cons (.ctor syms_ok.2.2.2.1 .nil) .nil))) .nil))
      (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

theorem step (b : Bool) : Step c X (D b) := step_iff_by.mpr ⟨r0, σ b, stepBy b⟩

/-! ## Every match at `c()` is one of the two -/

/-- A substitution that agrees with `σ b` on the rule's two variables gives the step to `d(b)`. -/
theorem stepBy_of_agree {τ : Subst} (b : Bool) (h : ∀ j, j < 2 → (σ b).lookup j = τ.lookup j) :
    StepBy c r0 τ X (D b) where
  mem := r0_mem
  hσ := fun j s hs => by
    have hj : j < 2 := by
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hs
      rw [r0_vars] at hlt
      exact hlt
    obtain ⟨v, hl, hv⟩ := (stepBy b).hσ j s hs
    exact ⟨v, by rw [← h j hj]; exact hl, hv⟩
  hmatch := PatVal.congr_lookup (stepBy b).hmatch fun j hj => by
    rw [lhs_vars j hj]; exact (h 0 (by decide)).symm
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := Exec.EvalTerm.congr (stepBy b).heval fun i hi => h i (rhs_vars i hi)
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- A substitution that matches the rule's left side at `<k> c() </k>` gives the counter cell to
variable 0. -/
theorem lookup0 {τ : Subst} (hm : PatVal c τ r0.lhs X.val) : τ.lookup 0 = some ctr := by
  rw [r0_lhs] at hm
  have hm' : PatVal c τ (.app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC []),
    .app dotk []]], .var 0]) (.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symC []),
      .ctor dotk []]], ctr]) := hm
  cases hm' with
  | ctor _ hs =>
    cases hs with
    | cons _ hs =>
      cases hs with
      | cons hv _ => exact PatVal.var_inv hv
  | hook hp _ _ => exact absurd hp (by decide +kernel)
  | coll hc _ _ _ => rw [syms_ok.1] at hc; cases hc
  | ovl hc _ _ _ => rw [syms_ok.1] at hc; cases hc

/-- A well-sorted substitution that matches at `<k> c() </k>` agrees with `σ b` on the rule's
variables, for the Boolean b it gives Z. -/
theorem match_two {τ : Subst} (hτ : c.WellSorted r0.vars τ) (hm : PatVal c τ r0.lhs X.val) :
    ∃ b, ∀ j, j < 2 → (σ b).lookup j = τ.lookup j := by
  obtain ⟨v, hl, hv⟩ := hτ 1 Srt.bool (by rw [r0_vars]; rfl)
  obtain ⟨b, rfl⟩ := shape_bool shapesOK hv
  refine ⟨b, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => rw [lookup0 hm]; rfl
  | 1, _ => rw [hl]; rfl

/-- **Every successor of `c()` is `d(true)` or `d(false)`.** -/
theorem step_inv {τ : Subst} {y : Config c} (hs : StepBy c r0 τ X y) : ∃ b, y = D b := by
  obtain ⟨b, hb⟩ := match_two hs.hσ hs.hmatch
  refine ⟨b, Subtype.ext ?_⟩
  have h1 : EvalTerm c τ r0.rhs (some (D b).val) :=
    Exec.EvalTerm.congr (stepBy b).heval fun i hi => hb i (rhs_vars i hi)
  exact Option.some.inj (EvalTerm.functional_of_fnDet (fnModel_of_fnHyp coreOK fnHyp).1 hs.heval h1)

/-! ## No single instance is entailed -/

/-- The steps of `Step`, less the one from `c()` to `d(false)`. -/
def T (x y : Config c) : Prop := Step c x y ∧ (x = X → y ≠ D false)

/-- **A model in which `c()` does not step to `d(false)`** (`has_model_choice` at `T`): a model of
`Γc` with the step's closure in which `den c() ⇒ ¬•den d(false)` holds, while
`den c() ⇒ ¬•den d(true)` does not: there `c()` has a successor, and `d(false)` is not one. So the
theory does not entail the step to the instance `d(false)`, which `Step` has. -/
theorem choice : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
    (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c (D false).val))) ∧
    ¬ (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c (D true).val))) := by
  obtain ⟨M, i, I, hI, hT⟩ := has_model_choice c coreOK fnHyp T (fun _ _ h => h.1)
    (fun x y r τ hs hex => by
      rw [rule_eq hs.mem, r0_shape.2.2.2.2] at hex; cases hex)
    (fun x y r τ hs => by
      have hr := rule_eq hs.mem
      subst hr
      by_cases hx : x = X
      · subst hx
        have h0 := lookup0 hs.hmatch
        refine ⟨D true, (1, bool true) :: τ, fun i hi => ?_,
          stepBy_of_agree true (fun j hj => ?_), step true, fun _ => D_ne⟩
        · rw [r0_shape.2.2.2.2] at hi
          have hne : (i == 1) = false := beq_false_of_ne (by simpa using hi)
          show List.lookup i ((1, bool true) :: τ) = List.lookup i τ
          rw [List.lookup_cons, hne]
        · match j, hj with
          | 0, _ => exact h0.symm
          | 1, _ => rfl
      · exact ⟨y, τ, fun _ _ => rfl, hs, step_iff_by.mpr ⟨_, _, hs⟩, fun h => absurd h hx⟩)
  exact ⟨M, i, I, hI, Classical.not_not.mp fun hn => ((hT X (D false)).mpr hn).2 rfl rfl,
    (hT X (D true)).mp ⟨step true, fun _ => D_ne⟩⟩

/-! ## The outcomes of the match -/

/-- **The instances of the application are `d(true)` and `d(false)`** (`famOpen_values`): in every
model of `Γc`, a state in the family of the rule at `c()` is one of the two. -/
theorem outcomes : Γc c ⊧ (famOpen c r0 (σ true) ⇒
    KoreAML.disjList ([(D true).val, (D false).val].map (den c))) :=
  famOpen_values c coreOK fnHyp X r0 r0_mem (σ true)
    ⟨fun j _ s hs => (stepBy true).hσ j s hs, (stepBy true).hmatch,
      fun r' hr' hlt => (prio_none hr' hlt).elim⟩
    opens_confined _
    (fun y ⟨τ, _, hs⟩ => by
      obtain ⟨b, rfl⟩ := step_inv hs
      cases b
      · exact .tail _ (.head _)
      · exact .head _)

/-- info: 'ExFixtures.Bool.choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms choice
/-- info: 'ExFixtures.Bool.outcomes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outcomes
/-- info: 'ExFixtures.Bool.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step

end Bool

end ExFixtures
