/-
  The rules with existential variables of test/ExFixtures.lean, under every interpretation of the
  parameters: K 7.1.337 kompile's texts of the fixtures e3-vars, e3-vars-two and e3-vars-bool
  (`f2-examples/e3-vars.kompile.kore`, `exvarstwo.kompile.kore`, `exvarsbool.kompile.kore`; each is
  its fixture's text up to the Source and Location attributes), each read by the reader, each
  statement over `c0.withHooks H` for every `H : HookParams`, `c0` the reading.
  Run from the package root: `lake env lean -j1 test/ExFixturesH.lean`.

  ## Why no statement depends on H
  An interpretation enters evaluation in three places: a parameter symbol without a registry hook
  (`Semantics.paramVal`), an interpreted symbol at a silent point (`Semantics.hookRes`), and the
  sort of an open generator's application (`Semantics.sortOf`). The texts declare no function
  (`fns_nil`) and no open generator (`noRaw0`), and the sides of the rules the statements read
  apply constructors only (`syms_ok`), so matching and evaluation read no hook, and every value
  has the sort the parsed data gives it (`sortOf_eq`). The proofs are those of
  test/ExFixtures.lean with the semantics `c0.withHooks H`.

  Each rule's item in Γ is a consequence of its text sentence (W1), on the same texts:
  test/TieE3Vars.lean `rule2_from_text` (sentence 170), test/TieE3VarsTwo.lean `rule0_from_text`
  (sentence 154), test/TieE3VarsBool.lean `rule0_from_text` (sentence 113).

  - `Vars` (`rule <k> c(_, _Y) => d(?Z:Int) ... </k>`, the text's third rule `r2`, Z its
    existential variable 5). At `<k> c(1, 2) </k>` (`X H`): `step H i`, `Step` to `<k> d(i) </k>`
    (`D H i`) for every Int i, with Z := i; `sound_x H i`, `sound_d H i`: in every model of `Γc`,
    x has a successor among the instances of the application (`den x ⇒ •famEx`) and `d(i)` is one
    of them (`den d(i) ⇒ famEx`), by the pinned `sound_at`.
  - `Two` (`rule <k> c() => d(?Y:Int, ?Z:Int) ... </k>`, the right side under
    `\exists(?Y, \exists(?Z, …))`). `exs_order H`: the one rule read has `exs = [2, 3]`, the
    variables named `?Y` and `?Z`: the text's order of nesting.
  - `Bool` (`rule <k> c() => d(?Z:Bool) </k>`, the text's one rule, Z its existential variable 1).
    `step H b`: `<k> c() </k>` steps to `d(true)` and to `d(false)`; `step_iff H`: and to nothing
    else. `choice H b`: by the pinned `has_model_choice` at the steps of `Step` less the one from
    `c()` to `d(!b)`, a model of `Γc` with the step's closure in which `c()` does not step to
    `d(!b)` and does step to `d(b)`; at b true and b false, a pair of models that differ on the
    successor, so no single instance of the rule is entailed. `outcomes H`: by the pinned
    `famOpen_values`, in every model of `Γc` the family of the rule at `c()` is within
    `d(true) ∨ d(false)`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace ExFixturesH

/-! The conditions of the parsed data that the proofs read do not read the interpretation. -/
theorem isCtor_wh_exh (c : Semantics) (H : HookParams) (f : Sym) : (c.withHooks H).isCtor f = c.isCtor f := rfl
theorem rules_wh_exh (c : Semantics) (H : HookParams) : (c.withHooks H).rules = c.rules := rfl
theorem fns_wh_exh (c : Semantics) (H : HookParams) : (c.withHooks H).fns = c.fns := rfl
theorem params_wh_exh (c : Semantics) (H : HookParams) : (c.withHooks H).params = c.params := rfl
theorem shapesOK_wh_exh (c : Semantics) (H : HookParams) : (c.withHooks H).shapesOK = c.shapesOK := rfl
theorem litSort_wh_exh (c : Semantics) (H : HookParams) (s : Srt) : (c.withHooks H).litSort s = c.litSort s := rfl

namespace Vars

definition_of defn from "f2-examples/e3-vars.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_exh, rules_wh_exh, fns_wh_exh, params_wh_exh, shapesOK_wh_exh];
    decide +kernel))

def sExp : Srt := 34
def kCell : Sym := 385
def nCell : Sym := 387
def symC : Sym := 391
def symD : Sym := 392

theorem names_ok : c0.sortName sExp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName nCell = "Lbl'-LT-'n'-GT-'" ∧ c0.symName symC = "Lblc" ∧ c0.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r2 : Rule := c0.rules[2]'(by decide +kernel)

theorem r2_mem : r2 ∈ (c0.withHooks H).rules := List.getElem_mem _

theorem r2_vars : r2.vars = [Srt.int, Srt.int, Srt.k, 32, 19, Srt.int] := by decide +kernel
theorem r2_lhs : r2.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC [.var 0, .var 1]),
    .var 2]], .var 3, .var 4] := rfl
theorem r2_rhs : r2.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symD [.var 5]),
    .var 2]], .var 3, .var 4] := rfl
theorem r2_shape : r2.req = none ∧ r2.ens = none ∧ r2.pre = .top ∧ r2.post = .top ∧ r2.exs = [5] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every rule of the text has the priority 50, and the text declares no function. -/
theorem prios : ∀ r ∈ (c0.withHooks H).rules, r.prio = 50 := by whd
theorem fns_nil : (c0.withHooks H).fns = [] := by whd

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧
    (c0.withHooks H).isCtor kseq = true ∧ (c0.withHooks H).isCtor symC = true ∧
    (c0.withHooks H).isCtor symD = true := by
  whd

/-! ## The configurations -/

/-- `<k> st ~> . </k> <n> 0 </n>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]],
    .ctor nCell [int 0], .ctor counterLabel [int 0]]

theorem sortOf_ctor_congr {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c0.ctorSigs f).isSome = true)
    (h : c0.sortsOf ts = c0.sortsOf ts0) : c0.sortOf (.ctor f ts) = c0.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr {t t0 : GroundTerm} {ts : List GroundTerm} (h : c0.sortOf t = c0.sortOf t0) :
    c0.sortsOf (t :: ts) = c0.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congr {a b : Srt} {t t0 : GroundTerm} (h : c0.sortOf t = c0.sortOf t0)
    (hi : t.isInj = t0.isInj) : c0.sortOf (.inj a b t) = c0.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

theorem lookups_ok : (lookupSig c0.ctorSigs topLabel).isSome = true ∧ (lookupSig c0.ctorSigs kCell).isSome = true ∧
    (lookupSig c0.ctorSigs kseq).isSome = true ∧ (lookupSig c0.ctorSigs symD).isSome = true := by
  decide +kernel

/-- `<k> d(v) </k>` is a configuration for every v of sort Int, layer by layer from `d(0)`'s. -/
theorem sortOf_cfgD {v : GroundTerm} (hv : c0.sortOf v = some Srt.int) :
    (c0.withHooks H).sortOf (cfg (.ctor symD [v])) = some topCellSort := by
  have h0 : c0.sortOf (cfg (.ctor symD [int 0])) = some topCellSort := by decide +kernel
  rw [sortOf_eq, ← h0]
  exact sortOf_ctor_congr lookups_ok.1 (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.1
    (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.2.1 (sortsOf_head_congr (sortOf_inj_congr
      (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hv, sortOf_int]))) rfl))))))

/-- `<k> c(1, 2) </k>`. -/
def X (H : HookParams) : Config (c0.withHooks H) := ⟨cfg (.ctor symC [int 1, int 2]), by whd⟩
/-- `<k> d(i) </k>`. -/
def D (H : HookParams) (i : Int) : Config (c0.withHooks H) :=
  ⟨cfg (.ctor symD [int i]), sortOf_cfgD (sortOf_int i)⟩

/-! ## `Step` from `c(1, 2)` to `d(i)`, for every Int i -/

def σ (i : Int) : Subst :=
  [(0, int 1), (1, int 2), (2, .ctor dotk []), (3, .ctor nCell [int 0]), (4, .ctor counterLabel [int 0]),
    (5, int i)]

theorem prio_none {r' : Rule} (hr' : r' ∈ (c0.withHooks H).rules) (hlt : r'.prio < r2.prio) : False := by
  rw [prios r' hr', prios r2 (r2_mem (H := H))] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

/-- **`c(1, 2)` steps to `d(i)` by the existential rule**, Z := i. -/
theorem stepBy (i : Int) : StepBy (c0.withHooks H) r2 (σ i) (X H) (D H i) where
  mem := r2_mem
  hσ := fun j s hs => by
    rw [r2_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 1⟩
    | 1, hs => cases hs; exact ⟨_, rfl, sortOf_int 2⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 3, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 4, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 5, hs => cases hs; exact ⟨_, rfl, sortOf_int i⟩
  hmatch := by
    have hs := syms_ok (H := H)
    rw [r2_lhs]
    exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
      (.cons (.inj (.ctor hs.2.2.2.1 (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) (.cons (.var rfl) .nil)))
  hreq := fun t ht => by rw [r2_shape.1] at ht; cases ht
  hpre := by rw [r2_shape.2.2.1]; exact .top
  heval := by
    have hs := syms_ok (H := H)
    rw [r2_rhs]
    exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
      (.cons (.inj (.ctor hs.2.2.2.2 (.cons .var .nil))) (.cons .var .nil))) .nil))
      (.cons .var (.cons .var .nil)))
  hens := fun t ht => by rw [r2_shape.2.1] at ht; cases ht
  hpost := by rw [r2_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- **`<k> c(1, 2) </k>` steps to `<k> d(i) </k>`**, for every Int i. -/
theorem step (H : HookParams) (i : Int) : Step (c0.withHooks H) (X H) (D H i) :=
  step_iff_by.mpr ⟨r2, σ i, stepBy i⟩

theorem sound_xd (H : HookParams) (i : Int) :
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (X H).val ⇒ KoreAML.sNext (famEx (c0.withHooks H) r2 (σ i)))) ∧
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (D H i).val ⇒ famEx (c0.withHooks H) r2 (σ i))) :=
  sound_at (c0.withHooks H) coreOK (X H) (D H i) r2 (σ i) (stepBy i)
    (fun r' hr' hlt _ _ => (prio_none hr' hlt).elim)
    (fun fn hfn => by rw [fns_nil] at hfn; cases hfn)

/-- **In every model of `Γc`, `<k> c(1, 2) </k>` has a successor among the instances of the
application**, for every Int i (`sound_at`; no competitor, no function). -/
theorem sound_x (H : HookParams) (i : Int) :
    Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (X H).val ⇒ KoreAML.sNext (famEx (c0.withHooks H) r2 (σ i))) :=
  (sound_xd H i).1
/-- **In every model of `Γc`, `<k> d(i) </k>` is one of the instances**, for every Int i. -/
theorem sound_d (H : HookParams) (i : Int) :
    Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (D H i).val ⇒ famEx (c0.withHooks H) r2 (σ i)) :=
  (sound_xd H i).2

/-- The rule has an existential variable: the step above is not one `famEx_closed` covers. -/
theorem r2_exs_ne : r2.exs ≠ [] := by rw [r2_shape.2.2.2.2]; exact List.cons_ne_nil _ _

/-- info: 'ExFixturesH.Vars.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step
/-- info: 'ExFixturesH.Vars.sound_xd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_xd

end Vars

namespace Two

definition_of defn from "f2-examples/exvarstwo.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

/-- **`exs` is in the text's order of nesting**, under every interpretation: the one rule read has
the existential variables 2 and 3, named `?Y` and `?Z`. -/
theorem exs_order (H : HookParams) : (c0.withHooks H).rules.map (·.exs) = [[2, 3]] ∧
    ((defn.pres.rules.getD 0 default).names.getD 2 "", (defn.pres.rules.getD 0 default).names.getD 3 "") =
      ("'Ques'Y", "'Ques'Z") := by
  simp only [rules_wh_exh]
  decide +kernel

/-- info: 'ExFixturesH.Two.exs_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms exs_order

end Two

namespace Bool

definition_of defn from "f2-examples/exvarsbool.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_exh, rules_wh_exh, fns_wh_exh, params_wh_exh, shapesOK_wh_exh];
    decide +kernel))

def sExp : Srt := 32
def kCell : Sym := 383
def symC : Sym := 385
def symD : Sym := 386

theorem names_ok : c0.sortName sExp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symC = "Lblc" ∧ c0.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ (c0.withHooks H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ (c0.withHooks H).rules) : r = r0 := by
  rw [rules_wh_exh] at hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c0.rules.length = 1 := by decide +kernel
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

theorem prios : ∀ r ∈ (c0.withHooks H).rules, r.prio = 50 := by whd

/-- The text declares no function and no open generator, and no rule needs a witness. -/
theorem fns_nil : (c0.withHooks H).fns = [] := by whd
theorem noRaw : ∀ k ∈ (c0.withHooks H).params, k.raw = false := by whd
theorem noWitness : ∀ r ∈ (c0.withHooks H).rules, r.needsWitness (c0.withHooks H) = false := by
  intro r hr
  rw [rule_eq hr]
  have h : r0.reqOpen = false := by decide +kernel
  simp only [Rule.needsWitness, h, Bool.false_and]
theorem shapesOK : (c0.withHooks H).shapesOK = true := by whd
theorem lhs_vars : ∀ j ∈ varOccs r0.lhs, j = 0 := by decide +kernel
theorem rhs_vars : ∀ j ∈ varOccs r0.rhs, j < 2 := by decide +kernel

/-- The rule's open variable is Z, of the sort Bool, which is confined under every interpretation:
its values are the two literals. -/
theorem opens_confined : ∀ i ∈ r0.opens, (r0.vars[i]?.map (c0.withHooks H).confined).getD false = true := by
  have ho : r0.opens = [1] := by decide +kernel
  have hl : (c0.withHooks H).confinedAt 0 Srt.bool = true := by
    simp only [Semantics.confinedAt, litSort_wh_exh]
    decide +kernel
  have hc : (c0.withHooks H).confined Srt.bool = true := by
    unfold Semantics.confined
    cases (Faithful.kernelSorts (c0.withHooks H)).length with
    | zero => exact hl
    | succ k => simp only [Semantics.confinedAt, hl, Bool.true_or]
  intro i hi
  rw [ho, List.mem_singleton] at hi
  subst hi
  rw [r0_vars]
  exact hc

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧
    (c0.withHooks H).isCtor kseq = true ∧ (c0.withHooks H).isCtor dotk = true ∧
    (c0.withHooks H).isCtor symC = true ∧ (c0.withHooks H).isCtor symD = true := by
  whd

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and no
parameter is an open generator. -/
theorem fnHyp : FnHyp (c0.withHooks H) :=
  have hn : ∀ fn, fn ∈ (c0.withHooks H).fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
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
def X (H : HookParams) : Config (c0.withHooks H) := ⟨cfg (.ctor symC []), by whd⟩
/-- `<k> d(b) </k>`. -/
def D (H : HookParams) (b : Bool) : Config (c0.withHooks H) :=
  ⟨cfg (.ctor symD [bool b]), by cases b <;> whd⟩

theorem D_ne (b : Bool) : D H b ≠ D H (!b) := fun h => absurd (congrArg Subtype.val h)
  (by show ¬ cfg (.ctor symD [bool b]) = cfg (.ctor symD [bool (!b)]); cases b <;> decide +kernel)

/-! ## `Step` from `c()` to `d(true)` and to `d(false)` -/

def σ (b : Bool) : Subst := [(0, ctr), (1, bool b)]

theorem prio_none {r' : Rule} (hr' : r' ∈ (c0.withHooks H).rules) (hlt : r'.prio < r0.prio) : False := by
  rw [prios r' hr', prios r0 (r0_mem (H := H))] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

/-- **`c()` steps to `d(b)` by the existential rule**, Z := b. -/
theorem stepBy (b : Bool) : StepBy (c0.withHooks H) r0 (σ b) (X H) (D H b) where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 1, hs => cases hs; exact ⟨_, rfl, sortOf_bool b⟩
  hmatch := by
    have hs := syms_ok (H := H)
    rw [r0_lhs]
    exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
      (.cons (.inj (.ctor hs.2.2.2.2.1 .nil)) (.cons (.ctor hs.2.2.2.1 .nil) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    have hs := syms_ok (H := H)
    rw [r0_rhs]
    exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
      (.cons (.inj (.ctor hs.2.2.2.2.2 (.cons .var .nil))) (.cons (.ctor hs.2.2.2.1 .nil) .nil))) .nil))
      (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- **`<k> c() </k>` steps to `<k> d(b) </k>`**, for b true and b false. -/
theorem step (H : HookParams) (b : Bool) : Step (c0.withHooks H) (X H) (D H b) :=
  step_iff_by.mpr ⟨r0, σ b, stepBy b⟩

/-! ## Every match at `c()` is one of the two -/

/-- A substitution that agrees with `σ b` on the rule's two variables gives the step to `d(b)`. -/
theorem stepBy_of_agree {τ : Subst} (b : Bool) (h : ∀ j, j < 2 → (σ b).lookup j = τ.lookup j) :
    StepBy (c0.withHooks H) r0 τ (X H) (D H b) where
  mem := r0_mem
  hσ := fun j s hs => by
    have hj : j < 2 := by
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hs
      rw [r0_vars] at hlt
      exact hlt
    obtain ⟨v, hl, hv⟩ := (stepBy (H := H) b).hσ j s hs
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
theorem lookup0 {τ : Subst} (hm : PatVal (c0.withHooks H) τ r0.lhs (X H).val) : τ.lookup 0 = some ctr := by
  rw [r0_lhs] at hm
  have hm' : PatVal (c0.withHooks H) τ (.app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC []),
    .app dotk []]], .var 0]) (.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symC []),
      .ctor dotk []]], ctr]) := hm
  cases hm' with
  | ctor _ hs =>
    cases hs with
    | cons _ hs =>
      cases hs with
      | cons hv _ => exact PatVal.var_inv hv
  | hook hp _ _ => exact absurd hp (by decide +kernel)
  | coll hc _ _ _ => rw [(syms_ok (H := H)).1] at hc; cases hc
  | ovl hc _ _ _ => rw [(syms_ok (H := H)).1] at hc; cases hc

/-- A well-sorted substitution that matches at `<k> c() </k>` agrees with `σ b` on the rule's
variables, for the Boolean b it gives Z. -/
theorem match_two {τ : Subst} (hτ : (c0.withHooks H).WellSorted r0.vars τ)
    (hm : PatVal (c0.withHooks H) τ r0.lhs (X H).val) :
    ∃ b, ∀ j, j < 2 → (σ b).lookup j = τ.lookup j := by
  obtain ⟨v, hl, hv⟩ := hτ 1 Srt.bool (by rw [r0_vars]; rfl)
  obtain ⟨b, rfl⟩ := shape_bool (shapesOK (H := H)) hv
  refine ⟨b, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => rw [lookup0 hm]; rfl
  | 1, _ => rw [hl]; rfl

/-- **Every successor of `c()` by the rule is `d(true)` or `d(false)`.** -/
theorem step_inv {τ : Subst} {y : Config (c0.withHooks H)} (hs : StepBy (c0.withHooks H) r0 τ (X H) y) :
    ∃ b, y = D H b := by
  obtain ⟨b, hb⟩ := match_two hs.hσ hs.hmatch
  refine ⟨b, Subtype.ext ?_⟩
  have h1 : EvalTerm (c0.withHooks H) τ r0.rhs (some (D H b).val) :=
    Exec.EvalTerm.congr (stepBy b).heval fun i hi => hb i (rhs_vars i hi)
  exact Option.some.inj (EvalTerm.functional_of_fnDet
    (fnModel_of_fnHyp (coreOK (H := H)) (fnHyp (H := H))).1 hs.heval h1)

/-- **The successors of `<k> c() </k>`** are exactly `<k> d(true) </k>` and `<k> d(false) </k>`. -/
theorem step_iff (H : HookParams) (y : Config (c0.withHooks H)) :
    Step (c0.withHooks H) (X H) y ↔ ∃ b, y = D H b := by
  refine ⟨fun hs => ?_, fun ⟨b, hb⟩ => hb ▸ step H b⟩
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  obtain rfl := rule_eq hb.mem
  exact step_inv hb

/-! ## No single instance is entailed -/

/-- **A model in which `c()` does not step to `d(!b)`, and does step to `d(b)`** (`has_model_choice`
at the steps of `Step` less the one from `c()` to `d(!b)`): a model of `Γc` with the step's closure
in which `den c() ⇒ ¬•den d(!b)` holds, while `den c() ⇒ ¬•den d(b)` does not. At b true and b
false the two models differ on the successor of `c()`: the theory entails the step to neither
instance, each of which `Step` has. -/
theorem choice (H : HookParams) (b : Bool) : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧
    (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) (D H (!b)).val))) ∧
    ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) (D H b).val))) := by
  let T : Config (c0.withHooks H) → Config (c0.withHooks H) → Prop :=
    fun x y => Step (c0.withHooks H) x y ∧ (x = X H → y ≠ D H (!b))
  obtain ⟨M, i, I, hI, hT⟩ := has_model_choice (c0.withHooks H) coreOK fnHyp T (fun _ _ h => h.1)
    (fun x y r τ hs hex => by
      rw [rule_eq hs.mem, r0_shape.2.2.2.2] at hex; cases hex)
    (fun x y r τ hs => by
      have hr := rule_eq hs.mem
      subst hr
      by_cases hx : x = X H
      · subst hx
        have h0 := lookup0 hs.hmatch
        refine ⟨D H b, (1, bool b) :: τ, fun i hi => ?_,
          stepBy_of_agree b (fun j hj => ?_), step H b, fun _ => D_ne b⟩
        · rw [r0_shape.2.2.2.2] at hi
          have hne : (i == 1) = false := beq_false_of_ne (by simpa using hi)
          show List.lookup i ((1, bool b) :: τ) = List.lookup i τ
          rw [List.lookup_cons, hne]
        · match j, hj with
          | 0, _ => exact h0.symm
          | 1, _ => rfl
      · exact ⟨y, τ, fun _ _ => rfl, hs, step_iff_by.mpr ⟨_, _, hs⟩, fun h => absurd h hx⟩)
  exact ⟨M, i, I, hI, Classical.not_not.mp fun hn => ((hT (X H) (D H (!b))).mpr hn).2 rfl rfl,
    (hT (X H) (D H b)).mp ⟨step H b, fun _ => D_ne b⟩⟩

/-! ## The outcomes of the match -/

/-- **The instances of the application are `d(true)` and `d(false)`** (`famOpen_values`): in every
model of `Γc`, a state in the family of the rule at `c()` is one of the two. -/
theorem outcomes (H : HookParams) : Γc (c0.withHooks H) ⊧ (famOpen (c0.withHooks H) r0 (σ true) ⇒
    KoreAML.disjList ([(D H true).val, (D H false).val].map (den (c0.withHooks H)))) :=
  famOpen_values (c0.withHooks H) coreOK fnHyp (X H) r0 r0_mem (σ true)
    ⟨fun j _ s hs => (stepBy (H := H) true).hσ j s hs, (stepBy true).hmatch,
      fun r' hr' hlt => (prio_none hr' hlt).elim⟩
    opens_confined _
    (fun y ⟨τ, _, hs⟩ => by
      obtain ⟨b, rfl⟩ := step_inv hs
      cases b
      · exact .tail _ (.head _)
      · exact .head _)

/-- info: 'ExFixturesH.Bool.choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms choice
/-- info: 'ExFixturesH.Bool.outcomes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outcomes
/-- info: 'ExFixturesH.Bool.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff

end Bool

end ExFixturesH

#check @ExFixturesH.Vars.step
#check @ExFixturesH.Vars.sound_x
#check @ExFixturesH.Vars.sound_d
#check @ExFixturesH.Two.exs_order
#check @ExFixturesH.Bool.step
#check @ExFixturesH.Bool.step_iff
#check @ExFixturesH.Bool.choice
#check @ExFixturesH.Bool.outcomes
