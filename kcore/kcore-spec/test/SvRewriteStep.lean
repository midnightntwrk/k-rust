/-
  The steps of a rewrite axiom with a set variable, on K 7.1.337 kompile's text of fixture
  e3-setvar-rewrite (`rule <k> c(@S, @S) => d(@S) ... </k>`, `syntax Exp ::= a() | b() | c(Exp, Exp)
  | d(Exp)`; `f2-examples/e3-setvar-rewrite.kompile.kore`, its paths restored). Run from the package
  root: `lake env lean -j1 test/SvRewriteStep.lean`.

  The reader reads the axiom through its instances at one element per occurrence
  (`Parse.svRewrite?`; test/SvRewriteRead.lean): the rule `r0`, `c(L0, L1) => d(?R0)`, the left
  occurrences the variables 0 and 1, the right one the existential variable 4, with
  `post := R0 ∈ L0 ∨ R0 ∈ L1` (`r0_shape`). The text has `coreOK` and declares no function, so
  `FnHyp` holds (`fnHyp`).

  - `step_a`, `step_b`: at `<k> c(a, b) </k>` (`X`), `Step` to `<k> d(a) </k>` and to
    `<k> d(b) </k>` (`DA`, `DB`), R0 := a and R0 := b; `step_inv`: every step by the rule at X is to
    one of the two, since `post` puts R0 among the matched elements.
  - `sound`: in every model of `Γc`, X has a successor among the instances of the application
    (`famEx`), and `d(a)` and `d(b)` are both instances (the pinned `sound_at`). `famEx_iff`: a value
    the instances hold in every model of `Γc` is `d(a)` or `d(b)` (the pinned `famEx_values`).
  - `choice_a`, `choice_b`: by the pinned `has_model_choice` at the steps of `Step` less the one from
    X to `d(b)` (to `d(a)`), a model of `Γc` with the step's closure in which X does not step to
    `d(b)` (to `d(a)`) and does step to the other. So, a and b distinct, the theory entails neither
    step alone: it entails that X steps to `d(a)` or `d(b)`, as the sentence at the set `{a, b}`
    says.

  The shapes the reader refuses are test/SvRewriteRead.lean's: the set variable in the requires
  (fixture e3-setvar-rewrite-req) `setVariable`, and `=> d(g(@S))` (e3-setvar-rewrite-fn)
  `openRight`, the existential variable under the function g.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace SvRewriteStep

definition_of defn from "f2-examples/e3-setvar-rewrite.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symC : Sym := 387
def symD : Sym := 388

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧ c.symName symC = "Lblc" ∧
    c.symName symD = "Lbld" := by
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

theorem r0_vars : r0.vars = [sExp, sExp, Srt.k, 19, sExp] := by decide +kernel
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC [.var 0, .var 1]),
    .var 2]], .var 3] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symD [.var 4]),
    .var 2]], .var 3] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧
    r0.post = .or (.mem sExp (.var 4) (.var 0)) (.mem sExp (.var 4) (.var 1)) ∧ r0.exs = [4] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem facts : c.ruleSorted r0 = true ∧ (∀ r ∈ c.rules, r.prio = 50) := by
  decide +kernel

theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel
theorem lhs_vars : ∀ j ∈ varOccs r0.lhs, j < 4 := by decide +kernel
theorem rhs_vars : ∀ j ∈ varOccs r0.rhs, j < 5 := by decide +kernel

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor dotk = true ∧ c.isCtor symA = true ∧ c.isCtor symB = true ∧ c.isCtor symC = true ∧
    c.isCtor symD = true := by
  decide +kernel

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false := by
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
def dk : GroundTerm := .ctor dotk []
def a : GroundTerm := .ctor symA []
def b : GroundTerm := .ctor symB []

/-- `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, dk]], ctr]

/-- `<k> c(a, b) </k>`. -/
def X : Config c := ⟨cfg (.ctor symC [a, b]), by decide +kernel⟩
/-- `<k> d(a) </k>` and `<k> d(b) </k>`. -/
def DA : Config c := ⟨cfg (.ctor symD [a]), by decide +kernel⟩
def DB : Config c := ⟨cfg (.ctor symD [b]), by decide +kernel⟩

theorem DA_ne : DA ≠ DB := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)

/-! ## `Step` from `c(a, b)` to `d(a)` and to `d(b)` -/

/-- The match of the left side at X, with R0 := z. -/
def σ (z : GroundTerm) : Subst := [(0, a), (1, b), (2, dk), (3, ctr), (4, z)]

theorem prio_none {r' : Rule} (hr' : r' ∈ c.rules) (hlt : r'.prio < r0.prio) : False := by
  rw [facts.2 r' hr', facts.2 r0 r0_mem] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

theorem ws (z : GroundTerm) (hz : c.sortOf z = some sExp) : c.WellSorted r0.vars (σ z) := fun j s hs => by
  rw [r0_vars] at hs
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 3, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 4, hs => cases hs; exact ⟨_, rfl, hz⟩

theorem matchX (z : GroundTerm) : PatVal c (σ z) r0.lhs X.val := by
  rw [r0_lhs]
  exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
    (.cons (.inj (.ctor syms_ok.2.2.2.2.2.2.1 (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))

theorem evalD (z : GroundTerm) :
    EvalTerm c (σ z) r0.rhs (some (cfg (.ctor symD [z]))) := by
  rw [r0_rhs]
  exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
    (.cons (.inj (.ctor syms_ok.2.2.2.2.2.2.2 (.cons .var .nil))) (.cons .var .nil))) .nil))
    (.cons .var .nil))

/-- `post` at σ z: z is a or b. -/
theorem post_iff (z : GroundTerm) :
    Holds c r0.vars.length (σ z) r0.post ((some z).isSome && sameResult (some z) (some a) ||
      (some z).isSome && sameResult (some z) (some b)) := by
  rw [r0_shape.2.2.2.1]
  exact .or (.mem .var .var) (.mem .var .var)

/-- **`c(a, b)` steps to `d(z)` by the rule, R0 := z**, for z among the matched elements. -/
theorem stepBy (z : GroundTerm) (hz : c.sortOf z = some sExp)
    (hpost : ((some z).isSome && sameResult (some z) (some a) ||
      (some z).isSome && sameResult (some z) (some b)) = true) (y : Config c)
    (hy : y.val = cfg (.ctor symD [z])) : StepBy c r0 (σ z) X y where
  mem := r0_mem
  hσ := ws z hz
  hmatch := matchX z
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := hy ▸ evalD z
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := hpost ▸ post_iff z
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

theorem stepByA : StepBy c r0 (σ a) X DA := stepBy a (by decide +kernel) (by decide +kernel) DA rfl
theorem stepByB : StepBy c r0 (σ b) X DB := stepBy b (by decide +kernel) (by decide +kernel) DB rfl

theorem step_a : Step c X DA := step_iff_by.mpr ⟨r0, σ a, stepByA⟩
theorem step_b : Step c X DB := step_iff_by.mpr ⟨r0, σ b, stepByB⟩

/-! ## Every step at `c(a, b)` is to `d(a)` or `d(b)` -/

/-- A substitution that matches the left side at X gives the four variables the values of `σ`. -/
theorem lookups {τ : Subst} (hm : PatVal c τ r0.lhs X.val) :
    ∀ j, j < 4 → τ.lookup j = (σ a).lookup j := by
  rw [r0_lhs] at hm
  obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.1 hm syms_ok.1
  injection hv with _ hv
  subst hv
  cases hs with
  | cons hk hs =>
    cases hs with
    | cons h3 _ =>
      obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.2.1 hk syms_ok.2.1
      injection hv with _ hv
      subst hv
      cases hs with
      | cons hq _ =>
        obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.2.2.1 hq syms_ok.2.2.1
        injection hv with _ hv
        subst hv
        cases hs with
        | cons hi hs =>
          cases hs with
          | cons h2 _ =>
            obtain ⟨w, hw, hwv⟩ := PatVal.inj_inv hi
            rw [PatVal.injNormal_of (by decide +kernel) hw] at hwv
            injection hwv with _ _ hwv
            subst hwv
            obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw syms_ok.2.2.2.2.2.2.1
            injection hv with _ hv
            subst hv
            cases hs with
            | cons h0 hs =>
              cases hs with
              | cons h1 _ =>
                intro j hj
                match j, hj with
                | 0, _ => exact PatVal.var_inv h0
                | 1, _ => exact PatVal.var_inv h1
                | 2, _ => exact PatVal.var_inv h2
                | 3, _ => exact PatVal.var_inv h3

/-- `post` at any substitution, its truth value read from the substitution. -/
theorem post_at (τ : Subst) :
    Holds c r0.vars.length τ r0.post ((τ.lookup 4).isSome && sameResult (τ.lookup 4) (τ.lookup 0) ||
      (τ.lookup 4).isSome && sameResult (τ.lookup 4) (τ.lookup 1)) := by
  rw [r0_shape.2.2.2.1]
  exact .or (.mem .var .var) (.mem .var .var)

/-- A substitution that agrees with `σ z` on the rule's five variables gives the step to `d(z)`. -/
theorem stepBy_of_agree {τ : Subst} (z : GroundTerm) (hz : c.sortOf z = some sExp)
    (hpz : ((some z).isSome && sameResult (some z) (some a) ||
      (some z).isSome && sameResult (some z) (some b)) = true)
    (h : ∀ j, j < 5 → (σ z).lookup j = τ.lookup j) (y : Config c)
    (hy : y.val = cfg (.ctor symD [z])) : StepBy c r0 τ X y where
  mem := r0_mem
  hσ := fun j s hs => by
    have hj : j < 5 := by
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hs
      rw [r0_vars] at hlt
      exact hlt
    obtain ⟨v, hl, hv⟩ := ws z hz j s hs
    exact ⟨v, by rw [← h j hj]; exact hl, hv⟩
  hmatch := PatVal.congr_lookup (matchX z) fun j hj => (h j (by have := lhs_vars j hj; omega)).symm
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := hy ▸ Exec.EvalTerm.congr (evalD z) fun i hi => h i (rhs_vars i hi)
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by
    have hp := post_at τ
    rw [← h 4 (by decide), ← h 0 (by decide), ← h 1 (by decide)] at hp
    exact hpz ▸ hp
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- **Every step by the rule at `c(a, b)` is to `d(a)` or to `d(b)`**: `post` puts R0 among the
matched elements. -/
theorem step_inv {τ : Subst} {y : Config c} (hs : StepBy c r0 τ X y) : y = DA ∨ y = DB := by
  have hl := lookups hs.hmatch
  have hd := (fnModel_of_fnHyp coreOK fnHyp).1
  obtain ⟨z, hz, -⟩ := hs.hσ 4 sExp (by rw [r0_vars]; rfl)
  have hb := Holds.functional_of_fnDet hd hs.hpost (post_at τ)
  rw [hz, hl 0 (by decide), hl 1 (by decide)] at hb
  have hτ : ∀ j, j < 5 → (σ z).lookup j = τ.lookup j := fun j hj => by
    match j, hj with
    | 0, _ => exact (hl 0 (by decide)).symm
    | 1, _ => exact (hl 1 (by decide)).symm
    | 2, _ => exact (hl 2 (by decide)).symm
    | 3, _ => exact (hl 3 (by decide)).symm
    | 4, _ => exact hz.symm
  have hev := fun (w : GroundTerm) (hw : z = w) =>
    EvalTerm.functional_of_fnDet hd hs.heval
      (hw ▸ Exec.EvalTerm.congr (evalD z) fun i hi => hτ i (rhs_vars i hi))
  change true = ((some z).isSome && sameResult (some z) (some a) ||
      (some z).isSome && sameResult (some z) (some b)) at hb
  have hzab : z = a ∨ z = b := by
    cases h1 : (GroundTerm.cmp z a == .eq)
    · cases h2 : (GroundTerm.cmp z b == .eq)
      · exfalso
        simp only [sameResult, Option.isSome_some, Bool.true_and, h1, h2, Bool.or_false] at hb
        exact Bool.noConfusion hb
      · exact .inr (cmp_eq_iff.mp (beq_iff_eq.mp h2))
    · exact .inl (cmp_eq_iff.mp (beq_iff_eq.mp h1))
  rcases hzab with rfl | rfl
  · exact .inl (Subtype.ext (Option.some.inj (hev _ rfl)))
  · exact .inr (Subtype.ext (Option.some.inj (hev _ rfl)))

/-! ## In every model of `Γc`, the instances are `d(a)` and `d(b)` -/

/-- **In every model of `Γc`, `<k> c(a, b) </k>` has a successor among the instances of the
application, and `d(a)` and `d(b)` are both instances** (the pinned `sound_at`: no competitor, no
function). The family at `σ a` and at `σ b` is one: the two substitutions differ at the
existential variable only. -/
theorem sound :
    (Γc c ⊧ (den c X.val ⇒ KoreAML.sNext (famEx c r0 (σ a)))) ∧
    (Γc c ⊧ (den c DA.val ⇒ famEx c r0 (σ a))) ∧ (Γc c ⊧ (den c DB.val ⇒ famEx c r0 (σ a))) := by
  have hw : ∀ r' ∈ c.rules, r'.prio < r0.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs X.val) → r'.CondDecided c := fun r' hr' hlt _ _ => (prio_none hr' hlt).elim
  have hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c :=
    fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  have hA := sound_at c coreOK X DA r0 (σ a) stepByA hw hc
  have hB := sound_at c coreOK X DB r0 (σ b) stepByB hw hc
  have heq : famEx c r0 (σ b) = famEx c r0 (σ a) := rfl
  exact ⟨hA.1, hA.2, heq ▸ hB.2⟩

/-- **A value the instances hold in every model of `Γc` is `d(a)` or `d(b)`** (the pinned
`famEx_values`, then `step_inv`). -/
theorem famEx_iff (y : Config c) (hy : Γc c ⊧ (den c y.val ⇒ famEx c r0 (σ a))) : y = DA ∨ y = DB := by
  obtain ⟨σ', -, hs⟩ := famEx_values c coreOK fnHyp X y r0 (σ a) ⟨DA, stepByA⟩ hy
  exact step_inv hs

/-! ## Neither instance alone is entailed -/

/-- `has_model_choice` at the steps of `Step` less the one from X to `w`, given a step from X to
the other instance `v` by the substitution `σ v`. -/
theorem choice_of (v w : Config c) (zv : GroundTerm) (hvw : v ≠ w)
    (hagree : ∀ {τ : Subst}, PatVal c τ r0.lhs X.val → StepBy c r0 ((4, zv) :: τ) X v) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c w.val))) ∧
      ¬ (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c v.val))) := by
  let T : Config c → Config c → Prop := fun x y => Step c x y ∧ (x = X → y ≠ w)
  obtain ⟨M, i, I, hI, hT⟩ := has_model_choice c coreOK fnHyp T (fun _ _ h => h.1)
    (fun x y r τ hs hex => by
      rw [rule_eq hs.mem, r0_shape.2.2.2.2] at hex; cases hex)
    (fun x y r τ hs => by
      have hr := rule_eq hs.mem
      subst hr
      by_cases hx : x = X
      · subst hx
        refine ⟨v, (4, zv) :: τ, fun i hi => ?_, hagree hs.hmatch,
          step_iff_by.mpr ⟨_, _, hagree hs.hmatch⟩, fun _ => hvw⟩
        rw [r0_shape.2.2.2.2] at hi
        have hne : (i == 4) = false := beq_false_of_ne (by simpa using hi)
        show List.lookup i ((4, zv) :: τ) = List.lookup i τ
        rw [List.lookup_cons, hne]
      · exact ⟨y, τ, fun _ _ => rfl, hs, step_iff_by.mpr ⟨_, _, hs⟩, fun h => absurd h hx⟩)
  exact ⟨M, i, I, hI, Classical.not_not.mp fun hn => ((hT X w).mpr hn).2 rfl rfl,
    (hT X v).mp ⟨step_iff_by.mpr ⟨r0, (4, zv) :: σ a, hagree (matchX a)⟩, fun _ => hvw⟩⟩

/-- `(4, z) :: τ` agrees with `σ z` on the rule's variables where τ matches the left side at X. -/
theorem agree_cons {τ : Subst} (z : GroundTerm) (hm : PatVal c τ r0.lhs X.val) :
    ∀ j, j < 5 → (σ z).lookup j = ((4, z) :: τ).lookup j := fun j hj => by
  have hl := lookups hm
  match j, hj with
  | 0, _ => exact (hl 0 (by decide)).symm
  | 1, _ => exact (hl 1 (by decide)).symm
  | 2, _ => exact (hl 2 (by decide)).symm
  | 3, _ => exact (hl 3 (by decide)).symm
  | 4, _ => rfl

/-- **A model in which `c(a, b)` does not step to `d(b)`**, and does step to `d(a)`. -/
theorem choice_b : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
    (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c DB.val))) ∧
    ¬ (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c DA.val))) :=
  choice_of DA DB a DA_ne fun hm =>
    stepBy_of_agree a (by decide +kernel) (by decide +kernel) (agree_cons a hm) DA rfl

/-- **A model in which `c(a, b)` does not step to `d(a)`**, and does step to `d(b)`. -/
theorem choice_a : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
    (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c DA.val))) ∧
    ¬ (I ⊧ᴵ (den c X.val ⇒ ∼ KoreAML.sNext (den c DB.val))) :=
  choice_of DB DA b (fun h => DA_ne h.symm) fun hm =>
    stepBy_of_agree b (by decide +kernel) (by decide +kernel) (agree_cons b hm) DB rfl

/-- info: 'SvRewriteStep.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_inv
/-- info: 'SvRewriteStep.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound
/-- info: 'SvRewriteStep.famEx_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms famEx_iff
/-- info: 'SvRewriteStep.choice_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms choice_a
/-- info: 'SvRewriteStep.choice_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms choice_b

end SvRewriteStep
