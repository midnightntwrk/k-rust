/-
  The steps of the rewrite axiom with a set variable of test/SvRewriteStep.lean, under every
  interpretation of the parameters: K 7.1.337 kompile's text of fixture e3-setvar-rewrite
  (`rule <k> c(@S, @S) => d(@S) ... </k>`, `syntax Exp ::= a() | b() | c(Exp, Exp) | d(Exp)`;
  `f2-examples/e3-setvar-rewrite.kompile.kore`), read by the reader, each statement over
  `c0.withHooks H` for every `H : HookParams`, `c0` the reading.
  Run from the package root: `lake env lean -j1 test/SvRewriteStepH.lean`.

  ## Why no statement depends on H
  An interpretation enters evaluation in three places: a parameter symbol without a registry hook
  (`Semantics.paramVal`), an interpreted symbol at a silent point (`Semantics.hookRes`), and the
  sort of an open generator's application (`Semantics.sortOf`). The text declares no function and
  no parameter (`fns_nil`, `noRaw0`), and the rule's sides apply constructors only (`syms_ok`), so
  matching and evaluation read no hook, and every value has the sort the parsed data gives it
  (`sortOf_eq`). The proofs are those of test/SvRewriteStep.lean with the semantics `c0.withHooks H`.

  The reader reads sentence 104 through its instances at one element per occurrence: the rule `r0`,
  `c(L0, L1) => d(?R0)`, the left occurrences the variables 0 and 1, the right one the existential
  variable 4, with `post := R0 ∈ L0 ∨ R0 ∈ L1` (`r0_shape`); test/TieE3SetvarRewrite.lean ties Γ's
  item of the rule to the sentence (`rule_from_text_sig`).

  - `step_iff H`: the `Step` successors of `<k> c(a, b) </k>` (`X H`) are exactly `<k> d(a) </k>` and
    `<k> d(b) </k>` (`DA H`, `DB H`): `post` puts R0 among the matched elements.
  - `sound H`: in every model of `Γc`, X has a successor among the instances of the application
    (`famEx`), and `d(a)` and `d(b)` are both instances (`sound_at`).
  - `famEx_iff H`: a value the instances hold in every model of `Γc` is `d(a)` or `d(b)`
    (`famEx_values`, then `step_inv`).
  - `choice_a H`, `choice_b H`: by `has_model_choice` at the steps of `Step` less the one from X to
    `d(a)` (to `d(b)`), a model of `Γc` with the step's closure in which X does not step to `d(a)`
    (to `d(b)`) and does step to the other. So, a and b distinct, the theory entails neither step
    alone: it entails that X steps to `d(a)` or `d(b)`, as the sentence at the set `{a, b}` says.
    Each of the two is a model of sentence 104 as written: every model of `Γc` with the step's
    closure is, for every H (test/TieE3SetvarRewrite.lean, `rule_in_step_models`, on the same text).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace SvRewriteStepH

definition_of defn from "f2-examples/e3-setvar-rewrite.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

/-! The conditions of the parsed data that the proofs read do not read the interpretation. -/
theorem isCtor_wh_svh (H : HookParams) (f : Sym) : (c0.withHooks H).isCtor f = c0.isCtor f := rfl
theorem rules_wh_svh (H : HookParams) : (c0.withHooks H).rules = c0.rules := rfl
theorem fns_wh_svh (H : HookParams) : (c0.withHooks H).fns = c0.fns := rfl
theorem params_wh_svh (H : HookParams) : (c0.withHooks H).params = c0.params := rfl
theorem ctorHeaded_wh_svh (H : HookParams) (t : Term) : ctorHeaded (c0.withHooks H) t = ctorHeaded c0 t := rfl

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_svh, rules_wh_svh, fns_wh_svh, params_wh_svh, ctorHeaded_wh_svh]; decide +kernel))

def sExp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symC : Sym := 387
def symD : Sym := 388

theorem names_ok : c0.sortName sExp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symA = "Lbla" ∧ c0.symName symB = "Lblb" ∧ c0.symName symC = "Lblc" ∧
    c0.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ (c0.withHooks H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ (c0.withHooks H).rules) : r = r0 := by
  rw [rules_wh_svh] at hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c0.rules.length = 1 := by decide +kernel
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

theorem prios : ∀ r ∈ (c0.withHooks H).rules, r.prio = 50 := by whd

theorem fns_nil : (c0.withHooks H).fns = [] := by whd
theorem noRaw : ∀ k ∈ (c0.withHooks H).params, k.raw = false := by whd
theorem noWitness : ∀ r ∈ (c0.withHooks H).rules, r.needsWitness (c0.withHooks H) = false := by
  intro r hr
  rw [rule_eq hr]
  have h : r0.reqOpen = false := by decide +kernel
  simp only [Rule.needsWitness, h, Bool.false_and]
theorem lhs_vars : ∀ j ∈ varOccs r0.lhs, j < 4 := by decide +kernel
theorem rhs_vars : ∀ j ∈ varOccs r0.rhs, j < 5 := by decide +kernel

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧
    (c0.withHooks H).isCtor kseq = true ∧ (c0.withHooks H).isCtor dotk = true ∧
    (c0.withHooks H).isCtor symA = true ∧ (c0.withHooks H).isCtor symB = true ∧
    (c0.withHooks H).isCtor symC = true ∧ (c0.withHooks H).isCtor symD = true := by
  whd

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false := by
  decide +kernel

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
def dk : GroundTerm := .ctor dotk []
def a : GroundTerm := .ctor symA []
def b : GroundTerm := .ctor symB []

/-- `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, dk]], ctr]

/-- `<k> c(a, b) </k>`. -/
def X (H : HookParams) : Config (c0.withHooks H) := ⟨cfg (.ctor symC [a, b]), by whd⟩
/-- `<k> d(a) </k>` and `<k> d(b) </k>`. -/
def DA (H : HookParams) : Config (c0.withHooks H) := ⟨cfg (.ctor symD [a]), by whd⟩
def DB (H : HookParams) : Config (c0.withHooks H) := ⟨cfg (.ctor symD [b]), by whd⟩

theorem DA_ne : DA H ≠ DB H := fun h => absurd (congrArg Subtype.val h)
  (by show ¬ cfg (.ctor symD [a]) = cfg (.ctor symD [b]); decide +kernel)

theorem sortOf_a : (c0.withHooks H).sortOf a = some sExp := by whd
theorem sortOf_b : (c0.withHooks H).sortOf b = some sExp := by whd

/-! ## `Step` from `c(a, b)` to `d(a)` and to `d(b)` -/

/-- The match of the left side at X, with R0 := z. -/
def σ (z : GroundTerm) : Subst := [(0, a), (1, b), (2, dk), (3, ctr), (4, z)]

theorem prio_none {r' : Rule} (hr' : r' ∈ (c0.withHooks H).rules) (hlt : r'.prio < r0.prio) : False := by
  rw [prios r' hr', prios r0 (r0_mem (H := H))] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

theorem ws (z : GroundTerm) (hz : (c0.withHooks H).sortOf z = some sExp) :
    (c0.withHooks H).WellSorted r0.vars (σ z) := fun j s hs => by
  rw [r0_vars] at hs
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, sortOf_a⟩
  | 1, hs => cases hs; exact ⟨_, rfl, sortOf_b⟩
  | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
  | 3, hs => cases hs; exact ⟨_, rfl, by whd⟩
  | 4, hs => cases hs; exact ⟨_, rfl, hz⟩

theorem matchX (z : GroundTerm) : PatVal (c0.withHooks H) (σ z) r0.lhs (X H).val := by
  have hs := syms_ok (H := H)
  rw [r0_lhs]
  exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
    (.cons (.inj (.ctor hs.2.2.2.2.2.2.1 (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))

theorem evalD (z : GroundTerm) :
    EvalTerm (c0.withHooks H) (σ z) r0.rhs (some (cfg (.ctor symD [z]))) := by
  have hs := syms_ok (H := H)
  rw [r0_rhs]
  exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
    (.cons (.inj (.ctor hs.2.2.2.2.2.2.2 (.cons .var .nil))) (.cons .var .nil))) .nil))
    (.cons .var .nil))

/-- `post` at σ z: z is a or b. -/
theorem post_iff (z : GroundTerm) :
    Holds (c0.withHooks H) r0.vars.length (σ z) r0.post ((some z).isSome && sameResult (some z) (some a) ||
      (some z).isSome && sameResult (some z) (some b)) := by
  rw [r0_shape.2.2.2.1]
  exact .or (.mem .var .var) (.mem .var .var)

/-- **`c(a, b)` steps to `d(z)` by the rule, R0 := z**, for z among the matched elements. -/
theorem stepBy (z : GroundTerm) (hz : (c0.withHooks H).sortOf z = some sExp)
    (hpost : ((some z).isSome && sameResult (some z) (some a) ||
      (some z).isSome && sameResult (some z) (some b)) = true) (y : Config (c0.withHooks H))
    (hy : y.val = cfg (.ctor symD [z])) : StepBy (c0.withHooks H) r0 (σ z) (X H) y where
  mem := r0_mem
  hσ := ws z hz
  hmatch := matchX z
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := hy ▸ evalD z
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := hpost ▸ post_iff z
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

theorem stepByA : StepBy (c0.withHooks H) r0 (σ a) (X H) (DA H) :=
  stepBy a sortOf_a (by decide +kernel) (DA H) rfl
theorem stepByB : StepBy (c0.withHooks H) r0 (σ b) (X H) (DB H) :=
  stepBy b sortOf_b (by decide +kernel) (DB H) rfl

theorem step_a : Step (c0.withHooks H) (X H) (DA H) := step_iff_by.mpr ⟨r0, σ a, stepByA⟩
theorem step_b : Step (c0.withHooks H) (X H) (DB H) := step_iff_by.mpr ⟨r0, σ b, stepByB⟩

/-! ## Every step at `c(a, b)` is to `d(a)` or `d(b)` -/

/-- A substitution that matches the left side at X gives the four variables the values of `σ`. -/
theorem lookups {τ : Subst} (hm : PatVal (c0.withHooks H) τ r0.lhs (X H).val) :
    ∀ j, j < 4 → τ.lookup j = (σ a).lookup j := by
  have hsy := syms_ok (H := H)
  rw [r0_lhs] at hm
  obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.1 hm hsy.1
  injection hv with _ hv
  subst hv
  cases hs with
  | cons hk hs =>
    cases hs with
    | cons h3 _ =>
      obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.2.1 hk hsy.2.1
      injection hv with _ hv
      subst hv
      cases hs with
      | cons hq _ =>
        obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.2.2.1 hq hsy.2.2.1
        injection hv with _ hv
        subst hv
        cases hs with
        | cons hi hs =>
          cases hs with
          | cons h2 _ =>
            obtain ⟨w, hw, hwv⟩ := PatVal.inj_inv hi
            rw [PatVal.injNormal_of (by whd) hw] at hwv
            injection hwv with _ _ hwv
            subst hwv
            obtain ⟨-, vs, hv, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw hsy.2.2.2.2.2.2.1
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
    Holds (c0.withHooks H) r0.vars.length τ r0.post ((τ.lookup 4).isSome && sameResult (τ.lookup 4) (τ.lookup 0) ||
      (τ.lookup 4).isSome && sameResult (τ.lookup 4) (τ.lookup 1)) := by
  rw [r0_shape.2.2.2.1]
  exact .or (.mem .var .var) (.mem .var .var)

/-- A substitution that agrees with `σ z` on the rule's five variables gives the step to `d(z)`. -/
theorem stepBy_of_agree {τ : Subst} (z : GroundTerm) (hz : (c0.withHooks H).sortOf z = some sExp)
    (hpz : ((some z).isSome && sameResult (some z) (some a) ||
      (some z).isSome && sameResult (some z) (some b)) = true)
    (h : ∀ j, j < 5 → (σ z).lookup j = τ.lookup j) (y : Config (c0.withHooks H))
    (hy : y.val = cfg (.ctor symD [z])) : StepBy (c0.withHooks H) r0 τ (X H) y where
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
    have hp := post_at (H := H) τ
    rw [← h 4 (by decide), ← h 0 (by decide), ← h 1 (by decide)] at hp
    exact hpz ▸ hp
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- **Every step by the rule at `c(a, b)` is to `d(a)` or to `d(b)`**: `post` puts R0 among the
matched elements. -/
theorem step_inv {τ : Subst} {y : Config (c0.withHooks H)} (hs : StepBy (c0.withHooks H) r0 τ (X H) y) :
    y = DA H ∨ y = DB H := by
  have hl := lookups hs.hmatch
  have hd := (fnModel_of_fnHyp (coreOK (H := H)) (fnHyp (H := H))).1
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

/-- **The successors of `<k> c(a, b) </k>`** are exactly `<k> d(a) </k>` and `<k> d(b) </k>`. -/
theorem step_iff (H : HookParams) (y : Config (c0.withHooks H)) :
    Step (c0.withHooks H) (X H) y ↔ y = DA H ∨ y = DB H := by
  refine ⟨fun hs => ?_, fun h => ?_⟩
  · obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
    obtain rfl := rule_eq hb.mem
    exact step_inv hb
  · rcases h with rfl | rfl
    · exact step_a
    · exact step_b

/-! ## In every model of `Γc`, the instances are `d(a)` and `d(b)` -/

/-- **In every model of `Γc`, `<k> c(a, b) </k>` has a successor among the instances of the
application, and `d(a)` and `d(b)` are both instances** (`sound_at`: no competitor, no function).
The family at `σ a` and at `σ b` is one: the two substitutions differ at the existential variable
only. -/
theorem sound (H : HookParams) :
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (X H).val ⇒ KoreAML.sNext (famEx (c0.withHooks H) r0 (σ a)))) ∧
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (DA H).val ⇒ famEx (c0.withHooks H) r0 (σ a))) ∧
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (DB H).val ⇒ famEx (c0.withHooks H) r0 (σ a))) := by
  have hw : ∀ r' ∈ (c0.withHooks H).rules, r'.prio < r0.prio → r'.needsWitness (c0.withHooks H) = true →
      (∃ σ', PatVal (c0.withHooks H) σ' r'.lhs (X H).val) → r'.CondDecided (c0.withHooks H) :=
    fun r' hr' hlt _ _ => (prio_none hr' hlt).elim
  have hc : ∀ fn ∈ (c0.withHooks H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (c0.withHooks H) = true →
      cl.CondDecided (c0.withHooks H) :=
    fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  have hA := sound_at (c0.withHooks H) coreOK (X H) (DA H) r0 (σ a) stepByA hw hc
  have hB := sound_at (c0.withHooks H) coreOK (X H) (DB H) r0 (σ b) stepByB hw hc
  have heq : famEx (c0.withHooks H) r0 (σ b) = famEx (c0.withHooks H) r0 (σ a) := rfl
  exact ⟨hA.1, hA.2, heq ▸ hB.2⟩

/-- **A value the instances hold in every model of `Γc` is `d(a)` or `d(b)`** (`famEx_values`, then
`step_inv`). -/
theorem famEx_iff (H : HookParams) (y : Config (c0.withHooks H))
    (hy : Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) y.val ⇒ famEx (c0.withHooks H) r0 (σ a))) :
    y = DA H ∨ y = DB H := by
  obtain ⟨σ', -, hs⟩ := famEx_values (c0.withHooks H) coreOK fnHyp (X H) y r0 (σ a) ⟨DA H, stepByA⟩ hy
  exact step_inv hs

/-! ## Neither instance alone is entailed -/

/-- `has_model_choice` at the steps of `Step` less the one from X to `w`, given a step from X to
the other instance `v` by the substitution `σ v`. -/
theorem choice_of (v w : Config (c0.withHooks H)) (zv : GroundTerm) (hvw : v ≠ w)
    (hagree : ∀ {τ : Subst}, PatVal (c0.withHooks H) τ r0.lhs (X H).val →
      StepBy (c0.withHooks H) r0 ((4, zv) :: τ) (X H) v) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧
      (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) w.val))) ∧
      ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) v.val))) := by
  let T : Config (c0.withHooks H) → Config (c0.withHooks H) → Prop :=
    fun x y => Step (c0.withHooks H) x y ∧ (x = X H → y ≠ w)
  obtain ⟨M, i, I, hI, hT⟩ := has_model_choice (c0.withHooks H) coreOK fnHyp T (fun _ _ h => h.1)
    (fun x y r τ hs hex => by
      rw [rule_eq hs.mem, r0_shape.2.2.2.2] at hex; cases hex)
    (fun x y r τ hs => by
      have hr := rule_eq hs.mem
      subst hr
      by_cases hx : x = X H
      · subst hx
        refine ⟨v, (4, zv) :: τ, fun i hi => ?_, hagree hs.hmatch,
          step_iff_by.mpr ⟨_, _, hagree hs.hmatch⟩, fun _ => hvw⟩
        rw [r0_shape.2.2.2.2] at hi
        have hne : (i == 4) = false := beq_false_of_ne (by simpa using hi)
        show List.lookup i ((4, zv) :: τ) = List.lookup i τ
        rw [List.lookup_cons, hne]
      · exact ⟨y, τ, fun _ _ => rfl, hs, step_iff_by.mpr ⟨_, _, hs⟩, fun h => absurd h hx⟩)
  exact ⟨M, i, I, hI, Classical.not_not.mp fun hn => ((hT (X H) w).mpr hn).2 rfl rfl,
    (hT (X H) v).mp ⟨step_iff_by.mpr ⟨r0, (4, zv) :: σ a, hagree (matchX a)⟩, fun _ => hvw⟩⟩

/-- `(4, z) :: τ` agrees with `σ z` on the rule's variables where τ matches the left side at X. -/
theorem agree_cons {τ : Subst} (z : GroundTerm) (hm : PatVal (c0.withHooks H) τ r0.lhs (X H).val) :
    ∀ j, j < 5 → (σ z).lookup j = ((4, z) :: τ).lookup j := fun j hj => by
  have hl := lookups hm
  match j, hj with
  | 0, _ => exact (hl 0 (by decide)).symm
  | 1, _ => exact (hl 1 (by decide)).symm
  | 2, _ => exact (hl 2 (by decide)).symm
  | 3, _ => exact (hl 3 (by decide)).symm
  | 4, _ => rfl

/-- **A model in which `c(a, b)` does not step to `d(b)`**, and does step to `d(a)`. -/
theorem choice_b (H : HookParams) : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧
    (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) (DB H).val))) ∧
    ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) (DA H).val))) :=
  choice_of (DA H) (DB H) a DA_ne fun hm =>
    stepBy_of_agree a sortOf_a (by decide +kernel) (agree_cons a hm) (DA H) rfl

/-- **A model in which `c(a, b)` does not step to `d(a)`**, and does step to `d(b)`. -/
theorem choice_a (H : HookParams) : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧
    (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) (DA H).val))) ∧
    ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) (DB H).val))) :=
  choice_of (DB H) (DA H) b (fun h => DA_ne h.symm) fun hm =>
    stepBy_of_agree b sortOf_b (by decide +kernel) (agree_cons b hm) (DB H) rfl

/-- info: 'SvRewriteStepH.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'SvRewriteStepH.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound
/-- info: 'SvRewriteStepH.famEx_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms famEx_iff
/-- info: 'SvRewriteStepH.choice_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms choice_a
/-- info: 'SvRewriteStepH.choice_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms choice_b

end SvRewriteStepH

#check @SvRewriteStepH.step_iff
#check @SvRewriteStepH.sound
#check @SvRewriteStepH.famEx_iff
#check @SvRewriteStepH.choice_a
#check @SvRewriteStepH.choice_b
