/-
  `StepDecided` is what `complete_at` reads at a configuration, and a configuration whose step
  reads an evaluation with no result is outside it. Run from the package root:
  `lake env lean test/StepDecidedLoop.lean`.

  The configuration is `<k> K </k>` with the generated counter. One function and one rule:
  - `loop : Int → Bool`, `loop(X) = loop(X)`: `Eval` has no derivation of `loop(0)`
    (`loop_none`), so the term `loop(0)` has no result (`req_none`);
  - `r`: `<k> X </k> <generatedCounter> N </generatedCounter> => <k> X </k> <generatedCounter> 1 </generatedCounter>
    requires loop(0)`.
  `coreOK` holds. At `<k> . </k> <generatedCounter> 0 </generatedCounter>` the rule matches and its
  `requires` has no result: `Step` gives no successor (`A_stuck`) and the configuration is not
  `StepDecided` (`A_not_decided`), so `complete_at` says nothing there. The theory does not settle
  `loop(0)`: the equation `loop(X) = loop(X)` holds whatever value an interpretation gives it, and
  where it gives `true` the rule gives A a successor; so `⟦A⟧ → ◦⊥` is not expected to be entailed
  although `Step` gives no successor. That interpretation is not built here.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace StepDecidedLoop

open Faithful.UndefRhsWitness (kIds cellSorts cellCtors cellSubsorts)

/-- `loop`, numbered after the four cell symbols. -/
def L : Sym := nRegSyms + 4

/-- `loop(X) = loop(X)`. -/
def clLoop : Clause := ⟨[Srt.int], [.var 0], none, .app L [.var 0], none, 50, false, [], .top, .top⟩

def fLoop : Fn := ⟨L, [Srt.int], Srt.bool, [clLoop], false⟩

def lhs : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]]
def rhs : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.dv Srt.int (.int 1)]]

/-- `loop(0)`. -/
def req : Term := .app L [.dv Srt.int (.int 0)]

def r : Rule := { vars := [Srt.k, Srt.int], lhs := lhs, req := some req, rhs := rhs, ens := none, prio := 50 }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblloop"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fLoop]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [r] }

theorem coreOK : c.coreOK = true := by decide_cheap

def i0 : GroundTerm := .dv Srt.int (.int 0)

/-- **`loop` has no result at 0**: its clause applies there and calls `loop` at 0 again. -/
theorem loop_none {res : Option GroundTerm} : ¬ Eval c L [i0] res := by
  intro hv
  have hlook : c.lookupFn L = some fLoop := rfl
  have hct : c.isCtor L = false := by decide +kernel
  exact Eval.rec (c := c)
    (motive_1 := fun f vs _ _ => f = L → vs = [i0] → False)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun σ t _ _ => t = .app L [.var 0] → σ.lookup 0 = some i0 → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True) (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ _ _ _} hfn hmem _ hmatch _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clLoop] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases hmatch with
      | cons h1 _ => cases h1 with | var hl => exact ihrhs rfl hl)
    (fun hfn hnone _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      cases hnone clLoop (by simp [fLoop]) with
      | intro h =>
        have hσ : c.WellSorted [Srt.int] [(0, i0)] := by
          intro i s hi
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨i0, rfl, by decide +kernel⟩
          | succ i => simp at hi
        cases h [(0, i0)] (fun i _ => hσ i) (.cons (.var rfl) .nil) with
        | intro ht _ _ => cases ht
        | pre hp => exact absurd (Holds.top_eq hp) (by simp))
    (fun {_ _ _ _ _ _ _} hfn hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clLoop] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases ht)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clLoop] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact hne rfl)
    (fun {_ _ _ _ _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clLoop] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact hne rfl)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    (fun h _ => by cases h) (fun h _ => by cases h) (fun _ _ => fun h _ => by cases h)
    (fun hk _ _ => fun h _ => by cases h; rw [hct] at hk; cases hk)
    (fun _ hhk _ _ _ _ => fun h _ => by cases h; exact absurd hhk (by decide +kernel))
    (fun _ _ hp _ _ _ => fun h _ => by cases h; exact absurd hp (by decide +kernel))
    (fun _ _ hts hvs _ _ _ ihf => fun h h0 => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [h0] at hvs
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        exact ihf rfl hvs.symm)
    (fun _ _ hts hvs _ _ => fun h h0 => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [h0] at hvs
        simp [allSome] at hvs)
    (fun _ ho _ _ _ => fun h _ => by cases h; exact absurd ho (by decide +kernel))
    (fun _ ho _ _ _ _ _ _ _ => fun h _ => by cases h; exact absurd ho (by decide +kernel))
    trivial (fun _ _ _ _ => trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    hv rfl rfl

/-- **`loop(0)` has no result** under any σ. -/
theorem req_none (σ : Subst) (res : Option GroundTerm) : ¬ EvalTerm c σ req res := by
  intro h
  cases h with
  | ctor hc _ => exact absurd hc (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons h1 h2 =>
      cases h2; cases h1
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
      subst hvs
      exact loop_none hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons h1 h2 => cases h2; cases h1; simp [allSome] at hvs
  | ovl _ ho _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho => exact absurd ho (by decide +kernel)

/-- `<k> . </k> <generatedCounter> 0 </generatedCounter>`. -/
def cfg : GroundTerm := .ctor topLabel [.ctor kIds.label [.ctor dotk []], .ctor counterLabel [int 0]]

theorem cfg_sort : c.sortOf cfg = some topCellSort := by decide +kernel

def A : Config c := ⟨cfg, cfg_sort⟩

def σ : Subst := [(0, .ctor dotk []), (1, int 0)]

theorem hσ : c.WellSorted [Srt.k, Srt.int] σ := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, rfl, by decide +kernel⟩
  | 1, h => cases h; exact ⟨_, rfl, by decide +kernel⟩

theorem hmatch : PatVal c σ lhs cfg :=
  .ctor (by decide +kernel) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil))
    (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil)) .nil))

/-- **A has no successor**: the one rule's `requires` has no result. -/
theorem A_stuck : ∀ y, ¬ Step c A y := by
  intro y h
  cases h with
  | rule r' mem σ' _ _ hreq _ _ _ _ _ =>
    simp only [c, List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    exact req_none σ' _ (hreq req rfl)

/-- **A is not `StepDecided`**: the rule, which no rule of a smaller priority blocks, matches A and
its `requires` has no result. -/
theorem A_not_decided : ¬ StepDecided c A.val := by
  intro hd
  obtain ⟨v, hv⟩ := ((hd r (by simp [c]) (fun r' hr' hlt => by
    simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _))).1 σ (hσ.at _) hmatch).1 req rfl
  exact req_none σ v hv

end StepDecidedLoop

end KCore

/-- info: 'KCore.StepDecidedLoop.coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.StepDecidedLoop.coreOK

/-- info: 'KCore.StepDecidedLoop.A_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.StepDecidedLoop.A_stuck

/-- info: 'KCore.StepDecidedLoop.A_not_decided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.StepDecidedLoop.A_not_decided
