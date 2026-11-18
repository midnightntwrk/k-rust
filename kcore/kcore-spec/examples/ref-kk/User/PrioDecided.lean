/-
  kore.k's `requires` beside an `[owise]` equation have results at `HookParams.none`
  (`KK.prioDecided : PrioDecided c₀`), and `leq` has a Bool result at every argument list of its
  sorts (`KK.leq_result`).

  `PrioDecided` asks, of each clause of a priority below another clause of its function, that its
  `requires` have a result and its predicate a truth value wherever its patterns match under a
  substitution well sorted on the variables of its left side. Every clause's predicate is `\top`.
  A term of variables, domain values, injections, constructors and hooked symbols has a result
  under every substitution: a hooked symbol has a meaning at every argument list, a result or none.
  The `requires` of kore.k beside an `[owise]` equation are such terms, but for calls of `leq` (in
  `m-inj-sub`) and of `isElem` (in `mc-head`, `mc-frame`, `mc-choose` and `mc-split`) on variables
  of their argument sorts (`Prio.okTerm`, `Prio.okTerm_res`; checked over every clause by
  `Prio.prioReqOK_c₀`), which have Bool results:

  - `leq(A, B, S)` with A, B Ints and S a table: `leq-refl` where A is B, else `leq-up`, whose
    right side is `above(A, B, S, S, S)`; `above(A, B, T, All, F)` has a Bool result by induction
    on the fuel F and then on the table T, a value of sort `Subs` being `.Subs` or
    `sub(X, Y, R)` (`subs_shape`): `above-nil` at `.Subs`, `above-dry` at the fuel `.Subs`,
    `above-hit` (its calls at the shorter fuel, and at the same fuel and the shorter table) where X
    is A, `above-miss` (the shorter table) where it is not.
  - `isElem(V)` with V a `Term`: `true` where `elem-el` or `elem-kv` applies, else `elem-not`
    decides, both failing, and gives `false`.
-/
import User.Coherent

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK

open KCore KCore.Det RefKk

namespace Prio

/-! ## Hooked symbols -/

/-- A hooked symbol has a meaning at every argument list. -/
theorem hookRes_some {c : Semantics} {f : Sym} (hk : isHook f = true) (vs : List GroundTerm) :
    ∃ r, c.hookRes f vs = some r := by
  have hs : (hook f vs).isSome = true := by
    unfold isHook hook at *
    cases h : hookTrie.find f <;> simp_all
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  unfold Semantics.hookRes
  split
  · exact ⟨_, by rw [hr]; rfl⟩
  · exact ⟨r, hr⟩

/-- A hooked symbol's application has a result where its arguments have results. -/
theorem evalTerm_hookApp {c : Semantics} {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hc : c.isCtor f = false) (hk : isHook f = true) (hts : EvalTerms c σ ts rs) :
    ∃ r, EvalTerm c σ (.app f ts) r := by
  cases ha : allSome rs with
  | none => exact ⟨none, .hook hc hk hts (fun vs h => by rw [ha] at h; cases h) (fun _ => rfl)⟩
  | some vs =>
    obtain ⟨r, hr⟩ := hookRes_some (c := c) hk vs
    exact ⟨r, .hook hc hk hts (fun vs' h => by rw [ha] at h; cases h; exact hr)
      (fun h => by rw [ha] at h; cases h)⟩

/-! ## The values of `Int` and `Subs` -/

theorem hshapes : c₀.shapesOK = true := by decide +kernel

theorem hparams : c₀.params = [] := by kernel_rfl

theorem sort_int (a : Int) : c₀.sortOf (int a) = some 3 :=
  sortOf_dv.mpr ⟨by simp only [dvOK]; decide +kernel, rfl⟩

theorem sort_nil : c₀.sortOf (.ctor 405 []) = some 32 := by decide +kernel

/-- The constructors of sort `Subs`: `.Subs` and `sub(Int, Int, Subs)`. -/
theorem subs_ctors : ∀ k ∈ c₀.ctorSigs, k.result = 32 →
    (k.name = 405 ∧ k.args = []) ∨ (k.name = 442 ∧ k.args = [3, 3, 32]) := by decide +kernel

theorem subs_not_sub : ∀ p ∈ c₀.subsorts, p.2 ≠ 32 := by decide +kernel

theorem subs_collOf : c₀.collOf 32 = none := by decide +kernel

/-- **A value of sort `Subs`** is `.Subs` or `sub(X, Y, R)` of two Ints and a `Subs`. -/
theorem subs_shape {v : GroundTerm} (h : c₀.sortOf v = some 32) :
    v = .ctor 405 [] ∨ ∃ x y r, v = .ctor 442 [x, y, r] ∧ c₀.sortOf x = some 3 ∧ c₀.sortOf y = some 3 ∧
      c₀.sortOf r = some 32 := by
  cases v with
  | ctor f ts =>
    obtain ⟨k, hk, hts, hr⟩ := (c₀.sortOf_ctor_of_none hovls (by rw [hparams]; intro _ h; cases h)).mp h
    obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
    rcases subs_ctors k hkm hr.symm with ⟨hn, ha⟩ | ⟨hn, ha⟩
    · rw [ha] at hts
      rcases ts with _ | ⟨t, ts⟩
      · left; rw [← hkn, hn]
      · obtain ⟨s, ss, -, -, he⟩ := sortsOf_cons.mp hts; cases he
    · rw [ha] at hts
      rcases ts with _ | ⟨x, _ | ⟨y, _ | ⟨r, _ | ⟨w, ts⟩⟩⟩⟩
      · cases hts
      · obtain ⟨s, ss, -, h1, he⟩ := sortsOf_cons.mp hts; cases he; cases h1
      · obtain ⟨s, ss, -, h1, he⟩ := sortsOf_cons.mp hts; cases he
        obtain ⟨s, ss, -, h1, he⟩ := sortsOf_cons.mp h1; cases he; cases h1
      · obtain ⟨hx, h1⟩ := OvlLaws.sortsOf_cons_iff.mp hts
        obtain ⟨hy, h2⟩ := OvlLaws.sortsOf_cons_iff.mp h1
        obtain ⟨hr, -⟩ := OvlLaws.sortsOf_cons_iff.mp h2
        exact .inr ⟨x, y, r, by rw [← hkn, hn], hx, hy, hr⟩
      · obtain ⟨-, h1⟩ := OvlLaws.sortsOf_cons_iff.mp hts
        obtain ⟨-, h2⟩ := OvlLaws.sortsOf_cons_iff.mp h1
        obtain ⟨-, h3⟩ := OvlLaws.sortsOf_cons_iff.mp h2
        obtain ⟨s, ss, -, -, he⟩ := sortsOf_cons.mp h3; cases he
  | inj a b t =>
    obtain ⟨hab, -, -, rfl⟩ := sortOf_inj.mp h
    exact (subs_not_sub _ hab rfl).elim
  | dv s lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp h
    have h1 : (c₀.lib.carrier 32 == Srt.int) = false := by decide +kernel
    have h2 : (c₀.lib.carrier 32 == Srt.bool) = false := by decide +kernel
    have h3 : (c₀.lib.carrier 32 == Srt.kconfigVar || c₀.lib.carrier 32 == Srt.string ||
        c₀.lib.tokenSorts.contains (c₀.lib.carrier 32)) = false := by decide +kernel
    have h4 : (c₀.lib.carrier 32 == Srt.bytes || c₀.lib.byteSorts.contains (c₀.lib.carrier 32)) = false := by
      decide +kernel
    have h5 : (c₀.lib.carrier 32 == Srt.float) = false := by decide +kernel
    cases lit with
    | int _ => simp only [dvOK, h1] at hok; cases hok
    | bool _ => simp only [dvOK, h2] at hok; cases hok
    | tok t => simp only [dvOK, h3, h4, Bool.false_and, Bool.or_false] at hok; cases hok
    | float _ _ _ => simp only [dvOK, h5, Bool.false_and] at hok; cases hok
  | map s es =>
    obtain ⟨k, _, hk, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [subs_collOf] at hk; cases hk
  | set s es =>
    obtain ⟨k, hk, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [subs_collOf] at hk; cases hk
  | list s es =>
    obtain ⟨k, hk, -, -, rfl⟩ := sortOf_listS.mp h
    rw [subs_collOf] at hk; cases hk

/-- Induction over the values of sort `Subs`. -/
theorem subs_ind {P : GroundTerm → Prop} (h0 : P (.ctor 405 []))
    (h1 : ∀ x y r, c₀.sortOf x = some 3 → c₀.sortOf y = some 3 → c₀.sortOf r = some 32 →
      c₀.sortOf (.ctor 442 [x, y, r]) = some 32 → P r → P (.ctor 442 [x, y, r])) :
    ∀ n v, sizeOf v < n → c₀.sortOf v = some 32 → P v
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, v, hn, hs => by
    rcases subs_shape hs with rfl | ⟨x, y, r, rfl, hx, hy, hr⟩
    · exact h0
    · exact h1 x y r hx hy hr hs (subs_ind h0 h1 n r (by simp at hn; omega) hr)

theorem int_shape {v : GroundTerm} (h : c₀.sortOf v = some 3) : ∃ a, v = int a := shape_int hshapes h

/-! ## Evaluation helpers -/

theorem evalVar {σ : Subst} {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) :
    EvalTerm c₀ σ (.var i) (some v) := h ▸ .var

/-- A hooked symbol at the values of its arguments. -/
theorem evalHook {σ : Subst} {f : Sym} {ts : List Term} {vs : List GroundTerm} {r : GroundTerm}
    (hts : EvalTerms c₀ σ ts (vs.map some)) (hh : hook f vs = some (some r))
    (hc : c₀.isCtor f = false := by decide +kernel) (hk : isHook f = true := by decide +kernel) :
    EvalTerm c₀ σ (.app f ts) (some r) :=
  .hook hc hk hts (fun vs' h => by rw [KCore.Det.allSome_map_some] at h; cases h; exact Semantics.hookRes_of_value hh)
    (fun h => by rw [KCore.Det.allSome_map_some] at h; cases h)

/-- A call of a function of the semantics at the values of its arguments. -/
theorem evalCall {σ : Subst} {f : Sym} {ts : List Term} {vs : List GroundTerm} {r : Option GroundTerm}
    (hts : EvalTerms c₀ σ ts (vs.map some)) (hE : Eval c₀ f vs r)
    (hc : c₀.isCtor f = false := by decide +kernel) (hk : isHook f = false := by decide +kernel)
    (hp : c₀.isParam f = false := by decide +kernel) : EvalTerm c₀ σ (.app f ts) r :=
  .call hc hk hts (KCore.Det.allSome_map_some vs) hE hp

/-- A clause of a function all of whose clauses are of one priority, without existential variables,
`ensures` and predicates, decides where it applies: its right-hand side's result is the function's. -/
theorem eval_of_clause {f : Sym} {fn : Fn} (hlk : c₀.lookupFn f = some fn) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hp : ∀ cl' ∈ fn.clauses, ¬ cl'.prio < cl.prio) (hx : cl.exs = []) (he : cl.ens = none)
    (hpre : cl.pre = .top) (hpost : cl.post = .top) {σ : Subst} {vs : List GroundTerm} {r : Option GroundTerm}
    (hσ : c₀.WellSorted cl.vars σ) (hm : PatVals c₀ σ cl.pats vs)
    (hq : ∀ t, cl.req = some t → EvalTerm c₀ σ t (some (bool true))) (hr : EvalTerm c₀ σ cl.rhs r) :
    Eval c₀ f vs r :=
  .clause hlk hcl hσ hm hq (hpre ▸ .top) (fun cl' h _ hlt => absurd hlt (hp cl' h)) hx hr
    (fun t ht => by rw [he] at ht; cases ht) (hpost ▸ .top)

theorem hook_intEq_int (x y : Int) : hook intEq [int x, int y] = some (some (bool (decide (x = y)))) := rfl
theorem hook_intNe_int (x y : Int) : hook intNe [int x, int y] = some (some (bool (decide (x ≠ y)))) := rfl
theorem hook_boolOr_bool (a b : Bool) : hook boolOr [bool a, bool b] = some (some (bool (a || b))) := rfl

/-! ## `above` and `leq` -/

/-- The clause of `above` from kore.k's rule `above-hit`. -/
def aboveHit : Clause :=
  { vars := [3, 3, 3, 3, 32, 32, 3, 3, 32, 32],
    pats := [.var 0, .var 1, .app 442 [.var 2, .var 3, .var 4], .var 5, .as (.app 442 [.var 6, .var 7, .var 8]) 9],
    req := some (.app 23 [.var 2, .var 0]),
    rhs := .app 6 [.app 6 [.app 23 [.var 3, .var 1], .app 446 [.var 3, .var 1, .var 5, .var 5, .var 8]],
      .app 446 [.var 0, .var 1, .var 4, .var 5, .var 9]],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `above` from kore.k's rule `above-miss`. -/
def aboveMiss : Clause :=
  { vars := [3, 3, 3, 3, 32, 32, 3, 3, 32, 32],
    pats := [.var 0, .var 1, .app 442 [.var 2, .var 3, .var 4], .var 5, .as (.app 442 [.var 6, .var 7, .var 8]) 9],
    req := some (.app 24 [.var 2, .var 0]),
    rhs := .app 446 [.var 0, .var 1, .var 4, .var 5, .var 9],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `above` from kore.k's rule `above-nil`. -/
def aboveNil : Clause :=
  { vars := [3, 3, 32, 32],
    pats := [.var 0, .var 1, .app 405 [], .var 2, .var 3],
    req := none,
    rhs := .dv 2 (.bool false),
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `above` from kore.k's rule `above-dry`. -/
def aboveDry : Clause :=
  { vars := [3, 3, 3, 3, 32, 32],
    pats := [.var 0, .var 1, .app 442 [.var 2, .var 3, .var 4], .var 5, .app 405 []],
    req := none,
    rhs := .dv 2 (.bool false),
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- `above` (symbol 446) as the definition's semantics holds it. -/
def fnAbove : Fn :=
  { label := 446, args := [3, 3, 32, 32, 32], result := 2,
    clauses := [aboveHit, aboveMiss, aboveNil, aboveDry], total := false }

/-- The clause of `leq` from kore.k's rule `leq-up`. -/
def leqUp : Clause :=
  { vars := [3, 3, 32],
    pats := [.var 0, .var 1, .var 2],
    req := some (.app 24 [.var 0, .var 1]),
    rhs := .app 446 [.var 0, .var 1, .var 2, .var 2, .var 2],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `leq` from kore.k's rule `leq-refl`. -/
def leqRefl : Clause :=
  { vars := [3, 3, 32],
    pats := [.var 0, .var 1, .var 2],
    req := some (.app 23 [.var 0, .var 1]),
    rhs := .dv 2 (.bool true),
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- `leq` (symbol 482) as the definition's semantics holds it. -/
def fnLeq : Fn :=
  { label := 482, args := [3, 3, 32], result := 2, clauses := [leqUp, leqRefl], total := false }

theorem lookup_above : c₀.lookupFn 446 = some fnAbove := by kernel_rfl
theorem lookup_leq : c₀.lookupFn 482 = some fnLeq := by kernel_rfl

theorem above_prio : ∀ cl ∈ fnAbove.clauses, ∀ cl' ∈ fnAbove.clauses, ¬ cl'.prio < cl.prio := by
  have h : ∀ cl ∈ fnAbove.clauses, cl.prio = 50 := by
    intro cl h
    simp only [fnAbove, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  intro cl hcl cl' hcl'
  rw [h cl hcl, h cl' hcl']
  exact Nat.lt_irrefl 50

theorem leq_prio : ∀ cl ∈ fnLeq.clauses, ∀ cl' ∈ fnLeq.clauses, ¬ cl'.prio < cl.prio := by
  have h : ∀ cl ∈ fnLeq.clauses, cl.prio = 50 := by
    intro cl h
    simp only [fnLeq, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  intro cl hcl cl' hcl'
  rw [h cl hcl, h cl' hcl']
  exact Nat.lt_irrefl 50

theorem mem_hit : aboveHit ∈ fnAbove.clauses := List.mem_cons_self
theorem mem_miss : aboveMiss ∈ fnAbove.clauses := List.mem_cons_of_mem _ List.mem_cons_self
theorem mem_nil : aboveNil ∈ fnAbove.clauses := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_dry : aboveDry ∈ fnAbove.clauses :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem mem_up : leqUp ∈ fnLeq.clauses := List.mem_cons_self
theorem mem_refl : leqRefl ∈ fnLeq.clauses := List.mem_cons_of_mem _ List.mem_cons_self

end Prio

open Prio

/-- **`above` has a Bool result at every argument list of its sorts**, by induction on the fuel
and then on the table. -/
theorem above_res : ∀ F, c₀.sortOf F = some 32 → ∀ T, c₀.sortOf T = some 32 → ∀ All, c₀.sortOf All = some 32 →
    ∀ a b : Int, ∃ x, Eval c₀ 446 [int a, int b, T, All, F] (some (bool x)) := by
  intro F hF
  refine subs_ind (P := fun F => ∀ T, c₀.sortOf T = some 32 → ∀ All, c₀.sortOf All = some 32 →
    ∀ a b : Int, ∃ x, Eval c₀ 446 [int a, int b, T, All, F] (some (bool x))) ?_ ?_ _ F (Nat.lt_succ_self _) hF
  · -- the fuel `.Subs`: `above-nil` or `above-dry`
    intro T hT All hAll a b
    rcases subs_shape hT with rfl | ⟨x, y, R, rfl, hx, hy, hR⟩
    · refine ⟨false, eval_of_clause lookup_above (cl := aboveNil) mem_nil (above_prio _ mem_nil)
        rfl rfl rfl rfl (σ := [(0, int a), (1, int b), (2, All), (3, .ctor 405 [])]) ?_
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel) .nil) (.cons (.var rfl) (.cons (.var rfl) .nil)))))
        (fun _ h => by cases h) .dv⟩
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, sort_int a⟩
      | 1, hs => cases hs; exact ⟨_, rfl, sort_int b⟩
      | 2, hs => cases hs; exact ⟨_, rfl, hAll⟩
      | 3, hs => cases hs; exact ⟨_, rfl, sort_nil⟩
      | _ + 4, hs => simp [aboveNil] at hs
    · refine ⟨false, eval_of_clause lookup_above (cl := aboveDry) mem_dry (above_prio _ mem_dry)
        rfl rfl rfl rfl (σ := [(0, int a), (1, int b), (2, x), (3, y), (4, R), (5, All)]) ?_
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
          (.cons (.var rfl) (.cons (.ctor (by decide +kernel) .nil) .nil)))))
        (fun _ h => by cases h) .dv⟩
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, sort_int a⟩
      | 1, hs => cases hs; exact ⟨_, rfl, sort_int b⟩
      | 2, hs => cases hs; exact ⟨_, rfl, hx⟩
      | 3, hs => cases hs; exact ⟨_, rfl, hy⟩
      | 4, hs => cases hs; exact ⟨_, rfl, hR⟩
      | 5, hs => cases hs; exact ⟨_, rfl, hAll⟩
      | _ + 6, hs => simp [aboveDry] at hs
  · intro p q F' hp hq hF' hFs ih T hT
    refine subs_ind (P := fun T => ∀ All, c₀.sortOf All = some 32 → ∀ a b : Int,
      ∃ x, Eval c₀ 446 [int a, int b, T, All, .ctor 442 [p, q, F']] (some (bool x))) ?_ ?_ _ T (Nat.lt_succ_self _) hT
    · -- the table `.Subs`: `above-nil`
      intro All hAll a b
      refine ⟨false, eval_of_clause lookup_above (cl := aboveNil) mem_nil (above_prio _ mem_nil)
        rfl rfl rfl rfl (σ := [(0, int a), (1, int b), (2, All), (3, .ctor 442 [p, q, F'])]) ?_
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel) .nil) (.cons (.var rfl) (.cons (.var rfl) .nil)))))
        (fun _ h => by cases h) .dv⟩
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, sort_int a⟩
      | 1, hs => cases hs; exact ⟨_, rfl, sort_int b⟩
      | 2, hs => cases hs; exact ⟨_, rfl, hAll⟩
      | 3, hs => cases hs; exact ⟨_, rfl, hFs⟩
      | _ + 4, hs => simp [aboveNil] at hs
    · intro x y R hx hy hR hTs ihT All hAll a b
      obtain ⟨x', rfl⟩ := int_shape hx
      obtain ⟨y', rfl⟩ := int_shape hy
      have hm : ∀ σ : Subst, σ.lookup 0 = some (int a) → σ.lookup 1 = some (int b) → σ.lookup 2 = some (int x') →
          σ.lookup 3 = some (int y') → σ.lookup 4 = some R → σ.lookup 5 = some All → σ.lookup 6 = some p →
          σ.lookup 7 = some q → σ.lookup 8 = some F' → σ.lookup 9 = some (.ctor 442 [p, q, F']) →
          PatVals c₀ σ aboveHit.pats [int a, int b, .ctor 442 [int x', int y', R], All, .ctor 442 [p, q, F']] :=
        fun σ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
          .cons (.var h0) (.cons (.var h1) (.cons (.ctor (by decide +kernel) (.cons (.var h2) (.cons (.var h3) (.cons (.var h4) .nil))))
            (.cons (.var h5) (.cons (.as (.ctor (by decide +kernel) (.cons (.var h6) (.cons (.var h7) (.cons (.var h8) .nil)))) h9) .nil))))
      let σ : Subst := [(0, int a), (1, int b), (2, int x'), (3, int y'), (4, R), (5, All), (6, p), (7, q), (8, F'),
        (9, .ctor 442 [p, q, F'])]
      have hw : c₀.WellSorted aboveHit.vars σ := by
        intro i s hs
        match i, hs with
        | 0, hs => cases hs; exact ⟨_, rfl, sort_int a⟩
        | 1, hs => cases hs; exact ⟨_, rfl, sort_int b⟩
        | 2, hs => cases hs; exact ⟨_, rfl, sort_int x'⟩
        | 3, hs => cases hs; exact ⟨_, rfl, sort_int y'⟩
        | 4, hs => cases hs; exact ⟨_, rfl, hR⟩
        | 5, hs => cases hs; exact ⟨_, rfl, hAll⟩
        | 6, hs => cases hs; exact ⟨_, rfl, hp⟩
        | 7, hs => cases hs; exact ⟨_, rfl, hq⟩
        | 8, hs => cases hs; exact ⟨_, rfl, hF'⟩
        | 9, hs => cases hs; exact ⟨_, rfl, hFs⟩
        | _ + 10, hs => simp [aboveHit] at hs
      obtain ⟨w, hw'⟩ := ihT All hAll a b
      by_cases hxa : x' = a
      · -- `above-hit`
        subst hxa
        obtain ⟨u, hu⟩ := ih All hAll All hAll y' b
        refine ⟨(decide (y' = b) || u) || w, eval_of_clause lookup_above (cl := aboveHit) mem_hit
          (above_prio _ mem_hit) rfl rfl rfl rfl (σ := σ) hw (hm σ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) ?_ ?_⟩
        · intro t ht; cases ht
          have := evalHook (σ := σ) (f := intEq) (ts := [.var 2, .var 0]) (vs := [int x', int x'])
            (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intEq_int x' x')
          simpa using this
        · exact evalHook (vs := [bool (decide (y' = b) || u), bool w])
            (.cons (evalHook (vs := [bool (decide (y' = b)), bool u])
                (.cons (evalHook (vs := [int y', int b]) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intEq_int y' b))
                  (.cons (evalCall (vs := [int y', int b, All, All, F'])
                    (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil))))) hu) .nil))
                (hook_boolOr_bool _ _))
              (.cons (evalCall (vs := [int x', int b, R, All, .ctor 442 [p, q, F']])
                (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil))))) hw') .nil))
            (hook_boolOr_bool _ _)
      · -- `above-miss`
        refine ⟨w, eval_of_clause lookup_above (cl := aboveMiss) mem_miss
          (above_prio _ mem_miss) rfl rfl rfl rfl (σ := σ) hw (hm σ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) ?_ ?_⟩
        · intro t ht; cases ht
          have := evalHook (σ := σ) (f := intNe) (ts := [.var 2, .var 0]) (vs := [int x', int a])
            (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intNe_int x' a)
          simpa [hxa] using this
        · exact evalCall (vs := [int a, int b, R, All, .ctor 442 [p, q, F']])
            (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil))))) hw'

/-- **`leq` has a Bool result at every argument list of its sorts** (Int, Int, Subs): `leq-refl`
where the two Ints are one, else `leq-up` and `above`'s result (`above_res`). -/
theorem leq_result {x y s : GroundTerm} (hx : c₀.sortOf x = some 3) (hy : c₀.sortOf y = some 3)
    (hs : c₀.sortOf s = some 32) : ∃ b, Eval c₀ 482 [x, y, s] (some (bool b)) := by
  obtain ⟨a, rfl⟩ := int_shape hx
  obtain ⟨b, rfl⟩ := int_shape hy
  have hw : c₀.WellSorted [3, 3, 32] [(0, int a), (1, int b), (2, s)] := by
    intro i s' hs'
    match i, hs' with
    | 0, hs' => cases hs'; exact ⟨_, rfl, sort_int a⟩
    | 1, hs' => cases hs'; exact ⟨_, rfl, sort_int b⟩
    | 2, hs' => cases hs'; exact ⟨_, rfl, hs⟩
    | _ + 3, hs' => simp at hs'
  have hm : PatVals c₀ [(0, int a), (1, int b), (2, s)] [.var 0, .var 1, .var 2] [int a, int b, s] :=
    .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))
  by_cases hab : a = b
  · subst hab
    refine ⟨true, eval_of_clause lookup_leq (cl := leqRefl) mem_refl (leq_prio _ mem_refl)
      rfl rfl rfl rfl hw hm ?_ .dv⟩
    intro t ht; cases ht
    have := evalHook (σ := [(0, int a), (1, int a), (2, s)]) (f := intEq) (ts := [.var 0, .var 1])
      (vs := [int a, int a]) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intEq_int a a)
    simpa using this
  · obtain ⟨u, hu⟩ := above_res s hs s hs s hs a b
    refine ⟨u, eval_of_clause lookup_leq (cl := leqUp) mem_up (leq_prio _ mem_up)
      rfl rfl rfl rfl hw hm ?_ ?_⟩
    · intro t ht; cases ht
      have := evalHook (σ := [(0, int a), (1, int b), (2, s)]) (f := intNe) (ts := [.var 0, .var 1])
        (vs := [int a, int b]) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intNe_int a b)
      simpa [hab] using this
    · exact evalCall (vs := [int a, int b, s, s, s])
        (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil))))) hu

/-! ## `isElem` -/

namespace Prio

theorem mem_el : elemEl ∈ fnIsElem.clauses := List.mem_cons_self
theorem mem_kv : elemKv ∈ fnIsElem.clauses := List.mem_cons_of_mem _ List.mem_cons_self
theorem mem_not : elemNot ∈ fnIsElem.clauses := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- `isElem`'s equations of priority 50 have no clause of a smaller priority. -/
theorem isElem_prio50 {cl : Clause} (h : cl.prio = 50) : ∀ cl' ∈ fnIsElem.clauses, ¬ cl'.prio < cl.prio := by
  intro cl' h'
  simp only [fnIsElem, List.mem_cons, List.not_mem_nil, or_false] at h'
  rw [h]
  rcases h' with rfl | rfl | rfl <;> decide

/-- A clause of `isElem` of priority 50 that does not apply fails: it has no `requires`, and its
variables are those of its pattern. -/
theorem isElem_fails {cl : Clause} (hq : cl.req = none) (hp : cl.pre = .top) (hu : cl.univ = cl.leftVars)
    {v : GroundTerm} (hn : ¬ ∃ σ, cl.AppliesAt c₀ σ [v]) : Fails c₀ [v] cl := by
  refine fails_of_not_applies (fun _ _ _ => ⟨fun t ht => (by rw [hq] at ht; cases ht), true, ?_⟩)
    fun σ hσ hm hq' => hn ⟨σ, by rw [hu]; exact hσ, hm, hq'⟩
  rw [hp]; exact .top

end Prio

/-- **`isElem` has a Bool result at every value of sort `Term`**: `true` where `elem-el` or
`elem-kv` applies, else `false` by `elem-not`. -/
theorem isElem_result {v : GroundTerm} (hv : c₀.sortOf v = some 33) : ∃ b, Eval c₀ 478 [v] (some (bool b)) := by
  by_cases h : ∃ σ, elemEl.AppliesAt c₀ σ [v] ∨ elemKv.AppliesAt c₀ σ [v]
  · obtain ⟨σ, ha | ha⟩ := h
    · exact ⟨true, eval_of_clause lookup_isElem mem_el (isElem_prio50 rfl) rfl rfl rfl rfl
        ((wellSortedAt_univ rfl).mp ha.1) ha.2.1 ha.2.2.1 .dv⟩
    · exact ⟨true, eval_of_clause lookup_isElem mem_kv (isElem_prio50 rfl) rfl rfl rfl rfl
        ((wellSortedAt_univ rfl).mp ha.1) ha.2.1 ha.2.2.1 .dv⟩
  · have hel : Fails c₀ [v] elemEl := isElem_fails rfl rfl rfl fun ⟨σ, ha⟩ => h ⟨σ, .inl ha⟩
    have hkv : Fails c₀ [v] elemKv := isElem_fails rfl rfl rfl fun ⟨σ, ha⟩ => h ⟨σ, .inr ha⟩
    refine ⟨false, .clause lookup_isElem mem_not (σ := [(0, v)]) ?_ (.cons (.var rfl) .nil)
      (fun _ h => by cases h) .top (fun cl' h' _ _ => ?_) rfl .dv (fun _ h => by cases h) .top⟩
    · intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, hv⟩
      | _ + 1, hs => simp [elemNot] at hs
    · simp only [fnIsElem, List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl
      · exact hel
      · exact hkv
      · contradiction

/-! ## The `requires` beside an `[owise]` equation -/

namespace Prio

/-- A variable of the sort `s` among the variables `lv` the substitution is well sorted on. -/
def okVar (vars : List Srt) (lv : List Nat) (s : Srt) : Term → Bool
  | .var i => vars[i]? == some s && lv.contains i
  | _ => false

theorem okVar_val {vars : List Srt} {lv : List Nat} {s : Srt} {σ : Subst} {t : Term}
    (hw : c₀.WellSortedAt vars lv σ) (h : okVar vars lv s t = true) :
    ∃ i v, t = .var i ∧ σ.lookup i = some v ∧ c₀.sortOf v = some s := by
  cases t with
  | var i =>
    simp only [okVar, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    obtain ⟨v, hv, hs⟩ := hw i h.2 s h.1
    exact ⟨i, v, rfl, hv, hs⟩
  | _ => simp [okVar] at h

/-- The arguments of a call of `leq`: variables of the sorts Int, Int and `Subs`. -/
def okLeqArgs (vars : List Srt) (lv : List Nat) : List Term → Bool
  | [a, b, s] => okVar vars lv 3 a && okVar vars lv 3 b && okVar vars lv 32 s
  | _ => false

/-- The argument of a call of `isElem`: a variable of the sort `Term`. -/
def okElemArgs (vars : List Srt) (lv : List Nat) : List Term → Bool
  | [a] => okVar vars lv 33 a
  | _ => false

mutual
  /-- A term of variables, domain values, injections, constructors, hooked symbols, and calls of
  `leq` and `isElem` at variables of their argument sorts among `lv`. -/
  def okTerm (c : Semantics) (vars : List Srt) (lv : List Nat) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .inj _ _ t => okTerm c vars lv t
    | .as _ _ => false
    | .app f ts => (f == 482 && okLeqArgs vars lv ts) || (f == 478 && okElemArgs vars lv ts) ||
        ((c.isCtor f || isHook f) && okTerms c vars lv ts)
    termination_by structural t => t
  def okTerms (c : Semantics) (vars : List Srt) (lv : List Nat) : List Term → Bool
    | [] => true
    | t :: ts => okTerm c vars lv t && okTerms c vars lv ts
    termination_by structural ts => ts
end

mutual
  /-- **A term `okTerm` accepts has a result** under a substitution well sorted on `lv`. -/
  theorem okTerm_res {vars : List Srt} {lv : List Nat} {σ : Subst} (hw : c₀.WellSortedAt vars lv σ) :
      ∀ {t : Term}, okTerm c₀ vars lv t = true → ∃ r, EvalTerm c₀ σ t r
    | .var _, _ => ⟨_, .var⟩
    | .dv _ _, _ => ⟨_, .dv⟩
    | .inj _ _ t, h => by
      simp only [okTerm] at h
      obtain ⟨r, hr⟩ := okTerm_res hw h
      exact ⟨_, .inj hr⟩
    | .as _ _, h => by simp [okTerm] at h
    | .app f ts, h => by
      simp only [okTerm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨hf, h⟩
      · match ts, h with
        | [a, b, s], h =>
          simp only [okLeqArgs, Bool.and_eq_true] at h
          obtain ⟨i, x, rfl, hi, hx⟩ := okVar_val hw h.1.1
          obtain ⟨j, y, rfl, hj, hy⟩ := okVar_val hw h.1.2
          obtain ⟨k, z, rfl, hk, hz⟩ := okVar_val hw h.2
          obtain ⟨u, hu⟩ := leq_result hx hy hz
          exact ⟨_, evalCall (vs := [x, y, z]) (.cons (evalVar hi) (.cons (evalVar hj) (.cons (evalVar hk) .nil))) hu⟩
      · match ts, h with
        | [a], h =>
          simp only [okElemArgs] at h
          obtain ⟨i, x, rfl, hi, hx⟩ := okVar_val hw h
          obtain ⟨u, hu⟩ := isElem_result hx
          exact ⟨_, evalCall (vs := [x]) (.cons (evalVar hi) .nil) hu⟩
      · obtain ⟨rs, hrs⟩ := okTerms_res hw h
        cases hc : c₀.isCtor f
        · exact evalTerm_hookApp hc (hf.resolve_left (by simp [hc])) hrs
        · exact ⟨_, .ctor hc hrs⟩
    termination_by structural t => t
  theorem okTerms_res {vars : List Srt} {lv : List Nat} {σ : Subst} (hw : c₀.WellSortedAt vars lv σ) :
      ∀ {ts : List Term}, okTerms c₀ vars lv ts = true → ∃ rs, EvalTerms c₀ σ ts rs
    | [], _ => ⟨[], .nil⟩
    | t :: ts, h => by
      simp only [okTerms, Bool.and_eq_true] at h
      obtain ⟨r, hr⟩ := okTerm_res hw h.1
      obtain ⟨rs, hrs⟩ := okTerms_res hw h.2
      exact ⟨r :: rs, .cons hr hrs⟩
    termination_by structural ts => ts
end

/-- The predicate `\top`. -/
def isTopB : Cond → Bool
  | .top => true
  | _ => false

/-- Each clause of each function of a priority below another clause of its function has the
predicate `\top` and a `requires` `okTerm` accepts (or none). -/
def prioReqOK (c : Semantics) : Bool :=
  c.fns.all fun fn => fn.clauses.all fun cl' =>
    (fn.clauses.all fun cl => !decide (cl'.prio < cl.prio)) ||
    (isTopB cl'.pre && match cl'.req with
      | none => true
      | some t => okTerm c cl'.vars cl'.leftVars t)

theorem prioReqOK_c₀ : prioReqOK c₀ = true := by decide +kernel

end Prio

/-- **kore.k's `requires` beside an equation of a larger priority have results at
`HookParams.none`** (`PrioDecided`): where a clause applies, each clause of its function of a
smaller priority has, under every substitution well sorted on its left side's variables at which
its patterns match, a `requires` with a result and the predicate `\top`. -/
theorem prioDecided : PrioDecided c₀ := by
  intro fn hfn vs cl σ hcl _ cl' hcl' _ hlt σ' hw _
  have h := List.all_eq_true.mp (List.all_eq_true.mp prioReqOK_c₀ fn hfn) cl' hcl'
  simp only [Bool.or_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.and_eq_true] at h
  rcases h with h | ⟨hp, hq⟩
  · exact absurd hlt (h cl hcl)
  · refine ⟨fun t ht => ?_, ?_⟩
    · rw [ht] at hq; exact okTerm_res hw hq
    · cases hpre : cl'.pre <;> rw [hpre] at hp <;> simp [isTopB] at hp
      exact ⟨true, .top⟩

end KK
