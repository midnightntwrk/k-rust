/-
  The kit of the cascade text on kore.k's own semantics: what the evaluation proofs of its functions
  read and no function is about. The values of kore.k's list sorts (`tsOf`, `fnsOf`, `lookOf`) and
  the sorts of constructor terms; the substitution that lists the variables' values, with its
  well-sortedness; terms forward (a variable, a constructor, a call, an Int comparison). User.KkFacts
  holds the facts about single symbols (constructor or not, hook or not, a constructor's signature),
  each decided once.
-/
import User.Coherent

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK.Kit

open KCore KCore.Det RefKk KK

/-! ## Heartbeats of one command -/

open Lean Elab Command in
/-- `spike_hb in cmd`: elaborates `cmd` and reports the heartbeats it used (in thousands, the unit
of `maxHeartbeats`) and the time. -/
elab "spike_hb " "in " cmd:command : command => do
  let start ← IO.getNumHeartbeats
  let t ← IO.monoMsNow
  elabCommand cmd
  let stop ← IO.getNumHeartbeats
  logInfo m!"heartbeats: {(stop - start) / 1000}, {(← IO.monoMsNow) - t} ms"

/-! ## Values -/

/-- kore.k's `Ts`: `T ; Ts` and `.Ts`. -/
def tsOf : List GroundTerm → GroundTerm
  | [] => .ctor 406 []
  | t :: ts => .ctor 407 [t, tsOf ts]

/-- kore.k's `Fns`: `fn(G, Cs, Fs)` and `.Fns`. -/
def fnsOf : List (Int × GroundTerm) → GroundTerm
  | [] => .ctor 402 []
  | (g, cs) :: fs => .ctor 421 [.dv 3 (.int g), cs, fnsOf fs]

/-- kore.k's `Look`: `fnd(Cs)` and `nofn`. -/
def lookOf : Option GroundTerm → GroundTerm
  | some cs => .ctor 422 [cs]
  | none => .ctor 432 []

/-! ## Sorts -/

/-- A constructor at values of its argument sorts is a value of its result sort; the constructor's
signature is read by the kernel. -/
theorem sort_ctor {f : Sym} {vs : List GroundTerm} {as : List Srt} {s : Srt}
    (hk : (lookupSig c₀.ctorSigs f).map (fun k => (k.args, k.result)) = some (as, s))
    (hvs : c₀.sortsOf vs = some as) : c₀.sortOf (.ctor f vs) = some s := by
  cases hl : lookupSig c₀.ctorSigs f with
  | none => rw [hl] at hk; cases hk
  | some k =>
    rw [hl] at hk
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    exact c₀.sortOf_ctor_iff.mpr (.inl ⟨k, hl, hk.1 ▸ hvs, hk.2.symm⟩)

theorem sorts_nil : c₀.sortsOf [] = some [] := by simp [Semantics.sortsOf]

theorem sorts_cons {v : GroundTerm} {vs : List GroundTerm} {a : Srt} {as : List Srt}
    (hv : c₀.sortOf v = some a) (hvs : c₀.sortsOf vs = some as) : c₀.sortsOf (v :: vs) = some (a :: as) := by
  simp [Semantics.sortsOf, hv, hvs]

theorem sort_int (x : Int) : c₀.sortOf (.dv 3 (.int x)) = some 3 := by
  have h : dvOK c₀.lib 3 (.int x) = true := by
    show (c₀.lib.carrier 3 == Srt.int) = true
    decide +kernel
  simp [Semantics.sortOf, h]

theorem sort_bool (b : Bool) : c₀.sortOf (.dv 2 (.bool b)) = some 2 := by
  have h : dvOK c₀.lib 2 (.bool b) = true := by
    show (c₀.lib.carrier 2 == Srt.bool) = true
    decide +kernel
  simp [Semantics.sortOf, h]

/-- The argument sorts of a constructor term's constructor are its arguments' sorts. -/
theorem sort_args {f : Sym} {vs : List GroundTerm} {as : List Srt} {s : Srt}
    (h : c₀.sortOf (.ctor f vs) = some s) (hk : (lookupSig c₀.ctorSigs f).map (·.args) = some as) :
    c₀.sortsOf vs = some as := by
  cases hl : lookupSig c₀.ctorSigs f with
  | none => rw [hl] at hk; cases hk
  | some k =>
    rw [hl] at hk
    rcases c₀.sortOf_ctor_iff.mp h with ⟨k', hk', hs, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [hl] at hk'; cases hk'; cases hk; exact hs
    · rw [hl] at hn; cases hn
    · rw [hl] at hn; cases hn

theorem sorts_cons_inv {v : GroundTerm} {vs : List GroundTerm} {a : Srt} {as : List Srt}
    (h : c₀.sortsOf (v :: vs) = some (a :: as)) : c₀.sortOf v = some a ∧ c₀.sortsOf vs = some as := by
  simp only [Semantics.sortsOf] at h
  split at h
  · next s ss hv hvs => cases h; exact ⟨hv, hvs⟩
  · cases h

/-! ## Substitutions and terms, forward -/

/-- The substitution that gives the variables `n`, `n + 1`, … the listed values. -/
def enumFrom (n : Nat) : List GroundTerm → Subst
  | [] => []
  | v :: vs => (n, v) :: enumFrom (n + 1) vs

theorem lookup_enumFrom : ∀ (vs : List GroundTerm) (n i : Nat), (enumFrom n vs).lookup (n + i) = vs[i]?
  | [], _, _ => rfl
  | v :: vs, n, 0 => by simp [enumFrom]
  | v :: vs, n, i + 1 => by
    have hne : (n + (i + 1) == n) = false := by simp
    rw [enumFrom, List.lookup, hne]
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using lookup_enumFrom vs (n + 1) i

/-- Values of the listed sorts, one by one. -/
inductive Sorts : List GroundTerm → List Srt → Prop where
  | nil : Sorts [] []
  | cons {v : GroundTerm} {vs : List GroundTerm} {s : Srt} {ss : List Srt}
      (h : c₀.sortOf v = some s) (hs : Sorts vs ss) : Sorts (v :: vs) (s :: ss)

/-- Values of the variables' sorts, listed in the variables' order, are a well-sorted
substitution. -/
theorem ws_enum {vars : List Srt} {vs : List GroundTerm} (h : Sorts vs vars) :
    c₀.WellSorted vars (enumFrom 0 vs) := by
  intro i s hs
  have hl := lookup_enumFrom vs 0 i
  rw [Nat.zero_add] at hl
  rw [hl]
  clear hl
  induction h generalizing i with
  | nil => simp at hs
  | cons hv _ ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; subst hs; exact ⟨_, rfl, hv⟩
    | succ i => simpa using ih i (by simpa using hs)

/-- A guard that holds selects the first branch. -/
theorem ite_pos {α : Type} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a := by
  simp [h]

/-- A guard that does not hold selects the second branch. -/
theorem ite_neg {α : Type} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b := by
  simp [h]

/-- A variable has its value. -/
theorem ev_var {σ : Subst} {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) :
    EvalTerm c₀ σ (.var i) (some v) := h ▸ .var

/-- Terms with values, listed. -/
inductive EvArgs (σ : Subst) : List Term → List GroundTerm → Prop where
  | nil : EvArgs σ [] []
  | cons {t : Term} {ts : List Term} {v : GroundTerm} {vs : List GroundTerm}
      (h : EvalTerm c₀ σ t (some v)) (hs : EvArgs σ ts vs) : EvArgs σ (t :: ts) (v :: vs)

theorem EvArgs.terms {σ : Subst} {ts : List Term} {vs : List GroundTerm} (h : EvArgs σ ts vs) :
    EvalTerms c₀ σ ts (vs.map some) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

/-- A constructor at arguments with values. -/
theorem ev_ctor {σ : Subst} {f : Sym} {ts : List Term} {vs : List GroundTerm} (h : EvArgs σ ts vs)
    (hc : c₀.isCtor f = true := by decide +kernel) : EvalTerm c₀ σ (.app f ts) (some (.ctor f vs)) := by
  have := EvalTerm.ctor hc h.terms
  rwa [_root_.KCore.allSome_map_some] at this

/-- A call of a function at arguments with values. -/
theorem ev_call {σ : Subst} {f : Sym} {ts : List Term} {vs : List GroundTerm} {r : Option GroundTerm}
    (h : EvArgs σ ts vs) (hf : Eval c₀ f vs r) (hc : c₀.isCtor f = false := by decide +kernel)
    (hh : isHook f = false := by decide +kernel) (hp : c₀.isParam f = false := by decide +kernel) :
    EvalTerm c₀ σ (.app f ts) r :=
  .call hc hh h.terms (_root_.KCore.allSome_map_some vs) hf hp

/-- An Int comparison at two terms with Int values. -/
theorem ev_int2 {σ : Subst} {f : Sym} {t u : Term} {x y : Int} {P : Int → Int → Prop} [∀ x y, Decidable (P x y)]
    (hf : ∀ vs, hook f vs = some (int2 vs fun x y => some (bool (decide (P x y)))))
    (ht : EvalTerm c₀ σ t (some (.dv 3 (.int x)))) (hu : EvalTerm c₀ σ u (some (.dv 3 (.int y))))
    (hc : c₀.isCtor f = false := by decide +kernel) (hh : isHook f = true := by decide +kernel) :
    EvalTerm c₀ σ (.app f [t, u]) (some (bool (decide (P x y)))) := by
  refine .hook hc hh (EvArgs.terms (.cons ht (.cons hu .nil))) (fun vs hvs => ?_) (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value (by rw [hf]; rfl)
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

/-- Every clause of the function is of the priority of this one: no clause of a smaller priority. -/
theorem no_smaller {fn : Fn} {cl : Clause} {vs : List GroundTerm}
    (h : ∀ cl' ∈ fn.clauses, cl.prio ≤ cl'.prio) :
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c₀ vs cl' :=
  fun cl' hm _ hp => absurd hp (Nat.not_lt.mpr (h cl' hm))

/-- A list of terms is a `Ts`. -/
theorem sort_ts {ts : List GroundTerm} (h : ∀ t ∈ ts, c₀.sortOf t = some 33) : c₀.sortOf (tsOf ts) = some 43 := by
  induction ts with
  | nil => exact sort_ctor (by decide +kernel) sorts_nil
  | cons t ts ih =>
    exact sort_ctor (by decide +kernel)
      (sorts_cons (h t (List.mem_cons_self ..)) (sorts_cons (ih fun u hu => h u (List.mem_cons_of_mem _ hu)) sorts_nil))

/-- A list of numbered clause lists is an `Fns`. -/
theorem sort_fns {fs : List (Int × GroundTerm)} (h : ∀ p ∈ fs, c₀.sortOf p.2 = some 35) :
    c₀.sortOf (fnsOf fs) = some 39 := by
  induction fs with
  | nil => exact sort_ctor (by decide +kernel) sorts_nil
  | cons p fs ih =>
    exact sort_ctor (by decide +kernel)
      (sorts_cons (sort_int p.1) (sorts_cons (h p (List.mem_cons_self ..))
        (sorts_cons (ih fun q hq => h q (List.mem_cons_of_mem _ hq)) sorts_nil)))

end KK.Kit
