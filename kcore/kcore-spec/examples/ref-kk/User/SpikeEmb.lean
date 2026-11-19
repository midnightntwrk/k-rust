/-
  The measurement of kk-helpers-gen-emb, by hand: `app` and `mkInj` over kore.k's mirrors, in the
  statement shape of decision:kk-helpers (`F` over mirrors with an `Option` result, `F.eval` at
  `K₀ sig` over `emb`, no sortedness hypothesis, `F.eval_iff`).

  Two routes: the sorted-value theorem of User.KkCascade at the embedded arguments, whose sortedness
  `emb_sorted` gives, with the equation `F_G (emb …) = (F …).map emb` between the cascade over values
  and the cascade over mirrors (`appH`, `mkInjH`; the route gen/kkcascade.py emits into
  User.KkGenEmb); and `app` proved over `emb` directly, clause by clause (`appD.eval`).
-/
import User.KkCascade
import User.EmbKit

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK.SpikeEmb

open KCore.KK

/-! ## `app` -/

def appH : List T → List T → Option (List T)
  | [], ys => some ys
  | t :: ts, ys => (appH ts ys).map fun r => t :: r

theorem appH_bridge (xs ys : List T) :
    _root_.KK.Cascade.appF (xs.map emb) (ys.map emb) = (appH xs ys).map (·.map emb) := by
  induction xs with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, _root_.KK.Cascade.appF, appH, ih]
    cases appH ts ys <;> rfl

theorem embTs_fun : embTs = fun ts => _root_.KK.Kit.tsOf (ts.map emb) := funext embTs_eq

spike_hb in
theorem appH.eval (xs ys : List T) :
    Eval (K₀ sig) 447 [embTs xs, embTs ys] ((appH xs ys).map embTs) := by
  have h := _root_.KK.Cascade.appF.eval (xs.map emb) (ys.map emb)
    (by simp only [List.mem_map]; rintro _ ⟨t, -, rfl⟩; exact emb_sorted_c₀ t)
    (by simp only [List.mem_map]; rintro _ ⟨t, -, rfl⟩; exact emb_sorted_c₀ t)
  rw [appH_bridge, Option.map_map] at h
  rw [embTs_fun]; exact h

/-! ## `mkInj` -/

def mkInjH (a b : Int) (t : T) : Option T :=
  match t with
  | .ij c _ t2 => some (.ij c b t2)
  | .bot => some .bot
  | _ => some (.ij a b t)

theorem mkInjH_bridge (a b : Int) (t : T) :
    _root_.KK.Cascade.mkInjF (.dv 3 (.int a)) (.dv 3 (.int b)) (emb t) = (mkInjH a b t).map emb := by
  cases t <;> rfl

spike_hb in
theorem mkInjH.eval (a b : Int) (t : T) :
    Eval (K₀ sig) 493 [.dv 3 (.int a), .dv 3 (.int b), emb t] ((mkInjH a b t).map emb) := by
  have h := _root_.KK.Cascade.mkInjF.eval (.dv 3 (.int a)) (.dv 3 (.int b)) (emb t)
    (_root_.KK.Kit.sort_int a) (_root_.KK.Kit.sort_int b) (emb_sorted_c₀ t)
  rw [mkInjH_bridge] at h; exact h


/-! ## `app` over `emb` directly (hand, no sorted-value theorem) -/

section Direct
open _root_.KK _root_.KK.Kit _root_.KK.Facts _root_.KK.Cascade

spike_hb in
theorem appD.eval (xs ys : List T) :
    Eval (K₀ sig) 447 [embTs xs, embTs ys] ((appH xs ys).map embTs) := by
  show Eval c₀ 447 [embTs xs, embTs ys] ((appH xs ys).map embTs)
  have hno : ∀ cl' ∈ appDef.clauses, cl'.aside = false → cl'.prio < 50 → Fails c₀ [embTs xs, embTs ys] cl' := by
    intro cl' hm _ hp
    simp only [appDef, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> exact absurd hp (by decide)
  induction xs with
  | nil =>
    refine Eval.clause (cl := appNilCl) (σ := enumFrom 0 [embTs ys]) appDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embTs_sorted_c₀ ys) .nil))
      (.cons (by rw [embTs]; exact .ctor ctor_406 .nil) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) Holds.top hno rfl (ev_var rfl) (fun _ h => by cases h) Holds.top
  | cons t ts ih =>
    have hno' : ∀ cl' ∈ appDef.clauses, cl'.aside = false → cl'.prio < 50 → Fails c₀ [embTs ts, embTs ys] cl' := by
      intro cl' hm _ hp
      simp only [appDef, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> exact absurd hp (by decide)
    have ih := ih hno'
    refine Eval.clause (cl := appConsCl) (σ := enumFrom 0 [emb t, embTs ts, embTs ys]) appDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) (.cons (embTs_sorted_c₀ ys) .nil))))
      (.cons (by rw [embTs]; exact .ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) Holds.top hno rfl ?_ (fun _ h => by cases h) Holds.top
    simp only [appH]
    cases hr : appH ts ys with
    | none =>
      rw [hr] at ih
      exact EvalTerm.ctor (σ := enumFrom 0 [emb t, embTs ts, embTs ys]) (rs := [some (emb t), none]) ctor_407
        (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih notCtor_447 notHook_447 notParam_447) .nil))
    | some r =>
      rw [hr] at ih
      rw [Option.map_some, Option.map_some, embTs]
      exact ev_ctor (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih notCtor_447 notHook_447 notParam_447) .nil)) ctor_407

end Direct

end KCore.KK.SpikeEmb
