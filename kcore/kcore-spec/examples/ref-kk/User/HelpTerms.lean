/-
  kore.k's functions `inst`, `instTs`, `mkInj`, `bindAfter`, `bindVar` and `cat` over the mirrors, on
  kore.k's semantics read from its kompiled text, in one shape: a Lean function `F` of the mirrors,
  `F.eval : Eval (K₀ sig) f [emb x, …] ((F x …).map emb)` at the function's symbol `f`, with no
  hypothesis on the arguments (each embedding is a value of its sort, User.Sig and User.EmbKit), and
  `F.eval_iff` from `evalF_iff`.

  `instF` and `instTsF` give `none` exactly where kore.k's `inst` has no value: at a term with no
  equation of `inst` (`as`, `bot`, `co`) anywhere below the constructors `inst` descends through, and
  at a variable the substitution does not bind (`valOf` has no equation at `none`). `mkInjF` is the
  three equations of `mkInj`; on the encoding of a value that is not an injection and holds no `bot`
  it gives `inj-new`'s term (`mkInjF_new`, `mkInjF_enc`), which is the case at the argument of a
  sorted injection (`mkInjF_enc_inj`, from `sortOf`'s `!t.isInj`). `bindVar`, `bindAfter` and `cat`
  have a value at every argument: their `F` is KKMatchF.lean's `bindVarF`, `bindAfterF` and `++`
  (`catF`), the functions `matchF` is written with. `look` and `valOf`, which `inst` and `bindAfter`
  call, are evaluated here as far as these proofs read them (`look_eval_kht`, `valOf_eval_kht`).

  The clauses are the semantics' own, as literals tied to `lookupFn` by the kernel.
-/
import User.EmbKit

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The functions over the mirrors -/

mutual
/-- kore.k's `inst(T, B)`: `T` with each variable replaced by its entry in `B`. -/
def instF : T → Bind → Option T
  | .vr x, B => lookF x B
  | .ap f ts, B => (instTsF ts B).map (.ap f)
  | .hk o ts, B => (instTsF ts B).map (.hk o)
  | .ij a c t, B => (instF t B).map (.ij a c)
  | .iv i, _ => some (.iv i)
  | .bv b, _ => some (.bv b)
  | .tk s x, _ => some (.tk s x)
  | .cb k c ts, B => (instTsF ts B).map (.cb k c)
  | .kv t u, B => (instF t B).bind fun t' => (instF u B).map (.kv t')
  | .el t, B => (instF t B).map .el
  | .en t e, B => (instF t B).bind fun t' => (instF e B).map (.en t')
  | .as _ _, _ => none
  | .bot, _ => none
  | .co _ _ _, _ => none
  termination_by structural t => t
/-- kore.k's `instTs(Ts, B)`: `inst` on each term. -/
def instTsF : List T → Bind → Option (List T)
  | [], _ => some []
  | t :: ts, B => (instF t B).bind fun t' => (instTsF ts B).map (t' :: ·)
  termination_by structural ts => ts
end

/-- kore.k's `mkInj(A, B, T)`: `bot` stays `bot`, an injection's target is replaced, any other term
is injected. -/
def mkInjF (a b : Int) : T → Option T
  | .ij c _ u => some (.ij c b u)
  | .bot => some .bot
  | t => some (.ij a b t)

/-- kore.k's `cat(Ms, Ns)`. -/
abbrev catF (ms ns : Ms) : Ms := ms ++ ns

/-! ## The symbols -/

/-- Each symbol number the evaluations below are at has the KORE name of the function. -/
theorem helpTerms_names :
    RefKk.defn.sem.symName 451 = "LblbindAfter'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Int'Unds'Term'Unds'Ms" ∧
    RefKk.defn.sem.symName 452 = "LblbindVar'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Int'Unds'Term'Unds'Bind'Unds'Res" ∧
    RefKk.defn.sem.symName 453 = "Lblcat'LParUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Ms'Unds'Ms" ∧
    RefKk.defn.sem.symName 476 = "Lblinst'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Term'Unds'Bind" ∧
    RefKk.defn.sem.symName 477 = "LblinstTs'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Ts'Unds'Bind" ∧
    RefKk.defn.sem.symName 484 = "Lbllook'LParUndsCommUndsRParUnds'KORE'Unds'Res'Unds'Int'Unds'Bind" ∧
    RefKk.defn.sem.symName 493 = "LblmkInj'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Int'Unds'Int'Unds'Term" ∧
    RefKk.defn.sem.symName 516 = "LblvalOf'LParUndsRParUnds'KORE'Unds'Term'Unds'Res" := by
  decide +kernel

/-! ## The clauses, as the semantics holds them -/

namespace Terms
open _root_.KK

/-- A clause with no `requires`, at priority 50 unless given. -/
def plainCl (vars : List Srt) (pats : List Term) (rhs : Term) (prio : Nat := 50)
    (req : Option Term := none) : Clause :=
  { vars, pats, req, rhs, ens := none, prio, aside := false, exs := [], pre := .top, post := .top }

/-- `kseq(inj{Term,KItem}(X), dotk)`, the K sequence `==K` and `=/=K` compare. -/
abbrev kq (i : Nat) : Term := .app 0 [.inj 33 1 (.var i), .app 1 []]

/-- `inst` (476): `inst-bool`, `inst-int`, `inst-tok`, `inst-app`, `inst-col`, `inst-el`, `inst-en`,
`inst-hook`, `inst-inj`, `inst-kv`, `inst-var`. -/
def instDef : Fn :=
  { label := 476, args := [33, 46], result := 33, total := false, clauses := [
    plainCl [2, 33, 46] [.as (.app 413 [.var 0]) 1, .var 2] (.var 1),
    plainCl [3, 33, 46] [.as (.app 425 [.var 0]) 1, .var 2] (.var 1),
    plainCl [3, 10, 33, 46] [.as (.app 443 [.var 0, .var 1]) 2, .var 3] (.var 2),
    plainCl [3, 43, 46] [.app 408 [.var 0, .var 1], .var 2] (.app 408 [.var 0, .app 477 [.var 1, .var 2]]),
    plainCl [34, 3, 43, 46] [.app 414 [.var 0, .var 1, .var 2], .var 3]
      (.app 414 [.var 0, .var 1, .app 477 [.var 2, .var 3]]),
    plainCl [33, 46] [.app 419 [.var 0], .var 1] (.app 419 [.app 476 [.var 0, .var 1]]),
    plainCl [33, 33, 46] [.app 420 [.var 0, .var 1], .var 2]
      (.app 420 [.app 476 [.var 0, .var 2], .app 476 [.var 1, .var 2]]),
    plainCl [3, 43, 46] [.app 423 [.var 0, .var 1], .var 2] (.app 423 [.var 0, .app 477 [.var 1, .var 2]]),
    plainCl [3, 3, 33, 46] [.app 424 [.var 0, .var 1, .var 2], .var 3]
      (.app 424 [.var 0, .var 1, .app 476 [.var 2, .var 3]]),
    plainCl [33, 33, 46] [.app 426 [.var 0, .var 1], .var 2]
      (.app 426 [.app 476 [.var 0, .var 2], .app 476 [.var 1, .var 2]]),
    plainCl [3, 46] [.app 445 [.var 0], .var 1] (.app 516 [.app 484 [.var 0, .var 1]])] }

/-- `instTs` (477): `insts-nil`, `insts-cons`. -/
def instTsDef : Fn :=
  { label := 477, args := [43, 46], result := 43, total := false, clauses := [
    plainCl [43, 46] [.as (.app 406 []) 0, .var 1] (.var 0),
    plainCl [33, 43, 46] [.app 407 [.var 0, .var 1], .var 2]
      (.app 407 [.app 476 [.var 0, .var 2], .app 477 [.var 1, .var 2]])] }

/-- `look` (484): `look-hit`, `look-miss`, `look-nil`. -/
def lookDef : Fn :=
  { label := 484, args := [3, 46], result := 41, total := false, clauses := [
    plainCl [3, 3, 33, 46] [.var 0, .app 411 [.var 1, .var 2, .var 3]] (.app 439 [.var 2])
      (req := some (.app 23 [.var 0, .var 1])),
    plainCl [3, 3, 33, 46] [.var 0, .app 411 [.var 1, .var 2, .var 3]] (.app 484 [.var 0, .var 3])
      (req := some (.app 24 [.var 0, .var 1])),
    plainCl [3] [.var 0, .app 400 []] (.app 433 [])] }

/-- `valOf` (516): `val-of`. -/
def valOfDef : Fn :=
  { label := 516, args := [41], result := 33, total := false, clauses := [
    plainCl [33] [.app 439 [.var 0]] (.var 0)] }

/-- `mkInj` (493): `inj-compose`, `inj-bot`, `inj-new` (priority 200, `[owise]`). -/
def mkInjDef : Fn :=
  { label := 493, args := [3, 3, 33], result := 33, total := false, clauses := [
    plainCl [3, 3, 33, 3, 3] [.var 3, .var 4, .app 424 [.var 0, .var 1, .var 2]] (.app 424 [.var 0, .var 4, .var 2]),
    plainCl [3, 33, 3] [.var 2, .var 0, .as (.app 412 []) 1] (.var 1),
    plainCl [3, 3, 33] [.var 0, .var 1, .var 2] (.app 424 [.var 0, .var 1, .var 2]) (prio := 200)] }

/-- `bindVar` (452): `bind-new`, `bind-same`, `bind-clash`. -/
def bindVarDef : Fn :=
  { label := 452, args := [3, 33, 46, 41], result := 37, total := false, clauses := [
    plainCl [3, 33, 46] [.var 0, .var 1, .var 2, .app 433 []] (.app 428 [.app 411 [.var 0, .var 1, .var 2], .app 403 []]),
    plainCl [3, 33, 46, 33] [.var 0, .var 1, .var 2, .app 439 [.var 3]] (.app 428 [.var 2, .app 403 []])
      (req := some (.app 29 [kq 1, kq 3])),
    plainCl [3, 33, 46, 33] [.var 0, .var 1, .var 2, .app 439 [.var 3]] (.app 403 [])
      (req := some (.app 30 [kq 1, kq 3]))] }

/-- `bindAfter` (451): `as-bind`, `as-fail`. -/
def bindAfterDef : Fn :=
  { label := 451, args := [3, 33, 37], result := 37, total := false, clauses := [
    plainCl [3, 33, 46, 37] [.var 0, .var 1, .app 428 [.var 2, .var 3]]
      (.app 453 [.app 452 [.var 0, .var 1, .var 2, .app 484 [.var 0, .var 2]], .app 451 [.var 0, .var 1, .var 3]]),
    plainCl [3, 33, 37] [.var 0, .var 1, .as (.app 403 []) 2] (.var 2)] }

/-- `cat` (453): `cat-nil`, `cat-cons`. -/
def catDef : Fn :=
  { label := 453, args := [37, 37], result := 37, total := false, clauses := [
    plainCl [37] [.app 403 [], .var 0] (.var 0),
    plainCl [46, 37, 37] [.app 428 [.var 0, .var 1], .var 2] (.app 428 [.var 0, .app 453 [.var 1, .var 2]])] }

theorem instDef_lookup : c₀.lookupFn 476 = some instDef := by kernel_rfl
theorem instTsDef_lookup : c₀.lookupFn 477 = some instTsDef := by kernel_rfl
theorem lookDef_lookup : c₀.lookupFn 484 = some lookDef := by kernel_rfl
theorem valOfDef_lookup : c₀.lookupFn 516 = some valOfDef := by kernel_rfl
theorem mkInjDef_lookup : c₀.lookupFn 493 = some mkInjDef := by kernel_rfl
theorem bindVarDef_lookup : c₀.lookupFn 452 = some bindVarDef := by kernel_rfl
theorem bindAfterDef_lookup : c₀.lookupFn 451 = some bindAfterDef := by kernel_rfl
theorem catDef_lookup : c₀.lookupFn 453 = some catDef := by kernel_rfl

end Terms

/-! ## Shared steps -/

section Kit
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

spike_hb in
/-- A clause with no existential variable, `ensures` or predicate, and of the smallest priority of
its function, decides where its patterns and `requires` hold. -/
theorem clause_kht {f : Sym} {fn : Fn} {cl : Clause} {σ : Subst} {vs : List GroundTerm}
    {r : Option GroundTerm} (hfn : c₀.lookupFn f = some fn) (hm : cl ∈ fn.clauses)
    (hσ : c₀.WellSorted cl.vars σ) (hp : PatVals c₀ σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c₀ σ t (some (bool true)))
    (hlow : ∀ cl' ∈ fn.clauses, cl.prio ≤ cl'.prio)
    (hcl : cl.exs = [] ∧ cl.ens = none ∧ cl.pre = .top ∧ cl.post = .top)
    (hr : EvalTerm c₀ σ cl.rhs r) : Eval c₀ f vs r := by
  obtain ⟨hex, hens, hpre, hpost⟩ := hcl
  refine Eval.clause hfn hm hσ hp hreq ?_ (no_smaller hlow) hex hr (fun _ h => by rw [hens] at h; cases h) ?_
  · rw [hpre]; exact Holds.top
  · rw [hpost]; exact Holds.top

spike_hb in
/-- A clause none of whose substitutions makes its patterns denote the arguments fails. -/
theorem fails_kht {vs : List GroundTerm} {cl : Clause} (h : ∀ σ, PatVals c₀ σ cl.pats vs → False) :
    Fails c₀ vs cl :=
  .intro fun σ _ hm => (h σ hm).elim

spike_hb in
/-- A constructor pattern denotes no value of another head. -/
theorem patCtor_ne_kht {σ : Subst} {f : Sym} {qs : List Term} {v : GroundTerm}
    (h : PatVal c₀ σ (.app f qs) v) (hv : ∀ ws, v ≠ .ctor f ws)
    (hc : c₀.isCtor f = true := by decide +kernel) (hh : patternHooks.contains f = false := by decide +kernel) :
    False := by
  obtain ⟨ws, he, -⟩ := pv_ctor h hc hh
  exact hv ws he

spike_hb in
theorem emb_ne_kht {t : T} {f : Sym} (hne : headOf t ≠ f) : ∀ ws, emb t ≠ .ctor f ws :=
  fun _ h => hne (GroundTerm.ctor.inj ((emb_ctor t).symm.trans h)).1

spike_hb in
/-- `kseq(inj{Term,KItem}(emb t), dotk)`. -/
abbrev kqV (t : T) : GroundTerm := .ctor 0 [.inj 33 1 (emb t), .ctor 1 []]

theorem kq_eval_kht {σ : Subst} {i : Nat} {t : T} (h : σ.lookup i = some (emb t)) :
    EvalTerm c₀ σ (kq i) (some (kqV t)) := by
  have e : injNormal 33 1 (emb t) = .inj 33 1 (emb t) := by rw [emb_ctor]; rfl
  have := EvalTerm.ctor (σ := σ) (f := 0) (by decide +kernel)
    (.cons (EvalTerm.inj (a := 33) (b := 1) (ev_var h)) (.cons (EvalTerm.ctor (ts := []) (f := 1) (by decide +kernel) .nil) .nil))
  rw [kqV, ← e]
  exact this

spike_hb in
theorem kqV_cmp_kht (t u : T) : (GroundTerm.cmp (kqV t) (kqV u) == .eq) = decide (t = u) := by
  by_cases h : t = u
  · subst h; simp [GroundTerm.cmp_refl]
  · rw [decide_eq_false h]
    cases hc : GroundTerm.cmp (kqV t) (kqV u) with
    | eq =>
      have e := cmp_eq_iff.mp hc
      simp only [kqV, GroundTerm.ctor.injEq, List.cons.injEq, GroundTerm.inj.injEq, true_and, and_true] at e
      exact absurd (emb_injective e) h
    | lt => rfl
    | gt => rfl

spike_hb in
/-- `t ==K u` on two terms' K sequences is whether the terms are equal. -/
theorem keq_eval_kht {σ : Subst} {i j : Nat} {t u : T} (hi : σ.lookup i = some (emb t))
    (hj : σ.lookup j = some (emb u)) :
    EvalTerm c₀ σ (.app 29 [kq i, kq j]) (some (bool (decide (t = u)))) := by
  refine EvalTerm.hook (by decide +kernel) rfl (.cons (kq_eval_kht hi) (.cons (kq_eval_kht hj) .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  rw [← kqV_cmp_kht]
  exact Semantics.hookRes_of_value (hook_kEq _ _)

spike_hb in
/-- `t =/=K u` on two terms' K sequences is whether the terms differ. -/
theorem kne_eval_kht {σ : Subst} {i j : Nat} {t u : T} (hi : σ.lookup i = some (emb t))
    (hj : σ.lookup j = some (emb u)) :
    EvalTerm c₀ σ (.app 30 [kq i, kq j]) (some (bool (!decide (t = u)))) := by
  refine EvalTerm.hook (by decide +kernel) rfl (.cons (kq_eval_kht hi) (.cons (kq_eval_kht hj) .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  rw [← kqV_cmp_kht]
  refine Semantics.hookRes_of_value ((hook_kNe _ _).trans ?_)
  cases GroundTerm.cmp (kqV t) (kqV u) <;> rfl

end Kit

/-! ## `cat`, `look`, `valOf` -/

section Small
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

spike_hb in
theorem catF_eval_c₀ (ms ns : Ms) : Eval c₀ 453 [embMs ms, embMs ns] (some (embMs (catF ms ns))) := by
  induction ms with
  | nil =>
    exact clause_kht (σ := enumFrom 0 [embMs ns]) catDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embMs_sorted_c₀ ns) .nil)) (.cons (.ctor ctor_403 .nil) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | cons B ms ih =>
    exact clause_kht (σ := enumFrom 0 [embB B, embMs ms, embMs ns]) catDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (embB_sorted_c₀ B) (.cons (embMs_sorted_c₀ ms) (.cons (embMs_sorted_c₀ ns) .nil))))
      (.cons (.ctor ctor_428 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih
        notCtor_453 notHook_453 notParam_453) .nil)) ctor_428)

spike_hb in
/-- `look(X, B)` evaluates to `lookF`'s entry. -/
theorem look_eval_kht (x : Int) (B : Bind) :
    Eval c₀ 484 [.dv 3 (.int x), embB B] (some (embRes (lookF x B))) := by
  induction B with
  | nil =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int x)]) lookDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (ws_enum (.cons (sort_int x) .nil)) (.cons (.var rfl) (.cons (.ctor ctor_400 .nil) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_433)
  | cons e B ih =>
    obtain ⟨y, t⟩ := e
    have hσ := ws_enum (vars := [3, 3, 33, 46]) (.cons (sort_int x) (.cons (sort_int y)
      (.cons (emb_sorted_c₀ t) (.cons (embB_sorted_c₀ B) .nil))))
    have hp : PatVals c₀ (enumFrom 0 [.dv 3 (.int x), .dv 3 (.int y), emb t, embB B])
        [.var 0, .app 411 [.var 1, .var 2, .var 3]] [.dv 3 (.int x), embB ((y, t) :: B)] :=
      .cons (.var rfl) (.cons (.ctor ctor_411 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil)
    by_cases h : x = y
    · rw [lookF, ite_pos h]
      refine clause_kht lookDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
        (ev_ctor (.cons (ev_var rfl) .nil) ctor_439)
      intro q hq
      cases hq
      have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int x), .dv 3 (.int y), emb t, embB B]) (P := (· = ·))
        hook_intEq (ev_var (i := 0) rfl) (ev_var (i := 1) rfl) notCtor_23 isHook_23
      rwa [decide_eq_true h] at hq
    · rw [lookF, ite_neg h]
      refine clause_kht lookDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
        ⟨rfl, rfl, rfl, rfl⟩
        (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih notCtor_484 notHook_484 notParam_484)
      intro q hq
      cases hq
      have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int x), .dv 3 (.int y), emb t, embB B]) (P := (· ≠ ·))
        hook_intNe (ev_var (i := 0) rfl) (ev_var (i := 1) rfl) notCtor_24 isHook_24
      rwa [decide_eq_true h] at hq

spike_hb in
/-- `valOf(R)` evaluates to `R`'s term, and has no value at `none`. -/
theorem valOf_eval_kht (r : Option T) : Eval c₀ 516 [embRes r] (r.map emb) := by
  cases r with
  | some t =>
    exact clause_kht (σ := enumFrom 0 [emb t]) valOfDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ t) .nil)) (.cons (.ctor ctor_439 (.cons (.var rfl) .nil)) .nil)
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | none =>
    refine Eval.rest valOfDef_lookup fun cl hm => ?_
    simp only [valOfDef, List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    exact fails_kht fun σ hm => by
      rcases hm with _ | ⟨h0, -⟩
      exact patCtor_ne_kht h0 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)

end Small

/-! ## `bindVar`, `bindAfter` -/

section Bind
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

spike_hb in
theorem bindVarF_eval_c₀ (x : Int) (t : T) (B : Bind) (r : Option T) :
    Eval c₀ 452 [.dv 3 (.int x), emb t, embB B, embRes r] (some (embMs (bindVarF x t B r))) := by
  cases r with
  | none =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int x), emb t, embB B]) bindVarDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (sort_int x) (.cons (emb_sorted_c₀ t) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_433 .nil) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) ctor_411)
        (.cons (ev_ctor .nil ctor_403) .nil)) ctor_428)
  | some u =>
    have hσ := ws_enum (vars := [3, 33, 46, 33]) (.cons (sort_int x) (.cons (emb_sorted_c₀ t)
      (.cons (embB_sorted_c₀ B) (.cons (emb_sorted_c₀ u) .nil))))
    have hp : PatVals c₀ (enumFrom 0 [.dv 3 (.int x), emb t, embB B, emb u])
        [.var 0, .var 1, .var 2, .app 439 [.var 3]] [.dv 3 (.int x), emb t, embB B, embRes (some u)] :=
      .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_439 (.cons (.var rfl) .nil)) .nil)))
    by_cases h : t = u
    · rw [bindVarF, ite_pos h]
      refine clause_kht bindVarDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
        ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_403) .nil)) ctor_428)
      intro q hq
      cases hq
      have hq := keq_eval_kht (σ := enumFrom 0 [.dv 3 (.int x), emb t, embB B, emb u]) (i := 1) (j := 3) rfl rfl
      rwa [decide_eq_true h] at hq
    · rw [bindVarF, ite_neg h]
      refine clause_kht bindVarDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_403)
      intro q hq
      cases hq
      have hq := kne_eval_kht (σ := enumFrom 0 [.dv 3 (.int x), emb t, embB B, emb u]) (i := 1) (j := 3) rfl rfl
      rwa [decide_eq_false h] at hq

spike_hb in
theorem bindAfterF_eval_c₀ (x : Int) (t : T) (ms : Ms) :
    Eval c₀ 451 [.dv 3 (.int x), emb t, embMs ms] (some (embMs (bindAfterF x t ms))) := by
  induction ms with
  | nil =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int x), emb t, embMs []]) bindAfterDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (sort_int x) (.cons (emb_sorted_c₀ t) (.cons (embMs_sorted_c₀ []) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.as (.ctor ctor_403 .nil) rfl) .nil)))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | cons B ms ih =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int x), emb t, embB B, embMs ms]) bindAfterDef_lookup
      (List.mem_cons_self ..)
      (ws_enum (.cons (sort_int x) (.cons (emb_sorted_c₀ t) (.cons (embB_sorted_c₀ B) (.cons (embMs_sorted_c₀ ms) .nil)))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_428 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
          (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (look_eval_kht x B)
            notCtor_484 notHook_484 notParam_484) .nil))))
          (bindVarF_eval_c₀ x t B (lookF x B)) notCtor_452 notHook_452 notParam_452)
        (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) ih
          notCtor_451 notHook_451 notParam_451) .nil))
        (catF_eval_c₀ _ _) notCtor_453 notHook_453 notParam_453)

end Bind

/-! ## `mkInj` -/

section MkInj
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

spike_hb in
/-- A term that is neither an injection nor `bot` has neither head. -/
theorem headOf_new_kht : ∀ {t : T}, isIjT_kkc t = false → t ≠ .bot → headOf t ≠ 424 ∧ headOf t ≠ 412
  | .ij .., hi, _ => by simp [isIjT_kkc] at hi
  | .bot, _, hb => absurd rfl hb
  | .ap .., _, _ => show (408 : Sym) ≠ 424 ∧ (408 : Sym) ≠ 412 by decide
  | .iv _, _, _ => show (425 : Sym) ≠ 424 ∧ (425 : Sym) ≠ 412 by decide
  | .bv _, _, _ => show (413 : Sym) ≠ 424 ∧ (413 : Sym) ≠ 412 by decide
  | .tk .., _, _ => show (443 : Sym) ≠ 424 ∧ (443 : Sym) ≠ 412 by decide
  | .vr _, _, _ => show (445 : Sym) ≠ 424 ∧ (445 : Sym) ≠ 412 by decide
  | .as .., _, _ => show (409 : Sym) ≠ 424 ∧ (409 : Sym) ≠ 412 by decide
  | .hk .., _, _ => show (423 : Sym) ≠ 424 ∧ (423 : Sym) ≠ 412 by decide
  | .cb .., _, _ => show (414 : Sym) ≠ 424 ∧ (414 : Sym) ≠ 412 by decide
  | .co .., _, _ => show (416 : Sym) ≠ 424 ∧ (416 : Sym) ≠ 412 by decide
  | .en .., _, _ => show (420 : Sym) ≠ 424 ∧ (420 : Sym) ≠ 412 by decide
  | .kv .., _, _ => show (426 : Sym) ≠ 424 ∧ (426 : Sym) ≠ 412 by decide
  | .el _, _, _ => show (419 : Sym) ≠ 424 ∧ (419 : Sym) ≠ 412 by decide

spike_hb in
/-- At a term that is neither an injection nor `bot`, `inj-new` decides: the two equations of a
smaller priority fail on the term's head. -/
theorem mkInj_new_kht (a b : Int) {t : T} (hi : isIjT_kkc t = false) (hb : t ≠ .bot) :
    Eval c₀ 493 [.dv 3 (.int a), .dv 3 (.int b), emb t] (some (emb (.ij a b t))) := by
  obtain ⟨h1, h2⟩ := headOf_new_kht hi hb
  refine Eval.clause (σ := enumFrom 0 [.dv 3 (.int a), .dv 3 (.int b), emb t]) mkInjDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (ws_enum (.cons (sort_int a) (.cons (sort_int b) (.cons (emb_sorted_c₀ t) .nil))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
    (fun _ h => by cases h) Holds.top ?_ rfl
    (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) ctor_424)
    (fun _ h => by cases h) Holds.top
  intro cl' hm _ hp
  simp only [mkInjDef, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact fails_kht fun σ hm => by
      rcases hm with _ | ⟨_, _ | ⟨_, _ | ⟨h, -⟩⟩⟩
      exact patCtor_ne_kht h (emb_ne_kht h1)
  · exact fails_kht fun σ hm => by
      rcases hm with _ | ⟨_, _ | ⟨_, _ | ⟨h, -⟩⟩⟩
      exact patCtor_ne_kht (PatVal.as_inv h).1 (emb_ne_kht h2)
  · exact absurd hp (by decide)

spike_hb in
theorem mkInjF_eval_c₀ (a b : Int) (t : T) :
    Eval c₀ 493 [.dv 3 (.int a), .dv 3 (.int b), emb t] ((mkInjF a b t).map emb) := by
  cases t with
  | ij c d u =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int c), .dv 3 (.int d), emb u, .dv 3 (.int a), .dv 3 (.int b)])
      mkInjDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (sort_int c) (.cons (sort_int d) (.cons (emb_sorted_c₀ u)
        (.cons (sort_int a) (.cons (sort_int b) .nil))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.var rfl) .nil)))) .nil)))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) ctor_424)
  | bot =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int b), emb .bot, .dv 3 (.int a)])
      mkInjDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (sort_int b) (.cons (emb_sorted_c₀ .bot) (.cons (sort_int a) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.as (.ctor ctor_412 .nil) rfl) .nil)))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | _ => exact mkInj_new_kht a b rfl nofun

end MkInj

/-! ## `inst`, `instTs` -/

section Inst
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

spike_hb in
/-- A term none of `inst`'s equations takes (`as`, `bot`, `co`) has no instance. -/
theorem inst_rest_kht {t : T} (B : Bind) {h : Sym} (hh : headOf t = h)
    (hn : h ∉ [413, 425, 443, 408, 414, 419, 420, 423, 424, 426, 445] := by decide) :
    Eval c₀ 476 [emb t, embB B] none := by
  refine Eval.rest instDef_lookup fun cl hm => ?_
  simp only [instDef, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine fails_kht fun σ hm => ?_ <;> rcases hm with _ | ⟨h0, -⟩
  all_goals first
    | exact patCtor_ne_kht (PatVal.as_inv h0).1 (emb_ne_kht fun e => hn (by rw [← hh, e]; decide))
    | exact patCtor_ne_kht h0 (emb_ne_kht fun e => hn (by rw [← hh, e]; decide))

spike_hb in
/-- A binary constructor at two results. -/
theorem ctor2_kht {α β : Type} {σ : Subst} {f : Sym} {t u : Term} {g : α → GroundTerm} {k : β → GroundTerm}
    {r : Option α} {q : Option β} (hf : c₀.isCtor f = true)
    (ht : EvalTerm c₀ σ t (r.map g)) (hu : EvalTerm c₀ σ u (q.map k)) :
    EvalTerm c₀ σ (.app f [t, u]) ((r.bind fun x => q.map fun y => (x, y)).map fun p => .ctor f [g p.1, k p.2]) := by
  have h := EvalTerm.ctor hf (.cons ht (.cons hu .nil))
  cases r <;> cases q <;> exact h

spike_hb in
/-- `instTs` at a list each of whose terms `inst` evaluates. -/
theorem instTsF_eval_of_kht : ∀ (ts : List T),
    (∀ a ∈ ts, ∀ B, Eval c₀ 476 [emb a, embB B] ((instF a B).map emb)) →
    ∀ B, Eval c₀ 477 [embTs ts, embB B] ((instTsF ts B).map embTs)
  | [], _, B => by
    rw [instTsF]
    exact clause_kht (σ := enumFrom 0 [embTs [], embB B]) instTsDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embTs_sorted_c₀ []) (.cons (embB_sorted_c₀ B) .nil)))
      (.cons (.as (.ctor ctor_406 .nil) rfl) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | t :: ts, h, B => by
    have ih := instTsF_eval_of_kht ts (fun a ha => h a (List.mem_cons_of_mem _ ha)) B
    have ht := h t (List.mem_cons_self ..) B
    have hr := ctor2_kht (σ := enumFrom 0 [emb t, embTs ts, embB B]) ctor_407
      (ev_call (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 2) rfl) .nil)) ht notCtor_476 notHook_476 notParam_476)
      (ev_call (.cons (ev_var (i := 1) rfl) (.cons (ev_var (i := 2) rfl) .nil)) ih notCtor_477 notHook_477 notParam_477)
    have e : (instTsF (t :: ts) B).map embTs = ((instF t B).bind fun x => (instTsF ts B).map fun y => (x, y)).map
        fun p => .ctor 407 [emb p.1, embTs p.2] := by
      rw [instTsF]; cases instF t B <;> cases instTsF ts B <;> rfl
    rw [e]
    exact clause_kht (σ := enumFrom 0 [emb t, embTs ts, embB B]) instTsDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ hr

spike_hb in
theorem instF_eval_c₀ (t : T) : ∀ B, Eval c₀ 476 [emb t, embB B] ((instF t B).map emb) := by
  induction t using tInd_kkc with
  | hap f as ih =>
    intro B
    have hl := instTsF_eval_of_kht as ih B
    have e : (instF (.ap f as) B).map emb = (instTsF as B).map fun l => .ctor 408 [.dv 3 (.int f), embTs l] := by
      rw [instF]; cases instTsF as B <;> rfl
    rw [e]
    refine clause_kht (σ := enumFrom 0 [.dv 3 (.int f), embTs as, embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (ws_enum (.cons (sort_int f) (.cons (embTs_sorted_c₀ as) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.ctor ctor_408 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    have h := EvalTerm.ctor (σ := enumFrom 0 [.dv 3 (.int f), embTs as, embB B]) ctor_408 (.cons (ev_var (i := 0) rfl)
      (.cons (ev_call (.cons (ev_var (i := 1) rfl) (.cons (ev_var (i := 2) rfl) .nil)) hl notCtor_477 notHook_477 notParam_477) .nil))
    generalize instTsF as B = o at h ⊢
    cases o <;> exact h
  | hiv i =>
    intro B
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int i), emb (.iv i), embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (sort_int i) (.cons (emb_sorted_c₀ _) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.as (.ctor ctor_425 (.cons (.var rfl) .nil)) rfl) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | hbv b =>
    intro B
    exact clause_kht (σ := enumFrom 0 [.dv 2 (.bool b), emb (.bv b), embB B]) instDef_lookup
      (List.mem_cons_self ..)
      (ws_enum (.cons (sort_bool b) (.cons (emb_sorted_c₀ _) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.as (.ctor ctor_413 (.cons (.var rfl) .nil)) rfl) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | htk s x =>
    intro B
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int s), .dv 10 (.tok x), emb (.tk s x), embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (ws_enum (.cons (sort_int s) (.cons (sort_string_kemb x) (.cons (emb_sorted_c₀ _) (.cons (embB_sorted_c₀ B) .nil)))))
      (.cons (.as (.ctor ctor_443 (.cons (.var rfl) (.cons (.var rfl) .nil))) rfl) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | hij a c t ih =>
    intro B
    have e : (instF (.ij a c t) B).map emb = (instF t B).map fun u => .ctor 424 [.dv 3 (.int a), .dv 3 (.int c), emb u] := by
      rw [instF]; cases instF t B <;> rfl
    rw [e]
    refine clause_kht (σ := enumFrom 0 [.dv 3 (.int a), .dv 3 (.int c), emb t, embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..)))))))))
      (ws_enum (.cons (sort_int a) (.cons (sort_int c) (.cons (emb_sorted_c₀ t) (.cons (embB_sorted_c₀ B) .nil)))))
      (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    have h := EvalTerm.ctor (σ := enumFrom 0 [.dv 3 (.int a), .dv 3 (.int c), emb t, embB B]) ctor_424
      (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 1) rfl)
        (.cons (ev_call (.cons (ev_var (i := 2) rfl) (.cons (ev_var (i := 3) rfl) .nil)) (ih B)
          notCtor_476 notHook_476 notParam_476) .nil)))
    generalize instF t B = o at h ⊢
    cases o <;> exact h
  | hvr x =>
    intro B
    rw [instF]
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int x), embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))
      (ws_enum (.cons (sort_int x) (.cons (embB_sorted_c₀ B) .nil)))
      (.cons (.ctor ctor_445 (.cons (.var rfl) .nil)) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (look_eval_kht x B)
        notCtor_484 notHook_484 notParam_484) .nil) (valOf_eval_kht _) notCtor_516 notHook_516 notParam_516)
  | has p i _ => intro B; exact inst_rest_kht B (h := 409) rfl
  | hhk o as ih =>
    intro B
    have hl := instTsF_eval_of_kht as ih B
    have e : (instF (.hk o as) B).map emb = (instTsF as B).map fun l => .ctor 423 [.dv 3 (.int o), embTs l] := by
      rw [instF]; cases instTsF as B <;> rfl
    rw [e]
    refine clause_kht (σ := enumFrom 0 [.dv 3 (.int o), embTs as, embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
      (ws_enum (.cons (sort_int o) (.cons (embTs_sorted_c₀ as) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.ctor ctor_423 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    have h := EvalTerm.ctor (σ := enumFrom 0 [.dv 3 (.int o), embTs as, embB B]) ctor_423 (.cons (ev_var (i := 0) rfl)
      (.cons (ev_call (.cons (ev_var (i := 1) rfl) (.cons (ev_var (i := 2) rfl) .nil)) hl notCtor_477 notHook_477 notParam_477) .nil))
    generalize instTsF as B = o at h ⊢
    cases o <;> exact h
  | hbot => intro B; exact inst_rest_kht B (h := 412) rfl
  | hcb k c ps ih =>
    intro B
    have hl := instTsF_eval_of_kht ps ih B
    have e : (instF (.cb k c ps) B).map emb = (instTsF ps B).map fun l => .ctor 414 [embK k, .dv 3 (.int c), embTs l] := by
      rw [instF]; cases instTsF ps B <;> rfl
    rw [e]
    refine clause_kht (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))))
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ ps) (.cons (embB_sorted_c₀ B) .nil)))))
      (.cons (.ctor ctor_414 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    have h := EvalTerm.ctor (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embB B]) ctor_414
      (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 1) rfl)
        (.cons (ev_call (.cons (ev_var (i := 2) rfl) (.cons (ev_var (i := 3) rfl) .nil)) hl
          notCtor_477 notHook_477 notParam_477) .nil)))
    generalize instTsF ps B = o at h ⊢
    cases o <;> exact h
  | hco k c es _ => intro B; exact inst_rest_kht B (h := 416) rfl
  | hen t e iht ihe =>
    intro B
    have hr := ctor2_kht (σ := enumFrom 0 [emb t, emb e, embB B]) ctor_420
      (ev_call (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 2) rfl) .nil)) (iht B) notCtor_476 notHook_476 notParam_476)
      (ev_call (.cons (ev_var (i := 1) rfl) (.cons (ev_var (i := 2) rfl) .nil)) (ihe B) notCtor_476 notHook_476 notParam_476)
    have e' : (instF (.en t e) B).map emb = ((instF t B).bind fun x => (instF e B).map fun y => (x, y)).map
        fun p => .ctor 420 [emb p.1, emb p.2] := by
      rw [instF]; cases instF t B <;> cases instF e B <;> rfl
    rw [e']
    exact clause_kht (σ := enumFrom 0 [emb t, emb e, embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (emb_sorted_c₀ e) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.ctor ctor_420 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ hr
  | hkv a v iha ihv =>
    intro B
    have hr := ctor2_kht (σ := enumFrom 0 [emb a, emb v, embB B]) ctor_426
      (ev_call (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 2) rfl) .nil)) (iha B) notCtor_476 notHook_476 notParam_476)
      (ev_call (.cons (ev_var (i := 1) rfl) (.cons (ev_var (i := 2) rfl) .nil)) (ihv B) notCtor_476 notHook_476 notParam_476)
    have e' : (instF (.kv a v) B).map emb = ((instF a B).bind fun x => (instF v B).map fun y => (x, y)).map
        fun p => .ctor 426 [emb p.1, emb p.2] := by
      rw [instF]; cases instF a B <;> cases instF v B <;> rfl
    rw [e']
    exact clause_kht (σ := enumFrom 0 [emb a, emb v, embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
      (ws_enum (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) (.cons (embB_sorted_c₀ B) .nil))))
      (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ hr
  | hel x ih =>
    intro B
    have e : (instF (.el x) B).map emb = (instF x B).map fun u => .ctor 419 [emb u] := by
      rw [instF]; cases instF x B <;> rfl
    rw [e]
    refine clause_kht (σ := enumFrom 0 [emb x, embB B]) instDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
      (ws_enum (.cons (emb_sorted_c₀ x) (.cons (embB_sorted_c₀ B) .nil)))
      (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    have h := EvalTerm.ctor (σ := enumFrom 0 [emb x, embB B]) ctor_419
      (.cons (ev_call (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 1) rfl) .nil)) (ih B)
        notCtor_476 notHook_476 notParam_476) .nil)
    generalize instF x B = o at h ⊢
    cases o <;> exact h

end Inst


/-! ## The helpers at `K₀ sig` -/

section Shape

theorem instF.eval (t : T) (B : Bind) : Eval (K₀ sig) 476 [emb t, embB B] ((instF t B).map emb) :=
  instF_eval_c₀ t B
theorem instF.eval_iff (t : T) (B : Bind) {r : Option GroundTerm} :
    Eval (K₀ sig) 476 [emb t, embB B] r ↔ r = (instF t B).map emb :=
  evalF_iff (instF.eval t B)

theorem instTsF.eval (ts : List T) (B : Bind) :
    Eval (K₀ sig) 477 [embTs ts, embB B] ((instTsF ts B).map embTs) :=
  instTsF_eval_of_kht ts (fun a _ => instF_eval_c₀ a) B
theorem instTsF.eval_iff (ts : List T) (B : Bind) {r : Option GroundTerm} :
    Eval (K₀ sig) 477 [embTs ts, embB B] r ↔ r = (instTsF ts B).map embTs :=
  evalF_iff (instTsF.eval ts B)

theorem mkInjF.eval (a b : Int) (t : T) :
    Eval (K₀ sig) 493 [.dv 3 (.int a), .dv 3 (.int b), emb t] ((mkInjF a b t).map emb) :=
  mkInjF_eval_c₀ a b t
theorem mkInjF.eval_iff (a b : Int) (t : T) {r : Option GroundTerm} :
    Eval (K₀ sig) 493 [.dv 3 (.int a), .dv 3 (.int b), emb t] r ↔ r = (mkInjF a b t).map emb :=
  evalF_iff (mkInjF.eval a b t)

theorem bindVarF.eval (x : Int) (t : T) (B : Bind) (r : Option T) :
    Eval (K₀ sig) 452 [.dv 3 (.int x), emb t, embB B, embRes r] (some (embMs (bindVarF x t B r))) :=
  bindVarF_eval_c₀ x t B r
theorem bindVarF.eval_iff (x : Int) (t : T) (B : Bind) (r : Option T) {q : Option GroundTerm} :
    Eval (K₀ sig) 452 [.dv 3 (.int x), emb t, embB B, embRes r] q ↔ q = some (embMs (bindVarF x t B r)) :=
  evalF_iff (bindVarF.eval x t B r)

theorem bindAfterF.eval (x : Int) (t : T) (ms : Ms) :
    Eval (K₀ sig) 451 [.dv 3 (.int x), emb t, embMs ms] (some (embMs (bindAfterF x t ms))) :=
  bindAfterF_eval_c₀ x t ms
theorem bindAfterF.eval_iff (x : Int) (t : T) (ms : Ms) {q : Option GroundTerm} :
    Eval (K₀ sig) 451 [.dv 3 (.int x), emb t, embMs ms] q ↔ q = some (embMs (bindAfterF x t ms)) :=
  evalF_iff (bindAfterF.eval x t ms)

theorem catF.eval (ms ns : Ms) : Eval (K₀ sig) 453 [embMs ms, embMs ns] (some (embMs (catF ms ns))) :=
  catF_eval_c₀ ms ns
theorem catF.eval_iff (ms ns : Ms) {q : Option GroundTerm} :
    Eval (K₀ sig) 453 [embMs ms, embMs ns] q ↔ q = some (embMs (catF ms ns)) :=
  evalF_iff (catF.eval ms ns)

/-- `look(X, B)` at `K₀ sig`. -/
theorem look_eval_iff_kht (x : Int) (B : Bind) {q : Option GroundTerm} :
    Eval (K₀ sig) 484 [.dv 3 (.int x), embB B] q ↔ q = some (embRes (lookF x B)) :=
  evalF_iff (look_eval_kht x B)

/-- `valOf(R)` at `K₀ sig`. -/
theorem valOf_eval_iff_kht (r : Option T) {q : Option GroundTerm} :
    Eval (K₀ sig) 516 [embRes r] q ↔ q = r.map emb :=
  evalF_iff (valOf_eval_kht r)

end Shape

/-! ## `mkInj` on encodings -/

/-- At a term that is neither an injection nor `bot`, `mkInj` injects it (`inj-new`). -/
theorem mkInjF_new (a b : Int) {t : T} (h1 : isIjT_kkc t = false) (h2 : t ≠ .bot) :
    mkInjF a b t = some (.ij a b t) := by
  cases t <;> first | rfl | exact absurd rfl h2 | simp [isIjT_kkc] at h1

/-- The encoding of a value that is not an injection and has a `kore.k` form for each literal is
neither an injection nor `bot`: `mkInj` injects it. -/
theorem mkInjF_enc (a b : Int) {v : GroundTerm} (hi : v.isInj = false) (lv : litsV v = true) :
    mkInjF a b (enc v) = some (.ij a b (enc v)) :=
  mkInjF_new a b (enc_isIj_kkc hi) fun h => by
    have hn := enc_ne_bot lv
    rw [h] at hn
    exact hn

/-- The argument of a sorted injection is no injection (`sortOf`), so `mkInj` at its encoding
gives the injection's encoding. -/
theorem mkInjF_enc_inj {c : Semantics} {a b : Srt} {w : GroundTerm} {s : Srt}
    (hv : c.sortOf (.inj a b w) = some s) (lv : litsV w = true) :
    mkInjF a b (enc w) = some (enc (.inj a b w)) := by
  rw [mkInjF_enc a b (sortOf_inj_kel hv).2.1 lv, enc]

/-- `mkInj(A, B, T)` at the encoding of a sorted injection's argument evaluates to the
injection's encoding. -/
theorem mkInjF_eval_enc_inj {c : Semantics} {a b : Srt} {w : GroundTerm} {s : Srt}
    (hv : c.sortOf (.inj a b w) = some s) (lv : litsV w = true) :
    Eval (K₀ sig) 493 [.dv 3 (.int a), .dv 3 (.int b), emb (enc w)] (some (emb (enc (.inj a b w)))) := by
  have h := mkInjF.eval a b (enc w)
  rwa [mkInjF_enc_inj hv lv] at h

/-! ## Checks -/

#check @instF.eval
#check @instF.eval_iff
#check @instTsF.eval
#check @instTsF.eval_iff
#check @mkInjF.eval
#check @mkInjF.eval_iff
#check @bindVarF.eval
#check @bindVarF.eval_iff
#check @bindAfterF.eval
#check @bindAfterF.eval_iff
#check @catF.eval
#check @catF.eval_iff
#check @mkInjF_new
#check @mkInjF_enc
#check @mkInjF_enc_inj
#check @mkInjF_eval_enc_inj
#check @look_eval_kht
#check @valOf_eval_kht

open Lean in
#eval show CoreM Unit from do
  for n in [``helpTerms_names, ``instF.eval, ``instF.eval_iff, ``instTsF.eval, ``instTsF.eval_iff,
      ``mkInjF.eval, ``mkInjF.eval_iff, ``bindVarF.eval, ``bindVarF.eval_iff, ``bindAfterF.eval,
      ``bindAfterF.eval_iff, ``catF.eval, ``catF.eval_iff, ``look_eval_iff_kht, ``valOf_eval_iff_kht,
      ``mkInjF_new, ``mkInjF_enc, ``mkInjF_enc_inj, ``mkInjF_eval_enc_inj] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
