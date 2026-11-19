/-
  kore.k's `eval` is the identity on the encoding of a value: `eval_value` gives
  `Eval (K₀ sig) eval [embD E, emb (enc v)] (some (emb (enc v)))` for a value `v` with a sort in
  `d₀ d`, every literal of which has a kore.k form (`litsV`), where `encDef d = some E` and no
  parameter of `d` is an open generator; `eval_value_iff` gives that this is its only result.

  By induction on `v`, one equation of `eval` per form of the encoding:
  - `iv`, `bv`, `tk` (`ev-int`, `ev-bool`, `ev-tok`) and `co` (`ev-val`: a collection's elements
    are not evaluated again) give the term itself;
  - `ij(A, B, T)` (`ev-inj`) gives `mkInj(A, B, eval(D, T))`; the argument of a sorted injection is
    no injection (`sortOf`) and its encoding holds no `bot` (`litsV`), so `mkInj` injects it
    (`inj-new`, HelpTerms' `mkInjF_enc_inj`);
  - `ap(F, As)` (`ev-app`) gives `apply(D, F, evalTs(D, As))`; `evalTs` gives the arguments back,
    none of them is `bot`, so `hasBot` is false and `apply-look` applies; the head of a sorted
    constructor term is a constructor of `d` (no overload by C1, no open generator by the
    hypothesis), so it is no label of `d`'s functions (C4) and `lookup` gives `nofn`, and
    `apply-ctor` gives `ap(F, As)`.

  `encodable` alone does not give the hypothesis on the parameters: a parameter with `raw` and an
  `impl` passes C2, its application to sorted arguments is a sorted value of `d₀ d` (the
  interpretation `HookParams.none` leaves it raw), and C4 does not keep its number out of the
  functions' labels, where `lookup` would find a function and `eval` would apply it. `execReady`
  gives it (`noRaw_kev`): its `paramsPlain` gives an open generator no `impl`, and C2 gives every
  parameter one.

  Every equation of `eval`, `evalTs`, `apply`, `applyL` and `hasBot` is at priority 50, so each
  step is `Eval.clause` with no equation of a smaller priority to fail. The clauses are the
  semantics' own, as literals tied to `lookupFn` by the kernel.
-/
import User.HelpTerms
import User.KkGenEmb

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The clauses, as the semantics holds them -/

namespace EvalV
open _root_.KK Terms

/-- `eval` (464): `ev-app`, `ev-col`, `ev-el`, `ev-en`, `ev-hook`, `ev-inj`, `ev-kv`, `ev-bool`,
`ev-val`, `ev-int`, `ev-tok`. -/
def evalDef_kev : Fn :=
  { label := 464, args := [45, 33], result := 33, total := false, clauses := [
    plainCl [45, 3, 43] [.var 0, .app 408 [.var 1, .var 2]] (.app 448 [.var 0, .var 1, .app 467 [.var 0, .var 2]]),
    plainCl [45, 34, 3, 43] [.var 0, .app 414 [.var 1, .var 2, .var 3]]
      (.app 459 [.var 1, .var 2, .app 467 [.var 0, .var 3]]),
    plainCl [45, 33] [.var 0, .app 419 [.var 1]] (.app 492 [.app 464 [.var 0, .var 1]]),
    plainCl [45, 33, 33] [.var 0, .app 420 [.var 1, .var 2]]
      (.app 463 [.app 464 [.var 0, .var 2], .app 464 [.var 0, .var 1]]),
    plainCl [45, 3, 43] [.var 0, .app 423 [.var 1, .var 2]] (.app 508 [.var 1, .app 467 [.var 0, .var 2]]),
    plainCl [45, 3, 3, 33] [.var 0, .app 424 [.var 1, .var 2, .var 3]]
      (.app 493 [.var 1, .var 2, .app 464 [.var 0, .var 3]]),
    plainCl [45, 33, 33] [.var 0, .app 426 [.var 1, .var 2]]
      (.app 494 [.app 464 [.var 0, .var 1], .app 464 [.var 0, .var 2]]),
    plainCl [45, 2, 33] [.var 0, .as (.app 413 [.var 1]) 2] (.var 2),
    plainCl [45, 34, 3, 43, 33] [.var 0, .as (.app 416 [.var 1, .var 2, .var 3]) 4] (.var 4),
    plainCl [45, 3, 33] [.var 0, .as (.app 425 [.var 1]) 2] (.var 2),
    plainCl [45, 3, 10, 33] [.var 0, .as (.app 443 [.var 1, .var 2]) 3] (.var 3)] }

/-- `evalTs` (467): `evs-cons`, `evs-nil`. -/
def evalTsDef_kev : Fn :=
  { label := 467, args := [45, 43], result := 43, total := false, clauses := [
    plainCl [45, 33, 43] [.var 0, .app 407 [.var 1, .var 2]]
      (.app 407 [.app 464 [.var 0, .var 1], .app 467 [.var 0, .var 2]]),
    plainCl [45, 43] [.var 0, .as (.app 406 []) 1] (.var 1)] }

/-- `apply` (448): `apply-look`, `apply-bot`. -/
def applyDef_kev : Fn :=
  { label := 448, args := [45, 3, 43], result := 33, total := false, clauses := [
    plainCl [32, 39, 42, 45, 3, 43] [.as (.app 417 [.var 0, .var 1, .var 2]) 3, .var 4, .var 5]
      (.app 449 [.var 3, .var 4, .var 5, .app 485 [.var 4, .var 1]])
      (req := some (.app 3 [.app 471 [.var 5]])),
    plainCl [45, 3, 43] [.var 0, .var 1, .var 2] (.app 412 []) (req := some (.app 471 [.var 2]))] }

/-- `applyL` (449): `apply-fn`, `apply-ctor`. -/
def applyLDef_kev : Fn :=
  { label := 449, args := [45, 3, 43, 40], result := 33, total := false, clauses := [
    plainCl [45, 3, 43, 35] [.var 0, .var 1, .var 2, .app 422 [.var 3]]
      (.app 502 [.var 1, .var 2, .app 465 [.var 0, .var 2, .var 3, .app 495 [.var 3, .app 431 []]]]),
    plainCl [45, 3, 43] [.var 0, .var 1, .var 2, .app 432 []] (.app 408 [.var 1, .var 2])] }

/-- `hasBot` (471): `hasbot-nil`, `hasbot-cons`. -/
def hasBotDef_kev : Fn :=
  { label := 471, args := [43], result := 2, total := false, clauses := [
    plainCl [] [.app 406 []] (.dv 2 (.bool false)),
    plainCl [33, 43] [.app 407 [.var 0, .var 1]]
      (.app 6 [.app 29 [kq 0, .app 0 [.inj 33 1 (.app 412 []), .app 1 []]], .app 471 [.var 1]])] }

theorem evalDef_lookup_kev : c₀.lookupFn 464 = some evalDef_kev := by kernel_rfl
theorem evalTsDef_lookup_kev : c₀.lookupFn 467 = some evalTsDef_kev := by kernel_rfl
theorem applyDef_lookup_kev : c₀.lookupFn 448 = some applyDef_kev := by kernel_rfl
theorem applyLDef_lookup_kev : c₀.lookupFn 449 = some applyLDef_kev := by kernel_rfl
theorem hasBotDef_lookup_kev : c₀.lookupFn 471 = some hasBotDef_kev := by kernel_rfl

end EvalV

/-! ## Shared steps -/

section Steps
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms EvalV

/-- `kseq(inj{Term,KItem}(T), dotk)` at a term whose value is an embedding. -/
theorem kqT_eval_kev {σ : Subst} {a : Term} {t : T} (h : EvalTerm c₀ σ a (some (emb t))) :
    EvalTerm c₀ σ (.app 0 [.inj 33 1 a, .app 1 []]) (some (kqV t)) := by
  have e : injNormal 33 1 (emb t) = .inj 33 1 (emb t) := by rw [emb_ctor]; rfl
  have := EvalTerm.ctor (σ := σ) (f := 0) (by decide +kernel)
    (.cons (EvalTerm.inj (a := 33) (b := 1) h) (.cons (EvalTerm.ctor (ts := []) (f := 1) (by decide +kernel) .nil) .nil))
  rw [kqV, ← e]
  exact this

/-- `A ==K B` on the K sequences of two terms whose values are embeddings. -/
theorem keqT_eval_kev {σ : Subst} {a b : Term} {t u : T} (ha : EvalTerm c₀ σ a (some (emb t)))
    (hb : EvalTerm c₀ σ b (some (emb u))) :
    EvalTerm c₀ σ (.app 29 [.app 0 [.inj 33 1 a, .app 1 []], .app 0 [.inj 33 1 b, .app 1 []]])
      (some (bool (decide (t = u)))) := by
  refine EvalTerm.hook (by decide +kernel) rfl (.cons (kqT_eval_kev ha) (.cons (kqT_eval_kev hb) .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  rw [← kqV_cmp_kht]
  exact Semantics.hookRes_of_value (hook_kEq _ _)

/-- `A orBool B` at two Bool values. -/
theorem or_eval_kev {σ : Subst} {a b : Term} {x y : Bool} (ha : EvalTerm c₀ σ a (some (.dv 2 (.bool x))))
    (hb : EvalTerm c₀ σ b (some (.dv 2 (.bool y)))) :
    EvalTerm c₀ σ (.app 6 [a, b]) (some (.dv 2 (.bool (x || y)))) := by
  refine EvalTerm.hook (by decide +kernel) (by decide +kernel) (.cons ha (.cons hb .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  exact Semantics.hookRes_of_value ((hook_or _).trans rfl)

/-- `notBool A` at a Bool value. -/
theorem not_eval_kev {σ : Subst} {a : Term} {x : Bool} (ha : EvalTerm c₀ σ a (some (.dv 2 (.bool x)))) :
    EvalTerm c₀ σ (.app 3 [a]) (some (.dv 2 (.bool (!x)))) := by
  refine EvalTerm.hook (by decide +kernel) (by decide +kernel) (.cons ha .nil)
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  exact Semantics.hookRes_of_value ((hook_not _).trans rfl)

/-- `hasBot(Ts)` is false at a list without `bot`. -/
theorem hasBot_false_kev : ∀ (ts : List T), (∀ t ∈ ts, t ≠ .bot) →
    Eval c₀ 471 [embTs ts] (some (.dv 2 (.bool false)))
  | [], _ =>
    clause_kht (σ := enumFrom 0 []) hasBotDef_lookup_kev (List.mem_cons_self ..) (ws_enum .nil)
      (.cons (.ctor ctor_406 .nil) .nil) (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  | t :: ts, h => by
    have ih := hasBot_false_kev ts fun u hu => h u (List.mem_cons_of_mem _ hu)
    have hk := keqT_eval_kev (σ := enumFrom 0 [emb t, embTs ts]) (u := .bot) (ev_var (i := 0) rfl)
      (ev_ctor .nil ctor_412)
    rw [decide_eq_false (h t (List.mem_cons_self ..))] at hk
    exact clause_kht (σ := enumFrom 0 [emb t, embTs ts]) hasBotDef_lookup_kev
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) .nil)))
      (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (or_eval_kev hk (ev_call (.cons (ev_var rfl) .nil) ih notCtor_471 notHook_471 notParam_471))

end Steps

/-! ## `eval` at each form of an encoded value -/

section Forms
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms EvalV

/-- `ev-int`. -/
theorem eval_iv_kev (E : D) (i : Int) : Eval c₀ 464 [embD E, emb (.iv i)] (some (emb (.iv i))) :=
  clause_kht (σ := enumFrom 0 [embD E, .dv 3 (.int i), emb (.iv i)]) evalDef_lookup_kev
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))))
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int i) (.cons (emb_sorted_c₀ _) .nil))))
    (.cons (.var rfl) (.cons (.as (.ctor ctor_425 (.cons (.var rfl) .nil)) rfl) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)

/-- `ev-bool`. -/
theorem eval_bv_kev (E : D) (b : Bool) : Eval c₀ 464 [embD E, emb (.bv b)] (some (emb (.bv b))) :=
  clause_kht (σ := enumFrom 0 [embD E, .dv 2 (.bool b), emb (.bv b)]) evalDef_lookup_kev
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_bool b) (.cons (emb_sorted_c₀ _) .nil))))
    (.cons (.var rfl) (.cons (.as (.ctor ctor_413 (.cons (.var rfl) .nil)) rfl) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)

/-- `ev-tok`. -/
theorem eval_tk_kev (E : D) (s : Int) (x : String) :
    Eval c₀ 464 [embD E, emb (.tk s x)] (some (emb (.tk s x))) :=
  clause_kht (σ := enumFrom 0 [embD E, .dv 3 (.int s), .dv 10 (.tok x), emb (.tk s x)]) evalDef_lookup_kev
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))))))
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int s) (.cons (sort_string_kemb x)
      (.cons (emb_sorted_c₀ _) .nil)))))
    (.cons (.var rfl) (.cons (.as (.ctor ctor_443 (.cons (.var rfl) (.cons (.var rfl) .nil))) rfl) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)

/-- `ev-val`: a collection is not evaluated again. -/
theorem eval_co_kev (E : D) (k : Kind) (c : Int) (es : List T) :
    Eval c₀ 464 [embD E, emb (.co k c es)] (some (emb (.co k c es))) :=
  clause_kht (σ := enumFrom 0 [embD E, embK k, .dv 3 (.int c), embTs es, emb (.co k c es)]) evalDef_lookup_kev
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))))))))
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embK_sorted_c₀ k) (.cons (sort_int c)
      (.cons (embTs_sorted_c₀ es) (.cons (emb_sorted_c₀ _) .nil))))))
    (.cons (.var rfl) (.cons (.as (.ctor ctor_416 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) rfl) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)

/-- `ev-inj`: `mkInj(A, B, eval(D, T))`. -/
theorem eval_ij_kev (E : D) (a b : Int) {t u : T} (ht : Eval c₀ 464 [embD E, emb t] (some (emb t)))
    (hu : mkInjF a b t = some u) : Eval c₀ 464 [embD E, emb (.ij a b t)] (some (emb u)) := by
  have hm := mkInjF_eval_c₀ a b t
  rw [hu] at hm
  exact clause_kht (σ := enumFrom 0 [embD E, .dv 3 (.int a), .dv 3 (.int b), emb t]) evalDef_lookup_kev
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int a) (.cons (sort_int b) (.cons (emb_sorted_c₀ t) .nil)))))
    (.cons (.var rfl) (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl)
      (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ht notCtor_464 notHook_464 notParam_464) .nil)))
      hm notCtor_493 notHook_493 notParam_493)

/-- `evalTs(D, Ts)` gives the list back where `eval` gives each term back. -/
theorem evalTs_kev (E : D) : ∀ (ts : List T), (∀ t ∈ ts, Eval c₀ 464 [embD E, emb t] (some (emb t))) →
    Eval c₀ 467 [embD E, embTs ts] (some (embTs ts))
  | [], _ =>
    clause_kht (σ := enumFrom 0 [embD E, embTs []]) evalTsDef_lookup_kev
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ []) .nil)))
      (.cons (.var rfl) (.cons (.as (.ctor ctor_406 .nil) rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | t :: ts, h => by
    have ih := evalTs_kev E ts fun u hu => h u (List.mem_cons_of_mem _ hu)
    exact clause_kht (σ := enumFrom 0 [embD E, emb t, embTs ts]) evalTsDef_lookup_kev (List.mem_cons_self ..)
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) .nil))))
      (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (h t (List.mem_cons_self ..))
          notCtor_464 notHook_464 notParam_464)
        (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih notCtor_467 notHook_467 notParam_467) .nil))
        ctor_407)

/-- `apply-ctor`: `applyL` at `nofn` gives the application. -/
theorem applyL_ctor_kev (E : D) (f : Int) (ts : List T) :
    Eval c₀ 449 [embD E, .dv 3 (.int f), embTs ts, embLook none] (some (emb (.ap f ts))) :=
  clause_kht (σ := enumFrom 0 [embD E, .dv 3 (.int f), embTs ts]) applyLDef_lookup_kev
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int f) (.cons (embTs_sorted_c₀ ts) .nil))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_432 .nil) .nil))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_408)

/-- `apply-look` then `apply-ctor`: at arguments without `bot` and a symbol `lookup` does not find,
`apply` gives the application. -/
theorem apply_ctor_kev (E : D) (f : Int) (ts : List T) (hb : ∀ t ∈ ts, t ≠ .bot)
    (hl : Gen.lookupF f E.fns = some none) :
    Eval c₀ 448 [embD E, .dv 3 (.int f), embTs ts] (some (emb (.ap f ts))) := by
  have hlook : Eval c₀ 485 [.dv 3 (.int f), embFns E.fns] (some (embLook none)) := by
    have h := Gen.lookupF.eval f E.fns
    rw [hl] at h
    exact h
  have hnot := not_eval_kev (σ := enumFrom 0 [embS E.subs, embFns E.fns, embRls E.rules, embD E,
      .dv 3 (.int f), embTs ts]) (ev_call (.cons (ev_var (i := 5) rfl) .nil) (hasBot_false_kev ts hb)
      notCtor_471 notHook_471 notParam_471)
  exact clause_kht (σ := enumFrom 0 [embS E.subs, embFns E.fns, embRls E.rules, embD E,
      .dv 3 (.int f), embTs ts]) applyDef_lookup_kev (List.mem_cons_self ..)
    (ws_enum (.cons (embS_sorted_c₀ E.subs) (.cons (embFns_sorted_c₀ E.fns) (.cons (embRls_sorted_c₀ E.rules)
      (.cons (embD_sorted_c₀ E) (.cons (sort_int f) (.cons (embTs_sorted_c₀ ts) .nil)))))))
    (.cons (.as (.ctor ctor_417 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) rfl)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))
    (fun _ h => by cases h; exact hnot) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
      (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) hlook notCtor_485 notHook_485 notParam_485) .nil))))
      (applyL_ctor_kev E f ts) notCtor_449 notHook_449 notParam_449)

/-- `ev-app`: at arguments `eval` gives back, none `bot`, and a symbol `lookup` does not find,
`eval` gives the application back. -/
theorem eval_ap_kev (E : D) (f : Int) (ts : List T)
    (hts : ∀ t ∈ ts, Eval c₀ 464 [embD E, emb t] (some (emb t))) (hb : ∀ t ∈ ts, t ≠ .bot)
    (hl : Gen.lookupF f E.fns = some none) :
    Eval c₀ 464 [embD E, emb (.ap f ts)] (some (emb (.ap f ts))) :=
  clause_kht (σ := enumFrom 0 [embD E, .dv 3 (.int f), embTs ts]) evalDef_lookup_kev (List.mem_cons_self ..)
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int f) (.cons (embTs_sorted_c₀ ts) .nil))))
    (.cons (.var rfl) (.cons (.ctor ctor_408 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl)
      (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (evalTs_kev E ts hts)
        notCtor_467 notHook_467 notParam_467) .nil)))
      (apply_ctor_kev E f ts hb hl) notCtor_448 notHook_448 notParam_448)

end Forms

/-! ## `lookup` misses a symbol that labels no function -/

theorem lookupF_none_kev (f : Int) : ∀ (fs : List (Int × List Cl)), (∀ p ∈ fs, p.1 ≠ f) →
    Gen.lookupF f fs = some none
  | [], _ => rfl
  | (g, cs) :: fs, h => by
    have hg : f ≠ g := fun e => h (g, cs) (List.mem_cons_self ..) e.symm
    rw [Gen.lookupF, ite_eq_right_of_eq_false _ _ (eq_false hg), ite_eq_left_of_eq_true _ _ (eq_true hg)]
    exact lookupF_none_kev f fs fun p hp => h p (List.mem_cons_of_mem _ hp)

/-! ## The identity on values -/

/-- The parts of `encodable` the proof reads: no overload (C1) and no constructor among the
functions' labels (C4). -/
theorem encodable_heads_kev {d : Semantics} (h : encodable d = true) :
    d.ovls = [] ∧ ∀ f ∈ fnLabels d, d.isCtor f = false := by
  have ho := (encodable_facts h).1
  simp only [encodable, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  simp only [headsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h4
  exact ⟨ho, h4.1⟩

/-- Under `execReady` and `encodable` no parameter is an open generator: `paramsPlain` gives an
open generator no `impl`, and C2 gives every parameter a collection `impl`. -/
theorem noRaw_kev {d : Semantics} {E : D} (hr : CExec.execReady d = true) (hE : encDef d = some E) :
    ∀ k ∈ d.params, k.raw = false := by
  intro k hk
  have hc : encodable d = true := by rw [← encDef_isSome, hE]; rfl
  have hs : d.sortedOK = true := by
    simp only [CExec.execReady, Bool.and_eq_true] at hr
    exact hr.1.1.1.1.1.1
  have hp : d.paramsPlain = true := by
    simp only [Semantics.sortedOK, Bool.and_eq_true] at hs
    exact hs.2
  have h2 : paramsOK d = true := by
    simp only [encodable, Bool.and_eq_true] at hc
    exact hc.1.1.1.1.1.1.1.1.2
  cases hraw : k.raw
  · rfl
  · have hi := (Semantics.raw_of_paramsPlain hp hk hraw).1
    simp only [paramsOK, List.all_eq_true] at h2
    have := h2 k hk
    simp [hi] at this

/-- The encoding of a sorted value of `d₀ d` whose literals all have a kore.k form evaluates to
itself at `encDef d`, where no parameter of `d` is an open generator. -/
theorem eval_value {d : Semantics} {E : D} (hE : encDef d = some E) (hraw : ∀ k ∈ d.params, k.raw = false)
    {v : GroundTerm} {s : Srt} (hv : (d₀ d).sortOf v = some s) (lv : litsV v = true) :
    Eval (K₀ sig) 464 [embD E, emb (enc v)] (some (emb (enc v))) := by
  have hc : encodable d = true := by rw [← encDef_isSome, hE]; rfl
  obtain ⟨hov, h4⟩ := encodable_heads_kev hc
  have hfns : E.fns = d.allFns.map (fun fn => ((fn.label : Int), fn.clauses.map (encCl d))) := by
    unfold encDef at hE
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hE
    cases hE
    rfl
  show Eval _root_.KK.c₀ 464 [embD E, emb (enc v)] (some (emb (enc v)))
  induction v using gtInd_kel generalizing s with
  | hctor f vs ih =>
    simp only [litsV] at lv
    have lvs := litsVL_iff.mp lv
    rcases (d₀ d).sortOf_ctor_iff.mp hv with ⟨k, hk, hs, -⟩ | ⟨-, o, ho, -⟩ | ⟨-, -, k, hk, -⟩
    · have hct : d.isCtor f = true := by
        show (lookupSig d.ctorSigs f).isSome = true
        rw [show d.ctorSigs = (d₀ d).ctorSigs from rfl, hk]; rfl
      have hl : Gen.lookupF (f : Int) E.fns = some none := by
        refine lookupF_none_kev _ _ fun p hp e => ?_
        rw [hfns, List.mem_map] at hp
        obtain ⟨fn, hfn, rfl⟩ := hp
        have e' : fn.label = f := Int.ofNat.inj e
        have := h4 fn.label (List.mem_map_of_mem hfn)
        rw [e', hct] at this
        cases this
      have hmem : ∀ t ∈ encTs vs, ∃ w ∈ vs, t = enc w := by
        intro t ht
        rw [encTs_eq_map, List.mem_map] at ht
        obtain ⟨w, hw, rfl⟩ := ht
        exact ⟨w, hw, rfl⟩
      refine eval_ap_kev E f (encTs vs) (fun t ht => ?_) (fun t ht => ?_) hl
      · obtain ⟨w, hw, rfl⟩ := hmem t ht
        obtain ⟨s', -, hs'⟩ := sortsOf_mem_kel hs w hw
        exact ih w hw hs' (lvs w hw)
      · obtain ⟨w, hw, rfl⟩ := hmem t ht
        intro e
        have hn := enc_ne_bot (lvs w hw)
        rw [e] at hn
        exact hn
    · rw [show (d₀ d).lookupOvl f = none by simp [Semantics.lookupOvl, d₀, Semantics.withHooks, hov]] at ho
      cases ho
    · obtain ⟨hkm, hkr, -⟩ := (d₀ d).lookupOpen_spec hk
      rw [hraw k hkm] at hkr
      cases hkr
  | hinj a b w ih =>
    obtain ⟨-, -, hw, -⟩ := sortOf_inj_kel hv
    simp only [litsV] at lv
    exact eval_ij_kev E a b (ih hw lv) (mkInjF_enc_inj hv lv)
  | hdv s' l =>
    simp only [litsV, Option.isSome_iff_exists] at lv
    obtain ⟨t, ht⟩ := lv
    rw [enc_dv_of_encLit ht]
    rcases encLit_some ht with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩
    · exact eval_iv_kev E i
    · exact eval_bv_kev E b
    · exact eval_tk_kev E s' x
  | hmap s' es => exact eval_co_kev E _ _ _
  | hset s' es => exact eval_co_kev E _ _ _
  | hlist s' es => exact eval_co_kev E _ _ _

/-- Its only result: `eval` at `K₀ sig` has one result (`KK.coherent`). -/
theorem eval_value_iff {d : Semantics} {E : D} (hE : encDef d = some E) (hraw : ∀ k ∈ d.params, k.raw = false)
    {v : GroundTerm} {s : Srt} (hv : (d₀ d).sortOf v = some s) (lv : litsV v = true) {r : Option GroundTerm} :
    Eval (K₀ sig) 464 [embD E, emb (enc v)] r ↔ r = some (emb (enc v)) :=
  evalF_iff (eval_value hE hraw hv lv)

/-- The symbol 464 is kore.k's `eval`. -/
theorem eval_name_kev :
    RefKk.defn.sem.symName 464 = "Lbleval'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Def'Unds'Term" := by
  decide +kernel

/-! ## Checks -/

#check @eval_value
#check @eval_value_iff
#check @eval_ap_kev
#check @apply_ctor_kev
#check @evalTs_kev
#check @hasBot_false_kev
#check @noRaw_kev

open Lean in
#eval show CoreM Unit from do
  for n in [``eval_value, ``eval_value_iff, ``eval_name_kev, ``eval_ap_kev, ``apply_ctor_kev,
      ``applyL_ctor_kev, ``evalTs_kev, ``eval_ij_kev, ``eval_co_kev, ``eval_tk_kev, ``eval_bv_kev,
      ``eval_iv_kev, ``hasBot_false_kev, ``not_eval_kev, ``lookupF_none_kev, ``encodable_heads_kev, ``noRaw_kev] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
