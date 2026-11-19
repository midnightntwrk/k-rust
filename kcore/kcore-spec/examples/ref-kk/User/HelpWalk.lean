/-
  kore.k's walk and lookup helpers over the mirrors, on kore.k's semantics read from its kompiled
  text, in one shape: a Lean function `F` of the mirrors, `F.eval : Eval (K₀ sig) f [emb x, …] …` at
  the function's symbol `f` with no hypothesis on the arguments (each embedding is a value of its
  sort, User.Sig and User.EmbKit), and `F.eval_iff` from `evalF_iff`.

  Every function here has a value at every argument, so `F` gives the result itself and `F.eval`
  has `some` of its embedding: `prioF`, `rprioF`, `cprioF` (an Int at an Int and a Bool), `overF`,
  `leastF`, `nextRlF`, `nextClF` (a `Prio`, embedded by `embPrio`), `dropF` (a `Ts`), `ensureF` (a
  `Term`), `hasBotF` (a Bool), `lenF`, and kore.k's `lex` and `b2i` as KKEnc.lean's `lexF` and
  `b2iF`, the functions `cmpF` is written with. `look` is HelpTerms' `look_eval_kht` restated at
  `K₀ sig` as `lookF.eval`; `valOf`, `lookup` and `subsOf` are User.KkGenEmb's `Gen.valOfF`,
  `Gen.lookupF` and `Gen.subsOfF`, whose `eval` and `eval_iff` the checks below name.

  The clauses are the semantics' own, as literals tied to `lookupFn` by the kernel.
-/
import User.HelpTerms
import User.KkGenEmb

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The functions over the mirrors -/

/-- kore.k's `prio(P, O)`: an `[owise]` rule or equation is at 200, any other at its priority. -/
def prioF (p : Int) : Bool → Int
  | false => p
  | true => 200

/-- kore.k's `rprio(P, O)`, a rule's priority. -/
def rprioF (p : Int) (o : Bool) : Int := prioF p o

/-- kore.k's `cprio(P, O)`, an equation's priority. -/
def cprioF (p : Int) (o : Bool) : Int := prioF p o

/-- kore.k's `over(P, B)`: the priority if it is above the bound. -/
def overF (p : Int) : Option Int → Option Int
  | none => some p
  | some b => if p > b then some p else none

/-- kore.k's `least(P, Q)`. -/
def leastF : Option Int → Option Int → Option Int
  | none, q => q
  | some p, none => some p
  | some p, some q => if p ≤ q then some p else some q

/-- kore.k's `nextRl(Rs, B)`: the least priority of the rules above the bound. -/
def nextRlF : List Rl → Option Int → Option Int
  | [], _ => none
  | r :: rs, b => leastF (overF (rprioF r.prio r.owise) b) (nextRlF rs b)

/-- kore.k's `nextCl(Cs, B)`: the least priority of the equations above the bound. -/
def nextClF : List Cl → Option Int → Option Int
  | [], _ => none
  | c :: cs, b => leastF (overF (cprioF c.prio c.owise) b) (nextClF cs b)

/-- kore.k's `drop(X, Ts)`: the list without the terms equal to `X`. -/
def dropF (x : T) : List T → List T
  | [] => []
  | t :: ts => if t = x then dropF x ts else t :: dropF x ts

/-- kore.k's `ensure(E, T)`: `T` where the ensures is `bv(true)`, else `bot`. -/
def ensureF (e t : T) : T := if e = .bv true then t else .bot

/-- kore.k's `hasBot(Ts)`: whether a term of the list is `bot`. -/
def hasBotF : List T → Bool
  | [] => false
  | t :: ts => decide (t = .bot) || hasBotF ts

/-- kore.k's `len(Ts)`. -/
def lenF (ts : List T) : Int := ts.length

theorem lenF_cons_khw (t : T) (ts : List T) : lenF (t :: ts) = 1 + lenF ts := by
  simp only [lenF, List.length_cons]; omega

/-! ## The symbols -/

/-- Each symbol number the evaluations below are at has the KORE name of the function. -/
theorem helpWalk_names :
    RefKk.defn.sem.symName 450 = "Lblb2i'LParUndsRParUnds'KORE'Unds'Int'Unds'Bool" ∧
    RefKk.defn.sem.symName 460 = "Lblcprio'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Int'Unds'Bool" ∧
    RefKk.defn.sem.symName 462 = "Lbldrop'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 463 = "Lblensure'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 471 = "LblhasBot'LParUndsRParUnds'KORE'Unds'Bool'Unds'Ts" ∧
    RefKk.defn.sem.symName 480 = "Lblleast'LParUndsCommUndsRParUnds'KORE'Unds'Prio'Unds'Prio'Unds'Prio" ∧
    RefKk.defn.sem.symName 481 = "Lbllen'LParUndsRParUnds'KORE'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 483 = "Lbllex'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Int'Unds'Int" ∧
    RefKk.defn.sem.symName 495 = "LblnextCl'LParUndsCommUndsRParUnds'KORE'Unds'Prio'Unds'Clauses'Unds'Prio" ∧
    RefKk.defn.sem.symName 496 = "LblnextRl'LParUndsCommUndsRParUnds'KORE'Unds'Prio'Unds'Rules'Unds'Prio" ∧
    RefKk.defn.sem.symName 498 = "Lblover'LParUndsCommUndsRParUnds'KORE'Unds'Prio'Unds'Int'Unds'Prio" ∧
    RefKk.defn.sem.symName 499 = "Lblprio'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Int'Unds'Bool" ∧
    RefKk.defn.sem.symName 503 = "Lblrprio'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Int'Unds'Bool" ∧
    RefKk.defn.sem.symName 6 = "Lbl'Unds'orBool'Unds'" ∧
    RefKk.defn.sem.symName 12 = "Lbl'UndsPlus'Int'Unds'" ∧
    RefKk.defn.sem.symName 20 = "Lbl'Unds-LT-Eqls'Int'Unds'" ∧
    RefKk.defn.sem.symName 21 = "Lbl'Unds-GT-'Int'Unds'" := by
  decide +kernel

/-! ## The clauses, as the semantics holds them -/

namespace Walk
open _root_.KK Terms

/-- `prio` (499): `prio-given`, `prio-owise`. -/
def prioDef : Fn :=
  { label := 499, args := [3, 2], result := 3, total := false, clauses := [
    plainCl [3] [.var 0, .dv 2 (.bool false)] (.var 0),
    plainCl [3] [.var 0, .dv 2 (.bool true)] (.dv 3 (.int 200))] }

/-- `rprio` (503). -/
def rprioDef : Fn :=
  { label := 503, args := [3, 2], result := 3, total := false, clauses := [
    plainCl [3, 2] [.var 0, .var 1] (.app 499 [.var 0, .var 1])] }

/-- `cprio` (460). -/
def cprioDef : Fn :=
  { label := 460, args := [3, 2], result := 3, total := false, clauses := [
    plainCl [3, 2] [.var 0, .var 1] (.app 499 [.var 0, .var 1])] }

/-- `over` (498): `over-above`, `over-below`, `over-free`. -/
def overDef : Fn :=
  { label := 498, args := [3, 36], result := 36, total := false, clauses := [
    plainCl [3, 3] [.var 0, .app 410 [.var 1]] (.app 410 [.var 0]) (req := some (.app 21 [.var 0, .var 1])),
    plainCl [3, 3] [.var 0, .app 410 [.var 1]] (.app 431 []) (req := some (.app 20 [.var 0, .var 1])),
    plainCl [3] [.var 0, .app 431 []] (.app 410 [.var 0])] }

/-- `least` (480): `least-left`, `least-only`, `least-right`, `least-none`. -/
def leastDef : Fn :=
  { label := 480, args := [36, 36], result := 36, total := false, clauses := [
    plainCl [3, 36, 3] [.as (.app 410 [.var 0]) 1, .app 410 [.var 2]] (.var 1)
      (req := some (.app 20 [.var 0, .var 2])),
    plainCl [3, 36] [.as (.app 410 [.var 0]) 1, .app 431 []] (.var 1),
    plainCl [3, 3, 36] [.app 410 [.var 0], .as (.app 410 [.var 1]) 2] (.var 2)
      (req := some (.app 21 [.var 0, .var 1])),
    plainCl [36] [.app 431 [], .var 0] (.var 0)] }

/-- `nextCl` (495): `ncl-nil`, `ncl-cons`. -/
def nextClDef : Fn :=
  { label := 495, args := [35, 36], result := 36, total := false, clauses := [
    plainCl [36] [.app 401 [], .var 0] (.app 431 []),
    plainCl [3, 2, 43, 33, 33, 35, 36] [.app 415 [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5], .var 6]
      (.app 480 [.app 498 [.app 460 [.var 0, .var 1], .var 6], .app 495 [.var 5, .var 6]])] }

/-- `nextRl` (496): `nrl-nil`, `nrl-cons`. -/
def nextRlDef : Fn :=
  { label := 496, args := [42, 36], result := 36, total := false, clauses := [
    plainCl [36] [.app 404 [], .var 0] (.app 431 []),
    plainCl [3, 2, 33, 33, 33, 42, 36] [.app 436 [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5], .var 6]
      (.app 480 [.app 498 [.app 503 [.var 0, .var 1], .var 6], .app 496 [.var 5, .var 6]])] }

/-- `drop` (462): `drop-keep`, `drop-hit`, `drop-nil`. -/
def dropDef : Fn :=
  { label := 462, args := [33, 43], result := 43, total := false, clauses := [
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 407 [.var 1, .app 462 [.var 0, .var 2]])
      (req := some (.app 30 [kq 1, kq 0])),
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 462 [.var 0, .var 2])
      (req := some (.app 29 [kq 1, kq 0])),
    plainCl [33, 43] [.var 0, .as (.app 406 []) 1] (.var 1)] }

/-- `ensure` (463): `ensure-holds`, `ensure-fails` (priority 200, `[owise]`). -/
def ensureDef : Fn :=
  { label := 463, args := [33, 33], result := 33, total := false, clauses := [
    plainCl [33] [.app 413 [.dv 2 (.bool true)], .var 0] (.var 0),
    plainCl [33, 33] [.var 0, .var 1] (.app 412 []) (prio := 200)] }

/-- `hasBot` (471): `hasbot-nil`, `hasbot-cons`. -/
def hasBotDef : Fn :=
  { label := 471, args := [43], result := 2, total := false, clauses := [
    plainCl [] [.app 406 []] (.dv 2 (.bool false)),
    plainCl [33, 43] [.app 407 [.var 0, .var 1]]
      (.app 6 [.app 29 [kq 0, .app 0 [.inj 33 1 (.app 412 []), .app 1 []]], .app 471 [.var 1]])] }

/-- `len` (481): `len-nil`, `len-cons`. -/
def lenDef : Fn :=
  { label := 481, args := [43], result := 3, total := false, clauses := [
    plainCl [] [.app 406 []] (.dv 3 (.int 0)),
    plainCl [33, 43] [.app 407 [.var 0, .var 1]] (.app 12 [.dv 3 (.int 1), .app 481 [.var 1]])] }

/-- `b2i` (450): `b2i-false`, `b2i-true`. -/
def b2iDef : Fn :=
  { label := 450, args := [2], result := 3, total := false, clauses := [
    plainCl [] [.dv 2 (.bool false)] (.dv 3 (.int 0)),
    plainCl [] [.dv 2 (.bool true)] (.dv 3 (.int 1))] }

/-- `lex` (483): `lex-tie`, `lex-first`. -/
def lexDef : Fn :=
  { label := 483, args := [3, 3], result := 3, total := false, clauses := [
    plainCl [3, 3] [.var 0, .var 1] (.var 1) (req := some (.app 23 [.var 0, .dv 3 (.int 0)])),
    plainCl [3, 3] [.var 0, .var 1] (.var 0) (req := some (.app 24 [.var 0, .dv 3 (.int 0)]))] }

theorem prioDef_lookup : c₀.lookupFn 499 = some prioDef := by kernel_rfl
theorem rprioDef_lookup : c₀.lookupFn 503 = some rprioDef := by kernel_rfl
theorem cprioDef_lookup : c₀.lookupFn 460 = some cprioDef := by kernel_rfl
theorem overDef_lookup : c₀.lookupFn 498 = some overDef := by kernel_rfl
theorem leastDef_lookup : c₀.lookupFn 480 = some leastDef := by kernel_rfl
theorem nextClDef_lookup : c₀.lookupFn 495 = some nextClDef := by kernel_rfl
theorem nextRlDef_lookup : c₀.lookupFn 496 = some nextRlDef := by kernel_rfl
theorem dropDef_lookup : c₀.lookupFn 462 = some dropDef := by kernel_rfl
theorem ensureDef_lookup : c₀.lookupFn 463 = some ensureDef := by kernel_rfl
theorem hasBotDef_lookup : c₀.lookupFn 471 = some hasBotDef := by kernel_rfl
theorem lenDef_lookup : c₀.lookupFn 481 = some lenDef := by kernel_rfl
theorem b2iDef_lookup : c₀.lookupFn 450 = some b2iDef := by kernel_rfl
theorem lexDef_lookup : c₀.lookupFn 483 = some lexDef := by kernel_rfl

end Walk

/-! ## Shared steps -/

section Kit
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

spike_hb in
/-- `kseq(inj{Term,KItem}(T), dotk)` at a term whose value is an embedding. -/
theorem kqT_eval_khw {σ : Subst} {a : Term} {t : T} (h : EvalTerm c₀ σ a (some (emb t))) :
    EvalTerm c₀ σ (.app 0 [.inj 33 1 a, .app 1 []]) (some (kqV t)) := by
  have e : injNormal 33 1 (emb t) = .inj 33 1 (emb t) := by rw [emb_ctor]; rfl
  have := EvalTerm.ctor (σ := σ) (f := 0) (by decide +kernel)
    (.cons (EvalTerm.inj (a := 33) (b := 1) h) (.cons (EvalTerm.ctor (ts := []) (f := 1) (by decide +kernel) .nil) .nil))
  rw [kqV, ← e]
  exact this

spike_hb in
/-- `A ==K B` on the K sequences of two terms whose values are embeddings. -/
theorem keqT_eval_khw {σ : Subst} {a b : Term} {t u : T} (ha : EvalTerm c₀ σ a (some (emb t)))
    (hb : EvalTerm c₀ σ b (some (emb u))) :
    EvalTerm c₀ σ (.app 29 [.app 0 [.inj 33 1 a, .app 1 []], .app 0 [.inj 33 1 b, .app 1 []]])
      (some (bool (decide (t = u)))) := by
  refine EvalTerm.hook (by decide +kernel) rfl (.cons (kqT_eval_khw ha) (.cons (kqT_eval_khw hb) .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  rw [← kqV_cmp_kht]
  exact Semantics.hookRes_of_value (hook_kEq _ _)

spike_hb in
/-- `A orBool B` at two Bool values. -/
theorem or_eval_khw {σ : Subst} {a b : Term} {x y : Bool} (ha : EvalTerm c₀ σ a (some (.dv 2 (.bool x))))
    (hb : EvalTerm c₀ σ b (some (.dv 2 (.bool y)))) :
    EvalTerm c₀ σ (.app 6 [a, b]) (some (.dv 2 (.bool (x || y)))) := by
  refine EvalTerm.hook (by decide +kernel) (by decide +kernel) (.cons ha (.cons hb .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  exact Semantics.hookRes_of_value ((hook_or _).trans rfl)

spike_hb in
/-- `A +Int B` at two Int values. -/
theorem add_eval_khw {σ : Subst} {a b : Term} {x y : Int} (ha : EvalTerm c₀ σ a (some (.dv 3 (.int x))))
    (hb : EvalTerm c₀ σ b (some (.dv 3 (.int y)))) :
    EvalTerm c₀ σ (.app 12 [a, b]) (some (.dv 3 (.int (x + y)))) := by
  refine EvalTerm.hook (by decide +kernel) (by decide +kernel) (.cons ha (.cons hb .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  exact Semantics.hookRes_of_value rfl

end Kit

/-! ## Priorities -/

section Prio
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Walk

spike_hb in
theorem prioF_eval_c₀ (p : Int) (o : Bool) :
    Eval c₀ 499 [.dv 3 (.int p), .dv 2 (.bool o)] (some (.dv 3 (.int (prioF p o)))) := by
  cases o with
  | false =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int p)]) prioDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (sort_int p) .nil)) (.cons (.var rfl) (.cons .dv .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | true =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int p)]) prioDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (sort_int p) .nil)) (.cons (.var rfl) (.cons .dv .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv

spike_hb in
theorem rprioF_eval_c₀ (p : Int) (o : Bool) :
    Eval c₀ 503 [.dv 3 (.int p), .dv 2 (.bool o)] (some (.dv 3 (.int (rprioF p o)))) :=
  clause_kht (σ := enumFrom 0 [.dv 3 (.int p), .dv 2 (.bool o)]) rprioDef_lookup (List.mem_cons_self ..)
    (ws_enum (.cons (sort_int p) (.cons (sort_bool o) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (prioF_eval_c₀ p o) notCtor_499 notHook_499 notParam_499)

spike_hb in
theorem cprioF_eval_c₀ (p : Int) (o : Bool) :
    Eval c₀ 460 [.dv 3 (.int p), .dv 2 (.bool o)] (some (.dv 3 (.int (cprioF p o)))) :=
  clause_kht (σ := enumFrom 0 [.dv 3 (.int p), .dv 2 (.bool o)]) cprioDef_lookup (List.mem_cons_self ..)
    (ws_enum (.cons (sort_int p) (.cons (sort_bool o) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (prioF_eval_c₀ p o) notCtor_499 notHook_499 notParam_499)

spike_hb in
theorem overF_eval_c₀ (p : Int) (b : Option Int) :
    Eval c₀ 498 [.dv 3 (.int p), embPrio b] (some (embPrio (overF p b))) := by
  cases b with
  | none =>
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int p)]) overDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (ws_enum (.cons (sort_int p) .nil)) (.cons (.var rfl) (.cons (.ctor ctor_431 .nil) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) .nil) ctor_410)
  | some b =>
    have hσ := ws_enum (vars := [3, 3]) (.cons (sort_int p) (.cons (sort_int b) .nil))
    have hp : PatVals c₀ (enumFrom 0 [.dv 3 (.int p), .dv 3 (.int b)]) [.var 0, .app 410 [.var 1]]
        [.dv 3 (.int p), embPrio (some b)] :=
      .cons (.var rfl) (.cons (.ctor ctor_410 (.cons (.var rfl) .nil)) .nil)
    by_cases h : p > b
    · have e : overF p (some b) = some p := ite_pos h _ _
      rw [e]
      refine clause_kht overDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
        (ev_ctor (.cons (ev_var rfl) .nil) ctor_410)
      intro q hq
      cases hq
      have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int p), .dv 3 (.int b)]) (P := (· > ·))
        hook_intGt (ev_var (i := 0) rfl) (ev_var (i := 1) rfl)
      rwa [decide_eq_true h] at hq
    · have e : overF p (some b) = none := ite_neg h _ _
      rw [e]
      refine clause_kht overDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
        ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_431)
      intro q hq
      cases hq
      have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int p), .dv 3 (.int b)]) (P := (· ≤ ·))
        hook_intLe (ev_var (i := 0) rfl) (ev_var (i := 1) rfl)
      rwa [decide_eq_true (Int.not_lt.mp h)] at hq

spike_hb in
theorem leastF_eval_c₀ (a b : Option Int) :
    Eval c₀ 480 [embPrio a, embPrio b] (some (embPrio (leastF a b))) := by
  cases a with
  | none =>
    exact clause_kht (σ := enumFrom 0 [embPrio b]) leastDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (ws_enum (.cons (embPrio_sorted_c₀ b) .nil)) (.cons (.ctor ctor_431 .nil) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | some p =>
    cases b with
    | none =>
      exact clause_kht (σ := enumFrom 0 [.dv 3 (.int p), embPrio (some p)]) leastDef_lookup
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (ws_enum (.cons (sort_int p) (.cons (embPrio_sorted_c₀ _) .nil)))
        (.cons (.as (.ctor ctor_410 (.cons (.var rfl) .nil)) rfl) (.cons (.ctor ctor_431 .nil) .nil))
        (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
    | some q =>
      by_cases h : p ≤ q
      · have e : leastF (some p) (some q) = some p := ite_pos h _ _
        rw [e]
        refine clause_kht (σ := enumFrom 0 [.dv 3 (.int p), embPrio (some p), .dv 3 (.int q)]) leastDef_lookup
          (List.mem_cons_self ..)
          (ws_enum (.cons (sort_int p) (.cons (embPrio_sorted_c₀ _) (.cons (sort_int q) .nil))))
          (.cons (.as (.ctor ctor_410 (.cons (.var rfl) .nil)) rfl) (.cons (.ctor ctor_410 (.cons (.var rfl) .nil)) .nil))
          ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
        intro r hr
        cases hr
        have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int p), embPrio (some p), .dv 3 (.int q)]) (P := (· ≤ ·))
          hook_intLe (ev_var (i := 0) rfl) (ev_var (i := 2) rfl)
        rwa [decide_eq_true h] at hq
      · have e : leastF (some p) (some q) = some q := ite_neg h _ _
        rw [e]
        refine clause_kht (σ := enumFrom 0 [.dv 3 (.int p), .dv 3 (.int q), embPrio (some q)]) leastDef_lookup
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (ws_enum (.cons (sort_int p) (.cons (sort_int q) (.cons (embPrio_sorted_c₀ _) .nil))))
          (.cons (.ctor ctor_410 (.cons (.var rfl) .nil)) (.cons (.as (.ctor ctor_410 (.cons (.var rfl) .nil)) rfl) .nil))
          ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
        intro r hr
        cases hr
        have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int p), .dv 3 (.int q), embPrio (some q)]) (P := (· > ·))
          hook_intGt (ev_var (i := 0) rfl) (ev_var (i := 1) rfl)
        rwa [decide_eq_true (Int.lt_of_not_ge h)] at hq

spike_hb in
theorem nextRlF_eval_c₀ (rs : List Rl) (b : Option Int) :
    Eval c₀ 496 [embRls rs, embPrio b] (some (embPrio (nextRlF rs b))) := by
  induction rs with
  | nil =>
    exact clause_kht (σ := enumFrom 0 [embPrio b]) nextRlDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embPrio_sorted_c₀ b) .nil)) (.cons (.ctor ctor_404 .nil) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_431)
  | cons r rs ih =>
    obtain ⟨q, o, l, rq, rh⟩ := r
    rw [nextRlF]
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int q), .dv 2 (.bool o), emb l, emb rq, emb rh, embRls rs, embPrio b])
      nextRlDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (sort_int q) (.cons (sort_bool o) (.cons (emb_sorted_c₀ l) (.cons (emb_sorted_c₀ rq)
        (.cons (emb_sorted_c₀ rh) (.cons (embRls_sorted_c₀ rs) (.cons (embPrio_sorted_c₀ b) .nil))))))))
      (.cons (.ctor ctor_436 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.var rfl) (.cons (.var rfl) .nil))))))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_call (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (rprioF_eval_c₀ q o)
            notCtor_503 notHook_503 notParam_503) (.cons (ev_var rfl) .nil))
          (overF_eval_c₀ _ b) notCtor_498 notHook_498 notParam_498)
        (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih notCtor_496 notHook_496 notParam_496) .nil))
        (leastF_eval_c₀ _ _) notCtor_480 notHook_480 notParam_480)

spike_hb in
theorem nextClF_eval_c₀ (cs : List Cl) (b : Option Int) :
    Eval c₀ 495 [embCls cs, embPrio b] (some (embPrio (nextClF cs b))) := by
  induction cs with
  | nil =>
    exact clause_kht (σ := enumFrom 0 [embPrio b]) nextClDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embPrio_sorted_c₀ b) .nil)) (.cons (.ctor ctor_401 .nil) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_431)
  | cons c cs ih =>
    obtain ⟨q, o, ps, rq, rh⟩ := c
    rw [nextClF]
    exact clause_kht (σ := enumFrom 0 [.dv 3 (.int q), .dv 2 (.bool o), embTs ps, emb rq, emb rh, embCls cs, embPrio b])
      nextClDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (sort_int q) (.cons (sort_bool o) (.cons (embTs_sorted_c₀ ps) (.cons (emb_sorted_c₀ rq)
        (.cons (emb_sorted_c₀ rh) (.cons (embCls_sorted_c₀ cs) (.cons (embPrio_sorted_c₀ b) .nil))))))))
      (.cons (.ctor ctor_415 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.var rfl) (.cons (.var rfl) .nil))))))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_call (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (cprioF_eval_c₀ q o)
            notCtor_460 notHook_460 notParam_460) (.cons (ev_var rfl) .nil))
          (overF_eval_c₀ _ b) notCtor_498 notHook_498 notParam_498)
        (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih notCtor_495 notHook_495 notParam_495) .nil))
        (leastF_eval_c₀ _ _) notCtor_480 notHook_480 notParam_480)

end Prio

/-! ## Lists of terms -/

section Lists
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Walk

spike_hb in
theorem dropF_eval_c₀ (x : T) (ts : List T) : Eval c₀ 462 [emb x, embTs ts] (some (embTs (dropF x ts))) := by
  induction ts with
  | nil =>
    exact clause_kht (σ := enumFrom 0 [emb x, embTs []]) dropDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (ws_enum (.cons (emb_sorted_c₀ x) (.cons (embTs_sorted_c₀ []) .nil)))
      (.cons (.var rfl) (.cons (.as (.ctor ctor_406 .nil) rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | cons t ts ih =>
    have hσ := ws_enum (vars := [33, 33, 43]) (.cons (emb_sorted_c₀ x) (.cons (emb_sorted_c₀ t)
      (.cons (embTs_sorted_c₀ ts) .nil)))
    have hp : PatVals c₀ (enumFrom 0 [emb x, emb t, embTs ts]) [.var 0, .app 407 [.var 1, .var 2]]
        [emb x, embTs (t :: ts)] :=
      .cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)
    by_cases h : t = x
    · have e : dropF x (t :: ts) = dropF x ts := by rw [dropF, ite_pos h]
      rw [e]
      refine clause_kht dropDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
        ⟨rfl, rfl, rfl, rfl⟩ (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih
          notCtor_462 notHook_462 notParam_462)
      intro q hq
      cases hq
      have hq := keq_eval_kht (σ := enumFrom 0 [emb x, emb t, embTs ts]) (i := 1) (j := 0) rfl rfl
      rwa [decide_eq_true h] at hq
    · have e : dropF x (t :: ts) = t :: dropF x ts := by rw [dropF, ite_neg h]
      rw [e]
      refine clause_kht dropDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
        (ev_ctor (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih
          notCtor_462 notHook_462 notParam_462) .nil)) ctor_407)
      intro q hq
      cases hq
      have hq := kne_eval_kht (σ := enumFrom 0 [emb x, emb t, embTs ts]) (i := 1) (j := 0) rfl rfl
      rwa [decide_eq_false h] at hq

spike_hb in
theorem hasBotF_eval_c₀ (ts : List T) : Eval c₀ 471 [embTs ts] (some (.dv 2 (.bool (hasBotF ts)))) := by
  induction ts with
  | nil =>
    exact clause_kht (σ := enumFrom 0 []) hasBotDef_lookup (List.mem_cons_self ..) (ws_enum .nil)
      (.cons (.ctor ctor_406 .nil) .nil) (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  | cons t ts ih =>
    rw [hasBotF]
    exact clause_kht (σ := enumFrom 0 [emb t, embTs ts]) hasBotDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) .nil)))
      (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (or_eval_khw (keqT_eval_khw (u := .bot) (ev_var (i := 0) rfl) (ev_ctor .nil ctor_412))
        (ev_call (.cons (ev_var rfl) .nil) ih notCtor_471 notHook_471 notParam_471))

spike_hb in
theorem lenF_eval_c₀ (ts : List T) : Eval c₀ 481 [embTs ts] (some (.dv 3 (.int (lenF ts)))) := by
  induction ts with
  | nil =>
    exact clause_kht (σ := enumFrom 0 []) lenDef_lookup (List.mem_cons_self ..) (ws_enum .nil)
      (.cons (.ctor ctor_406 .nil) .nil) (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  | cons t ts ih =>
    rw [lenF_cons_khw]
    exact clause_kht (σ := enumFrom 0 [emb t, embTs ts]) lenDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) .nil)))
      (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (add_eval_khw .dv (ev_call (.cons (ev_var rfl) .nil) ih notCtor_481 notHook_481 notParam_481))

end Lists

/-! ## `ensure`, `b2i`, `lex` -/

section Small
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Walk

spike_hb in
/-- `bv(true)` as a pattern denotes no embedding but `bv(true)`'s. -/
theorem pat_bvTrue_khw {σ : Subst} {e : T} (h : PatVal c₀ σ (.app 413 [.dv 2 (.bool true)]) (emb e)) :
    e = .bv true := by
  obtain ⟨ws, he, hws⟩ := pv_ctor h
  rw [emb_ctor] at he
  obtain ⟨hh, ha⟩ := GroundTerm.ctor.inj he
  obtain ⟨b, rfl⟩ := headOf_eq_bv.mp hh
  cases ha
  rcases hws with _ | ⟨hb, -⟩
  cases hb
  rfl

spike_hb in
theorem ensureF_eval_c₀ (e t : T) : Eval c₀ 463 [emb e, emb t] (some (emb (ensureF e t))) := by
  by_cases h : e = .bv true
  · subst h
    exact clause_kht (σ := enumFrom 0 [emb t]) ensureDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ t) .nil)) (.cons (.ctor ctor_413 (.cons .dv .nil)) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  · have e' : ensureF e t = .bot := ite_neg h _ _
    rw [e']
    refine Eval.clause (σ := enumFrom 0 [emb e, emb t]) ensureDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ e) (.cons (emb_sorted_c₀ t) .nil)))
      (.cons (.var rfl) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) Holds.top ?_ rfl (ev_ctor .nil ctor_412) (fun _ h => by cases h) Holds.top
    intro cl' hm _ hp
    simp only [ensureDef, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact fails_kht fun σ hm => by
        rcases hm with _ | ⟨h0, -⟩
        exact h (pat_bvTrue_khw h0)
    · exact absurd hp (by decide)

spike_hb in
theorem b2iF_eval_c₀ (b : Bool) : Eval c₀ 450 [.dv 2 (.bool b)] (some (.dv 3 (.int (b2iF b)))) := by
  cases b with
  | false =>
    exact clause_kht (σ := enumFrom 0 []) b2iDef_lookup (List.mem_cons_self ..) (ws_enum .nil)
      (.cons .dv .nil) (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  | true =>
    exact clause_kht (σ := enumFrom 0 []) b2iDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum .nil) (.cons .dv .nil) (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv

spike_hb in
theorem lexF_eval_c₀ (x y : Int) : Eval c₀ 483 [.dv 3 (.int x), .dv 3 (.int y)] (some (.dv 3 (.int (lexF x y)))) := by
  have hσ := ws_enum (vars := [3, 3]) (.cons (sort_int x) (.cons (sort_int y) .nil))
  have hp : PatVals c₀ (enumFrom 0 [.dv 3 (.int x), .dv 3 (.int y)]) [.var 0, .var 1]
      [.dv 3 (.int x), .dv 3 (.int y)] := .cons (.var rfl) (.cons (.var rfl) .nil)
  by_cases h : x = 0
  · have e : lexF x y = y := ite_pos h _ _
    rw [e]
    refine clause_kht lexDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_var rfl)
    intro q hq
    cases hq
    have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int x), .dv 3 (.int y)]) (P := (· = ·))
      hook_intEq (ev_var (i := 0) rfl) (.dv (lit := .int 0)) notCtor_23 isHook_23
    rwa [decide_eq_true h] at hq
  · have e : lexF x y = x := ite_neg h _ _
    rw [e]
    refine clause_kht lexDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
      ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
    intro q hq
    cases hq
    have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int x), .dv 3 (.int y)]) (P := (· ≠ ·))
      hook_intNe (ev_var (i := 0) rfl) (.dv (lit := .int 0)) notCtor_24 isHook_24
    rwa [decide_eq_true h] at hq

end Small

/-! ## The helpers at `K₀ sig` -/

section Shape

theorem prioF.eval (p : Int) (o : Bool) :
    Eval (K₀ sig) 499 [.dv 3 (.int p), .dv 2 (.bool o)] (some (.dv 3 (.int (prioF p o)))) :=
  prioF_eval_c₀ p o
theorem prioF.eval_iff (p : Int) (o : Bool) {r : Option GroundTerm} :
    Eval (K₀ sig) 499 [.dv 3 (.int p), .dv 2 (.bool o)] r ↔ r = some (.dv 3 (.int (prioF p o))) :=
  evalF_iff (prioF.eval p o)

theorem rprioF.eval (p : Int) (o : Bool) :
    Eval (K₀ sig) 503 [.dv 3 (.int p), .dv 2 (.bool o)] (some (.dv 3 (.int (rprioF p o)))) :=
  rprioF_eval_c₀ p o
theorem rprioF.eval_iff (p : Int) (o : Bool) {r : Option GroundTerm} :
    Eval (K₀ sig) 503 [.dv 3 (.int p), .dv 2 (.bool o)] r ↔ r = some (.dv 3 (.int (rprioF p o))) :=
  evalF_iff (rprioF.eval p o)

theorem cprioF.eval (p : Int) (o : Bool) :
    Eval (K₀ sig) 460 [.dv 3 (.int p), .dv 2 (.bool o)] (some (.dv 3 (.int (cprioF p o)))) :=
  cprioF_eval_c₀ p o
theorem cprioF.eval_iff (p : Int) (o : Bool) {r : Option GroundTerm} :
    Eval (K₀ sig) 460 [.dv 3 (.int p), .dv 2 (.bool o)] r ↔ r = some (.dv 3 (.int (cprioF p o))) :=
  evalF_iff (cprioF.eval p o)

theorem overF.eval (p : Int) (b : Option Int) :
    Eval (K₀ sig) 498 [.dv 3 (.int p), embPrio b] (some (embPrio (overF p b))) :=
  overF_eval_c₀ p b
theorem overF.eval_iff (p : Int) (b : Option Int) {r : Option GroundTerm} :
    Eval (K₀ sig) 498 [.dv 3 (.int p), embPrio b] r ↔ r = some (embPrio (overF p b)) :=
  evalF_iff (overF.eval p b)

theorem leastF.eval (a b : Option Int) :
    Eval (K₀ sig) 480 [embPrio a, embPrio b] (some (embPrio (leastF a b))) :=
  leastF_eval_c₀ a b
theorem leastF.eval_iff (a b : Option Int) {r : Option GroundTerm} :
    Eval (K₀ sig) 480 [embPrio a, embPrio b] r ↔ r = some (embPrio (leastF a b)) :=
  evalF_iff (leastF.eval a b)

theorem nextRlF.eval (rs : List Rl) (b : Option Int) :
    Eval (K₀ sig) 496 [embRls rs, embPrio b] (some (embPrio (nextRlF rs b))) :=
  nextRlF_eval_c₀ rs b
theorem nextRlF.eval_iff (rs : List Rl) (b : Option Int) {r : Option GroundTerm} :
    Eval (K₀ sig) 496 [embRls rs, embPrio b] r ↔ r = some (embPrio (nextRlF rs b)) :=
  evalF_iff (nextRlF.eval rs b)

theorem nextClF.eval (cs : List Cl) (b : Option Int) :
    Eval (K₀ sig) 495 [embCls cs, embPrio b] (some (embPrio (nextClF cs b))) :=
  nextClF_eval_c₀ cs b
theorem nextClF.eval_iff (cs : List Cl) (b : Option Int) {r : Option GroundTerm} :
    Eval (K₀ sig) 495 [embCls cs, embPrio b] r ↔ r = some (embPrio (nextClF cs b)) :=
  evalF_iff (nextClF.eval cs b)

theorem dropF.eval (x : T) (ts : List T) :
    Eval (K₀ sig) 462 [emb x, embTs ts] (some (embTs (dropF x ts))) :=
  dropF_eval_c₀ x ts
theorem dropF.eval_iff (x : T) (ts : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 462 [emb x, embTs ts] r ↔ r = some (embTs (dropF x ts)) :=
  evalF_iff (dropF.eval x ts)

theorem ensureF.eval (e t : T) : Eval (K₀ sig) 463 [emb e, emb t] (some (emb (ensureF e t))) :=
  ensureF_eval_c₀ e t
theorem ensureF.eval_iff (e t : T) {r : Option GroundTerm} :
    Eval (K₀ sig) 463 [emb e, emb t] r ↔ r = some (emb (ensureF e t)) :=
  evalF_iff (ensureF.eval e t)

theorem hasBotF.eval (ts : List T) : Eval (K₀ sig) 471 [embTs ts] (some (.dv 2 (.bool (hasBotF ts)))) :=
  hasBotF_eval_c₀ ts
theorem hasBotF.eval_iff (ts : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 471 [embTs ts] r ↔ r = some (.dv 2 (.bool (hasBotF ts))) :=
  evalF_iff (hasBotF.eval ts)

theorem lenF.eval (ts : List T) : Eval (K₀ sig) 481 [embTs ts] (some (.dv 3 (.int (lenF ts)))) :=
  lenF_eval_c₀ ts
theorem lenF.eval_iff (ts : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 481 [embTs ts] r ↔ r = some (.dv 3 (.int (lenF ts))) :=
  evalF_iff (lenF.eval ts)

theorem b2iF.eval (b : Bool) : Eval (K₀ sig) 450 [.dv 2 (.bool b)] (some (.dv 3 (.int (b2iF b)))) :=
  b2iF_eval_c₀ b
theorem b2iF.eval_iff (b : Bool) {r : Option GroundTerm} :
    Eval (K₀ sig) 450 [.dv 2 (.bool b)] r ↔ r = some (.dv 3 (.int (b2iF b))) :=
  evalF_iff (b2iF.eval b)

theorem lexF.eval (x y : Int) :
    Eval (K₀ sig) 483 [.dv 3 (.int x), .dv 3 (.int y)] (some (.dv 3 (.int (lexF x y)))) :=
  lexF_eval_c₀ x y
theorem lexF.eval_iff (x y : Int) {r : Option GroundTerm} :
    Eval (K₀ sig) 483 [.dv 3 (.int x), .dv 3 (.int y)] r ↔ r = some (.dv 3 (.int (lexF x y))) :=
  evalF_iff (lexF.eval x y)

/-- kore.k's `look(X, B)` at `K₀ sig`: `lookF`'s entry. -/
theorem lookF.eval (x : Int) (B : Bind) :
    Eval (K₀ sig) 484 [.dv 3 (.int x), embB B] (some (embRes (lookF x B))) :=
  look_eval_kht x B
theorem lookF.eval_iff (x : Int) (B : Bind) {r : Option GroundTerm} :
    Eval (K₀ sig) 484 [.dv 3 (.int x), embB B] r ↔ r = some (embRes (lookF x B)) :=
  look_eval_iff_kht x B

end Shape

/-! ## Checks -/

#check @prioF.eval
#check @rprioF.eval
#check @cprioF.eval
#check @overF.eval
#check @leastF.eval
#check @nextRlF.eval
#check @nextClF.eval
#check @dropF.eval
#check @ensureF.eval
#check @hasBotF.eval
#check @lenF.eval
#check @b2iF.eval
#check @lexF.eval
#check @lookF.eval
#check @Gen.valOfF.eval
#check @Gen.lookupF.eval
#check @Gen.subsOfF.eval

open Lean in
#eval show CoreM Unit from do
  for n in [``helpWalk_names, ``prioF.eval, ``prioF.eval_iff, ``rprioF.eval, ``rprioF.eval_iff,
      ``cprioF.eval, ``cprioF.eval_iff, ``overF.eval, ``overF.eval_iff, ``leastF.eval, ``leastF.eval_iff,
      ``nextRlF.eval, ``nextRlF.eval_iff, ``nextClF.eval, ``nextClF.eval_iff, ``dropF.eval, ``dropF.eval_iff,
      ``ensureF.eval, ``ensureF.eval_iff, ``hasBotF.eval, ``hasBotF.eval_iff, ``lenF.eval, ``lenF.eval_iff,
      ``b2iF.eval, ``b2iF.eval_iff, ``lexF.eval, ``lexF.eval_iff, ``lookF.eval, ``lookF.eval_iff,
      ``Gen.valOfF.eval, ``Gen.valOfF.eval_iff, ``Gen.lookupF.eval, ``Gen.lookupF.eval_iff,
      ``Gen.subsOfF.eval, ``Gen.subsOfF.eval_iff] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
