/-
  kore.k's order functions over the mirrors, on kore.k's semantics read from its kompiled text, in
  the shape of User.HelpTerms: a Lean function `F` of the mirrors, `F.eval : Eval (K₀ sig) f [emb x,
  …] r` at the function's symbol `f` with no hypothesis on the arguments, and `F.eval_iff` from
  `evalF_iff`.

  `cmp`, `cmpTs`, `cmpI`, `tag` and `ckey` are KKEnc.lean's `cmpF`, `cmpTsF`, `cmpIF`, `tagF` and
  `ckeyF`, the functions `enc` sorts a collection's elements with: kore.k evaluates each to that
  function's value (`cmpF.eval`, …), and `ckey` has no value exactly where `ckeyF` is `none`. `cmpI`
  and `tag` are User.KkGenEmb's evaluations (`Gen.cmpIF.eval`, `Gen.tagF.eval`) read at KKEnc's
  functions. `insert` and `member` are `insertF` and `memberF`, total; `putE` (`putEF`) and `union`
  (`unionF`) have no value where a `ckey` they compute has none. `lex` and `b2i`, which `cmp`
  calls, and the hooks `<String` and `orBool` are evaluated as far as these proofs read them.

  On the encodings of values sorted in one semantics whose literals have a kore.k form
  (`EncSorted c`), `cmpF` is 0 exactly between equal terms and strictly ordered otherwise
  (`cmpF_eq_zero_iff`, `cmpF_trans` of KKEncCanon.lean), so `member` is membership
  (`memberF_iff_ord`, `memberF_enc`) and `insert` is insertion into a list strictly increasing by
  `cmpF`, which it keeps strictly increasing (`insertF_mem_ord`, `insertF_sorted_ord`,
  `insertF_of_mem_ord`). A map or set an encoding holds is strictly increasing by what kore.k's
  `ckey` computes (`ckey_canon_eval`, from `enc_canonical`).

  The clauses are the semantics' own, as literals tied to `lookupFn` by the kernel.
-/
import User.HelpTerms
import User.KkGenEmb

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The functions over the mirrors -/

/-- kore.k's `insert(T, Ts)`: `T` before the first term it is below by `cmpF`, left out where a
term compares 0 with it. -/
def insertF (t : T) : List T → List T
  | [] => [t]
  | u :: us => if cmpF t u < 0 then t :: u :: us else if cmpF t u = 0 then u :: us else u :: insertF t us

/-- kore.k's `member(T, Ts)`: whether a term of the list compares 0 with `T`. -/
def memberF (t : T) : List T → Bool
  | [] => false
  | u :: us => decide (cmpF t u = 0) || memberF t us

/-- kore.k's `putE(E, Ts)`: `E` before the first element whose key it is below by `ckeyF`, in
place of the element of its key; no value where `ckeyF` has none. -/
def putEF (e : T) : List T → Option (List T)
  | [] => some [e]
  | f :: fs => (ckeyF e f).bind fun k =>
      if k < 0 then some (e :: f :: fs) else if k = 0 then some (e :: fs) else (putEF e fs).map (f :: ·)

/-- kore.k's `union(Es, Fs)`: each element of `Fs` put into `Es` in turn. -/
def unionF : List T → List T → Option (List T)
  | es, [] => some es
  | es, f :: fs => (putEF f es).bind fun es' => unionF es' fs

/-! ## The symbols -/

/-- Each symbol number the evaluations below are at has the KORE name of the function. -/
theorem helpOrder_names :
    RefKk.defn.sem.symName 450 = "Lblb2i'LParUndsRParUnds'KORE'Unds'Int'Unds'Bool" ∧
    RefKk.defn.sem.symName 455 = "Lblckey'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 456 = "Lblcmp'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 457 = "LblcmpI'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Int'Unds'Int" ∧
    RefKk.defn.sem.symName 458 = "LblcmpTs'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Ts'Unds'Ts" ∧
    RefKk.defn.sem.symName 475 = "Lblinsert'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 483 = "Lbllex'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Int'Unds'Int" ∧
    RefKk.defn.sem.symName 490 = "Lblmember'LParUndsCommUndsRParUnds'KORE'Unds'Bool'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 500 = "LblputE'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 511 = "Lbltag'LParUndsRParUnds'KORE'Unds'Int'Unds'Term" ∧
    RefKk.defn.sem.symName 515 = "Lblunion'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Ts'Unds'Ts" := by
  decide +kernel

/-! ## The clauses, as the semantics holds them -/

namespace Order
open _root_.KK Terms

/-- `b2i` (450): `b2i-false`, `b2i-true`. -/
def b2iDef : Fn :=
  { label := 450, args := [2], result := 3, total := false, clauses := [
    plainCl [] [.dv 2 (.bool false)] (.dv 3 (.int 0)),
    plainCl [] [.dv 2 (.bool true)] (.dv 3 (.int 1))] }

/-- `ckey` (455): `ckey-el`, `ckey-kv`. -/
def ckeyDef : Fn :=
  { label := 455, args := [33, 33], result := 3, total := false, clauses := [
    plainCl [33, 33] [.app 419 [.var 0], .app 419 [.var 1]] (.app 456 [.var 0, .var 1]),
    plainCl [33, 33, 33, 33] [.app 426 [.var 0, .var 1], .app 426 [.var 2, .var 3]] (.app 456 [.var 0, .var 2])] }

/-- `cmp` (456): `cmp-app`, `cmp-bool`, `cmp-col`, `cmp-el`, `cmp-inj`, `cmp-int`, `cmp-kv`, `cmp-tok`,
`cmp-tag` (priority 200, `[owise]`). -/
def cmpDef : Fn :=
  { label := 456, args := [33, 33], result := 3, total := false, clauses := [
    plainCl [43, 3, 43, 3] [.app 408 [.var 1, .var 2], .app 408 [.var 3, .var 0]]
      (.app 483 [.app 457 [.var 1, .var 3], .app 458 [.var 2, .var 0]]),
    plainCl [2, 2] [.app 413 [.var 0], .app 413 [.var 1]] (.app 457 [.app 450 [.var 0], .app 450 [.var 1]]),
    plainCl [34, 43, 3, 43, 34, 3] [.app 416 [.var 0, .var 2, .var 3], .app 416 [.var 4, .var 5, .var 1]]
      (.app 483 [.app 457 [.var 2, .var 5], .app 458 [.var 3, .var 1]]),
    plainCl [33, 33] [.app 419 [.var 0], .app 419 [.var 1]] (.app 456 [.var 0, .var 1]),
    plainCl [3, 3, 33, 3, 3, 33] [.app 424 [.var 3, .var 4, .var 5], .app 424 [.var 0, .var 1, .var 2]]
      (.app 483 [.app 457 [.var 3, .var 0], .app 483 [.app 457 [.var 4, .var 1], .app 456 [.var 5, .var 2]]]),
    plainCl [3, 3] [.app 425 [.var 1], .app 425 [.var 0]] (.app 457 [.var 1, .var 0]),
    plainCl [33, 33, 33, 33] [.app 426 [.var 0, .var 1], .app 426 [.var 2, .var 3]]
      (.app 483 [.app 456 [.var 0, .var 2], .app 456 [.var 1, .var 3]]),
    plainCl [3, 3, 10, 10] [.app 443 [.var 0, .var 3], .app 443 [.var 1, .var 2]]
      (.app 483 [.app 457 [.var 0, .var 1],
        .app 457 [.app 450 [.app 287 [.var 2, .var 3]], .app 450 [.app 287 [.var 3, .var 2]]]]),
    plainCl [33, 33] [.var 0, .var 1] (.app 457 [.app 511 [.var 0], .app 511 [.var 1]]) (prio := 200)] }

/-- `cmpTs` (458): `cmps-nil`, `cmps-short`, `cmps-cons`, `cmps-long`. -/
def cmpTsDef : Fn :=
  { label := 458, args := [43, 43], result := 3, total := false, clauses := [
    plainCl [] [.app 406 [], .app 406 []] (.dv 3 (.int 0)),
    plainCl [33, 43] [.app 406 [], .app 407 [.var 0, .var 1]] (.dv 3 (.int (-1))),
    plainCl [33, 43, 33, 43] [.app 407 [.var 0, .var 1], .app 407 [.var 2, .var 3]]
      (.app 483 [.app 456 [.var 0, .var 2], .app 458 [.var 1, .var 3]]),
    plainCl [33, 43] [.app 407 [.var 0, .var 1], .app 406 []] (.dv 3 (.int 1))] }

/-- `cmp(T, U) <op> 0`, the `requires` of `insert`'s equations. -/
abbrev cmpReq (op : Sym) : Term := .app op [.app 456 [.var 0, .var 1], .dv 3 (.int 0)]

/-- `ckey(E, F) <op> 0`, the `requires` of `putE`'s equations. -/
abbrev ckeyReq (op : Sym) : Term := .app op [.app 455 [.var 0, .var 1], .dv 3 (.int 0)]

/-- `insert` (475): `ins-nil`, `ins-dup`, `ins-before`, `ins-after`. -/
def insertDef : Fn :=
  { label := 475, args := [33, 43], result := 43, total := false, clauses := [
    plainCl [33, 43] [.var 0, .as (.app 406 []) 1] (.app 407 [.var 0, .var 1]),
    plainCl [33, 33, 43, 43] [.var 0, .as (.app 407 [.var 1, .var 2]) 3] (.var 3) (req := some (cmpReq 23)),
    plainCl [33, 33, 43, 43] [.var 0, .as (.app 407 [.var 1, .var 2]) 3] (.app 407 [.var 0, .var 3])
      (req := some (cmpReq 19)),
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 407 [.var 1, .app 475 [.var 0, .var 2]])
      (req := some (cmpReq 21))] }

/-- `lex` (483): `lex-tie`, `lex-first`. -/
def lexDef : Fn :=
  { label := 483, args := [3, 3], result := 3, total := false, clauses := [
    plainCl [3, 3] [.var 0, .var 1] (.var 1) (req := some (.app 23 [.var 0, .dv 3 (.int 0)])),
    plainCl [3, 3] [.var 0, .var 1] (.var 0) (req := some (.app 24 [.var 0, .dv 3 (.int 0)]))] }

/-- `member` (490): `mem-cons`, `mem-nil`. -/
def memberDef : Fn :=
  { label := 490, args := [33, 43], result := 2, total := false, clauses := [
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 6 [cmpReq 23, .app 490 [.var 0, .var 2]]),
    plainCl [33] [.var 0, .app 406 []] (.dv 2 (.bool false))] }

/-- `putE` (500): `pute-nil`, `pute-before`, `pute-replace`, `pute-after`. -/
def putEDef : Fn :=
  { label := 500, args := [33, 43], result := 43, total := false, clauses := [
    plainCl [33, 43] [.var 0, .as (.app 406 []) 1] (.app 407 [.var 0, .var 1]),
    plainCl [33, 33, 43, 43] [.var 0, .as (.app 407 [.var 1, .var 2]) 3] (.app 407 [.var 0, .var 3])
      (req := some (ckeyReq 19)),
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 407 [.var 0, .var 2]) (req := some (ckeyReq 23)),
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 407 [.var 1, .app 500 [.var 0, .var 2]])
      (req := some (ckeyReq 21))] }

/-- `union` (515): `union-nil`, `union-cons`. -/
def unionDef : Fn :=
  { label := 515, args := [43, 43], result := 43, total := false, clauses := [
    plainCl [43] [.var 0, .app 406 []] (.var 0),
    plainCl [43, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 515 [.app 500 [.var 1, .var 0], .var 2])] }

theorem b2iDef_lookup : c₀.lookupFn 450 = some b2iDef := by kernel_rfl
theorem ckeyDef_lookup : c₀.lookupFn 455 = some ckeyDef := by kernel_rfl
theorem cmpDef_lookup : c₀.lookupFn 456 = some cmpDef := by kernel_rfl
theorem cmpTsDef_lookup : c₀.lookupFn 458 = some cmpTsDef := by kernel_rfl
theorem insertDef_lookup : c₀.lookupFn 475 = some insertDef := by kernel_rfl
theorem lexDef_lookup : c₀.lookupFn 483 = some lexDef := by kernel_rfl
theorem memberDef_lookup : c₀.lookupFn 490 = some memberDef := by kernel_rfl
theorem putEDef_lookup : c₀.lookupFn 500 = some putEDef := by kernel_rfl
theorem unionDef_lookup : c₀.lookupFn 515 = some unionDef := by kernel_rfl

end Order

/-! ## Shared steps -/

section Kit
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Order

/-- An Int as kore.k's value. -/
abbrev iv3 (x : Int) : GroundTerm := .dv 3 (.int x)

spike_hb in
/-- A constructor pattern that denotes `emb t` names `t`'s head. -/
theorem pat_head_kho {σ : Subst} {f : Sym} {qs : List Term} {t : T} (h : PatVal c₀ σ (.app f qs) (emb t))
    (hc : c₀.isCtor f = true) (hh : patternHooks.contains f = false) : headOf t = f := by
  obtain ⟨ws, he, -⟩ := pv_ctor h hc hh
  exact (GroundTerm.ctor.inj ((emb_ctor t).symm.trans he)).1

spike_hb in
/-- `cmpI` evaluates to KKEnc's `cmpIF`: User.KkGenEmb's evaluation, its function read at Ints. -/
theorem genCmpIF_kho (x y : Int) : Gen.cmpIF x y = some (cmpIF x y) := by
  unfold Gen.cmpIF cmpIF
  by_cases h1 : x < y
  · rw [ite_pos h1, ite_pos h1]
  · by_cases h2 : x = y
    · rw [ite_neg h1, ite_pos h2, ite_neg h1, ite_pos h2]
    · rw [ite_neg h1, ite_neg h2, ite_pos (show x > y by omega), ite_neg h1, ite_neg h2]

spike_hb in
/-- `tag` evaluates to KKEnc's `tagF`. -/
theorem genTagF_kho (t : T) : Gen.tagF t = some (tagF t) := by
  cases t <;> rfl

theorem cmpI_eval_kho (x y : Int) : Eval c₀ 457 [iv3 x, iv3 y] (some (iv3 (cmpIF x y))) := by
  have h := Gen.cmpIF.eval x y
  rw [genCmpIF_kho] at h
  exact h

theorem tag_eval_kho (t : T) : Eval c₀ 511 [emb t] (some (iv3 (tagF t))) := by
  have h := Gen.tagF.eval t
  rw [genTagF_kho] at h
  exact h

spike_hb in
theorem b2i_eval_kho (b : Bool) : Eval c₀ 450 [.dv 2 (.bool b)] (some (iv3 (b2iF b))) := by
  cases b
  · exact clause_kht (σ := enumFrom 0 []) b2iDef_lookup (List.mem_cons_self ..) (ws_enum .nil)
      (.cons .dv .nil) (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  · exact clause_kht (σ := enumFrom 0 []) b2iDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum .nil) (.cons .dv .nil) (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv

spike_hb in
theorem lex_eval_kho (x y : Int) : Eval c₀ 483 [iv3 x, iv3 y] (some (iv3 (lexF x y))) := by
  have hσ := ws_enum (vars := [3, 3]) (.cons (sort_int x) (.cons (sort_int y) .nil))
  have hp : PatVals c₀ (enumFrom 0 [iv3 x, iv3 y]) [.var 0, .var 1] [iv3 x, iv3 y] :=
    .cons (.var rfl) (.cons (.var rfl) .nil)
  by_cases h : x = 0
  · rw [lexF, ite_pos h]
    refine clause_kht lexDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
    intro q hq
    cases hq
    have hq := ev_int2 (σ := enumFrom 0 [iv3 x, iv3 y]) (P := (· = ·)) hook_intEq (ev_var (i := 0) rfl)
      (EvalTerm.dv (lit := .int 0)) notCtor_23 isHook_23
    rwa [decide_eq_true h] at hq
  · rw [lexF, ite_neg h]
    refine clause_kht lexDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
      ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
    intro q hq
    cases hq
    have hq := ev_int2 (σ := enumFrom 0 [iv3 x, iv3 y]) (P := (· ≠ ·)) hook_intNe (ev_var (i := 0) rfl)
      (EvalTerm.dv (lit := .int 0)) notCtor_24 isHook_24
    rwa [decide_eq_true h] at hq

/-- `lex(A, B)` at two Int values. -/
theorem ev_lex_kho {σ : Subst} {a b : Term} {x y : Int} (ha : EvalTerm c₀ σ a (some (iv3 x)))
    (hb : EvalTerm c₀ σ b (some (iv3 y))) : EvalTerm c₀ σ (.app 483 [a, b]) (some (iv3 (lexF x y))) :=
  ev_call (.cons ha (.cons hb .nil)) (lex_eval_kho x y) notCtor_483 notHook_483 notParam_483

/-- `cmpI(A, B)` at two Int values. -/
theorem ev_cmpI_kho {σ : Subst} {a b : Term} {x y : Int} (ha : EvalTerm c₀ σ a (some (iv3 x)))
    (hb : EvalTerm c₀ σ b (some (iv3 y))) : EvalTerm c₀ σ (.app 457 [a, b]) (some (iv3 (cmpIF x y))) :=
  ev_call (.cons ha (.cons hb .nil)) (cmpI_eval_kho x y) notCtor_457 notHook_457 notParam_457

/-- `b2i(A)` at a Bool value. -/
theorem ev_b2i_kho {σ : Subst} {a : Term} {b : Bool} (ha : EvalTerm c₀ σ a (some (.dv 2 (.bool b)))) :
    EvalTerm c₀ σ (.app 450 [a]) (some (iv3 (b2iF b))) :=
  ev_call (.cons ha .nil) (b2i_eval_kho b) notCtor_450 notHook_450 notParam_450

theorem hook_stringLt_kho (x y : String) :
    hook 287 [.dv 10 (.tok x), .dv 10 (.tok y)] = some (some (bool (KStr.lexLt x.toList y.toList))) := rfl

/-- `A <String B` at two String values. -/
theorem ev_strLt_kho {σ : Subst} {a b : Term} {x y : String} (ha : EvalTerm c₀ σ a (some (.dv 10 (.tok x))))
    (hb : EvalTerm c₀ σ b (some (.dv 10 (.tok y)))) :
    EvalTerm c₀ σ (.app 287 [a, b]) (some (.dv 2 (.bool (KStr.lexLt x.toList y.toList)))) := by
  refine .hook (by decide +kernel) (by decide +kernel) (EvArgs.terms (.cons ha (.cons hb .nil)))
    (fun vs hvs => ?_) (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value (hook_stringLt_kho x y)
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

theorem hook_boolOr_kho (a b : Bool) : hook 6 [bool a, bool b] = some (some (bool (a || b))) := rfl

/-- `A orBool B` at two Bool values. -/
theorem ev_or_kho {σ : Subst} {a b : Term} {x y : Bool} (ha : EvalTerm c₀ σ a (some (bool x)))
    (hb : EvalTerm c₀ σ b (some (bool y))) : EvalTerm c₀ σ (.app 6 [a, b]) (some (bool (x || y))) := by
  refine .hook (by decide +kernel) (by decide +kernel) (EvArgs.terms (.cons ha (.cons hb .nil)))
    (fun vs hvs => ?_) (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value (hook_boolOr_kho x y)
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

end Kit

/-! ## `cmp`, `cmpTs` -/

section Cmp
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Order

/-- What `cmp` evaluates to at two mirror terms. -/
abbrev CmpEv_kho (t u : T) (r : Int) : Prop := Eval c₀ 456 [emb t, emb u] (some (iv3 r))

/-- What `cmpTs` evaluates to at two lists of mirror terms. -/
abbrev CmpTsEv_kho (ts us : List T) (r : Int) : Prop := Eval c₀ 458 [embTs ts, embTs us] (some (iv3 r))

/-- `cmp(A, B)` at two terms. -/
theorem ev_cmp_kho {σ : Subst} {a b : Term} {t u : T} {r : Int} (ha : EvalTerm c₀ σ a (some (emb t)))
    (hb : EvalTerm c₀ σ b (some (emb u))) (h : CmpEv_kho t u r) :
    EvalTerm c₀ σ (.app 456 [a, b]) (some (iv3 r)) :=
  ev_call (.cons ha (.cons hb .nil)) h notCtor_456 notHook_456 notParam_456

/-- `cmpTs(A, B)` at two lists. -/
theorem ev_cmpTs_kho {σ : Subst} {a b : Term} {ts us : List T} {r : Int} (ha : EvalTerm c₀ σ a (some (embTs ts)))
    (hb : EvalTerm c₀ σ b (some (embTs us))) (h : CmpTsEv_kho ts us r) :
    EvalTerm c₀ σ (.app 458 [a, b]) (some (iv3 r)) :=
  ev_call (.cons ha (.cons hb .nil)) h notCtor_458 notHook_458 notParam_458

spike_hb in
theorem cmp_iv_kho (x y : Int) : CmpEv_kho (.iv x) (.iv y) (cmpIF x y) :=
  clause_kht (σ := enumFrom 0 [iv3 y, iv3 x]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
    (ws_enum (.cons (sort_int y) (.cons (sort_int x) .nil)))
    (.cons (.ctor ctor_425 (.cons (.var rfl) .nil)) (.cons (.ctor ctor_425 (.cons (.var rfl) .nil)) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_cmpI_kho (ev_var rfl) (ev_var rfl))

spike_hb in
theorem cmp_bv_kho (x y : Bool) : CmpEv_kho (.bv x) (.bv y) (cmpIF (b2iF x) (b2iF y)) :=
  clause_kht (σ := enumFrom 0 [.dv 2 (.bool x), .dv 2 (.bool y)]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (ws_enum (.cons (sort_bool x) (.cons (sort_bool y) .nil)))
    (.cons (.ctor ctor_413 (.cons (.var rfl) .nil)) (.cons (.ctor ctor_413 (.cons (.var rfl) .nil)) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_cmpI_kho (ev_b2i_kho (ev_var rfl)) (ev_b2i_kho (ev_var rfl)))

spike_hb in
theorem cmp_tk_kho (s : Int) (x : String) (t : Int) (y : String) :
    CmpEv_kho (.tk s x) (.tk t y)
      (lexF (cmpIF s t) (cmpIF (b2iF (KStr.lexLt y.toList x.toList)) (b2iF (KStr.lexLt x.toList y.toList)))) :=
  clause_kht (σ := enumFrom 0 [iv3 s, iv3 t, .dv 10 (.tok y), .dv 10 (.tok x)]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
    (ws_enum (.cons (sort_int s) (.cons (sort_int t) (.cons (sort_string_kemb y) (.cons (sort_string_kemb x) .nil)))))
    (.cons (.ctor ctor_443 (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (.cons (.ctor ctor_443 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_lex_kho (ev_cmpI_kho (ev_var rfl) (ev_var rfl))
      (ev_cmpI_kho (ev_b2i_kho (ev_strLt_kho (ev_var rfl) (ev_var rfl)))
        (ev_b2i_kho (ev_strLt_kho (ev_var rfl) (ev_var rfl)))))

spike_hb in
theorem cmp_ap_kho (f : Int) (as : List T) (g : Int) (bs : List T) {r : Int} (ih : CmpTsEv_kho as bs r) :
    CmpEv_kho (.ap f as) (.ap g bs) (lexF (cmpIF f g) r) :=
  clause_kht (σ := enumFrom 0 [embTs bs, iv3 f, embTs as, iv3 g]) cmpDef_lookup (List.mem_cons_self ..)
    (ws_enum (.cons (embTs_sorted_c₀ bs) (.cons (sort_int f) (.cons (embTs_sorted_c₀ as) (.cons (sort_int g) .nil)))))
    (.cons (.ctor ctor_408 (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (.cons (.ctor ctor_408 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_lex_kho (ev_cmpI_kho (ev_var rfl) (ev_var rfl)) (ev_cmpTs_kho (ev_var rfl) (ev_var rfl) ih))

spike_hb in
theorem cmp_ij_kho (a b : Int) (t : T) (c e : Int) (u : T) {r : Int} (ih : CmpEv_kho t u r) :
    CmpEv_kho (.ij a b t) (.ij c e u) (lexF (cmpIF a c) (lexF (cmpIF b e) r)) :=
  clause_kht (σ := enumFrom 0 [iv3 c, iv3 e, emb u, iv3 a, iv3 b, emb t]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))))
    (ws_enum (.cons (sort_int c) (.cons (sort_int e) (.cons (emb_sorted_c₀ u) (.cons (sort_int a)
      (.cons (sort_int b) (.cons (emb_sorted_c₀ t) .nil)))))))
    (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_lex_kho (ev_cmpI_kho (ev_var rfl) (ev_var rfl))
      (ev_lex_kho (ev_cmpI_kho (ev_var rfl) (ev_var rfl)) (ev_cmp_kho (ev_var rfl) (ev_var rfl) ih)))

spike_hb in
theorem cmp_co_kho (k : Kind) (c : Int) (es : List T) (k' : Kind) (d : Int) (fs : List T) {r : Int}
    (ih : CmpTsEv_kho es fs r) : CmpEv_kho (.co k c es) (.co k' d fs) (lexF (cmpIF c d) r) :=
  clause_kht (σ := enumFrom 0 [embK k, embTs fs, iv3 c, embTs es, embK k', iv3 d]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (ws_enum (.cons (embK_sorted_c₀ k) (.cons (embTs_sorted_c₀ fs) (.cons (sort_int c) (.cons (embTs_sorted_c₀ es)
      (.cons (embK_sorted_c₀ k') (.cons (sort_int d) .nil)))))))
    (.cons (.ctor ctor_416 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (.cons (.ctor ctor_416 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_lex_kho (ev_cmpI_kho (ev_var rfl) (ev_var rfl)) (ev_cmpTs_kho (ev_var rfl) (ev_var rfl) ih))

spike_hb in
theorem cmp_kv_kho (a v b w : T) {r q : Int} (iha : CmpEv_kho a b r) (ihv : CmpEv_kho v w q) :
    CmpEv_kho (.kv a v) (.kv b w) (lexF r q) :=
  clause_kht (σ := enumFrom 0 [emb a, emb v, emb b, emb w]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
    (ws_enum (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) (.cons (emb_sorted_c₀ b) (.cons (emb_sorted_c₀ w) .nil)))))
    (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_lex_kho (ev_cmp_kho (ev_var rfl) (ev_var rfl) iha) (ev_cmp_kho (ev_var rfl) (ev_var rfl) ihv))

spike_hb in
theorem cmp_el_kho (x y : T) {r : Int} (ih : CmpEv_kho x y r) : CmpEv_kho (.el x) (.el y) r :=
  clause_kht (σ := enumFrom 0 [emb x, emb y]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (ws_enum (.cons (emb_sorted_c₀ x) (.cons (emb_sorted_c₀ y) .nil)))
    (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_cmp_kho (ev_var rfl) (ev_var rfl) ih)

spike_hb in
/-- Two terms no equation of `cmp` of priority 50 takes compare by `tag` (`cmp-tag`): each of those
equations names one head for both arguments, and the two terms do not both have it. -/
theorem cmp_tag_kho (t u : T)
    (h1 : ∀ (x y : Int), t = .iv x → u = .iv y → False)
    (h2 : ∀ (x y : Bool), t = .bv x → u = .bv y → False)
    (h3 : ∀ (s : Int) (x : String) (t' : Int) (y : String), t = .tk s x → u = .tk t' y → False)
    (h4 : ∀ (f : Int) (as : List T) (g : Int) (bs : List T), t = .ap f as → u = .ap g bs → False)
    (h5 : ∀ (a b : Int) (t' : T) (c e : Int) (u' : T), t = .ij a b t' → u = .ij c e u' → False)
    (h6 : ∀ (k : Kind) (c : Int) (es : List T) (k' : Kind) (d : Int) (fs : List T),
      t = .co k c es → u = .co k' d fs → False)
    (h7 : ∀ (a v b w : T), t = .kv a v → u = .kv b w → False)
    (h8 : ∀ (x y : T), t = .el x → u = .el y → False) :
    CmpEv_kho t u (cmpIF (tagF t) (tagF u)) := by
  refine Eval.clause (σ := enumFrom 0 [emb t, emb u]) cmpDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))))))))
    (ws_enum (.cons (emb_sorted_c₀ t) (.cons (emb_sorted_c₀ u) .nil)))
    (.cons (.var rfl) (.cons (.var rfl) .nil))
    (fun _ h => by cases h) Holds.top ?_ rfl
    (ev_cmpI_kho (ev_call (.cons (ev_var rfl) .nil) (tag_eval_kho t) notCtor_511 notHook_511 notParam_511)
      (ev_call (.cons (ev_var rfl) .nil) (tag_eval_kho u) notCtor_511 notHook_511 notParam_511))
    (fun _ h => by cases h) Holds.top
  intro cl' hm _ hp
  simp only [cmpDef, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hp (by decide)
    | refine fails_kht fun σ hm => ?_
      rcases hm with _ | ⟨h0, _ | ⟨h1', -⟩⟩
  · obtain ⟨f, as, rfl⟩ := headOf_eq_ap.mp (pat_head_kho h0 ctor_408 noHook_408)
    obtain ⟨g, bs, rfl⟩ := headOf_eq_ap.mp (pat_head_kho h1' ctor_408 noHook_408)
    exact h4 f as g bs rfl rfl
  · obtain ⟨x, rfl⟩ := headOf_eq_bv.mp (pat_head_kho h0 ctor_413 noHook_413)
    obtain ⟨y, rfl⟩ := headOf_eq_bv.mp (pat_head_kho h1' ctor_413 noHook_413)
    exact h2 x y rfl rfl
  · obtain ⟨k, c, es, rfl⟩ := headOf_eq_co.mp (pat_head_kho h0 ctor_416 noHook_416)
    obtain ⟨k', d, fs, rfl⟩ := headOf_eq_co.mp (pat_head_kho h1' ctor_416 noHook_416)
    exact h6 k c es k' d fs rfl rfl
  · obtain ⟨x, rfl⟩ := headOf_eq_el.mp (pat_head_kho h0 ctor_419 noHook_419)
    obtain ⟨y, rfl⟩ := headOf_eq_el.mp (pat_head_kho h1' ctor_419 noHook_419)
    exact h8 x y rfl rfl
  · obtain ⟨a, b, t', rfl⟩ := headOf_eq_ij.mp (pat_head_kho h0 ctor_424 noHook_424)
    obtain ⟨c, e, u', rfl⟩ := headOf_eq_ij.mp (pat_head_kho h1' ctor_424 noHook_424)
    exact h5 a b t' c e u' rfl rfl
  · obtain ⟨x, rfl⟩ := headOf_eq_iv.mp (pat_head_kho h0 ctor_425 noHook_425)
    obtain ⟨y, rfl⟩ := headOf_eq_iv.mp (pat_head_kho h1' ctor_425 noHook_425)
    exact h1 x y rfl rfl
  · obtain ⟨a, v, rfl⟩ := headOf_eq_kv.mp (pat_head_kho h0 ctor_426 noHook_426)
    obtain ⟨b, w, rfl⟩ := headOf_eq_kv.mp (pat_head_kho h1' ctor_426 noHook_426)
    exact h7 a v b w rfl rfl
  · obtain ⟨s, x, rfl⟩ := headOf_eq_tk.mp (pat_head_kho h0 ctor_443 noHook_443)
    obtain ⟨t', y, rfl⟩ := headOf_eq_tk.mp (pat_head_kho h1' ctor_443 noHook_443)
    exact h3 s x t' y rfl rfl

spike_hb in
theorem cmpTs_nil_nil_kho : CmpTsEv_kho [] [] 0 :=
  clause_kht (σ := enumFrom 0 []) cmpTsDef_lookup (List.mem_cons_self ..) (ws_enum .nil)
    (.cons (.ctor ctor_406 .nil) (.cons (.ctor ctor_406 .nil) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv

spike_hb in
theorem cmpTs_nil_cons_kho (u : T) (us : List T) : CmpTsEv_kho [] (u :: us) (-1) :=
  clause_kht (σ := enumFrom 0 [emb u, embTs us]) cmpTsDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (ws_enum (.cons (emb_sorted_c₀ u) (.cons (embTs_sorted_c₀ us) .nil)))
    (.cons (.ctor ctor_406 .nil) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv

spike_hb in
theorem cmpTs_cons_nil_kho (t : T) (ts : List T) : CmpTsEv_kho (t :: ts) [] 1 :=
  clause_kht (σ := enumFrom 0 [emb t, embTs ts]) cmpTsDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) .nil)))
    (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.ctor ctor_406 .nil) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv

spike_hb in
theorem cmpTs_cons_cons_kho (t : T) (ts : List T) (u : T) (us : List T) {r q : Int} (ih : CmpEv_kho t u r)
    (ihs : CmpTsEv_kho ts us q) : CmpTsEv_kho (t :: ts) (u :: us) (lexF r q) :=
  clause_kht (σ := enumFrom 0 [emb t, embTs ts, emb u, embTs us]) cmpTsDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ ts) (.cons (emb_sorted_c₀ u) (.cons (embTs_sorted_c₀ us) .nil)))))
    (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_lex_kho (ev_cmp_kho (ev_var rfl) (ev_var rfl) ih) (ev_cmpTs_kho (ev_var rfl) (ev_var rfl) ihs))

spike_hb in
theorem cmp_eval_kho (t u : T) : CmpEv_kho t u (cmpF t u) :=
  cmpF.induct_unfolding (motive_1 := CmpEv_kho) (motive_2 := CmpTsEv_kho) cmp_iv_kho cmp_bv_kho cmp_tk_kho
    (fun f as g bs ih => cmp_ap_kho f as g bs ih) (fun a b t c e u ih => cmp_ij_kho a b t c e u ih)
    (fun k c es k' d fs ih => cmp_co_kho k c es k' d fs ih) (fun a v b w iha ihv => cmp_kv_kho a v b w iha ihv)
    (fun x y ih => cmp_el_kho x y ih) cmp_tag_kho cmpTs_nil_nil_kho cmpTs_nil_cons_kho cmpTs_cons_nil_kho
    (fun t ts u us ih ihs => cmpTs_cons_cons_kho t ts u us ih ihs) t u

spike_hb in
theorem cmpTs_eval_kho (ts us : List T) : CmpTsEv_kho ts us (cmpTsF ts us) :=
  cmpTsF.induct_unfolding (motive_1 := CmpEv_kho) (motive_2 := CmpTsEv_kho) cmp_iv_kho cmp_bv_kho cmp_tk_kho
    (fun f as g bs ih => cmp_ap_kho f as g bs ih) (fun a b t c e u ih => cmp_ij_kho a b t c e u ih)
    (fun k c es k' d fs ih => cmp_co_kho k c es k' d fs ih) (fun a v b w iha ihv => cmp_kv_kho a v b w iha ihv)
    (fun x y ih => cmp_el_kho x y ih) cmp_tag_kho cmpTs_nil_nil_kho cmpTs_nil_cons_kho cmpTs_cons_nil_kho
    (fun t ts u us ih ihs => cmpTs_cons_cons_kho t ts u us ih ihs) ts us

end Cmp

/-! ## `ckey` -/

section Ckey
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Order

spike_hb in
theorem ckey_eval_kho (e f : T) : Eval c₀ 455 [emb e, emb f] ((ckeyF e f).map iv3) := by
  refine ckeyF.fun_cases_unfolding (motive := fun e f r => Eval c₀ 455 [emb e, emb f] (r.map iv3)) ?_ ?_ ?_ e f
  · intro a v b w
    exact clause_kht (σ := enumFrom 0 [emb a, emb v, emb b, emb w]) ckeyDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) (.cons (emb_sorted_c₀ b) (.cons (emb_sorted_c₀ w) .nil)))))
      (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_cmp_kho (ev_var rfl) (ev_var rfl) (cmp_eval_kho a b))
  · intro x y
    exact clause_kht (σ := enumFrom 0 [emb x, emb y]) ckeyDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ x) (.cons (emb_sorted_c₀ y) .nil)))
      (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_cmp_kho (ev_var rfl) (ev_var rfl) (cmp_eval_kho x y))
  · intro e f hkv hel
    refine Eval.rest ckeyDef_lookup fun cl hm => ?_
    simp only [ckeyDef, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> refine fails_kht fun σ hm => ?_ <;> rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
    · obtain ⟨x, rfl⟩ := headOf_eq_el.mp (pat_head_kho h0 ctor_419 noHook_419)
      obtain ⟨y, rfl⟩ := headOf_eq_el.mp (pat_head_kho h1 ctor_419 noHook_419)
      exact hel x y rfl rfl
    · obtain ⟨a, v, rfl⟩ := headOf_eq_kv.mp (pat_head_kho h0 ctor_426 noHook_426)
      obtain ⟨b, w, rfl⟩ := headOf_eq_kv.mp (pat_head_kho h1 ctor_426 noHook_426)
      exact hkv a v b w rfl rfl

end Ckey

/-! ## `insert`, `member` -/

section Ins
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Order

/-- `cmp(T, U) <op> 0` under a substitution whose first two entries are `emb t` and `emb u`. -/
theorem ev_cmpReq_kho {σ : Subst} {t u : T} {op : Sym} {P : Int → Int → Prop} [∀ x y, Decidable (P x y)]
    (hf : ∀ vs, hook op vs = some (int2 vs fun x y => some (bool (decide (P x y)))))
    (h0 : σ.lookup 0 = some (emb t)) (h1 : σ.lookup 1 = some (emb u))
    (hc : c₀.isCtor op = false) (hh : isHook op = true) :
    EvalTerm c₀ σ (cmpReq op) (some (bool (decide (P (cmpF t u) 0)))) :=
  ev_int2 hf (ev_cmp_kho (ev_var h0) (ev_var h1) (cmp_eval_kho t u)) EvalTerm.dv hc hh

spike_hb in
theorem insert_eval_kho (t : T) : ∀ us : List T, Eval c₀ 475 [emb t, embTs us] (some (embTs (insertF t us)))
  | [] =>
    clause_kht (σ := enumFrom 0 [emb t, embTs []]) insertDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embTs_sorted_c₀ []) .nil)))
      (.cons (.var rfl) (.cons (.as (.ctor ctor_406 .nil) rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_407)
  | u :: us => by
    have hσ := ws_enum (vars := [33, 33, 43, 43]) (.cons (emb_sorted_c₀ t) (.cons (emb_sorted_c₀ u)
      (.cons (embTs_sorted_c₀ us) (.cons (embTs_sorted_c₀ (u :: us)) .nil))))
    have hp : PatVals c₀ (enumFrom 0 [emb t, emb u, embTs us, embTs (u :: us)])
        [.var 0, .as (.app 407 [.var 1, .var 2]) 3] [emb t, embTs (u :: us)] :=
      .cons (.var rfl) (.cons (.as (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) rfl) .nil)
    by_cases h1 : cmpF t u < 0
    · rw [insertF, ite_pos h1]
      refine clause_kht insertDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_407)
      intro q hq; cases hq
      have hq := ev_cmpReq_kho (σ := enumFrom 0 [emb t, emb u, embTs us, embTs (u :: us)]) (P := (· < ·))
        hook_intLt rfl rfl notCtor_19 isHook_19
      rwa [decide_eq_true h1] at hq
    · rw [insertF, ite_neg h1]
      by_cases h2 : cmpF t u = 0
      · rw [ite_pos h2]
        refine clause_kht insertDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
        intro q hq; cases hq
        have hq := ev_cmpReq_kho (σ := enumFrom 0 [emb t, emb u, embTs us, embTs (u :: us)]) (P := (· = ·))
          hook_intEq rfl rfl notCtor_23 isHook_23
        rwa [decide_eq_true h2] at hq
      · rw [ite_neg h2]
        have h3 : cmpF t u > 0 := by omega
        refine clause_kht (σ := enumFrom 0 [emb t, emb u, embTs us]) insertDef_lookup
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
          (ws_enum (.cons (emb_sorted_c₀ t) (.cons (emb_sorted_c₀ u) (.cons (embTs_sorted_c₀ us) .nil))))
          (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
          ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
          (ev_ctor (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))
            (insert_eval_kho t us) notCtor_475 notHook_475 notParam_475) .nil)) ctor_407)
        intro q hq; cases hq
        have hq := ev_cmpReq_kho (σ := enumFrom 0 [emb t, emb u, embTs us]) (P := (· > ·))
          hook_intGt rfl rfl notCtor_21 isHook_21
        rwa [decide_eq_true h3] at hq

spike_hb in
theorem member_eval_kho (t : T) : ∀ us : List T, Eval c₀ 490 [emb t, embTs us] (some (bool (memberF t us)))
  | [] =>
    clause_kht (σ := enumFrom 0 [emb t]) memberDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ t) .nil)) (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  | u :: us =>
    clause_kht (σ := enumFrom 0 [emb t, emb u, embTs us]) memberDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (emb_sorted_c₀ u) (.cons (embTs_sorted_c₀ us) .nil))))
      (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_or_kho (ev_cmpReq_kho (P := (· = ·)) hook_intEq rfl rfl notCtor_23 isHook_23)
        (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (member_eval_kho t us)
          notCtor_490 notHook_490 notParam_490))

end Ins

/-! ## `putE`, `union` -/

section Put
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Order

/-- `ckey(E, F) <op> 0` where `ckey` has a value. -/
theorem ev_ckeyReq_kho {σ : Subst} {e f : T} {k : Int} {op : Sym} {P : Int → Int → Prop} [∀ x y, Decidable (P x y)]
    (hk : ckeyF e f = some k) (hf : ∀ vs, hook op vs = some (int2 vs fun x y => some (bool (decide (P x y)))))
    (h0 : σ.lookup 0 = some (emb e)) (h1 : σ.lookup 1 = some (emb f))
    (hc : c₀.isCtor op = false) (hh : isHook op = true) :
    EvalTerm c₀ σ (ckeyReq op) (some (bool (decide (P k 0)))) := by
  have h := ckey_eval_kho e f
  rw [hk] at h
  exact ev_int2 hf (ev_call (.cons (ev_var h0) (.cons (ev_var h1) .nil)) h notCtor_455 notHook_455 notParam_455)
    EvalTerm.dv hc hh

/-- `ckey(E, F) <op> 0` where `ckey` has no value is undefined. -/
theorem ev_ckeyReq_none_kho {σ : Subst} {e f : T} {op : Sym} (hk : ckeyF e f = none)
    (h0 : σ.lookup 0 = some (emb e)) (h1 : σ.lookup 1 = some (emb f))
    (hc : c₀.isCtor op = false) (hh : isHook op = true) : EvalTerm c₀ σ (ckeyReq op) none := by
  have h := ckey_eval_kho e f
  rw [hk] at h
  exact .hook hc hh (.cons (ev_call (.cons (ev_var h0) (.cons (ev_var h1) .nil)) h notCtor_455 notHook_455 notParam_455)
    (.cons EvalTerm.dv .nil)) (fun _ h => nomatch h) (fun _ => rfl)

spike_hb in
theorem putE_eval_kho (e : T) : ∀ fs : List T, Eval c₀ 500 [emb e, embTs fs] ((putEF e fs).map embTs)
  | [] =>
    clause_kht (σ := enumFrom 0 [emb e, embTs []]) putEDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ e) (.cons (embTs_sorted_c₀ []) .nil)))
      (.cons (.var rfl) (.cons (.as (.ctor ctor_406 .nil) rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_407)
  | f :: fs => by
    have hσ := ws_enum (vars := [33, 33, 43, 43]) (.cons (emb_sorted_c₀ e) (.cons (emb_sorted_c₀ f)
      (.cons (embTs_sorted_c₀ fs) (.cons (embTs_sorted_c₀ (f :: fs)) .nil))))
    have hp : PatVals c₀ (enumFrom 0 [emb e, emb f, embTs fs, embTs (f :: fs)])
        [.var 0, .as (.app 407 [.var 1, .var 2]) 3] [emb e, embTs (f :: fs)] :=
      .cons (.var rfl) (.cons (.as (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) rfl) .nil)
    have hσ' := ws_enum (vars := [33, 33, 43]) (.cons (emb_sorted_c₀ e) (.cons (emb_sorted_c₀ f)
      (.cons (embTs_sorted_c₀ fs) .nil)))
    have hp' : PatVals c₀ (enumFrom 0 [emb e, emb f, embTs fs])
        [.var 0, .app 407 [.var 1, .var 2]] [emb e, embTs (f :: fs)] :=
      .cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)
    cases hk : ckeyF e f with
    | none =>
      rw [putEF, hk]
      refine Eval.rest putEDef_lookup fun cl hm => ?_
      simp only [putEDef, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact fails_kht fun σ hm => by
          rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
          exact patCtor_ne_kht (PatVal.as_inv h1).1 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)
      all_goals
        refine .intro fun σ _ hm => ?_
        rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
        first
        | obtain ⟨ws, hw, hs⟩ := pv_ctor (PatVal.as_inv h1).1 ctor_407 noHook_407
        | obtain ⟨ws, hw, hs⟩ := pv_ctor h1 ctor_407 noHook_407
        rw [embTs, GroundTerm.ctor.injEq] at hw
        obtain ⟨-, rfl⟩ := hw
        rcases hs with _ | ⟨h1', -⟩
        exact .intro rfl (ev_ckeyReq_none_kho hk (PatVal.var_inv h0) (PatVal.var_inv h1') (by decide +kernel)
          (by decide +kernel)) nofun
    | some k =>
      rw [putEF, hk]
      simp only [Option.bind_some]
      by_cases h1 : k < 0
      · rw [ite_pos h1]
        refine clause_kht putEDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
          ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_407)
        intro q hq; cases hq
        have hq := ev_ckeyReq_kho (σ := enumFrom 0 [emb e, emb f, embTs fs, embTs (f :: fs)]) (P := (· < ·)) hk
          hook_intLt rfl rfl notCtor_19 isHook_19
        rwa [decide_eq_true h1] at hq
      · rw [ite_neg h1]
        by_cases h2 : k = 0
        · rw [ite_pos h2]
          refine clause_kht putEDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            hσ' hp' ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_407)
          intro q hq; cases hq
          have hq := ev_ckeyReq_kho (σ := enumFrom 0 [emb e, emb f, embTs fs]) (P := (· = ·)) hk
            hook_intEq rfl rfl notCtor_23 isHook_23
          rwa [decide_eq_true h2] at hq
        · rw [ite_neg h2]
          have h3 : k > 0 := by omega
          refine clause_kht putEDef_lookup
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
            hσ' hp' ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
          · intro q hq; cases hq
            have hq := ev_ckeyReq_kho (σ := enumFrom 0 [emb e, emb f, embTs fs]) (P := (· > ·)) hk
              hook_intGt rfl rfl notCtor_21 isHook_21
            rwa [decide_eq_true h3] at hq
          · have h := EvalTerm.ctor (σ := enumFrom 0 [emb e, emb f, embTs fs]) ctor_407 (.cons (ev_var (i := 1) rfl)
              (.cons (ev_call (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 2) rfl) .nil)) (putE_eval_kho e fs)
                notCtor_500 notHook_500 notParam_500) .nil))
            rw [Option.map_map]
            generalize putEF e fs = o at h ⊢
            cases o <;> exact h

spike_hb in
theorem union_eval_kho : ∀ (es fs : List T), Eval c₀ 515 [embTs es, embTs fs] ((unionF es fs).map embTs)
  | es, [] =>
    clause_kht (σ := enumFrom 0 [embTs es]) unionDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embTs_sorted_c₀ es) .nil)) (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | es, f :: fs => by
    have hput := putE_eval_kho f es
    refine clause_kht (σ := enumFrom 0 [embTs es, emb f, embTs fs]) unionDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (embTs_sorted_c₀ es) (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ fs) .nil))))
      (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    rw [unionF]
    cases hp : putEF f es with
    | none =>
      rw [hp] at hput
      exact .callUndef notCtor_515 notHook_515
        (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) hput notCtor_500 notHook_500 notParam_500)
          (.cons (ev_var rfl) .nil)) rfl notParam_515
    | some es' =>
      rw [hp] at hput
      exact ev_call (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) hput notCtor_500 notHook_500
        notParam_500) (.cons (ev_var rfl) .nil)) (union_eval_kho es' fs) notCtor_515 notHook_515 notParam_515

end Put

/-! ## The helpers at `K₀ sig` -/

section Shape

theorem cmpF.eval (t u : T) : Eval (K₀ sig) 456 [emb t, emb u] (some (.dv 3 (.int (cmpF t u)))) :=
  cmp_eval_kho t u
theorem cmpF.eval_iff (t u : T) {r : Option GroundTerm} :
    Eval (K₀ sig) 456 [emb t, emb u] r ↔ r = some (.dv 3 (.int (cmpF t u))) :=
  evalF_iff (cmpF.eval t u)

theorem cmpTsF.eval (ts us : List T) :
    Eval (K₀ sig) 458 [embTs ts, embTs us] (some (.dv 3 (.int (cmpTsF ts us)))) :=
  cmpTs_eval_kho ts us
theorem cmpTsF.eval_iff (ts us : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 458 [embTs ts, embTs us] r ↔ r = some (.dv 3 (.int (cmpTsF ts us))) :=
  evalF_iff (cmpTsF.eval ts us)

theorem cmpIF.eval (x y : Int) :
    Eval (K₀ sig) 457 [.dv 3 (.int x), .dv 3 (.int y)] (some (.dv 3 (.int (cmpIF x y)))) :=
  cmpI_eval_kho x y
theorem cmpIF.eval_iff (x y : Int) {r : Option GroundTerm} :
    Eval (K₀ sig) 457 [.dv 3 (.int x), .dv 3 (.int y)] r ↔ r = some (.dv 3 (.int (cmpIF x y))) :=
  evalF_iff (cmpIF.eval x y)

theorem tagF.eval (t : T) : Eval (K₀ sig) 511 [emb t] (some (.dv 3 (.int (tagF t)))) :=
  tag_eval_kho t
theorem tagF.eval_iff (t : T) {r : Option GroundTerm} :
    Eval (K₀ sig) 511 [emb t] r ↔ r = some (.dv 3 (.int (tagF t))) :=
  evalF_iff (tagF.eval t)

theorem ckeyF.eval (e f : T) :
    Eval (K₀ sig) 455 [emb e, emb f] ((ckeyF e f).map fun k => .dv 3 (.int k)) :=
  ckey_eval_kho e f
theorem ckeyF.eval_iff (e f : T) {r : Option GroundTerm} :
    Eval (K₀ sig) 455 [emb e, emb f] r ↔ r = (ckeyF e f).map fun k => .dv 3 (.int k) :=
  evalF_iff (ckeyF.eval e f)

theorem insertF.eval (t : T) (us : List T) :
    Eval (K₀ sig) 475 [emb t, embTs us] (some (embTs (insertF t us))) :=
  insert_eval_kho t us
theorem insertF.eval_iff (t : T) (us : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 475 [emb t, embTs us] r ↔ r = some (embTs (insertF t us)) :=
  evalF_iff (insertF.eval t us)

theorem memberF.eval (t : T) (us : List T) :
    Eval (K₀ sig) 490 [emb t, embTs us] (some (.dv 2 (.bool (memberF t us)))) :=
  member_eval_kho t us
theorem memberF.eval_iff (t : T) (us : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 490 [emb t, embTs us] r ↔ r = some (.dv 2 (.bool (memberF t us))) :=
  evalF_iff (memberF.eval t us)

theorem putEF.eval (e : T) (fs : List T) :
    Eval (K₀ sig) 500 [emb e, embTs fs] ((putEF e fs).map embTs) :=
  putE_eval_kho e fs
theorem putEF.eval_iff (e : T) (fs : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 500 [emb e, embTs fs] r ↔ r = (putEF e fs).map embTs :=
  evalF_iff (putEF.eval e fs)

theorem unionF.eval (es fs : List T) :
    Eval (K₀ sig) 515 [embTs es, embTs fs] ((unionF es fs).map embTs) :=
  union_eval_kho es fs
theorem unionF.eval_iff (es fs : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 515 [embTs es, embTs fs] r ↔ r = (unionF es fs).map embTs :=
  evalF_iff (unionF.eval es fs)

end Shape

/-! ## The order on encodings -/

section Ord
open _root_.KK.Kit (ite_pos ite_neg)

/-- `t` is the encoding of a value sorted in `c` whose literals have a kore.k form. -/
def EncSorted (c : Semantics) (t : T) : Prop :=
  ∃ v s, c.sortOf v = some s ∧ litsV v = true ∧ enc v = t

theorem encSorted_enc {c : Semantics} {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (lv : litsV v = true) : EncSorted c (enc v) :=
  ⟨v, s, hv, lv, rfl⟩

/-- On such encodings `cmpF` is 0 exactly between equal terms. -/
theorem cmpF_eq_zero_iff_ord {c : Semantics} {t u : T} (ht : EncSorted c t) (hu : EncSorted c u) :
    cmpF t u = 0 ↔ t = u := by
  obtain ⟨v, s, hv, lv, rfl⟩ := ht
  obtain ⟨w, s', hw, lw, rfl⟩ := hu
  rw [cmpF_eq_zero_iff hv hw lv lw]
  exact ⟨congrArg enc, enc_inj hv hw lv lw⟩

theorem cmpF_trans_ord {c : Semantics} {t u w : T} (ht : EncSorted c t) (hu : EncSorted c u)
    (hw : EncSorted c w) (h1 : cmpF t u = -1) (h2 : cmpF u w = -1) : cmpF t w = -1 := by
  obtain ⟨v₁, s₁, hv₁, -, rfl⟩ := ht
  obtain ⟨v₂, s₂, hv₂, -, rfl⟩ := hu
  obtain ⟨v₃, s₃, hv₃, -, rfl⟩ := hw
  exact cmpF_trans hv₁ hv₂ hv₃ h1 h2

/-- `member` on such encodings is membership. -/
theorem memberF_iff_ord {c : Semantics} {t : T} (ht : EncSorted c t) :
    ∀ {us : List T}, (∀ u ∈ us, EncSorted c u) → (memberF t us = true ↔ t ∈ us)
  | [], _ => by simp [memberF]
  | u :: us, hus => by
    rw [memberF, Bool.or_eq_true, decide_eq_true_iff, cmpF_eq_zero_iff_ord ht (hus u (List.mem_cons_self ..)),
      memberF_iff_ord ht fun w hw => hus w (List.mem_cons_of_mem _ hw), List.mem_cons]

/-- `member(enc v, ws)` on the encodings of values sorted in one semantics is whether `v` is in
`ws`. -/
theorem memberF_enc {c : Semantics} {v : GroundTerm} {s : Srt} {ws : List GroundTerm}
    (hv : c.sortOf v = some s) (lv : litsV v = true)
    (hws : ∀ w ∈ ws, ∃ s', c.sortOf w = some s' ∧ litsV w = true) :
    memberF (enc v) (ws.map enc) = decide (v ∈ ws) := by
  have hall : ∀ u ∈ ws.map enc, EncSorted c u := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    obtain ⟨s', h1, h2⟩ := hws w hw
    exact encSorted_enc h1 h2
  have h := memberF_iff_ord (encSorted_enc hv lv) hall
  have hm : enc v ∈ ws.map enc ↔ v ∈ ws := by
    refine ⟨fun hm => ?_, fun hm => List.mem_map_of_mem hm⟩
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
    obtain ⟨s', h1, h2⟩ := hws w hw
    rwa [enc_inj h1 hv h2 lv he] at hw
  rw [hm] at h
  by_cases hin : v ∈ ws
  · rw [decide_eq_true hin]; exact h.mpr hin
  · rw [decide_eq_false hin]; exact Bool.eq_false_iff.mpr fun e => hin (h.mp e)

/-- `insert` on such encodings adds `t` to the members. -/
theorem insertF_mem_ord {c : Semantics} {t : T} (ht : EncSorted c t) :
    ∀ {us : List T}, (∀ u ∈ us, EncSorted c u) → ∀ x, (x ∈ insertF t us ↔ x = t ∨ x ∈ us)
  | [], _, x => by simp [insertF]
  | u :: us, hus, x => by
    have hu := hus u (List.mem_cons_self ..)
    rw [insertF]
    by_cases h1 : cmpF t u < 0
    · rw [ite_pos h1, List.mem_cons]
    · rw [ite_neg h1]
      by_cases h2 : cmpF t u = 0
      · rw [ite_pos h2, (cmpF_eq_zero_iff_ord ht hu).mp h2, List.mem_cons]
        constructor
        · intro h; exact .inr h
        · rintro (h | h | h) <;> simp [h]
      · rw [ite_neg h2, List.mem_cons, List.mem_cons,
          insertF_mem_ord ht (fun w hw => hus w (List.mem_cons_of_mem _ hw)) x]
        constructor
        · rintro (h | h | h) <;> simp [h]
        · rintro (h | h | h) <;> simp [h]

/-- `insert` keeps a list of such encodings strictly increasing by `cmpF`. -/
theorem insertF_sorted_ord {c : Semantics} {t : T} (ht : EncSorted c t) :
    ∀ {us : List T}, (∀ u ∈ us, EncSorted c u) → us.Pairwise (fun a b => cmpF a b = -1) →
      (insertF t us).Pairwise (fun a b => cmpF a b = -1)
  | [], _, _ => by simp [insertF]
  | u :: us, hus, hs => by
    have hu := hus u (List.mem_cons_self ..)
    have hus' : ∀ w ∈ us, EncSorted c w := fun w hw => hus w (List.mem_cons_of_mem _ hw)
    rw [List.pairwise_cons] at hs
    rw [insertF]
    by_cases h1 : cmpF t u < 0
    · rw [ite_pos h1]
      have htu : cmpF t u = -1 := by rcases cmpF_range t u with h | h | h <;> omega
      refine List.Pairwise.cons (fun w hw => ?_) (List.Pairwise.cons hs.1 hs.2)
      rcases List.mem_cons.mp hw with rfl | hw
      · exact htu
      · exact cmpF_trans_ord ht hu (hus' w hw) htu (hs.1 w hw)
    · rw [ite_neg h1]
      by_cases h2 : cmpF t u = 0
      · rw [ite_pos h2]; exact List.Pairwise.cons hs.1 hs.2
      · rw [ite_neg h2]
        have hut : cmpF u t = -1 := by
          rw [cmpF_swap]; rcases cmpF_range t u with h | h | h <;> omega
        refine List.Pairwise.cons (fun w hw => ?_) (insertF_sorted_ord ht hus' hs.2)
        rcases (insertF_mem_ord ht hus' w).mp hw with rfl | hw
        · exact hut
        · exact hs.1 w hw

/-- `insert` leaves a list of such encodings strictly increasing by `cmpF` unchanged where `t` is a
member. -/
theorem insertF_of_mem_ord {c : Semantics} {t : T} (ht : EncSorted c t) :
    ∀ {us : List T}, (∀ u ∈ us, EncSorted c u) → us.Pairwise (fun a b => cmpF a b = -1) → t ∈ us →
      insertF t us = us
  | [], _, _, hm => nomatch hm
  | u :: us, hus, hs, hm => by
    have hu := hus u (List.mem_cons_self ..)
    rw [List.pairwise_cons] at hs
    rw [insertF]
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [cmpF_self, ite_neg (show ¬ (0 : Int) < 0 by decide), ite_pos rfl]
    · have hut := hs.1 t hm
      have htu : cmpF t u = 1 := by rw [cmpF_swap, hut]; rfl
      rw [htu, ite_neg (show ¬ (1 : Int) < 0 by decide), ite_neg (show ¬ (1 : Int) = 0 by decide),
        insertF_of_mem_ord ht (fun w hw => hus w (List.mem_cons_of_mem _ hw)) hs.2 hm]

/-- kore.k's `ckey` computes, between any two members of a map or set that the encoding of a value
sorted in `c` with kore.k literals holds, -1 for the earlier: `enc` writes them strictly increasing
by `ckeyF` (`enc_canonical`), and `ckey` evaluates to `ckeyF`. -/
theorem ckey_canon_eval {c : Semantics} {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (lv : litsV v = true) {k : Kind} {n : Int} {es : List T} (he : enc v = .co k n es) (hk : k ≠ .list) :
    es.Pairwise fun a b => Eval (K₀ sig) 455 [emb a, emb b] (some (.dv 3 (.int (-1)))) := by
  have h := enc_canonical hv lv
  rw [he, Canon] at h
  refine (h.1 hk).imp fun {a b} hab => ?_
  have := ckeyF.eval a b
  rwa [hab] at this

end Ord

/-! ## Checks -/

#check @cmpF.eval
#check @cmpF.eval_iff
#check @cmpTsF.eval
#check @cmpTsF.eval_iff
#check @cmpIF.eval
#check @cmpIF.eval_iff
#check @tagF.eval
#check @tagF.eval_iff
#check @ckeyF.eval
#check @ckeyF.eval_iff
#check @insertF.eval
#check @insertF.eval_iff
#check @memberF.eval
#check @memberF.eval_iff
#check @putEF.eval
#check @putEF.eval_iff
#check @unionF.eval
#check @unionF.eval_iff
#check @cmpF_eq_zero_iff_ord
#check @cmpF_trans_ord
#check @memberF_iff_ord
#check @memberF_enc
#check @insertF_mem_ord
#check @insertF_sorted_ord
#check @insertF_of_mem_ord
#check @ckey_canon_eval

open Lean in
#eval show CoreM Unit from do
  for n in [``helpOrder_names, ``cmpF.eval, ``cmpF.eval_iff, ``cmpTsF.eval, ``cmpTsF.eval_iff, ``cmpIF.eval,
      ``cmpIF.eval_iff, ``tagF.eval, ``tagF.eval_iff, ``ckeyF.eval, ``ckeyF.eval_iff, ``insertF.eval,
      ``insertF.eval_iff, ``memberF.eval, ``memberF.eval_iff, ``putEF.eval, ``putEF.eval_iff, ``unionF.eval,
      ``unionF.eval_iff, ``cmpF_eq_zero_iff_ord, ``cmpF_trans_ord, ``memberF_iff_ord, ``memberF_enc,
      ``insertF_mem_ord, ``insertF_sorted_ord, ``insertF_of_mem_ord, ``ckey_canon_eval] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
