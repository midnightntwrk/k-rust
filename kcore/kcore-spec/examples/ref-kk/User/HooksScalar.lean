/-
  kore.k's `strictHook` at the operation codes of Int (1 to 5, 10 to 15), Bool (20 to 23), `ite`
  (30), K equality (70, 71) and String (80, 81), on kore.k's semantics read from its kompiled text:
  at the code `o` of an interpreted symbol `f` (`hookCodes`) and the encoded arguments, `strictHook`
  evaluates at `K₀ sig` to the encoding of KCore's result, `emb (encR ((d₀ d).hookRes f vs).join)`,
  for every semantics `d`. Where the text gives no value (`/Int` and `%Int` by zero, an argument of
  another shape or number) both sides are undefined: KCore's `hook` gives none and kore.k's
  `op-undef` gives `bot`.

  The proof has two sides. On kore.k's side, `hookOp` at a code evaluates over the mirrors to a Lean
  function of the arguments' terms (`int2T_khs`, `bool2T_khs`, `notT_khs`, `iteT_khs`, `keqT_khs`,
  `kneT_khs`, `str2T_khs`): the equation of the code where its patterns hold, `op-undef` where none
  of the code's equations applies (every equation of another code fails at its code literal), and
  `strictHook` adds `hook-bot` (`strictT_khs`). On KCore's side, each function at the encodings is
  `encR` of `hook`'s value: `enc` writes `iv`, `bv` exactly at an Int or Bool literal of its sort,
  as `asInt` and `asBool` read them (`ivOf_enc_khs`, `bvOf_enc_khs`). None of these symbols is a
  key of `silentTable`, so `hookRes` is `hook` at every interpretation.

  Hypotheses where the two readings could part:
  - 80, 81: `tk(_, X)` matches a token of any sort, `asStr` a String: the arguments are sorted at
    `String`.
  - 70, 71: `cmp` is 0 exactly between equal encodings of values sorted in one semantics whose
    literals have a kore.k form (`cmpF_eq_zero_iff`); a Float literal is written `bot`, and two such
    compare 0. The arguments are sorted and `litsV`.
  - 30: the branch not taken may be a value `enc` writes `bot` (a Float), where `hook-bot` gives `bot`
    and KCore the other branch: the arguments are `litsV` (no sort: an `ite` at any sort reads it).
  `=/=Bool` has no code: it is written `hk 22 [hk 23 as]`, `notBool (B1 ==Bool B2)`, and
  `boolNe_comp` is that composition on KCore's side at every argument list; `boolNe_hook` and
  `boolNe_term` evaluate the nested form at every argument list from the lemmas of codes 23 and 22.
  `hooks_scalar` states the twenty codes at once (at `opOf f = some o` with `o` below 40 or from 70
  on), `hooks_scalar_add` … one each.

  The clauses are the semantics' own, as literals tied to `lookupFn` by the kernel.
-/
import User.HelpWalk
import User.HelpOrder

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## kore.k's results over the mirrors -/

/-- The Int of an `iv` term. -/
def ivOf_khs : T → Option Int
  | .iv x => some x
  | _ => none

/-- The Bool of a `bv` term. -/
def bvOf_khs : T → Option Bool
  | .bv b => some b
  | _ => none

/-- The string of a `tk` term, as code points. -/
def tkOf_khs : T → Option (List Char)
  | .tk _ x => some x.toList
  | _ => none

/-- `hookOp` at a code whose equation reads two `iv` arguments. -/
def int2T_khs (f : Int → Int → T) : List T → T
  | [a, b] => match ivOf_khs a, ivOf_khs b with
    | some x, some y => f x y
    | _, _ => .bot
  | _ => .bot

/-- `hookOp` at a code whose equation reads two `bv` arguments. -/
def bool2T_khs (f : Bool → Bool → Bool) : List T → T
  | [a, b] => match bvOf_khs a, bvOf_khs b with
    | some x, some y => .bv (f x y)
    | _, _ => .bot
  | _ => .bot

/-- `hookOp(22, …)`, `op-not`. -/
def notT_khs : List T → T
  | [a] => match bvOf_khs a with
    | some x => .bv !x
    | none => .bot
  | _ => .bot

/-- `hookOp(30, …)`, `op-ite-then` and `op-ite-else`. -/
def iteT_khs : List T → T
  | [c, t, e] => match bvOf_khs c with
    | some b => if b then t else e
    | none => .bot
  | _ => .bot

/-- `hookOp(70, …)`, `op-keq`. -/
def keqT_khs : List T → T
  | [a, b] => .bv (decide (cmpF a b = 0))
  | _ => .bot

/-- `hookOp(71, …)`, `op-kne`. -/
def kneT_khs : List T → T
  | [a, b] => .bv (decide (cmpF a b ≠ 0))
  | _ => .bot

/-- `hookOp` at a code whose equation reads two `tk` arguments. -/
def str2T_khs (f : List Char → List Char → Bool) : List T → T
  | [a, b] => match tkOf_khs a, tkOf_khs b with
    | some x, some y => .bv (f x y)
    | _, _ => .bot
  | _ => .bot

/-- kore.k's `strictHook(O, Ts)`: `bot` where a term of the list is `bot` (`hook-bot`), else
`hookOp`'s value `r` (`hook-def`). -/
def strictT_khs (ts : List T) (r : T) : T := if hasBotF ts then .bot else r

/-! ## The symbols -/

/-- Each symbol number the evaluations below are at has the KORE name of the function. -/
theorem hooksScalar_names :
    RefKk.defn.sem.symName 473 = "LblhookOp'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 508 = "LblstrictHook'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Int'Unds'Ts" := by
  decide +kernel

/-! ## The clauses, as the semantics holds them -/

namespace HooksS
open _root_.KK Terms

/-- `hook-def`. -/
abbrev hookDefCl : Clause :=
  plainCl [3, 43] [.var 0, .var 1] (.app 473 [.var 0, .var 1]) (req := some (.app 3 [.app 471 [.var 1]]))
/-- `hook-bot`. -/
abbrev hookBotCl : Clause :=
  plainCl [3, 43] [.var 0, .var 1] (.app 412 []) (req := some (.app 471 [.var 1]))

/-- `strictHook` (508). -/
def strictHookDef : Fn :=
  { label := 508, args := [3, 43], result := 33, total := false, clauses := [hookDefCl, hookBotCl] }

abbrev opAdd : Clause := plainCl [3, 3]
  [.dv 3 (.int 1), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 425 [.app 12 [.var 0, .var 1]])
abbrev opLt : Clause := plainCl [3, 3]
  [.dv 3 (.int 10), .app 407 [.app 425 [.var 1], .app 407 [.app 425 [.var 0], .app 406 []]]]
  (.app 413 [.app 19 [.var 1, .var 0]])
abbrev opLe : Clause := plainCl [3, 3]
  [.dv 3 (.int 11), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 413 [.app 20 [.var 0, .var 1]])
abbrev opGt : Clause := plainCl [3, 3]
  [.dv 3 (.int 12), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 413 [.app 21 [.var 0, .var 1]])
abbrev opGe : Clause := plainCl [3, 3]
  [.dv 3 (.int 13), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 413 [.app 22 [.var 0, .var 1]])
abbrev opEq : Clause := plainCl [3, 3]
  [.dv 3 (.int 14), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 413 [.app 23 [.var 0, .var 1]])
abbrev opNe : Clause := plainCl [3, 3]
  [.dv 3 (.int 15), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 413 [.app 24 [.var 0, .var 1]])
abbrev opSub : Clause := plainCl [3, 3]
  [.dv 3 (.int 2), .app 407 [.app 425 [.var 1], .app 407 [.app 425 [.var 0], .app 406 []]]]
  (.app 425 [.app 13 [.var 1, .var 0]])
abbrev opAnd : Clause := plainCl [2, 2]
  [.dv 3 (.int 20), .app 407 [.app 413 [.var 0], .app 407 [.app 413 [.var 1], .app 406 []]]]
  (.app 413 [.app 4 [.var 0, .var 1]])
abbrev opOr : Clause := plainCl [2, 2]
  [.dv 3 (.int 21), .app 407 [.app 413 [.var 0], .app 407 [.app 413 [.var 1], .app 406 []]]]
  (.app 413 [.app 6 [.var 0, .var 1]])
abbrev opNot : Clause := plainCl [2]
  [.dv 3 (.int 22), .app 407 [.app 413 [.var 0], .app 406 []]] (.app 413 [.app 3 [.var 0]])
abbrev opBoolEq : Clause := plainCl [2, 2]
  [.dv 3 (.int 23), .app 407 [.app 413 [.var 0], .app 407 [.app 413 [.var 1], .app 406 []]]]
  (.app 413 [.app 10 [.var 0, .var 1]])
abbrev opMul : Clause := plainCl [3, 3]
  [.dv 3 (.int 3), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 425 [.app 14 [.var 0, .var 1]])
abbrev opIteThen : Clause := plainCl [2, 33, 33]
  [.dv 3 (.int 30), .app 407 [.app 413 [.var 0], .app 407 [.var 1, .app 407 [.var 2, .app 406 []]]]]
  (.var 1) (req := some (.var 0))
abbrev opIteElse : Clause := plainCl [33, 2, 33]
  [.dv 3 (.int 30), .app 407 [.app 413 [.var 1], .app 407 [.var 2, .app 407 [.var 0, .app 406 []]]]]
  (.var 0) (req := some (.app 3 [.var 1]))
abbrev opDiv : Clause := plainCl [3, 3]
  [.dv 3 (.int 4), .app 407 [.app 425 [.var 1], .app 407 [.app 425 [.var 0], .app 406 []]]]
  (.app 425 [.app 15 [.var 1, .var 0]]) (req := some (.app 24 [.var 0, .dv 3 (.int 0)]))
abbrev opLookup : Clause := plainCl [33, 3, 43]
  [.dv 3 (.int 40), .app 407 [.app 416 [.app 429 [], .var 1, .var 2], .app 407 [.var 0, .app 406 []]]]
  (.app 517 [.var 0, .app 412 [], .var 2])
abbrev opLookupOr : Clause := plainCl [3, 43, 33, 33]
  [.dv 3 (.int 41), .app 407 [.app 416 [.app 429 [], .var 0, .var 1], .app 407 [.var 2, .app 407 [.var 3, .app 406 []]]]]
  (.app 517 [.var 2, .var 3, .var 1])
abbrev opUpdate : Clause := plainCl [33, 34, 3, 43, 33]
  [.dv 3 (.int 42), .app 407 [.app 416 [.as (.app 429 []) 1, .var 2, .var 3], .app 407 [.var 4, .app 407 [.var 0, .app 406 []]]]]
  (.app 416 [.var 1, .var 2, .app 500 [.app 426 [.var 4, .var 0], .var 3]])
abbrev opRemove : Clause := plainCl [34, 3, 43, 33]
  [.dv 3 (.int 43), .app 407 [.app 416 [.as (.app 429 []) 0, .var 1, .var 2], .app 407 [.var 3, .app 406 []]]]
  (.app 416 [.var 0, .var 1, .app 461 [.app 426 [.var 3, .var 3], .var 2]])
abbrev opInKeys : Clause := plainCl [33, 3, 43]
  [.dv 3 (.int 44), .app 407 [.var 0, .app 407 [.app 416 [.app 429 [], .var 1, .var 2], .app 406 []]]]
  (.app 413 [.app 472 [.app 426 [.var 0, .var 0], .var 2]])
abbrev opSizeMap : Clause := plainCl [3, 43]
  [.dv 3 (.int 45), .app 407 [.app 416 [.app 429 [], .var 0, .var 1], .app 406 []]] (.app 425 [.app 481 [.var 1]])
abbrev opMod : Clause := plainCl [3, 3]
  [.dv 3 (.int 5), .app 407 [.app 425 [.var 0], .app 407 [.app 425 [.var 1], .app 406 []]]]
  (.app 425 [.app 16 [.var 0, .var 1]]) (req := some (.app 24 [.var 1, .dv 3 (.int 0)]))
abbrev opSetIn : Clause := plainCl [43, 33, 3]
  [.dv 3 (.int 50), .app 407 [.var 1, .app 407 [.app 416 [.app 438 [], .var 2, .var 0], .app 406 []]]]
  (.app 413 [.app 472 [.app 419 [.var 1], .var 0]])
abbrev opSizeSet : Clause := plainCl [43, 3]
  [.dv 3 (.int 51), .app 407 [.app 416 [.app 438 [], .var 1, .var 0], .app 406 []]] (.app 425 [.app 481 [.var 0]])
abbrev opUnion : Clause := plainCl [34, 43, 3, 3, 43]
  [.dv 3 (.int 52), .app 407 [.app 416 [.as (.app 438 []) 0, .var 3, .var 4], .app 407 [.app 416 [.as (.app 438 []) 0, .var 2, .var 1], .app 406 []]]]
  (.app 416 [.var 0, .var 3, .app 515 [.var 4, .var 1]])
abbrev opSizeList : Clause := plainCl [3, 43]
  [.dv 3 (.int 60), .app 407 [.app 416 [.app 427 [], .var 0, .var 1], .app 406 []]] (.app 425 [.app 481 [.var 1]])
abbrev opKeq : Clause := plainCl [33, 33]
  [.dv 3 (.int 70), .app 407 [.var 1, .app 407 [.var 0, .app 406 []]]]
  (.app 413 [.app 23 [.app 456 [.var 1, .var 0], .dv 3 (.int 0)]])
abbrev opKne : Clause := plainCl [33, 33]
  [.dv 3 (.int 71), .app 407 [.var 0, .app 407 [.var 1, .app 406 []]]]
  (.app 413 [.app 24 [.app 456 [.var 0, .var 1], .dv 3 (.int 0)]])
abbrev opStrEq : Clause := plainCl [3, 10, 3, 10]
  [.dv 3 (.int 80), .app 407 [.app 443 [.var 0, .var 1], .app 407 [.app 443 [.var 2, .var 3], .app 406 []]]]
  (.app 413 [.app 285 [.var 1, .var 3]])
abbrev opStrLt : Clause := plainCl [3, 10, 3, 10]
  [.dv 3 (.int 81), .app 407 [.app 443 [.var 2, .var 3], .app 407 [.app 443 [.var 0, .var 1], .app 406 []]]]
  (.app 413 [.app 287 [.var 3, .var 1]])
/-- `op-undef`, `[owise]`. -/
abbrev opUndef : Clause := plainCl [3, 43] [.var 0, .var 1] (.app 412 []) (prio := 200)

/-- The equations of `hookOp` other than `op-undef`, in the semantics' order. -/
def opCls : List Clause :=
  [opAdd, opLt, opLe, opGt, opGe, opEq, opNe, opSub, opAnd, opOr, opNot, opBoolEq, opMul, opIteThen,
   opIteElse, opDiv, opLookup, opLookupOr, opUpdate, opRemove, opInKeys, opSizeMap, opMod, opSetIn,
   opSizeSet, opUnion, opSizeList, opKeq, opKne, opStrEq, opStrLt]

/-- `hookOp` (473). -/
def hookOpDef : Fn :=
  { label := 473, args := [3, 43], result := 33, total := false, clauses := opCls ++ [opUndef] }

theorem strictHookDef_lookup : c₀.lookupFn 508 = some strictHookDef := by kernel_rfl
theorem hookOpDef_lookup : c₀.lookupFn 473 = some hookOpDef := by kernel_rfl

/-- The code an equation of `hookOp` is at: its first pattern's Int literal. -/
def codeOf (cl : Clause) : Option Int :=
  match cl.pats with
  | .dv 3 (.int k) :: _ => some k
  | _ => none

theorem codeOf_all : ∀ cl ∈ opCls, (codeOf cl).isSome = true := by decide +kernel

end HooksS

/-! ## Shared steps -/

section KitS
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms HooksS

/-- An interpreted symbol of one argument at a term with a value, where `hook` gives a value. -/
theorem ev_hook1_khs {σ : Subst} {f : Sym} {a : Term} {va r : GroundTerm}
    (hf : hook f [va] = some (some r)) (ha : EvalTerm c₀ σ a (some va))
    (hc : c₀.isCtor f = false := by decide +kernel) (hh : isHook f = true := by decide +kernel) :
    EvalTerm c₀ σ (.app f [a]) (some r) := by
  refine .hook hc hh (EvArgs.terms (.cons ha .nil)) (fun vs hvs => ?_) (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value hf
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

/-- An interpreted symbol of two arguments at two terms with values, where `hook` gives a value. -/
theorem ev_hook2_khs {σ : Subst} {f : Sym} {a b : Term} {va vb r : GroundTerm}
    (hf : hook f [va, vb] = some (some r)) (ha : EvalTerm c₀ σ a (some va)) (hb : EvalTerm c₀ σ b (some vb))
    (hc : c₀.isCtor f = false := by decide +kernel) (hh : isHook f = true := by decide +kernel) :
    EvalTerm c₀ σ (.app f [a, b]) (some r) := by
  refine .hook hc hh (EvArgs.terms (.cons ha (.cons hb .nil))) (fun vs hvs => ?_) (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value hf
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

/-- `T ; Ts` as a pattern denotes the embedding of a nonempty list. -/
theorem pv_cons_khs {σ : Subst} {p q : Term} {ts : List T} (h : PatVal c₀ σ (.app 407 [p, q]) (embTs ts)) :
    ∃ t ts', ts = t :: ts' ∧ PatVal c₀ σ p (emb t) ∧ PatVal c₀ σ q (embTs ts') := by
  obtain ⟨ws, he, hws⟩ := pv_ctor h
  cases ts with
  | nil => rw [embTs] at he; cases he
  | cons t ts' =>
    rw [embTs] at he
    obtain ⟨-, rfl⟩ := GroundTerm.ctor.inj he
    rcases hws with _ | ⟨h1, _ | ⟨h2, -⟩⟩
    exact ⟨t, ts', rfl, h1, h2⟩

/-- `.Ts` as a pattern denotes the embedding of the empty list only. -/
theorem pv_nil_khs {σ : Subst} {ts : List T} (h : PatVal c₀ σ (.app 406 []) (embTs ts)) : ts = [] := by
  obtain ⟨ws, he, -⟩ := pv_ctor h
  cases ts with
  | nil => rfl
  | cons t ts' => rw [embTs] at he; cases he

/-- `iv(I)` as a pattern denotes an `iv` term, and binds its Int. -/
theorem pv_iv_khs {σ : Subst} {i : Nat} {t : T} (h : PatVal c₀ σ (.app 425 [.var i]) (emb t)) :
    ∃ x, t = .iv x ∧ σ.lookup i = some (.dv 3 (.int x)) := by
  obtain ⟨ws, he, hws⟩ := pv_ctor h
  rw [emb_ctor] at he
  obtain ⟨hh, rfl⟩ := GroundTerm.ctor.inj he
  obtain ⟨x, rfl⟩ := headOf_eq_iv.mp hh
  rcases hws with _ | ⟨hv, -⟩
  cases hv with
  | var hl => exact ⟨x, rfl, hl⟩

/-- `bv(B)` as a pattern denotes a `bv` term, and binds its Bool. -/
theorem pv_bv_khs {σ : Subst} {i : Nat} {t : T} (h : PatVal c₀ σ (.app 413 [.var i]) (emb t)) :
    ∃ b, t = .bv b ∧ σ.lookup i = some (.dv 2 (.bool b)) := by
  obtain ⟨ws, he, hws⟩ := pv_ctor h
  rw [emb_ctor] at he
  obtain ⟨hh, rfl⟩ := GroundTerm.ctor.inj he
  obtain ⟨b, rfl⟩ := headOf_eq_bv.mp hh
  rcases hws with _ | ⟨hv, -⟩
  cases hv with
  | var hl => exact ⟨b, rfl, hl⟩

/-- `tk(S, X)` as a pattern denotes a `tk` term. -/
theorem pv_tk_khs {σ : Subst} {i j : Nat} {t : T} (h : PatVal c₀ σ (.app 443 [.var i, .var j]) (emb t)) :
    ∃ s x, t = .tk s x := by
  obtain ⟨ws, he, -⟩ := pv_ctor h
  rw [emb_ctor] at he
  exact headOf_eq_tk.mp (GroundTerm.ctor.inj he).1

/-- A variable pattern binds the value. -/
theorem pv_var_khs {σ : Subst} {i : Nat} {v : GroundTerm} (h : PatVal c₀ σ (.var i) v) : σ.lookup i = some v := by
  cases h with
  | var hl => exact hl

/-- An equation of another code fails. -/
theorem fails_code_khs {cl : Clause} {k o : Int} {rest : List GroundTerm} (hk : codeOf cl = some k)
    (hne : k ≠ o) : Fails c₀ (.dv 3 (.int o) :: rest) cl := by
  unfold codeOf at hk
  split at hk
  · next k' ps heq =>
    cases hk
    refine .intro fun σ _ hm => ?_
    rw [heq] at hm
    rcases hm with _ | ⟨h0, -⟩
    cases h0
    exact (hne rfl).elim
  · cases hk

/-- `op-undef`: where every equation of the code fails, `hookOp` is `bot`. -/
theorem hookOp_undef_khs {o : Int} {ts : List T}
    (h : ∀ cl ∈ opCls.filter (fun c => codeOf c == some o), Fails c₀ [.dv 3 (.int o), embTs ts] cl) :
    Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb .bot)) := by
  refine Eval.clause (σ := enumFrom 0 [.dv 3 (.int o), embTs ts]) (cl := opUndef) hookOpDef_lookup
    (List.mem_append_right _ (List.mem_singleton_self _))
    (ws_enum (.cons (sort_int o) (.cons (embTs_sorted_c₀ ts) .nil)))
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun _ h => by cases h) Holds.top ?_ rfl
    (ev_ctor .nil ctor_412) (fun _ h => by cases h) Holds.top
  intro cl hm _ hp
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (codeOf_all cl hm)
    by_cases hko : k = o
    · subst hko
      exact h cl (List.mem_filter.mpr ⟨hm, by rw [hk]; exact beq_self_eq_true _⟩)
    · exact fails_code_khs hk hko
  · rw [List.mem_singleton] at hm
    subst hm
    exact absurd hp (by decide)

/-- `hasBot` at a list of no `bot`. -/
theorem hasBotF_false_khs {ts : List T} (h : ∀ t ∈ ts, t ≠ .bot) : hasBotF ts = false := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [hasBotF, decide_eq_false (h t (List.mem_cons_self ..)), Bool.false_or]
    exact ih fun u hu => h u (List.mem_cons_of_mem _ hu)

/-- `strictHook(O, Ts)`: `hook-bot` where `hasBot(Ts)`, else `hook-def` at `hookOp`'s value. -/
theorem strictHook_eval_khs (o : Int) (ts : List T) {r : T}
    (h : hasBotF ts = false → Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb r))) :
    Eval c₀ 508 [.dv 3 (.int o), embTs ts] (some (emb (strictT_khs ts r))) := by
  have hσ := ws_enum (vars := [3, 43]) (.cons (sort_int o) (.cons (embTs_sorted_c₀ ts) .nil))
  have hp : PatVals c₀ (enumFrom 0 [.dv 3 (.int o), embTs ts]) [.var 0, .var 1] [.dv 3 (.int o), embTs ts] :=
    .cons (.var rfl) (.cons (.var rfl) .nil)
  have hb := hasBotF_eval_c₀ ts
  unfold strictT_khs
  cases e : hasBotF ts with
  | true =>
    rw [e] at hb
    exact clause_kht strictHookDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp
      (fun t ht => by
        cases ht
        exact ev_call (.cons (ev_var rfl) .nil) hb notCtor_471 notHook_471 notParam_471)
      (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_412)
  | false =>
    rw [e] at hb
    exact clause_kht strictHookDef_lookup (List.mem_cons_self ..) hσ hp
      (fun t ht => by
        cases ht
        exact ev_hook1_khs rfl (ev_call (.cons (ev_var rfl) .nil) hb notCtor_471 notHook_471 notParam_471))
      (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (h e) notCtor_473 notHook_473 notParam_473)

end KitS

/-! ## `hookOp` at each shape of arguments -/

section Shapes
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms HooksS

theorem ivOf_some_khs {t : T} {x : Int} (h : ivOf_khs t = some x) : t = .iv x := by
  cases t <;> simp_all [ivOf_khs]

theorem bvOf_some_khs {t : T} {b : Bool} (h : bvOf_khs t = some b) : t = .bv b := by
  cases t <;> simp_all [bvOf_khs]

theorem tkOf_some_khs {t : T} {x : List Char} (h : tkOf_khs t = some x) : ∃ s y, t = .tk s y ∧ y.toList = x := by
  cases t with
  | tk s y => exact ⟨s, y, rfl, Option.some.inj h⟩
  | _ => cases h

/-- Two `iv` arguments: the code's equation, given at every two Ints (`hpos`); `op-undef` otherwise. -/
theorem hookOp_int2_khs {o : Int} {cl : Clause} {f : Int → Int → T} {i j : Nat}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl])
    (hp : cl.pats = [.dv 3 (.int o), .app 407 [.app 425 [.var i], .app 407 [.app 425 [.var j], .app 406 []]]])
    (hpos : ∀ x y, Eval c₀ 473 [.dv 3 (.int o), embTs [.iv x, .iv y]] (some (emb (f x y)))) (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb (int2T_khs f ts))) := by
  by_cases hs : ∃ x y, ts = [.iv x, .iv y]
  · obtain ⟨x, y, rfl⟩ := hs
    exact hpos x y
  · have e : int2T_khs f ts = .bot := by
      unfold int2T_khs
      split
      · next a b =>
        split
        · next x y ha hb => exact (hs ⟨x, y, by rw [ivOf_some_khs ha, ivOf_some_khs hb]⟩).elim
        · rfl
      · rfl
    rw [e]
    refine hookOp_undef_khs fun c hc => ?_
    rw [hf, List.mem_singleton] at hc
    subst hc
    refine .intro fun σ _ hm => ?_
    rw [hp] at hm
    rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
    obtain ⟨t, ts', rfl, h2, h3⟩ := pv_cons_khs h1
    obtain ⟨u, ts'', rfl, h4, h5⟩ := pv_cons_khs h3
    obtain rfl := pv_nil_khs h5
    obtain ⟨x, rfl, -⟩ := pv_iv_khs h2
    obtain ⟨y, rfl, -⟩ := pv_iv_khs h4
    exact (hs ⟨x, y, rfl⟩).elim

/-- Two `bv` arguments. -/
theorem hookOp_bool2_khs {o : Int} {cl : Clause} {f : Bool → Bool → Bool} {i j : Nat}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl])
    (hp : cl.pats = [.dv 3 (.int o), .app 407 [.app 413 [.var i], .app 407 [.app 413 [.var j], .app 406 []]]])
    (hpos : ∀ x y, Eval c₀ 473 [.dv 3 (.int o), embTs [.bv x, .bv y]] (some (emb (.bv (f x y))))) (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb (bool2T_khs f ts))) := by
  by_cases hs : ∃ x y, ts = [.bv x, .bv y]
  · obtain ⟨x, y, rfl⟩ := hs
    exact hpos x y
  · have e : bool2T_khs f ts = .bot := by
      unfold bool2T_khs
      split
      · next a b =>
        split
        · next x y ha hb => exact (hs ⟨x, y, by rw [bvOf_some_khs ha, bvOf_some_khs hb]⟩).elim
        · rfl
      · rfl
    rw [e]
    refine hookOp_undef_khs fun c hc => ?_
    rw [hf, List.mem_singleton] at hc
    subst hc
    refine .intro fun σ _ hm => ?_
    rw [hp] at hm
    rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
    obtain ⟨t, ts', rfl, h2, h3⟩ := pv_cons_khs h1
    obtain ⟨u, ts'', rfl, h4, h5⟩ := pv_cons_khs h3
    obtain rfl := pv_nil_khs h5
    obtain ⟨x, rfl, -⟩ := pv_bv_khs h2
    obtain ⟨y, rfl, -⟩ := pv_bv_khs h4
    exact (hs ⟨x, y, rfl⟩).elim

/-- Two `tk` arguments. -/
theorem hookOp_str2_khs {o : Int} {cl : Clause} {f : List Char → List Char → Bool} {i j k l : Nat}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl])
    (hp : cl.pats = [.dv 3 (.int o),
      .app 407 [.app 443 [.var i, .var j], .app 407 [.app 443 [.var k, .var l], .app 406 []]]])
    (hpos : ∀ s x s' y, Eval c₀ 473 [.dv 3 (.int o), embTs [.tk s x, .tk s' y]]
      (some (emb (.bv (f x.toList y.toList))))) (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb (str2T_khs f ts))) := by
  by_cases hs : ∃ s x s' y, ts = [.tk s x, .tk s' y]
  · obtain ⟨s, x, s', y, rfl⟩ := hs
    exact hpos s x s' y
  · have e : str2T_khs f ts = .bot := by
      unfold str2T_khs
      split
      · next a b =>
        split
        · next x y ha hb =>
          obtain ⟨s, x', rfl, -⟩ := tkOf_some_khs ha
          obtain ⟨s', y', rfl, -⟩ := tkOf_some_khs hb
          exact (hs ⟨s, x', s', y', rfl⟩).elim
        · rfl
      · rfl
    rw [e]
    refine hookOp_undef_khs fun c hc => ?_
    rw [hf, List.mem_singleton] at hc
    subst hc
    refine .intro fun σ _ hm => ?_
    rw [hp] at hm
    rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
    obtain ⟨t, ts', rfl, h2, h3⟩ := pv_cons_khs h1
    obtain ⟨u, ts'', rfl, h4, h5⟩ := pv_cons_khs h3
    obtain rfl := pv_nil_khs h5
    obtain ⟨s, x, rfl⟩ := pv_tk_khs h2
    obtain ⟨s', y, rfl⟩ := pv_tk_khs h4
    exact (hs ⟨s, x, s', y, rfl⟩).elim

/-- Any two arguments. -/
theorem hookOp_any2_khs {o : Int} {cl : Clause} {F : List T → T} {i j : Nat}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl])
    (hp : cl.pats = [.dv 3 (.int o), .app 407 [.var i, .app 407 [.var j, .app 406 []]]])
    (hF : ∀ ts, (∀ a b, ts ≠ [a, b]) → F ts = .bot)
    (hpos : ∀ a b, Eval c₀ 473 [.dv 3 (.int o), embTs [a, b]] (some (emb (F [a, b])))) (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb (F ts))) := by
  by_cases hs : ∃ a b, ts = [a, b]
  · obtain ⟨a, b, rfl⟩ := hs
    exact hpos a b
  · rw [hF ts fun a b e => hs ⟨a, b, e⟩]
    refine hookOp_undef_khs fun c hc => ?_
    rw [hf, List.mem_singleton] at hc
    subst hc
    refine .intro fun σ _ hm => ?_
    rw [hp] at hm
    rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
    obtain ⟨t, ts', rfl, -, h3⟩ := pv_cons_khs h1
    obtain ⟨u, ts'', rfl, -, h5⟩ := pv_cons_khs h3
    obtain rfl := pv_nil_khs h5
    exact (hs ⟨t, u, rfl⟩).elim

/-- One `bv` argument. -/
theorem hookOp_not_khs {o : Int} {cl : Clause} {i : Nat}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl])
    (hp : cl.pats = [.dv 3 (.int o), .app 407 [.app 413 [.var i], .app 406 []]])
    (hpos : ∀ x, Eval c₀ 473 [.dv 3 (.int o), embTs [.bv x]] (some (emb (.bv !x)))) (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb (notT_khs ts))) := by
  by_cases hs : ∃ x, ts = [.bv x]
  · obtain ⟨x, rfl⟩ := hs
    exact hpos x
  · have e : notT_khs ts = .bot := by
      unfold notT_khs
      split
      · next a =>
        split
        · next x ha => exact (hs ⟨x, by rw [bvOf_some_khs ha]⟩).elim
        · rfl
      · rfl
    rw [e]
    refine hookOp_undef_khs fun c hc => ?_
    rw [hf, List.mem_singleton] at hc
    subst hc
    refine .intro fun σ _ hm => ?_
    rw [hp] at hm
    rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
    obtain ⟨t, ts', rfl, h2, h3⟩ := pv_cons_khs h1
    obtain rfl := pv_nil_khs h3
    obtain ⟨x, rfl, -⟩ := pv_bv_khs h2
    exact (hs ⟨x, rfl⟩).elim

/-- `bv(C) ; T ; E` as a pattern denotes a three-term list headed by a `bv` term. -/
theorem pv_ite_shape_khs {σ : Subst} {i j k : Nat} {ts : List T}
    (h : PatVal c₀ σ (.app 407 [.app 413 [.var i], .app 407 [.var j, .app 407 [.var k, .app 406 []]]]) (embTs ts)) :
    ∃ c t e, ts = [.bv c, t, e] := by
  obtain ⟨a, l₁, rfl, h2, h3⟩ := pv_cons_khs h
  obtain ⟨t, l₂, rfl, -, h5⟩ := pv_cons_khs h3
  obtain ⟨e, l₃, rfl, -, h7⟩ := pv_cons_khs h5
  obtain rfl := pv_nil_khs h7
  obtain ⟨c, rfl, -⟩ := pv_bv_khs h2
  exact ⟨c, t, e, rfl⟩

/-- `ite`'s code: `op-ite-then` and `op-ite-else` at a `bv` and two terms, `op-undef` otherwise. -/
theorem hookOp_ite_khs {o : Int} {cl₁ cl₂ : Clause} {i₁ j₁ k₁ i₂ j₂ k₂ : Nat}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl₁, cl₂])
    (hp₁ : cl₁.pats = [.dv 3 (.int o),
      .app 407 [.app 413 [.var i₁], .app 407 [.var j₁, .app 407 [.var k₁, .app 406 []]]]])
    (hp₂ : cl₂.pats = [.dv 3 (.int o),
      .app 407 [.app 413 [.var i₂], .app 407 [.var j₂, .app 407 [.var k₂, .app 406 []]]]])
    (hpos : ∀ c t e, Eval c₀ 473 [.dv 3 (.int o), embTs [.bv c, t, e]] (some (emb (if c then t else e))))
    (ts : List T) : Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb (iteT_khs ts))) := by
  by_cases hs : ∃ c t e, ts = [.bv c, t, e]
  · obtain ⟨c, t, e, rfl⟩ := hs
    exact hpos c t e
  · have e : iteT_khs ts = .bot := by
      unfold iteT_khs
      split
      · next c t e =>
        split
        · next b hc => exact (hs ⟨b, t, e, by rw [bvOf_some_khs hc]⟩).elim
        · rfl
      · rfl
    rw [e]
    refine hookOp_undef_khs fun c hc => ?_
    rw [hf] at hc
    refine .intro fun σ _ hm => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [hp₁] at hm
      rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
      exact (hs (pv_ite_shape_khs h1)).elim
    · rw [hp₂] at hm
      rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
      exact (hs (pv_ite_shape_khs h1)).elim

end Shapes

/-! ## `hookOp` at each code -/

section Codes
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms HooksS

/-- The `k`-th equation of `hookOp`. -/
theorem memOp_khs (k : Nat) (h : k < opCls.length := by decide) : opCls[k] ∈ opCls := List.getElem_mem h

theorem hookOp_low_khs : ∀ cl' ∈ hookOpDef.clauses, 50 ≤ cl'.prio := by decide +kernel

/-- An equation of `hookOp` of priority 50 decides where its patterns and `requires` hold. -/
theorem op_clause_khs {cl : Clause} {σ : Subst} {o : Int} {ts : List T} {r : T} (hm : cl ∈ opCls)
    (hσ : c₀.WellSorted cl.vars σ) (hp : PatVals c₀ σ cl.pats [.dv 3 (.int o), embTs ts])
    (hreq : ∀ t, cl.req = some t → EvalTerm c₀ σ t (some (bool true))) (hpr : cl.prio = 50)
    (hcl : cl.exs = [] ∧ cl.ens = none ∧ cl.pre = .top ∧ cl.post = .top)
    (hr : EvalTerm c₀ σ cl.rhs (some (emb r))) : Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb r)) :=
  clause_kht hookOpDef_lookup (List.mem_append_left _ hm) hσ hp hreq (by rw [hpr]; exact hookOp_low_khs) hcl hr

theorem pv_ivv_khs {σ : Subst} {i j : Nat} {o x y : Int} (hi : σ.lookup i = some (.dv 3 (.int x)))
    (hj : σ.lookup j = some (.dv 3 (.int y))) :
    PatVals c₀ σ [.dv 3 (.int o), .app 407 [.app 425 [.var i], .app 407 [.app 425 [.var j], .app 406 []]]]
      [.dv 3 (.int o), embTs [.iv x, .iv y]] :=
  .cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_425 (.cons (.var hi) .nil))
    (.cons (.ctor ctor_407 (.cons (.ctor ctor_425 (.cons (.var hj) .nil)) (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil)

theorem pv_bvv_khs {σ : Subst} {i j : Nat} {o : Int} {x y : Bool} (hi : σ.lookup i = some (.dv 2 (.bool x)))
    (hj : σ.lookup j = some (.dv 2 (.bool y))) :
    PatVals c₀ σ [.dv 3 (.int o), .app 407 [.app 413 [.var i], .app 407 [.app 413 [.var j], .app 406 []]]]
      [.dv 3 (.int o), embTs [.bv x, .bv y]] :=
  .cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_413 (.cons (.var hi) .nil))
    (.cons (.ctor ctor_407 (.cons (.ctor ctor_413 (.cons (.var hj) .nil)) (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil)

theorem pv_bv1_khs {σ : Subst} {i : Nat} {o : Int} {x : Bool} (hi : σ.lookup i = some (.dv 2 (.bool x))) :
    PatVals c₀ σ [.dv 3 (.int o), .app 407 [.app 413 [.var i], .app 406 []]] [.dv 3 (.int o), embTs [.bv x]] :=
  .cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_413 (.cons (.var hi) .nil)) (.cons (.ctor ctor_406 .nil) .nil))) .nil)

theorem pv_tkk_khs {σ : Subst} {i j k l : Nat} {o : Int} {s s' : Int} {x y : String}
    (hi : σ.lookup i = some (.dv 3 (.int s))) (hj : σ.lookup j = some (.dv 10 (.tok x)))
    (hk : σ.lookup k = some (.dv 3 (.int s'))) (hl : σ.lookup l = some (.dv 10 (.tok y))) :
    PatVals c₀ σ [.dv 3 (.int o),
      .app 407 [.app 443 [.var i, .var j], .app 407 [.app 443 [.var k, .var l], .app 406 []]]]
      [.dv 3 (.int o), embTs [.tk s x, .tk s' y]] :=
  .cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_443 (.cons (.var hi) (.cons (.var hj) .nil)))
    (.cons (.ctor ctor_407 (.cons (.ctor ctor_443 (.cons (.var hk) (.cons (.var hl) .nil)))
      (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil)

theorem pv_any2_khs {σ : Subst} {i j : Nat} {o : Int} {a b : T} (hi : σ.lookup i = some (emb a))
    (hj : σ.lookup j = some (emb b)) :
    PatVals c₀ σ [.dv 3 (.int o), .app 407 [.var i, .app 407 [.var j, .app 406 []]]] [.dv 3 (.int o), embTs [a, b]] :=
  .cons .dv (.cons (.ctor ctor_407 (.cons (.var hi) (.cons (.ctor ctor_407 (.cons (.var hj)
    (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil)

theorem pv_ite_khs {σ : Subst} {i j k : Nat} {o : Int} {c : Bool} {t e : T}
    (hi : σ.lookup i = some (.dv 2 (.bool c))) (hj : σ.lookup j = some (emb t)) (hk : σ.lookup k = some (emb e)) :
    PatVals c₀ σ [.dv 3 (.int o), .app 407 [.app 413 [.var i], .app 407 [.var j, .app 407 [.var k, .app 406 []]]]]
      [.dv 3 (.int o), embTs [.bv c, t, e]] :=
  .cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_413 (.cons (.var hi) .nil))
    (.cons (.ctor ctor_407 (.cons (.var hj) (.cons (.ctor ctor_407 (.cons (.var hk)
      (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))) .nil)

/-- Two Ints as the clause's two variables. -/
abbrev σ2_khs (x y : Int) : Subst := enumFrom 0 [.dv 3 (.int x), .dv 3 (.int y)]

theorem ws_ii_khs (x y : Int) : c₀.WellSorted [3, 3] (σ2_khs x y) :=
  ws_enum (.cons (sort_int x) (.cons (sort_int y) .nil))

/-- An Int operation that has a value at two Int literals, in an `iv(…)` right side. -/
theorem ev_ivop_khs {σ : Subst} {f : Sym} {i j : Nat} {x y z : Int} (hf : hook f [int x, int y] = some (some (int z)))
    (hi : σ.lookup i = some (.dv 3 (.int x))) (hj : σ.lookup j = some (.dv 3 (.int y)))
    (hc : c₀.isCtor f = false := by decide +kernel) (hh : isHook f = true := by decide +kernel) :
    EvalTerm c₀ σ (.app 425 [.app f [.var i, .var j]]) (some (emb (.iv z))) :=
  ev_ctor (.cons (ev_hook2_khs hf (ev_var hi) (ev_var hj) hc hh) .nil) ctor_425

/-- A test that has a value at two literals, in a `bv(…)` right side. -/
theorem ev_bvop_khs {σ : Subst} {f : Sym} {i j : Nat} {va vb : GroundTerm} {z : Bool}
    (hf : hook f [va, vb] = some (some (bool z)))
    (hi : σ.lookup i = some va) (hj : σ.lookup j = some vb)
    (hc : c₀.isCtor f = false := by decide +kernel) (hh : isHook f = true := by decide +kernel) :
    EvalTerm c₀ σ (.app 413 [.app f [.var i, .var j]]) (some (emb (.bv z))) :=
  ev_ctor (.cons (ev_hook2_khs hf (ev_var hi) (ev_var hj) hc hh) .nil) ctor_413

theorem hookOp_add_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 1), embTs ts] (some (emb (int2T_khs (fun x y => .iv (x + y)) ts))) :=
  hookOp_int2_khs (cl := opAdd) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs x y) (memOp_khs 0 : opAdd ∈ opCls)
    (ws_ii_khs x y) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_ivop_khs rfl rfl rfl)) ts

theorem hookOp_sub_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 2), embTs ts] (some (emb (int2T_khs (fun x y => .iv (x - y)) ts))) :=
  hookOp_int2_khs (cl := opSub) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs y x) (memOp_khs 7 : opSub ∈ opCls)
    (ws_ii_khs y x) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_ivop_khs rfl rfl rfl)) ts

theorem hookOp_mul_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 3), embTs ts] (some (emb (int2T_khs (fun x y => .iv (x * y)) ts))) :=
  hookOp_int2_khs (cl := opMul) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs x y) (memOp_khs 12 : opMul ∈ opCls)
    (ws_ii_khs x y) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_ivop_khs rfl rfl rfl)) ts

/-- `X =/=Int 0` at an Int value. -/
theorem ev_nz_khs {σ : Subst} {i : Nat} {y : Int} (hi : σ.lookup i = some (.dv 3 (.int y))) :
    EvalTerm c₀ σ (.app 24 [.var i, .dv 3 (.int 0)]) (some (bool (decide (y ≠ 0)))) :=
  ev_int2 (P := (· ≠ ·)) hook_intNe (ev_var hi) (.dv (lit := .int 0))

/-- An equation of an `iv ; iv` code whose `requires` is `Y =/=Int 0`, with `Y` its `j`-th pattern
variable bound to the second argument, fails where the second argument is `iv(0)`. -/
theorem fails_nz_khs {cl : Clause} {o x : Int} {i j : Nat}
    (hp : cl.pats = [.dv 3 (.int o), .app 407 [.app 425 [.var i], .app 407 [.app 425 [.var j], .app 406 []]]])
    (hr : cl.req = some (.app 24 [.var j, .dv 3 (.int 0)])) :
    Fails c₀ [.dv 3 (.int o), embTs [.iv x, .iv 0]] cl := by
  refine .intro fun σ _ hm => ?_
  rw [hp] at hm
  rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
  obtain ⟨t, l₁, e₁, -, h3⟩ := pv_cons_khs h1
  cases e₁
  obtain ⟨u, l₂, e₂, h4, -⟩ := pv_cons_khs h3
  cases e₂
  obtain ⟨y, e, hl⟩ := pv_iv_khs h4
  cases e
  exact .intro hr (ev_nz_khs hl) (by decide)

theorem hookOp_div_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 4), embTs ts]
      (some (emb (int2T_khs (fun x y => if y = 0 then .bot else .iv (x.tdiv y)) ts))) := by
  refine hookOp_int2_khs (cl := opDiv) rfl rfl (fun x y => ?_) ts
  by_cases hy : y = 0
  · rw [ite_pos hy]
    subst hy
    refine hookOp_undef_khs fun c hc => ?_
    rw [show opCls.filter (fun c => codeOf c == some 4) = [opDiv] from rfl, List.mem_singleton] at hc
    subst hc
    exact fails_nz_khs rfl rfl
  · rw [ite_neg hy]
    refine op_clause_khs (σ := σ2_khs y x) (memOp_khs 15 : opDiv ∈ opCls) (ws_ii_khs y x) (pv_ivv_khs rfl rfl)
      (fun _ h => by cases h; have := ev_nz_khs (σ := σ2_khs y x) (i := 0) rfl; rwa [decide_eq_true hy] at this)
      rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_ivop_khs ?_ rfl rfl)
    rw [show hook 15 [int x, int y] = some (nonzero y (x.tdiv y)) from rfl, nonzero, ite_neg hy]

theorem hookOp_mod_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 5), embTs ts]
      (some (emb (int2T_khs (fun x y => if y = 0 then .bot else .iv (x.tmod y)) ts))) := by
  refine hookOp_int2_khs (cl := opMod) rfl rfl (fun x y => ?_) ts
  by_cases hy : y = 0
  · rw [ite_pos hy]
    subst hy
    refine hookOp_undef_khs fun c hc => ?_
    rw [show opCls.filter (fun c => codeOf c == some 5) = [opMod] from rfl, List.mem_singleton] at hc
    subst hc
    exact fails_nz_khs rfl rfl
  · rw [ite_neg hy]
    refine op_clause_khs (σ := σ2_khs x y) (memOp_khs 22 : opMod ∈ opCls) (ws_ii_khs x y) (pv_ivv_khs rfl rfl)
      (fun _ h => by cases h; have := ev_nz_khs (σ := σ2_khs x y) (i := 1) rfl; rwa [decide_eq_true hy] at this)
      rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_ivop_khs ?_ rfl rfl)
    rw [show hook 16 [int x, int y] = some (nonzero y (x.tmod y)) from rfl, nonzero, ite_neg hy]

theorem hookOp_lt_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 10), embTs ts] (some (emb (int2T_khs (fun x y => .bv (decide (x < y))) ts))) :=
  hookOp_int2_khs (cl := opLt) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs y x) (memOp_khs 1 : opLt ∈ opCls)
    (ws_ii_khs y x) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_le_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 11), embTs ts] (some (emb (int2T_khs (fun x y => .bv (decide (x ≤ y))) ts))) :=
  hookOp_int2_khs (cl := opLe) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs x y) (memOp_khs 2 : opLe ∈ opCls)
    (ws_ii_khs x y) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_gt_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 12), embTs ts] (some (emb (int2T_khs (fun x y => .bv (decide (x > y))) ts))) :=
  hookOp_int2_khs (cl := opGt) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs x y) (memOp_khs 3 : opGt ∈ opCls)
    (ws_ii_khs x y) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_ge_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 13), embTs ts] (some (emb (int2T_khs (fun x y => .bv (decide (x ≥ y))) ts))) :=
  hookOp_int2_khs (cl := opGe) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs x y) (memOp_khs 4 : opGe ∈ opCls)
    (ws_ii_khs x y) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_eq_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 14), embTs ts] (some (emb (int2T_khs (fun x y => .bv (decide (x = y))) ts))) :=
  hookOp_int2_khs (cl := opEq) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs x y) (memOp_khs 5 : opEq ∈ opCls)
    (ws_ii_khs x y) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_ne_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 15), embTs ts] (some (emb (int2T_khs (fun x y => .bv (decide (x ≠ y))) ts))) :=
  hookOp_int2_khs (cl := opNe) rfl rfl (fun x y => op_clause_khs (σ := σ2_khs x y) (memOp_khs 6 : opNe ∈ opCls)
    (ws_ii_khs x y) (pv_ivv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

/-- Two Bools as the clause's two variables. -/
abbrev σb_khs (x y : Bool) : Subst := enumFrom 0 [.dv 2 (.bool x), .dv 2 (.bool y)]

theorem ws_bb_khs (x y : Bool) : c₀.WellSorted [2, 2] (σb_khs x y) :=
  ws_enum (.cons (sort_bool x) (.cons (sort_bool y) .nil))

theorem hookOp_and_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 20), embTs ts] (some (emb (bool2T_khs (· && ·) ts))) :=
  hookOp_bool2_khs (cl := opAnd) rfl rfl (fun x y => op_clause_khs (σ := σb_khs x y) (memOp_khs 8 : opAnd ∈ opCls)
    (ws_bb_khs x y) (pv_bvv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_or_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 21), embTs ts] (some (emb (bool2T_khs (· || ·) ts))) :=
  hookOp_bool2_khs (cl := opOr) rfl rfl (fun x y => op_clause_khs (σ := σb_khs x y) (memOp_khs 9 : opOr ∈ opCls)
    (ws_bb_khs x y) (pv_bvv_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_boolEq_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 23), embTs ts] (some (emb (bool2T_khs (· == ·) ts))) :=
  hookOp_bool2_khs (cl := opBoolEq) rfl rfl (fun x y => op_clause_khs (σ := σb_khs x y)
    (memOp_khs 11 : opBoolEq ∈ opCls) (ws_bb_khs x y) (pv_bvv_khs rfl rfl) (fun _ h => by cases h) rfl
    ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_not_code_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 22), embTs ts] (some (emb (notT_khs ts))) :=
  hookOp_not_khs (cl := opNot) rfl rfl (fun x => op_clause_khs (σ := enumFrom 0 [.dv 2 (.bool x)])
    (memOp_khs 10 : opNot ∈ opCls) (ws_enum (.cons (sort_bool x) .nil)) (pv_bv1_khs rfl) (fun _ h => by cases h)
    rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_hook1_khs rfl (ev_var rfl)) .nil) ctor_413)) ts

theorem hookOp_ite_code_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 30), embTs ts] (some (emb (iteT_khs ts))) := by
  refine hookOp_ite_khs (cl₁ := opIteThen) (cl₂ := opIteElse) rfl rfl rfl (fun c t e => ?_) ts
  cases c with
  | true =>
    rw [ite_pos rfl]
    exact op_clause_khs (σ := enumFrom 0 [.dv 2 (.bool true), emb t, emb e]) (memOp_khs 13 : opIteThen ∈ opCls)
      (ws_enum (.cons (sort_bool true) (.cons (emb_sorted_c₀ t) (.cons (emb_sorted_c₀ e) .nil))))
      (pv_ite_khs rfl rfl rfl) (fun _ h => by cases h; exact ev_var rfl) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | false =>
    rw [ite_neg (by decide)]
    exact op_clause_khs (σ := enumFrom 0 [emb e, .dv 2 (.bool false), emb t]) (memOp_khs 14 : opIteElse ∈ opCls)
      (ws_enum (.cons (emb_sorted_c₀ e) (.cons (sort_bool false) (.cons (emb_sorted_c₀ t) .nil))))
      (pv_ite_khs rfl rfl rfl) (fun _ h => by cases h; exact ev_hook1_khs rfl (ev_var rfl)) rfl
      ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)

theorem keqT_bot_khs (ts : List T) (h : ∀ a b, ts ≠ [a, b]) : keqT_khs ts = .bot := by
  unfold keqT_khs
  split
  · next a b => exact absurd rfl (h a b)
  · rfl

theorem kneT_bot_khs (ts : List T) (h : ∀ a b, ts ≠ [a, b]) : kneT_khs ts = .bot := by
  unfold kneT_khs
  split
  · next a b => exact absurd rfl (h a b)
  · rfl

theorem hookOp_keq_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 70), embTs ts] (some (emb (keqT_khs ts))) :=
  hookOp_any2_khs (cl := opKeq) rfl rfl keqT_bot_khs (fun a b => op_clause_khs (σ := enumFrom 0 [emb b, emb a])
    (memOp_khs 27 : opKeq ∈ opCls) (ws_enum (.cons (emb_sorted_c₀ b) (.cons (emb_sorted_c₀ a) .nil)))
    (pv_any2_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_hook2_khs rfl (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (cmpF.eval a b)
      notCtor_456 notHook_456 notParam_456) .dv) .nil) ctor_413)) ts

theorem hookOp_kne_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 71), embTs ts] (some (emb (kneT_khs ts))) :=
  hookOp_any2_khs (cl := opKne) rfl rfl kneT_bot_khs (fun a b => op_clause_khs (σ := enumFrom 0 [emb a, emb b])
    (memOp_khs 28 : opKne ∈ opCls) (ws_enum (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ b) .nil)))
    (pv_any2_khs rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_hook2_khs rfl (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (cmpF.eval a b)
      notCtor_456 notHook_456 notParam_456) .dv) .nil) ctor_413)) ts

theorem hookOp_strEq_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 80), embTs ts] (some (emb (str2T_khs (fun x y => x == y) ts))) :=
  hookOp_str2_khs (cl := opStrEq) rfl rfl (fun s x s' y => op_clause_khs
    (σ := enumFrom 0 [.dv 3 (.int s), .dv 10 (.tok x), .dv 3 (.int s'), .dv 10 (.tok y)])
    (memOp_khs 29 : opStrEq ∈ opCls)
    (ws_enum (.cons (sort_int s) (.cons (sort_string_kemb x) (.cons (sort_int s') (.cons (sort_string_kemb y) .nil)))))
    (pv_tkk_khs rfl rfl rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

theorem hookOp_strLt_khs (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 81), embTs ts] (some (emb (str2T_khs KStr.lexLt ts))) :=
  hookOp_str2_khs (cl := opStrLt) rfl rfl (fun s x s' y => op_clause_khs
    (σ := enumFrom 0 [.dv 3 (.int s'), .dv 10 (.tok y), .dv 3 (.int s), .dv 10 (.tok x)])
    (memOp_khs 30 : opStrLt ∈ opCls)
    (ws_enum (.cons (sort_int s') (.cons (sort_string_kemb y) (.cons (sort_int s) (.cons (sort_string_kemb x) .nil)))))
    (pv_tkk_khs rfl rfl rfl rfl) (fun _ h => by cases h) rfl ⟨rfl, rfl, rfl, rfl⟩ (ev_bvop_khs rfl rfl rfl)) ts

end Codes

/-! ## KCore's side: the hooks at the encodings -/

section Obj
open KCore.Det
open _root_.KK.Kit (ite_pos ite_neg)

theorem hook_add_khs (vs : List GroundTerm) : hook intAdd vs = some (int2 vs fun x y => some (int (x + y))) := rfl
theorem hook_sub_khs (vs : List GroundTerm) : hook intSub vs = some (int2 vs fun x y => some (int (x - y))) := rfl
theorem hook_mul_khs (vs : List GroundTerm) : hook intMul vs = some (int2 vs fun x y => some (int (x * y))) := rfl
theorem hook_tdiv_khs (vs : List GroundTerm) : hook intTDiv vs = some (int2 vs fun x y => nonzero y (x.tdiv y)) := rfl
theorem hook_tmod_khs (vs : List GroundTerm) : hook intTMod vs = some (int2 vs fun x y => nonzero y (x.tmod y)) := rfl
theorem hook_and_khs (vs : List GroundTerm) : hook boolAnd vs = some (bool2 vs (· && ·)) := rfl
theorem hook_boolEq_khs (vs : List GroundTerm) : hook boolEq vs = some (bool2 vs (· == ·)) := rfl
theorem hook_boolNe_khs (vs : List GroundTerm) : hook boolNe vs = some (bool2 vs (· != ·)) := rfl
theorem hook_not_khs (vs : List GroundTerm) :
    hook boolNot vs = some (match vs with | [a] => (asBool a).map fun x => bool !x | _ => none) := rfl
theorem hook_ite_khs (vs : List GroundTerm) :
    hook kIte vs = some (match vs with | [c, x, y] => (asBool c).map fun b => if b then x else y | _ => none) := rfl
theorem hook_kEq_khs (vs : List GroundTerm) :
    hook kEq vs = some (match vs with | [a, b] => some (bool (GroundTerm.cmp a b == .eq)) | _ => none) := rfl
theorem hook_kNe_khs (vs : List GroundTerm) :
    hook kNe vs = some (match vs with | [a, b] => some (bool (GroundTerm.cmp a b != .eq)) | _ => none) := rfl
theorem hook_strEq_khs (vs : List GroundTerm) : hook stringEq vs = some (str2 vs fun x y => x == y) := rfl
theorem hook_strLt_khs (vs : List GroundTerm) : hook stringLt vs = some (str2 vs KStr.lexLt) := rfl

/-- `enc` writes `iv` exactly at an Int literal of sort `Int`, the literals `asInt` reads. -/
theorem ivOf_enc_khs (v : GroundTerm) : ivOf_khs (enc v) = asInt v := by
  cases v with
  | dv s l =>
    cases l with
    | int i =>
      by_cases hs : s = Srt.int
      · subst hs; simp only [enc]; rfl
      · rw [enc.eq_6] <;> simp_all [ivOf_khs, asInt]
    | bool b =>
      by_cases hs : s = Srt.bool
      · subst hs; simp only [enc]; rfl
      · rw [enc.eq_6] <;> simp_all [ivOf_khs, asInt]
    | tok x => simp only [enc]; rfl
    | float p e b => rw [enc.eq_6] <;> simp_all [ivOf_khs, asInt]
  | ctor f vs => simp only [enc]; rfl
  | inj a b w => simp only [enc]; rfl
  | map s es => simp only [enc]; rfl
  | set s es => simp only [enc]; rfl
  | list s es => simp only [enc]; rfl

/-- `enc` writes `bv` exactly at a Bool literal of sort `Bool`, the literals `asBool` reads. -/
theorem bvOf_enc_khs (v : GroundTerm) : bvOf_khs (enc v) = asBool v := by
  cases v with
  | dv s l =>
    cases l with
    | int i =>
      by_cases hs : s = Srt.int
      · subst hs; simp only [enc]; rfl
      · rw [enc.eq_6] <;> simp_all [bvOf_khs, asBool]
    | bool b =>
      by_cases hs : s = Srt.bool
      · subst hs; simp only [enc]; rfl
      · rw [enc.eq_6] <;> simp_all [bvOf_khs, asBool]
    | tok x => simp only [enc]; rfl
    | float p e b => rw [enc.eq_6] <;> simp_all [bvOf_khs, asBool]
  | ctor f vs => simp only [enc]; rfl
  | inj a b w => simp only [enc]; rfl
  | map s es => simp only [enc]; rfl
  | set s es => simp only [enc]; rfl
  | list s es => simp only [enc]; rfl

/-- At a value none of whose token literals has a sort other than `String`, `enc` writes `tk`
exactly at a String literal, the literals `asStr` reads. -/
theorem tkOf_enc_khs {v : GroundTerm} (hv : ∀ s x, v = .dv s (.tok x) → s = Srt.string) :
    tkOf_khs (enc v) = asStr v := by
  cases v with
  | dv s l =>
    cases l with
    | int i =>
      clear hv
      by_cases hs : s = Srt.int
      · subst hs; simp only [enc]; rfl
      · rw [enc.eq_6] <;> simp_all [tkOf_khs, asStr]
    | bool b =>
      clear hv
      by_cases hs : s = Srt.bool
      · subst hs; simp only [enc]; rfl
      · rw [enc.eq_6] <;> simp_all [tkOf_khs, asStr]
    | tok x => obtain rfl := hv s x rfl; simp only [enc]; rfl
    | float p e b => clear hv; rw [enc.eq_6] <;> simp_all [tkOf_khs, asStr]
  | ctor f vs => simp only [enc]; rfl
  | inj a b w => simp only [enc]; rfl
  | map s es => simp only [enc]; rfl
  | set s es => simp only [enc]; rfl
  | list s es => simp only [enc]; rfl

theorem int2T_enc_khs (f : Int → Int → T) (g : Int → Int → Option GroundTerm) (hfg : ∀ x y, f x y = encR (g x y)) :
    ∀ vs, int2T_khs f (encTs vs) = encR (int2 vs g)
  | [a, b] => by
    simp only [encTs, int2T_khs, int2, ivOf_enc_khs]
    cases asInt a <;> cases asInt b <;> simp [hfg, encR]
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ :: _ => rfl

theorem bool2T_enc_khs (f : Bool → Bool → Bool) : ∀ vs, bool2T_khs f (encTs vs) = encR (bool2 vs f)
  | [a, b] => by
    simp only [encTs, bool2T_khs, bool2, bvOf_enc_khs]
    cases asBool a <;> cases asBool b <;> rfl
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ :: _ => rfl

theorem str2T_enc_khs (f : List Char → List Char → Bool) :
    ∀ vs, (∀ v ∈ vs, ∀ s x, v = .dv s (.tok x) → s = Srt.string) → str2T_khs f (encTs vs) = encR (str2 vs f)
  | [a, b], hv => by
    simp only [encTs, str2T_khs, str2, tkOf_enc_khs (hv a (by simp)), tkOf_enc_khs (hv b (by simp))]
    cases asStr a <;> cases asStr b <;> rfl
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _ :: _, _ => rfl

theorem obj_not_khs : ∀ vs, notT_khs (encTs vs) = encR (hook boolNot vs).join
  | [a] => by
    rw [hook_not_khs]
    simp only [encTs, notT_khs, bvOf_enc_khs, Option.join_some]
    cases asBool a <;> rfl
  | [] => rfl
  | _ :: _ :: _ => rfl

theorem obj_ite_khs : ∀ vs, iteT_khs (encTs vs) = encR (hook kIte vs).join
  | [c, x, y] => by
    rw [hook_ite_khs]
    simp only [encTs, iteT_khs, bvOf_enc_khs, Option.join_some]
    cases asBool c with
    | none => rfl
    | some b => cases b <;> rfl
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ :: _ => rfl

theorem obj_keq_khs {c : Semantics} :
    ∀ vs, (∀ v ∈ vs, ∃ s, c.sortOf v = some s) → (∀ v ∈ vs, litsV v = true) →
      keqT_khs (encTs vs) = encR (hook kEq vs).join
  | [a, b], hs, hl => by
    obtain ⟨s, ha⟩ := hs a (by simp)
    obtain ⟨s', hb⟩ := hs b (by simp)
    have la := hl a (by simp)
    have lb := hl b (by simp)
    rw [hook_kEq_khs]
    show T.bv (decide (cmpF (enc a) (enc b) = 0)) = enc (bool (GroundTerm.cmp a b == .eq))
    by_cases h : a = b
    · subst h
      rw [decide_eq_true ((cmpF_eq_zero_iff ha ha la la).mpr rfl), cmp_eq_iff.mpr rfl]
      rfl
    · rw [decide_eq_false (fun h' => h ((cmpF_eq_zero_iff ha hb la lb).mp h'))]
      cases hc : GroundTerm.cmp a b with
      | eq => exact (h (cmp_eq_iff.mp hc)).elim
      | lt => rfl
      | gt => rfl
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _ :: _, _, _ => rfl

theorem obj_kne_khs {c : Semantics} :
    ∀ vs, (∀ v ∈ vs, ∃ s, c.sortOf v = some s) → (∀ v ∈ vs, litsV v = true) →
      kneT_khs (encTs vs) = encR (hook kNe vs).join
  | [a, b], hs, hl => by
    obtain ⟨s, ha⟩ := hs a (by simp)
    obtain ⟨s', hb⟩ := hs b (by simp)
    have la := hl a (by simp)
    have lb := hl b (by simp)
    rw [hook_kNe_khs]
    show T.bv (decide (cmpF (enc a) (enc b) ≠ 0)) = enc (bool (GroundTerm.cmp a b != .eq))
    by_cases h : a = b
    · subst h
      rw [decide_eq_false (fun h' => h' ((cmpF_eq_zero_iff ha ha la la).mpr rfl)), cmp_eq_iff.mpr rfl]
      rfl
    · rw [decide_eq_true (show cmpF (enc a) (enc b) ≠ 0 from fun h' => h ((cmpF_eq_zero_iff ha hb la lb).mp h'))]
      cases hc : GroundTerm.cmp a b with
      | eq => exact (h (cmp_eq_iff.mp hc)).elim
      | lt => rfl
      | gt => rfl
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _ :: _, _, _ => rfl

/-- `hook-bot` changes nothing where `hookOp` is already `bot` at a list holding `bot`. -/
theorem strictT_of_khs {ts : List T} {r : T} (h : hasBotF ts = true → r = .bot) : strictT_khs ts r = r := by
  unfold strictT_khs
  cases e : hasBotF ts with
  | false => rfl
  | true => exact (h e).symm

theorem int2T_bot_khs (f : Int → Int → T) {ts : List T} (h : hasBotF ts = true) : int2T_khs f ts = .bot := by
  unfold int2T_khs
  split
  · split
    · next x y ha hb =>
      rw [ivOf_some_khs ha, ivOf_some_khs hb] at h
      simp [hasBotF] at h
    · rfl
  · rfl

theorem bool2T_bot_khs (f : Bool → Bool → Bool) {ts : List T} (h : hasBotF ts = true) : bool2T_khs f ts = .bot := by
  unfold bool2T_khs
  split
  · split
    · next x y ha hb =>
      rw [bvOf_some_khs ha, bvOf_some_khs hb] at h
      simp [hasBotF] at h
    · rfl
  · rfl

theorem notT_bot_khs {ts : List T} (h : hasBotF ts = true) : notT_khs ts = .bot := by
  unfold notT_khs
  split
  · split
    · next x ha =>
      rw [bvOf_some_khs ha] at h
      simp [hasBotF] at h
    · rfl
  · rfl

theorem str2T_bot_khs (f : List Char → List Char → Bool) {ts : List T} (h : hasBotF ts = true) :
    str2T_khs f ts = .bot := by
  unfold str2T_khs
  split
  · split
    · next x y ha hb =>
      obtain ⟨s, x', rfl, -⟩ := tkOf_some_khs ha
      obtain ⟨s', y', rfl, -⟩ := tkOf_some_khs hb
      simp [hasBotF] at h
    · rfl
  · rfl

/-- The encodings of values whose literals have a kore.k form hold no `bot` at the top. -/
theorem hasBotF_encTs_khs {vs : List GroundTerm} (h : ∀ v ∈ vs, litsV v = true) : hasBotF (encTs vs) = false :=
  hasBotF_false_khs fun t ht e => by
    rw [encTs_eq_map] at ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    have hn := enc_ne_bot (h v hv)
    rw [e] at hn
    exact hn

end Obj

/-! ## `strictHook` at each code -/

section Scalar
open KCore.Det _root_.KK
open _root_.KK.Kit (ite_pos ite_neg)

/-- kore.k's side and KCore's side meet: `hookRes` is `hook` off the keys of `silentTable`. -/
theorem scalar_of_khs {d : Semantics} {f : Sym} {o : Int} {vs : List GroundTerm} {r : T}
    (hk : silentKey f = false)
    (hop : hasBotF (encTs vs) = false → Eval c₀ 473 [.dv 3 (.int o), embTs (encTs vs)] (some (emb r)))
    (hr : strictT_khs (encTs vs) r = encR (hook f vs).join) :
    Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes f vs).join))) := by
  rw [Semantics.hookRes_of_notKey hk, ← hr]
  exact strictHook_eval_khs o (encTs vs) hop

theorem nonzero_enc_khs (r : Int → Int → Int) (x y : Int) :
    (if y = 0 then T.bot else .iv (r x y)) = encR (nonzero y (r x y)) := by
  unfold nonzero
  by_cases hy : y = 0
  · rw [ite_pos hy, ite_pos hy]; rfl
  · rw [ite_neg hy, ite_neg hy]; rfl

/-- `+Int` (code 1), at every argument list. -/
theorem hooks_scalar_add {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 1), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intAdd vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_add_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_add_khs]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `-Int` (code 2), at every argument list. -/
theorem hooks_scalar_sub {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 2), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intSub vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_sub_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_sub_khs]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `*Int` (code 3), at every argument list. -/
theorem hooks_scalar_mul {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 3), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intMul vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_mul_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_mul_khs]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `/Int` (code 4), at every argument list: `bot` by zero on both sides. -/
theorem hooks_scalar_div {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 4), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intTDiv vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_div_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_tdiv_khs]
    exact int2T_enc_khs _ _ (fun x y => nonzero_enc_khs Int.tdiv x y) vs)

/-- `%Int` (code 5), at every argument list: `bot` by zero on both sides. -/
theorem hooks_scalar_mod {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 5), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intTMod vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_mod_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_tmod_khs]
    exact int2T_enc_khs _ _ (fun x y => nonzero_enc_khs Int.tmod x y) vs)

/-- `<Int` (code 10), at every argument list. -/
theorem hooks_scalar_lt {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 10), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intLt vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_lt_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_intLt]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `<=Int` (code 11), at every argument list. -/
theorem hooks_scalar_le {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 11), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intLe vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_le_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_intLe]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `>Int` (code 12), at every argument list. -/
theorem hooks_scalar_gt {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 12), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intGt vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_gt_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_intGt]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `>=Int` (code 13), at every argument list. -/
theorem hooks_scalar_ge {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 13), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intGe vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_ge_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_intGe]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `==Int` (code 14), at every argument list. -/
theorem hooks_scalar_eq {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 14), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intEq vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_eq_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_intEq]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `=/=Int` (code 15), at every argument list. -/
theorem hooks_scalar_ne {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 15), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes intNe vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_ne_khs _) (by
    rw [strictT_of_khs (int2T_bot_khs _), hook_intNe]; exact int2T_enc_khs _ _ (by intros; rfl) vs)

/-- `andBool` (code 20), at every argument list. -/
theorem hooks_scalar_and {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 20), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes boolAnd vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_and_khs _) (by
    rw [strictT_of_khs (bool2T_bot_khs _), hook_and_khs]; exact bool2T_enc_khs _ vs)

/-- `orBool` (code 21), at every argument list. -/
theorem hooks_scalar_or {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 21), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes boolOr vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_or_khs _) (by
    rw [strictT_of_khs (bool2T_bot_khs _), hook_or]; exact bool2T_enc_khs _ vs)

/-- `notBool` (code 22), at every argument list. -/
theorem hooks_scalar_not {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 22), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes boolNot vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_not_code_khs _) (by
    rw [strictT_of_khs notT_bot_khs]; exact obj_not_khs vs)

/-- `==Bool` (code 23), at every argument list. -/
theorem hooks_scalar_boolEq {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 23), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes boolEq vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_boolEq_khs _) (by
    rw [strictT_of_khs (bool2T_bot_khs _), hook_boolEq_khs]; exact bool2T_enc_khs _ vs)

/-- `ite` (code 30), at arguments whose literals have a kore.k form. -/
theorem hooks_scalar_ite {d : Semantics} (vs : List GroundTerm) (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 30), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes kIte vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_ite_code_khs _) (by
    rw [strictT_of_khs (fun h => by rw [hasBotF_encTs_khs hl] at h; cases h)]; exact obj_ite_khs vs)

/-- `==K` (code 70), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_scalar_keq {d : Semantics} (vs : List GroundTerm) (hs : ∀ v ∈ vs, ∃ s, (d₀ d).sortOf v = some s)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 70), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes kEq vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_keq_khs _) (by
    rw [strictT_of_khs (fun h => by rw [hasBotF_encTs_khs hl] at h; cases h)]; exact obj_keq_khs vs hs hl)

/-- `=/=K` (code 71), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_scalar_kne {d : Semantics} (vs : List GroundTerm) (hs : ∀ v ∈ vs, ∃ s, (d₀ d).sortOf v = some s)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 71), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes kNe vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_kne_khs _) (by
    rw [strictT_of_khs (fun h => by rw [hasBotF_encTs_khs hl] at h; cases h)]; exact obj_kne_khs vs hs hl)

/-- A value of sort `String` that is a token literal is one of sort `String`. -/
theorem tok_string_khs {c : Semantics} {v : GroundTerm} (hv : c.sortOf v = some Srt.string) :
    ∀ s x, v = .dv s (.tok x) → s = Srt.string := by
  rintro s x rfl
  exact (sortOf_dv.mp hv).2.symm

/-- `==String` (code 80), at arguments sorted at `String`. -/
theorem hooks_scalar_strEq {d : Semantics} (vs : List GroundTerm)
    (hs : ∀ v ∈ vs, (d₀ d).sortOf v = some Srt.string) :
    Eval (K₀ sig) 508 [.dv 3 (.int 80), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes stringEq vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_strEq_khs _) (by
    rw [strictT_of_khs (str2T_bot_khs _), hook_strEq_khs]
    exact str2T_enc_khs _ vs fun v hv => tok_string_khs (hs v hv))

/-- `<String` (code 81), at arguments sorted at `String`. -/
theorem hooks_scalar_strLt {d : Semantics} (vs : List GroundTerm)
    (hs : ∀ v ∈ vs, (d₀ d).sortOf v = some Srt.string) :
    Eval (K₀ sig) 508 [.dv 3 (.int 81), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes stringLt vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_strLt_khs _) (by
    rw [strictT_of_khs (str2T_bot_khs _), hook_strLt_khs]
    exact str2T_enc_khs _ vs fun v hv => tok_string_khs (hs v hv))

end Scalar

/-! ## `=/=Bool`: `notBool (B1 ==Bool B2)` -/

section BoolNe
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts

/-- KCore's `=/=Bool` is `notBool` of its `==Bool`, at every argument list: both undefined where
`==Bool` is. -/
theorem boolNe_comp (vs : List GroundTerm) :
    (hook boolNe vs).join = (hook boolEq vs).join.bind fun v => (hook boolNot [v]).join := by
  rw [hook_boolNe_khs, hook_boolEq_khs]
  match vs with
  | [a, b] =>
    simp only [Option.join_some, bool2]
    cases asBool a <;> cases asBool b <;> rfl
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- `hk 22 [hk 23 As]` at the encoded arguments: code 23 gives the encoding of `==Bool`'s result,
and code 22 at that term the encoding of `=/=Bool`'s, for every argument list. -/
theorem boolNe_hook {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 23), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes boolEq vs).join))) ∧
    Eval (K₀ sig) 508 [.dv 3 (.int 22), embTs [encR ((d₀ d).hookRes boolEq vs).join]]
      (some (emb (encR ((d₀ d).hookRes boolNe vs).join))) := by
  refine ⟨hooks_scalar_boolEq vs, ?_⟩
  rw [Semantics.hookRes_of_notKey (f := boolEq) (by decide), Semantics.hookRes_of_notKey (f := boolNe) (by decide),
    boolNe_comp]
  have h22 := strictHook_eval_khs 22 [encR (hook boolEq vs).join] (fun _ => hookOp_not_code_khs _)
  rw [strictT_of_khs notT_bot_khs] at h22
  have e : notT_khs [encR (hook boolEq vs).join] =
      encR ((hook boolEq vs).join.bind fun v => (hook boolNot [v]).join) := by
    cases (hook boolEq vs).join with
    | none => rfl
    | some v => exact obj_not_khs [v]
  rw [e] at h22
  exact h22

/-- The term `strictHook(22, strictHook(23, As) ; .Ts)`, with `As` bound to the encoded arguments,
evaluates at `K₀ sig` to the encoding of `=/=Bool`'s result. -/
theorem boolNe_term {d : Semantics} (vs : List GroundTerm) {σ : Subst} {i : Nat}
    (hi : σ.lookup i = some (embTs (encTs vs))) :
    EvalTerm (K₀ sig) σ (.app 508 [.dv 3 (.int 22), .app 407 [.app 508 [.dv 3 (.int 23), .var i], .app 406 []]])
      (some (emb (encR ((d₀ d).hookRes boolNe vs).join))) :=
  ev_call (.cons .dv (.cons (ev_ctor (.cons (ev_call (.cons .dv (.cons (ev_var hi) .nil)) (boolNe_hook (d := d) vs).1
      notCtor_508 notHook_508 notParam_508) (.cons (ev_ctor .nil ctor_406) .nil)) ctor_407) .nil))
    (boolNe_hook vs).2 notCtor_508 notHook_508 notParam_508

end BoolNe

/-! ## Every scalar code -/

section Uniform
open KCore.Det _root_.KK

/-- The codes of `hookCodes` this module covers: those below the collections' and from K equality on. -/
def scalarCodes_khs : List (Sym × Int) := hookCodes.filter fun p => p.2 < 40 || 70 ≤ p.2

theorem scalarCodes_eq_khs : scalarCodes_khs =
    [(intAdd, 1), (intSub, 2), (intMul, 3), (intTDiv, 4), (intTMod, 5),
     (intLt, 10), (intLe, 11), (intGt, 12), (intGe, 13), (intEq, 14), (intNe, 15),
     (boolAnd, 20), (boolOr, 21), (boolNot, 22), (boolEq, 23), (kIte, 30),
     (kEq, 70), (kNe, 71), (stringEq, 80), (stringLt, 81)] := by decide +kernel

/-- Arguments sorted at the argument sorts `hookSigs` gives `f`. -/
def SortedArgs_khs (c : Semantics) (f : Sym) (vs : List GroundTerm) : Prop :=
  ∃ k, lookupSig hookSigs f = some k ∧ c.sortsOf vs = some k.args

theorem sortedArgs_sorted_khs {c : Semantics} {f : Sym} {vs : List GroundTerm} (h : SortedArgs_khs c f vs) :
    ∀ v ∈ vs, ∃ s, c.sortOf v = some s := fun v hv => by
  obtain ⟨k, -, hF⟩ := h
  obtain ⟨s, -, hs⟩ := sortsOf_mem_kel hF v hv
  exact ⟨s, hs⟩

theorem sortedArgs_string_khs {c : Semantics} {f : Sym} {vs : List GroundTerm}
    (hk : lookupSig hookSigs f = some ⟨f, [Srt.string, Srt.string], Srt.bool⟩) (h : SortedArgs_khs c f vs) :
    ∀ v ∈ vs, c.sortOf v = some Srt.string := fun v hv => by
  obtain ⟨k, hk', hF⟩ := h
  rw [hk] at hk'
  cases hk'
  obtain ⟨s, hm, hs⟩ := sortsOf_mem_kel hF v hv
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hs
  · rcases List.mem_cons.mp hm with rfl | hm
    · exact hs
    · cases hm

/-- At a pair of `scalarCodes_khs`, `strictHook` at the encoded arguments evaluates at `K₀ sig` to the encoding of
KCore's result. -/
theorem hooks_scalar_mem_khs {d : Semantics} {f : Sym} {o : Int} (hfo : (f, o) ∈ scalarCodes_khs) (vs : List GroundTerm)
    (hs : o ≠ 30 → SortedArgs_khs (d₀ d) f vs) (hl : o = 30 ∨ o = 70 ∨ o = 71 → ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes f vs).join))) := by
  rw [scalarCodes_eq_khs] at hfo
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hfo
  rcases hfo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hooks_scalar_add vs
  · exact hooks_scalar_sub vs
  · exact hooks_scalar_mul vs
  · exact hooks_scalar_div vs
  · exact hooks_scalar_mod vs
  · exact hooks_scalar_lt vs
  · exact hooks_scalar_le vs
  · exact hooks_scalar_gt vs
  · exact hooks_scalar_ge vs
  · exact hooks_scalar_eq vs
  · exact hooks_scalar_ne vs
  · exact hooks_scalar_and vs
  · exact hooks_scalar_or vs
  · exact hooks_scalar_not vs
  · exact hooks_scalar_boolEq vs
  · exact hooks_scalar_ite vs (hl (.inl rfl))
  · exact hooks_scalar_keq vs (sortedArgs_sorted_khs (hs (by decide))) (hl (.inr (.inl rfl)))
  · exact hooks_scalar_kne vs (sortedArgs_sorted_khs (hs (by decide))) (hl (.inr (.inr rfl)))
  · exact hooks_scalar_strEq vs (sortedArgs_string_khs (by decide +kernel) (hs (by decide)))
  · exact hooks_scalar_strLt vs (sortedArgs_string_khs (by decide +kernel) (hs (by decide)))

/-- `opOf`'s code of `f` is `f`'s pair in `hookCodes`. -/
theorem opOf_mem_khs {f : Sym} {o : Int} (h : opOf f = some o) : (f, o) ∈ hookCodes := by
  unfold opOf at h
  cases hq : hookCodes.find? (·.1 == f) with
  | none => rw [hq] at h; cases h
  | some p =>
    rw [hq] at h
    cases h
    have hm := List.mem_of_find?_eq_some hq
    have he := List.find?_some hq
    obtain ⟨g, o'⟩ := p
    simp only [beq_iff_eq] at he
    subst he
    exact hm

/-- **The scalar hook lemma.** At the code `o` (`opOf`) of an interpreted symbol `f` of Int, Bool,
`ite`, K equality or String (`o` below 40 or from 70 on), `strictHook` at the encoded arguments
evaluates at `K₀ sig` to the encoding of KCore's result, for every semantics `d`: at arguments sorted
at `f`'s argument sorts (no sort for `ite`), and whose literals have a kore.k form at `ite`, `==K`
and `=/=K`. -/
theorem hooks_scalar {d : Semantics} {f : Sym} {o : Int} (hfo : opOf f = some o) (ho : o < 40 ∨ 70 ≤ o)
    (vs : List GroundTerm) (hs : o ≠ 30 → SortedArgs_khs (d₀ d) f vs)
    (hl : o = 30 ∨ o = 70 ∨ o = 71 → ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes f vs).join))) :=
  hooks_scalar_mem_khs (List.mem_filter.mpr ⟨opOf_mem_khs hfo, by rcases ho with h | h <;> simp [h]⟩) vs hs hl

end Uniform

/-! ## Instances -/

section Instances
open _root_.KK _root_.KK.Kit

/-- `7 /Int 0`: no value on either side. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 4), embTs [.iv 7, .iv 0]] (some (emb .bot)) :=
  hooks_scalar_div (d := RefKk.defn.sem) [int 7, int 0]

/-- `7 /Int 2` is `3`. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 4), embTs [.iv 7, .iv 2]] (some (emb (.iv 3))) :=
  hooks_scalar_div (d := RefKk.defn.sem) [int 7, int 2]

/-- `1 ==K 2` is `false`. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 70), embTs [.iv 1, .iv 2]] (some (emb (.bv false))) :=
  hooks_scalar_keq (d := RefKk.defn.sem) [int 1, int 2]
    (fun v hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨_, sort_int 1⟩
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨_, sort_int 2⟩
        · cases hv)
    (by decide)

/-- `2 +Int 3` through the uniform statement, its sort hypothesis discharged. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 1), embTs [.iv 2, .iv 3]] (some (emb (.iv 5))) :=
  hooks_scalar (d := RefKk.defn.sem) (f := intAdd) rfl (by decide) [int 2, int 3]
    (fun _ => ⟨⟨intAdd, [Srt.int, Srt.int], Srt.int⟩, by decide +kernel,
      sorts_cons (sort_int 2) (sorts_cons (sort_int 3) sorts_nil)⟩) (by decide)

/-- `ite(true, 1, 2)` is `1`. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 30), embTs [.bv true, .iv 1, .iv 2]] (some (emb (.iv 1))) :=
  hooks_scalar_ite (d := RefKk.defn.sem) [bool true, int 1, int 2] (by decide)

/-- `true =/=Bool false` is `true`, through codes 23 and 22. -/
example : EvalTerm (K₀ sig) (enumFrom 0 [embTs [.bv true, .bv false]])
    (.app 508 [.dv 3 (.int 22), .app 407 [.app 508 [.dv 3 (.int 23), .var 0], .app 406 []]]) (some (emb (.bv true))) :=
  boolNe_term (d := RefKk.defn.sem) [bool true, bool false] rfl

end Instances

/-! ## Checks -/

#check @hooks_scalar
#check @boolNe_comp
#check @boolNe_hook
#check @boolNe_term

open Lean in
#eval show CoreM Unit from do
  for n in [``hooksScalar_names, ``HooksS.strictHookDef_lookup, ``HooksS.hookOpDef_lookup,
      ``hooks_scalar_add, ``hooks_scalar_sub, ``hooks_scalar_mul, ``hooks_scalar_div, ``hooks_scalar_mod,
      ``hooks_scalar_lt, ``hooks_scalar_le, ``hooks_scalar_gt, ``hooks_scalar_ge, ``hooks_scalar_eq,
      ``hooks_scalar_ne, ``hooks_scalar_and, ``hooks_scalar_or, ``hooks_scalar_not, ``hooks_scalar_boolEq,
      ``hooks_scalar_ite, ``hooks_scalar_keq, ``hooks_scalar_kne, ``hooks_scalar_strEq, ``hooks_scalar_strLt,
      ``hooks_scalar_mem_khs, ``hooks_scalar, ``boolNe_comp, ``boolNe_hook, ``boolNe_term] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
