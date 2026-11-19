/-
  kore.k's collection helpers over the mirrors, on kore.k's semantics read from its kompiled text,
  in the shape of User.HelpTerms: a Lean function `F` of the mirrors, `F.eval : Eval (K₀ sig) f
  [emb x, …] r` at the function's symbol `f` with no hypothesis on the arguments, and `F.eval_iff`
  from `evalF_iff`.

  `mkKv` and `mkCol` (`mkKvF`, `mkColF`) give `bot` where a part is `bot` and have a value
  everywhere. `insE` (`insEF`), `delE` (`delEF`), `hasKey` (`hasKeyF`) have no value where a `ckey`
  they compute has none; `insE` marks an element whose key is already there by a `bot` in its place.
  `valueOr` (`valueOrF`) has none at a list holding a term that is not an entry before the first
  entry whose key compares 0 with the key looked up. `join` (`joinF`)
  recurses on the summed size of its part list (`psizeLF`): a collection part is replaced by its
  elements, an element is added to a list at its end and to a map or a set by `insE`; it has no
  value at a part that is neither, or at a first argument that is neither `bot` nor a collection.
  `colOf` (`colOfF`) is `bot` where a part is, else `join` from the empty collection. `isElem` is
  KKEncDef.lean's `isElemT`. `putE` is User.HelpOrder's `putEF`; `app` and `mkEl` are
  User.KkGenEmb's `Gen.appF` and `Gen.mkElF` (`appF_eq_khc`: `app` is `++`).

  `join` on the parts of a map's or a set's construction whose elements are entries (elements) with
  keys that encode values sorted in one semantics with kore.k literals is the insertion of all the
  elements by `insK` where no two keys meet, and `bot` where two do (`joinF_parts_khc`); on a list's,
  the elements in order (`joinF_list_parts_khc`). Against KCore: on parts that hold the items `its`
  of a collection of kind `K` (`PartsIts_khc`: an element is one item, the encoding of a collection
  value of `K` its items), `colOf` gives the collection of the items' encodings ordered by `ckeyF`,
  or `bot` where two items share a key (a map) or are equal (a set) (`colOfF_items_khc`); where KCore's
  concatenation of the parts has a value `u` holding those items up to order, that is `enc u`
  (`colOfF_coll_khc`, through `enc_items_khc`), and where two items meet it is `bot`
  (`colOfF_overlap_khc`). A list's construction gives the list of its items in order
  (`colOfF_list_items_khc`, `enc_list_items_khc`).

  The clauses are the semantics' own, as literals tied to `lookupFn` by the kernel.
-/
import User.HelpOrder
import User.HelpWalk

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The functions over the mirrors -/

/-- kore.k's `mkKv(A, V)`: `bot` where the key or the value is `bot`, else the entry. -/
def mkKvF (a v : T) : T := if hasBotF [a, v] then .bot else .kv a v

/-- kore.k's `mkCol(K, C, Es)`: `bot` where an element is `bot`, else the collection value. -/
def mkColF (k : Kind) (c : Int) (es : List T) : T := if hasBotF es then .bot else .co k c es

/-- kore.k's `insE(K, E, Es)`: `E` before the first element whose key it is below by `ckeyF`, `bot`
in its place where an element has its key; no value where `ckeyF` has none. -/
def insEF (k : Kind) (e : T) : List T → Option (List T)
  | [] => some [e]
  | f :: fs => (ckeyF e f).bind fun x =>
      if x < 0 then some (e :: f :: fs) else if x = 0 then some (.bot :: f :: fs)
      else (insEF k e fs).map (f :: ·)

/-- kore.k's `delE(E, Es)`: the list without the first element of `E`'s key; no value where
`ckeyF` has none. -/
def delEF (e : T) : List T → Option (List T)
  | [] => some []
  | f :: fs => (ckeyF e f).bind fun x => if x = 0 then some fs else (delEF e fs).map (f :: ·)

/-- kore.k's `valueOr(A, V, Es)`: the value of the first entry whose key compares 0 with `A`, `V`
where there is none; no value at a list with a term that is not an entry before such an entry. -/
def valueOrF (a v : T) : List T → Option T
  | [] => some v
  | .kv b w :: es => if cmpF a b = 0 then some w else valueOrF a v es
  | _ :: _ => none

/-- kore.k's `hasKey(E, Es)`: whether an element has `E`'s key; no value where `ckeyF` has none at
any element. -/
def hasKeyF (e : T) : List T → Option Bool
  | [] => some false
  | f :: fs => (ckeyF e f).bind fun x => (hasKeyF e fs).map fun b => decide (x = 0) || b

theorem psizeLF_append_khc : ∀ (as bs : List T), psizeLF (as ++ bs) = psizeLF as + psizeLF bs
  | [], bs => by simp [psizeLF]
  | a :: as, bs => by
    simp only [List.cons_append, psizeLF, psizeLF_append_khc as bs]
    omega

/-- kore.k's `join(V, Ps)`: the parts added one by one to the collection value `V`: a collection
part by its elements, an element at the end of a list and by `insE` into a map or a set, after
which a `bot` element makes the whole `bot`. No value at a part that is neither, or at a `V` that is
neither `bot` nor a collection. -/
def joinF : T → List T → Option T
  | v, [] => some v
  | .bot, _ :: _ => some .bot
  | .co k c es, p :: ps =>
    match p with
    | .co _ _ fs => joinF (.co k c es) (fs ++ ps)
    | e =>
      if isElemT e then
        if k = .list then joinF (.co .list c (es ++ [e])) ps
        else (insEF k e es).bind fun es' => joinF (mkColF k c es') ps
      else none
  | _, _ :: _ => none
  termination_by _ ps => psizeLF ps
  decreasing_by
    all_goals simp only [psizeLF, psizeF, psizeLF_append_khc]
    all_goals omega

/-- kore.k's `colOf(K, C, Ps)`: `bot` where a part is `bot`, else the parts joined from the empty
collection. -/
def colOfF (k : Kind) (c : Int) (ps : List T) : Option T :=
  if hasBotF ps then some .bot else joinF (.co k c []) ps

/-! ### `join`'s equations -/

theorem joinF_nil_khc (v : T) : joinF v [] = some v := by
  rw [joinF]

theorem joinF_bot_khc (p : T) (ps : List T) : joinF .bot (p :: ps) = some .bot := by
  rw [joinF]

theorem joinF_col_khc (k : Kind) (c : Int) (es : List T) (k' : Kind) (c' : Int) (fs ps : List T) :
    joinF (.co k c es) (.co k' c' fs :: ps) = joinF (.co k c es) (fs ++ ps) := by
  rw [joinF]

theorem joinF_list_khc (c : Int) (es : List T) {e : T} (he : isElemT e = true) (ps : List T) :
    joinF (.co .list c es) (e :: ps) = joinF (.co .list c (es ++ [e])) ps := by
  cases e <;> simp only [isElemT, Bool.false_eq_true] at he <;> rw [joinF] <;> simp [isElemT]

theorem joinF_elem_khc (k : Kind) (c : Int) (es : List T) {e : T} (he : isElemT e = true)
    (hk : k ≠ .list) (ps : List T) :
    joinF (.co k c es) (e :: ps) = (insEF k e es).bind fun es' => joinF (mkColF k c es') ps := by
  cases e <;> simp only [isElemT, Bool.false_eq_true] at he <;> rw [joinF] <;> simp [isElemT, hk]

theorem joinF_other_khc (k : Kind) (c : Int) (es : List T) {e : T} (he : isElemT e = false)
    (hc : ∀ k' c' fs, e ≠ .co k' c' fs) (ps : List T) : joinF (.co k c es) (e :: ps) = none := by
  cases e <;> simp only [isElemT, Bool.true_eq_false] at he <;>
    first | exact absurd rfl (hc _ _ _) | (rw [joinF] <;> first | rfl | exact fun _ _ _ h => T.noConfusion h)

theorem joinF_none_khc {v : T} (hb : v ≠ .bot) (hc : ∀ k c es, v ≠ .co k c es) (p : T) (ps : List T) :
    joinF v (p :: ps) = none := by
  cases v <;> first | exact absurd rfl hb | exact absurd rfl (hc _ _ _) |
    (rw [joinF] <;> first | rfl | exact fun h => T.noConfusion h | exact fun _ _ _ h => T.noConfusion h)

/-- kore.k's `app` is `++`. -/
theorem appF_eq_khc : ∀ (xs ys : List T), Gen.appF xs ys = some (xs ++ ys)
  | [], ys => rfl
  | x :: xs, ys => by rw [Gen.appF, appF_eq_khc xs ys]; rfl

/-- kore.k's `mkEl` keeps `bot`. -/
theorem mkElF_bot_khc : Gen.mkElF .bot = some .bot := rfl

/-- kore.k's `mkEl` makes any other term an element. -/
theorem mkElF_of_ne_khc {t : T} (h : t ≠ .bot) : Gen.mkElF t = some (.el t) := by
  cases t <;> first | exact absurd rfl h | rfl

/-! ## The symbols -/

/-- Each symbol number the evaluations below are at has the KORE name of the function. -/
theorem helpColl_names :
    RefKk.defn.sem.symName 459 = "LblcolOf'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Kind'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 461 = "LbldelE'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 472 = "LblhasKey'LParUndsCommUndsRParUnds'KORE'Unds'Bool'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 474 = "LblinsE'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Kind'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 478 = "LblisElem'LParUndsRParUnds'KORE'Unds'Bool'Unds'Term" ∧
    RefKk.defn.sem.symName 479 = "Lbljoin'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 491 = "LblmkCol'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Kind'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 494 = "LblmkKv'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 517 = "LblvalueOr'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Term'Unds'Term'Unds'Ts" := by
  decide +kernel

/-! ## The clauses, as the semantics holds them -/

namespace Coll
open _root_.KK Terms

/-- `ckey(E, F) <op> 0` at the variables `i` and `j`. -/
abbrev ckeyAt (op : Sym) (i j : Nat) : Term := .app op [.app 455 [.var i, .var j], .dv 3 (.int 0)]

/-- `colOf` (459): `col-def`, `col-bot`. -/
def colOfDef : Fn :=
  { label := 459, args := [34, 3, 43], result := 33, total := false, clauses := [
    plainCl [34, 3, 43] [.var 0, .var 1, .var 2] (.app 479 [.app 416 [.var 0, .var 1, .app 406 []], .var 2])
      (req := some (.app 3 [.app 471 [.var 2]])),
    plainCl [34, 3, 43] [.var 0, .var 1, .var 2] (.app 412 []) (req := some (.app 471 [.var 2]))] }

/-- `delE` (461): `dele-hit`, `dele-miss`, `dele-nil`. -/
def delEDef : Fn :=
  { label := 461, args := [33, 43], result := 43, total := false, clauses := [
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.var 2) (req := some (ckeyAt 23 0 1)),
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 407 [.var 1, .app 461 [.var 0, .var 2]])
      (req := some (ckeyAt 24 0 1)),
    plainCl [33, 43] [.var 0, .as (.app 406 []) 1] (.var 1)] }

/-- `hasKey` (472): `haskey-cons`, `haskey-nil`. -/
def hasKeyDef : Fn :=
  { label := 472, args := [33, 43], result := 2, total := false, clauses := [
    plainCl [33, 33, 43] [.var 0, .app 407 [.var 1, .var 2]] (.app 6 [ckeyAt 23 0 1, .app 472 [.var 0, .var 2]]),
    plainCl [33] [.var 0, .app 406 []] (.dv 2 (.bool false))] }

/-- `insE` (474): `inse-after`, `inse-nil`, `inse-before`, `inse-overlap`. -/
def insEDef : Fn :=
  { label := 474, args := [34, 33, 43], result := 43, total := false, clauses := [
    plainCl [34, 33, 33, 43] [.var 0, .var 1, .app 407 [.var 2, .var 3]]
      (.app 407 [.var 2, .app 474 [.var 0, .var 1, .var 3]]) (req := some (ckeyAt 21 1 2)),
    plainCl [34, 33, 43] [.var 0, .var 1, .as (.app 406 []) 2] (.app 407 [.var 1, .var 2]),
    plainCl [34, 33, 33, 43, 43] [.var 0, .var 1, .as (.app 407 [.var 2, .var 3]) 4] (.app 407 [.var 1, .var 4])
      (req := some (ckeyAt 19 1 2)),
    plainCl [34, 33, 33, 43, 43] [.var 0, .var 1, .as (.app 407 [.var 2, .var 3]) 4]
      (.app 407 [.app 412 [], .var 4]) (req := some (ckeyAt 23 1 2))] }

/-- `isElem` (478): `elem-el`, `elem-kv`, `elem-not` (priority 200, `[owise]`). -/
def isElemDef : Fn :=
  { label := 478, args := [33], result := 2, total := false, clauses := [
    plainCl [33] [.app 419 [.var 0]] (.dv 2 (.bool true)),
    plainCl [33, 33] [.app 426 [.var 0, .var 1]] (.dv 2 (.bool true)),
    plainCl [33] [.var 0] (.dv 2 (.bool false)) (prio := 200)] }

/-- `K =/=K list` on `K`'s K sequence. -/
abbrev kindNeList : Term :=
  .app 30 [.app 0 [.inj 34 1 (.var 0), .app 1 []], .app 0 [.inj 34 1 (.app 427 []), .app 1 []]]

/-- `join` (479): `join-bot`, `join-col`, `join-nil`, `join-list`, `join-elem`. -/
def joinDef : Fn :=
  { label := 479, args := [33, 43], result := 33, total := false, clauses := [
    plainCl [33, 33, 43] [.as (.app 412 []) 0, .app 407 [.var 1, .var 2]] (.var 0),
    plainCl [34, 3, 43, 33, 34, 3, 43, 43]
      [.as (.app 416 [.var 0, .var 1, .var 2]) 3, .app 407 [.app 416 [.var 4, .var 5, .var 6], .var 7]]
      (.app 479 [.var 3, .app 447 [.var 6, .var 7]]),
    plainCl [33] [.var 0, .app 406 []] (.var 0),
    plainCl [34, 3, 43, 33, 43] [.app 416 [.as (.app 427 []) 0, .var 1, .var 2], .app 407 [.var 3, .var 4]]
      (.app 479 [.app 416 [.var 0, .var 1, .app 447 [.var 2, .app 407 [.var 3, .app 406 []]]], .var 4])
      (req := some (.app 478 [.var 3])),
    plainCl [34, 3, 43, 33, 43] [.app 416 [.var 0, .var 1, .var 2], .app 407 [.var 3, .var 4]]
      (.app 479 [.app 491 [.var 0, .var 1, .app 474 [.var 0, .var 3, .var 2]], .var 4])
      (req := some (.app 4 [.app 478 [.var 3], kindNeList]))] }

/-- `mkCol` (491): `mkcol-def`, `mkcol-bot`. -/
def mkColDef : Fn :=
  { label := 491, args := [34, 3, 43], result := 33, total := false, clauses := [
    plainCl [34, 3, 43] [.var 0, .var 1, .var 2] (.app 416 [.var 0, .var 1, .var 2])
      (req := some (.app 3 [.app 471 [.var 2]])),
    plainCl [34, 3, 43] [.var 0, .var 1, .var 2] (.app 412 []) (req := some (.app 471 [.var 2]))] }

/-- `mkKv` (494): `kv-bot`, `kv-def`. -/
def mkKvDef : Fn :=
  { label := 494, args := [33, 33], result := 33, total := false, clauses := [
    plainCl [33, 33] [.var 0, .var 1] (.app 412 []) (req := some (.app 471 [.app 407 [.var 0, .app 407 [.var 1, .app 406 []]]])),
    plainCl [33, 33] [.var 0, .var 1] (.app 426 [.var 0, .var 1])
      (req := some (.app 3 [.app 471 [.app 407 [.var 0, .app 407 [.var 1, .app 406 []]]]]))] }

/-- `valueOr` (517): `at-miss`, `at-hit`, `at-missing`. -/
def valueOrDef : Fn :=
  { label := 517, args := [33, 33, 43], result := 33, total := false, clauses := [
    plainCl [33, 33, 33, 33, 43] [.var 0, .var 1, .app 407 [.app 426 [.var 2, .var 3], .var 4]]
      (.app 517 [.var 0, .var 1, .var 4]) (req := some (.app 24 [.app 456 [.var 0, .var 2], .dv 3 (.int 0)])),
    plainCl [33, 33, 33, 33, 43] [.var 0, .var 1, .app 407 [.app 426 [.var 2, .var 3], .var 4]]
      (.var 3) (req := some (.app 23 [.app 456 [.var 0, .var 2], .dv 3 (.int 0)])),
    plainCl [33, 33] [.var 0, .var 1, .app 406 []] (.var 1)] }

theorem colOfDef_lookup : c₀.lookupFn 459 = some colOfDef := by kernel_rfl
theorem delEDef_lookup : c₀.lookupFn 461 = some delEDef := by kernel_rfl
theorem hasKeyDef_lookup : c₀.lookupFn 472 = some hasKeyDef := by kernel_rfl
theorem insEDef_lookup : c₀.lookupFn 474 = some insEDef := by kernel_rfl
theorem isElemDef_lookup : c₀.lookupFn 478 = some isElemDef := by kernel_rfl
theorem joinDef_lookup : c₀.lookupFn 479 = some joinDef := by kernel_rfl
theorem mkColDef_lookup : c₀.lookupFn 491 = some mkColDef := by kernel_rfl
theorem mkKvDef_lookup : c₀.lookupFn 494 = some mkKvDef := by kernel_rfl
theorem valueOrDef_lookup : c₀.lookupFn 517 = some valueOrDef := by kernel_rfl

end Coll

/-! ## Shared steps -/

section Kit
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Coll

theorem hook_not_khc (x : Bool) : hook 3 [bool x] = some (some (bool (!x))) := by cases x <;> rfl

theorem hook_and_khc (x y : Bool) : hook 4 [bool x, bool y] = some (some (bool (x && y))) := by
  cases x <;> cases y <;> rfl

/-- `notBool A` at a Bool value. -/
theorem ev_not_khc {σ : Subst} {a : Term} {x : Bool} (ha : EvalTerm c₀ σ a (some (bool x))) :
    EvalTerm c₀ σ (.app 3 [a]) (some (bool (!x))) := by
  refine .hook (by decide +kernel) (by decide +kernel) (EvArgs.terms (.cons ha .nil)) (fun vs hvs => ?_)
    (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value (hook_not_khc x)
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

/-- `A andBool B` at two Bool values. -/
theorem ev_and_khc {σ : Subst} {a b : Term} {x y : Bool} (ha : EvalTerm c₀ σ a (some (bool x)))
    (hb : EvalTerm c₀ σ b (some (bool y))) : EvalTerm c₀ σ (.app 4 [a, b]) (some (bool (x && y))) := by
  refine .hook (by decide +kernel) (by decide +kernel) (EvArgs.terms (.cons ha (.cons hb .nil)))
    (fun vs hvs => ?_) (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value (hook_and_khc x y)
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

/-- `hasBot(A)` at a list. -/
theorem ev_hasBot_khc {σ : Subst} {a : Term} {ts : List T} (ha : EvalTerm c₀ σ a (some (embTs ts))) :
    EvalTerm c₀ σ (.app 471 [a]) (some (bool (hasBotF ts))) :=
  ev_call (.cons ha .nil) (hasBotF_eval_c₀ ts) notCtor_471 notHook_471 notParam_471

/-- `kseq(inj{Kind,KItem}(K), dotk)`. -/
abbrev kindV_khc (k : Kind) : GroundTerm := .ctor 0 [.inj 34 1 (embK k), .ctor 1 []]

theorem kindV_cmp_khc (k : Kind) :
    (GroundTerm.cmp (kindV_khc k) (kindV_khc .list) != .eq) = !decide (k = .list) := by
  by_cases h : k = .list
  · subst h; simp [GroundTerm.cmp_refl]
  · rw [decide_eq_false h]
    cases hc : GroundTerm.cmp (kindV_khc k) (kindV_khc .list) with
    | eq =>
      have e := cmp_eq_iff.mp hc
      simp only [kindV_khc, GroundTerm.ctor.injEq, List.cons.injEq, GroundTerm.inj.injEq, true_and,
        and_true] at e
      exact absurd (embK_injective e) h
    | lt => rfl
    | gt => rfl

theorem kindV_eval_khc {σ : Subst} {a : Term} {k : Kind} (ha : EvalTerm c₀ σ a (some (embK k))) :
    EvalTerm c₀ σ (.app 0 [.inj 34 1 a, .app 1 []]) (some (kindV_khc k)) := by
  have e : injNormal 34 1 (embK k) = .inj 34 1 (embK k) := by cases k <;> rfl
  have := EvalTerm.ctor (σ := σ) (f := 0) (by decide +kernel)
    (.cons (EvalTerm.inj (a := 34) (b := 1) ha) (.cons (EvalTerm.ctor (ts := []) (f := 1) (by decide +kernel) .nil) .nil))
  rw [kindV_khc, ← e]
  exact this

/-- `A =/=K list` on the K sequences of a term whose value is a kind. -/
theorem ev_kindNeT_khc {σ : Subst} {a : Term} {k : Kind} (ha : EvalTerm c₀ σ a (some (embK k))) :
    EvalTerm c₀ σ (.app 30 [.app 0 [.inj 34 1 a, .app 1 []], .app 0 [.inj 34 1 (.app 427 []), .app 1 []]])
      (some (bool (!decide (k = .list)))) := by
  refine EvalTerm.hook (by decide +kernel) rfl
    (.cons (kindV_eval_khc ha) (.cons (kindV_eval_khc (k := .list) (ev_ctor .nil ctor_427)) .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  rw [← kindV_cmp_khc]
  exact Semantics.hookRes_of_value (hook_kNe _ _)

/-- `K =/=K list` at the variable 0, as `join-elem`'s `requires` has it. -/
theorem ev_kindNe_khc {σ : Subst} {k : Kind} (h0 : σ.lookup 0 = some (embK k)) :
    EvalTerm c₀ σ kindNeList (some (bool (!decide (k = .list)))) :=
  ev_kindNeT_khc (ev_var h0)

/-- `ckey(E, F) <op> 0` at the variables `i` and `j`, where `ckey` has a value. -/
theorem ev_ckeyAt_khc {σ : Subst} {e f : T} {x : Int} {op : Sym} {P : Int → Int → Prop}
    [∀ x y, Decidable (P x y)] {i j : Nat} (hk : ckeyF e f = some x)
    (hf : ∀ vs, hook op vs = some (int2 vs fun x y => some (bool (decide (P x y)))))
    (hi : σ.lookup i = some (emb e)) (hj : σ.lookup j = some (emb f))
    (hc : c₀.isCtor op = false) (hh : isHook op = true) :
    EvalTerm c₀ σ (ckeyAt op i j) (some (bool (decide (P x 0)))) := by
  have h := ckey_eval_kho e f
  rw [hk] at h
  exact ev_int2 hf (ev_call (.cons (ev_var hi) (.cons (ev_var hj) .nil)) h notCtor_455 notHook_455 notParam_455)
    EvalTerm.dv hc hh

/-- `ckey(E, F) <op> 0` at the variables `i` and `j`, where `ckey` has no value. -/
theorem ev_ckeyAt_none_khc {σ : Subst} {e f : T} {op : Sym} {i j : Nat} (hk : ckeyF e f = none)
    (hi : σ.lookup i = some (emb e)) (hj : σ.lookup j = some (emb f))
    (hc : c₀.isCtor op = false) (hh : isHook op = true) : EvalTerm c₀ σ (ckeyAt op i j) none := by
  have h := ckey_eval_kho e f
  rw [hk] at h
  exact .hook hc hh (.cons (ev_call (.cons (ev_var hi) (.cons (ev_var hj) .nil)) h notCtor_455 notHook_455 notParam_455)
    (.cons EvalTerm.dv .nil)) (fun _ h => nomatch h) (fun _ => rfl)

end Kit

/-! ## `isElem`, `mkKv`, `mkCol` -/

section Small
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Coll

spike_hb in
theorem isElem_eval_khc (t : T) : Eval c₀ 478 [emb t] (some (bool (isElemT t))) := by
  by_cases h1 : ∃ x, t = .el x
  · obtain ⟨x, rfl⟩ := h1
    exact clause_kht (σ := enumFrom 0 [emb x]) isElemDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ x) .nil)) (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) .nil)
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  by_cases h2 : ∃ a v, t = .kv a v
  · obtain ⟨a, v, rfl⟩ := h2
    exact clause_kht (σ := enumFrom 0 [emb a, emb v]) isElemDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) .nil)))
      (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  have hf : isElemT t = false := by
    cases t <;> first | rfl | exact absurd ⟨_, rfl⟩ h1 | exact absurd ⟨_, _, rfl⟩ h2
  rw [hf]
  refine Eval.clause (σ := enumFrom 0 [emb t]) isElemDef_lookup
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (ws_enum (.cons (emb_sorted_c₀ t) .nil)) (.cons (.var rfl) .nil)
    (fun _ h => by cases h) Holds.top ?_ rfl .dv (fun _ h => by cases h) Holds.top
  intro cl' hm _ hp
  simp only [isElemDef, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;>
    first
    | exact absurd hp (by decide)
    | refine fails_kht fun σ hm => ?_
      rcases hm with _ | ⟨h0, -⟩
  · obtain ⟨x, rfl⟩ := headOf_eq_el.mp (pat_head_kho h0 ctor_419 noHook_419)
    exact h1 ⟨x, rfl⟩
  · obtain ⟨a, v, rfl⟩ := headOf_eq_kv.mp (pat_head_kho h0 ctor_426 noHook_426)
    exact h2 ⟨a, v, rfl⟩

/-- `isElem(A)` at a term. -/
theorem ev_isElem_khc {σ : Subst} {a : Term} {t : T} (ha : EvalTerm c₀ σ a (some (emb t))) :
    EvalTerm c₀ σ (.app 478 [a]) (some (bool (isElemT t))) :=
  ev_call (.cons ha .nil) (isElem_eval_khc t) notCtor_478 notHook_478 notParam_478

spike_hb in
theorem mkKv_eval_khc (a v : T) : Eval c₀ 494 [emb a, emb v] (some (emb (mkKvF a v))) := by
  have hσ := ws_enum (vars := [33, 33]) (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) .nil))
  have hp : PatVals c₀ (enumFrom 0 [emb a, emb v]) [.var 0, .var 1] [emb a, emb v] :=
    .cons (.var rfl) (.cons (.var rfl) .nil)
  have hb : EvalTerm c₀ (enumFrom 0 [emb a, emb v]) (.app 471 [.app 407 [.var 0, .app 407 [.var 1, .app 406 []]]])
      (some (bool (hasBotF [a, v]))) :=
    ev_hasBot_khc (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406) .nil))
      ctor_407) .nil)) ctor_407)
  rw [mkKvF]
  cases hh : hasBotF [a, v]
  · rw [ite_neg Bool.false_ne_true]
    refine clause_kht mkKvDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
      ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_426)
    intro q hq; cases hq
    have h := ev_not_khc hb
    rw [hh] at h; exact h
  · rw [ite_pos rfl]
    refine clause_kht mkKvDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor .nil ctor_412)
    intro q hq; cases hq
    rw [hh] at hb; exact hb

spike_hb in
theorem mkCol_eval_khc (k : Kind) (c : Int) (es : List T) :
    Eval c₀ 491 [embK k, iv3 c, embTs es] (some (emb (mkColF k c es))) := by
  have hσ := ws_enum (vars := [34, 3, 43]) (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ es) .nil)))
  have hp : PatVals c₀ (enumFrom 0 [embK k, iv3 c, embTs es]) [.var 0, .var 1, .var 2] [embK k, iv3 c, embTs es] :=
    .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))
  have hb := ev_hasBot_khc (σ := enumFrom 0 [embK k, iv3 c, embTs es]) (a := .var 2) (ev_var rfl)
  rw [mkColF]
  cases hh : hasBotF es
  · rw [ite_neg Bool.false_ne_true]
    refine clause_kht mkColDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) ctor_416)
    intro q hq; cases hq
    have h := ev_not_khc hb
    rw [hh] at h; exact h
  · rw [ite_pos rfl]
    refine clause_kht mkColDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
      ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_412)
    intro q hq; cases hq
    rw [hh] at hb; exact hb

end Small

/-! ## `insE`, `delE`, `hasKey`, `valueOr` -/

section Lists
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Coll

spike_hb in
theorem insE_eval_khc (k : Kind) (e : T) :
    ∀ fs : List T, Eval c₀ 474 [embK k, emb e, embTs fs] ((insEF k e fs).map embTs)
  | [] =>
    clause_kht (σ := enumFrom 0 [embK k, emb e, embTs []]) insEDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (emb_sorted_c₀ e) (.cons (embTs_sorted_c₀ []) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.as (.ctor ctor_406 .nil) rfl) .nil)))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_407)
  | f :: fs => by
    have hσ := ws_enum (vars := [34, 33, 33, 43, 43]) (.cons (embK_sorted_c₀ k) (.cons (emb_sorted_c₀ e)
      (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ fs) (.cons (embTs_sorted_c₀ (f :: fs)) .nil)))))
    have hp : PatVals c₀ (enumFrom 0 [embK k, emb e, emb f, embTs fs, embTs (f :: fs)])
        [.var 0, .var 1, .as (.app 407 [.var 2, .var 3]) 4] [embK k, emb e, embTs (f :: fs)] :=
      .cons (.var rfl) (.cons (.var rfl)
        (.cons (.as (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) rfl) .nil))
    have hσ' := ws_enum (vars := [34, 33, 33, 43]) (.cons (embK_sorted_c₀ k) (.cons (emb_sorted_c₀ e)
      (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ fs) .nil))))
    have hp' : PatVals c₀ (enumFrom 0 [embK k, emb e, emb f, embTs fs])
        [.var 0, .var 1, .app 407 [.var 2, .var 3]] [embK k, emb e, embTs (f :: fs)] :=
      .cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
    cases hk : ckeyF e f with
    | none =>
      rw [insEF, hk]
      refine Eval.rest insEDef_lookup fun cl hm => ?_
      simp only [insEDef, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      all_goals first
        | exact fails_kht fun σ hm => by
            rcases hm with _ | ⟨-, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩
            exact patCtor_ne_kht (PatVal.as_inv h2).1 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)
        | refine .intro fun σ _ hm => ?_
          rcases hm with _ | ⟨-, _ | ⟨h1, _ | ⟨h2, -⟩⟩⟩
          first
          | obtain ⟨ws, hw, hs⟩ := pv_ctor (PatVal.as_inv h2).1 ctor_407 noHook_407
          | obtain ⟨ws, hw, hs⟩ := pv_ctor h2 ctor_407 noHook_407
          rw [embTs, GroundTerm.ctor.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          rcases hs with _ | ⟨h2', -⟩
          exact .intro rfl (ev_ckeyAt_none_khc hk (PatVal.var_inv h1) (PatVal.var_inv h2') (by decide +kernel)
            (by decide +kernel)) nofun
    | some x =>
      rw [insEF, hk]
      simp only [Option.bind_some]
      by_cases h1 : x < 0
      · rw [ite_pos h1]
        refine clause_kht insEDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_407)
        intro q hq; cases hq
        have hq := ev_ckeyAt_khc (σ := enumFrom 0 [embK k, emb e, emb f, embTs fs, embTs (f :: fs)])
          (P := (· < ·)) (i := 1) (j := 2) hk hook_intLt rfl rfl notCtor_19 isHook_19
        rwa [decide_eq_true h1] at hq
      · rw [ite_neg h1]
        by_cases h2 : x = 0
        · rw [ite_pos h2]
          refine clause_kht insEDef_lookup
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
            hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
            (ev_ctor (.cons (ev_ctor .nil ctor_412) (.cons (ev_var rfl) .nil)) ctor_407)
          intro q hq; cases hq
          have hq := ev_ckeyAt_khc (σ := enumFrom 0 [embK k, emb e, emb f, embTs fs, embTs (f :: fs)])
            (P := (· = ·)) (i := 1) (j := 2) hk hook_intEq rfl rfl notCtor_23 isHook_23
          rwa [decide_eq_true h2] at hq
        · rw [ite_neg h2]
          have h3 : x > 0 := by omega
          refine clause_kht insEDef_lookup (List.mem_cons_self ..) hσ' hp' ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
          · intro q hq; cases hq
            have hq := ev_ckeyAt_khc (σ := enumFrom 0 [embK k, emb e, emb f, embTs fs])
              (P := (· > ·)) (i := 1) (j := 2) hk hook_intGt rfl rfl notCtor_21 isHook_21
            rwa [decide_eq_true h3] at hq
          · have h := EvalTerm.ctor (σ := enumFrom 0 [embK k, emb e, emb f, embTs fs]) ctor_407
              (.cons (ev_var (i := 2) rfl) (.cons (ev_call (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 1) rfl)
                (.cons (ev_var (i := 3) rfl) .nil))) (insE_eval_khc k e fs) notCtor_474 notHook_474 notParam_474) .nil))
            rw [Option.map_map]
            generalize insEF k e fs = o at h ⊢
            cases o <;> exact h

spike_hb in
theorem delE_eval_khc (e : T) : ∀ fs : List T, Eval c₀ 461 [emb e, embTs fs] ((delEF e fs).map embTs)
  | [] =>
    clause_kht (σ := enumFrom 0 [emb e, embTs []]) delEDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (ws_enum (.cons (emb_sorted_c₀ e) (.cons (embTs_sorted_c₀ []) .nil)))
      (.cons (.var rfl) (.cons (.as (.ctor ctor_406 .nil) rfl) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | f :: fs => by
    have hσ := ws_enum (vars := [33, 33, 43]) (.cons (emb_sorted_c₀ e) (.cons (emb_sorted_c₀ f)
      (.cons (embTs_sorted_c₀ fs) .nil)))
    have hp : PatVals c₀ (enumFrom 0 [emb e, emb f, embTs fs])
        [.var 0, .app 407 [.var 1, .var 2]] [emb e, embTs (f :: fs)] :=
      .cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)
    cases hk : ckeyF e f with
    | none =>
      rw [delEF, hk]
      refine Eval.rest delEDef_lookup fun cl hm => ?_
      simp only [delEDef, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      all_goals first
        | exact fails_kht fun σ hm => by
            rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
            exact patCtor_ne_kht (PatVal.as_inv h1).1 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)
        | refine .intro fun σ _ hm => ?_
          rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
          obtain ⟨ws, hw, hs⟩ := pv_ctor h1 ctor_407 noHook_407
          rw [embTs, GroundTerm.ctor.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          rcases hs with _ | ⟨h1', -⟩
          exact .intro rfl (ev_ckeyAt_none_khc hk (PatVal.var_inv h0) (PatVal.var_inv h1') (by decide +kernel)
            (by decide +kernel)) nofun
    | some x =>
      rw [delEF, hk]
      simp only [Option.bind_some]
      by_cases h : x = 0
      · rw [ite_pos h]
        refine clause_kht delEDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
          (ev_var rfl)
        intro q hq; cases hq
        have hq := ev_ckeyAt_khc (σ := enumFrom 0 [emb e, emb f, embTs fs]) (P := (· = ·)) (i := 0) (j := 1)
          hk hook_intEq rfl rfl notCtor_23 isHook_23
        rwa [decide_eq_true h] at hq
      · rw [ite_neg h]
        refine clause_kht delEDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
          ⟨rfl, rfl, rfl, rfl⟩ ?_
        · intro q hq; cases hq
          have hq := ev_ckeyAt_khc (σ := enumFrom 0 [emb e, emb f, embTs fs]) (P := (· ≠ ·)) (i := 0) (j := 1)
            hk hook_intNe rfl rfl notCtor_24 isHook_24
          rwa [decide_eq_true h] at hq
        · have h := EvalTerm.ctor (σ := enumFrom 0 [emb e, emb f, embTs fs]) ctor_407
            (.cons (ev_var (i := 1) rfl) (.cons (ev_call (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 2) rfl) .nil))
              (delE_eval_khc e fs) notCtor_461 notHook_461 notParam_461) .nil))
          rw [Option.map_map]
          generalize delEF e fs = o at h ⊢
          cases o <;> exact h

spike_hb in
theorem hasKey_eval_khc (e : T) :
    ∀ fs : List T, Eval c₀ 472 [emb e, embTs fs] ((hasKeyF e fs).map fun b => .dv 2 (.bool b))
  | [] =>
    clause_kht (σ := enumFrom 0 [emb e]) hasKeyDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ e) .nil)) (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ .dv
  | f :: fs => by
    have hrec := ev_call (σ := enumFrom 0 [emb e, emb f, embTs fs])
      (.cons (ev_var (i := 0) rfl) (.cons (ev_var (i := 2) rfl) .nil)) (hasKey_eval_khc e fs)
      notCtor_472 notHook_472 notParam_472
    refine clause_kht (σ := enumFrom 0 [emb e, emb f, embTs fs]) hasKeyDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (emb_sorted_c₀ e) (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ fs) .nil))))
      (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    rw [hasKeyF]
    cases hk : ckeyF e f with
    | none =>
      exact .hook (by decide +kernel) (by decide +kernel)
        (.cons (ev_ckeyAt_none_khc hk rfl rfl notCtor_23 isHook_23) (.cons hrec .nil))
        (fun _ h => nomatch h) (fun _ => rfl)
    | some x =>
      simp only [Option.bind_some]
      have hq := ev_ckeyAt_khc (σ := enumFrom 0 [emb e, emb f, embTs fs]) (P := (· = ·)) (i := 0) (j := 1)
        hk hook_intEq rfl rfl notCtor_23 isHook_23
      cases hr : hasKeyF e fs with
      | none =>
        rw [hr] at hrec
        exact .hook (by decide +kernel) (by decide +kernel) (.cons hq (.cons hrec .nil))
          (fun _ h => nomatch h) (fun _ => rfl)
      | some b =>
        rw [hr] at hrec
        exact ev_or_kho hq hrec

spike_hb in
theorem valueOr_eval_khc (a v : T) : ∀ es : List T, Eval c₀ 517 [emb a, emb v, embTs es] ((valueOrF a v es).map emb)
  | [] =>
    clause_kht (σ := enumFrom 0 [emb a, emb v]) valueOrDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (ws_enum (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) .nil)))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil)))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | e :: es => by
    by_cases he : ∃ b w, e = .kv b w
    · obtain ⟨b, w, rfl⟩ := he
      have hσ := ws_enum (vars := [33, 33, 33, 33, 43]) (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v)
        (.cons (emb_sorted_c₀ b) (.cons (emb_sorted_c₀ w) (.cons (embTs_sorted_c₀ es) .nil)))))
      have hp : PatVals c₀ (enumFrom 0 [emb a, emb v, emb b, emb w, embTs es])
          [.var 0, .var 1, .app 407 [.app 426 [.var 2, .var 3], .var 4]] [emb a, emb v, embTs (.kv b w :: es)] :=
        .cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.ctor ctor_426 (.cons (.var rfl)
          (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      have hc := ev_cmp_kho (σ := enumFrom 0 [emb a, emb v, emb b, emb w, embTs es]) (a := .var 0) (b := .var 2)
        (ev_var rfl) (ev_var rfl) (cmp_eval_kho a b)
      rw [valueOrF]
      by_cases h : cmpF a b = 0
      · rw [ite_pos h]
        refine clause_kht valueOrDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
          ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
        intro q hq; cases hq
        have hq := ev_int2 (P := (· = ·)) (u := .dv 3 (.int 0)) (y := 0) hook_intEq hc EvalTerm.dv notCtor_23 isHook_23
        rwa [decide_eq_true h] at hq
      · rw [ite_neg h]
        refine clause_kht valueOrDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
          (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) (valueOr_eval_khc a v es)
            notCtor_517 notHook_517 notParam_517)
        intro q hq; cases hq
        have hq := ev_int2 (P := (· ≠ ·)) (u := .dv 3 (.int 0)) (y := 0) hook_intNe hc EvalTerm.dv notCtor_24 isHook_24
        rwa [decide_eq_true h] at hq
    · have hnone : valueOrF a v (e :: es) = none := by
        cases e <;> first | rfl | exact absurd ⟨_, _, rfl⟩ he
      rw [hnone]
      refine Eval.rest valueOrDef_lookup fun cl hm => ?_
      simp only [valueOrDef, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> refine fails_kht fun σ hm => ?_ <;>
        rcases hm with _ | ⟨-, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩
      all_goals first
        | exact patCtor_ne_kht h2 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)
        | obtain ⟨ws, hw, hs⟩ := pv_ctor h2 ctor_407 noHook_407
          rw [embTs, GroundTerm.ctor.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          rcases hs with _ | ⟨h3, -⟩
          obtain ⟨b, w, rfl⟩ := headOf_eq_kv.mp (pat_head_kho h3 ctor_426 noHook_426)
          exact he ⟨b, w, rfl⟩

end Lists

/-! ## `join`, `colOf` -/

section Join
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms Coll

theorem app_eval_khc (xs ys : List T) : Eval c₀ 447 [embTs xs, embTs ys] (some (embTs (xs ++ ys))) := by
  have h := Gen.appF.eval xs ys
  rw [appF_eq_khc] at h
  exact h

spike_hb in
theorem join_eval_khc (v : T) (ps : List T) : Eval c₀ 479 [emb v, embTs ps] ((joinF v ps).map emb) := by
  match ps with
  | [] =>
    rw [joinF_nil_khc]
    exact clause_kht (σ := enumFrom 0 [emb v]) joinDef_lookup
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (ws_enum (.cons (emb_sorted_c₀ v) .nil)) (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | p :: ps =>
    by_cases hb : v = .bot
    · subst hb
      rw [joinF_bot_khc]
      exact clause_kht (σ := enumFrom 0 [emb .bot, emb p, embTs ps]) joinDef_lookup (List.mem_cons_self ..)
        (ws_enum (.cons (emb_sorted_c₀ .bot) (.cons (emb_sorted_c₀ p) (.cons (embTs_sorted_c₀ ps) .nil))))
        (.cons (.as (.ctor ctor_412 .nil) rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
        (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
    by_cases hco : ∃ k c es, v = .co k c es
    · obtain ⟨k, c, es, rfl⟩ := hco
      by_cases hpc : ∃ k' c' fs, p = .co k' c' fs
      · obtain ⟨k', c', fs, rfl⟩ := hpc
        rw [joinF_col_khc]
        have ih := join_eval_khc (.co k c es) (fs ++ ps)
        exact clause_kht (σ := enumFrom 0 [embK k, iv3 c, embTs es, emb (.co k c es), embK k', iv3 c', embTs fs,
            embTs ps]) joinDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ es)
            (.cons (emb_sorted_c₀ (.co k c es)) (.cons (embK_sorted_c₀ k') (.cons (sort_int c')
              (.cons (embTs_sorted_c₀ fs) (.cons (embTs_sorted_c₀ ps) .nil)))))))))
          (.cons (.as (.ctor ctor_416 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) rfl)
            (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
              (.cons (.var rfl) .nil))) .nil))
          (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
          (ev_call (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))
            (app_eval_khc fs ps) notCtor_447 notHook_447 notParam_447) .nil)) ih notCtor_479 notHook_479 notParam_479)
      have hσ := ws_enum (vars := [34, 3, 43, 33, 43]) (.cons (embK_sorted_c₀ k) (.cons (sort_int c)
        (.cons (embTs_sorted_c₀ es) (.cons (emb_sorted_c₀ p) (.cons (embTs_sorted_c₀ ps) .nil)))))
      cases he : isElemT p
      · rw [joinF_other_khc k c es he (fun k' c' fs h => hpc ⟨k', c', fs, h⟩)]
        refine Eval.rest joinDef_lookup fun cl hm => ?_
        simp only [joinDef, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl
        · exact fails_kht fun σ hm => by
            rcases hm with _ | ⟨h0, -⟩
            exact patCtor_ne_kht (PatVal.as_inv h0).1 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)
        · exact fails_kht fun σ hm => by
            rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
            obtain ⟨ws, hw, hs⟩ := pv_ctor h1 ctor_407 noHook_407
            rw [embTs, GroundTerm.ctor.injEq] at hw
            obtain ⟨-, rfl⟩ := hw
            rcases hs with _ | ⟨h3, -⟩
            obtain ⟨k', c', fs, rfl⟩ := headOf_eq_co.mp (pat_head_kho h3 ctor_416 noHook_416)
            exact hpc ⟨k', c', fs, rfl⟩
        · exact fails_kht fun σ hm => by
            rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
            exact patCtor_ne_kht h1 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)
        · refine .intro fun σ _ hm => ?_
          rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
          obtain ⟨ws, hw, hs⟩ := pv_ctor h1 ctor_407 noHook_407
          rw [embTs, GroundTerm.ctor.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          rcases hs with _ | ⟨h3, -⟩
          refine .intro rfl (ev_isElem_khc (ev_var (PatVal.var_inv h3))) ?_
          rw [he]; decide
        · refine .intro fun σ _ hm => ?_
          rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
          obtain ⟨ws, hw, hs⟩ := pv_ctor h1 ctor_407 noHook_407
          rw [embTs, GroundTerm.ctor.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          rcases hs with _ | ⟨h3, -⟩
          obtain ⟨ws', hw', hs'⟩ := pv_ctor h0 ctor_416 noHook_416
          rw [emb, GroundTerm.ctor.injEq] at hw'
          obtain ⟨-, rfl⟩ := hw'
          rcases hs' with _ | ⟨h4, -⟩
          refine .intro rfl (ev_and_khc (ev_isElem_khc (ev_var (PatVal.var_inv h3)))
            (ev_kindNe_khc (PatVal.var_inv h4))) ?_
          rw [he, Bool.false_and]; decide
      · by_cases hk : k = .list
        · subst hk
          rw [joinF_list_khc c es he]
          have ih := join_eval_khc (.co .list c (es ++ [p])) ps
          refine clause_kht (σ := enumFrom 0 [embK .list, iv3 c, embTs es, emb p, embTs ps]) joinDef_lookup
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) hσ
            (.cons (.ctor ctor_416 (.cons (.as (.ctor ctor_427 .nil) rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
              (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
            ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
            (ev_call (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl)
              (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406) .nil)) ctor_407) .nil))
              (app_eval_khc es [p]) notCtor_447 notHook_447 notParam_447) .nil))) ctor_416) (.cons (ev_var rfl) .nil))
              ih notCtor_479 notHook_479 notParam_479)
          intro q hq; cases hq
          have h := ev_isElem_khc (σ := enumFrom 0 [embK .list, iv3 c, embTs es, emb p, embTs ps]) (ev_var (i := 3) rfl)
          rw [he] at h; exact h
        · rw [joinF_elem_khc k c es he hk]
          refine clause_kht (σ := enumFrom 0 [embK k, iv3 c, embTs es, emb p, embTs ps]) joinDef_lookup
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_self ..))))) hσ
            (.cons (.ctor ctor_416 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
              (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil))
            ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
          · intro q hq; cases hq
            have h := ev_and_khc (ev_isElem_khc (σ := enumFrom 0 [embK k, iv3 c, embTs es, emb p, embTs ps])
              (ev_var (i := 3) rfl)) (ev_kindNe_khc (k := k) rfl)
            rw [he, decide_eq_false hk] at h; exact h
          · have hins := insE_eval_khc k p es
            cases hi : insEF k p es with
            | none =>
              rw [hi] at hins
              exact .callUndef notCtor_479 notHook_479
                (.cons (.callUndef notCtor_491 notHook_491 (.cons (ev_var rfl) (.cons (ev_var rfl)
                  (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) hins
                    notCtor_474 notHook_474 notParam_474) .nil))) rfl notParam_491) (.cons (ev_var rfl) .nil))
                rfl notParam_479
            | some es' =>
              rw [hi] at hins
              have ih := join_eval_khc (mkColF k c es') ps
              exact ev_call (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl)
                (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))) hins
                  notCtor_474 notHook_474 notParam_474) .nil))) (mkCol_eval_khc k c es') notCtor_491 notHook_491
                  notParam_491) (.cons (ev_var rfl) .nil)) ih notCtor_479 notHook_479 notParam_479
    · have hco' : headOf v ≠ 416 := fun h => by
        obtain ⟨k, c, es, rfl⟩ := headOf_eq_co.mp h
        exact hco ⟨k, c, es, rfl⟩
      have hb' : headOf v ≠ 412 := fun h => hb (headOf_eq_bot.mp h)
      rw [joinF_none_khc hb (fun k c es h => hco ⟨k, c, es, h⟩)]
      refine Eval.rest joinDef_lookup fun cl hm => ?_
      simp only [joinDef, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> refine fails_kht fun σ hm => ?_ <;>
        rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
      · exact patCtor_ne_kht (PatVal.as_inv h0).1 (emb_ne_kht hb')
      · exact patCtor_ne_kht (PatVal.as_inv h0).1 (emb_ne_kht hco')
      · exact patCtor_ne_kht h1 fun ws h => absurd (GroundTerm.ctor.inj h).1 (by decide)
      · exact patCtor_ne_kht h0 (emb_ne_kht hco')
      · exact patCtor_ne_kht h0 (emb_ne_kht hco')
termination_by psizeLF ps
decreasing_by
  all_goals (try subst_vars); simp only [psizeLF, psizeF, psizeLF_append_khc]; omega

spike_hb in
theorem colOf_eval_khc (k : Kind) (c : Int) (ps : List T) :
    Eval c₀ 459 [embK k, iv3 c, embTs ps] ((colOfF k c ps).map emb) := by
  have hσ := ws_enum (vars := [34, 3, 43]) (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ ps) .nil)))
  have hp : PatVals c₀ (enumFrom 0 [embK k, iv3 c, embTs ps]) [.var 0, .var 1, .var 2] [embK k, iv3 c, embTs ps] :=
    .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))
  have hb := ev_hasBot_khc (σ := enumFrom 0 [embK k, iv3 c, embTs ps]) (a := .var 2) (ev_var rfl)
  rw [colOfF]
  cases hh : hasBotF ps
  · rw [ite_neg Bool.false_ne_true]
    refine clause_kht colOfDef_lookup (List.mem_cons_self ..) hσ hp ?_ (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406) .nil))) ctor_416)
        (.cons (ev_var rfl) .nil)) (join_eval_khc (.co k c []) ps) notCtor_479 notHook_479 notParam_479)
    intro q hq; cases hq
    have h := ev_not_khc hb
    rw [hh] at h; exact h
  · rw [ite_pos rfl]
    refine clause_kht colOfDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_ (by decide)
      ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_412)
    intro q hq; cases hq
    rw [hh] at hb; exact hb

end Join

/-! ## The helpers at `K₀ sig` -/

section Shape

theorem isElemT.eval (t : T) : Eval (K₀ sig) 478 [emb t] (some (.dv 2 (.bool (isElemT t)))) :=
  isElem_eval_khc t
theorem isElemT.eval_iff (t : T) {r : Option GroundTerm} :
    Eval (K₀ sig) 478 [emb t] r ↔ r = some (.dv 2 (.bool (isElemT t))) :=
  evalF_iff (isElemT.eval t)

theorem mkKvF.eval (a v : T) : Eval (K₀ sig) 494 [emb a, emb v] (some (emb (mkKvF a v))) :=
  mkKv_eval_khc a v
theorem mkKvF.eval_iff (a v : T) {r : Option GroundTerm} :
    Eval (K₀ sig) 494 [emb a, emb v] r ↔ r = some (emb (mkKvF a v)) :=
  evalF_iff (mkKvF.eval a v)

theorem mkColF.eval (k : Kind) (c : Int) (es : List T) :
    Eval (K₀ sig) 491 [embK k, .dv 3 (.int c), embTs es] (some (emb (mkColF k c es))) :=
  mkCol_eval_khc k c es
theorem mkColF.eval_iff (k : Kind) (c : Int) (es : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 491 [embK k, .dv 3 (.int c), embTs es] r ↔ r = some (emb (mkColF k c es)) :=
  evalF_iff (mkColF.eval k c es)

theorem insEF.eval (k : Kind) (e : T) (fs : List T) :
    Eval (K₀ sig) 474 [embK k, emb e, embTs fs] ((insEF k e fs).map embTs) :=
  insE_eval_khc k e fs
theorem insEF.eval_iff (k : Kind) (e : T) (fs : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 474 [embK k, emb e, embTs fs] r ↔ r = (insEF k e fs).map embTs :=
  evalF_iff (insEF.eval k e fs)

theorem delEF.eval (e : T) (fs : List T) : Eval (K₀ sig) 461 [emb e, embTs fs] ((delEF e fs).map embTs) :=
  delE_eval_khc e fs
theorem delEF.eval_iff (e : T) (fs : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 461 [emb e, embTs fs] r ↔ r = (delEF e fs).map embTs :=
  evalF_iff (delEF.eval e fs)

theorem hasKeyF.eval (e : T) (fs : List T) :
    Eval (K₀ sig) 472 [emb e, embTs fs] ((hasKeyF e fs).map fun b => .dv 2 (.bool b)) :=
  hasKey_eval_khc e fs
theorem hasKeyF.eval_iff (e : T) (fs : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 472 [emb e, embTs fs] r ↔ r = (hasKeyF e fs).map fun b => .dv 2 (.bool b) :=
  evalF_iff (hasKeyF.eval e fs)

theorem valueOrF.eval (a v : T) (es : List T) :
    Eval (K₀ sig) 517 [emb a, emb v, embTs es] ((valueOrF a v es).map emb) :=
  valueOr_eval_khc a v es
theorem valueOrF.eval_iff (a v : T) (es : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 517 [emb a, emb v, embTs es] r ↔ r = (valueOrF a v es).map emb :=
  evalF_iff (valueOrF.eval a v es)

theorem joinF.eval (v : T) (ps : List T) : Eval (K₀ sig) 479 [emb v, embTs ps] ((joinF v ps).map emb) :=
  join_eval_khc v ps
theorem joinF.eval_iff (v : T) (ps : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 479 [emb v, embTs ps] r ↔ r = (joinF v ps).map emb :=
  evalF_iff (joinF.eval v ps)

theorem colOfF.eval (k : Kind) (c : Int) (ps : List T) :
    Eval (K₀ sig) 459 [embK k, .dv 3 (.int c), embTs ps] ((colOfF k c ps).map emb) :=
  colOf_eval_khc k c ps
theorem colOfF.eval_iff (k : Kind) (c : Int) (ps : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 459 [embK k, .dv 3 (.int c), embTs ps] r ↔ r = (colOfF k c ps).map emb :=
  evalF_iff (colOfF.eval k c ps)

end Shape

/-! ## `join` on the parts of a map's or a set's construction -/

/-- What `ckeyF` compares an element by: an entry's key, an element's value. -/
def keyT_khc : T → T
  | .kv a _ => a
  | .el x => x
  | t => t

/-- An element of a map (an entry) or of a set (an `el`), whose key is the encoding of a value
sorted in `c` with kore.k literals. -/
def ElemOK_khc (c : Semantics) (k : Kind) (e : T) : Prop :=
  match k with
  | .map => ∃ a v, e = .kv a v ∧ EncSorted c a
  | _ => ∃ x, e = .el x ∧ EncSorted c x

/-- A part of a construction: an element, or a collection value whose elements are elements. -/
def PartOK_khc (c : Semantics) (k : Kind) (p : T) : Prop :=
  ElemOK_khc c k p ∨ ∃ k' n fs, p = .co k' n fs ∧ ∀ f ∈ fs, ElemOK_khc c k f

/-- The elements the parts contribute, in order: a collection value's elements in its place. -/
def flatK_khc : List T → List T
  | [] => []
  | .co _ _ fs :: ps => fs ++ flatK_khc ps
  | p :: ps => p :: flatK_khc ps

/-- Strictly increasing by `ckeyF`. -/
abbrev SortedK_khc (es : List T) : Prop := es.Pairwise fun a b => ckeyF a b = some (-1)

section Elems
open _root_.KK.Kit (ite_pos ite_neg)
variable {c : Semantics} {k : Kind}

theorem ElemOK_khc.ckey {e f : T} (he : ElemOK_khc c k e) (hf : ElemOK_khc c k f) :
    ckeyF e f = some (cmpF (keyT_khc e) (keyT_khc f)) := by
  cases k with
  | map =>
    obtain ⟨a, v, rfl, -⟩ := he
    obtain ⟨b, w, rfl, -⟩ := hf
    rfl
  | set =>
    obtain ⟨x, rfl, -⟩ := he
    obtain ⟨y, rfl, -⟩ := hf
    rfl
  | list =>
    obtain ⟨x, rfl, -⟩ := he
    obtain ⟨y, rfl, -⟩ := hf
    rfl

theorem ElemOK_khc.key {e : T} (he : ElemOK_khc c k e) : EncSorted c (keyT_khc e) := by
  cases k with
  | map => obtain ⟨a, v, rfl, h⟩ := he; exact h
  | set => obtain ⟨x, rfl, h⟩ := he; exact h
  | list => obtain ⟨x, rfl, h⟩ := he; exact h

theorem ElemOK_khc.elem {e : T} (he : ElemOK_khc c k e) : isElemT e = true := by
  cases k with
  | map => obtain ⟨a, v, rfl, -⟩ := he; rfl
  | set => obtain ⟨x, rfl, -⟩ := he; rfl
  | list => obtain ⟨x, rfl, -⟩ := he; rfl

theorem ElemOK_khc.ne_bot {e : T} (he : ElemOK_khc c k e) : e ≠ .bot := by
  have h := he.elem
  intro hb; subst hb; cases h

theorem ElemOK_khc.ne_co {e : T} (he : ElemOK_khc c k e) : ∀ k' n fs, e ≠ .co k' n fs := by
  have h := he.elem
  intro k' n fs hb; subst hb; cases h

/-- Two elements of different keys are ordered one way or the other. -/
theorem ElemOK_khc.total {e f : T} (he : ElemOK_khc c k e) (hf : ElemOK_khc c k f)
    (hne : keyT_khc e ≠ keyT_khc f) : ckeyF e f = some (-1) ∨ ckeyF f e = some (-1) := by
  rw [he.ckey hf, hf.ckey he, cmpF_swap (keyT_khc e)]
  have h0 : cmpF (keyT_khc e) (keyT_khc f) ≠ 0 := fun h => hne ((cmpF_eq_zero_iff_ord he.key hf.key).mp h)
  rcases cmpF_range (keyT_khc e) (keyT_khc f) with h | h | h
  · exact .inl (by rw [h])
  · exact absurd h h0
  · exact .inr (by rw [h])

theorem ElemOK_khc.trans {a b e : T} (ha : ElemOK_khc c k a) (hb : ElemOK_khc c k b)
    (he : ElemOK_khc c k e) (h1 : ckeyF a b = some (-1)) (h2 : ckeyF b e = some (-1)) :
    ckeyF a e = some (-1) := by
  rw [ha.ckey hb, Option.some.injEq] at h1
  rw [hb.ckey he, Option.some.injEq] at h2
  rw [ha.ckey he, cmpF_trans_ord ha.key hb.key he.key h1 h2]

theorem hasBotF_false_khc : ∀ {ts : List T}, (∀ t ∈ ts, t ≠ .bot) → hasBotF ts = false
  | [], _ => rfl
  | t :: ts, h => by
    rw [hasBotF, hasBotF_false_khc fun u hu => h u (List.mem_cons_of_mem _ hu),
      decide_eq_false (h t (List.mem_cons_self ..))]
    rfl

/-- Keys apart in a list single out its members. -/
theorem eq_of_keyT_khc : ∀ {L : List T}, (L.map keyT_khc).Nodup → ∀ {a b : T}, a ∈ L → b ∈ L →
    keyT_khc a = keyT_khc b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: L, hn, a, b, ha, hb, hk => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd (hk ▸ List.mem_map_of_mem h2) hn.1
    · subst h2; exact absurd (hk.symm ▸ List.mem_map_of_mem h1) hn.1
    · exact eq_of_keyT_khc hn.2 h1 h2 hk

/-- A list strictly increasing by `ckeyF` has its keys apart. -/
theorem SortedK_khc.keys {es : List T} (hS : ∀ e ∈ es, ElemOK_khc c k e) (hp : SortedK_khc es) :
    (es.map keyT_khc).Nodup := by
  refine List.pairwise_map.mpr (hp.imp_of_mem fun {a b} ha hb h hk => ?_)
  rw [(hS a ha).ckey (hS b hb), hk, cmpF_self] at h
  cases h

/-- `insE` of an element of a new key is `insK`. -/
theorem insEF_new_khc {e : T} (he : ElemOK_khc c k e) :
    ∀ {es : List T}, (∀ f ∈ es, ElemOK_khc c k f) → keyT_khc e ∉ es.map keyT_khc →
      insEF k e es = some (insK e es)
  | [], _, _ => rfl
  | f :: fs, hS, hn => by
    have hf := hS f (List.mem_cons_self ..)
    rw [List.map_cons, List.mem_cons, not_or] at hn
    have h0 : cmpF (keyT_khc e) (keyT_khc f) ≠ 0 :=
      fun h => hn.1 ((cmpF_eq_zero_iff_ord he.key hf.key).mp h)
    rw [insEF, insK, he.ckey hf, Option.bind_some]
    rcases cmpF_range (keyT_khc e) (keyT_khc f) with h | h | h
    · rw [h]; rfl
    · exact absurd h h0
    · rw [h, insEF_new_khc he (fun g hg => hS g (List.mem_cons_of_mem _ hg)) hn.2]
      rfl

/-- `insE` of an element of a key already there leaves a `bot`. -/
theorem insEF_dup_khc {e : T} (he : ElemOK_khc c k e) :
    ∀ {es : List T}, (∀ f ∈ es, ElemOK_khc c k f) → SortedK_khc es → keyT_khc e ∈ es.map keyT_khc →
      ∃ L, insEF k e es = some L ∧ hasBotF L = true
  | [], _, _, hm => nomatch hm
  | f :: fs, hS, hp, hm => by
    have hf := hS f (List.mem_cons_self ..)
    rw [insEF, he.ckey hf, Option.bind_some]
    by_cases hk : keyT_khc f = keyT_khc e
    · rw [hk, cmpF_self]
      exact ⟨_, rfl, rfl⟩
    · rw [List.map_cons, List.mem_cons] at hm
      have hm : keyT_khc e ∈ fs.map keyT_khc := hm.resolve_left fun h => hk h.symm
      obtain ⟨g, hg, hge⟩ := List.mem_map.mp hm
      have hp := List.pairwise_cons.mp hp
      have h1 := hp.1 g hg
      rw [hf.ckey (hS g (List.mem_cons_of_mem _ hg)), hge, Option.some.injEq] at h1
      have h2 : cmpF (keyT_khc e) (keyT_khc f) = 1 := by rw [cmpF_swap, h1]; rfl
      obtain ⟨L, hL, hb⟩ := insEF_dup_khc he (fun g hg => hS g (List.mem_cons_of_mem _ hg)) hp.2 hm
      rw [h2, ite_neg (by decide), ite_neg (by decide), hL]
      refine ⟨_, rfl, ?_⟩
      rw [hasBotF, hb, Bool.or_true]

/-- Inserting an element of a new key keeps a list strictly increasing by `ckeyF`. -/
theorem insK_ok_khc {e : T} (he : ElemOK_khc c k e) {es : List T} (hS : ∀ f ∈ es, ElemOK_khc c k f)
    (hp : SortedK_khc es) (hn : keyT_khc e ∉ es.map keyT_khc) :
    SortedK_khc (insK e es) ∧ ∀ f ∈ insK e es, ElemOK_khc c k f := by
  have hS' : ∀ f ∈ e :: es, ElemOK_khc c k f := fun f hf => by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact he
    · exact hS f hf
  have hnd : ((e :: es).map keyT_khc).Nodup := by
    rw [List.map_cons, List.nodup_cons]; exact ⟨hn, hp.keys hS⟩
  refine ⟨insK_sorted_kkc (S := (· ∈ e :: es))
    (fun a b x ha hb hx => (hS' a ha).trans (hS' b hb) (hS' x hx))
    (fun a b ha hb hne => (hS' a ha).total (hS' b hb) fun hk => hne (eq_of_keyT_khc hnd ha hb hk))
    (List.mem_cons_self ..) (fun f hf => List.mem_cons_of_mem _ hf)
    (fun hm => hn (List.mem_map_of_mem hm)) hp, fun f hf => ?_⟩
  rcases mem_insK.mp hf with rfl | hf
  · exact he
  · exact hS f hf

theorem joinF_bot_any_khc : ∀ ps : List T, joinF .bot ps = some .bot
  | [] => joinF_nil_khc _
  | p :: ps => joinF_bot_khc p ps

/-- `join` adds elements to a map or a set one by one: the result is the insertion of all of them
where no two keys meet, and `bot` where two do. -/
theorem joinF_elems_khc (hk : k ≠ .list) (n : Int) :
    ∀ (E : List T) {es : List T} (ps : List T), (∀ e ∈ E, ElemOK_khc c k e) → (∀ f ∈ es, ElemOK_khc c k f) →
      SortedK_khc es →
      joinF (.co k n es) (E ++ ps) =
        if ((es ++ E).map keyT_khc).Nodup then joinF (.co k n (E.foldl (fun acc e => insK e acc) es)) ps
        else some .bot
  | [], es, ps, _, hS, hp => by
    rw [List.append_nil, ite_pos (hp.keys hS)]; rfl
  | e :: E, es, ps, hE, hS, hp => by
    have he := hE e (List.mem_cons_self ..)
    have hE' : ∀ x ∈ E, ElemOK_khc c k x := fun x hx => hE x (List.mem_cons_of_mem _ hx)
    rw [List.cons_append, joinF_elem_khc k n es he.elem hk]
    by_cases hm : keyT_khc e ∈ es.map keyT_khc
    · obtain ⟨L, hL, hb⟩ := insEF_dup_khc he hS hp hm
      rw [hL, Option.bind_some, mkColF, ite_pos hb, joinF_bot_any_khc, ite_neg]
      rw [List.map_append, List.nodup_append]
      exact fun h => h.2.2 _ hm _ (List.mem_cons_self ..) rfl
    · obtain ⟨hp', hS'⟩ := insK_ok_khc he hS hp hm
      rw [insEF_new_khc he hS hm, Option.bind_some, mkColF,
        ite_neg (by rw [hasBotF_false_khc fun f hf => (hS' f hf).ne_bot]; decide),
        joinF_elems_khc hk n E ps hE' hS' hp', List.foldl_cons]
      have hiff : ((insK e es ++ E).map keyT_khc).Nodup ↔ ((es ++ e :: E).map keyT_khc).Nodup :=
        ((((insK_perm_kkc e es).append_right E).trans List.perm_middle.symm).map keyT_khc).nodup_iff
      by_cases hn : ((es ++ e :: E).map keyT_khc).Nodup
      · rw [ite_pos hn, ite_pos (hiff.mpr hn)]
      · rw [ite_neg hn, ite_neg fun h => hn (hiff.mp h)]

theorem foldl_insK_ok_khc : ∀ (E : List T) {es : List T}, (∀ e ∈ E, ElemOK_khc c k e) →
    (∀ f ∈ es, ElemOK_khc c k f) → SortedK_khc es → ((es ++ E).map keyT_khc).Nodup →
    SortedK_khc (E.foldl (fun acc e => insK e acc) es) ∧
      ∀ f ∈ E.foldl (fun acc e => insK e acc) es, ElemOK_khc c k f
  | [], _, _, hS, hp, _ => ⟨hp, hS⟩
  | e :: E, es, hE, hS, hp, hn => by
    have hm : keyT_khc e ∉ es.map keyT_khc := by
      rw [List.map_append, List.nodup_append] at hn
      exact fun h => hn.2.2 _ h _ (List.mem_cons_self ..) rfl
    obtain ⟨hp', hS'⟩ := insK_ok_khc (hE e (List.mem_cons_self ..)) hS hp hm
    exact foldl_insK_ok_khc E (fun x hx => hE x (List.mem_cons_of_mem _ hx)) hS' hp'
      (((((insK_perm_kkc e es).append_right E).trans List.perm_middle.symm).map keyT_khc).nodup_iff.mpr hn)

/-- **`join` on the parts of a map's or a set's construction.** From a collection value strictly
increasing by `ckeyF`, `join` gives the collection of all the parts' elements inserted by `insK`
where no two keys meet, and `bot` where two do. -/
theorem joinF_parts_khc (hk : k ≠ .list) (n : Int) :
    ∀ (ps : List T) {es : List T}, (∀ p ∈ ps, PartOK_khc c k p) → (∀ f ∈ es, ElemOK_khc c k f) →
      SortedK_khc es →
      joinF (.co k n es) ps =
        some (if ((es ++ flatK_khc ps).map keyT_khc).Nodup then
          .co k n ((flatK_khc ps).foldl (fun acc e => insK e acc) es) else .bot)
  | [], es, _, hS, hp => by
    rw [joinF_nil_khc, ite_pos (by simpa [flatK_khc] using hp.keys hS)]; rfl
  | p :: ps, es, hps, hS, hp => by
    have hps' : ∀ q ∈ ps, PartOK_khc c k q := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    obtain ⟨G, hG, hj, hf⟩ : ∃ G : List T, (∀ e ∈ G, ElemOK_khc c k e) ∧
        joinF (.co k n es) (p :: ps) = joinF (.co k n es) (G ++ ps) ∧
        flatK_khc (p :: ps) = G ++ flatK_khc ps := by
      rcases hps p (List.mem_cons_self ..) with he | ⟨k', n', fs, rfl, hfs⟩
      · refine ⟨[p], fun e he' => by rw [List.mem_singleton.mp he']; exact he, rfl, ?_⟩
        have h := he.elem
        cases p <;> first | rfl | cases h
      · exact ⟨fs, hfs, joinF_col_khc k n es k' n' fs ps, rfl⟩
    rw [hj, joinF_elems_khc hk n G ps hG hS hp, hf]
    by_cases hn : ((es ++ G).map keyT_khc).Nodup
    · obtain ⟨hp', hS'⟩ := foldl_insK_ok_khc G hG hS hp hn
      rw [ite_pos hn, joinF_parts_khc hk n ps hps' hS' hp', List.foldl_append]
      have hiff : ((G.foldl (fun acc e => insK e acc) es ++ flatK_khc ps).map keyT_khc).Nodup ↔
          ((es ++ (G ++ flatK_khc ps)).map keyT_khc).Nodup := by
        rw [← List.append_assoc]
        exact (((foldl_insK_perm_kkc G es).append_right _).map keyT_khc).nodup_iff
      by_cases hn' : ((es ++ (G ++ flatK_khc ps)).map keyT_khc).Nodup
      · rw [ite_pos hn', ite_pos (hiff.mpr hn')]
      · rw [ite_neg hn', ite_neg fun h => hn' (hiff.mp h)]
    · rw [ite_neg hn, ite_neg]
      intro h
      apply hn
      rw [← List.append_assoc, List.map_append] at h
      exact (List.nodup_append.mp h).1

theorem PartOK_khc.ne_bot {p : T} (h : PartOK_khc c k p) : p ≠ .bot := by
  rcases h with he | ⟨k', n, fs, rfl, -⟩
  · exact he.ne_bot
  · exact fun h => T.noConfusion h

/-- **`colOf` on the parts of a map's or a set's construction**: the collection of the parts'
elements ordered by `ckeyF` (`sortK`) where no two keys meet, `bot` where two do. -/
theorem colOfF_parts_khc (hk : k ≠ .list) (n : Int) {ps : List T} (hps : ∀ p ∈ ps, PartOK_khc c k p) :
    colOfF k n ps = some (if ((flatK_khc ps).map keyT_khc).Nodup then .co k n (sortK (flatK_khc ps)) else .bot) := by
  rw [colOfF, ite_neg (by rw [hasBotF_false_khc fun p hp => (hps p hp).ne_bot]; decide),
    joinF_parts_khc hk n ps hps (fun _ h => by cases h) .nil]
  rfl

end Elems

/-! ## `join` on the parts of a list's construction -/

section ListParts
open _root_.KK.Kit (ite_pos ite_neg)

theorem joinF_list_elems_khc (n : Int) : ∀ (E : List T) (es ps : List T), (∀ e ∈ E, isElemT e = true) →
    joinF (.co .list n es) (E ++ ps) = joinF (.co .list n (es ++ E)) ps
  | [], es, ps, _ => by rw [List.append_nil, List.nil_append]
  | e :: E, es, ps, hE => by
    rw [List.cons_append, joinF_list_khc n es (hE e (List.mem_cons_self ..)),
      joinF_list_elems_khc n E (es ++ [e]) ps fun x hx => hE x (List.mem_cons_of_mem _ hx)]
    simp

/-- A part of a list's construction: an element, or a collection value whose elements are
elements. -/
def ListPartOK_khc (p : T) : Prop :=
  isElemT p = true ∨ ∃ k' n fs, p = .co k' n fs ∧ ∀ f ∈ fs, isElemT f = true

/-- **`join` on the parts of a list's construction**: the parts' elements in order. -/
theorem joinF_list_parts_khc (n : Int) : ∀ (ps es : List T), (∀ p ∈ ps, ListPartOK_khc p) →
    joinF (.co .list n es) ps = some (.co .list n (es ++ flatK_khc ps))
  | [], es, _ => by rw [joinF_nil_khc]; simp [flatK_khc]
  | p :: ps, es, hps => by
    have hps' : ∀ q ∈ ps, ListPartOK_khc q := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    rcases hps p (List.mem_cons_self ..) with he | ⟨k', n', fs, rfl, hfs⟩
    · rw [joinF_list_khc n es he, joinF_list_parts_khc n ps (es ++ [p]) hps']
      have : flatK_khc (p :: ps) = p :: flatK_khc ps := by cases p <;> first | rfl | cases he
      rw [this]; simp
    · rw [joinF_col_khc, joinF_list_elems_khc n fs es ps hfs, joinF_list_parts_khc n ps _ hps']
      simp [flatK_khc]

/-- **`colOf` on the parts of a list's construction**: the list of the parts' elements in order. -/
theorem colOfF_list_parts_khc (n : Int) {ps : List T} (hps : ∀ p ∈ ps, ListPartOK_khc p) :
    colOfF .list n ps = some (.co .list n (flatK_khc ps)) := by
  have hb : ∀ p ∈ ps, p ≠ .bot := fun p hp h => by
    subst h
    rcases hps _ hp with h | ⟨_, _, _, h, -⟩
    · cases h
    · cases h
  rw [colOfF, ite_neg (by rw [hasBotF_false_khc hb]; decide), joinF_list_parts_khc n ps [] hps]
  rfl

end ListParts

/-! ## `colOf` against the collection value KCore builds from the same items -/

section Items
open KCore.CExec (content build)
open _root_.KK.Kit (ite_pos ite_neg)
variable {c : Semantics}

/-- An item's key: a map entry's key, a set's or a list's element. -/
def keyIt_khc : List GroundTerm → GroundTerm
  | [a, _] => a
  | [e] => e
  | _ => .ctor 0 []

/-- An item of a collection of kind `K`: a map's entry `[a, b]` and a set's element `[e]` whose key
is a value sorted in `c` with kore.k literals; a list's element `[e]`. -/
def ItemOK_khc (c : Semantics) : CollKind → List GroundTerm → Prop
  | .map, it => ∃ a b s, it = [a, b] ∧ c.sortOf a = some s ∧ litsV a = true
  | .set, it => ∃ e s, it = [e] ∧ c.sortOf e = some s ∧ litsV e = true
  | .list, it => ∃ e, it = [e]
  | .rangeMap, _ => False

/-- The parts of a construction of kind `K` as `kore.k` evaluates them, and the items they hold in
order: an element part (`encIt_cdp`) its one item, and the encoding of a collection value of `K`
the value's items. -/
inductive PartsIts_khc (c : Semantics) (K : CollKind) : List T → List (List GroundTerm) → Prop
  | nil : PartsIts_khc c K [] []
  | elem {it : List GroundTerm} {ps : List T} {its : List (List GroundTerm)} (h : ItemOK_khc c K it)
      (hs : PartsIts_khc c K ps its) : PartsIts_khc c K (encIt_cdp it :: ps) (it :: its)
  | coll {w : GroundTerm} {s : Srt} {g : List (List GroundTerm)} {ps : List T}
      {its : List (List GroundTerm)} (hc : content w = some (K, s, g)) (hg : ∀ it ∈ g, ItemOK_khc c K it)
      (hs : PartsIts_khc c K ps its) : PartsIts_khc c K (enc w :: ps) (g ++ its)

theorem PartsIts_khc.items {K : CollKind} {ps : List T} {its : List (List GroundTerm)}
    (h : PartsIts_khc c K ps its) : ∀ it ∈ its, ItemOK_khc c K it := by
  induction h with
  | nil => exact fun _ h => by cases h
  | elem hit _ ih =>
    intro it' hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hit
    · exact ih it' hm
  | coll _ hg _ ih =>
    intro it' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hg it' hm
    · exact ih it' hm

/-- The encoding of a collection value: its items' encodings, as `kore.k` holds them. -/
theorem enc_content_khc {K : CollKind} {k : Kind} (hK : kindOf K = some k) {w : GroundTerm} {s : Srt}
    {g : List (List GroundTerm)} (hc : content w = some (K, s, g)) :
    enc w = .co k s (ordK_cdp k (g.map encIt_cdp)) := by
  cases w with
  | map s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    cases hK
    simp only [enc, encKvs_eq_map, ordK_cdp, List.map_map]; rfl
  | set s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    cases hK
    simp only [enc, encEls_eq_map, ordK_cdp, List.map_map]; rfl
  | list s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    cases hK
    simp only [enc, encEls_eq_map, ordK_cdp, List.map_map]; rfl
  | _ => simp [content] at hc

theorem ItemOK_khc.elemOK {K : CollKind} {k : Kind} (hK : kindOf K = some k) (hk : k ≠ .list)
    {it : List GroundTerm} (h : ItemOK_khc c K it) : ElemOK_khc c k (encIt_cdp it) ∧ keyT_khc (encIt_cdp it) = enc (keyIt_khc it) := by
  cases K with
  | map =>
    cases hK
    obtain ⟨a, b, s, rfl, hs, la⟩ := h
    exact ⟨⟨_, _, rfl, ⟨a, s, hs, la, rfl⟩⟩, rfl⟩
  | set =>
    cases hK
    obtain ⟨e, s, rfl, hs, le⟩ := h
    exact ⟨⟨_, rfl, ⟨e, s, hs, le, rfl⟩⟩, rfl⟩
  | list => cases hK; exact absurd rfl hk
  | rangeMap => cases hK

theorem nodup_of_map_khc {α β : Type} {f : α → β} {L : List α} (h : (L.map f).Nodup) : L.Nodup :=
  (List.pairwise_map.mp h).imp fun hne he => hne (congrArg f he)

theorem nodup_map_khc {α β : Type} {f : α → β} {L : List α} (h : L.Nodup)
    (hf : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) : (L.map f).Nodup :=
  List.pairwise_map.mpr (h.imp_of_mem fun {x y} hx hy hne he => hne (hf x hx y hy he))

theorem perm_keys_nodup_khc {L L' : List T} (h : L.Perm L') :
    (L.map keyT_khc).Nodup ↔ (L'.map keyT_khc).Nodup := (h.map keyT_khc).nodup_iff

/-- A list of elements whose keys are apart is put strictly increasing by `sortK`. -/
theorem sortK_ok_khc {k : Kind} {L : List T} (hS : ∀ e ∈ L, ElemOK_khc c k e)
    (hn : (L.map keyT_khc).Nodup) : SortedK_khc (sortK L) :=
  sortK_sorted (nodup_of_map_khc hn) (fun a ha b hb e he => (hS a ha).trans (hS b hb) (hS e he))
    (fun a ha b hb hne => (hS a ha).total (hS b hb) fun hk => hne (eq_of_keyT_khc hn ha hb hk))

/-- The parts are parts of a map's or a set's construction, and their elements are the items'
encodings, up to order. -/
theorem PartsIts_khc.flat {K : CollKind} {k : Kind} (hK : kindOf K = some k) (hk : k ≠ .list)
    {ps : List T} {its : List (List GroundTerm)} (h : PartsIts_khc c K ps its) :
    (∀ p ∈ ps, PartOK_khc c k p) ∧ (flatK_khc ps).Perm (its.map encIt_cdp) := by
  induction h with
  | nil => exact ⟨(fun _ h => by cases h), .refl _⟩
  | @elem it ps its hit _ ih =>
    obtain ⟨he, -⟩ := hit.elemOK hK hk
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact .inl he
      · exact ih.1 p hp
    · have : flatK_khc (encIt_cdp it :: ps) = encIt_cdp it :: flatK_khc ps := by
        have h := he.elem
        generalize encIt_cdp it = q at h ⊢
        cases q <;> first | rfl | cases h
      rw [this, List.map_cons]
      exact ih.2.cons _
  | @coll w s g ps its hc hg _ ih =>
    rw [enc_content_khc hK hc, ordK_ne_list_cpv hk]
    have hS : ∀ f ∈ sortK (g.map encIt_cdp), ElemOK_khc c k f := fun f hf => by
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp (mem_sortK.mp hf)
      exact ((hg it hit).elemOK hK hk).1
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact .inr ⟨_, _, _, rfl, hS⟩
      · exact ih.1 p hp
    · show (sortK (g.map encIt_cdp) ++ flatK_khc ps).Perm ((g ++ its).map encIt_cdp)
      rw [List.map_append]
      exact (sortK_perm _).append ih.2

/-- The items' keys are apart exactly where their encodings' keys are. -/
theorem keys_nodup_iff_khc {K : CollKind} {k : Kind} (hK : kindOf K = some k) (hk : k ≠ .list)
    {its : List (List GroundTerm)} (h : ∀ it ∈ its, ItemOK_khc c K it) :
    ((its.map encIt_cdp).map keyT_khc).Nodup ↔ (its.map keyIt_khc).Nodup := by
  have he : (its.map encIt_cdp).map keyT_khc = (its.map keyIt_khc).map enc := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun it hit => ((h it hit).elemOK hK hk).2
  rw [he]
  refine ⟨fun hn => nodup_of_map_khc hn, fun hn => nodup_map_khc hn fun x hx y hy hxy => ?_⟩
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hx
  obtain ⟨it', hit', rfl⟩ := List.mem_map.mp hy
  cases K with
  | map =>
    obtain ⟨a, b, s, rfl, hs, la⟩ := h it hit
    obtain ⟨a', b', s', rfl, hs', la'⟩ := h it' hit'
    exact enc_inj hs hs' la la' hxy
  | set =>
    obtain ⟨e, s, rfl, hs, le⟩ := h it hit
    obtain ⟨e', s', rfl, hs', le'⟩ := h it' hit'
    exact enc_inj hs hs' le le' hxy
  | list => cases hK; exact absurd rfl hk
  | rangeMap => cases hK

/-- **`colOf` on the items of a map's or a set's construction.** On parts that hold the items
`its`, `colOf` gives the collection of the items' encodings ordered by `ckeyF` where no two items
share a key (a map) or are equal (a set), and `bot` where two do. -/
theorem colOfF_items_khc {K : CollKind} {k : Kind} (hK : kindOf K = some k) (hk : k ≠ .list) (n : Int)
    {ps : List T} {its : List (List GroundTerm)} (h : PartsIts_khc c K ps its) :
    colOfF k n ps =
      some (if (its.map keyIt_khc).Nodup then .co k n (sortK (its.map encIt_cdp)) else .bot) := by
  obtain ⟨hps, hperm⟩ := h.flat hK hk
  have hits := h.items
  have hiff : ((flatK_khc ps).map keyT_khc).Nodup ↔ (its.map keyIt_khc).Nodup :=
    (perm_keys_nodup_khc hperm).trans (keys_nodup_iff_khc hK hk hits)
  rw [colOfF_parts_khc hk n hps]
  by_cases hn : (its.map keyIt_khc).Nodup
  · have hn' := hiff.mpr hn
    rw [ite_pos hn', ite_pos hn]
    have hS : ∀ e ∈ flatK_khc ps, ElemOK_khc c k e := fun e he => by
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp (hperm.subset he)
      exact ((hits it hit).elemOK hK hk).1
    have hS' : ∀ e ∈ its.map encIt_cdp, ElemOK_khc c k e := fun e he => hS e (hperm.symm.subset he)
    have hn'' : ((its.map encIt_cdp).map keyT_khc).Nodup := (keys_nodup_iff_khc hK hk hits).mpr hn
    rw [perm_pairwise_eq_cdp (fun _ _ => ckeyF_asym_cdp) (sortK_ok_khc hS hn') (sortK_ok_khc hS' hn'')
      (((sortK_perm _).trans hperm).trans (sortK_perm _).symm)]
  · rw [ite_neg fun h => hn (hiff.mp h), ite_neg hn]

/-- **The collection value KCore builds from the items.** A value sorted in `c` with kore.k
literals, of the kind `K` and the sort `s`, whose items are those of the parts up to order, has its
items' keys apart, and its encoding is the collection of the items' encodings ordered by `ckeyF`. -/
theorem enc_items_khc {K : CollKind} {k : Kind} (hK : kindOf K = some k) (hk : k ≠ .list)
    {its : List (List GroundTerm)} (hits : ∀ it ∈ its, ItemOK_khc c K it) {u : GroundTerm} {s : Srt}
    {Y : List (List GroundTerm)} (hu : c.sortOf u = some s) (lu : litsV u = true)
    (hc : content u = some (K, s, Y)) (hp : Y.Perm its) :
    (its.map keyIt_khc).Nodup ∧ enc u = .co k s (sortK (its.map encIt_cdp)) := by
  have he := enc_content_khc hK hc
  rw [ordK_ne_list_cpv hk] at he
  have hcan := enc_canonical hu lu
  rw [he, Canon] at hcan
  have hsY : SortedK_khc (sortK (Y.map encIt_cdp)) := hcan.1 hk
  have hS : ∀ e ∈ sortK (Y.map encIt_cdp), ElemOK_khc c k e := fun e hm => by
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp (mem_sortK.mp hm)
    exact ((hits it (hp.subset hit)).elemOK hK hk).1
  have hpm : (sortK (Y.map encIt_cdp)).Perm (its.map encIt_cdp) := (sortK_perm _).trans (hp.map _)
  have hn : ((its.map encIt_cdp).map keyT_khc).Nodup := (perm_keys_nodup_khc hpm).mp (hsY.keys hS)
  refine ⟨(keys_nodup_iff_khc hK hk hits).mp hn, ?_⟩
  rw [he, perm_pairwise_eq_cdp (fun _ _ => ckeyF_asym_cdp) hsY
    (sortK_ok_khc (fun e hm => hS e (hpm.symm.subset hm)) hn) (hpm.trans (sortK_perm _).symm)]

/-- **`colOf` against the collection value of the same items.** Where KCore's concatenation of the
parts has a value `u` (sorted in `c`, with kore.k literals, holding the parts' items up to order),
`colOf` gives `u`'s encoding. -/
theorem colOfF_coll_khc {K : CollKind} {k : Kind} (hK : kindOf K = some k) (hk : k ≠ .list)
    {ps : List T} {its : List (List GroundTerm)} (h : PartsIts_khc c K ps its) {u : GroundTerm} {s : Srt}
    {Y : List (List GroundTerm)} (hu : c.sortOf u = some s) (lu : litsV u = true)
    (hc : content u = some (K, s, Y)) (hp : Y.Perm its) : colOfF k s ps = some (enc u) := by
  obtain ⟨hn, he⟩ := enc_items_khc hK hk h.items hu lu hc hp
  rw [colOfF_items_khc hK hk s h, ite_pos hn, he]

/-- **`colOf` where two items meet**: `bot`, KCore's undefined. -/
theorem colOfF_overlap_khc {K : CollKind} {k : Kind} (hK : kindOf K = some k) (hk : k ≠ .list) (n : Int)
    {ps : List T} {its : List (List GroundTerm)} (h : PartsIts_khc c K ps its)
    (hn : ¬ (its.map keyIt_khc).Nodup) : colOfF k n ps = some .bot := by
  rw [colOfF_items_khc hK hk n h, ite_neg hn]

/-- **`colOf` on the items of a list's construction**: the list of the items' encodings in order,
the encoding of the list value of those items. -/
theorem colOfF_list_items_khc (n : Int) {ps : List T} {its : List (List GroundTerm)}
    (h : PartsIts_khc c .list ps its) : colOfF .list n ps = some (.co .list n (its.map encIt_cdp)) := by
  have key : (∀ p ∈ ps, ListPartOK_khc p) ∧ flatK_khc ps = its.map encIt_cdp := by
    induction h with
    | nil => exact ⟨(fun _ h => by cases h), rfl⟩
    | @elem it ps its hit _ ih =>
      obtain ⟨e, rfl⟩ := hit
      refine ⟨fun p hp => ?_, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact .inl rfl
        · exact ih.1 p hp
      · show encIt_cdp [e] :: flatK_khc ps = _
        rw [ih.2]; rfl
    | @coll w s g ps its hc hg _ ih =>
      rw [enc_content_khc rfl hc]
      refine ⟨fun p hp => ?_, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · refine .inr ⟨_, _, _, rfl, fun f hf => ?_⟩
          obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hf
          obtain ⟨e, rfl⟩ := hg it hit
          rfl
        · exact ih.1 p hp
      · show g.map encIt_cdp ++ flatK_khc ps = (g ++ its).map encIt_cdp
        rw [ih.2, List.map_append]
  rw [colOfF_list_parts_khc n key.1, key.2]

theorem enc_list_items_khc {u : GroundTerm} {s : Srt} {its : List (List GroundTerm)}
    (hc : content u = some (.list, s, its)) : enc u = .co .list s (its.map encIt_cdp) :=
  enc_content_khc rfl hc

end Items


/-! ## Instances -/

section Instances
open _root_.KK
open _root_.KK.Kit (sort_int ite_pos)

/-- The parts of a set's construction from the Int elements 1 and 2. -/
theorem partsIts_ex_khc : PartsIts_khc c₀ .set [encIt_cdp [iv3 1], encIt_cdp [iv3 2]] [[iv3 1], [iv3 2]] :=
  .elem ⟨_, 3, rfl, sort_int 1, rfl⟩ (.elem ⟨_, 3, rfl, sort_int 2, rfl⟩ .nil)

/-- On apart items, `colOf` is the collection of their encodings. -/
theorem colOfF_items_ex_khc :
    colOfF .set 7 [encIt_cdp [iv3 1], encIt_cdp [iv3 2]] =
      some (.co .set 7 (sortK [encIt_cdp [iv3 1], encIt_cdp [iv3 2]])) := by
  rw [colOfF_items_khc rfl (by decide) 7 partsIts_ex_khc, ite_pos (by decide)]
  rfl

/-- The parts of a set's construction from the Int element 1 twice. -/
theorem partsIts_dup_ex_khc : PartsIts_khc c₀ .set [encIt_cdp [iv3 1], encIt_cdp [iv3 1]] [[iv3 1], [iv3 1]] :=
  .elem ⟨_, 3, rfl, sort_int 1, rfl⟩ (.elem ⟨_, 3, rfl, sort_int 1, rfl⟩ .nil)

/-- On two equal elements of a set, `colOf` is `bot`. -/
theorem colOfF_overlap_ex_khc : colOfF .set 7 [encIt_cdp [iv3 1], encIt_cdp [iv3 1]] = some .bot :=
  colOfF_overlap_khc rfl (by decide) 7 partsIts_dup_ex_khc (by decide)

end Instances

/-! ## Checks -/

#check @isElemT.eval
#check @isElemT.eval_iff
#check @mkKvF.eval
#check @mkKvF.eval_iff
#check @mkColF.eval
#check @mkColF.eval_iff
#check @insEF.eval
#check @insEF.eval_iff
#check @delEF.eval
#check @delEF.eval_iff
#check @hasKeyF.eval
#check @hasKeyF.eval_iff
#check @valueOrF.eval
#check @valueOrF.eval_iff
#check @joinF.eval
#check @joinF.eval_iff
#check @colOfF.eval
#check @colOfF.eval_iff
#check @appF_eq_khc
#check @mkElF_bot_khc
#check @mkElF_of_ne_khc
#check @joinF_nil_khc
#check @joinF_bot_khc
#check @joinF_col_khc
#check @joinF_list_khc
#check @joinF_elem_khc
#check @joinF_other_khc
#check @joinF_none_khc
#check @insEF_new_khc
#check @insEF_dup_khc
#check @joinF_elems_khc
#check @joinF_parts_khc
#check @colOfF_parts_khc
#check @joinF_list_parts_khc
#check @colOfF_list_parts_khc
#check @colOfF_items_khc
#check @enc_items_khc
#check @colOfF_coll_khc
#check @colOfF_overlap_khc
#check @colOfF_list_items_khc
#check @enc_list_items_khc
#check @colOfF_items_ex_khc
#check @ev_kindNeT_khc
#check @ev_isElem_khc
#check @ev_ckeyAt_khc
#check @ev_ckeyAt_none_khc
#check @colOfF_overlap_ex_khc

open Lean in
#eval show CoreM Unit from do
  for n in [``helpColl_names, ``isElemT.eval, ``isElemT.eval_iff, ``mkKvF.eval, ``mkKvF.eval_iff, ``mkColF.eval, ``mkColF.eval_iff, ``insEF.eval, ``insEF.eval_iff, ``delEF.eval, ``delEF.eval_iff, ``hasKeyF.eval, ``hasKeyF.eval_iff, ``valueOrF.eval, ``valueOrF.eval_iff, ``joinF.eval, ``joinF.eval_iff, ``colOfF.eval, ``colOfF.eval_iff, ``appF_eq_khc, ``mkElF_bot_khc, ``mkElF_of_ne_khc, ``joinF_nil_khc, ``joinF_bot_khc, ``joinF_col_khc, ``joinF_list_khc, ``joinF_elem_khc, ``joinF_other_khc, ``joinF_none_khc, ``insEF_new_khc, ``insEF_dup_khc, ``joinF_elems_khc, ``joinF_parts_khc, ``colOfF_parts_khc, ``joinF_list_parts_khc, ``colOfF_list_parts_khc, ``colOfF_items_khc, ``enc_items_khc, ``colOfF_coll_khc, ``colOfF_overlap_khc, ``colOfF_list_items_khc, ``enc_list_items_khc, ``colOfF_items_ex_khc, ``colOfF_overlap_ex_khc] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
