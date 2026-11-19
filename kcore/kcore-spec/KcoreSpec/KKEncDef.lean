import KcoreSpec.KKEnc

/-!
# An object definition as a `kore.k` definition

`encDef d` is `some E` exactly when `encodable d`: the conjunction of one Bool per condition below,
each computed from `d`'s data and none reading `d.hooks`. `E` holds `d`'s subsorts, the clauses of
its functions (the sort predicates among them) and its rules, each term written by `encTerm`.

`encTerm` reads an application as KCore's `EvalTerm` and `PatVal` read it, in their order: a
constructor is `ap`; an interpreted symbol that is the unit, element or concatenation symbol of the
library's `Map`, `Set` or `List`, or a parameter symbol whose `impl` is one, builds a collection
(`cb`, with nested concatenations of the same collection flattened, units dropped, elements as
`kv` and `el`, and for a `Map` or `Set` the elements before the other parts); another interpreted
symbol is `hk` with `kore.k`'s operation code (`hookOp`), or for `=/=Bool` the composition of
two (`derivedHook`); a function of `allFns` is `ap`, which `kore.k` calls since its label is among
`E.fns`. Anything else has no `kore.k` form.

The conditions (`none` where one fails):
- C1 `ovlsOK`: no overloading symbol; `kore.k` has no normal forms of overloads.
- C2 `paramsOK`: every parameter symbol is a collection symbol: its `impl` is the unit, element or
  concatenation symbol of the library's `Map`, `Set` or `List`, and its result sort a collection
  sort of that kind (a cell collection). A parameter without `impl` has no value at the member
  `kore.k` is; its applications are refused rather than written as an undefined operation.
- C3 `appsOK`: every application in a left side, `requires` or right side has a `kore.k` form, a
  collection symbol with its arity.
- C4 `headsOK`: no constructor is a label of `allFns` (`kore.k` decides constructor or function by
  the label's presence among the functions), and no symbol `kore.k` reads as an operation
  (`hookCodes`, `derivedHook`) is either.
- C5 `litsOK`: every literal of a term is an Int at `Int`, a Bool at `Bool` or a token, and no
  value of a sort the definition's signatures or subsorts name holds another literal: the library
  maps no sort to a carrier, and no signature, collection or subsort names `Float`.
- C7 `subsortsOK`: the subsort list is irreflexive and transitive: `kore.k`'s `leq` computes the
  closure of the list it is given and ends only on an acyclic one, and KCore's `sortOf` reads the
  list itself.
- C8 `colPatsOK`: in a left side, a `Map` or `Set` pattern has at most one part that is not an
  element, and no alias stands directly over an element: `kore.k`'s `matchCol` takes element
  patterns in turn and the one other part last.
- C10 `asOK`: an alias occurs only in a left side; `eval` has no equation for `as`.
- C11 `ensOK`: every ensures has a `kore.k` form, of C3's and C5's kind, without an alias; it is
  written as `en (rhs) (ensures)` at the top of its right side, and `encTerm` writes `en` nowhere
  else.
- C12 `shapesOK`: every rule and clause has the fields `rl` and `cl` hold.
- C13 `collFormOK`: the definition's collections are what `cb` and `co` can hold, which carry a
  kind and a sort and nothing else: each collection of the definition has its unit, element and
  concatenation declared at the collection's sorts (`Faithful.collsOK`), and a collection sort
  holds collections only: no domain value (`Faithful.collSortsOK`), no constructor's result and no
  upper sort of a subsort pair is one.
-/

set_option autoImplicit false

namespace KCore.KK

deriving instance Repr for Cl, Rl, D

/-! ## kore.k's readings of a symbol -/

/-- `hookOp`'s operation codes of KCore's interpreted symbols (`kore.k`'s comment above
`strictHook`). -/
def hookCodes : List (Sym × Int) :=
  [(intAdd, 1), (intSub, 2), (intMul, 3), (intTDiv, 4), (intTMod, 5),
   (intLt, 10), (intLe, 11), (intGt, 12), (intGe, 13), (intEq, 14), (intNe, 15),
   (boolAnd, 20), (boolOr, 21), (boolNot, 22), (boolEq, 23), (kIte, 30),
   (mapLookup, 40), (mapLookupOrDefault, 41), (mapUpdate, 42), (mapRemove, 43), (mapInKeys, 44),
   (mapSize, 45), (setIn, 50), (setSize, 51), (setUnion, 52), (listSize, 60),
   (kEq, 70), (kNe, 71), (stringEq, 80), (stringLt, 81)]

/-- The operation code of an interpreted symbol, if `kore.k` has one. -/
def opOf (f : Sym) : Option Int := (hookCodes.find? (·.1 == f)).map (·.2)

/-- An interpreted symbol `kore.k` has no code for, written through codes it has: `=/=Bool` is
`notBool (B1 ==Bool B2)`, the equation BOOL states for it (`domains.md`: `rule B1:Bool =/=Bool
B2:Bool => notBool (B1 ==Bool B2)`). Both operations are strict, so the composition is undefined
exactly where an argument is. -/
def derivedHook (f : Sym) (as : List T) : Option T :=
  if f == boolNe then some (.hk 22 [.hk 23 as]) else none

/-- KCore's `=/=Bool` is the negation of its `==Bool`, at every pair of Bool values. -/
example : ∀ a b : Bool, hook boolNe [.dv Srt.bool (.bool a), .dv Srt.bool (.bool b)] =
    (hook boolEq [.dv Srt.bool (.bool a), .dv Srt.bool (.bool b)]).map
      (·.bind fun v => hook boolNot [v] |>.join) := by decide +kernel

/-- The part a collection symbol plays. -/
inductive CRole | unit | elem | concat
  deriving DecidableEq, Repr

/-- `kore.k`'s kind of a library collection kind; a range map has none. -/
def kindOf : CollKind → Option Kind
  | .map => some .map
  | .set => some .set
  | .list => some .list
  | .rangeMap => none

/-- The role of `g` in the collection `k`. -/
def roleIn (k : CollSig) (g : Sym) : Option CRole :=
  if g == k.unit then some .unit else if g == k.elem then some .elem
  else if g == k.concat then some .concat else none

/-- `g` as a symbol of the library's `Map`, `Set` or `List`: the kind, the collection's sort and
the role. -/
def libCollOf (g : Sym) : Option (Kind × Srt × CRole) :=
  builtinColls.findSome? fun k => (kindOf k.kind).bind fun kd => (roleIn k g).map (kd, k.sort, ·)

/-- `f` as a collection symbol of `d`: an interpreted symbol of the library's collections, or a
parameter symbol whose `impl` is one, at the parameter's result sort. -/
def collSymOf (d : Semantics) (f : Sym) : Option (Kind × Srt × CRole) :=
  if isHook f then libCollOf f
  else match d.lookupParam f with
    | some k => k.impl.bind fun g => (libCollOf g).map fun (kd, _, r) => (kd, k.sig.result, r)
    | none => none

/-- A literal as `kore.k` writes it, given a form for a literal it has none for. -/
def encLitWith (other : Srt → Lit → Option T) : Srt → Lit → Option T
  | Srt.int, .int i => some (.iv i)
  | Srt.bool, .bool b => some (.bv b)
  | s, .tok x => some (.tk s x)
  | s, l => other s l

/-- A literal `kore.k` has a form for. -/
def encLit : Srt → Lit → Option T := encLitWith fun _ _ => none

/-- An element of a collection value or construction. -/
def isElemT : T → Bool
  | .kv _ _ | .el _ => true
  | _ => false

/-- A construction's parts: for a `Map` or a `Set`, the elements before the other parts. -/
def orderParts (k : Kind) (ps : List T) : List T :=
  if k == .list then ps else ps.filter isElemT ++ ps.filter (!isElemT ·)

/-! ## Terms -/

/-- An application of `f`, read as `EvalTerm` and `PatVal` read it, from the forms of its
arguments (`args`) and, for a collection symbol, the parts they build (`parts`). -/
def readApp (d : Semantics) (f : Sym) (args : Option (List T)) (parts : Option (List T)) : Option T :=
  if d.isCtor f then args.map (.ap f)
  else match collSymOf d f with
    | some (k, s, _) => parts.map fun ps => .cb k s (orderParts k ps)
    | none =>
      if isHook f then match opOf f with
        | some o => args.map (.hk o)
        | none => args.bind (derivedHook f)
      else if d.isParam f then none
      else if (d.lookupFn f).isSome then args.map (.ap f)
      else none

section
variable (d : Semantics) (lit : Srt → Lit → Option T)

mutual
/-- A term of a rule or a clause as a `kore.k` term, literals by `lit`. -/
def encTermWith : Term → Option T
  | .var i => some (.vr i)
  | .dv s l => lit s l
  | .inj a b t => (encTermWith t).map (.ij a b)
  | .as t i => (encTermWith t).map (.as · i)
  | .app f ts =>
      readApp d f (encTermsWith ts) ((collSymOf d f).bind fun (k, s, r) => encCollWith k s r ts)
  termination_by structural t => t
/-- Terms, in order. -/
def encTermsWith : List Term → Option (List T)
  | [] => some []
  | t :: ts => match encTermWith t, encTermsWith ts with
    | some p, some ps => some (p :: ps)
    | _, _ => none
  termination_by structural ts => ts
/-- The parts a collection symbol of the role `r` builds from its arguments: none for the unit,
one element, or the parts of both arguments of a concatenation. -/
def encCollWith (k : Kind) (s : Srt) (r : CRole) : List Term → Option (List T)
  | [] => if r == .unit then some [] else none
  | [x] => if r == .elem && k != .map then (encTermWith x).map fun p => [.el p] else none
  | [a, v] =>
      if r == .elem && k == .map then
        match encTermWith a, encTermWith v with
        | some p, some q => some [.kv p q]
        | _, _ => none
      else if r == .concat then
        match encPartWith k s a, encPartWith k s v with
        | some ps, some qs => some (ps ++ qs)
        | _, _ => none
      else none
  | _ :: _ :: _ :: _ => none
  termination_by structural ts => ts
/-- An argument of a concatenation: the parts of a nested construction of the same collection,
else the argument itself as one part. -/
def encPartWith (k : Kind) (s : Srt) : Term → Option (List T)
  | .app f ts =>
      match d.isCtor f, collSymOf d f with
      | false, some (k', s', r) =>
          if k' == k && s' == s then encCollWith k s r ts
          else (readApp d f (encTermsWith ts) (encCollWith k' s' r ts)).map ([·])
      | _, _ =>
          (readApp d f (encTermsWith ts)
            ((collSymOf d f).bind fun (k', s', r) => encCollWith k' s' r ts)).map ([·])
  | .var i => some [.vr i]
  | .dv s' l => (lit s' l).map ([·])
  | .inj a b t => (encTermWith t).map fun p => [.ij a b p]
  | .as t i => (encTermWith t).map fun p => [.as p i]
  termination_by structural t => t
end

end

/-- A term of a rule or a clause as a `kore.k` term. -/
def encTerm (d : Semantics) : Term → Option T := encTermWith d encLit

/-! ## The conditions -/

/-- No alias in the term. -/
def asFree : Term → Bool
  | .var _ | .dv _ _ => true
  | .inj _ _ t => asFree t
  | .as _ _ => false
  | .app _ ts => asFreeL ts
where
  asFreeL : List Term → Bool
    | [] => true
    | t :: ts => asFree t && asFreeL ts

/-- Every literal of the term has a `kore.k` form. -/
def litsIn : Term → Bool
  | .var _ => true
  | .dv s l => (encLit s l).isSome
  | .inj _ _ t | .as t _ => litsIn t
  | .app _ ts => litsInL ts
where
  litsInL : List Term → Bool
    | [] => true
    | t :: ts => litsIn t && litsInL ts

mutual
/-- In an encoded left side: every `Map` or `Set` pattern has at most one part that is not an
element, and no part is an alias over an element. -/
def colPatOK : T → Bool
  | .ap _ as | .hk _ as => colPatsOKL as
  | .ij _ _ t | .as t _ | .el t => colPatOK t
  | .kv a v | .en a v => colPatOK a && colPatOK v
  | .cb k _ ps =>
      (k == .list || (ps.filter (!isElemT ·)).length ≤ 1 && ps.all fun
        | .as p _ => !isElemT p
        | _ => true) && colPatsOKL ps
  | .co _ _ es => colPatsOKL es
  | .iv _ | .bv _ | .tk _ _ | .vr _ | .bot => true
  termination_by structural t => t
def colPatsOKL : List T → Bool
  | [] => true
  | t :: ts => colPatOK t && colPatsOKL ts
  termination_by structural ts => ts
end

/-- The left sides of `d`: rules' left sides and clauses' argument patterns. -/
def lhsTerms (d : Semantics) : List Term :=
  d.rules.map (·.lhs) ++ d.allFns.flatMap fun fn => fn.clauses.flatMap (·.pats)

/-- The `requires` and right sides of `d`'s rules and clauses. -/
def rhsTerms (d : Semantics) : List Term :=
  d.rules.flatMap (fun r => r.req.toList ++ [r.rhs]) ++
    d.allFns.flatMap fun fn => fn.clauses.flatMap fun cl => cl.req.toList ++ [cl.rhs]

/-- The ensures of `d`'s rules and clauses. -/
def ensTerms (d : Semantics) : List Term :=
  d.rules.filterMap (·.ens) ++ d.allFns.flatMap fun fn => fn.clauses.filterMap (·.ens)

/-- The function labels and constructors of `d`. -/
def fnLabels (d : Semantics) : List Sym := d.allFns.map (·.label)

/-- C1. -/
def ovlsOK (d : Semantics) : Bool := d.ovls.isEmpty

/-- C2. -/
def paramsOK (d : Semantics) : Bool :=
  d.params.all fun p => match p.impl.bind libCollOf, d.collOf p.sig.result with
    | some (kd, _, _), some k => kindOf k.kind == some kd
    | _, _ => false

/-- C3: literals are read as any form here, so that only the applications decide. -/
def appsOK (d : Semantics) : Bool :=
  (lhsTerms d ++ rhsTerms d).all fun t => (encTermWith d (encLitWith fun _ _ => some .bot) t).isSome

/-- C4. -/
def headsOK (d : Semantics) : Bool :=
  (fnLabels d).all (fun f => !d.isCtor f) &&
    (boolNe :: hookCodes.map (·.1)).all fun f => !d.isCtor f && !(fnLabels d).contains f

/-- The sorts the signatures, collections and subsorts of `d` name. -/
def sigSorts (d : Semantics) : List Srt :=
  d.ctorSigs.flatMap (fun k => k.result :: k.args) ++
    d.allFns.flatMap (fun fn => fn.result :: fn.args) ++
    d.params.flatMap (fun p => p.sig.result :: p.sig.args) ++
    d.allColls.flatMap (fun k => k.sort :: k.key :: k.val.toList) ++
    d.subsorts.flatMap fun (a, b) => [a, b]

/-- C5. -/
def litsOK (d : Semantics) : Bool :=
  (lhsTerms d ++ rhsTerms d).all litsIn && d.lib.carriers.isEmpty && !(sigSorts d).contains Srt.float

/-- C7. -/
def subsortsOK (d : Semantics) : Bool :=
  d.subsorts.all (fun (a, b) => a != b) &&
    d.subsorts.all fun (a, b) => d.subsorts.all fun (b', c) => b' != b || d.subsorts.contains (a, c)

/-- C8. -/
def colPatsOK (d : Semantics) : Bool :=
  (lhsTerms d).all fun t => match encTerm d t with
    | some p => colPatOK p
    | none => true

/-- C10. -/
def asOK (d : Semantics) : Bool := (rhsTerms d).all asFree

/-- C11. -/
def ensOK (d : Semantics) : Bool := (ensTerms d).all fun e => (encTerm d e).isSome && asFree e

/-- C13. -/
def collFormOK (d : Semantics) : Bool :=
  Faithful.collsOK d && Faithful.collSortsOK d &&
    d.ctorSigs.all (fun k => (d.collOf k.result).isNone) &&
    d.subsorts.all fun p => (d.collOf p.2).isNone

/-- Every condition: `encDef d` is `some` exactly here (`encDef_isSome`). -/
def encodable (d : Semantics) : Bool :=
  ovlsOK d && paramsOK d && appsOK d && headsOK d && litsOK d && subsortsOK d && colPatsOK d &&
    asOK d && ensOK d && shapesOK d && collFormOK d

/-! ## The definition -/

/-- A term, `bot` where it has no form (never under `encodable`). -/
def encT (d : Semantics) (t : Term) : T := (encTerm d t).getD .bot

/-- A right side with its ensures. -/
def encRhs (d : Semantics) (rhs : Term) : Option Term → T
  | some e => .en (encT d rhs) (encT d e)
  | none => encT d rhs

/-- A `requires`: `\top` is `bv(true)`. -/
def encReq (d : Semantics) : Option Term → T
  | some t => encT d t
  | none => .bv true

/-- A clause. Its priority is KCore's (200 for `[owise]`), so `owise` is false. -/
def encCl (d : Semantics) (cl : Clause) : Cl :=
  ⟨cl.prio, false, cl.pats.map (encT d), encReq d cl.req, encRhs d cl.rhs cl.ens⟩

/-- A rule, as a clause. -/
def encRl (d : Semantics) (r : Rule) : Rl :=
  ⟨r.prio, false, encT d r.lhs, encReq d r.req, encRhs d r.rhs r.ens⟩

/-- The `kore.k` definition of `d`, where `d` is `encodable`. -/
def encDef (d : Semantics) : Option D :=
  if encodable d then
    some ⟨d.subsorts.map fun (a, b) => ((a : Int), (b : Int)),
      d.allFns.map (fun fn => ((fn.label : Int), fn.clauses.map (encCl d))),
      d.rules.map (encRl d)⟩
  else none

theorem encDef_isSome (d : Semantics) : (encDef d).isSome = encodable d := by
  unfold encDef; split <;> simp_all

set_option smartUnfolding false in
/-- `encDef` reads no interpretation. -/
theorem encDef_withHooks (d : Semantics) (H : HookParams) : encDef (d.withHooks H) = encDef d := rfl

/-- C13 reads no interpretation. -/
example (d : Semantics) (H : HookParams) : collFormOK (d.withHooks H) = collFormOK d := rfl

/-- What C13 states, read off `encodable`. -/
theorem encodable_colls_c13 {d : Semantics} (h : encodable d = true) :
    Faithful.collsOK d = true ∧ Faithful.collSortsOK d = true ∧
      (∀ k ∈ d.ctorSigs, d.collOf k.result = none) ∧ (∀ p ∈ d.subsorts, d.collOf p.2 = none) := by
  simp only [encodable, Bool.and_eq_true] at h
  have h13 := h.2
  simp only [collFormOK, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at h13
  exact ⟨h13.1.1.1, h13.1.1.2, h13.1.2, h13.2⟩

open Faithful Faithful.Model in
/-- `coreOK` gives C13: `collsOK` and `collSortsOK` are conjuncts of `faithCoreOK`, and `genWf`
makes every constructor's result and every subsort pair's upper sort a constructor sort, which is
no collection sort. -/
theorem collFormOK_of_coreOK {c : Semantics} (h : c.coreOK = true) : collFormOK c = true := by
  obtain ⟨-, hf, -, -, -⟩ := Semantics.coreOK_parts h
  unfold Semantics.faithCoreOK at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hg⟩, hcs⟩, hco⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hf
  unfold genWf at hg
  simp only [Bool.and_eq_true, List.all_eq_true] at hg
  have hcons : ∀ s ∈ consSorts c, (c.collOf s).isNone = true := fun s hs => by
    exact (hg.1.1.2 s hs).1.1.1.2
  simp only [collFormOK, hcs, hco, Bool.and_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun k hk => hcons _ (List.contains_iff_mem.mp (hg.1.1.1.1 k hk)),
    fun p hp => hcons _ (List.contains_iff_mem.mp (hg.1.1.1.2 p hp).1)⟩

end KCore.KK
