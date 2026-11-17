/-
  KCore. Matching and evaluation (KCORE-SPEC.md). Frozen layer.

  1. **Matching is denotational.** A pattern matches a value v under σ when it denotes v under
     σ: `PatVal c σ p v`. With map patterns (`K |-> V M`, several matches) and the non-linear
     patterns kompile emits (a key bound in the k cell and matched in a map), a matching
     algorithm belongs in the checked layer, proved equal to this relation (MatchSound.lean,
     MatchComplete.lean), as `step_iff` does for evaluation. σ ranges over well-sorted
     substitutions (`WellSorted`), as a matching-logic valuation ranges over the sorts of the
     variables.

  2. **Evaluation states definedness** (`EvalTerm c σ t r`, `r : Option GroundTerm`; `none` is
     "undefined", ⊥ in matching logic). `requires` needs it: a clause applies when its
     patterns match and its `requires` evaluates to `true`; it does not apply when they do not
     match, or its `requires` evaluates to `false` *or is undefined* (the KORE premise is
     `\equals(req, true)`, false when req is ⊥). "Is undefined" must be derivable positively for
     the reading of priorities (a clause decides where no clause of a smaller priority applies)
     to stay an inductive definition, so undefinedness is a result: an interpreted hook may be
     undefined (`/Int` by zero, a lookup off the keys), undefinedness propagates through
     constructors, hooks and calls (strictness). A clause that decides and whose `ensures` is not
     `true` gives no value (`Eval.ensFails`). A function all of whose clauses fail has its
     rest there (`Eval.rest`): the interpretation's value (`Semantics.fnRest`), undefined where it
     gives none. A non-terminating evaluation has no derivation at all.

  3. **Clauses of one priority are unordered.** `Eval.clause` reads no order among the clauses:
     any clause that applies, with no clause of a smaller priority applying, gives a result. Two
     clauses of one priority, or two matches of one clause, may both apply; that they then give
     one result is a property of the definition (`Coherent`, `Eval.functional`,
     EvalFunctional.lean), not part of the relation.

  `lookupFn` finds the user's functions and the generated sort predicates (`Semantics.allFns`,
  Core.lean).
-/
import KcoreSpec.Hooks
import KcoreSpec.DefinitionWf

set_option autoImplicit false

namespace KCore

abbrev Subst := List (Nat × GroundTerm)

namespace Semantics
variable (c : Semantics)

def isCtor (f : Sym) : Bool := (lookupSig c.ctorSigs f).isSome

/-- σ gives each variable of the list a value of its sort. -/
def WellSorted (vars : List Srt) (σ : Subst) : Prop :=
  ∀ (i : Nat) (s : Srt), vars[i]? = some s → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some s

/-- A function of the definition: the user's, or a generated sort predicate (`allFns`). -/
def lookupFn (f : Sym) : Option Fn := (NatMap.ofList (c.allFns.map fun fn => (fn.label, fn))).find f

/-- `lookupFn` (by the trie of the functions' numbers) is the first function of that number. -/
theorem lookupFn_eq (f : Sym) : c.lookupFn f = c.allFns.find? (·.label == f) := by
  rw [lookupFn, NatMap.find_ofList, List.find?_map]
  simp only [Function.comp_def]
  cases c.allFns.find? (·.label == f) <;> rfl

end Semantics

/-- `f` is an interpreted hooked symbol. -/
def isHook (f : Sym) : Bool := (hook f []).isSome

namespace Semantics
variable (c : Semantics)

/-- The interpretation's value of the interpreted symbol `f` at `vs`, kept only when it has `f`'s
result sort (`hookSigs`). -/
def fallback (f : Sym) (vs : List GroundTerm) : Option GroundTerm :=
  match lookupSig hookSigs f with
  | some k => (c.hooks.app f vs).filter fun v => c.sortOf v == some k.result
  | none => none

/-- An interpreted symbol's result: `hook`'s, and where `hook` gives no value at a silent point
(`silent`), the interpretation's (`fallback`). -/
def hookRes (f : Sym) (vs : List GroundTerm) : Option (Option GroundTerm) :=
  if silent f vs then (hook f vs).map fun r => r.or (c.fallback f vs) else hook f vs

variable {c}

/-- A value of `hook` is the result, whatever the table and the interpretation. -/
theorem hookRes_of_value {f : Sym} {vs : List GroundTerm} {v : GroundTerm}
    (h : hook f vs = some (some v)) : c.hookRes f vs = some (some v) := by
  unfold hookRes; split <;> simp [h]

/-- Where `vs` is no silent point of `f`, the result is `hook`'s. -/
theorem hookRes_of_not_silent {f : Sym} {vs : List GroundTerm} (h : silent f vs = false) :
    c.hookRes f vs = hook f vs := by
  unfold hookRes; rw [h]; rfl

/-- Off the keys of `silentTable`, the result is `hook`'s. -/
theorem hookRes_of_notKey {f : Sym} (h : silentKey f = false) (vs : List GroundTerm) :
    c.hookRes f vs = hook f vs :=
  hookRes_of_not_silent (silent_of_not_silentKey h vs)

/-- At a silent point where `hook` gives no value, the result is the fallback. -/
theorem hookRes_of_silent {f : Sym} {vs : List GroundTerm} (he : hook f vs = some none)
    (hs : silent f vs = true) : c.hookRes f vs = some (c.fallback f vs) := by
  unfold hookRes; rw [hs, he]; rfl

/-- Under the interpretation that gives nothing (`HookParams.none`), the result is `hook`'s. -/
theorem hookRes_withHooks_none (f : Sym) (vs : List GroundTerm) :
    (c.withHooks HookParams.none).hookRes f vs = hook f vs := by
  unfold hookRes
  split
  · have hf : (c.withHooks HookParams.none).fallback f vs = none := by
      unfold fallback; split <;> rfl
    rw [hf]
    cases hook f vs with
    | none => rfl
    | some r => cases r <;> rfl
  · rfl

/-- The result is defined exactly where `hook` is: at the interpreted symbols. -/
theorem hookRes_eq_none_iff {f : Sym} {vs : List GroundTerm} :
    c.hookRes f vs = none ↔ hook f vs = none := by
  unfold hookRes; split <;> simp

/-- The result is `hook`'s, except at a silent point where `hook` gives no value: the fallback. -/
theorem hookRes_cases {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
    (h : c.hookRes f vs = some r) :
    (hook f vs = some r ∧ (r = none → silent f vs = false)) ∨
      (hook f vs = some none ∧ silent f vs = true ∧ r = c.fallback f vs) := by
  unfold hookRes at h
  cases hs : silent f vs
  · rw [hs] at h; refine .inl ⟨by simpa using h, fun hr => rfl⟩
  · rw [hs] at h
    simp only [if_true, Option.map_eq_some_iff] at h
    obtain ⟨o, ho, rfl⟩ := h
    cases o with
    | some v => exact .inl ⟨ho, fun h => by cases h⟩
    | none => exact .inr ⟨ho, rfl, rfl⟩

/-- A fallback has the interpreted symbol's result sort. -/
theorem fallback_sorted {f : Sym} {vs : List GroundTerm} {v : GroundTerm} {k : CtorSig}
    (hk : lookupSig hookSigs f = some k) (h : c.fallback f vs = some v) : c.sortOf v = some k.result := by
  unfold fallback at h
  rw [hk] at h
  simp only [Option.filter_eq_some_iff, beq_iff_eq] at h
  exact h.2

/-- `hook`'s result, where it is no ⊥ at a silent point, is the result. -/
theorem hookRes_of_hook {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
    (h : hook f vs = some r) (hs : r = none → silent f vs = false) : c.hookRes f vs = some r := by
  cases r with
  | some v => exact hookRes_of_value h
  | none => rw [hookRes_of_not_silent (hs rfl), h]

/-- An interpreted symbol has a result at every argument list. -/
theorem hookRes_some {f : Sym} (h : isHook f = true) (vs : List GroundTerm) : ∃ o, c.hookRes f vs = some o := by
  cases he : c.hookRes f vs with
  | some o => exact ⟨o, rfl⟩
  | none =>
    rw [hookRes_eq_none_iff] at he
    unfold isHook hook at h; unfold hook at he
    cases hf : hookTrie.find f with
    | none => rw [hf] at h; simp at h
    | some g => rw [hf] at he; cases he

end Semantics

/-- Where every clause of `fn` fails at values `vs` of its argument sorts: the interpretation's
value of `fn` there, kept only when it has `fn`'s result sort; undefined where it gives none, and at
argument lists not of `fn`'s sorts, which no well-sorted term applies it to. The equations of a
function say what it is where a clause applies and nothing elsewhere, so the value there is the
interpretation's (a function with no clause has it at every argument list of its sorts). -/
def Semantics.fnRest (c : Semantics) (fn : Fn) (vs : List GroundTerm) : Option GroundTerm :=
  (c.hooks.app fn.label vs).filter fun v => c.sortsOf vs == some fn.args && c.sortOf v == some fn.result

/-- A rest is at arguments of the function's sorts, and has its result sort. -/
theorem Semantics.fnRest_spec {c : Semantics} {fn : Fn} {vs : List GroundTerm} {v : GroundTerm}
    (h : c.fnRest fn vs = some v) :
    c.hooks.app fn.label vs = some v ∧ c.sortsOf vs = some fn.args ∧ c.sortOf v = some fn.result := by
  unfold Semantics.fnRest at h
  simp only [Option.filter_eq_some_iff, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- A rest has the function's result sort. -/
theorem Semantics.fnRest_sorted {c : Semantics} {fn : Fn} {vs : List GroundTerm} {v : GroundTerm}
    (h : c.fnRest fn vs = some v) : c.sortOf v = some fn.result :=
  (Semantics.fnRest_spec h).2.2

/-- Under the interpretation that gives nothing (`HookParams.none`), every rest is undefined. -/
theorem Semantics.fnRest_withHooks_none (c : Semantics) (fn : Fn) (vs : List GroundTerm) :
    (c.withHooks HookParams.none).fnRest fn vs = none := rfl

namespace Semantics
variable (c : Semantics)

/-- The parameter symbol f's declaration (by the trie of their numbers). -/
def lookupParam (f : Sym) : Option ParamSig :=
  (NatMap.ofList (c.params.map fun k => (k.sig.name, k))).find f

theorem lookupParam_eq (f : Sym) : c.lookupParam f = c.params.find? (·.sig.name == f) := by
  rw [lookupParam, NatMap.find_ofList, List.find?_map]
  simp only [Function.comp_def]
  cases c.params.find? (·.sig.name == f) <;> rfl

/-- `f` is a parameter symbol of `c`. -/
def isParam (f : Sym) : Bool := (c.lookupParam f).isSome

/-- The hooks that hold or pass on their arguments as they are: the unit, element and
concatenation symbols of the library's collections (Map, Set, List, range maps) and `ite`. -/
def rawArgHooks : List Sym := patternHooks ++ collPatternHooks ++ [rmUnit, rmElem, rmConcat, kIte]

/-- The arguments the registry hook g reads: a collection's hooks and `ite` (`rawArgHooks`) the values themselves, which they hold as they are; every other hook the library's values, a
literal of a sort hooked to a library carrier as that carrier's literal (`toLib`). -/
def libArgs (g : Sym) (vs : List GroundTerm) : List GroundTerm :=
  if rawArgHooks.contains g then vs else vs.map (GroundTerm.toLib c.lib)

/-- A collection's hook reads its arguments as they are. -/
theorem libArgs_coll {g : Sym} (h : rawArgHooks.contains g = true) (vs : List GroundTerm) : c.libArgs g vs = vs := by
  unfold libArgs; rw [if_pos h]

/-- Without carriers, a hook reads the arguments as they are. -/
theorem libArgs_nil (h : c.lib.carriers = []) (g : Sym) (vs : List GroundTerm) : c.libArgs g vs = vs := by
  unfold libArgs; split
  · rfl
  · conv => rhs; rw [← List.map_id vs]
    exact List.map_congr_left fun v _ => GroundTerm.toLib_nil h v

/-- The value of the parameter symbol f at `vs`: the registry hook's (`impl = some g`, its result
`hookRes` at the arguments it reads, `libArgs`, so at a silent point of g the
interpretation's value of g; a collection it builds is one of f's result sort, `_AccountCellMap_`
building an `AccountCellMap`, and a literal of the carrier of f's result sort one of that sort,
`asSort`) or the interpretation's
(`impl = none`; at an open generator, `raw`, the interpretation's answer, and where it gives none
the raw application `.ctor f vs`), kept only when it has f's declared result sort. -/
def paramVal (f : Sym) (vs : List GroundTerm) : Option GroundTerm :=
  match c.lookupParam f with
  | none => none
  | some k =>
    (match k.impl with
      | some g => (c.hookRes g (c.libArgs g vs)).join.map (GroundTerm.asSort c.lib k.sig.result)
      | none => if k.raw then some ((c.hooks.app f vs).getD (.ctor f vs)) else c.hooks.app f vs).filter
        fun v => c.sortOf v == some k.sig.result

/-- The parameters' signatures, looked up by number, are their declarations'. -/
theorem lookupSig_params (f : Sym) :
    lookupSig (c.params.map (·.sig)) f = (c.lookupParam f).map (·.sig) := by
  rw [lookupSig_eq, lookupParam_eq, List.find?_map]
  rfl

theorem lookupSig_params_of_not {f : Sym} (h : c.isParam f = false) :
    lookupSig (c.params.map (·.sig)) f = none := by
  rw [lookupSig_params]
  unfold isParam at h
  cases hk : c.lookupParam f with
  | none => rfl
  | some k => rw [hk] at h; cases h

/-- Without carriers, `paramVal` is its text before carriers: the hook at the arguments, a
collection it builds of f's result sort. -/
theorem paramVal_nil (h : c.lib.carriers = []) (f : Sym) (vs : List GroundTerm) :
    c.paramVal f vs = match c.lookupParam f with
      | none => none
      | some k =>
        (match k.impl with
          | some g => (c.hookRes g vs).join.map (GroundTerm.withSort k.sig.result)
          | none => if k.raw then some ((c.hooks.app f vs).getD (.ctor f vs)) else c.hooks.app f vs).filter
            fun v => c.sortOf v == some k.sig.result := by
  have h1 : ∀ g, c.libArgs g vs = vs := fun g => c.libArgs_nil h g vs
  have h2 : GroundTerm.asSort c.lib = fun s => GroundTerm.withSort s := by
    funext s v; exact GroundTerm.asSort_of_self (Lib.carrier_nil _ h s) v
  unfold paramVal; simp only [h1, h2]

/-- A parameter's value has its declared result sort. -/
theorem paramVal_sorted {f : Sym} {vs : List GroundTerm} {v : GroundTerm}
    (h : c.paramVal f vs = some v) : ∃ k, c.lookupParam f = some k ∧ c.sortOf v = some k.sig.result := by
  unfold paramVal at h
  cases hk : c.lookupParam f with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k =>
    rw [hk] at h
    refine ⟨k, rfl, ?_⟩
    simp only at h
    revert h
    generalize (match k.impl with
      | some g => (c.hookRes g (c.libArgs g vs)).join.map (GroundTerm.asSort c.lib k.sig.result)
      | none => if k.raw then some ((c.hooks.app f vs).getD (.ctor f vs)) else c.hooks.app f vs) = o
    intro h
    cases o with
    | none => exact absurd h (by simp)
    | some w =>
      simp only [Option.filter] at h
      by_cases hw : (c.sortOf w == some k.sig.result) = true
      · rw [if_pos hw] at h; cases h; exact beq_iff_eq.mp hw
      · rw [if_neg hw] at h; cases h

/-- A collection pattern symbol: the library's set and list symbols (`.Set`, `SetItem`, `_Set_`,
`.List`, `ListItem`, `_List_`, `collPatternHooks`), or a parameter implemented by a map pattern
symbol or by one of those (a cell map's `.AccountCellMap`, `AccountCellMapItem`,
`_AccountCellMap_`, a cell set's `TaskCellSetItem`, `_TaskCellSet_`); not one of the map pattern
symbols, which `PatVal.hook` reads. -/
def isCollPat (f : Sym) : Bool :=
  !patternHooks.contains f && if isHook f then collPatternHooks.contains f else
    match c.lookupParam f with
    | some k => match k.impl with
      | some g => patternHooks.contains g || collPatternHooks.contains g
      | none => false
    | none => false

theorem isCollPat_of_hook {f : Sym} (h : patternHooks.contains f = true) : c.isCollPat f = false := by
  unfold isCollPat; rw [h]; rfl

/-- The value a collection pattern symbol builds from its arguments' values: the library symbol's
(`hook`), or the parameter's (`paramVal`, of the collection's sort), read in the order `EvalTerm`
reads a symbol, so that the pattern, read as a term, has the same value. -/
def collVal (f : Sym) (vs : List GroundTerm) : Option GroundTerm :=
  if isHook f then (hook f vs).join else c.paramVal f vs

/-- An overloading symbol of `c` (`ovls`) of no other kind: not a constructor, an interpreted
hook, a parameter symbol or a function, which are read first. Its applications denote normal
forms (`norm`). -/
def isOvl (f : Sym) : Bool :=
  !c.isCtor f && !isHook f && !c.isParam f && (c.lookupFn f).isNone && (c.lookupOvl f).isSome

theorem isOvl_parts {f : Sym} (h : c.isOvl f = true) :
    c.isCtor f = false ∧ isHook f = false ∧ c.isParam f = false ∧ c.lookupFn f = none ∧
      (c.lookupOvl f).isSome = true := by
  simp only [isOvl, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A function is no overloading symbol. -/
theorem isOvl_of_lookupFn {f : Sym} {fn : Fn} (h : c.lookupFn f = some fn) : c.isOvl f = false := by
  simp [isOvl, h]

/-- A map pattern symbol is no overloading symbol. -/
theorem isOvl_of_patternHook {f : Sym} (h : patternHooks.contains f = true) : c.isOvl f = false := by
  have hm : f = mapUnit ∨ f = mapElem ∨ f = mapConcat := by
    simpa [patternHooks] using List.contains_iff_mem.mp h
  have hh : isHook f = true := by rcases hm with rfl | rfl | rfl <;> rfl
  simp [isOvl, hh]

/-- A collection pattern symbol is no overloading symbol. -/
theorem isOvl_of_collPat {f : Sym} (h : c.isCollPat f = true) : c.isOvl f = false := by
  unfold isCollPat at h
  cases hh : isHook f with
  | true => simp [isOvl, hh]
  | false =>
    rw [hh] at h
    cases hp : c.lookupParam f with
    | none => rw [hp] at h; simp at h
    | some k => simp [isOvl, isParam, hp]

/-- Without overloading symbols, no symbol is one. -/
theorem isOvl_of_none {f : Sym} (hno : c.ovls = []) : c.isOvl f = false := by
  simp [isOvl, lookupOvl, hno]

end Semantics

/-- All defined: the values, or `none` if one is undefined. -/
def allSome : List (Option GroundTerm) → Option (List GroundTerm)
  | [] => some []
  | r :: rs => r.bind fun v => (allSome rs).map (v :: ·)

/-! ## Matching: the value a pattern denotes under σ -/

mutual
  /-- `PatVal c σ p v`: the left-hand-side pattern `p` denotes `v` under σ. Constructors build
  constructor terms; the map symbols allowed in patterns (`.Map`, `|->`, `_Map_`) denote their
  values (`hook`), so `K |-> V M` denotes the union of the singleton with M, defined only when
  K is not a key of M: the matches modulo associativity, commutativity and unit are exactly the
  σ under which the pattern denotes the map. A collection pattern symbol (`isCollPat`: a list's,
  or a cell map's) denotes the collection its operation builds from the parts' values (`collVal`),
  so `ListItem(P) L` denotes every list whose first element P denotes and whose rest L denotes. A
  constructor's pattern keeps its constructor meaning (`hc`). An overloading symbol's pattern
  denotes the value its application denotes (`norm`), so `f(P, Ps)` denotes `lift (g(v, vs))` where
  the arguments' values are covered by an overload of g. -/
  inductive PatVal (c : Semantics) (σ : Subst) : Term → GroundTerm → Prop where
    | var {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) : PatVal c σ (.var i) v
    | dv {s : Srt} {lit : Lit} : PatVal c σ (.dv s lit) (.dv s lit)
    | ctor {f : Sym} {ps : List Term} {vs : List GroundTerm}
        (h : c.isCtor f = true) (hs : PatVals c σ ps vs) : PatVal c σ (.app f ps) (.ctor f vs)
    | hook {f : Sym} {ps : List Term} {vs : List GroundTerm} {v : GroundTerm}
        (hp : patternHooks.contains f = true) (hs : PatVals c σ ps vs)
        (hv : hook f vs = some (some v)) : PatVal c σ (.app f ps) v
    | inj {a b : Srt} {p : Term} {w : GroundTerm} (h : PatVal c σ p w) :
        PatVal c σ (.inj a b p) (injNormal a b w)
    | coll {f : Sym} {ps : List Term} {vs : List GroundTerm} {v : GroundTerm}
        (hc : c.isCtor f = false) (hp : c.isCollPat f = true) (hs : PatVals c σ ps vs)
        (hv : c.collVal f vs = some v) :
        PatVal c σ (.app f ps) v
    | as {p : Term} {i : Nat} {v : GroundTerm} (h : PatVal c σ p v) (hi : σ.lookup i = some v) :
        PatVal c σ (.as p i) v
    | ovl {f : Sym} {ps : List Term} {vs : List GroundTerm} {v : GroundTerm}
        (hc : c.isCtor f = false) (ho : c.isOvl f = true) (hs : PatVals c σ ps vs)
        (hv : c.norm f vs = v) :
        PatVal c σ (.app f ps) v
  inductive PatVals (c : Semantics) (σ : Subst) : List Term → List GroundTerm → Prop where
    | nil : PatVals c σ [] []
    | cons {p : Term} {ps : List Term} {v : GroundTerm} {vs : List GroundTerm}
        (h : PatVal c σ p v) (hs : PatVals c σ ps vs) : PatVals c σ (p :: ps) (v :: vs)
end

/-! ## Evaluation -/

/-- σ gives each listed variable a value of its sort. -/
def Semantics.WellSortedAt (c : Semantics) (vars : List Srt) (is : List Nat) (σ : Subst) : Prop :=
  ∀ i ∈ is, ∀ s, vars[i]? = some s → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some s

/-- σ' is σ off the indices `is`. -/
def AgreeOff (is : List Nat) (σ σ' : Subst) : Prop := ∀ i, i ∉ is → σ'.lookup i = σ.lookup i

/-- The variables of a clause that its right side does not bind. -/
def Clause.univ (cl : Clause) : List Nat := (List.range cl.vars.length).filter (!cl.exs.contains ·)

/-- Without existential variables, well sorted on `univ` is well sorted. -/
theorem wellSortedAt_univ {c : Semantics} {cl : Clause} {σ : Subst} (h : cl.exs = []) :
    c.WellSortedAt cl.vars cl.univ σ ↔ c.WellSorted cl.vars σ := by
  constructor
  · intro hw i s hs
    have hlt : i < cl.vars.length := (List.getElem?_eq_some_iff.mp hs).1
    exact hw i (by simp [Clause.univ, h, hlt]) s hs
  · intro hw i _ s hs
    exact hw i s hs

/-! ## Conditions -/

def sameResult : Option GroundTerm → Option GroundTerm → Bool
  | none, none => true
  | some v, some w => GroundTerm.cmp v w == .eq
  | _, _ => false

/-- σ' is σ on the first `n` variables and gives the next `ys.length` values of the sorts `ys`. -/
def Extends (c : Semantics) (n : Nat) (ys : List Srt) (σ σ' : Subst) : Prop :=
  (∀ i, i < n → σ'.lookup i = σ.lookup i) ∧
  ∀ j s, ys[j]? = some s → ∃ v, σ'.lookup (n + j) = some v ∧ c.sortOf v = some s

mutual
  /-- `Eval c f vs r`: the function `f` of `c` at `vs` has the result `r` (`none`: undefined). -/
  inductive Eval (c : Semantics) : Sym → List GroundTerm → Option GroundTerm → Prop where
    /-- A clause that applies decides, when no clause of a smaller priority that is not `aside`
    applies: its patterns denote `vs` under a well-sorted σ, its `requires` evaluates to `true`
    under σ, its predicate `pre` is true under σ, and every clause of a smaller priority that is
    not `aside` fails. Where its `ensures` evaluates to `true` (or it has none), the result is its
    right-hand side's. -/
    | clause {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
        {σ : Subst} {r : Option GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hmem : cl ∈ fn.clauses)
        (hσ : c.WellSorted cl.vars σ)
        (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
        (hpre : Holds c cl.vars.length σ cl.pre true)
        (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
        (hrhs : EvalTerm c σ cl.rhs r)
        (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) : Eval c f vs r
    /-- Where every clause fails, `f` has its rest (`fnRest`). -/
    | rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) : Eval c f vs (c.fnRest fn vs)
    /-- A clause that decides (as in `clause`) whose `ensures` evaluates to something other than
    `true` (`false`, or undefined): `f` has no value there, `rhs ∧ ⊥` being empty whatever the
    right-hand side is. The rest is not read. -/
    | ensFails {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
        {σ : Subst} {t : Term} {w : Option GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hmem : cl ∈ fn.clauses)
        (hσ : c.WellSorted cl.vars σ)
        (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
        (hpre : Holds c cl.vars.length σ cl.pre true)
        (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
        (ht : cl.ens = some t) (he : EvalTerm c σ t w) (hw : w ≠ some (bool true)) :
        Eval c f vs none
  /-- `Fails c vs cl`: the clause does not apply at `vs`: for every σ that gives the variables of
  its patterns and conditions values of their sorts and under which its patterns denote `vs`, it
  has a `requires` that evaluates to something other than `true` (`false`, or undefined) or its
  predicate `pre` is false. With no `requires` and the predicate `\top`, no σ may match. A variable
  outside the patterns and conditions does not bear on whether the clause applies. -/
  inductive Fails (c : Semantics) : List GroundTerm → Clause → Prop where
    | intro {vs : List GroundTerm} {cl : Clause}
        (h : ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs → ReqFails c σ cl) :
        Fails c vs cl
  /-- `ReqFails c σ cl`: the clause has a `requires` whose result under σ is not `true` (`intro`),
  or its predicate `pre` is false under σ (`pre`). -/
  inductive ReqFails (c : Semantics) : Subst → Clause → Prop where
    | intro {σ : Subst} {cl : Clause} {t : Term} {r : Option GroundTerm}
        (ht : cl.req = some t) (he : EvalTerm c σ t r) (hr : r ≠ some (bool true)) :
        ReqFails c σ cl
    | pre {σ : Subst} {cl : Clause} (h : Holds c cl.vars.length σ cl.pre false) : ReqFails c σ cl
  /-- `EvalTerm c σ t r`: the right-hand side (or `requires`) `t` has the result `r` under σ. -/
  inductive EvalTerm (c : Semantics) : Subst → Term → Option GroundTerm → Prop where
    | var {σ : Subst} {i : Nat} : EvalTerm c σ (.var i) (σ.lookup i)
    | dv {σ : Subst} {s : Srt} {lit : Lit} : EvalTerm c σ (.dv s lit) (some (.dv s lit))
    | inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r) :
        EvalTerm c σ (.inj a b t) (r.map (injNormal a b))
    /-- A constructor of `c` builds the constructor term (undefined if an argument is). -/
    | ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = true) (hts : EvalTerms c σ ts rs) :
        EvalTerm c σ (.app f ts) ((allSome rs).map (.ctor f))
    /-- An interpreted hooked symbol has its meaning (Hooks.lean), and at a silent point the
    interpretation's value (`hookRes`). -/
    | hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = true) (hts : EvalTerms c σ ts rs)
        (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r)
        (hund : allSome rs = none → r = none) : EvalTerm c σ (.app f ts) r
    /-- A parameter symbol has the value `paramVal` gives it, on defined arguments;
    undefined if an argument is. -/
    | param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true)
        (hts : EvalTerms c σ ts rs) (hr : r = (allSome rs).bind (c.paramVal f)) :
        EvalTerm c σ (.app f ts) r
    /-- A function of `c` is called on defined arguments. -/
    | call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {vs : List GroundTerm} {r : Option GroundTerm}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms c σ ts rs)
        (hvs : allSome rs = some vs) (hf : Eval c f vs r) (hp : c.isParam f = false) :
        EvalTerm c σ (.app f ts) r
    /-- A call with an undefined argument is undefined. -/
    | callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms c σ ts rs)
        (hvs : allSome rs = none) (hp : c.isParam f = false) : EvalTerm c σ (.app f ts) none
    /-- An overloading symbol builds the normal form (`norm`; undefined if an argument is). -/
    | ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTerms c σ ts rs) :
        EvalTerm c σ (.app f ts) ((allSome rs).map (c.norm f))
  inductive EvalTerms (c : Semantics) : Subst → List Term → List (Option GroundTerm) → Prop where
    | nil {σ : Subst} : EvalTerms c σ [] []
    | cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
        {rs : List (Option GroundTerm)}
        (h : EvalTerm c σ t r) (hs : EvalTerms c σ ts rs) : EvalTerms c σ (t :: ts) (r :: rs)
  /-- `Holds c n σ p b`: the condition p, with n variables in scope, has the truth value b under σ.
  A negation is the result `false`, never a `¬`. -/
  inductive Holds (c : Semantics) : Nat → Subst → Cond → Bool → Prop where
    | top {n σ} : Holds c n σ .top true
    | bot {n σ} : Holds c n σ .bot false
    | not {n σ p b} (h : Holds c n σ p b) : Holds c n σ (.not p) (!b)
    | and {n σ p q b b'} (h : Holds c n σ p b) (h' : Holds c n σ q b') : Holds c n σ (.and p q) (b && b')
    | or {n σ p q b b'} (h : Holds c n σ p b) (h' : Holds c n σ q b') : Holds c n σ (.or p q) (b || b')
    | implies {n σ p q b b'} (h : Holds c n σ p b) (h' : Holds c n σ q b') :
        Holds c n σ (.implies p q) (!b || b')
    | ceil {n σ s t r} (h : EvalTerm c σ t r) : Holds c n σ (.ceil s t) r.isSome
    | equals {n σ s t u r r'} (h : EvalTerm c σ t r) (h' : EvalTerm c σ u r') :
        Holds c n σ (.equals s t u) (sameResult r r')
    | mem {n σ s t u r r'} (h : EvalTerm c σ t r) (h' : EvalTerm c σ u r') :
        Holds c n σ (.mem s t u) (r.isSome && sameResult r r')
    | exNone {n σ ys s p t body} (h : EvalTerm c σ t none) : Holds c n σ (.exMatch ys s p t body) false
    | exSome {n σ ys s p t body v b} (g : Subst → Bool) (h : EvalTerm c σ t (some v))
        (hb : ∀ σ', Extends c n ys σ σ' → PatVal c σ' p v → Holds c (n + ys.length) σ' body (g σ'))
        (hr : b = true ↔ ∃ σ', Extends c n ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true) :
        Holds c n σ (.exMatch ys s p t body) b
    | ex {n σ s body b} (g : Subst → Bool)
        (hb : ∀ σ', Extends c n [s] σ σ' → Holds c (n + 1) σ' body (g σ'))
        (hr : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) : Holds c n σ (.ex s body) b
    | all {n σ s body b} (g : Subst → Bool)
        (hb : ∀ σ', Extends c n [s] σ σ' → Holds c (n + 1) σ' body (g σ'))
        (hr : b = true ↔ ∀ σ', Extends c n [s] σ σ' → g σ' = true) : Holds c n σ (.all s body) b
end

/-- A function with a result is a function, so no overloading symbol. -/
theorem Eval.isOvl_false {c : Semantics} {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
    (h : Eval c f vs r) : c.isOvl f = false := by
  cases h with
  | clause hfn _ _ _ _ _ _ _ _ => exact c.isOvl_of_lookupFn hfn
  | rest hfn _ => exact c.isOvl_of_lookupFn hfn
  | ensFails hfn _ _ _ _ _ _ _ _ _ => exact c.isOvl_of_lookupFn hfn

end KCore
