/-
  KCore. The intended model of `Γ`: its carrier, its interpretation, the conditions it needs,
  and what remains to be proved of it, stated as propositions.

  The carrier (`Elem`) holds
  - the values (`val v`): a sort's elements are its values (`InSort`), so a sort without values
    is empty;
  - the sorts (`srt s`), which the encoding applies `⊤_` (`inh`) and the symbols' sort
    arguments to;
  - the heads of the encoding and their partial applications (`app h args`): an application is
    curried, so `f a b` is `f` applied to `a`, then to `b`.

  A symbol is interpreted by its name (`Γ` writes every symbol under its name): a constructor
  builds the constructor term, an injection `injNormal`, an interpreted hook `hook`, a parameter
  `paramVal`, an overloading symbol the normal form (`norm`) or, at arguments a function it
  overloads covers, that function's values at the stripped arguments, lifted (`ovlRes`), a function
  `f` the values `v` with `Eval c f vs (some v)`; `next` applied to `y` is
  the configurations `x` with `StepM c x y`: `Step` with its competitor premise read as "no rule
  of a smaller priority applies" (`RuleApplies`), which the rule's axiom states, rather than "each
  of them has a `requires` that evaluates to something other than `true`" (`NotApplies`), which
  asks a result of their `requires`; `⌈_⌉` is everything; `⌈_⌉{s,s'}` applied to anything is
  the sort `s'`.

  `HypModel` adds to `Hyp` and `HypSound` decidable conditions on names, literals and sorts: two
  symbols with one name make Γ inconsistent (ModelNamesWitness.lean), and so would a token or
  byte sort that is Int or Bool (two values with one literal text), and so would a constructor
  listed twice (ModelDupCtorWitness.lean, `ctorsOnce`), and so would a function named like a
  constructor (ModelFnCtorWitness.lean, `fnsApart`), and so would an overloading symbol listed twice
  (`ovlsOnce`: two copies of one generator, said to be apart); a value of a sort outside the numbered ones
  denotes no element of its sort (`sortsNumbered`), and a collection symbol that is also a
  constructor builds a constructor term (`collsNotCtors`). The goals below state what the
  model satisfies; those proved are proved in the files that import this one.
-/
import KcoreSpec.FaithfulSound
import KcoreSpec.OvlLaws
import KcoreSpec.FnSolves
import KcoreSpec.SortedCl

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

/-! ## The conditions -/

/-- Every symbol the semantics gives a signature has a name of its own: two of `kernelSyms` with
one name are one signature, and none is named `inj`; every numbered sort has a name of its own. -/
def NamesApartK (c : Semantics) : Prop :=
  (∀ k ∈ kernelSyms c, ∀ k' ∈ kernelSyms c, c.symName k.name = c.symName k'.name → k = k') ∧
  (∀ k ∈ kernelSyms c, c.symName k.name ≠ "inj") ∧
  (∀ s ∈ kernelSorts c, ∀ s' ∈ kernelSorts c, c.sortName s = c.sortName s' → s = s')

theorem namesApartK_spec {c : Semantics} (h : namesApartK c = true) : NamesApartK c := by
  simp only [namesApartK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k hk k' hk' he => ?_, fun k hk => h2 k hk, fun s hs s' hs' he => ?_⟩
  · exact (h1 k hk k' hk').resolve_left (fun h => h he)
  · exact (h3 s hs s' hs').resolve_left (fun h => h he)

/-- **What the model needs**: `Hyp` and `HypSound`, its symbols and sorts named apart, its
literals told apart by their text, its own sorts and symbols numbered (`idsOK`), the sorts of its
values and symbols numbered, its collection symbols apart from its constructors, its symbols
named like `ite` at a sort named at numbered sorts and apart by them, its hooks, parameters and
constructors apart, each constructor listed once, and its functions apart from the other kinds. -/
structure HypModel (c : Semantics) : Prop where
  hyp : Hyp c
  sound : HypSound c
  names : namesApartK c = true
  lits : LitsApart c = true
  ids : c.idsOK = true
  sorts : sortsNumbered c = true
  collCtors : collsNotCtors c = true
  ites : itesApart c = true
  kinds : kindsApart c = true
  ctors : ctorsOnce c = true
  fns : fnsApart c = true

/-- What the value model reads of the functions, beside the clauses being well sorted
(`sortedOKClEx`: each variable occurs in its clause, the patterns need not bind it, and a clause may
bind variables by `\exists`; `srReady`) and
the names numbered: every function has at most one result (`FnDet`) and evaluation solves the
equations (`FnSolves`). No termination and no totality. -/
def HypFnModel (c : Semantics) : Prop :=
  c.sortedOKClEx = true ∧ c.srReady = true ∧ NamesNumbered c ∧ FnDet c ∧ FnSolves c

/-- `HypSoundCore` with `sortedOKClEx` in place of `sortedOK`: what the value model reads of the
conditions step soundness reads. -/
def HypSoundModel (c : Semantics) : Prop :=
  c.sortedOKClEx = true ∧ c.srReady = true ∧ NamesNumbered c ∧ genWf c = true ∧ patHooksApart c = true ∧
    collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧ OvlOK c

theorem HypSoundCore.model {c : Semantics} (h : HypSoundCore c) : HypSoundModel c :=
  ⟨Semantics.sortedOKClEx_of_sortedOKEx (Semantics.sortedOK_iff_ex.mp h.1), h.2⟩

/-- `HypModel` with `HypFnModel` and `HypSoundModel` in place of `Hyp` and `HypSound`: what the
model's proofs read of the clauses and rules is that they are well sorted with each variable
occurring (`sortedOKClEx`), and of the functions `FnDet` and `FnSolves`. -/
structure HypModelCore (c : Semantics) : Prop where
  hyp : HypFnModel c
  sound : HypSoundModel c
  names : namesApartK c = true
  lits : LitsApart c = true
  ids : c.idsOK = true
  sorts : sortsNumbered c = true
  collCtors : collsNotCtors c = true
  ites : itesApart c = true
  kinds : kindsApart c = true
  ctors : ctorsOnce c = true
  fns : fnsApart c = true
  /-- the overloading symbols are well formed -/
  ovlOK : c.overloadsOK = true
  /-- no overloading symbol is listed twice -/
  ovlsOnce : (c.ovls.map (·.sig.name)).Nodup

/-- What subject reduction reads of the overloading symbols, from `HypModelCore`. -/
theorem HypModelCore.ovlCase {c : Semantics} (h : HypModelCore c) : c.OvlCase :=
  OvlOK.ovlCase h.sound.2.2.2.2.2.2.2.2

theorem HypModelCore.det {c : Semantics} (h : HypModelCore c) : FnDet c := h.hyp.2.2.2.1

theorem HypModelCore.solves {c : Semantics} (h : HypModelCore c) : FnSolves c := h.hyp.2.2.2.2

/-- `HypModelCore` from its parts other than the functions'. -/
theorem HypModel.core_of {c : Semantics} (h : HypModel c) (hd : FnDet c) (hs : FnSolves c) : HypModelCore c :=
  have hc := h.hyp.core (Semantics.overloadsOK_pats h.sound.2.2.2.2.2.2.2.2.ok)
  ⟨⟨Semantics.sortedOKClEx_of_sortedOKEx (Semantics.sortedOK_iff_ex.mp hc.1), hc.2.1, hc.2.2.2.2.2.2, hd, hs⟩,
    HypSoundCore.model h.sound.core, h.names, h.lits, h.ids,
    h.sorts, h.collCtors, h.ites, h.kinds, h.ctors, h.fns, h.sound.2.2.2.2.2.2.2.2.ok, ovlsOnce_of_ids h.ids⟩

/-! ## The carrier -/

/-- The heads the encoding applies: the definedness, inhabitant, sort-of-sorts, sorted
definedness and next symbols, `inj`, a domain value's literal, and a symbol by its name. -/
inductive Head where
  | defined
  | inh
  | sortSort
  | ceil
  | next
  | inj
  | dv (lit : String)
  | sym (n : String)

/-- **The carrier.** -/
inductive Elem where
  | val (v : GroundTerm)
  | srt (s : Srt)
  | app (h : Head) (args : List Elem)

instance : Inhabited Elem := ⟨.srt 0⟩

variable (c : Semantics)

/-- The elements of the sort `s`: its values. -/
def InSort (s : Srt) : Elem → Prop
  | .val v => c.sortOf v = some s
  | _ => False

/-- The numbered sort of a sort symbol's name. -/
def sortOfName (n : String) : Option Srt := (kernelSorts c).find? fun s => "Sort" ++ c.sortName s == n

/-- The values of a list of elements, if all are values. -/
def vals : List Elem → Option (List GroundTerm)
  | [] => some []
  | .val v :: es => (vals es).map (v :: ·)
  | _ :: _ => none

/-- The symbol an application of the head named `n` to `args` is, with the number of sort
arguments it takes first: the symbol named `ite` at the sort of a leading sort argument, for
`Lblite` applied to a sort (`symApp`); otherwise the symbol of that name. -/
def resolve (n : String) (args : List Elem) : Option (CtorSig × Nat) :=
  match n, args with
  | "Lblite", .srt s :: _ =>
    ((kernelSyms c).find? fun k => iteSort? (c.symName k.name) == some (c.sortName s)).map (·, 1)
  | _, _ => ((kernelSyms c).find? fun k => c.symName k.name == n).map (·, 0)

/-- What the overloading symbol `f` gives at the argument values `vs`: where a function it
overloads covers them (`fnCover`), that function's results under `Eval` at the stripped arguments,
lifted to `f`'s result sort (none where the function has none: the overload's equation states the
application equal to the lifted application of the function, whatever that is); otherwise the
normal form (`norm`). It is `EvalTerm`'s reading of the application (`EvalTerm.ovlFn`,
`EvalTerm.ovl`). -/
def ovlRes (f : Sym) (vs : List GroundTerm) : Set Elem := fun x =>
  match c.fnCover f vs with
  | some kg => ∃ o v, c.lookupOvl f = some o ∧ x = .val (lift kg.result o.sig.result v) ∧
      Eval c kg.name (stripAll kg.args o.sig.args vs) (some v)
  | none => x = .val (c.norm f vs)

/-- What the symbol `k` gives at the argument values `vs`: a constructor the constructor term, an
interpreted hook its value, a parameter `paramVal`, an overloading symbol `ovlRes` (the normal
form, or the covering function's lifted results), a function its results under `Eval`. -/
def result (k : CtorSig) (vs : List GroundTerm) : Set Elem := fun x =>
  if c.isCtor k.name then x = .val (.ctor k.name vs)
  else if isHook k.name then ∃ v, x = .val v ∧ c.hookRes k.name vs = some (some v)
  else if c.isParam k.name then ∃ v, x = .val v ∧ c.paramVal k.name vs = some v
  else if c.isOvl k.name then ovlRes c k.name vs x
  else ∃ v, x = .val v ∧ Eval c k.name vs (some v)

/-- The head named `n` applied to `args`: a partial application while arguments are missing, the
symbol's result once all are there (on values only), nothing beyond. -/
def symAt (n : String) (args : List Elem) : Set Elem :=
  match resolve c n args with
  | some (k, p) =>
    if args.length < p + k.args.length then fun x => x = .app (.sym n) args
    else if args.length = p + k.args.length then
      match vals (args.drop p) with
      | some vs => result c k vs
      | none => fun _ => False
    else fun _ => False
  | none => if args = [] then fun x => x = .app (.sym n) [] else
      -- `Lblite` before its first argument is the only name that resolves late
      match n, args with
      | "Lblite", [_] => fun x => x = .app (.sym n) args
      | _, _ => fun _ => False

/-- The model's step: a rule whose left-hand side denotes `x` under a well-sorted σ, whose
`requires` and `ensures` evaluate to `true`, whose predicates `pre` and `post` hold (`Holds … true`)
and whose right-hand side evaluates to `y`, where no rule of a
smaller priority applies (`RuleApplies`). It is `Step` where each smaller priority's `requires` has
a result at its matches (`NotApplies` and `¬ RuleApplies` agree there). -/
def StepM (x y : GroundTerm) : Prop :=
  ∃ r ∈ c.rules, ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true ∧
    EvalTerm c σ r.rhs (some y) ∧
    (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.post true ∧
    ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x

/-- `x` has `y` as a successor under the transition `T`: both are configurations and `T` relates
them. -/
def StepE_T (T : GroundTerm → GroundTerm → Prop) : Elem → Elem → Prop
  | .val x, .val y => c.sortOf x = some topCellSort ∧ c.sortOf y = some topCellSort ∧ T x y
  | _, _ => False

/-- `x` has `y` as a successor: `StepE_T` at the transition `StepM`. -/
def StepE : Elem → Elem → Prop := StepE_T c (StepM c)

/-- Application in the model, `next` read through the transition `T`. -/
def evalApp_T (T : GroundTerm → GroundTerm → Prop) : Elem → Elem → Set Elem
  | .app .defined [], _ => fun _ => True
  | .app .inh [], .srt s => InSort c s
  | .app .inh [], .app .sortSort [] => fun x => ∃ s ∈ kernelSorts c, x = .srt s
  | .app .ceil [], b => fun x => x = .app .ceil [b]
  | .app .ceil [a], b => fun x => x = .app .ceil [a, b]
  | .app .ceil [_, .srt s'], _ => InSort c s'
  | .app .next [], y => fun x => StepE_T c T x y
  | .app (.dv lit) [], .srt s => fun x => ∃ l, x = .val (.dv s l) ∧ l.text = lit ∧ dvOK c.lib s l = true
  | .app .inj [], b => fun x => x = .app .inj [b]
  | .app .inj [a], b => fun x => x = .app .inj [a, b]
  | .app .inj [.srt a, .srt b], .val v => fun x => x = .val (injNormal a b v)
  | .app (.sym n) args, b => symAt c n (args ++ [b])
  | _, _ => fun _ => False

/-- Application in the model: `evalApp_T` at the transition `StepM`. -/
def evalApp : Elem → Elem → Set Elem := evalApp_T c (StepM c)

/-- The interpretation of the symbols: each head as itself, a sort by its name, a symbol by its
name (a constant is its value: a symbol of no arguments is applied to none). -/
def evalSymb : KoreAML.Sym → Set Elem
  | .defined => fun x => x = .app .defined []
  | .inh => fun x => x = .app .inh []
  | .sortSort => fun x => x = .app .sortSort []
  | .sort n => fun x => ∃ s, sortOfName c n = some s ∧ x = .srt s
  | .symbol "inj" => fun x => x = .app .inj []
  | .symbol n => match resolve c n [] with
    | some (k, 0) => if k.args = [] then result c k [] else fun x => x = .app (.sym n) []
    | _ => fun x => x = .app (.sym n) []
  | .ceil => fun x => x = .app .ceil []
  | .next => fun x => x = .app .next []
  | .dv lit => fun x => x = .app (.dv lit) []
  | .str _ => fun _ => False
  | .untranslated _ => fun _ => False

/-- **The value model at the transition `T`**: the symbols as in `evalSymb`, `next` applied to `y`
the configurations `x` with `T x y`. -/
def stdI_T (T : GroundTerm → GroundTerm → Prop) : Interpretation KoreAML.Sym Elem := ⟨evalSymb c, evalApp_T c T⟩

/-- **The intended interpretation**: the value model at the transition `StepM`. -/
def stdI : Interpretation KoreAML.Sym Elem := stdI_T c (StepM c)

/-- The intended interpretation is the value model at `StepM`, by definition. -/
theorem stdI_eq_T : stdI c = stdI_T c (StepM c) := rfl

/-- `StepE` is `StepE_T` at `StepM`, by definition. -/
theorem stepE_eq_T : StepE c = StepE_T c (StepM c) := rfl

/-! ## What it satisfies -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- `⌈φ⌉` is everything wherever `φ` is not empty. -/
theorem defined_app (φ : KoreAML.P) (e : Valuation Elem) (m : Elem) :
    (⌈φ⌉ : KoreAML.P).interpret (stdI_T c T) e m ↔ ∃ a, φ.interpret (stdI_T c T) e a := by
  simp only [Pattern.interpret]
  constructor
  · rintro ⟨d, a, -, ha, -⟩; exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨.app .defined [], a, rfl, ha, True.intro⟩

end AtT

/-- `⌈φ⌉` is everything wherever `φ` is not empty. -/
theorem defined_app (φ : KoreAML.P) (e : Valuation Elem) (m : Elem) :
    (⌈φ⌉ : KoreAML.P).interpret (stdI c) e m ↔ ∃ a, φ.interpret (stdI c) e a :=
  AtT.defined_app (c := c) (T := StepM c) (φ := φ) (e := e) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **Definedness holds**: `∀x. ⌈x⌉`. -/
theorem model_sat_definedness (x : EVar) : stdI_T c T ⊧ᴵ @definedness KoreAML.Sym _ x := by
  intro e m
  simp only [definedness, Pattern.interpret]
  rintro ⟨a, ha⟩
  exact ha ⟨.app .defined [], _, rfl, rfl, True.intro⟩

end AtT

/-- **Definedness holds**: `∀x. ⌈x⌉`. -/
theorem model_sat_definedness (x : EVar) : stdI c ⊧ᴵ @definedness KoreAML.Sym _ x :=
  AtT.model_sat_definedness (c := c) (T := StepM c) (x := x)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A list of items holds in the model when each item's pattern does: `itemsPremises` adds only
the definedness axiom. -/
theorem sat_itemsPremises {its : List KoreAML.Item} (h : ∀ it ∈ its, stdI_T c T ⊧ᴵ it.pat) :
    stdI_T c T ⊧ᴵP KoreAML.itemsPremises its := by
  rintro φ (⟨it, hit, rfl⟩ | ⟨x, rfl⟩)
  · exact h it hit
  · exact model_sat_definedness c x

end AtT

/-- A list of items holds in the model when each item's pattern does: `itemsPremises` adds only
the definedness axiom. -/
theorem sat_itemsPremises {its : List KoreAML.Item} (h : ∀ it ∈ its, stdI c ⊧ᴵ it.pat) :
    stdI c ⊧ᴵP KoreAML.itemsPremises its :=
  AtT.sat_itemsPremises (c := c) (T := StepM c) (its := its) (h := h)

/-! ## What remains: the goals -/

/-- **The reading lemma**: a value of a sort denotes its own element. -/
def DenGoal : Prop := ∀ (v : GroundTerm) (s : Srt), c.sortOf v = some s → ∀ (e : Valuation Elem) (m : Elem),
  (den c v).interpret (stdI c) e m ↔ m = .val v

namespace AtT

/-- Every value of a sort denotes exactly its own element in the value model at `T`. -/
def DenGoalT (c : Semantics) (T : GroundTerm → GroundTerm → Prop) : Prop :=
  ∀ (v : GroundTerm) (s : Srt), c.sortOf v = some s → ∀ (e : ML.Valuation Elem) (m : Elem),
    (den c v).interpret (stdI_T c T) e m ↔ m = .val v

end AtT

/-- Each item of the signature holds (definedness aside, `model_sat_definedness`), and every
domain value's arity (`dvArityAll`). -/
def SatSigGoal : Prop := stdI c ⊧ᴵP ΓSig c
/-- The constructors' axioms hold. -/
def SatConsGoal : Prop := stdI c ⊧ᴵP ΓCons c
/-- The domains' axioms hold: graphs, values are elements, distinctness, `collNoJunk`. -/
def SatDomainsGoal : Prop := stdI c ⊧ᴵP ΓDomains c
/-- The collections' axioms hold. -/
def SatCollsGoal : Prop := stdI c ⊧ᴵP ΓColls c
/-- The functions' equations hold. -/
def SatFnsGoal : Prop := stdI c ⊧ᴵP ΓFns c
/-- The rules' axioms hold. -/
def SatRulesGoal : Prop := stdI c ⊧ᴵP ΓRules c
/-- The step's closure axiom holds. -/
def SatStepGoal : Prop := stdI c ⊧ᴵP Γstep c
/-- The interpretation's values at silent points and the functions' rests hold. -/
def SatFallbackGoal : Prop := stdI c ⊧ᴵP ΓFallback c

/-- **`Γ` has a model, from the goals**: the model satisfies each part, so it satisfies their
union. -/
theorem has_model_of (h1 : SatSigGoal c) (h2 : SatConsGoal c) (h3 : SatDomainsGoal c)
    (h4 : SatCollsGoal c) (h5 : SatFnsGoal c) (h6 : SatRulesGoal c) (h8 : SatFallbackGoal c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c :=
  ⟨Elem, inferInstance, stdI c, fun φ hφ => by
    rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact h1 φ hφ
    · exact h2 φ hφ
    · exact h3 φ hφ
    · exact h4 φ hφ
    · exact h5 φ hφ
    · exact h6 φ hφ
    · exact h8 φ hφ⟩

/-- **`Γ` with the step's closure has a model, from the goals.** -/
theorem has_model_step_of (h1 : SatSigGoal c) (h2 : SatConsGoal c) (h3 : SatDomainsGoal c)
    (h4 : SatCollsGoal c) (h5 : SatFnsGoal c) (h6 : SatRulesGoal c) (h7 : SatStepGoal c)
    (h8 : SatFallbackGoal c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  ⟨Elem, inferInstance, stdI c, fun φ hφ => by
    rcases hφ with hφ | hφ
    · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
      · exact h1 φ hφ
      · exact h2 φ hφ
      · exact h3 φ hφ
      · exact h4 φ hφ
      · exact h5 φ hφ
      · exact h6 φ hφ
      · exact h8 φ hφ
    · exact h7 φ hφ⟩

end Model

end Faithful

end KCore
