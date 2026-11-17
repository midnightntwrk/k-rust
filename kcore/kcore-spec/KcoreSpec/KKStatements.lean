import KcoreSpec.Step
import KcoreSpec.EvalFunctional
import KcoreSpec.CollExec
import KcoreSpec.StepCompleteAt

/-!
# The statements of `kore.k`'s step function, without proofs

`kore.k` (`krs/semantics/kore`) is a K definition whose function `succs` computes, from an encoded
object definition and an encoded configuration, the successors of that configuration. This module
states what a proof of that reading shows, as three propositions over a signature `KK.Sig`:
`KK.SuccsSound` (each successor `succs` returns is a `Step`), `KK.SuccsStuck` (where it returns none,
no rule applies) and `KK.SuccsComplete` (where it returns at all, it returns every `Step`).

They are stated at `d.withHooks HookParams.none` for the object definition and at
`K.withHooks HookParams.none` for `kore.k`'s own semantics: `kore.k` gives no value where the
equations of a function give none and where a hook's text gives none, which is the member of the
family whose interpretation gives nothing. No hypothesis reads `d.hooks`.

Nothing here is proved of `kore.k`: `Sig` is a structure, and over an arbitrary one the three
propositions are false. The examples are the facts the form of the statements rests on.
-/

set_option autoImplicit false

namespace KCore.KK

/-! ## Mirrors of kore.k's sorts -/

inductive Kind | map | set | list
  deriving DecidableEq, Repr

inductive T
  | ap (f : Int) (as : List T) | iv (i : Int) | bv (b : Bool) | tk (s : Int) (x : String)
  | ij (a b : Int) (t : T) | vr (i : Int) | as (p : T) (i : Int) | hk (o : Int) (as : List T)
  | bot | cb (k : Kind) (c : Int) (ps : List T) | co (k : Kind) (c : Int) (es : List T)
  | en (t e : T) | kv (a v : T) | el (x : T)

/-- `cl(Int, Bool, Ts, Term, Term, _)`: the right side is `en r e` where the equation has an
ensures. -/
structure Cl where
  prio : Int
  owise : Bool
  pats : List T
  req : T
  rhs : T

/-- The ensures the clause holds. -/
def Cl.ens : Cl → Option T
  | ⟨_, _, _, _, .en _ e⟩ => some e
  | _ => none

/-- The right side without its ensures. -/
def Cl.body : Cl → T
  | ⟨_, _, _, _, .en r _⟩ => r
  | ⟨_, _, _, _, r⟩ => r

structure Rl where
  prio : Int
  owise : Bool
  lhs : T
  req : T
  rhs : T

def Rl.ens : Rl → Option T
  | ⟨_, _, _, _, .en _ e⟩ => some e
  | _ => none

structure D where
  subs : List (Int × Int)
  fns : List (Int × List Cl)
  rules : List Rl

inductive St | stuck | next (ss : List T)

/-- What the three statements are about: `K`, `kore.k`'s semantics as read from its kompiled text;
`succs`, its step function's symbol; the embeddings of the mirrors into `K`'s values; `enc`, the
encoding of an object configuration; and `encDef`, the encoding of an object definition, `none`
where `kore.k` has no place for it. -/
structure Sig where
  K : Semantics
  succs : Sym
  emb : T → GroundTerm
  embD : D → GroundTerm
  embSt : St → GroundTerm
  enc : GroundTerm → T
  encDef : Semantics → Option D

/-! ## The shapes of a rule and a clause kore.k has a place for -/

/-- Every variable bound by the left side, no existential variable, `\top` predicates. -/
def ruleShapeOK (r : Rule) : Bool :=
  r.opens.isEmpty && r.exs.isEmpty && r.pre.isTop && r.post.isTop

/-- The same of a clause, which is also not `aside`. -/
def clauseShapeOK (cl : Clause) : Bool :=
  cl.opens.isEmpty && cl.exs.isEmpty && cl.pre.isTop && cl.post.isTop && !cl.aside

/-- Every rule and every clause of every function has the shape `kore.k`'s `rl` and `cl` hold: a
priority, a left side, one `requires` term and a right side with its `ensures`. A variable the left
side does not bind and an existential variable range over a sort, which `kore.k` does not enumerate;
a predicate other than `\top` is no term it evaluates; an `aside` clause blocks nothing, and its walk
stops at the first priority with an applying clause. -/
def shapesOK (d : Semantics) : Bool :=
  d.rules.all ruleShapeOK && d.allFns.all fun fn => fn.clauses.all clauseShapeOK

/-- `shapesOK` reads no interpretation. -/
example (d : Semantics) (H : HookParams) : shapesOK (d.withHooks H) = shapesOK d := rfl

/-- `opens = []` is `binds`. -/
theorem opens_isEmpty_iff_binds (n : Nat) (occs : List Nat) :
    ((List.range n).filter fun i => !occs.contains i).isEmpty = binds n occs := by
  unfold binds
  rw [Bool.eq_iff_iff, List.isEmpty_iff, List.filter_eq_nil_iff, List.all_eq_true]
  constructor <;> intro h i hi <;> simpa using h i hi

example (r : Rule) : r.opens.isEmpty = binds r.vars.length (varOccs r.lhs) :=
  opens_isEmpty_iff_binds _ _
example (cl : Clause) : cl.opens.isEmpty = binds cl.vars.length (varOccsList cl.pats) :=
  opens_isEmpty_iff_binds _ _

/-- What `execReady` gives of `ruleShapeOK`: the left side binds every variable. -/
example {c : Semantics} (hr : CExec.execReady c = true) {r : Rule} (hmem : r ∈ c.rules) :
    r.opens.isEmpty = true :=
  (opens_isEmpty_iff_binds _ _).trans (CExec.rule_atoms_of_execReady hr hmem).2.2

/-! ## The members the statements are about -/

section
variable (S : Sig)

/-- The object definition's member the statements are about. -/
abbrev d₀ (d : Semantics) : Semantics := d.withHooks HookParams.none

/-- kore.k's member: where no equation of a kore.k function applies it has no value. -/
abbrev K₀ : Semantics := S.K.withHooks HookParams.none

/-- kore.k's `succs` at the encoding of `E` and `x` has the result `r`. -/
abbrev SuccsAt (E : D) (x : GroundTerm) (r : Option GroundTerm) : Prop :=
  Eval (K₀ S) S.succs [S.embD E, S.emb (S.enc x)] r

end

/-! ## The facts the form rests on -/

/-- `hco` is the hypothesis `Eval.functional` takes at `d₀`, and `EvalTerm.functional`'s. -/
example {d : Semantics} (hco : CoherentAll (d₀ d)) {f : Sym} {vs : List GroundTerm}
    {r r' : Option GroundTerm} (h : Eval (d₀ d) f vs r) (h' : Eval (d₀ d) f vs r') : r = r' :=
  Eval.functional hco h h'

/-- At `d₀` no premise of `Eval`, `EvalTerm` reads an interpretation: a hook's result is `hook`'s,
a function's rest is undefined, and a parameter without `impl` has no value unless it is an open
generator (`raw`), whose application is then the value: its own raw application, where that has
the declared sort. -/
example (d : Semantics) (f : Sym) (vs : List GroundTerm) : (d₀ d).hookRes f vs = hook f vs :=
  Semantics.hookRes_withHooks_none f vs
example (d : Semantics) (fn : Fn) (vs : List GroundTerm) : (d₀ d).fnRest fn vs = none := rfl
example (d : Semantics) (f : Sym) (vs : List GroundTerm) (k : ParamSig)
    (hk : (d₀ d).lookupParam f = some k) (hi : k.impl = none) (hraw : k.raw = false) :
    (d₀ d).paramVal f vs = none := by
  simp only [Semantics.paramVal, hk, hi, hraw]; rfl
example (d : Semantics) (f : Sym) (vs : List GroundTerm) (k : ParamSig)
    (hk : (d₀ d).lookupParam f = some k) (hi : k.impl = none) (hraw : k.raw = true) :
    (d₀ d).paramVal f vs =
      (some (GroundTerm.ctor f vs)).filter fun v => (d₀ d).sortOf v == some k.sig.result := by
  simp only [Semantics.paramVal, hk, hi, hraw]; rfl

/-- `execReady` and the rules are the same at `d` and `d₀`. -/
example (d : Semantics) : CExec.execReady (d₀ d) = CExec.execReady d := CExec.execReady_withHooks d _
example (d : Semantics) : (d₀ d).rules = d.rules := rfl
/-- A configuration of `d` is one of `d₀` where no parameter of `d` is an open generator: the sort
of an open generator's application is read from the interpretation, so with one the two types
differ. -/
def Config.toNone {d : Semantics} (hraw : ∀ k ∈ d.params, k.raw = false) (x : Config d) :
    Config (d₀ d) :=
  ⟨x.val, by rw [Semantics.sortOf_withHooks d _ hraw]; exact x.property⟩

/-- Under the same condition the two types of configurations are equal. -/
theorem config_withHooks (c : Semantics) (H : HookParams) (hraw : ∀ k ∈ c.params, k.raw = false) :
    Config (c.withHooks H) = Config c := by
  unfold Config Value; rw [Semantics.sortOf_withHooks c H hraw]

/-- The statements are about a definition whose own interpretation is arbitrary: `d₀` of
`d.withHooks H` is `d₀ d`. -/
example (d : Semantics) (H : HookParams) : d₀ (d.withHooks H) = d₀ d := rfl

/-! ## The three statements, as propositions over `Sig` -/

def SuccsSound (S : Sig) : Prop :=
  ∀ {d : Semantics} {E : D}, CExec.execReady d = true → S.encDef d = some E → ∀ (x : Config (d₀ d))
    {L : List T}, SuccsAt S E x.val (some (S.embSt (.next L))) → ∀ {y' : T}, y' ∈ L →
    ∃ y : Config (d₀ d), S.enc y.val = y' ∧ Step (d₀ d) x y

def SuccsStuck (S : Sig) : Prop :=
  ∀ {d : Semantics} {E : D}, CExec.execReady d = true → S.encDef d = some E → ∀ (x : Config (d₀ d)),
    SuccsAt S E x.val (some (S.embSt .stuck)) → ∀ r ∈ d.rules, NotApplies (d₀ d) r x.val

def SuccsComplete (S : Sig) : Prop :=
  ∀ {d : Semantics} {E : D}, CExec.execReady d = true → CoherentAll (d₀ d) → S.encDef d = some E →
    ∀ {x y : Config (d₀ d)} {s : GroundTerm}, SuccsAt S E x.val (some s) → Step (d₀ d) x y →
    ∃ L, s = S.embSt (.next L) ∧ S.enc y.val ∈ L

/-- For a `K` whose interpretation gives nothing, `K₀` is `K`. -/
example (c : Semantics) (h : c.hooks = HookParams.none) : c.withHooks HookParams.none = c := by
  cases c; cases h; rfl

end KCore.KK
