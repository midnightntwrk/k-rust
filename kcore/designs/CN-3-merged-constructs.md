# CN-3: the constructs triage refused for cost, one merged design

Review agent, 2026-11-15; revised the same day after findings/REVIEW-CN3-U1.md (section 7 resolves its 16 findings and the two rows added by the coordinator).
Replaces CN-1 and CN-2 as the plan; findings/REVIEW-CN.md gives the evidence behind the changes from them.
Library read at `7c6fecea` (`jj file show`). Nothing here was elaborated or run: every Lean block is **to run**.
Names marked (lane) are the lane's to spell; the pattern or statement they build is fixed here.
Sections 2 and 3 are written to be checked cold; 2.0 gives the definitions of the library they rest on.

Order of work: U0 (shapes, alone) → U1 (statements and the closure axiom, alone) → four lanes in parallel → e3.
Headline pins (test/Pins.lean) move at U1 and nowhere else. Package data moves at U0 and nowhere else.

**Annotations after U1 (orchestrator, 2026-11-15; they override the text below where they differ):**
- **Precedence.** `⊧`, `⊧ᴵ`, `⊧ᴵP` are infix at 26, below `∧` at 35. Every conjunction of `⊧` statements below (SoundC, ExactC, sound_at, has_model_choice, and the addendum's Pins bodies) is read with each `⊧` conjunct parenthesized: `(A ⊧ B) ∧ (C ⊧ D)`. This is the only well-typed reading; a lane writes the parentheses and does not stop on them (TICKETS "U1c STOPPED then AUTHORISED").
- **AM-4 (findings/REVIEW-CN3-ADD.md).** At U1, `has_model_choice` and both halves of `exact_hyp` are proved in any model of `Γc c ∪ Γstep c` from `consistent_of`, `sound_at`, `famEx_closed`, `step_successor_at` and `values_apart`; no model file is read. This replaces the addendum's 2.7 sentence "the proofs are the value model's".
- **HOOK-READING (findings/HOOK-READING-decision.md).** Reading U1-3's package form (§2.9 and the row-8 resolution in §7: "a package with a law states its theorems by `sound_withHooks … (lawHooks d.sem)`") and the addendum's C2 package sentence are superseded: such a package states its theorems for every `H` with `OpenLaws (d.sem.withHooks H)` as a named obligation, and gives the `lawHooks d.sem H` instance beside each (HOOK-READING §4, which lane V2's brief carries verbatim).
- **declsOK (addendum C6).** The three `…Plain` conjuncts leave `declsOK` and the three definitions sit in Tie.lean beside `sortedOK`, before stage 4 (unit BASE-1), so lanes R, F, V each edit only their own conjunct's body.
- **R1-DECISION (findings/R1-DECISION.md).** §4.1's `rulesPlain` arm C is amended: a variable held by closed conditions only must also share no condition variable with the right side, the `ensures` or `post` (`condApart`); such a rule is refused `openRequires`, because the text leaves its successors open beyond the values (counter-example `a() => b(X) requires X ==Int 2 *Int H`). R1's remaining work is the briefs R1b, R1c, R1d of that decision.
- **F1-DECISION (findings/F1-DECISION.md, §1-§7).** §4.2's `aside` texts are replaced: `Coherent` reads `Clause.Decides`; `ClausesAgree`/`CoherentAll` range over same-priority pairs or pairs whose strictly-lower member is aside; `DecidesAt` keeps its negative form over `WellSortedAt … leftVars`. Pins `fails_plain` and `notApplies_of_binds` gain the hypotheses §1.2 and §7.1 give; the other ₀ pins stand (§7.2). The clause analogue of arm C stays admitted, its `CondDecided` an owed fact (§7.3).
- **Library at U1's end:** kcore-merge `c1b90027`; review cone (v) is core-cone.txt at 68bcce20.

One principle governs sections 2, 3 and 5: **`Γ` asserts no more than K's text states.**
The text is the kompiled sentences and the builtin prose (domains.md) on which the graphs of the hooked symbols already rest. A statement about which elements a sort has is admitted only with the sentence that states it.

## 1. U0: shapes at defaults, one package regeneration

U0 adds every field and number the constructs need and changes no behaviour: three decided conditions hold each new field at its default, so every theorem keeps its proof.
`Rule`, `Clause`, `ParamSig`, `Lib` derive `Repr`, and the ties compare the printed data, so each new field changes every package's text. That is why they are added together.

```lean
-- Core.lean
/-- A condition of a rule or a clause: a matching-logic predicate over terms. Each form is the
KORE connective of the same name at the sentence's sort, its arguments terms. A binder binds the
next indices after the variables in scope: the sentence's, then those of each enclosing binder. -/
inductive Cond where
  | top | bot
  | not (p : Cond) | and (p q : Cond) | or (p q : Cond) | implies (p q : Cond)
  /-- `\ceil{s,_}(t)`: t has a value -/
  | ceil (s : Srt) (t : Term)
  /-- `\equals{s,_}(t, u)`: both undefined, or both defined with one value -/
  | equals (s : Srt) (t u : Term)
  /-- `\in{s,_}(t, u)`: both defined with one value -/
  | mem (s : Srt) (t u : Term)
  /-- `\exists ȳ. \in{s,_}(t, p) ∧ body`: t's value matches the pattern p under some values of
  the variables `ys`, and body holds there -/
  | exMatch (ys : List Srt) (s : Srt) (p t : Term) (body : Cond)
  /-- `\exists y:s. body` -/
  | ex (s : Srt) (body : Cond)
  /-- `\forall y:s. body` -/
  | all (s : Srt) (body : Cond)
  deriving Repr, Inhabited

def Cond.isTop : Cond → Bool
  | .top => true
  | _ => false

inductive CollKind where
  | map | set | list
  /-- a range map: a `GroundTerm.map` whose keys are `Range` terms of its maximal intervals -/
  | rangeMap
  deriving Repr, DecidableEq, Inhabited

structure Clause where
  vars : List Srt
  pats : List Term
  req : Option Term
  rhs : Term
  ens : Option Term
  prio : Nat := 50
  /-- an equation no `[owise]` premise negates (`non-executable`): it blocks no clause -/
  aside : Bool := false
  /-- the variables the right side binds by `\exists`, indices of `vars` -/
  exs : List Nat := []
  /-- a predicate of the premise: the clause applies where it holds -/
  pre : Cond := .top
  /-- a predicate of the right side: the clause gives its value where it holds -/
  post : Cond := .top
  deriving Repr

structure Rule where
  vars : List Srt
  lhs : Term
  req : Option Term
  rhs : Term
  ens : Option Term
  prio : Nat
  /-- the variables the right side binds by `\exists` (`?X`), in the text's order: indices of `vars` -/
  exs : List Nat := []
  /-- a predicate of the left side: the rule applies where it holds -/
  pre : Cond := .top
  /-- a predicate of the right side, under the binder of `exs`: the rule gives its step where it holds -/
  post : Cond := .top
  deriving Repr

structure ParamSig where
  sig : CtorSig
  impl : Option Sym := none
  /-- an open generator: a symbol the text declares total, lists among its result sort's
  generators and gives no constructor axiom -/
  raw : Bool := false
  /-- the text holds the associativity axiom of this symbol -/
  assoc : Bool := false
  /-- the text holds the idempotence axiom of this symbol -/
  idem : Bool := false
  deriving Repr, DecidableEq, Inhabited

-- FixedSignature.lean, structure Lib: one field, last
  /-- sorts hooked under their own name to a library sort with domain values: `(s, b)` -/
  carriers : List (Srt × Srt) := []

-- BuiltinNames.lean
def nNewSorts : Nat := 9      -- was 7: Range, RangeMap appended
def nNewSyms : Nat := 202     -- was 183: `RangeMap:Range` and the 18 RANGEMAP hooks appended
```

The 19 symbols, in this order after the present last one: `rangeCtor`, `rmUnit`, `rmElem`, `rmConcat`, `rmLookup`, `rmLookupOrDefault`, `rmFindRange`, `rmUpdate`, `rmRemove`, `rmDifference`, `rmUpdateAll`, `rmRemoveAll`, `rmKeys`, `rmInKeys`, `rmSize`, `rmInclusion`, `rmChoice`, `rmKeysList`, `rmValues`.
Every match on `CollKind` gains `| .rangeMap`, with the inert answer (`collAxioms … | .rangeMap => []`; `collNoJunk`'s `el` as `.map`); `builtinColls` is unchanged in U0.

```lean
-- Tie.lean: three conditions, one per lane, conjoined into `sortedOK` here and never again
/-- Rules use no field U0 added (lane R replaces the body). -/
def rulesPlain : Bool := c.rules.all fun r => r.exs.isEmpty && r.pre.isTop && r.post.isTop
/-- Clauses use no field U0 added (lane F replaces the body). -/
def clausesPlain : Bool := c.fns.all fun f => f.clauses.all fun cl =>
  !cl.aside && cl.exs.isEmpty && cl.pre.isTop && cl.post.isTop
/-- Parameters and the library use no field U0 added (lane V replaces the body). -/
def paramsPlain : Bool :=
  c.params.all (fun k => !k.raw && !k.assoc && !k.idem) && c.lib.carriers.isEmpty

def sortedOK : Bool :=
  c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.clausesPlain && c.paramsPlain
```

`coreOK` keeps its six conjuncts; its pin does not move.
Reader (Parse.lean, outside the cone): the `RefusalReason`s of section 5 replace `ruleShape`, `patternConnective`, `configurationReflection` and the silent `wf false`.

Reading U0-1. One unit for all shapes. Reason: each field is one regeneration of every package and one renumbering. Reversal: a field proves unnecessary; it then stays, inert.

Validation: library rebuilt; every package regenerated natively and diffed (the diff is the new fields at their defaults and the renumbering, nothing else); Pins unchanged.

## 2. U1: the statements

U1 writes every statement the constructs change, once, in its final text. With every field at its default each new statement reduces to the old one (2.9 states this as lemmas), so the proofs are the old proofs through them.
No later unit edits the text of a declaration of this section or of section 3.

### 2.0 What the statements rest on (library at `7c6fecea`, unchanged)

- `Γ c : Premises KoreAML.Sym` is the theory (signature, constructors, domains, collections, function equations, rule axioms, fallback); `Γstep c` is the closure axiom `∀y. •y ⊆ ⋁_r ∃x̄_r. (L_r ∧ y ∈ R_r)` over the rule axioms `\rewrites(L_r, R_r)`.
- `den c v : KoreAML.P` is the pattern of the ground value v; `KoreAML.den p` that of a closed KORE pattern.
- `KoreAML.sNext φ` is `•φ`: the elements with a successor in φ. `KoreAML.allNext φ := ∼(sNext (∼φ))`: every successor is in φ.
- `Γ ⊧ φ`: φ holds in every model of Γ, at every valuation.
- `Config c` is the type of ground values of the configuration sort; `Subst := List (Nat × GroundTerm)`.
- `c.WellSorted vars σ := ∀ i s, vars[i]? = some s → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some s`.
- `PatVal c σ p v`: the pattern p denotes the value v under σ. `EvalTerm c σ t r`: the term t has the result `r : Option GroundTerm` under σ (`none`: undefined).
- `Γ` states the graphs of interpreted symbols **at values only**. A model may hold elements of a sort that are no value's. A sort is **confined** (2.1) where the text states that it holds its values only.
- `genWf c` (FaithOK.lean:74-79, a conjunct of `coreOK` through `faithCoreOK`): every constructor's result sort and every subsort pair's upper sort is in `consSorts c`, and no sort of `consSorts c` is Int, Bool, KConfigVar, Float, String, Bytes, a token sort, a byte sort or a collection sort.

### 2.1 Variables of a rule; confined sorts

```lean
-- DefinitionWf.lean
/-- The free variables of a condition, n variables in scope. -/
def varOccsCond (n : Nat) : Cond → List Nat
  | .top | .bot => []
  | .not p => varOccsCond n p
  | .and p q | .or p q | .implies p q => varOccsCond n p ++ varOccsCond n q
  | .ceil _ t => varOccs t
  | .equals _ t u | .mem _ t u => varOccs t ++ varOccs u
  | .exMatch ys _ p t body => varOccs t ++
      (varOccs p ++ varOccsCond (n + ys.length) body).filter (· < n)
  | .ex _ body | .all _ body => (varOccsCond (n + 1) body).filter (· < n)

/-- The variables a term holds under constructors and injections only. -/
def ctorOccs (c : Semantics) : Term → List Nat      -- (lane): structural, as `varOccs`
  | .var i => [i]
  | .app f ts => if c.isCtor f && !c.isOvl f then ts.flatMap (ctorOccs c) else []
  | .inj _ _ t => ctorOccs c t
  | .as t i => ctorOccs c t ++ [i]
  | .dv _ _ => []

def Rule.condVars (r : Rule) : List Nat :=
  (r.req.map varOccs).getD [] ++ varOccsCond r.vars.length r.pre
def Rule.leftVars (r : Rule) : List Nat := varOccs r.lhs ++ r.condVars
/-- The variables the left side does not bind. -/
def Rule.opens (r : Rule) : List Nat :=
  (List.range r.vars.length).filter fun i => !(varOccs r.lhs).contains i
def Rule.openCondVars (r : Rule) : List Nat := r.opens.filter r.condVars.contains
/-- A condition of the left side holds a variable the left side does not bind. -/
def Rule.reqOpen (r : Rule) : Bool := !r.openCondVars.isEmpty
/-- No condition of the left side holds a variable the left side binds. -/
def Rule.reqClosed (r : Rule) : Bool := r.condVars.all fun i => !(varOccs r.lhs).contains i
-- `Clause.condVars`, `opens`, `openCondVars`, `reqOpen`, `reqClosed`: the same over `varOccsList cl.pats`.

-- Evaluation.lean
/-- σ gives each listed variable a value of its sort. -/
def Semantics.WellSortedAt (c : Semantics) (vars : List Srt) (is : List Nat) (σ : Subst) : Prop :=
  ∀ i ∈ is, ∀ s, vars[i]? = some s → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some s

-- FaithOK.lean
/-- Every value of s is a literal: no constructor, overloading symbol, open generator or injection
ends at s, and s is no token, byte, collection or carrier sort. -/
def Semantics.litSort (c : Semantics) (s : Srt) : Bool :=
  c.ctorSigs.all (·.result != s) && c.ovlSigs.all (·.result != s) && c.subsorts.all (·.2 != s) &&
  c.params.all (fun k => !(k.raw && k.sig.result == s)) && (c.collOf s).isNone &&
  !c.lib.tokenSorts.contains s && !c.lib.byteSorts.contains s && c.lib.carriers.all (·.1 != s)

/-- Confined at depth k: Bool with only literals; or a constructor sort each of whose
generators takes arguments of sorts confined at a smaller depth. -/
def Semantics.confinedAt (c : Semantics) : Nat → Srt → Bool
  | 0, s => s == Srt.bool && c.litSort s
  | k + 1, s => c.confinedAt 0 s ||
      ((consSorts c).contains s && (c.gens s).all fun g => g.argSrts.all (c.confinedAt k))
-- (lane): `Gen.argSrts` is the generator's argument sorts (`[a]` for `.inj a`).

/-- **The sorts every element of which the theory states to be a value's.** -/
def Semantics.confined (c : Semantics) (s : Srt) : Bool := c.confinedAt (kernelSorts c).length s
```

`confined` is final here: no later unit changes it. Section 3 gives the sentence behind each case and the lemma `confined_value`.
A recursive constructor sort is never confined (its own sort is an argument at every depth), nor is any sort that reaches Int, String, Bytes, Float, a token sort, KConfigVar or a collection sort; so K and KItem are not.

### 2.2 Conditions

```lean
-- Evaluation.lean, after the `Eval` block
def sameResult : Option GroundTerm → Option GroundTerm → Bool
  | none, none => true
  | some v, some w => GroundTerm.cmp v w == .eq
  | _, _ => false

/-- σ' is σ on the first `n` variables and gives the next `ys.length` values of the sorts `ys`. -/
def Extends (c : Semantics) (n : Nat) (ys : List Srt) (σ σ' : Subst) : Prop :=
  (∀ i, i < n → σ'.lookup i = σ.lookup i) ∧
  ∀ j s, ys[j]? = some s → ∃ v, σ'.lookup (n + j) = some v ∧ c.sortOf v = some s

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

-- DefinitionWf.lean
/-- Each binder of a condition ranges where values and elements agree: an `exMatch` variable is
held by its pattern under constructors and injections, or is of a confined sort; an `ex` or `all`
variable is of a confined sort. -/
def Cond.bound (c : Semantics) (n : Nat) : Cond → Bool
  | .exMatch ys _ p _ body =>
      (List.range ys.length).all (fun j =>
        (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) &&
      Cond.bound c (n + ys.length) body
  | .ex s body | .all s body => c.confined s && Cond.bound c (n + 1) body
  | .not p => Cond.bound c n p
  | .and p q | .or p q | .implies p q => Cond.bound c n p && Cond.bound c n q
  | _ => true
```

`Cond.kore c vs S : Cond → Kore.Pattern` (lane) writes each form as its connective at the sort S: `exMatch ys s p t body` as `\exists` over `ys` of `\and(\in{s,S}(t, p), body)`, `ex` and `all` as `\exists` and `\forall`. `Cond.conj c vs S p : List Kore.Pattern` is `[]` for `.top` and `[Cond.kore c vs S p]` otherwise.
`Cond.bound c r.vars.length` of `pre` and of `post` is a conjunct of `ruleSorted` and of `clauseSorted` from U1 on (trivial while `rulesPlain` holds them at `.top`).
Why it is needed: `Holds` quantifies a binder over values, `Cond.kore` over elements. A variable the pattern holds under constructors is a subterm of t's value, so the two agree; at a confined sort they agree by 3. Anywhere else a model may satisfy the condition by an element that is no value's, and the statements of 2.6 would be false.

### 2.3 The step (Step.lean)

```lean
inductive RuleReqFails (c : Semantics) (σ : Subst) (r : Rule) : Prop where
  | intro {t : Term} {v : Option GroundTerm} (ht : r.req = some t) (he : EvalTerm c σ t v)
      (hv : v ≠ some (bool true)) : RuleReqFails c σ r
  | pre (h : Holds c r.vars.length σ r.pre false) : RuleReqFails c σ r

/-- Rule r does not apply to x: under every σ that gives the variables of its left side and its
conditions values of their sorts and under which its left side denotes x, a condition fails. -/
def NotApplies (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x → RuleReqFails c σ r

inductive Step (c : Semantics) : Config c → Config c → Prop where
  | rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules) (σ : Subst)
      (hσ : c.WellSorted r.vars σ)
      (hmatch : PatVal c σ r.lhs x.val)
      (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
      (hpre : Holds c r.vars.length σ r.pre true)
      (heval : EvalTerm c σ r.rhs (some y.val))
      (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
      (hpost : Holds c r.vars.length σ r.post true)
      (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) : Step c x y

/-- `Step.rule`'s premises for the rule r and the substitution σ. -/
structure StepBy (c : Semantics) (r : Rule) (σ : Subst) (x y : Config c) : Prop where
  mem : r ∈ c.rules
  hσ : c.WellSorted r.vars σ
  hmatch : PatVal c σ r.lhs x.val
  hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))
  hpre : Holds c r.vars.length σ r.pre true
  heval : EvalTerm c σ r.rhs (some y.val)
  hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))
  hpost : Holds c r.vars.length σ r.post true
  hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val

theorem step_iff_by {c : Semantics} {x y : Config c} : Step c x y ↔ ∃ r σ, StepBy c r σ x y

def RuleApplies (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∃ σ, c.WellSortedAt r.vars r.leftVars σ ∧ PatVal c σ r.lhs x ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true

/-- The evaluations the step at x reads have results: the left side's conditions wherever
`NotApplies` reads them, the right side's wherever `Step.rule` reads them. -/
def StepDecided (c : Semantics) (x : GroundTerm) : Prop :=
  ∀ r ∈ c.rules, (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) →
    (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
        (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c r.vars.length σ r.post b)
```

Reading U1-1. `NotApplies`, `RuleApplies` and `applies` (2.4) range over the variables of the left side and its conditions, not over all of `r.vars`.
Reason: it is a repair. At `7c6fecea`, `NotApplies` asks a value of every variable's sort and `applies` binds every variable by a sorted `\exists`. Take two sorts `A ::= f(B)`, `B ::= g(A)` and nothing else: neither has a value, and the theory has a model in which each has one element (the per-sort no-junk item takes the other sort whole; the written sentence, one unfolding, admits it too). A competitor `a() => b(X:A)` then never "applies" in `Step` and applies in that model, and `sound_at` is false for the larger rule it should block. A variable that does not occur in the left side or its conditions does not bear on whether they hold.
Where the left side binds every variable (every rule today) the two texts are one (`notApplies_of_binds`, `applies_of_binds`, 2.9).
Reversal: `ruleSorted` refuses a rule with a variable of a sort without a value; then the old texts are true and equal to these.

Reading U1-2. `Step.rule` keeps `WellSorted r.vars`: σ gives every variable a value.
Reason: with D1 (2.5) `Step` is every instance some model realises at values. `ruleSorted` (lane R) asks that each variable of `vars` occurs somewhere in the rule.
Reversal: a rule the reader must read holds a variable that occurs nowhere.

Reading U1-4 (the "second `Step` reading" of REVIEW-CN3-U1 finding 6d is not taken). `Step` does not block a larger rule merely because a competitor with an undecided open condition matches.
Reason: with that reading `sound_at` needs no hypothesis, but `Step` is no longer the steps the models have (it loses a step every model has where the competitor's condition is refuted), so `ExactC` (2.6) would be false of it without the very hypothesis it avoids. The first reading keeps one `Step` that is exact, and pays with a hypothesis that is true wherever the text decides the condition.
Reversal: `OpenDecided` proves undischargeable for a definition of the corpus whose text does decide the condition.

### 2.4 The theory the statements are about (Statements.lean, Faithful.lean)

```lean
/-- `∃x̄'. (lhs' ∧ ⌈req' = true⌉ ∧ pre')`: the configurations a rule applies to, the variables of
its left side and its conditions bound. -/
def applies (c : Semantics) (r : Rule) (rp : RulePres) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := KoreAML.varList (r.vars.map c.sortName) rp.names
  let bound := (List.range r.vars.length).filter r.leftVars.contains |>.filterMap (vs[·]?)
  KoreAML.existsAll C (bound.map KoreAML.Var.kore)
    (.and C ([Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre))

/-- A rule's right side under its binder: `∃ē. (rhs ∧ ens ∧ post)`, ē the `exs`. -/
def ruleRight (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  (r.exs.filterMap (vs[·]?)).foldr (fun v p => .exists C v.kore p)
    (.and C ([Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))] ++ Cond.conj c vs C r.post))

def prioRuleK (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let right := ruleRight c r
  let rightDef : Kore.Pattern := .ceil C C right
  let left := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre
  if comps.isEmpty then .rewrites C (.and C (left ++ [rightDef])) right
  else .rewrites C (.and C (left ++ [.not C (anyOfC C comps), rightDef])) right

/-- The definition reads a confined sort: a rule or a clause has a variable its patterns do not
bind, or a condition with a binder. -/
def Semantics.readsConfined (c : Semantics) : Bool :=
  c.rules.any (fun r => !r.opens.isEmpty || !r.pre.isTop || !r.post.isTop) ||
  c.fns.any fun f => f.clauses.any fun cl => !cl.opens.isEmpty || !cl.pre.isTop || !cl.post.isTop

/-- **The closure axiom** (section 3), for a definition that reads a confined sort. -/
def Γcl (c : Semantics) : Premises KoreAML.Sym := fun φ =>
  c.readsConfined = true ∧ c.litSort Srt.bool = true ∧ φ = boolClosed c

/-- **The theory the statements are about.** -/
def Γc (c : Semantics) : Premises KoreAML.Sym := Γ c ∪ Γcl c
```

`Γ`'s definition is not edited. With `exs = []`, `pre = post = .top` and every variable in the left side, `applies`, `ruleRight`, `prioRuleK` are the patterns at `7c6fecea` (the fold over `[]` is the identity, `Cond.conj` of `.top` is `[]`, `bound` is every variable), and `Γcl c` is empty (`readsConfined = false`): `Γc c = Γ c` (`Γc_plain`, 2.9).
`stepClosureItem` keeps its text: `closureDisjunct` binds the free variables of the rule pattern, and the `exs` are not free in it.

Reading U1-5. The closure axioms are a part beside `Γ`, held only by a definition that reads a confined sort.
Reason: an axiom added to `Γ` makes every `Γ ⊧` statement speak of fewer models. Every definition of today reads no confined sort, so its theorems stay statements about `Γ c` and are not weakened; a definition that does read one has its theorems about `Γc c`, and the two axioms it adds are sentences of the text (section 3).
Reversal: none wanted; if the gate is dropped the old theorems hold a fortiori and say less.

What a rule axiom says, read for the statements below. The axiom is closed universally over its free variables, at the carriers of their sorts. So for a rule with existential variables ē and other variables x̄: at every x̄ where the left side, its conditions and `⌈∃ē. right⌉` hold and no competitor applies, the configuration has **some** successor in `∃ē. right`. It does not say which instance, nor that there is one only. This is the sentence kompile writes (fixture e3-vars, kore.txt:185-191: `\rewrites(\and(lhs, \top), \exists(Var'Ques'Z:SortInt, \and(rhs, \top)))`), with the priority premise and the definedness premise `Γ` adds to every rule.

### 2.5 The families (Faithful.lean)

```lean
/-- `Vᵢ = ⟦σ i⟧` for each listed variable that σ gives a value. -/
def fixK (c : Semantics) (r : Rule) (σ : Subst) (is : List Nat) : List Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  is.filterMap fun i => match vs[i]?, r.vars[i]?, σ.lookup i with
    | some v, some s, some g => some (.equals (srtOf c s) C (.var v.kore) (g.kore c))
    | _, _, _ => none

/-- **The instances of an application.** `∃ē. (rhs ∧ ens ∧ post)` with every variable but the
`exs` fixed to its value under σ. -/
def famEx (c : Semantics) (r : Rule) (σ : Subst) : KoreAML.P :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let fixed := (List.range r.vars.length).filter fun i => !r.exs.contains i
  KoreAML.den (KoreAML.existsAll C ((fixed.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C (fixK c r σ fixed ++ [ruleRight c r])))

/-- **The outcomes of a match.** `∃ō. (⌈req⌉ ∧ pre ∧ ∃ē. (rhs ∧ ens ∧ post))` with the variables
the left side binds fixed to their values under σ, ō the others less `exs`. -/
def famOpen (c : Semantics) (r : Rule) (σ : Subst) : KoreAML.P :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let outer := (List.range r.vars.length).filter fun i => !r.exs.contains i
  KoreAML.den (KoreAML.existsAll C ((outer.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C (fixK c r σ (varOccs r.lhs) ++ [reqPat C (r.req.map (Term.kore c vs))] ++
      Cond.conj c vs C r.pre ++ [ruleRight c r])))

inductive Outcome where
  | val (y : GroundTerm)
  | fam (r : Rule) (σ : Subst)
def Outcome.pat (c : Semantics) : Outcome → KoreAML.P
  | .val y => den c y
  | .fam r σ => famOpen c r σ
abbrev OutFn := GroundTerm → List Outcome

/-- σ is a match of r's left side at x that no rule of a smaller priority blocks. -/
def Unblocked (c : Semantics) (r : Rule) (σ : Subst) (x : GroundTerm) : Prop :=
  c.WellSortedAt r.vars (varOccs r.lhs) σ ∧ PatVal c σ r.lhs x ∧
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x
```

Reading D1. `Γ` holds the text's sentence and nothing else about an existential rule; `Step` gives every instance; what the theory entails of an application is a family.
Reason: the alternative (the choice of instance as a parameter of the interpretation, with `Γ` stating its graph) makes "y is a successor" an axiom, which is more than the text states for any choice, and makes soundness of such a step membership in `Γ`. It also follows from D1 with `has_model_choice` (2.7), while D1 does not follow from it.
Reversal: `has_model_choice` cannot be proved.

Two families. Soundness fixes every variable but the `exs`: for `a() => b(X, ?Z)` with X unbound the text states a successor for each X. Completeness binds the open variables too: the closure gives a successor "for some elements of the open variables' sorts".

### 2.6 The headline statements (Sound.lean, Statements.lean)

```lean
/-- **Soundness.** The theory with the step's closure has a model; and for every step of `Step`,
by the rule r under σ: in every model, x has a successor among the instances of that application,
and y is one of those instances. -/
def SoundC (c : Semantics) : Prop :=
  (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
  ∀ (x y : Config c) (r : Rule) (σ : Subst), StepBy c r σ x y →
    Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ)) ∧
    Γc c ⊧ (den c y.val ⇒ famEx c r σ)

/-- `ref` lists, at x: exactly `Step`'s successors by the rules whose left side binds every
variable; and, for each other rule, a family for each unblocked match (up to the values of the
variables the left side binds) and no other family. -/
def OutIs (c : Semantics) (ref : OutFn) : Prop := ∀ x : Config c,
  (∀ y, .val y ∈ ref x.val ↔
     ∃ (hy : c.sortOf y = some topCellSort) (r : Rule) (σ : Subst),
       r.opens = [] ∧ StepBy c r σ x ⟨y, hy⟩) ∧
  (∀ r σ, .fam r σ ∈ ref x.val → r ∈ c.rules ∧ r.opens ≠ [] ∧ Unblocked c r σ x.val) ∧
  (∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
     ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ ref x.val)

/-- **Completeness.** For `ref` listing the outcomes at each configuration, with the step's
closure every successor of x is in an outcome `ref` lists. -/
def CompleteC (c : Semantics) (ref : OutFn) : Prop :=
  OutIs c ref → ∀ x : Config c,
    (Γc c ∪ Γstep c) ⊧
      (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (Outcome.pat c))))

/-- **Exactness.** `Step` is exactly the steps some model of the theory has, at values. -/
def ExactC (c : Semantics) : Prop := ∀ x y : Config c,
  Step c x y ↔ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP (Γc c ∪ Γstep c) ∧ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))
```

The hypothesis on open conditions.

```lean
/-- The rule's conditions are closed over open variables of which one is not of a confined sort:
whether they hold is one fact, the same at every configuration, and it is not decided by values. -/
def Rule.needsWitness (c : Semantics) (r : Rule) : Bool :=
  r.reqOpen && r.reqClosed && !r.openCondVars.all fun i => (r.vars[i]?.map c.confined).getD false
/-- Some values satisfy the rule's conditions. -/
def Rule.Witnessed (c : Semantics) (r : Rule) : Prop :=
  ∃ σ, c.WellSortedAt r.vars r.condVars σ ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true
/-- `∃ō. (⌈req = true⌉ ∧ pre)`, ō the variables of the conditions: closed where `reqClosed`. -/
def Rule.condK (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  KoreAML.existsAll C (((List.range r.vars.length).filter r.condVars.contains |>.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C ([reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre))
/-- No element of any model satisfies the rule's conditions. -/
def Rule.Refuted (c : Semantics) (r : Rule) : Prop := Γc c ⊧ ∼ KoreAML.den (r.condK c)
/-- The text decides the rule's conditions. -/
def Rule.CondDecided (c : Semantics) (r : Rule) : Prop := r.Witnessed c ∨ r.Refuted c
-- `Clause.needsWitness`, `Witnessed`, `condK` (at the function's result sort), `Refuted`,
-- `CondDecided`: the same over the clause's patterns and conditions.

/-- Every closed open condition of the definition is decided by the text. -/
def OpenDecided (c : Semantics) : Prop :=
  (∀ r ∈ c.rules, r.needsWitness c = true → r.CondDecided c) ∧
  (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)

/-- The interpretation satisfies `f(f(a,b),d) = f(a,f(b,d))` at values of the sort s. -/
def OpenAssoc (c : Semantics) (f : Sym) (s : Srt) : Prop :=
  ∀ a b d, c.sortsOf [a, b, d] = some [s, s, s] →
    (c.paramVal f [a, b]).bind (fun ab => c.paramVal f [ab, d]) =
    (c.paramVal f [b, d]).bind (fun bd => c.paramVal f [a, bd])
/-- The interpretation satisfies `f(a,a) = a` at values of the sort s. -/
def OpenIdem (c : Semantics) (f : Sym) (s : Srt) : Prop :=
  ∀ a, c.sortOf a = some s → c.paramVal f [a, a] = some a
/-- The interpretation satisfies the laws the text writes for its open generators. -/
def OpenLaws (c : Semantics) : Prop :=
  ∀ k ∈ c.params, k.raw = true →
    (k.assoc = true → OpenAssoc c k.sig.name k.sig.result) ∧
    (k.idem = true → OpenIdem c k.sig.name k.sig.result)

def FnHyp (c : Semantics) : Prop :=
  (∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c fn.label vs r) ∧
  (∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) ∧
  (∀ fn ∈ c.fns, ClausesAgree c fn) ∧
  (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) ∧
  OpenDecided c ∧ OpenLaws c
```

The theorems.

```lean
theorem sound_at (c : Semantics) (h : c.coreOK = true)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ)) ∧ Γc c ⊧ (den c y.val ⇒ famEx c r σ)

theorem complete_at (c : Semantics) (h : c.coreOK = true) (x : Config c) (hd : StepDecided c x.val)
    (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c))))

def Consistent (c : Semantics) : Prop :=
  ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc c ∪ Γstep c)

theorem consistent_of (c : Semantics) (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c)
    (hl : OpenLaws c) : Consistent c

theorem sound_hyp (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) : SoundC c
theorem complete_hyp (c : Semantics) (ref : OutFn) (h : c.coreOK = true) (hf : FnHyp c) : CompleteC c ref
theorem exact_hyp (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) : ExactC c
```

`CoreObligations c t` gains the two conjuncts `OpenDecided c` and `OpenLaws c`, and `fnHyp_of_core` passes them on. `CoreObligations.of_nil` gains one hypothesis, `(h6 : c.plain = true)` (2.9's `plain` gives both conjuncts by the vacuity lemmas), so every definition of today discharges it as before with one decided fact more.
`complete_hyp` passes `hc` to `complete_at` from `FnHyp`'s `OpenDecided`. A package with an open condition or an open generator's law states them as two named obligations.
`Sound`, `Complete`, `sound`, `complete`, `sound_core`, `complete_core` and the `withHooks` forms follow with `OutFn` for `StepFn`; `Exact d := ExactC d.sem` and `exact` beside them.

**Pins.lean after U1.** By `rfl` against the body written out: `SoundC`, `CompleteC`, `ExactC`, `OutIs`, `OutFn`, `Outcome.pat`, `famEx`, `famOpen`, `Unblocked`, `StepBy`, `StepDecided`, `FnHyp`, `OpenDecided`, `OpenLaws`, `OpenAssoc`, `OpenIdem`, `Rule.needsWitness`, `Clause.needsWitness`, `Rule.CondDecided`, `Clause.CondDecided`, `Rule.Witnessed`, `Rule.Refuted`, `Rule.condK` and their clause forms, `Γc`, `Γcl`, `Semantics.plain`, `SoundC₀`, `CompleteC₀`, `coreOK`. By proof term at the type written out: `sound_hyp`, `complete_hyp`, `exact_hyp`, `sound_at`, `complete_at`, `consistent_of`, `has_model_choice`, `famEx_closed`, `completeC_closed`, `step_plain`, `sound₀`, `complete₀`.
By the review cone (definitions the pinned bodies read): `Step`, `NotApplies`, `RuleApplies`, `Holds`, `Cond.bound`, `confined`, `confinedAt`, `litSort`, `readsConfined`, `boolClosed`, `Step₀`, `NotApplies₀`, `RuleReqFails₀`, `StepIs₀`, `applies₀` (StepOld.lean, never edited), `Rule.opens`, `condVars`, `leftVars`, `ctorOccs`, `applies`, `ruleRight`, `prioRuleK`.
`confined` is final in U1, so no pinned text's content moves afterwards.

Why each is as strong as the text allows.

- **`SoundC`, first entailment.** The text gives a successor in `∃ē. right` at each valuation of the other variables; `famEx` is that set at σ. Nothing stronger is entailed: by `has_model_choice`, for any instance y' of the application there is a model in which y' is its only successor by it, so no single instance is a successor in every model once there are two.
- **`SoundC`, second entailment.** It ties y to the theory: x has a successor in a set that holds y. With `exs = []` the set is y alone (`famEx_closed`).
- **`CompleteC`.** For a rule whose left side binds every variable the outcome is the value, as before. For another rule the outcome is `famOpen`, the rule's disjunct of the closure with the left side's variables fixed. The closure says no more about where the open variables range. The old text is false for the construct where an open variable's sort is unconfined (a model gives it an element that is no value's and the listed values miss its successor); that case is what licenses the change. Where the sort is confined or infinite the old text was true or vacuous, and `famOpen_values` (2.7) and `ExactC` give its content back.
- **`ExactC`.** `SoundC` and `CompleteC` together do not constrain `Step` at a rule with an open variable: a relation that never fires such a rule satisfies both (soundness has fewer steps to speak of, and `OutIs` reads `Unblocked` only). `ExactC` does: its left-to-right half says every step is a step of some model, its right-to-left half that a value no step reaches is a successor in no model. No relation but the intended one satisfies it, and it needs no list, so it is not vacuous at an infinite sort. It is the strongest statement about `Step` at values: a `Step` exact at values is determined.
- **`sound_at`'s hypotheses.** Only the competitors of r whose left side matches x are read, and the clauses evaluation may reach. `CondDecided` is the weakest that makes values and models agree on a closed condition: a value witness makes it hold in every model, a refutation in none; where neither holds some model satisfies the condition by an element that is no value's and another does not, and no `Step` is sound and exact for the larger rule. `sortedOK` (4.1, 4.2) keeps every other open condition out or at confined sorts.
- **`FnHyp`'s two new conjuncts.** Both are `True` for every definition of today (`openDecided_of_plain`, `openLaws_of_plain`). Each is there because the old `sound_hyp` is false for the new construct without it.
- **`consistent_of`'s hypothesis `OpenLaws`.** The law is an axiom of `Γ` (4.3). `OpenDecided` is not needed: in the value model every element is a value.
- **`complete_at`.** `CompleteC` at one configuration, under `StepDecided`, which now asks the left side's evaluations wherever `NotApplies` reads them.

Reading U1-3. A law the text writes for an open generator (associativity, idempotence) is an axiom of `Γ` and a hypothesis on the interpretation.
Reason: it is a sentence of the text (e2-comm-ctor kore.txt:22), and every equation of the text is treated so (`ΓFns` holds it, `FnSolves` says evaluation solves it). `OpenAssoc` has no definedness premise: the axiom is an equality of patterns, so one side undefined forces the other.
A package with such a generator states its theorems at the free interpretation of the laws: `sound_withHooks d hwf (lawHooks d.sem)`, with `openLaws_lawHooks` (2.9) discharging the conjunct. At `HookParams.none`, `OpenLaws` is false and no theorem is stated.
Reversal: `lawHooks` cannot be defined for a combination of laws the corpus has (then that combination is refused `openLaw`, section 5).

### 2.7 The lemmas that carry the strength

```lean
/-- **The choice among instances is free.** For a relation T that holds only steps of `Step`,
every step of a rule without existential variables, and for each application of a rule with
existential variables at least one of its instances: a model whose transition at values is T. -/
theorem has_model_choice (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc c ∪ Γstep c) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))

/-- A value in the instances of an application is a step by it. -/
theorem famEx_values (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (x y : Config c)
    (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y

/-- The outcomes of a match are, in every model, among any values that hold its steps. -/
theorem famOpen_values (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys) :
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c)))
```

`exact_hyp`, left to right: `has_model_choice` with `T := Step`. Right to left, argument: a successor that is y's element lies, by the closure, in some rule's right side at a valuation of elements. The variables the left side binds are values (as today). Each open variable is, by `rulesPlain` (4.1), of one of three kinds: held by the right side under constructors and injections, and then equal to a subterm of y, a value; of a confined sort, and then a value's element by `confined_value` (3.3); or held by closed conditions and by nothing else of the rule (not its right side, `ensures` or `post`), which are witnessed (a value serves, and nothing else reads the variable) or refuted (the rule gives no successor in any model). So the valuation may be taken at values, and by `StepDecided` it is a `StepBy`.
`has_model_choice` is the value model the library has (transition `Step`) with the transition a parameter; `hsome` is what a rule axiom asks, `hsub` what the closure asks.
All four are suspected: their proofs were not read against the model files. `has_model_choice` and the right-to-left half of `exact_hyp` are U1's proof risk for a definition of today only in the trivial case (no open variable); their full proofs are lane R's (4.1), with the statements fixed here.

### 2.8 Counter-example for the old soundness text (to run after R2)

Text `rule <k> c() => d(?Z:Bool) </k>`. `Step` has the successors `d(true)` and `d(false)`. `has_model_choice` with `T x y := Step c x y ∧ y ≠ d(false)` (it meets `hsome` with `y' := d(true)`) gives a model in which `den x ⇒ •den d(false)` fails. A `Step` with no successor there makes the old completeness text false instead: the axiom gives a successor in every model.

### 2.9 The old texts, and the vacuity of what is new

```lean
-- StepOld.lean (library): `RuleReqFails₀`, `NotApplies₀`, `Step₀`, `StepIs₀`, `applies₀` are the
-- declarations of Step.lean and Statements.lean at `7c6fecea`, verbatim, under these names.

/-- `SoundC` at `7c6fecea`. -/
def SoundC₀ (c : Semantics) : Prop :=
  (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c)) ∧
  ∀ x y : Config c, Step₀ c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val))
/-- `CompleteC` at `7c6fecea`. -/
def CompleteC₀ (c : Semantics) (ref : StepFn) : Prop :=
  StepIs₀ c ref → ∀ x : Config c,
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c))))

/-- The definition uses nothing U0, U1 or a lane adds: its rules, clauses, parameters, carriers and
overloads are of the shapes `7c6fecea` admits. -/
def Semantics.plain (c : Semantics) : Bool :=
  c.rules.all (fun r => r.exs.isEmpty && r.pre.isTop && r.post.isTop &&
    binds r.vars.length (varOccs r.lhs)) &&
  c.fns.all (fun f => f.clauses.all fun cl => !cl.aside && cl.exs.isEmpty && cl.pre.isTop &&
    cl.post.isTop && binds cl.vars.length (varOccsList cl.pats)) &&
  c.params.all (fun k => !k.raw) && c.lib.carriers.isEmpty &&
  c.ovls.all (fun o => o.over.all fun g => !(c.fns.any (·.label == g)))
-- (lane): `o.over` as `OvlSig` spells the overloaded symbols.

-- EvalOld.lean (library): `Eval₀`, `Fails₀`, `ReqFails₀`, `EvalTerm₀`, `EvalTerms₀` are the mutual
-- block of Evaluation.lean at `7c6fecea`, verbatim; `Step₀` and `NotApplies₀` read these.
/-- **Evaluation is the old evaluation** where the definition is plain. Lane F re-proves it at
each of its units (`Fails` over pattern and condition variables, `aside`, `Holds` in the block,
the overload case), lane V at each of its (`paramVal`, `sortOf`). -/
theorem eval_plain {c : Semantics} (hp : c.plain = true) (f : Sym) (vs : List GroundTerm)
    (r : Option GroundTerm) : Eval c f vs r ↔ Eval₀ c f vs r
theorem evalTerm_plain {c : Semantics} (hp : c.plain = true) (σ : Subst) (t : Term)
    (r : Option GroundTerm) : EvalTerm c σ t r ↔ EvalTerm₀ c σ t r
/-- The function equations are the old ones where the definition is plain. -/
theorem fnItems_plain {c : Semantics} (hp : c.plain = true) : fnItems c = fnItems₀ c

theorem notApplies_of_binds {c : Semantics} {r : Rule} (x : GroundTerm)
    (h : (r.pre.isTop && binds r.vars.length (varOccs r.lhs)) = true) : NotApplies c r x ↔ NotApplies₀ c r x
theorem applies_of_binds (c : Semantics) (r : Rule) (rp : RulePres)
    (h : (r.pre.isTop && binds r.vars.length (varOccs r.lhs)) = true) : applies c r rp = applies₀ c r rp
/-- **The step is the old step** where the rules are plain. -/
theorem step_plain {c : Semantics} (hp : c.plain = true) (x y : Config c) : Step c x y ↔ Step₀ c x y
theorem Γc_plain {c : Semantics} (h : c.readsConfined = false) : Γc c = Γ c

/-- A step by a rule without existential variables has one instance. -/
theorem famEx_closed (c : Semantics) (h : c.coreOK = true) {x y : Config c} {r : Rule} {σ : Subst}
    (hs : StepBy c r σ x y) (hex : r.exs = [])
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (famEx c r σ ≡ den c y.val)
/-- Where every rule's left side binds every variable, completeness lists values. -/
theorem completeC_closed (c : Semantics) (ref : StepFn) (hop : ∀ r ∈ c.rules, r.opens = []) :
    CompleteC c (fun x => (ref x).map Outcome.val) ↔
      (StepIs c ref → ∀ x : Config c, (Γc c ∪ Γstep c) ⊧
        (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c)))))

/-- **The old theorems**, for a definition whose rules and clauses are plain. -/
theorem sound₀ (d : Definition) (hwf : wf d = true) (hob : Obligations d)
    (hp : d.sem.plain = true) (hc : d.sem.readsConfined = false) : SoundC₀ d.sem
theorem complete₀ (d : Definition) (ref : StepFn) (hwf : wf d = true) (hob : Obligations d)
    (hp : d.sem.plain = true) (hc : d.sem.readsConfined = false) : CompleteC₀ d.sem ref

/-- The new conjuncts of `FnHyp` are true where nothing new is used. -/
theorem needsWitness_of_binds {c : Semantics} {r : Rule}
    (h : binds r.vars.length (varOccs r.lhs) = true) : r.needsWitness c = false
theorem openDecided_of_plain {c : Semantics}
    (hr : ∀ r ∈ c.rules, r.needsWitness c = false)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false) : OpenDecided c
theorem openLaws_of_plain {c : Semantics} (h : ∀ k ∈ c.params, k.raw = false) : OpenLaws c
/-- Some interpretation satisfies the laws: the free one, where no generator carries both. -/
theorem openLaws_lawHooks (c : Semantics) (h : c.coreOK = true)
    (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false) : OpenLaws (c.withHooks (lawHooks c))
```

`sound₀` and `complete₀` are the evidence that an existing package's theorems mean what they meant: the old relation (`Step₀`, over `Eval₀`), the old theory, the old text. `plain` is what makes them so: it holds every shape a lane adds out, and `step_plain`, `eval_plain`, `evalTerm_plain`, `fnItems_plain` and `Γc_plain` say that under it each edited declaration is the one at `7c6fecea`. `plain` implies `readsConfined = false`, so `hc` of the two theorems is kept only for reading.
Every definition of today meets `plain` by `sortedOK` at `7c6fecea` (`binds` in `ruleSorted` and `clauseSorted`) and U0's defaults.
`famEx_closed`'s `hc`, and `complete_at`'s: a clause with an undecided open condition has one result in `Eval` and another in a model where an element satisfies the condition, so the instance of a step that evaluates it is not the value `Step` gives. `sound₀` and `complete₀` discharge `hc` by `openDecided_of_plain`.
`openLaws_lawHooks`'s `hl`: merging equal adjacent arguments is no normal form for an operation that is both associative and idempotent (`f(a, a)` with `a := f(x, y)` flattens to `x, y, x, y`). Lane V's `paramsPlain` refuses `raw && assoc && idem` (`openLaw (assoc, idem)`, section 5, for cost: a normal form exists and is not built).
`famEx_closed` is per rule: a definition with one existential rule keeps the old soundness text for every other rule. At U1 its proof reads `rulesPlain` (`post = .top`); lane R3 extends the proof to a `post` that `Cond.bound` admits, the statement unchanged.
`lawHooks c` (lane V): for each `raw` parameter, the right-nested application of the flattened arguments where `assoc`, with equal adjacent arguments merged where `idem`; any other symbol as `HookParams.none`.

## 3. The closure axioms

One axiom, in `Γcl` (2.4). It rests on a sentence of the text, quoted. Nothing else is added: 3.2 and 3.4 say what was withdrawn and what that costs.

Notation: `KoreAML.inhOf (sortP n)` is the set of elements of the sort n; `φ ⊆⊆ ψ` is inclusion; `.mu X φ` the least fixed point; `symP` a symbol; `KoreAML.appList` application.

### 3.1 Bool

```lean
/-- Every element of Bool is `true` or `false`. -/
def boolClosed (c : Semantics) : KoreAML.P :=
  KoreAML.inhOf (sortP (c.sortName Srt.bool)) ⊆⊆
    (den c (.dv Srt.bool (.bool true)) ⋁ den c (.dv Srt.bool (.bool false)))

/-- In a definition where Bool holds only literals, its values are the two. -/
theorem boolValues {c : Semantics} (h : c.coreOK = true) (hl : c.litSort Srt.bool = true)
    {v : GroundTerm} (hv : c.sortOf v = some Srt.bool) : ∃ b, v = .dv Srt.bool (.bool b)
/-- The value model satisfies the axiom. -/
theorem boolClosed_model {c : Semantics} (h : c.coreOK = true) (hl : c.litSort Srt.bool = true) :
    (valueModel c) ⊧ᴵ boolClosed c        -- (lane): `valueModel` is `Model.has_model_core`'s model
```

Source: domains.md:1084, "The boolean values are `true` and `false`." The axiom states that sentence and no more.
The kompiled sentence is a tautology: base kore.txt:240, `\or{SortBool{}}(\top{SortBool{}}(), \bottom{SortBool{}}()) [constructor{}()] // no junk (TODO: fix bug with \dv)`.
What keeps other values out of Bool: `litSort`, the axiom's own gate in `Γcl`. For a constructor and an injection it follows from `genWf` (2.0): their results are constructor sorts and Bool is none. For an overloading symbol, an open generator and a carrier pair `litSort` asks it outright, since nothing I read excludes them. `dvOK` admits at Bool the `.bool` literals only.
Tie row: a statement of the theory that rests on the builtin prose, the class the graphs of the hooked symbols have; the written `\or(\top, \bottom)` is entailed and stays `inert noJunk`.

### 3.2 Int: no axiom (reading IC-1, decided)

The question: does domains.md:1196-1198 state that the elements of Int are exactly the integer values?
The sentences: "Provided here is the syntax of an implementation of arbitrary-precision integer arithmetic in K. This type is hooked to an implementation of integers provided by the backend."
They do not. The first says what the module provides (syntax of an arithmetic); the second says what the type is hooked to. Neither names the type's values, as 1084 does for Bool ("The boolean values are `true` and `false`"). "Every element of Int is an integer literal's" is an inference from them, and the kompiled sentence is the tautology (base kore.txt:250, `\or{SortInt{}}(\top{SortInt{}}(), \bottom{SortInt{}}())`).
Decision: `intClosed` is not in `Γcl`; Int is unconfined.
Reversal: a sentence of the text that names Int's values. The axiom is then

```lean
def intClosed (c : Semantics) : KoreAML.P :=
  let X : SVar := ⟨1⟩
  let one := den c (.dv Srt.int (.int 1))
  KoreAML.inhOf (sortP (c.sortName Srt.int)) ⊆⊆
    .mu X (den c (.dv Srt.int (.int 0)) ⋁
      KoreAML.appList (symP (c.symName intAdd)) [.svar X, one] ⋁
      KoreAML.appList (symP (c.symName intSub)) [.svar X, one])
```

gated by `litSort Srt.int` as Bool's, with `intValues` and `intClosed_model` in the manner of 3.1, and `confinedAt 0` gains `Srt.int`. That is a new statement unit (section 5).

What it costs, each a row of section 5 until then:
- a condition that holds a bound variable and an open variable of sort Int, in a rule that is not last or in a clause (`requires X >Int V`, X unbound): `openRequires Int`;
- a quantifier over Int in a condition (`Cond.ex Srt.int`, `Cond.all Srt.int`, an `exMatch` variable of sort Int its pattern does not hold under constructors): `openExtent Int`;
- an existential variable of sort Int on an equation's right side: `existentialEquation Int`;
- an open Int variable the right side holds only under a function symbol, with no closed decided condition: refused by `rulesPlain`;
- range-map patterns that bind a variable (c3): their keys are of Int and the element symbol is no constructor, so whether a pattern matches reads Int's extent: `rangeMapPattern` is a first-principles row, not a cost row.
What it does not cost: every fixture of 4.1 (e2-unbound, e3-vars: the Int variable is in the right side under a constructor; e2-rule: closed and witnessed), the families, `ExactC`, and no statement of section 2, which read `confined` only.

### 3.3 Confined constructor sorts: no axiom

A constructor sort whose generators take only arguments of confined sorts, to a finite depth, is confined by what `Γ` already holds: its no-junk item entails the written sentence, "every element is a generator applied to elements of its argument sorts" (e3-vars kore.txt:154 for Exp), and the generators are functional.

```lean
/-- **Every element of a confined sort is a value's.** -/
theorem confined_value {c : Semantics} (h : c.coreOK = true) (hr : c.readsConfined = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γc c)
    {s : Srt} (hs : c.confined s = true) (ρ : Valuation M) (e : M)
    (he : e ∈ I.eval ρ (KoreAML.inhOf (sortP (c.sortName s)))) :      -- (lane): the library's spelling
    ∃ v, c.sortOf v = some s ∧ I.eval ρ (den c v) = {e}
```

By induction on the depth: depth 0 is `boolClosed` with `boolValues`; a deeper sort by one unfolding and the induction hypothesis at each argument.
It uses the one unfolding the text writes and never the least fixed point.

### 3.4 What was withdrawn, and what it costs

- **`stringClosed`: dropped.** The fixed point over `stringChr` holds no string with a surrogate (`KStr.chr` gives a string at scalar values only), while domains.md:1700-1701 admits `\u` followed by any four hexadecimal digits as a string literal, and 1681-1686 says of the module "The implementation is currently incomplete". The axiom would deny what the prose admits. String is unconfined.
- **`genAll`, `genClosedItems`: dropped.** No written sentence states that a constructor sort holds only finitely built elements: the kompiled no-junk axiom is one unfolding, and no line of prose was found for well-foundedness.
  Cost: a recursive constructor sort is not confined, so `closed_is_value` of the first draft is gone, and with it d4 (an open generator binding a variable in a left side) and quantifiers over a recursive sort; both move to section 5.
  Cost to U1-1: none, the other way: its witness (two mutually recursive sorts without a value, 2.3) stays a model, so U1-1 is a repair and not a choice.
- **Recorded, not acted on here.** `Cons.noJunkItem` at `7c6fecea` is `⟦N⟧ ≡ μX. …` with X at the arguments of sort N (Kore/Gamma.lean:123-127): a least fixed point in N, which the written sentence does not state either. CN-3 uses nothing of it beyond the unfolding it entails, so these units hold whether or not that item is restated; restating it is a change to the library's standing theory and belongs to its own unit.
- **Models with elements that are no value's.** `Γ` is not edited, so every witness theorem of the library that exhibits a model of `Γ c` stays as it is. Under `Γc`, a model with a Bool element that is no literal's is lost, for a definition with `readsConfined`; the two witnesses whose headers I read (ModelJunkWitness, ModelJunkNonemptyWitness: IOError, empty in the value model) are not of that kind. `FaithfulColl`'s model was not read; lane R1 lists every such theorem before it lifts `rulesPlain`.

## 4. The lanes

After U1. No two lanes edit one cone declaration; each lane's briefs run in order. No lane edits a declaration of sections 2 or 3.

### 4.1 Lane R: rules

Owns: `ruleSorted`, `rulesPlain`, the proofs of `sound_at`, `complete_at`, `exact_hyp`, `has_model_choice`, the lemmas of 2.7, the rule cases of the model.

```lean
def ruleSorted (r : Rule) : Bool :=
  sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort &&
  binds r.vars.length (varOccs r.lhs ++ r.condVars ++ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++
    varOccsCond r.vars.length r.post) &&
  nodup r.exs && r.exs.all (fun i => r.opens.contains i && !r.condVars.contains i) &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req && condOK c r.vars r.pre &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens && condOK c r.vars r.post &&
  Cond.bound c r.vars.length r.pre && Cond.bound c r.vars.length r.post &&
  sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort

/-- Each open variable is one the values decide: held by the right side under constructors, or
of a confined sort, or held by closed conditions (`OpenDecided`) and by nothing else of the rule. And a rule that competes
with a larger one has open condition variables of confined sorts, or closed conditions. -/
def rulesPlain : Bool := c.rules.all fun r =>
  let conf := fun i => (r.vars[i]?.map c.confined).getD false
  r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i ||
    (r.condVars.contains i && r.reqClosed &&
      !(varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post).contains i)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)
```

`condOK` (lane): every term of the condition is well sorted, the binders extending the variable sorts.

| Brief | Units | Fixtures and expectations |
|---|---|---|
| R1 | A2: open universal variables (`ruleSorted` and `rulesPlain` as above with `exs = []`, the family case of `complete_at`, `sound_at`'s hypotheses). A2x: `exact_hyp` right to left. | e2-unbound (kore.txt:94): `wf true`; at `<k> a() </k>`, `Step` to `b(i)` for every Int i; `Γc ⊧ den x ⇒ •den b(i)`; `OutIs` with one `fam`; by `ExactC`, no value but a `b(i)` is a successor in any model. e2-rule (kore.txt:170-186): `wf true`, no `openRequires`; `Witnessed` with HOLE := `kseq(inj{Int,KItem}(0), dotk)` for the `[cool]` rule (the `isKResult` equation of Int, from `syntax KResult ::= Int`) and HOLE := `dotk` for `[heat]` (`isKResult`'s `[owise]` equation, then `notBool`); at `c(1)` the successor `b(1)`. |
| R2 | A3: existential variables (`exs` admitted, `has_model_choice`, `famEx_values`, the reader arm, Emit). | e3-vars (kore.txt:185-191): `stage refusals: 0`; at `c(1, 2)`: `Step` to `d(i)` for every i; `Γc ⊧ den x ⇒ •famEx`; `Γc ⊧ den d(i) ⇒ famEx`. New fixture with `?Z:Bool`: 2.8, and `famOpen_values` with `ys = [d(true), d(false)]`. |
| R3 | e2: `pre`, `post` admitted; the `Holds` lemma (at a value substitution the theory entails `Cond.kore p` where the result is `true` and its negation where `false`, for a condition `Cond.bound` admits); R-5 right sides as `?Z` with `post`. B3: the function cut `c(f(X))` → `c(V)`, `pre := equals V f(X)`. | e7-guardors (`c(a() #Or b()) => a()`): `c(a)` and `c(b)` have the successor `a`; `c(c(a))` none. New `e3-ml-rule-lhs-not` (`c(#Not(a())) => a()`): `c(b) → a`, `c(c(a)) → a`, `c(a)` none (distinctness sentences). New `e3-ml-rule-rhs-or` (`go => a #Or b`): `famEx` is `a ∨ b`; `Step` to both; by `has_model_choice` neither alone is entailed. New B3 fixture (`c(f(X:Int)) => d(X)`, f total with two preimages of one value): both `d` are `Step` successors; X is in the right side under `d`, and the rule is the only one (Int is unconfined, so beside a larger rule it is `openRequires Int`). |

### 4.2 Lane F: functions

Owns: `clauseSorted`, `clausesPlain`, the `Eval` block, `DecidesAt`, `lowerClauses`, `clauseEquation`, `competingEquation`, `exclusion`, `ClausesAgree`, `OvlSig`, `overloadsOK`.

- `Fails` and `exclusion` range over the variables of the patterns and conditions, as `NotApplies` and `applies` (U1-1).
- `clausesPlain`: a clause's open condition variables are of confined sorts, or its conditions are closed (`OpenDecided`); an open variable of the right side or the `ensures` is admitted (`MatchIndependent` then asks that the result does not depend on it). No "largest priority" case.
  Reading F-1. Reason: at values where such a clause fails, `ΓFallback` states the function's rest, which says no element satisfies the condition; that is what the text states only where the condition is decided or the sort confined. Reversal: `ΓFallback` is restated to be silent at such a point; then `Eval.rest` is not entailed there and the clause is refused anyway.
- `aside`: `Eval.clause` and `Eval.ensFails` read `hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl'`; `DecidesAt` the same; `lowerClauses f cl := f.clauses.filter fun cl' => !cl'.aside && cl'.prio < cl.prio`; `ClausesAgree`: `cl.prio = cl'.prio ∨ cl.aside = true ∨ cl'.aside = true → Coherent …`. `Eval.rest` and `ΓFallback` keep `∀ cl ∈ fn.clauses`.

| Brief | Units | Fixtures and expectations |
|---|---|---|
| F1 | B1: open variables in clauses. C1: `aside`. | e2-cool-eq (kore.txt:80-84): `wf true`; `Eval f [int 3] (some (int 3))`, the clause `Witnessed` as in R1; the second sentence stays `inert simplification`. New e5-owise-nonexec (`choose(a, Y) => Y`, `choose(b, Y) => Y [non-executable]`, `choose(X, _) => X [owise]`): at (b, a) the text states `= a` and `= b`: `Eval … (some a)` and `(some b)`, so `¬ FnDet`; at (b, b) one value. |
| F2 (after e3) | FR: `t #Or u` on an equation's right side as three clauses of one priority (`pre := ceil t, rhs := t`; `pre := ceil u, rhs := u`; `pre := and (not (ceil t)) (not (ceil u)), ens := false`). EX: `Clause.exs`, the existential variable of a confined sort (Bool, or a flat constructor sort over it). | Each behind its fixture from lane P; kompile rejecting the shape makes the row R-b. `e3-ml-eq-rhs-or` (`h(X) => f(X) #Or g(X)`): where f and g agree, that value; where one is undefined, the other's; where they differ `¬ FnDet`. EX (`f(X:Bool) => ?B ensures ?B ==Bool notBool X`): `Eval f [true] (some false)`, from the sentence and `boolClosed`; the Int form (`?Z *Int 2 ==Int X`) prints `existentialEquation Int`. |
| F3 (after F2) | OV: the overload form `f(inj x̄) = inj(g(x̄))` whose covering production g is a function (triage row E5 `overloadForm`, the `KCore.OvlSig` case). | See below. |

OV. Today `Semantics.norm` rewrites a covered application of an overloading symbol on values, and cannot evaluate a function.
Change: `OvlSig.over` may name a function of `c.fns`; `overloadsOK` admits it where the function's sorts are the covered sorts; `EvalTerm` gains the case "an application of an overloading symbol at arguments a function overload covers has the result of `Eval` of that function at the uninjected arguments, injected, undefined where it is"; `norm` leaves such an application alone; `ovlEqItem` keeps its form (it already writes the equation for whatever `ovlOver` lists).
What f's other axioms then ask of g are properties of the text, not refusals: `functional` on f asks g defined at every covered argument list (an obligation in the total list); injectivity of f (`injItem` is stated for every generator) asks g injective there (an `agree`-kind obligation). Where one fails the theory has no model and `consistent_of`'s hypotheses are unprovable.
Reading OV-1. Reason: the equation has a statable meaning whatever attributes f carries, and `Γ` already states an overloading symbol's distinctness at uncovered arguments only (`distGuarded`, Faithful.lean:128-133). Reversal: the fixture shows kompile rejects the declaration (R-b), or shows a text other than the overload equation for it.
Fixture (lane P2): `syntax Exp ::= Exp "+" Exp [overload(plus)]`, `syntax Int ::= Int "+" Int [function, overload(plus)]`, `syntax Exp ::= Int`, the function by `rule I1 + I2 => I1 +Int I2`. Expectation, from the overload equation: `EvalTerm` of the Exp-level application at `inj(1), inj(2)` is `inj(3)`; injectivity of f then fails (`1 + 2` and `2 + 1`), so the injectivity obligation is unprovable and the account says so.
I did not read triage's rows.toml; this unit is cut to the row as the coordinator names it.

### 4.3 Lane V: values and carriers

Owns: `sortOf`, `dvOK`, `paramVal`, `paramsPlain`, `gens`, `consItemsK`, `ΓDomains`, `collNoJunk`, `collAxioms`, `builtinColls`, the hook tables, `silentTable`, `lawHooks`.
The Lean of S, c1 and d1 is CN-2's (§1.2, §2.2-2.3, §3.2), with these changes: the registry numbers and `CollKind.rangeMap` are U0's; d1 adds to `consItemsK` the associativity axiom of each `raw`, `assoc` parameter and the idempotence axiom of each `raw`, `idem` one; `genWf` asks an open generator's result to be a constructor sort; `paramsPlain`'s conjuncts are dropped one per unit.

| Brief | Units | Fixtures and expectations |
|---|---|---|
| V1 | S: user sort hooked to a builtin carrier. c1: RANGEMAP carrier and 15 hooks. | `e5-hooked-int`: `2 +My 3` is `\dv{SortMyInt{}}("5")`; it and `\dv{SortInt{}}("5")` are apart (no sentence relates the sorts). `e6-rangemap`: CN-2 §5's list (sizes 2, 1, 3, 2; `find_range(merged, 4) = [0,5)`; overlap `¬⌈…⌉`); `M[9]` undetermined over the interpretations. |
| V2 | d1: open generators. d3: `lawHooks`, `openLaws_lawHooks`, the laws' tie E. ID: idempotence (triage row IDEM on a production that is no collection concatenation). | e2-comm-ctor: sentence 172 is an axiom of `Γ`; at `lawHooks` the theory has a model; at `HookParams.none` `OpenLaws` fails (`or(or(x,x),x)`, `or(x,or(x,x))` distinct raw values). `e2-open-rule` (CN-2 §5): for every interpretation total on `and`, `go` has one successor; `same(x & y, y & x)` is `true` at one interpretation and `false` at another. ID: below. |
| V3 (only after 3.2's reversal) | c3: range-map patterns that bind variables. | Axioms by extension: lookup and `in_keys` of the unit, an entry and a concatenation at any elements; concatenation defined exactly where key sets are disjoint; two range maps equal where equal at every Int key. `([A, B) r|-> V) Rest` against `[0,2) r|-> a` has the three matches `[0,1)`, `[1,2)`, `[0,2)` with their rests. |

ID. `syntax Exp ::= Exp "|" Exp [idem]` on a production that is no collection concatenation. Expected text, as for `assoc` in e2-comm-ctor: the symbol without `constructor`, `functional`, listed in the sort's no-junk axiom, and an axiom `\equals(f(K, K), K) [idem]`. Then it is an open generator with `idem := true`: the axiom is in `Γ`, `OpenIdem` in `OpenLaws`, `lawHooks` merges equal adjacent arguments. The reader classifies the axiom `openLaw (idem)` and not `collectionLaw` or `setIdempotence`.
Reading ID-1. Reason: idempotence is a sentence of the text about a symbol the text leaves otherwise open; the same treatment as associativity. Reversal: the fixture (lane P2, `e2-idem-ctor`) shows another text; if kompile keeps `constructor` on the symbol, the idempotence axiom contradicts its injectivity at any two-element sort, which is a property of the text recorded upstream, and the reading is the constructor with the axiom in `Γ` and no model.
Fixture expectations, from the axiom: at `lawHooks`, `x | x` is `x` and `(x | y) | y` is a value distinct from `x | y` unless `assoc` is also written; at `HookParams.none`, `OpenIdem` fails at `x`.
A unit law (`[unit]` on such a production) has no field here; it is refused `openLaw (unit)` for cost until a row asks for it.

Reading RM-3: `lookup` and `find_range` off the keys are silent. Reason: the `silentTable` criterion ("no value only where the text says there is none (`#False`, `#Bottom`)"), applied to `memsetBytes` whose prose uses the same words; domains.md:526-528, 548-550 write "an exception during concrete execution" and no `#False`, where Map lookup (267-268) writes `#False`. Reversal: the criterion changes for all three hooks together.

### 4.4 Lane P: reader only

Owns nothing in the cone. Parse.lean, Builtins.lean, Account, fixtures.

| Brief | Units | Fixtures and expectations |
|---|---|---|
| P1 | B2: `#configuration` as a parameter symbol (`ReadingNote.reflectionAsOwn`; the note says K's documentation gives the symbol a state-dependent meaning and no interpretation here is that meaning). e0: the K texts of CN-2 §5 Brief 2, kompiled, no theorem. e1: the reader rows of CN-2 §4.4 with "Cone: none". | `e6-configuration`: no `configurationReflection` line; `∀ y, ¬ Step c x y` at `HookParams.none`. e0 decides, per shape, R-b or built. |
| P2 | c2 (after c1), d2 (after d1), and the fixtures for OV, ID, EX and a non-linear `@S` outside `[simplification]`. | As 4.2 and 4.3 give them. |

Reading SV-1 (kept from CN-2): a set variable occurring once per side under applications is read as an element variable. A non-linear one, if kompile writes it outside a simplification, is a clause on the diagonal plus a guard on the function's rest off it; built in F2 with its fixture.

### 4.5 After the lanes

**e3** (after R3 and F1, alone against lanes R and F): `Holds` joins the `Eval` block with its constructors unchanged; `Clause.pre`, `Clause.post` admitted; every mutual induction gains its cases. Then F2 and F3.
d4 of the first draft is withdrawn (section 5).

## 5. What stays refused

**On first principles: a construct whose meaning depends on which elements an unconfined sort has.**
The unconfined sorts are: the token sorts without a hook and KConfigVar; Int, String, Bytes and Float; every recursive constructor sort; every collection sort; and so K, KItem and every sort that reaches one of these.
The reason, per kind:
- token sorts, KConfigVar: the kompiled sentence is `\or{S}(\top{S}(), \bottom{S}()) // no junk (TODO: fix bug with \dv)` (base kore.txt:256; e1-lexical:76; e3-kast:186), which states nothing, and the sort has no hook, so no prose names its values;
- Int: domains.md:1196-1198 says what the type is hooked to and does not name its values (3.2);
- String: the prose admits surrogate code points as literals and calls itself incomplete (3.4); no statement of its extent agrees with the values the library has;
- Bytes, Float: no sentence stating the extent was read; listed here until one is quoted;
- recursive constructor sorts: the written no-junk sentence is one unfolding and does not state that elements are finitely built (3.4);
- collection sorts: their entries are of KItem.
So a sentence that quantifies over such a sort, or whose truth needs an element of it to be a value's, is true in some models of the text and false in others at the same values, and no `Step` on values is sound and exact for it.

| `RefusalReason` | Shape | Applies where |
|---|---|---|
| `openExtent s` | a quantifier, complement or `\floor` of a term over the sort s (`Cond.bound` false) | s unconfined |
| `openRequires s` | an open variable of sort s in a condition that also holds a bound variable; or in a closed condition that is neither witnessed nor refuted (then no refusal: `OpenDecided` is unprovable) | s unconfined, the variable not held by the right side under constructors, or the rule not last |
| `existentialEquation s` | `\exists` on an equation's right side, the variable of sort s | s unconfined |
| `openGeneratorPattern s` | an open generator binding a variable in a left side | always: its sort is recursive or reaches one (the cut with `==K`, all variables bound elsewhere, is read) |
| `rangeMapPattern` | a range-map symbol binding a variable | while Int is unconfined (3.2); then c3 |
| `openLaw (assoc, idem)` | an open generator with both laws | until its normal form is built (cost) |
| `openLaw (unit)` | a unit law on an open generator | until a row asks (cost) |

Reversal for the first-principles rows: a written sentence that states the sort's extent. Then `confined` grows by that case, with its axiom and values lemma in the manner of 3.1, and the rows lift; this is the one event after U1 that moves a pinned text's content, and it is a new statement unit.

**R-b:** any shape of e0, EX, OV, ID or `@S` that kompile rejects, with its `kompile.txt`.
**Not refused, a property of the text:** an equation whose instances differ, clauses that disagree where an `aside` clause overlaps, an interpretation that breaks a written law, an overload whose function is not injective. Each is read, and `FnDet`, `OpenLaws` or the named obligation is unprovable there.

## 6. Not read, and what rests on it

Every proof body, so every "the proof is the old one" and all four suspected lemmas of 2.7; `Model.has_model_core`'s statement; Value.lean, OvlLaws.lean (`norm`, `ovlOver`), Params.lean, Parse.lean, Emit.lean, Exec; `DecidesAt`; `Var.kore`'s, `existsAll`'s and `I.eval`'s exact spelling; whether `c.isCtor` is true of an overloading symbol (`ctorOccs` excludes them either way); TIE-0; triage's rows.toml; the BYTES and FLOAT prose; `FaithfulColl`'s witness model; the consumers of `Step` (Reachability, Runs, Determinism, Noninterference), which U1's `Step.rule` premises and `StepFn` → `OutFn` reach.

## 7. Resolution of REVIEW-CN3-U1

| # | Finding | Resolution |
|---|---|---|
| 1 | `complete_at` false: `StepDecided` and `NotApplies` read different substitutions | Accepted. `StepDecided` is the reviewer's text (2.3): left-side evaluations at `WellSortedAt r.vars r.leftVars`. |
| 2 | `consistent_of` false: `OpenAssoc`'s definedness premises | Accepted. `OpenAssoc c f s` with the sort premise only (2.6); `OpenIdem` written the same way. |
| 3 | `sound_at` false for an `exMatch` variable the pattern does not bind | Accepted. `Cond.bound` is in U1 (2.2), a conjunct of `ruleSorted` and `clauseSorted`; it uses `ctorOccs`, stricter than the reviewer's `varOccs` (a variable under a function symbol in the pattern is not a subterm of the value). |
| 4 | `SoundC ∧ CompleteC` do not constrain `Step` at an open rule | Accepted. `ExactC` and `exact_hyp` are pinned (2.6), with `has_model_choice`. `exact_hyp` has no hypothesis beyond `coreOK` and `FnHyp`: the reviewer's `opensValued` is a conjunct of `rulesPlain` (4.1), widened by a third arm (a variable held only by closed, decided conditions), which e2-rule needs. The "largest priority" admission of a mixed open condition at an unconfined sort is kept only where the variable is in the right side under constructors. |
| 5 | No lemma gives values back where the old `CompleteC` listed them | Accepted. `famOpen_values` (2.7), with the confinement of the rule's open variables as its hypothesis. |
| 6a | `OpenWitnessed` global on a one-step theorem | Accepted. `sound_at` reads the competitors of r whose left side matches x (2.6). |
| 6b | Clause conjunct without a "larger clause" test | Rejected. Reason: `ΓFallback` (Faithful.lean:236-240) states the rest wherever every clause `Fails` at values; for an undecided open condition that says no element satisfies it, more than the text states, whatever the clause's priority. Reversal: `ΓFallback` restated to be silent there (F-1). |
| 6c | A dead competitor is refused | Accepted. `CondDecided := Witnessed ∨ Refuted` (2.6), decided here, not left open. |
| 6d | A second `Step` reading without the hypothesis | Rejected (reading U1-4). Reason: that `Step` drops a step every model has where the competitor's condition is refuted, so `ExactC` is false of it. Reversal: at U1-4. |
| 7 | Vacuity is prose; route from `Obligations` not stated | Accepted. `needsWitness_of_binds`, `openDecided_of_plain`, `openLaws_of_plain` (2.9); `CoreObligations` gains the two conjuncts at U1 (2.6). |
| 8 | `OpenLaws` unsatisfiable at the packages' interpretation | Accepted. `openLaws_lawHooks` (2.9); a package with a law states its theorems by `sound_withHooks … (lawHooks d.sem)` (U1-3). |
| 9 | Closure axioms true of the value model by assertion | Accepted. `litSort` gates each axiom and `confined`; `boolValues`, `intValues`, `boolClosed_model`, `intClosed_model` (3.1, 3.2). |
| 10 | Sources: Bool exact, Int an inference, String and `genAll` more than the text | Accepted. Bool kept; Int kept and labelled IC-1 with its sentence and its reversal (3.2); `stringClosed` and `genAll` dropped (3.4). |
| 11 | `genClosedItems` removes U1-1's witness | Accepted, resolved by dropping `genAll`: the witness (two mutually recursive value-less sorts) stays, named in U1-1, which is therefore a repair. |
| 12 | Closure axioms may hide a defect; witness models lost | Accepted. The axioms are in `Γcl`, beside `Γ` and gated by `readsConfined` (U1-5), so `Γ` and its witness models are untouched; lane R1 lists the theorems before lifting `rulesPlain` (3.4). |
| 13 | Old `CompleteC` false only at an unconfined sort; U1-1 lemmas missing | Accepted. The licence is stated as that one case (2.6); `notApplies_of_binds`, `applies_of_binds` (2.9). |
| 14 | Recovery lemmas were over the new `Step` | Accepted. `Step₀` kept in StepOld.lean; `step_plain`, `Γc_plain`, `famEx_closed` (per rule), `sound₀`, `complete₀` over `Step₀` and `Γ` (2.9). `soundC_closed` is replaced by `famEx_closed`. |
| 15 | Pin list incomplete; `confined` moves after U1 | Accepted. The list of 2.6 names what Pins.lean holds and what the cone holds; `confined` is final in U1. |
| 16 | `OutIs` docstring | Accepted (2.6). |
| + | IDEM on a production that is no collection concatenation | Unit ID, lane V brief V2 (4.3); field `ParamSig.idem` in U0, `OpenIdem` in U1. |
| + | E5 `overloadForm`, the `KCore.OvlSig` case | Unit OV, lane F brief F3 (4.2); lane F owns `OvlSig`, `overloadsOK` and `EvalTerm`. Checked against the row only as the coordinator names it. |

Pinned texts changed since the first draft: `SoundC`, `CompleteC`, `Consistent` (now over `Γc`); `FnHyp` (`OpenDecided` for `OpenWitnessed`; `OpenLaws` with the sorted `OpenAssoc` and `OpenIdem`); `sound_at` (local hypotheses); `StepDecided`; new pins `ExactC`, `exact_hyp`, `Γc`, `Γcl`, `step_plain`, `sound₀`, `complete₀`, `famEx_closed`. `coreOK` is unchanged throughout.

### Outcome of the re-check (R1-R4, the pin entries, IC-1)

| # | Required change | Done |
|---|---|---|
| R1 | `exact_hyp` false through `rulesPlain`'s third arm | Accepted. The arm now asks that the variable is in no right side, `ensures` or `post` (4.1); 2.7's argument says the same. |
| R2 | `complete_at`, `famEx_closed` need the clause hypothesis | Accepted. Both take `hc` (2.6, 2.9); `complete_hyp`, `sound₀`, `complete₀` pass it. |
| R3 | `openLaws_lawHooks` false for `assoc` with `idem` | Accepted. The lemma takes `hl` (2.9); lane V refuses the combination as `openLaw (assoc, idem)`, a cost row (section 5). |
| R4 | `sound₀` / `complete₀` checked the rules only | Accepted, both ways: `plain` covers rules, clauses, parameters, carriers and overloads, and `Eval₀` is kept (EvalOld.lean) with `eval_plain`, `evalTerm_plain`, `fnItems_plain` re-proved by lanes F and V at each unit (2.9). |
| pins | `Witnessed`, `Refuted`, `condK`, `plain`, `Step₀`, `StepIs₀` | Added: the first four and `SoundC₀`, `CompleteC₀` to Pins.lean's list, the `₀` declarations to the cone's (2.6). `CoreObligations.of_nil`'s new hypothesis is stated (2.6). |
| IC-1 | Does domains.md:1196-1198 state Int's extent? | No (3.2). `Γcl` holds `boolClosed` only; `confinedAt 0` is Bool; Int is unconfined. Cost: 3.2's list; c3 moves behind the reversal; EX's fixture is at Bool. Resolution lines 9 and 10 above are superseded for Int. |

Pinned texts changed by this outcome: `Γcl` (Bool only), `complete_at`, `famEx_closed`, `Semantics.plain`; `confined`'s body (cone). `SoundC`, `CompleteC`, `ExactC`, `FnHyp`, `coreOK` are unchanged.
