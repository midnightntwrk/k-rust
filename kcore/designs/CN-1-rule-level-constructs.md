# CN-1: rule- and step-level constructs refused R-c, and what supporting each one takes

Review agent output, 2026-11-15. Library read at `1e306534` (`jj file show`), lane CE's `Clause.ens` taken as given.
Groups: (a) `?X` on a rule's right side; (b) variables no left side binds; (f) `#configuration`; sub-cases: non-executable beside `[owise]`, constructor-with-function overload, a function in a left side whose variables occur only under it.
Nothing here was run. Lean text is written out, not proved; helper names marked (lane) are the lane's to choose, the pattern they build is fixed.

## 0. Result

One fact decides most of this file, and it is not in the triage: **a variable that no left side binds is the first quantifier in KCore that ranges over the carrier of a sort instead of over the parts of a matched value.**
Every variable of a rule or clause at `1e306534` is bound by a pattern that matches a ground value, so the model's witness is a value's element (`patVal_backC`, then `substOf_ok … (hwit i (hbinds i hi))`, FaithfulCompleteAt.lean:154-156).
`Γ` does not say that a sort holds only its values: `ΓDomains` states graphs at values, "every value is one element" and distinctness; `ΓCons` has a per-sort least fixed point over `consSorts` only, which leaves Int, Bool, String, Bytes, Float and every token sort open, and leaves mutually recursive constructor sorts open to non-well-founded elements (each `noJunkItem` unfolds its own sort and takes the others whole).
TIE-0 reading TR-2 already records this as E against Ev.
So for an unbound variable the text's sentence and `Step` (which quantifies σ over values, `WellSorted`) can differ, and they differ in three places: a requires-only variable with no value witness; a competitor of smaller priority with such a variable; a successor built from a non-value element.

Decisions, each detailed below:

| # | Construct | Decision | Cone | Headline text |
|---|---|---|---|---|
| D1 | (a) `?X` | supported: `Rule.exs`; `Step` unchanged (every instance whose `ensures` is true); the rule's outcome is a family | `Rule`, `ruleSorted`, `prioRuleK`, `SoundC`, `CompleteC` | **`SoundC` and `CompleteC` change: both old texts are false for the construct** (§1.3) |
| D2 | (b) right-side or ensures-only variable (`unboundVariables(X)`) | supported, same family machinery; soundness per instance keeps its old form | `ruleSorted`, `CompleteC` | `sound_at` text holds; old `CompleteC` false |
| D3 | (b) requires variable (author-written `[heat]`/`[cool]`), rules | supported where the rule has the largest priority of the definition (`opensLast`); otherwise refused with a reason of its own until `Γ` states generated carriers | `ruleSorted`, `coreOK` conjunct | as D2 |
| D4 | (b) requires variable, equations | supported where the clause has the largest priority of its function | `clauseSorted` | none changes |
| D5 | (f) `#configuration` | **parameter** (reader only). "The configuration the term is evaluated in" is not a meaning any model of the text gives the symbol (§3.1) | none | none |
| D6 | non-executable beside `[owise]` | supported: `Clause.aside` | `Clause`, `Eval`, `lowerClauses`, `ClausesAgree` | none; `FnHyp` grows through `ClausesAgree` |
| D7 | constructor-with-function overload | undecided until its text is seen (no fixture); the two possible texts and their readings are given | `OvlSig`, `norm` or none | none expected |
| D8 | function in a left side, variables only under it | D3's case after `keyCut` | none beyond D3 | none |

To the owner, once: D3's unconditional form needs `Γ` to assert that every element of a sort is a value's (`ΓGen`, §2.5). That is more than any sentence of the text states; it is what K's values being free terms means. Estimated five units or more, not scheduled here.

## 1. Group (a): `?X` on a rule's right side

### 1.1 What the text states

Fixture e3-vars, sentence 329 (kore.txt:189-191): `\rewrites(lhs ∧ ⊤, \exists{C}(Var'Ques'Z:SortInt, rhs(Z) ∧ ⊤))`.
`\rewrites` is `φ → •ψ` (`sRewrites`, Kore/Signature.lean:141; `•` is `sNext`, "has a successor in"). The sentence is closed universally over its free variables (`trAxiom`), and Z is not free.
So at every valuation of the left side's variables: an element in `lhs` has **some** successor in `⋃_Z (rhs(Z) ∧ ens(Z))`. It does not say which instance, nor that there is only one.
With the closure axiom (`Γstep`, KCore's own), the successors by this rule are a subset of that union, nonempty where the rule applies and the union is.
The brief writes `⇒ ◦∃X.φ`; the library's `\rewrites` is the strong next, and the all-path form is what `Γstep` adds.

Consequence. Over the models of the text with the closure, the successors of x by an application (r, σ on the bound variables) are any nonempty subset W of the instances. The intersection over models is empty (two instances, two models), the union is every instance.

### 1.2 Step's successors: reading D1

`Step` keeps its text. With Z in `r.vars`, `Step.rule` quantifies σ over every well-sorted value of Z, so its successors are every instance whose right side evaluates and whose `ensures` is true: the union above, at values. `Step c x y` then reads "y is a successor of x in some model", not "in every model".
What the kernel lacked is the notion triage E3 names ("a step whose result the theory leaves open"): the **outcome** of an application is a family, `∃Z̄. (rhs ∧ ens)` at the match, not a value.

Reason. `Γ` then holds the text's sentence and nothing else about the rule, so the reading asserts no more than the text. A reading that strips the binder (TRIAGE-C undecided 1: "reading it needs only that the reader strip the binder") makes `Γ`'s axiom `∀Z`, every instance a successor in every model, which the text does not state.

Alternative D1' (not taken): the choice of W as a parameter of the interpretation, beside `hooks`, with `Γ` stating W's graph. Every headline statement then keeps its text, for every W. What it costs: `Γ` must hold "y is a successor" and "y is no successor" for the instances of existential rules as axioms of the interpretation (successors carry no rule tag, so no weaker pattern confines them to W), so soundness and completeness of those steps are true by membership in `Γ`; and consistency needs W nonempty wherever a witness exists, which is a normalisation inside `Step` (as `paramVal` normalises an ill-sorted answer). D1 proves more about the text; D1' pins less.
Reversal: the owner prefers unchanged headline texts to statements with content at existential rules; or a consumer needs one transition relation per model.

### 1.3 The old headline texts are false for the construct

Stated explicitly, as the brief asks. With `Γ` holding the text's sentence, no relation `Step` makes both old texts true when an application has two instances.

1. Old `SoundC`, second conjunct: `∀ x y, Step c x y → Γ c ⊧ (den x ⇒ •den y)`. Text `rule c() => d(?Z:Bool)`. `Step x d(true)` and `Step x d(false)`. The value model with the transition "c to d(true) only" satisfies `Γ ∪ Γstep` (the sentence asks for one successor in `∃Z. d(Z)`); in it `den c ⇒ •den d(false)` fails. If `Step` instead gave no successor, old `CompleteC` (`den x ⇒ ◦⊥`) fails in every model.
2. Old `CompleteC`: `den x ⇒ ◦ ⋁_{y ∈ ref x} den y`. Text `rule c() => d(?Z:Int) ensures ?Z ==Int 3`. `Step`'s successors are `[d(3)]`, `StepIs c ref` holds with that list. A model of `Γ ∪ Γstep` with one more element j in `⟦Int⟧`, `j ==Int 3` true (the graph of `==Int` is stated at values only), and successor `d(j)` satisfies the sentence and the closure; `den x ⇒ ◦ den d(3)` fails. Without an `ensures` and at an infinite sort the old text is true only because `StepIs` has no finite `ref`: vacuous.

To run (two witness files in the manner of `ModelPrioTextWitness.lean`): `theorem old_sound_false : ∃ c, c.coreOK = true ∧ FnHyp c ∧ ∃ x y, Step c x y ∧ ¬ (Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)))` on the first text; the second needs a non-standard model, so it is the costlier witness and may be left as the argument above if the first is kernel-checked.

### 1.4 Lean change

Core.lean, `Rule`: one field, last, with a default so that every `Rule` literal and generated package elaborates unchanged.

```lean
structure Rule where
  vars : List Srt
  lhs : Term
  req : Option Term
  rhs : Term
  ens : Option Term
  prio : Nat
  /-- the variables the right side binds by `\exists` (`?X`), in the text's order: indices of
  `vars` that neither the left side nor the `requires` holds -/
  exs : List Nat := []
  deriving Repr
```

Tie.lean (DefinitionWf.lean for the helpers), `ruleSorted`:

```lean
/-- The variables a rule's left side does not bind. -/
def Rule.opens (r : Rule) : List Nat :=
  (List.range r.vars.length).filter fun i => !(varOccs r.lhs).contains i
/-- A variable of the `requires` that the left side does not bind. -/
def Rule.reqOpen (r : Rule) : Bool :=
  r.opens.any fun i => (r.req.map varOccs).getD [] |>.contains i

def ruleSorted (r : Rule) : Bool :=
  sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort &&
  nodup r.exs && r.exs.all (fun i => r.opens.contains i && !((r.req.map varOccs).getD []).contains i) &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens &&
  sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort
```

`binds r.vars.length (varOccs r.lhs)` goes (groups a and b together); `Semantics.ok`'s `ruleOK` keeps it, so the executable matcher and `Exec.step_iff` are untouched (they are under `ok`).
`coreOK` gains `opensLast` (§2.3).

Faithful.lean, `prioRuleK`: only `right` changes; with `exs = []` the fold is the identity, so every existing package's `ruleItems` is the same term.

```lean
  let exV := r.exs.filterMap fun i => vs[i]?
  let right : Kore.Pattern :=
    exV.foldr (fun v p => .exist C v p) (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])
```

`rightDef := .ceil C C right` and both `\rewrites` branches keep their text: the premise becomes `⌈∃Z̄. rhs ∧ ens⌉`, the rule fires where some instance exists. `stepClosureItem` keeps its text: `closureDisjunct` binds `freeOf` of the rule pattern, and the `exs` are no longer free in it.

Step.lean, new beside `Step` (which keeps its text):

```lean
/-- `StepBy c r σ x y`: `Step.rule`'s premises for the rule r and the substitution σ. -/
structure StepBy (c : Semantics) (r : Rule) (σ : Subst) (x y : Config c) : Prop where
  mem : r ∈ c.rules
  hσ : c.WellSorted r.vars σ
  hmatch : PatVal c σ r.lhs x.val
  hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))
  heval : EvalTerm c σ r.rhs (some y.val)
  hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))
  hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val
theorem step_iff_by {c} {x y : Config c} : Step c x y ↔ ∃ r σ, StepBy c r σ x y
```

Faithful.lean, the family of an application (new; a statement's vocabulary, so cone):

```lean
/-- The outcome of rule r at a match σ of its left side: `∃ō. (⌈req⌉ ∧ ∃ē. (rhs ∧ ens))`, ō the
variables the left side does not bind less `exs`, ē the `exs`, each variable the left side binds
fixed to the element of its value under σ (`∃v:s. v = ⟦σ v⟧ ∧ …`, so the pattern is closed). -/
def famPat (c : Semantics) (r : Rule) (σ : Subst) : KoreAML.P := …   -- (lane): closeAt, existsK
/-- An outcome of a step: a value, or a rule's family at a match. -/
inductive Outcome where
  | val (y : GroundTerm)
  | fam (r : Rule) (σ : Subst)
def Outcome.pat (c : Semantics) : Outcome → KoreAML.P
  | .val y => den c y
  | .fam r σ => famPat c r σ
abbrev OutFn := GroundTerm → List Outcome
```

Sound.lean:

```lean
def SoundC (c : Semantics) : Prop :=
  (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c)) ∧
  (∀ (x y : Config c) r σ, StepBy c r σ x y → r.exs = [] →
     Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val))) ∧
  (∀ (x y : Config c) r σ, StepBy c r σ x y →
     Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (famPat c r σ)))

/-- `ref` lists, at x: `Step`'s successors by the rules whose left side binds every variable; and,
for each rule with a variable its left side does not bind, each match of its left side that no
rule of a smaller priority blocks, up to the values of the variables the left side binds. -/
def OutIs (c : Semantics) (ref : OutFn) : Prop := ∀ x : Config c,
  (∀ y, .val y ∈ ref x.val ↔
     ∃ (hy : c.sortOf y = some topCellSort) (r : Rule) (σ : Subst), r.opens = [] ∧ StepBy c r σ x ⟨y, hy⟩) ∧
  (∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, WellSortedAt c r (varOccs r.lhs) σ → PatVal c σ r.lhs x.val →
     (∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) →
     ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ ref x.val)

def CompleteC (c : Semantics) (ref : OutFn) : Prop :=
  OutIs c ref → ∀ x : Config c,
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (Outcome.pat c))))
```

`WellSortedAt` (lane) is `WellSorted` at the listed indices only: a sort of an open variable may have no value, and the match must still be listed.
`sound_at` becomes the two conjuncts' statements (`sound_at`: unchanged text plus the hypothesis that the step is by a rule with `exs = []`, i.e. stated over `StepBy`; `sound_at_fam`: the third conjunct). `complete_at` takes `(os : List Outcome)` and the two covering hypotheses of `OutIs` at x in place of `ys` and `hys`. `consistent_of`, `Consistent`, `StepDecided`, `FnHyp`, `coreOK`'s other conjuncts, `sound_hyp`'s and `complete_hyp`'s types up to `SoundC`, `CompleteC` and `OutFn`: unchanged.
Two lemmas keep the old texts as theorems where they were true: `soundC_closed`, `completeC_closed : (∀ r ∈ c.rules, r.opens = []) → (new ↔ old)`, old being the text at `1e306534` with `StepIs`. Pins.lean pins the new texts and these two.

Why the new `CompleteC` holds with no assumption on carriers: the closure's disjunct for r is `∃x̄_b. (L ∧ y ∈ R)` with the open variables bound inside it; the bound ones are values by `patVal_backC` as today; what is under the open binders is `famPat` itself. Why the family is listed at every unblocked match, not only where `Step` fires: where the only witness of `⌈right⌉` or of the `requires` is a non-value element, the model has a successor and `Step` none; the family covers it and is `⊥` in the models without it.
Why conjunct 3 holds: `StepBy` gives a value instance, so `⌈∃Z̄. right⌉` holds in every model and the sentence gives a successor in the family.

Reader (Parse.lean:1027 `ruleBody`): a second arm for `.rewrites _ (.and _ [l, r0]) R` where R is `.exist _ x₁ (… (.exist _ xₙ (.and _ [r, en])))`; the xᵢ are added to the variable list with their sorts, their indices are `exs`; an xᵢ occurring in `l` or `r0` cannot be written (scope). New `RefusalReason`s replacing `ruleShape` and the silent `wf false`: `existentialEquation` (an `\exists` on an equation's right side, §1.6), `openRequires` (§2.3). Emit's rule axiom prints the binders in `exs` order (outside the cone; `Reordered` needs it).

### 1.5 Proofs that change

`step_sound_core`, `step_complete_at`, `Model.has_model_core` and what they call read `rule_ctx`'s `hbinds` at 16 rule sites (FaithfulSound:98, FaithfulCompleteAt:87-156, FaithfulComplete:306-317 and 394-463, FaithfulNeg:2161-2184 and 2657-2681, FaithfulStage2:1132-1209, Stage3:434-510, Stage4:506, 967-974, 1081, ModelStep:251-341, ModelRules:133-154, ModelPat:616, 758). Each use is one of three kinds: (i) "variable i is free in the axiom and in the table": true of every non-`exs` variable from `sortOfTerm` of the side that holds it, to be re-derived per side; (ii) "the model's witness for variable i is a value" (`hwit`): kept for `varOccs r.lhs`, and the open variables stay under the family's binders; (iii) a competitor's `applies` is empty where `NotApplies` (`applies_empty`, `appEmpty_of_plain`): true as before for a competitor without `reqOpen`, which `opensLast` guarantees.
The model (`has_model_core`): the value model's transition is `Step`; for an existential rule the sentence asks one successor in the family where `⌈right⌉`, and in the value model every element is a value, so a witness is a `StepBy`.

### 1.6 Clause.ens and the tie

`Rule.ens` is where `?X` is constrained (`ensures ?X >Int 0`); it is under the binder, as the text has it. `Clause` gets no `exs`: `f(x̄) = ∃Z. r(Z)` equates a function symbol, at most one element in every model, with a union; it has a model only where the instances are one element, and "the Z such that" is not a term. Refused `existentialEquation`, reason as stated; no fixture shows kompile writes one. Reversal: a kompiled text holding one.
Tie (TIE-0 §1.3 row 1): unchanged class. W1: the text's sentence entails `Γ`'s item, which adds `¬⋁ competitors` and `⌈∃Z̄. right⌉` to the left side and has the text's right side. W2 is `AtValues` over the free variables, and the `exs` are not free.

## 2. Group (b): variables no left side binds

### 2.1 What the text states

The axiom is closed universally over every free variable, at the carriers of their sorts.
- Right-side variable (e2-unbound kore.txt:94, `a() => b(X)`): `∀X. (lhs ∧ ⌈right(X)⌉ → •right(X))` in `Γ`'s form: every instance is a successor, in every model.
- Requires variable (e2-rule kore.txt:170-186, HOLE of sort K): `∀H. (lhs ∧ ⌈req(H)⌉ → •rhs)`, which is `(lhs ∧ ∃H. ⌈req(H)⌉) → •rhs`.
- Ensures-only variable: `(lhs ∧ ∃E. ⌈rhs ∧ ens(E)⌉) → •rhs`.
- Equation (e2-cool-eq kore.txt:80-84): `∀X H. (req(H) ∧ args ∈ pats → f(args) = rhs)`.

### 2.2 D2: right-side and ensures-only variables

`Step` already carries it (σ over `r.vars`). `sound_at`'s old form holds per instance: a value instantiates the universal closure (first new conjunct of `SoundC`, `exs = []`). Completeness is by the family, as for (a): the old list form is false at a sort with a non-value element and finitely many values (Bool has no axiom confining it) and vacuous at Int.
No declaration beyond §1.4's. Difference from (a) in `Γ`: the variable stays free in `prioRuleK`, so `trAxiom` closes it universally.

### 2.3 D3: requires variables in rules

`Step` asks a value H. Soundness per instance holds for the rule itself. Two failures without a statement about carriers, both with no value witness and a non-value one:
(i) a rule r of larger priority fires in `Step`, and in that model the competitor applies, so `Γ`'s axiom for r is silent: old and new `sound_at` false for r;
(ii) the rule gives a successor in that model and `Step` none: covered by the family in the new `CompleteC`.
So (ii) costs nothing and (i) is excluded by a decided condition:

```lean
/-- A rule whose `requires` holds a variable its left side does not bind has the largest priority:
it is no competitor of any rule. -/
def Semantics.opensLast (c : Semantics) : Bool :=
  c.rules.all fun r' => !r'.reqOpen || c.rules.all fun r => decide (r.prio ≤ r'.prio)
```

a conjunct of `coreOK` (through `sortedOK` or beside it; the lane follows where `ruleSorted` enters).
Reason: it is the exact condition under which no negated premise of `Γ` quantifies over a carrier. Reversal: `ΓGen` (§2.5) lands; the conjunct is then dropped and nothing else changes.
A text that fails it is refused `openRequires` ("a `requires` variable the left side does not bind, in a rule that a rule of larger priority competes with: whether it applies where no value satisfies the `requires` depends on elements the text does not confine to values").
Fixture e2-rule fails it (its `[cool]` and `[heat]` rules have priority 50 beside priorities 60 and 200), so e2-rule stays refused, now by name; the supported shape needs a fixture of its own (§5).

### 2.4 D4: equations

`clauseSorted`: `binds cl.vars.length (varOccsList cl.pats)` goes; `fnsOK`-level condition added:

```lean
def Clause.reqOpen (cl : Clause) : Bool :=
  (List.range cl.vars.length).any fun i =>
    !(varOccsList cl.pats).contains i && ((cl.req.map varOccs).getD []).contains i
/-- A clause whose `requires` holds a variable its patterns do not bind has the largest priority of
its function: no equation's premise negates it. -/
def Semantics.clauseOpensLast (c : Semantics) : Bool :=
  c.fns.all fun f => f.clauses.all fun cl' => !cl'.reqOpen || f.clauses.all fun cl => decide (cl.prio ≤ cl'.prio)
```

Why no statement changes. `consistent_of`: in the value model every element is a value, so the equation holds as `Eval` reads it (`FnSolves`). In another model where only a non-value H satisfies the `requires`: the equation gives `f(vs) = rhs` and `ΓFallback` (all clauses `Fail`) gives the rest, or a clause of the same priority gives its value; either they agree or that interpretation is no model. No axiom negates the clause, by `clauseOpensLast`.
A right-side or `ensures` variable the patterns do not bind is admitted by the same change: `∀Z. f(x̄) = r(Z)` has a model only where r does not depend on Z, which is `MatchIndependent`, already an obligation of `FnHyp`; with lane CE's second `Eval` constructor an `ensures` false at one Z and true at another gives `none` and a value, and `FnDet` fails. Both are properties of the text shown by an unprovable hypothesis, not refusals.
14 clause sites read `hbinds` (ModelFns:273-724, FaithfulStep:721-1284, FaithfulStage2:318-755, Stage3:58-74, Stage4:435-620, FaithfulNeg:2094-2152, EvalSound:103-172, SubjectReduction:1519). Not read: whether `EvalSound`'s and `SubjectReduction`'s uses are only "σ is defined at i", which `WellSorted` gives without `binds`.

### 2.5 What lifts D3's condition: `ΓGen` (not scheduled; owner decision)

A part of `Γ` stating that every element of a sort of the definition is the element of a ground value.
It cannot be assembled from what `Γ` has: (i) a domain value is the symbol `dv lit` applied to its sort (Translate.lean:161), one symbol per literal, so no pattern denotes "the literals of a token sort"; Int (`μX. 0 ∨ X +Int 1 ∨ X -Int 1` over the hook's graph) and Bool can be stated, String, Bytes, Float, KConfigVar and the token sorts cannot without giving literals structure in the encoding; (ii) the constructor sorts need one least fixed point over all generators, not one per sort. HOLE has sort K in both fixtures, and K reaches KConfigVar in every text, so a partial `ΓGen` supports no fixture.
It asserts more than the text (the text's no-junk axioms are one unfolding); TIE-0 TR-2's reversal clause names the same change. Estimate: encoding symbols and their axioms 1 unit, the value model satisfies them 2, "every element is a value" 1, removing `opensLast` 1.

### 2.6 Clause.ens and the tie

`Clause.ens` reads patterns' and `requires`' variables only for "applies" (D1 of REVIEW-FA), so `reqOpen` is the only notion that needs the priority condition; an `ensures`-only open variable of a clause is §2.4's last paragraph.
Tie: rules stay row 1 (W1, W2). W2's `AtValues` sends every free variable, the open ones included, to a value, which is exactly `Step`'s reading; the open requires variable is where Ev holds and E does not. Equations: rows 2 and 3 unchanged (E at values).

## 3. Group (f): `#configuration`

### 3.1 What the text states

`hooked-symbol Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K{}() : SortK{} [function, hook(KREFLECTION.configuration), impure]` (domains.md:2380), no equation.
A nullary function symbol denotes, in each model, at most one element of K, the same in every pattern and at every valuation. The text states its sort and nothing else.
"The configuration the term is evaluated in" is not a value of that symbol in any model: two configurations in which a rule applies it would need two values of one constant, and distinct values are distinct elements (`ΓDomains`). So as a statement about this symbol it has no model; as a statement about rules it is a different sentence (`lhs #as C => … C …`), which the text does not hold and `Γ` with it would not entail (C14, entailed direction).
This is the first-principles reason, and it cuts the other way from the triage: the intended meaning is what KCore cannot state as the text's, and the text's own meaning needs no notion the kernel lacks.

### 3.2 D5

Read as the other seven K-REFLECTION hooks: a parameter symbol of the definition (`ParamSig` with `args = []`, `result = Srt.k`, `impl = none`, `ReadingNote.reflectionAsOwn`), status `parameter`. Every theorem holds for every `H`; at `HookParams.none` the application is undefined and a rule whose right side holds it gives no step.
Reader only: Parse.lean:386 and :1698 stop special-casing `configurationLabel`; `RefusalReason.configurationReflection` and `UnreadReason.configurationReflection` go. Cone: none. By R-11 the R-c refusal was not admissible once this reading exists.
The reading note must say that K's documentation gives the symbol a meaning that depends on the state and that no interpretation here is that meaning.
Reversal: the owner wants the documented behaviour. Then it is not this symbol's meaning but a reading "not as written" (each rule applying it reads its left side `#as C`; in a function there is no configuration, so `EvalTerm`, `Eval` and `HookParams.app` would take one: the triage's cone), with a C6 guard, and layer 2 of C14 fails for those sentences by construction.
`impure` is an attribute with no sentence; inert.

## 4. Sub-cases

### 4.1 D6: non-executable beside `[owise]`

Text (Parse.lean:126-132, :984-989 describe it; no fixture in the constructs tree): the `non-executable` equation is an axiom without a premise about other equations; the `[owise]` equation's premise negates the function's other equations except the non-executable ones. So the `[owise]` equation applies also where the non-executable one does, and where both apply the text states both values.
KCore's total order cannot say that: at priority below 200 the non-executable clause blocks the `[owise]` clause, at 200 or more the smaller priorities block it.

```lean
structure Clause where
  …
  prio : Nat := 50
  /-- an equation no `[owise]` premise negates (`non-executable`): it blocks no clause -/
  aside : Bool := false
```

`Eval.clause`: `hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl'`.
`Faithful.lowerClauses f cl := f.clauses.filter fun cl' => !cl'.aside && cl'.prio < cl.prio`.
`ClausesAgree`: `cl.prio = cl'.prio ∨ cl.aside = true ∨ cl'.aside = true → Coherent …`.
The two values at an overlap are then `ClausesAgree`'s to equate; where they differ `FnDet` fails and no theorem with `FnHyp` is stated, which is the text having no model there. Headline texts unchanged; `FnHyp` is stronger only for a function with an `aside` clause.
Reversal: a kompiled text whose `[owise]` premise does negate a non-executable equation.

### 4.2 D7: constructor-with-function overload

Not decidable from the reading set: triage marks it "suspected", there is no fixture, and Value.lean, OvlLaws.lean and Parse.lean:1951-2110 were not read.
The axiom is `f(inj x̄) = inj(g(x̄))`. Two texts are possible and they differ in what they state:
1. f keeps `constructor` and its no-confusion axioms. Then wherever g(ā) is defined the text equates an f-application with a term of another head or another f-application: no model there. A property of the text; the reading is f a constructor and the axiom refused by name, R-a in effect (nothing to support).
2. f is declared without `constructor` (an overloading symbol in `OvlSig`'s sense). Then the meaning is statable: `OvlSig.over` may name a function, and at covered arguments the application's value is g's, injected, undefined where g is. `Semantics.norm` is a function on values and cannot evaluate g, so the covered case moves into `EvalTerm` (an application of an overloading symbol whose covering overload is a function evaluates `g(ā)` by `Eval`); `ovlEqItem` keeps its form. Cone: `OvlSig` (doc), `EvalTerm`, `overloadsOK`.
Unit: the fixture first (§5), then one of the two.

### 4.3 D8: a function in a left side, a variable only under it

Text: `∀X. (c(f(X)) ∧ … → •rhs(X))`. The reader-only cut (TRIAGE-C B51) gives left side `c(V)`, `requires V ==K f(X)`: X is then a requires variable (and a right-side one) the left side does not bind. It is D3's case exactly: supported under `opensLast`, family outcome `∃X. (⌈V ==K f(X)⌉ ∧ rhs(X))`, successors in `Step` every value preimage. No declaration of its own.

## 5. Units

Costs are Opus lane sessions (one session: one brief, library modules rebuilt by lake-serial). No unit leaves a `sorry`; each ends with the headline theorems proved in the text it introduces.

**Brief CN-A (rules), in order.**
- A1, statements at closed rules. `StepBy`, `step_iff_by`, `Rule.opens`, `famPat`, `Outcome`, `OutFn`, `OutIs`, the new `SoundC`, `CompleteC`, `sound_at`, `sound_at_fam`, `complete_at`, `soundC_closed`, `completeC_closed`, Pins. `ruleSorted` unchanged, so every rule has `opens = []` and the proofs are the old ones through the two `_closed` lemmas. 1 session. Test: the library builds; Pins.
- A2, open universal variables. `ruleSorted` without `binds`, `Rule.reqOpen`, `opensLast`, the 16 sites of §1.5, the family case of `complete_at`. `exs` still `[]`. 2 sessions. Fixtures: e2-unbound, expectations from sentence kore.txt:94: account `parse: ok; wf true`; at x with `<k> a() </k>`: `∀ i : Int, Step c x (… b(i) …)`; `Γ c ⊧ den x ⇒ •den (b(i))` for every i; `OutIs` holds with one `fam`. New fixture e2-heatcool-last (the two rules `c(1) => b(1) [cool]`, `c(2) => b(2) [heat]` with `syntax KResult ::= Int`, no other rule): `Step` from c(1) to b(1), witness HOLE = `kseq(inj{Int,KItem}(0), dotk)`, from the `isKResult` equation of Int; from c(2) to b(2), witness HOLE = `dotk`, from `isKResult`'s `[owise]` equation. e2-rule: account prints `openRequires`.
- A3, existential variables. `Rule.exs`, `prioRuleK`'s `right`, the reader arm, Emit, the third conjunct of `SoundC`, the model case. 1 to 2 sessions. Fixture e3-vars, from sentence 329: account `stage refusals: 0`; `∀ i, Step c x (… d(i) …)` at `c(1, 2)`; `Γ c ⊧ den x ⇒ •famPat c r σ`; and the witness of §1.3 item 1 (to run).

**Brief CN-B (equations and reader-only), independent of CN-A except B3.**
- B1, `clauseSorted` and `clauseOpensLast` (§2.4). 1 to 2 sessions. Fixture e2-cool-eq, from kore.txt:80-84: `wf true`; `∀ H, Eval (c.withHooks H) f [int 3] (some (int 3))` (witness as above); the second sentence stays `inert simplification`.
- B2, `#configuration` as a parameter (§3.2). Half a session, reader only. New fixture e6-configuration (`imports K-REFLECTION`, `rule <k> get => #configuration ... </k>`): account `8 read reflectionAsOwn`, no `configurationReflection` line; the `param_undetermined` shape of C2 for the symbol; `∀ y, ¬ Step c x y` at `HookParams.none`.
- B3, the function cut for an open variable (§4.3), after A2. Half a session, reader only. New fixture: `rule <k> c(f(X)) => d(X) ... </k>` with f a total function with two preimages of one value; expectation: both `d` instances are `Step` successors, derived from f's equations.

**Brief CN-C (function-level sub-cases).**
- C1, `Clause.aside` (§4.1). 2 sessions (`Eval` is read by every evaluation proof). New fixture e5-owise-nonexec: `choose(a, Y) => Y`, `choose(b, Y) => Y [non-executable]`, `choose(X, _) => X [owise]` over constructors a, b. From the three sentences: at (b, a) the text states `choose(b, a) = a` and `= b`; expected `Eval c choose [b, a] (some a)` and `(some b)`, hence `¬ FnDet c`; at (b, b) one value.
- C2, the overload fixture (KFIX: a constructor production and a function production in one overload set), then §4.2's case 1 (half a session) or case 2 (2 sessions, to be re-briefed).

Order across briefs: A1 first (it moves the pins once); B1, B2, C1 parallel to A2; A3, B3 after A2.

## 6. Findings (review form)

1. `Γ` / Faithful.lean:204-223, FaithOK.lean:47. Claim: `Γ` confines no domain sort to its values and confines constructor sorts per sort only, so every statement about an unbound variable is carrier-relative. Evidence: `ΓDomains`' five disjuncts; `consSorts` filters out token sorts and `genWf` asks `s != Srt.int && s != Srt.bool …`. Shown by reading. Settles: nothing to settle; it is the premise of §2.
2. Sound.lean `SoundC`, `CompleteC`. Claim: both are false for `?X` under the text's sentence, for any `Step`. Evidence: §1.3. Shown by argument; item 1 to run.
3. TRIAGE-C undecided 1. Claim: its "to run" is settled by reading: `coreOK` is false on a rule with Z in `vars` and not in the left side, by `ruleSorted`'s `binds` (Tie.lean:74). And stripping the binder is not a reading of the sentence (§1.2). Shown by reading.
4. TRIAGE-B group unbound-variable, `settle`. Claim: "state sound_hyp and complete_hyp with ruleSorted lacking `binds`" is not enough: with a competitor holding an open requires variable `sound_at` is false. Evidence: §2.3 (i). Shown by argument. Settles: a witness semantics with a rule of priority 10 whose `requires` is `f(H) ==Int 1`, f partial, and a non-standard model; costly, the argument may stand.
5. TRIAGE-C E6 configuration-reflection. Claim: R-c was not admissible; the text's meaning is a parameter. Evidence: §3.1. Shown by reading the declaration.
6. Fixture e2-rule. Claim: it cannot be the `supported` evidence for author-written heat/cool at this stage; it mixes priorities. Evidence: e2-rule.k lines 6-13. Shown.

## 7. Not read

Value.lean, OvlLaws.lean, Evaluation.lean beyond `WellSorted` and `Eval`'s constructors' heads, the bodies of the model and stage proofs (sites located by `hbinds`, their kinds judged from the surrounding lines of FaithfulCompleteAt only), Emit.lean, Parse.lean beyond the cited lines, K8, TIE-0 beyond §1, whether `hookSigs` holds `+Int` unconditionally (used only in §2.5), the fixtures' kore.txt beyond the cited sentences, and the k-rust fixture `owise-ignored-competitors.k`. Whether kompile's `[owise]` premise omits non-executable equations rests on the reader's own comment (Parse.lean:984-986), not on a text I read.
