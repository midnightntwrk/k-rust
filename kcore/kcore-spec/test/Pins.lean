/-
  The headline statements of KCore, restated in full. Each restatement is checked against the
  library's declaration: a definition by `rfl` against its body written out (a structure by an `Iff`
  with its fields, `StepBy`), a theorem by its proof term at the type written out. A change to what
  one of them says makes this file fail to compile; a change that keeps the meaning (a renamed bound
  variable, a body unfolded into an equal helper) does not. What the restated bodies mention (`Γ`,
  `Γstep`, `den`, `KoreAML.denB`, `Step`, `NotApplies`, `RuleApplies`, `Holds`, `Eval`, `confined`,
  `ruleRight`, `applies`, `prioRuleK`, `boolClosed`, the conjuncts of `coreOK`, and the `₀`
  declarations) is pinned by the review cones (test/ReviewCone.lean, cones (iv) to (vii)), not here.
  `FnDet`, `FnSolves` and `ClausePreDecided`, hypotheses of `consistent_of` and of `CExec.run_exact`
  that no cone root reaches, are restated here, with `Clause.DecidesAt`. So are the statement definitions of the tie
  to a KORE text (`AtValues`, `EntailsAtValues`, `SetVarsAtValues`, `EntailsAtSetValues`,
  `SetVarsAtMostOne`, `symbolsOf`, `surplusItem`, `attrsAgree` with the
  checks it is made of) and the classes of an account with their directions (`tieClasses`). So are
  the rows' statements: `kore.k`'s three (`KK.SuccsSound`, `KK.SuccsStuck`, `KK.SuccsComplete`, with
  `KK.SuccsAt`, `KK.d₀`, `KK.K₀`, `KK.Sig`, `KK.St` and `CoherentAll`), and the all-path claims the
  consumer's statement is made of (`Reachability.AllPath`, `CPath`, `Progress`); the consumer's
  statement, which is about ref-kimp's semantics, is pinned in test/PinsKimp.lean.

  The axioms of every theorem pinned here are exactly `propext`, `Classical.choice` and
  `Quot.sound` (`#guard_msgs` fails the file on any other list). Run from kcore-spec, after the
  library:

      lake env lean test/Pins.lean
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.Pins

open KCore ML Faithful

/-! ## The definitions -/

example (c : Semantics) : SoundC c =
    ((∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ (x y : Config c) (r : Rule) (σ : Subst), StepBy c r σ x y →
        (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧
        (Γc c ⊧ (den c y.val ⇒ famEx c r σ))) := rfl

example (c : Semantics) (ref : OutFn) : CompleteC c ref =
    (OutIs c ref → ∀ x : Config c, (Γc c ∪ Γstep c) ⊧
      (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (Outcome.pat c))))) := rfl

example (c : Semantics) : ExactC c = (∀ x y : Config c,
    Step c x y ↔ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) := rfl

example (c : Semantics) (ref : OutFn) : OutIs c ref = (∀ x : Config c,
    (∀ y, .val y ∈ ref x.val ↔
       ∃ (hy : c.sortOf y = some topCellSort) (r : Rule) (σ : Subst),
         r.opens = [] ∧ StepBy c r σ x ⟨y, hy⟩) ∧
    (∀ r σ, .fam r σ ∈ ref x.val → r ∈ c.rules ∧ r.opens ≠ [] ∧ Unblocked c r σ x.val) ∧
    (∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
       ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ ref x.val)) := rfl

example : OutFn = (GroundTerm → List Outcome) := rfl
example (c : Semantics) (y : GroundTerm) : Outcome.pat c (.val y) = den c y := rfl
example (c : Semantics) (r : Rule) (σ : Subst) : Outcome.pat c (.fam r σ) = famOpen c r σ := rfl

example (c : Semantics) (r : Rule) (σ : Subst) : famEx c r σ =
    (let C := srtOf c topCellSort
     let vs := canonVars c r.vars
     let fixed := (List.range r.vars.length).filter fun i => !r.exs.contains i
     KoreAML.denB (KoreAML.existsAll C ((fixed.filterMap (vs[·]?)).map KoreAML.Var.kore)
       (.and C (fixK c r σ fixed ++ [ruleRight c r])))) := rfl

example (c : Semantics) (r : Rule) (σ : Subst) : famOpen c r σ =
    (let C := srtOf c topCellSort
     let vs := canonVars c r.vars
     let outer := (List.range r.vars.length).filter fun i => !r.exs.contains i
     KoreAML.denB (KoreAML.existsAll C ((outer.filterMap (vs[·]?)).map KoreAML.Var.kore)
       (.and C (fixK c r σ (varOccs r.lhs) ++ [reqPat C (r.req.map (Term.kore c vs))] ++
         Cond.conj c vs C r.pre ++ [ruleRight c r])))) := rfl

example (c : Semantics) (r : Rule) (σ : Subst) (x : GroundTerm) : Unblocked c r σ x =
    (c.WellSortedAt r.vars (varOccs r.lhs) σ ∧ PatVal c σ r.lhs x ∧
      ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x) := rfl

/-- `StepBy` is a structure: its fields, by the two anonymous constructors. -/
example (c : Semantics) (r : Rule) (σ : Subst) (x y : Config c) : StepBy c r σ x y ↔
    (r ∈ c.rules ∧ c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧
     (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
     Holds c r.vars.length σ r.pre true ∧ EvalTerm c σ r.rhs (some y.val) ∧
     (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧
     Holds c r.vars.length σ r.post true ∧
     ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) :=
  ⟨fun ⟨a, b, d, e, f, g, h, i, j⟩ => ⟨a, b, d, e, f, g, h, i, j⟩,
   fun ⟨a, b, d, e, f, g, h, i, j⟩ => ⟨a, b, d, e, f, g, h, i, j⟩⟩

example (c : Semantics) (x : GroundTerm) : StepDecided c x =
    (∀ r ∈ c.rules, (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) →
      (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
        (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
      (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
        (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
          (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
          ∃ b, Holds c r.vars.length σ r.post b)) := rfl

example (c : Semantics) : FnHyp c =
    ((∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c fn.label vs r) ∧
      (∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) ∧
      (∀ fn ∈ c.fns, ClausesAgree c fn) ∧
      (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) ∧
      OpenDecided c ∧ OpenLaws c) := rfl

example (c : Semantics) (cl : Clause) : MatchIndependent c cl =
    (Coherent c cl cl ∧
      (cl.exs ≠ [] → ∀ f fn vs σ, c.lookupFn f = some fn → cl ∈ fn.clauses →
        cl.Decides c fn σ vs → ∃ r, cl.Res c σ r)) := rfl

example : ∀ {c : Semantics} {cl : Clause}, cl.exs = [] → (MatchIndependent c cl ↔ Coherent c cl cl) :=
  @matchIndependent_iff_noExs

example (c : Semantics) (cl cl' : Clause) : CoherentPlain c cl cl' =
    (∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
      (∀ t, cl.req = some t → HDet c σ t) →
      ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs) →
      (∀ t, cl.ens = some t → HDet c σ t) →
      (∃ f fn, c.lookupFn f = some fn ∧ cl ∈ fn.clauses ∧ cl' ∈ fn.clauses ∧
        cl.Decides c fn σ vs ∧ cl'.Decides c fn σ' vs) →
      (cl.rhs = cl'.rhs ∧ cl.ens = cl'.ens ∧ (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∧
        ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) ∨
      ∀ r r',
        ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧ EvalTerm c σ cl.rhs r ∨
          ∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ r = none) →
        ((∀ t, cl'.ens = some t → EvalTerm c σ' t (some (bool true))) ∧ EvalTerm c σ' cl'.rhs r' ∨
          ∃ t w, cl'.ens = some t ∧ EvalTerm c σ' t w ∧ w ≠ some (bool true) ∧ r' = none) →
        r = r') := rfl

example : ∀ {c : Semantics} {cl cl' : Clause}, cl.exs = [] → cl'.exs = [] → cl.post = .top → cl'.post = .top →
    (Coherent c cl cl' ↔ CoherentPlain c cl cl') := @coherent_iff_noExs

example (c : Semantics) : OpenDecided c =
    ((∀ r ∈ c.rules, r.needsWitness c = true → r.CondDecided c) ∧
      (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)) := rfl

example (c : Semantics) : OpenLaws c =
    (∀ k ∈ c.params, k.raw = true →
      (k.assoc = true → OpenAssoc c k.sig.name k.sig.result) ∧
      (k.idem = true → OpenIdem c k.sig.name k.sig.result)) := rfl

example (c : Semantics) : OpenTotal c =
    (∀ k ∈ c.params, k.raw = true → ∀ vs, c.sortsOf vs = some k.sig.args →
      (c.paramVal k.sig.name vs).isSome = true) := rfl

example (c : Semantics) (f : Sym) (s : Srt) : OpenAssoc c f s =
    (∀ a b d, c.sortsOf [a, b, d] = some [s, s, s] →
      (c.paramVal f [a, b]).bind (fun ab => c.paramVal f [ab, d]) =
      (c.paramVal f [b, d]).bind (fun bd => c.paramVal f [a, bd])) := rfl

example (c : Semantics) (f : Sym) (s : Srt) : OpenIdem c f s =
    (∀ a, c.sortOf a = some s → c.paramVal f [a, a] = some a) := rfl

example (c : Semantics) (l : LawEq) : LawAt c l =
    (∀ σ, c.WellSorted l.vars σ → ∀ r, EvalTerm c σ l.lhs r ↔ EvalTerm c σ l.rhs r) := rfl

example (c : Semantics) (ls : List LawEq) : FnLaws c ls = (∀ l ∈ ls, LawAt c l) := rfl

example (c : Semantics) (r : Rule) : r.needsWitness c =
    (r.reqOpen && r.reqClosed && !r.openCondVars.all fun i => (r.vars[i]?.map c.confined).getD false) := rfl

example (c : Semantics) (cl : Clause) : cl.needsWitness c =
    (cl.reqOpen && cl.reqClosed && !cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false) := rfl

example (c : Semantics) (r : Rule) : r.Witnessed c =
    (∃ σ, c.WellSortedAt r.vars r.condVars σ ∧
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true) := rfl

example (c : Semantics) (cl : Clause) : cl.Witnessed c =
    (∃ σ, c.WellSortedAt cl.vars cl.condVars σ ∧
      (∀ t, cl.req = some t →
        EvalTerm c σ t (some (bool true)) ∧ ∀ r, EvalTerm c σ t r → r = some (bool true)) ∧
      Holds c cl.vars.length σ cl.pre true) := rfl

example (c : Semantics) (r : Rule) : r.condK c =
    (let C := srtOf c topCellSort
     let vs := canonVars c r.vars
     KoreAML.existsAll C
       ((((List.range r.vars.length).filter r.condVars.contains).filterMap (vs[·]?)).map KoreAML.Var.kore)
       (.and C ([reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre))) := rfl

example (c : Semantics) (cl : Clause) : cl.condK c =
    (let B := srtOf c Srt.bool
     let vs := canonVars c cl.vars
     KoreAML.existsAll B
       ((((List.range cl.vars.length).filter cl.condVars.contains).filterMap (vs[·]?)).map KoreAML.Var.kore)
       (.and B ([reqPat B (cl.req.map (Term.kore c vs))] ++ Cond.conj c vs B cl.pre))) := rfl

example (c : Semantics) (r : Rule) : r.Refuted c = (Γc c ⊧ ∼ KoreAML.denB (r.condK c)) := rfl
example (c : Semantics) (cl : Clause) : cl.Refuted c = (Γc c ⊧ ∼ KoreAML.denB (cl.condK c)) := rfl
example (c : Semantics) (r : Rule) : r.CondDecided c = (r.Witnessed c ∨ r.Refuted c) := rfl
example (c : Semantics) (cl : Clause) : cl.CondDecided c = (cl.Witnessed c ∨ cl.Refuted c) := rfl
example (c : Semantics) : Γc c = (Γ c ∪ Γcl c) := rfl
example (c : Semantics) : Γcl c =
    (fun φ => c.readsConfined = true ∧ c.litSort Srt.bool = true ∧ φ = boolClosed c) := rfl

example (c : Semantics) : c.plain =
    (c.rules.all (fun r => r.exs.isEmpty && r.pre.isTop && r.post.isTop &&
      binds r.vars.length (varOccs r.lhs)) &&
    c.fns.all (fun f => f.clauses.all fun cl => !cl.aside && cl.exs.isEmpty && cl.pre.isTop &&
      cl.post.isTop && binds cl.vars.length (varOccsList cl.pats)) &&
    c.params.all (fun k => !k.raw) && c.lib.carriers.isEmpty &&
    c.ovls.all (fun o => o.over.all fun g => !(c.fns.any (·.label == g)))) := rfl

example (c : Semantics) : SoundC₀ c =
    ((∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c)) ∧
      ∀ x y : Config c, Step₀ c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val))) := rfl

example (c : Semantics) (ref : StepFn) : CompleteC₀ c ref =
    (StepIs₀ c ref → ∀ x : Config c,
      (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c))))) := rfl

example (c : Semantics) : Consistent c =
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc c ∪ Γstep c)) := rfl

/-- `FnDet`: every function has at most one result at each argument list. -/
example (c : Semantics) : FnDet c = (∀ f vs r r', Eval c f vs r → Eval c f vs r' → r = r') := rfl

/-- `ClausePreDecided`: each clause's predicate has a truth value wherever its patterns match. -/
example (c : Semantics) : ClausePreDecided c =
    (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ σ vs, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs →
      ∃ b, Holds c cl.vars.length σ cl.pre b) := rfl

/-- `FnSolves`: where a clause decides, the function's values are the values the instances of that
clause's right side give. `Clause.DecidesAt`, `Clause.Gives`, `AgreeOff` and `Clause.exsFree`,
which it reads, are in no review cone, so their texts are here too. -/
example (c : Semantics) : FnSolves c =
    (∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∀ cl ∈ fn.clauses, ∀ σ,
      cl.DecidesAt c fn σ vs → ∀ v, Eval c fn.label vs (some v) ↔
        ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) := rfl

/-- Where no clause has an existential variable and every right side's predicate is `\top`,
`FnSolves` is: where a clause decides, the function's values are that clause's right-hand side's
where its `ensures` evaluates to `true`. -/
example : ∀ {c : Semantics}, (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top) →
    (FnSolves c ↔
      ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∀ cl ∈ fn.clauses, ∀ σ,
        cl.DecidesAt c fn σ vs → ∀ v, Eval c fn.label vs (some v) ↔
          EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) :=
  @fnSolves_iff_noExs

example (c : Semantics) (cl : Clause) (σ : Subst) (v : GroundTerm) : cl.Gives c σ v =
    (EvalTerm c σ cl.rhs (some v) ∧ (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c cl.vars.length σ cl.post true) := rfl

example (is : List Nat) (σ σ' : Subst) : AgreeOff is σ σ' = (∀ i, i ∉ is → σ'.lookup i = σ.lookup i) := rfl

example (cl : Clause) : cl.exsFree = cl.exs.filter (!cl.leftVars.contains ·) := rfl

example (c : Semantics) (fn : Fn) (cl : Clause) (σ : Subst) (vs : List GroundTerm) :
    cl.DecidesAt c fn σ vs =
    (cl.AppliesAt c σ vs ∧
      ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
        ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
          ¬ ((∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) ∧
             Holds c cl'.vars.length σ' cl'.pre true)) := rfl

/-- `StepIs`: `ref` lists exactly the configurations `Step` reaches in one step. -/
example (c : Semantics) (ref : StepFn) : StepIs c ref =
    ∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔ ∃ hy : c.sortOf y = some topCellSort, Step c x ⟨y, hy⟩ :=
  rfl

/-- `StepFn`: a step function on ground values. -/
example : StepFn = (GroundTerm → List GroundTerm) := rfl

/-- `Semantics.coreOK`: the six decidable conditions. -/
example (c : Semantics) : c.coreOK =
    (c.sortedOK && c.faithCoreOK && c.hooksApart && c.predsApart && c.idsOK && c.overloadsOK) := rfl

/-! The old texts no root of the cone reaches through a definition. -/

example (c : Semantics) (r : Rule) (x : GroundTerm) : NotApplies₀ c r x =
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x → RuleReqFails₀ c σ r) := rfl

example (c : Semantics) (ref : StepFn) : StepIs₀ c ref =
    (∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔
      ∃ hy : c.sortOf y = some topCellSort, Step₀ c x ⟨y, hy⟩) := rfl

example (c : Semantics) (r : Rule) (rp : RulePres) : applies₀ c r rp =
    (let C := srtOf c topCellSort
     let vs := KoreAML.varList (r.vars.map c.sortName) rp.names
     KoreAML.existsAll C (vs.map KoreAML.Var.kore)
       (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))])) := rfl

example (c : Semantics) (r : Rule) : prioRuleK₀ c r =
    (let C := srtOf c topCellSort
     let vs := canonVars c r.vars
     let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies₀ c r' (canonRulePres r')
     let right : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
     let rightDef : Kore.Pattern := .ceil C C right
     if comps.isEmpty then
       .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), rightDef]) right
     else .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
         .not C (anyOfC C comps), rightDef]) right) := rfl

/-! ## The tie's statement definitions (C14) and the classes' directions -/

example (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M) (a : Kore.Axiom) :
    AtValues c I e a =
    (∀ n s, KoreAML.VarKey.evar n s ∈ (KoreAML.freeOf [] a.pattern).eraseDups →
      ∃ (v : GroundTerm) (S : Srt), srtOf c S = s ∧ c.sortOf v = some S ∧
        (den c v).interpret I e (e.evalEvar ((KoreAML.tableOf a.sortVars a.pattern).ev (.evar n s)))) := rfl

example (c : Semantics) (ad : KoreAML.AxiomDecl) (φ : KoreAML.P) : EntailsAtValues c ad φ =
    (∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c →
      ∀ e, AtValues c I e ad.ax → ∀ m, φ.interpret I e m) := rfl

example (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M) (a : Kore.Axiom) :
    SetVarsAtValues c I e a =
    (∀ n s, KoreAML.VarKey.svar n s ∈ (KoreAML.freeOf [] a.pattern).eraseDups →
      ∀ m, e.evalSvar ((KoreAML.tableOf a.sortVars a.pattern).sv (.svar n s)) m →
        ∃ (v : GroundTerm) (S : Srt), srtOf c S = s ∧ c.sortOf v = some S ∧ (den c v).interpret I e m) := rfl

example (c : Semantics) (ad : KoreAML.AxiomDecl) (φ : KoreAML.P) : EntailsAtSetValues c ad φ =
    (∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c →
      ∀ e, AtValues c I e ad.ax → SetVarsAtValues c I e ad.ax → ∀ m, φ.interpret I e m) := rfl

example {M : Type} (e : Valuation M) (a : Kore.Axiom) : SetVarsAtMostOne e a =
    (∀ n s, KoreAML.VarKey.svar n s ∈ (KoreAML.freeOf [] a.pattern).eraseDups →
      ∀ m m', e.evalSvar ((KoreAML.tableOf a.sortVars a.pattern).sv (.svar n s)) m →
        e.evalSvar ((KoreAML.tableOf a.sortVars a.pattern).sv (.svar n s)) m' → m = m') := rfl

example (h : Kore.SymbolIdent) (ss : List Kore.KSort) (ps : List Kore.Pattern) :
    symbolsOf (.app h ss ps) = h.ident.name :: symbolsOfList ps ∧
    symbolsOf (.leftAssoc h ss ps) = h.ident.name :: symbolsOfList ps ∧
    symbolsOf (.rightAssoc h ss ps) = h.ident.name :: symbolsOfList ps := ⟨rfl, rfl, rfl⟩
example (v : Kore.VarPattern) (str : String) (s s' : Kore.KSort) :
    symbolsOf (.var v) = [] ∧ symbolsOf (.string str) = [] ∧ symbolsOf (.top s) = [] ∧
    symbolsOf (.bottom s) = [] ∧ symbolsOf (.dv s' str) = [] := ⟨rfl, rfl, rfl, rfl, rfl⟩
example (s s' : Kore.KSort) (x : Kore.EVar) (X : Kore.SVar) (p : Kore.Pattern) :
    symbolsOf (.not s p) = symbolsOf p ∧ symbolsOf (.next s p) = symbolsOf p ∧
    symbolsOf (.exist s x p) = symbolsOf p ∧ symbolsOf (.forall s x p) = symbolsOf p ∧
    symbolsOf (.mu X p) = symbolsOf p ∧ symbolsOf (.nu X p) = symbolsOf p ∧
    symbolsOf (.ceil s s' p) = symbolsOf p ∧ symbolsOf (.floor s s' p) = symbolsOf p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
example (s s' : Kore.KSort) (p q : Kore.Pattern) (ps : List Kore.Pattern) :
    symbolsOf (.and s ps) = symbolsOfList ps ∧ symbolsOf (.or s ps) = symbolsOfList ps ∧
    symbolsOf (.implies s p q) = symbolsOf p ++ symbolsOf q ∧ symbolsOf (.iff s p q) = symbolsOf p ++ symbolsOf q ∧
    symbolsOf (.rewrites s p q) = symbolsOf p ++ symbolsOf q ∧
    symbolsOf (.equals s s' p q) = symbolsOf p ++ symbolsOf q ∧
    symbolsOf (.in s s' p q) = symbolsOf p ++ symbolsOf q ∧
    symbolsOfList [] = [] ∧ symbolsOfList (p :: ps) = symbolsOf p ++ symbolsOfList ps :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example (s : Srt) : regSrtK s = KoreAML.srt (regSortNames.getD s "") := rfl

example (k : Kore.Definition) (it : KoreAML.Item) : surplusItem k it =
    ((List.range nRegSorts).any (fun s =>
      let n := "Sort" ++ regSortNames.getD s ""
      !(k.sortDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
        it.pat == (KoreAML.sortConstantItem ⟨n, [], false⟩).pat) ||
    hookSigs.any (fun h =>
      let n := regSymNames.getD h.name ""
      !(k.symbolDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
        it.pat == (KoreAML.arityItem ⟨n, [], h.args.map regSrtK, regSrtK h.result, false, []⟩).pat)) := rfl

section AttrsAgreePins
open AttrsAgree

example (k : Kore.Definition) (d : Definition) : attrsAgree k d =
    (ctors k d.sem && fns k d.sem && hooks k d.sem && colls k d.sem && prios k d) := rfl

example (as : List Kore.AppPattern) (a : String) : strArg as a =
    ((as.find? (·.head.ident.name == a)).bind fun p => match p.args with
      | [.string s] => some s
      | _ => none) := rfl

example (as : List Kore.AppPattern) (a : String) : symArg as a =
    ((as.find? (·.head.ident.name == a)).bind fun p => match p.args with
      | [.app h _ []] => some h.ident.name
      | _ => none) := rfl

example (as : List Kore.AppPattern) (a : String) : has as a = as.any (·.head.ident.name == a) := rfl

example (k : Kore.Definition) : symDecls k =
    (k.modules.flatMap fun m => m.sentences.filterMap fun
      | .symbol s => some (s.symbol.ident.ident.name, s.attributes)
      | .hookedSymbol s => some (s.symbol.ident.ident.name, s.attributes)
      | _ => none) := rfl

example (k : Kore.Definition) : AttrsAgree.sortDecls k =
    (k.modules.flatMap fun m => m.sentences.filterMap fun
      | .sort s => some (s.sort.ident.name, s.attributes)
      | .hookedSort s => some (s.sort.ident.name, s.attributes)
      | _ => none) := rfl

example (s : String) : digitsNat s =
    (let cs := s.toList
     if cs.isEmpty || !cs.all Char.isDigit then none
     else some (cs.foldl (fun a ch => a * 10 + (ch.toNat - 48)) 0)) := rfl

example (as : List Kore.AppPattern) : prioOf as =
    (if has as "owise" then 200 else match (strArg as "priority").bind digitsNat with
      | some n => n
      | none => 50) := rfl

example (s s' s'' : Kore.KSort) (prem rhs : Kore.Pattern) (h : Kore.SymbolIdent) (ss : List Kore.KSort)
    (ps : List Kore.Pattern) :
    eqnHead (.implies s prem (.equals s' s'' (.app h ss ps) rhs)) = some h.ident.name ∧
    eqnHead (.equals s' s'' (.app h ss ps) rhs) = some h.ident.name ∧
    eqnHead (.rewrites s prem rhs) = none ∧ eqnHead (.and s ps) = none := ⟨rfl, rfl, rfl, rfl⟩

example (s : Kore.KSort) (p q : Kore.Pattern) :
    isRewrite (.rewrites s p q) = true ∧ isRewrite (.implies s p q) = false ∧ isRewrite (.equals s s p q) = false :=
  ⟨rfl, rfl, rfl⟩

example (k : Kore.Definition) (c : Semantics) : ctors k c =
    ((symDecls k).all fun (n, as) => has as "constructor" == c.ctorSigs.any (c.symName ·.name == n)) := rfl

example (k : Kore.Definition) (c : Semantics) : fns k c =
    ((symDecls k).all fun (n, as) =>
      let fn := has as "function" && !has as "hook"
      let isFn := c.allFns.any (c.symName ·.label == n)
      let own := (c.ctorSigs ++ c.params.map (·.sig) ++ c.ovlSigs).any (c.symName ·.name == n)
      (!isFn || fn) && (!(fn && own) || isFn)) := rfl

example (g : CtorSig) : libFn g = !regHookNames.any (·.1 == g.name) := rfl

example (k : Kore.Definition) (c : Semantics) : hooks k c =
    ((symDecls k).all (fun (n, as) =>
      match strArg as "hook" with
      | some h =>
        (hookSigs.all fun g => c.symName g.name != n || regHookOf h == some g.name) &&
        (c.params.all fun p => c.symName p.sig.name != n || p.impl == regHookOf h)
      | none =>
        (hookSigs.all fun g => c.symName g.name != n || (libFn g && has as "function")) &&
        c.params.all fun p => c.symName p.sig.name != n)) := rfl

example (k : Kore.Definition) (c : Semantics) : colls k c =
    (let declared := (AttrsAgree.sortDecls k).filterMap fun (n, as) =>
       match symArg as "unit", symArg as "element", symArg as "concat" with
       | some u, some e, some cc => some (n, u, e, cc)
       | _, _, _ => none
     let own := fun (cs : CollSig) =>
       ("Sort" ++ c.sortName cs.sort, c.symName cs.unit, c.symName cs.elem, c.symName cs.concat)
     declared.all (fun x => c.allColls.any fun cs => own cs == x) &&
       c.colls.all fun cs => declared.contains (own cs)) := rfl

example (as : List Kore.AppPattern) : uidOf as = strArg as "UNIQUE'Unds'ID" := rfl

example (k : Kore.Definition) (u : String) : rewritePrioOf k u =
    ((k.axiomDecls.map (·.ax)).find? fun a => isRewrite a.pattern && uidOf a.attributes == some u).map
      (prioOf ·.attributes) := rfl

example (k : Kore.Definition) (d : Definition) : prios k d =
    (let c := d.sem
     let axs := k.axiomDecls.map (·.ax)
     d.pres.rules.length == c.rules.length &&
     ((c.rules.zip d.pres.rules).all fun (r, rp) => rewritePrioOf k rp.info.uid == some r.prio) &&
     ((axs.filter (isRewrite ·.pattern)).all fun a => d.pres.rules.any fun rp => uidOf a.attributes == some rp.info.uid) &&
     c.allFns.all fun f =>
       let n := c.symName f.label
       ((axs.filter fun a => eqnHead a.pattern == some n && !has a.attributes "simplification").map
           (prioOf ·.attributes)).isPerm (f.clauses.map (·.prio))) := rfl

end AttrsAgreePins

example : tieClasses =
    [("function equation", .equal), ("rewrite rule", .weaker), ("priority equation", .weaker),
     ("constructor functional", .entailed), ("subsort", .entailed), ("injectivity", .entailed),
     ("distinctness", .entailed), ("no junk", .entailed), ("function functional", .hypothesis),
     ("hooked functional", .atValues), ("collection law", .atValues), ("library", .atValues),
     ("set idempotence", .refuted), ("set-variable lemma", .refuted), ("no direction", .none)] := rfl

/-- The directions, by their constructors: seven, in this order. -/
example : (TieDir.equal.ctorIdx, TieDir.entailed.ctorIdx, TieDir.weaker.ctorIdx, TieDir.atValues.ctorIdx,
    TieDir.hypothesis.ctorIdx, TieDir.refuted.ctorIdx, TieDir.none.ctorIdx) = (0, 1, 2, 3, 4, 5, 6) := rfl
example (d : TieDir) : d.ctorIdx < 7 := by cases d <;> decide

/-! ## The rows' statements: `kore.k`'s step function (C10 part 2) and what the consumer's claim
statement is built from (C9 part 5; the statement itself, about ref-kimp's semantics, is pinned in
test/PinsKimp.lean) -/

/-- `KK.Sig`: its seven fields, in order, with their types. -/
example : (K : Semantics) → (succs : Sym) → (emb : KK.T → GroundTerm) → (embD : KK.D → GroundTerm) →
    (embSt : KK.St → GroundTerm) → (enc : GroundTerm → KK.T) → (encDef : Semantics → Option KK.D) →
    KK.Sig := @KK.Sig.mk
example (S : KK.Sig) : S = ⟨S.K, S.succs, S.emb, S.embD, S.embSt, S.enc, S.encDef⟩ := rfl

/-- `KK.St`: `stuck` and `next L`, nothing else. -/
example (s : KK.St) : s = .stuck ∨ ∃ L, s = .next L := by
  cases s with
  | stuck => exact .inl rfl
  | next L => exact .inr ⟨L, rfl⟩

example (d : Semantics) : KK.d₀ d = d.withHooks HookParams.none := rfl
example (S : KK.Sig) : KK.K₀ S = S.K.withHooks HookParams.none := rfl
example (S : KK.Sig) (E : KK.D) (x : GroundTerm) (r : Option GroundTerm) :
    KK.SuccsAt S E x r = Eval (S.K.withHooks HookParams.none) S.succs [S.embD E, S.emb (S.enc x)] r := rfl

example (S : KK.Sig) : KK.SuccsSound S =
    ∀ {d : Semantics} {E : KK.D}, CExec.execReady d = true → S.encDef d = some E →
      ∀ (x : Config (d.withHooks HookParams.none)) {L : List KK.T},
        KK.SuccsAt S E x.val (some (S.embSt (.next L))) → ∀ {y' : KK.T}, y' ∈ L →
        ∃ y : Config (d.withHooks HookParams.none), S.enc y.val = y' ∧ Step (d.withHooks HookParams.none) x y :=
  rfl

example (S : KK.Sig) : KK.SuccsStuck S =
    ∀ {d : Semantics} {E : KK.D}, CExec.execReady d = true → S.encDef d = some E →
      ∀ (x : Config (d.withHooks HookParams.none)), KK.SuccsAt S E x.val (some (S.embSt .stuck)) →
        ∀ r ∈ d.rules, NotApplies (d.withHooks HookParams.none) r x.val := rfl

example (S : KK.Sig) : KK.SuccsComplete S =
    ∀ {d : Semantics} {E : KK.D}, CExec.execReady d = true → CoherentAll (d.withHooks HookParams.none) →
      S.encDef d = some E → ∀ {x y : Config (d.withHooks HookParams.none)} {s : GroundTerm},
        KK.SuccsAt S E x.val (some s) → Step (d.withHooks HookParams.none) x y →
        ∃ L, s = S.embSt (.next L) ∧ S.enc y.val ∈ L := rfl

/-- `CoherentAll`, the hypothesis of `SuccsComplete`. -/
example (c : Semantics) : CoherentAll c =
    ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, ∀ cl' ∈ fn.clauses,
      (cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
        (cl'.aside = true ∧ cl'.prio < cl.prio)) →
      Coherent c cl cl' := rfl

/-- The all-path claims the consumer's statement is made of: `Progress`, `CPath` by its two
constructors and nothing else, `AllPath`. -/
example {α : Type} (r : α → α → Prop) (x : α) : Reachability.Progress r x = ∃ y, r x y := rfl
example {α : Type} (r : α → α → Prop) (x : α) (l : List α) : Reachability.CPath r x l ↔
    (l = [x] ∧ ¬ Reachability.Progress r x) ∨ ∃ y l', l = x :: l' ∧ r x y ∧ Reachability.CPath r y l' :=
  ⟨fun h => by
    cases h with
    | stuck h => exact .inl ⟨rfl, h⟩
    | cons h hl => exact .inr ⟨_, _, rfl, h, hl⟩,
   fun h => by
    rcases h with ⟨rfl, h⟩ | ⟨y, l', rfl, h, hl⟩
    · exact .stuck h
    · exact .cons h hl⟩
example {α : Type} (r : α → α → Prop) (P Q : α → Prop) : Reachability.AllPath r P Q =
    ∀ x, P x → ∀ l, Reachability.CPath r x l → ∃ z ∈ l, Q z := rfl

/-! ## The theorems (each `example : <the type, written out> := @name`) -/

example : ∀ (c : Semantics), c.coreOK = true → FnHyp c → SoundC c := @sound_hyp

example : ∀ (c : Semantics) (ref : OutFn), c.coreOK = true → FnHyp c → CompleteC c ref := @complete_hyp

example : ∀ (c : Semantics), c.coreOK = true → FnHyp c → ExactC c := @exact_hyp

example : ∀ (c : Semantics) (h : c.coreOK = true)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c),
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) := @sound_at

example : ∀ (c : Semantics) (h : c.coreOK = true) (x : Config c) (hd : StepDecided c x.val)
    (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c),
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) :=
  @complete_at

example : ∀ (c : Semantics), c.coreOK = true → FnDet c → FnSolves c → ClausePreDecided c → OpenLaws c →
    Consistent c :=
  @consistent_of

example : ∀ (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y'),
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := @has_model_choice

example : ∀ (c : Semantics) (h : c.coreOK = true) {x y : Config c} {r : Rule} {σ : Subst}
    (hs : StepBy c r σ x y) (hex : r.exs = [])
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c),
    Γc c ⊧ (famEx c r σ ≡ den c y.val) := @famEx_closed

example : ∀ (c : Semantics) (ref : StepFn) (hop : ∀ r ∈ c.rules, r.opens = []),
    CompleteC c (fun x => (ref x).map Outcome.val) ↔
      (StepIs c ref → ∀ x : Config c, (Γc c ∪ Γstep c) ⊧
        (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c))))) := @completeC_closed

example : ∀ {c : Semantics} (hp : c.plain = true) (x y : Config c), Step c x y ↔ Step₀ c x y := @step_plain

example : ∀ (d : Definition) (hwf : wf d = true) (hob : Obligations d)
    (hp : d.sem.plain = true) (hc : d.sem.readsConfined = false), SoundC₀ d.sem := @sound₀

example : ∀ (d : Definition) (ref : StepFn) (hwf : wf d = true) (hob : Obligations d)
    (hp : d.sem.plain = true) (hc : d.sem.readsConfined = false), CompleteC₀ d.sem ref := @complete₀

example : ∀ {c : Semantics} (hp : c.plain = true) (r : Rule) (hr : r ∈ c.rules),
    prioRuleK c r = prioRuleK₀ c r := @prioRuleK_plain

example : ∀ {c : Semantics} (h : c.readsConfined = false), Γc c = Γ c := @Γc_plain

example : ∀ {c : Semantics} (hp : c.plain = true) (f : Sym) (vs : List GroundTerm)
    (r : Option GroundTerm), Eval c f vs r ↔ Eval₀ c f vs r := @eval_plain

example : ∀ {c : Semantics} (hp : c.plain = true) (σ : Subst) (t : Term)
    (r : Option GroundTerm), EvalTerm c σ t r ↔ EvalTerm₀ c σ t r := @evalTerm_plain

example : ∀ {c : Semantics} (hp : c.plain = true), fnItems c = fnItems₀ c := @fnItems_plain

example : ∀ {c : Semantics} (hp : c.plain = true) (vs : List GroundTerm) (cl : Clause)
    (h : (cl.pre.isTop && binds cl.vars.length (varOccsList cl.pats)) = true),
    Fails c vs cl ↔ Fails₀ c vs cl := @fails_plain

example : ∀ (c : Semantics) (h : c.coreOK = true) (hp : c.plain = true)
    (x y : Config c) (hs : Step c x y), Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := @sound_at_plain

example : ∀ (c : Semantics) (h : c.coreOK = true) (hp : c.plain = true) (x : Config c)
    (hd : StepDecided c x.val) (ys : List GroundTerm) (hys : ∀ y : Config c, Step c x y → y.val ∈ ys),
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (ys.map (den c)))) :=
  @complete_at_plain

example : ∀ (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (x y : Config c)
    (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)),
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y := @famEx_values

example : ∀ (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys),
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) := @famOpen_values

example : ∀ {c : Semantics} {x y : Config c}, Step c x y ↔ ∃ r σ, StepBy c r σ x y := @step_iff_by

example : ∀ {c : Semantics} {r : Rule}
    (h : binds r.vars.length (varOccs r.lhs) = true), r.needsWitness c = false := @needsWitness_of_binds

example : ∀ {c : Semantics} {cl : Clause}
    (h : binds cl.vars.length (varOccsList cl.pats) = true), cl.needsWitness c = false :=
  @Clause.needsWitness_of_binds

example : ∀ {c : Semantics}
    (hr : ∀ r ∈ c.rules, r.needsWitness c = false)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false), OpenDecided c := @openDecided_of_plain

example : ∀ {c : Semantics} (h : ∀ k ∈ c.params, k.raw = false), OpenLaws c := @openLaws_of_plain

example : ∀ {c : Semantics} (h : c.plain = true), c.readsConfined = false := @Semantics.readsConfined_of_plain

example : ∀ (c : Semantics) (r : Rule) (rp : RulePres)
    (h : (r.pre.isTop && binds r.vars.length (varOccs r.lhs)) = true), applies c r rp = applies₀ c r rp :=
  @applies_of_binds

example : ∀ {c : Semantics} {r : Rule} (hp : c.plain = true) (x : GroundTerm)
    (h : (r.pre.isTop && binds r.vars.length (varOccs r.lhs)) = true), NotApplies c r x ↔ NotApplies₀ c r x :=
  @notApplies_of_binds

example : ∀ {c : Semantics} (hd : FnDet c) (cl cl' : Clause), Coherent c cl cl' := @Coherent.of_fnDet

example : ∀ (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (hp : c.plain = true), SoundC₀ c :=
  @sound_hyp₀

example : ∀ (c : Semantics) (ref : StepFn) (h : c.coreOK = true) (hf : FnHyp c)
    (hp : c.plain = true), CompleteC₀ c ref := @complete_hyp₀

example : ∀ {c : Semantics} (h : c.coreOK = true) (hr : CExec.execReady c = true) (hfd : FnDet c) {n : Nat}
    {x : Config c} (hf : CExec.outOfFuel c n x.val = false),
    ((Γ c ∪ Γstep c) ⊧
        (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((CExec.successorsN c n x.val).map (den c))))) ∧
      ∀ y ∈ CExec.successorsN c n x.val, Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y)) := @CExec.run_exact

/-- The members of the executor's list at a fuel where nothing ran out are `Step`'s successors:
what the list of `CExec.run_exact` is, stated without reading `CExec.successorsN`'s body. -/
example : ∀ {c : Semantics} (hr : CExec.execReady c = true) (hfd : FnDet c) {n : Nat} {x y : Config c}
    (hf : CExec.outOfFuel c n x.val = false), Step c x y ↔ y.val ∈ CExec.successorsN c n x.val :=
  @CExec.step_iff_at

/-! ## Their axioms: `#guard_msgs in #print axioms`, the list exactly -/

/-- info: 'KCore.sound_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.sound_hyp

/-- info: 'KCore.complete_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.complete_hyp

/-- info: 'KCore.exact_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.exact_hyp

/-- info: 'KCore.sound_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.sound_at

/-- info: 'KCore.complete_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.complete_at

/-- info: 'KCore.consistent_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.consistent_of

/-- info: 'KCore.has_model_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.has_model_choice

/-- info: 'KCore.famEx_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.famEx_closed

/-- info: 'KCore.completeC_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.completeC_closed

/-- info: 'KCore.step_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.step_plain

/-- info: 'KCore.sound₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.sound₀

/-- info: 'KCore.complete₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.complete₀

/-- info: 'KCore.prioRuleK_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.prioRuleK_plain

/-- info: 'KCore.Faithful.Γc_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Faithful.Γc_plain

/-- info: 'KCore.eval_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.eval_plain

/-- info: 'KCore.evalTerm_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.evalTerm_plain

/-- info: 'KCore.fnItems_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.fnItems_plain

/-- info: 'KCore.fails_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.fails_plain

/-- info: 'KCore.sound_at_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.sound_at_plain

/-- info: 'KCore.complete_at_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.complete_at_plain

/-- info: 'KCore.famEx_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.famEx_values

/-- info: 'KCore.famOpen_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.famOpen_values

/-- info: 'KCore.step_iff_by' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.step_iff_by

/-- info: 'KCore.needsWitness_of_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.needsWitness_of_binds

/-- info: 'KCore.Clause.needsWitness_of_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Clause.needsWitness_of_binds

/-- info: 'KCore.openDecided_of_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.openDecided_of_plain

/-- info: 'KCore.openLaws_of_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.openLaws_of_plain

/-- info: 'KCore.Semantics.readsConfined_of_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Semantics.readsConfined_of_plain

/-- info: 'KCore.applies_of_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.applies_of_binds

/-- info: 'KCore.notApplies_of_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.notApplies_of_binds

/-- info: 'KCore.Coherent.of_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Coherent.of_fnDet

/-- info: 'KCore.coherent_iff_noExs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.coherent_iff_noExs

/-- info: 'KCore.sound_hyp₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.sound_hyp₀

/-- info: 'KCore.complete_hyp₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.complete_hyp₀

/-- info: 'KCore.CExec.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CExec.run_exact

/-- info: 'KCore.CExec.step_iff_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CExec.step_iff_at

end KCore.Pins
