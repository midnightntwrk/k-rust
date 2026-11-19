/-
  KCore. What the statements of the specification (KCORE-SPEC.md §9) are built from: the KORE of a
  ground value and its matching-logic pattern (`GroundTerm.kore`, `den`), the parts of the theory's
  constructor and rule axioms that do not read the theory (`distLbItem`, `applies`), a step function and what it is to list `Step`'s successors (`StepFn`,
  `StepIs`), the decidable conditions the statements assume of a semantics (`Semantics.coreOK`,
  which `wf` implies, `Definition.coreOK_of_wf`), what they assume of its functions (`FnHyp`), and
  the named facts the deciders leave open, from which that follows (`CoreObligations`;
  `Obligations`, a definition's).

  The theory itself, `Γ`, is built from `Semantics` in Faithful.lean, which imports this file;
  soundness and completeness over it are stated in Sound.lean (`Sound`, `Complete`).

  - Symbols and sorts are numbers; the translation writes each under its name
    (`Semantics.symName`, `sortName`), so `den` and everything built on it take the semantics.
  - Ground terms are read as KORE by `GroundTerm.kore`: a map as `_Map_` of its `|->` entries and a
    set as `_Set_` of its `SetItem`s, in key or element order (`.Map`, `.Set` when empty).
  - Cons-Dist is refined for two injections `inj{A,N}`, `inj{B,N}` from incomparable sorts with a
    common lower bound (`distLbItem`, KCORE-AUDIT.md §5): their images meet exactly on the elements
    from a common lower bound.
-/
import KcoreSpec.Tie
import KcoreSpec.ClausesAgree
import KcoreSpec.EvalFunctional
import KcoreSpec.Step
import KcoreSpec.Lazy
import KcoreSpec.Kore.Gamma

set_option autoImplicit false

namespace KCore

open ML

/-- The symbols of the collection sort `s` of kind `k` (the library's of that kind when `s` is
not one). -/
def Semantics.collSig (c : Semantics) (k : CollKind) (s : Srt) : CollSig :=
  (c.collOf s).getD (match k with
    | .map => builtinColls[0] | .set => builtinColls[1] | .list => builtinColls[2]
    | .rangeMap => builtinColl .rangeMap)

mutual
  def GroundTerm.kore (c : Semantics) : GroundTerm → Kore.Pattern
    | .ctor f ts => .app ⟨⟨c.symName f⟩⟩ [] (GroundTerm.koreList c ts)
    | .inj a b t => KoreAML.injP (c.sortName a) (c.sortName b) (GroundTerm.kore c t)
    | .dv s lit => .dv (KoreAML.srt (c.sortName s)) lit.text
    | .map s es => GroundTerm.koreEntries c (c.collSig .map s) es
    | .set s es => GroundTerm.koreElems c (c.collSig .set s) es
    | .list s es => GroundTerm.koreElems c (c.collSig .list s) es
    termination_by structural t => t
  def GroundTerm.koreList (c : Semantics) : List GroundTerm → List Kore.Pattern
    | [] => []
    | t :: ts => GroundTerm.kore c t :: GroundTerm.koreList c ts
    termination_by structural ts => ts
  /-- `k₁ |-> v₁ _Map_ (k₂ |-> v₂ _Map_ …)`, `.Map` when empty (with the collection's symbols). -/
  def GroundTerm.koreEntries (c : Semantics) (k : CollSig) : List (GroundTerm × GroundTerm) → Kore.Pattern
    | [] => KoreAML.ap (c.symName k.unit) []
    | [e] => GroundTerm.koreEntry c k e
    | e :: es => KoreAML.ap (c.symName k.concat) [GroundTerm.koreEntry c k e, GroundTerm.koreEntries c k es]
    termination_by structural es => es
  def GroundTerm.koreEntry (c : Semantics) (k : CollSig) : GroundTerm × GroundTerm → Kore.Pattern
    | (x, v) => KoreAML.ap (c.symName k.elem) [GroundTerm.kore c x, GroundTerm.kore c v]
    termination_by structural e => e
  /-- `SetItem(e₁) _Set_ (SetItem(e₂) _Set_ …)`, `.Set` when empty; a list the same way with
  `ListItem`, `_List_` and `.List`. -/
  def GroundTerm.koreElems (c : Semantics) (k : CollSig) : List GroundTerm → Kore.Pattern
    | [] => KoreAML.ap (c.symName k.unit) []
    | [e] => KoreAML.ap (c.symName k.elem) [GroundTerm.kore c e]
    | e :: es => KoreAML.ap (c.symName k.concat) [KoreAML.ap (c.symName k.elem) [GroundTerm.kore c e], GroundTerm.koreElems c k es]
    termination_by structural es => es
end

/-- ⟦t⟧: the AML pattern of a ground value. -/
def den (c : Semantics) (t : GroundTerm) : KoreAML.P := KoreAML.den (t.kore c)

def symP (f : String) : KoreAML.P := KoreAML.sym (.symbol f)
def sortP (s : String) : KoreAML.P := KoreAML.sym (.sort ("Sort" ++ s))

/-! ## The constructors -/

/-- Cons-Dist′, for two injections into N from incomparable sorts A and B whose common lower
bounds are `lbs` (non-empty): `x ∈ ⟦A⟧ ∧ y ∈ ⟦B⟧ ∧ inj{A,N}(x) = inj{B,N}(y) →
⋁_{C ∈ lbs} ∃z:C. x = inj{C,A}(z) ∧ y = inj{C,B}(z)` (KCORE-AUDIT.md §5). True in the intended
model: an injection's value is determined by its core, which lies in a sort below both. -/
def distLbItem (N A B : String) (lbs : List String) : KoreAML.Item :=
  let x : EVar := ⟨1⟩
  let y : EVar := ⟨2⟩
  let z : EVar := ⟨3⟩
  let inj := fun (s t : String) (φ : KoreAML.P) => KoreAML.appList (KoreAML.sym (.symbol "inj")) [sortP s, sortP t, φ]
  { label := s!"cons-dist′ inj Sort{A} Sort{N} / inj Sort{B} Sort{N}", rule := "Cons-Dist′"
    names := ["x1", "y1", "z"]
    pat := KoreAML.guarded [x ∈∈ KoreAML.inhOf (sortP A), y ∈∈ KoreAML.inhOf (sortP B)]
      ((inj A N (.evar x) ≡ inj B N (.evar y)) ⇒
        KoreAML.disjList (lbs.map fun C =>
          KoreAML.sExists z (sortP C) ((.evar x ≡ inj C A (.evar z)) ⋀ (.evar y ≡ inj C B (.evar z))))) }

namespace Semantics
variable (c : Semantics)

/-- The common lower bounds of two sorts (strictly below both). -/
def lowerBounds (a b : Srt) : List Srt :=
  sortBy id ((c.subsorts.map (·.1)).eraseDups.filter fun s => c.subsorts.contains (s, a) && c.subsorts.contains (s, b))

end Semantics

/-! ## Rules with their priorities -/

def anyOfC (S : Kore.KSort) : List Kore.Pattern → Kore.Pattern
  | [] => .bottom S
  | e :: es => .or S [e, anyOfC S es]

/-- `∃x̄'. (lhs' ∧ ⌈req' = true⌉ ∧ pre')`: the configurations a rule applies to, the variables of
its left side and its conditions bound. -/
def applies (c : Semantics) (r : Rule) (rp : RulePres) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := KoreAML.varList (r.vars.map c.sortName) rp.names
  let bound := ((List.range r.vars.length).filter r.leftVars.contains).filterMap (vs[·]?)
  KoreAML.existsAll C (bound.map KoreAML.Var.kore)
    (.and C ([Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre))

theorem filterMap_range_getElem? {α : Type} : ∀ (vs : List α),
    (List.range vs.length).filterMap (vs[·]?) = vs
  | [] => rfl
  | a :: vs => by
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Function.comp_def]
    rw [filterMap_range_getElem? vs]

theorem withPres_length {α β : Type} [Inhabited β] : ∀ (as : List α) (bs : List β),
    (KoreAML.withPres as bs).length = as.length
  | [], _ => rfl
  | _ :: as, bs => by simp [KoreAML.withPres, withPres_length as bs.tail]

/-- `applies` of a rule whose premise predicate is `\top` and whose left side binds every
variable: `∃x̄. (lhs ∧ ⌈req = true⌉)` over every variable. -/
theorem applies_top {c : Semantics} {r : Rule} (rp : RulePres) (hp : r.pre = .top)
    (hb : binds r.vars.length (varOccs r.lhs) = true) :
    applies c r rp =
      (let C := srtOf c topCellSort
       let vs := KoreAML.varList (r.vars.map c.sortName) rp.names
       KoreAML.existsAll C (vs.map KoreAML.Var.kore)
         (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))])) := by
  have hf : (List.range r.vars.length).filter r.leftVars.contains = List.range r.vars.length := by
    apply List.filter_eq_self.mpr
    intro i hi
    have := List.all_eq_true.mp hb i hi
    simp only [Rule.leftVars, List.contains_append, this, Bool.true_or]
  have hl : (KoreAML.varList (r.vars.map c.sortName) rp.names).length = r.vars.length := by
    simp [KoreAML.varList, withPres_length]
  have hv := filterMap_range_getElem? (KoreAML.varList (r.vars.map c.sortName) rp.names)
  rw [hl] at hv
  simp only [applies, hf, hv, Cond.conj, hp, Cond.isTop, if_true, List.append_nil]

/-- Every variable below `n` occurs. -/
theorem binds_of_forall {n : Nat} {occs : List Nat} (h : ∀ i < n, i ∈ occs) : binds n occs = true :=
  List.all_eq_true.mpr fun i hi => List.contains_iff_mem.mpr (h i (List.mem_range.mp hi))

/-- `exclusion` of a clause whose predicate is `\top` and whose patterns bind every variable:
`∃x̄. ⌈req = true⌉ ∧ X̄ ∈ p̄` over every variable. -/
theorem exclusion_top {c : Semantics} {f : Fn} {cl : Clause} (cp : ClausePres) (hpre : cl.pre = .top)
    (hb : binds cl.vars.length (varOccsList cl.pats) = true) :
    exclusion c f cl cp =
      (let ren := KoreAML.varList (cl.vars.map c.sortName) cp.exclNames
       KoreAML.existsAll KoreAML.R (ren.map KoreAML.Var.kore)
         (premise (f.args.map c.sortName) (cl.req.map (Term.kore c ren)) (Term.koreList c ren cl.pats))) := by
  have hf : (List.range cl.vars.length).filter cl.leftVars.contains = List.range cl.vars.length := by
    apply List.filter_eq_self.mpr
    intro i hi
    have := List.all_eq_true.mp hb i hi
    simp only [Clause.leftVars, List.contains_append, this, Bool.true_or]
  have hl : (KoreAML.varList (cl.vars.map c.sortName) cp.exclNames).length = cl.vars.length := by
    simp [KoreAML.varList, withPres_length]
  have hv := filterMap_range_getElem? (KoreAML.varList (cl.vars.map c.sortName) cp.exclNames)
  rw [hl] at hv
  simp only [exclusion, hf, hv, withPre_top hpre]

/-- A step function on ground values. -/
abbrev StepFn := GroundTerm → List GroundTerm

/-- What a configuration may step to: a value, or the family of the instances of a match of the
rule r under σ. -/
inductive Outcome where
  | val (y : GroundTerm)
  | fam (r : Rule) (σ : Subst)

/-- An outcome function on ground values. -/
abbrev OutFn := GroundTerm → List Outcome

/-! ## What a definition reads beyond the plain shapes -/

/-- The condition holds a binder (`exMatch`, `ex`, `all`). -/
def Cond.hasBinder : Cond → Bool
  | .exMatch .. | .ex .. | .all .. => true
  | .not p => hasBinder p
  | .and p q | .or p q | .implies p q => hasBinder p || hasBinder q
  | _ => false

/-- The definition reads a confined sort: a rule or a clause has a variable its patterns do not
bind, or a `pre` or a `post` with a binder. -/
def Semantics.readsConfined (c : Semantics) : Bool :=
  c.rules.any (fun r => !r.opens.isEmpty || r.pre.hasBinder || r.post.hasBinder) ||
  c.fns.any fun f => f.clauses.any fun cl => !cl.opens.isEmpty || cl.pre.hasBinder || cl.post.hasBinder

/-- The definition uses no shape beyond the plain ones: no rule or clause binds a variable by
`\exists` on its right side or has a predicate, every rule's left side and every clause's patterns
bind each of its variables, no clause is `aside`, no parameter is an open generator, no sort is
hooked to a library carrier, and no overloading symbol overloads a function. -/
def Semantics.plain (c : Semantics) : Bool :=
  c.rules.all (fun r => r.exs.isEmpty && r.pre.isTop && r.post.isTop &&
    binds r.vars.length (varOccs r.lhs)) &&
  c.fns.all (fun f => f.clauses.all fun cl => !cl.aside && cl.exs.isEmpty && cl.pre.isTop &&
    cl.post.isTop && binds cl.vars.length (varOccsList cl.pats)) &&
  c.params.all (fun k => !k.raw) && c.lib.carriers.isEmpty &&
  c.ovls.all (fun o => o.over.all fun g => !(c.fns.any (·.label == g)))

/-- A plain definition reads no confined sort. -/
theorem Semantics.readsConfined_of_plain {c : Semantics} (h : c.plain = true) : c.readsConfined = false := by
  simp only [Semantics.plain, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hr, hf⟩, -⟩, -⟩, -⟩ := h
  have hrule : ∀ r ∈ c.rules, r.opens = [] ∧ r.pre.isTop = true ∧ r.post.isTop = true := by
    intro r hr'
    obtain ⟨⟨⟨-, hpre⟩, hpost⟩, hb⟩ := hr r hr'
    refine ⟨?_, hpre, hpost⟩
    simp only [Rule.opens, List.filter_eq_nil_iff, List.mem_range, Bool.not_eq_eq_eq_not,
      Bool.not_true, Bool.not_eq_false]
    intro i hi
    simpa using List.all_eq_true.mp hb i (List.mem_range.mpr hi)
  have hcl : ∀ f ∈ c.fns, ∀ cl ∈ f.clauses,
      cl.opens = [] ∧ cl.pre.isTop = true ∧ cl.post.isTop = true := by
    intro f hf' cl hcl'
    obtain ⟨⟨⟨⟨-, -⟩, hpre⟩, hpost⟩, hb⟩ := hf f hf' cl hcl'
    refine ⟨?_, hpre, hpost⟩
    simp only [Clause.opens, List.filter_eq_nil_iff, List.mem_range, Bool.not_eq_eq_eq_not,
      Bool.not_true, Bool.not_eq_false]
    intro i hi
    simpa using List.all_eq_true.mp hb i (List.mem_range.mpr hi)
  simp only [Semantics.readsConfined, Bool.or_eq_false_iff, List.any_eq_false]
  refine ⟨fun r hr' => ?_, fun f hf' => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hrule r hr'
    simp [h1, Cond.eq_top_of_isTop h2, Cond.eq_top_of_isTop h3, Cond.hasBinder]
  · simp only [List.any_eq_true, not_exists, not_and]
    intro cl hcl'
    obtain ⟨h1, h2, h3⟩ := hcl f hf' cl hcl'
    simp [h1, Cond.eq_top_of_isTop h2, Cond.eq_top_of_isTop h3, Cond.hasBinder]

/-! ## Conditions over variables the left side does not bind -/

/-- The rule's conditions are closed over open variables of which one is not of a confined sort:
whether they hold is one fact, the same at every configuration, and it is not decided by values. -/
def Rule.needsWitness (c : Semantics) (r : Rule) : Bool :=
  r.reqOpen && r.reqClosed && !r.openCondVars.all fun i => (r.vars[i]?.map c.confined).getD false
/-- Some values satisfy the rule's conditions. -/
def Rule.Witnessed (c : Semantics) (r : Rule) : Prop :=
  ∃ σ, c.WellSortedAt r.vars r.condVars σ ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true

/-- Some values satisfy the clause's conditions, and at them its `requires` has no result but
`true` and its predicate no truth value but `true`: no evaluation makes the clause fail where its
patterns match. -/
def Clause.Witnessed (c : Semantics) (cl : Clause) : Prop :=
  ∃ σ, c.WellSortedAt cl.vars cl.condVars σ ∧
    (∀ t, cl.req = some t →
      EvalTerm c σ t (some (bool true)) ∧ ∀ r, EvalTerm c σ t r → r = some (bool true)) ∧
    Holds c cl.vars.length σ cl.pre true ∧
    ∀ b, Holds c cl.vars.length σ cl.pre b → b = true

/-! ## What the statements assume of a semantics -/

/-- **The decidable conditions soundness and completeness assume of a semantics**: its subsorts,
clauses and rules are well sorted (`sortedOK`), the decidable conditions of its theory that the
proofs read hold (`faithCoreOK`), no user symbol is named like an interpreted hook (`hooksApart`),
the functions evaluation reads are named apart (`predsApart`), and its own sorts and symbols are
numbered in order (`idsOK`), and its overloading symbols are well formed (`overloadsOK`). -/
def Semantics.coreOK (c : Semantics) : Bool :=
  c.sortedOK && c.faithCoreOK && c.hooksApart && c.predsApart && c.idsOK && c.overloadsOK

theorem Semantics.coreOK_parts {c : Semantics} (h : c.coreOK = true) :
    c.sortedOK = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true := by
  simp only [Semantics.coreOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- `coreOK`'s condition on the overloading symbols. -/
theorem Semantics.coreOK_ovls {c : Semantics} (h : c.coreOK = true) : c.overloadsOK = true := by
  simp only [Semantics.coreOK, Bool.and_eq_true] at h
  exact h.2

/-- `okAll`, `faithOK`, the three name conditions and the overloading symbols' give `coreOK`. -/
theorem Semantics.coreOK_of_okAll {c : Semantics} (hok : c.okAll = true) (hfa : c.faithOK = true)
    (hha : c.hooksApart = true) (hpa : c.predsApart = true) (hids : c.idsOK = true)
    (hov : c.overloadsOK = true) : c.coreOK = true := by
  simp only [Semantics.coreOK, Semantics.sortedOK_of_okAll hok (Semantics.overloadsOK_pats hov), Semantics.faithCoreOK_of_faithOK hfa, hha,
    hpa, hids, hov, Bool.and_self]

/-- A well-formed definition's semantics meets `coreOK`: `wf` checks each of its conditions. -/
theorem Definition.coreOK_of_wf {d : Definition} (h : wf d = true) : d.sem.coreOK = true := by
  simp only [wf, Definition.namesOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hha⟩, hpa⟩, hids⟩, hok⟩, -⟩, -⟩, -⟩, hfa⟩, hov⟩ := h
  exact Semantics.coreOK_of_okAll hok hfa hha hpa hids hov

/-- The step relation's successors, as a step function (any enumeration of `Step`'s successors;
the checked layer gives the executable one, `Exec.successorsN`, with `Exec.step_iff`). -/
def StepIs (c : Semantics) (ref : StepFn) : Prop :=
  ∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔ ∃ hy : c.sortOf y = some topCellSort, Step c x ⟨y, hy⟩

end KCore
