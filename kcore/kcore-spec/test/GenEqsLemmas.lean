/-
  Instances of `KcoreSpec/GenEqsConservative.lean` on corpus-shaped texts. Run from the package
  root: `lake env lean -j1 test/GenEqsLemmas.lean`. The instances on the texts of f2-examples are in
  test/GenEqsLemmasNx.lean (`Nx`), test/GenEqsLemmasPrio.lean (`Prio`) and
  test/GenEqsLemmasNamedArg.lean (`NamedArg`), each run alone.

  ## Sort predicates (`Hand`, as `test/PredContent.lean`'s)

  One own sort Foo with `pair(Foo, Foo) : Foo`, and the two equations kompile writes for its
  predicate: `std`, `isFoo(kseq(inj{Foo,KItem}(V), dotk)) = true`, and `ow [dStd]`,
  `isFoo(K) = false [owise]` whose one disjunct excludes `std`. `predProjOK?` accepts both
  (`decide +kernel`), so by `GenEqs.sortPredEqn_in_Γ` each is read as a clause of `isFoo`'s
  `sortPreds` function whose equation is a premise of `Γ` (`std_in_Γ`, `ow_in_Γ`), and the `[owise]`
  one's disjunct pairs with the clause it negates, `std`'s, read back as that clause
  (`ow_excl`, by `GenEqs.predEqnOK_clause`).

  ## A constructor argument's projection (`HandArg`, `General`), a registry-numbered projection
  the arm refuses (`RegProj`): the sections below.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs

namespace GenEqsLemmas

namespace Hand

open KoreAML (ev evar ap srt asK uidAttr attr R)

def Foo : Srt := nRegSorts
def isFoo : Sym := nRegSyms
def pairS : Sym := nRegSyms + 1

def N : Names := { sorts := ["Foo"], syms := ["LblisFoo", "Lblpair"] }

def c : Semantics :=
  { lib := libOf [], sortNames := N.sorts, symNames := N.syms, userSorts := [Foo]
    ctors := [⟨pairS, [Foo, Foo], Foo⟩], fns := [], userSubsorts := [], pgmSort := Srt.k, rules := [] }

def tt : Kore.Pattern := .dv (srt "Bool") "true"
def ff : Kore.Pattern := .dv (srt "Bool") "false"
def item (p : Kore.Pattern) : Kore.Pattern := asK "Foo" p

def std : RawEqn := ⟨"LblisFoo", [item (ev "VarV" (srt "Foo"))], none, none, tt, [uidAttr "std"], none, false⟩

def disjunct (xs : List Kore.EVar) (req p : Kore.Pattern) : Kore.Pattern :=
  KoreAML.existsAll R xs (.and R [req, .and R [.in (srt "K") R (ev "X0" (srt "K")) p, .top R]])

def dStd : Kore.Pattern :=
  disjunct [evar "Var'Unds'Gen2" (srt "Foo")] (.top R) (item (ev "Var'Unds'Gen2" (srt "Foo")))

def ow (ds : List Kore.Pattern) : RawEqn :=
  ⟨"LblisFoo", [ev "VarK" (srt "K")], none, some ds, ff, [uidAttr "ow", attr "owise"], none, false⟩

def eqs : List RawEqn := [ow [dStd], std]

theorem std_ok : predProjOK? N "" eqs c std = some true := by decide +kernel
theorem ow_ok : predProjOK? N "" eqs c (ow [dStd]) = some true := by decide +kernel

/-- **The standard equation is a clause of `isFoo` that `Γ` states.** -/
theorem std_in_Γ : ∃ fn ∈ c.sortPreds, c.symName fn.label = "LblisFoo" ∧ ∃ cl cp, clause? N "" std none = .ok (cl, cp) ∧
    cl ∈ fn.clauses ∧ ∀ it ∈ Faithful.kernelItems [Faithful.prioEquation c fn cl], Faithful.Γ c it.pat :=
  sortPredEqn_in_Γ std_ok (by decide)

/-- **The `[owise]` equation is a clause of `isFoo` that `Γ` states.** -/
theorem ow_in_Γ : ∃ fn ∈ c.sortPreds, c.symName fn.label = "LblisFoo" ∧ ∃ cl cp, clause? N "" (ow [dStd]) none = .ok (cl, cp) ∧
    cl ∈ fn.clauses ∧ ∀ it ∈ Faithful.kernelItems [Faithful.prioEquation c fn cl], Faithful.Γ c it.pat :=
  sortPredEqn_in_Γ ow_ok (by decide)

/-- **The `[owise]` equation's one disjunct pairs with the clause it negates**, read back as it. -/
theorem ow_excl : ∃ fn ∈ c.sortPreds, ∃ cl cp, clause? N "" (ow [dStd]) none = .ok (cl, cp) ∧ cl ∈ fn.clauses ∧
    ∃ es : List (RawEqn × Clause), es.map (·.2) = Faithful.lowerClauses fn cl ∧ es.length = 1 ∧
      ∀ q ∈ (pairExcl (es.map (·.1)) [dStd]).zip es, ∃ cp', clause? N "" q.1.1 q.1.2 = .ok (q.2.2, cp') := by
  obtain ⟨fn, hfn, -, hok⟩ := predProjOK_sortPred ow_ok (by decide)
  obtain ⟨cl, cp, hc, hcl, hex⟩ := predEqnOK_clause hok
  obtain ⟨es, h1, h2, h3⟩ := hex [dStd] rfl
  exact ⟨fn, hfn, cl, cp, hc, hcl, es, h1, h2.symm, h3⟩

end Hand

/-! ## A constructor argument's projection (G8)

A hand-built semantics of kompile's shape: the configuration `<k> K </k>` with the generated
counter, and an own sort `Foo ::= leaf() | pair(left: Foo, right: Foo)`, whose named arguments kompile
gives the projections `project:pair:left` and `project:pair:right` with the equations
`project:pair:left(pair(K0, K1)) = K0` and the like (as it does for K-IO's `#tempFile` and
`#unknownIOError`; the corpus texts that hold such projections are the K-IO ones, 785 KB and up). Neither name is a registry name or one of the
semantics' own, so each resolves to no constant (`GenEqs.spareSymB_of_argProj`), and no premise of
the theory holds one (`free`, `GenEqs.nameFreeB`). Under `FnHyp` (no function), one model of the
theory whose steps are `Step`'s holds both projections' equations at `pair(leaf, pair(leaf, leaf))`
(`eqns`, `GenEqs.model_with_eqns_step` with `GenEqs.argFn`). -/

namespace HandArg

open KCore.Faithful.SortsWitness (cellSorts cellCtors cellSubsorts)

/-- The own sort Foo, after the `k` cell's two sorts; its predicate beside theirs, `leaf` and `pair` after the
four cell symbols. -/
def Foo : Srt := nRegSorts + 2
def leafS : Sym := nRegSyms + 5
def pairS : Sym := nRegSyms + 6

/-- The configuration `<k> K </k>` with the generated counter, and the own sort
`Foo ::= leaf() | pair(left: Foo, right: Foo)`. -/
def c : Semantics :=
  { lib := {}, sortNames := ["KCell", "KCellOpt", "Foo"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisFoo", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblleaf", "Lblpair"]
    userSorts := cellSorts ++ [Foo]
    ctors := cellCtors ++ [⟨leafS, [], Foo⟩, ⟨pairS, [Foo, Foo], Foo⟩], fns := []
    userSubsorts := cellSubsorts, pgmSort := Srt.k, rules := [] }

theorem coreOK : c.coreOK = true := by decide_coreOK

theorem rooted : rootedListsB c = true := by rw [rootedListsB]; decide_cheap 40

def left : String := "Lblproject'Coln'pair'Coln'left"
def right : String := "Lblproject'Coln'pair'Coln'right"
def names : List String := [left, right]

theorem free : nameFreeB c names = true := by
  rw [nameFreeB, NameFree.listsN, NameFree.valuesN, NameFree.graphsN]; decide_cheap 40

def argNames : String → Prop := fun n => n ∈ names

theorem arg_free : ∀ n, argNames n → ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ :=
  nameFree_of_decided c names coreOK free

theorem arg_spare : ∀ n, argNames n → spareSymB c n = true := by
  intro n hn
  simp only [argNames, names, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl <;>
    exact spareSymB_of_argProj c (by decide) (by decide +kernel) (by decide +kernel)

def argG : String → GroundTerm → Option GroundTerm := fun n =>
  if n = left then argFn pairS 0 else if n = right then argFn pairS 1 else fun _ => none

def leafV : GroundTerm := .ctor leafS []
def pairV : GroundTerm := .ctor pairS [leafV, .ctor pairS [leafV, leafV]]

theorem sorts : c.sortOf leafV = some Foo ∧ c.sortOf pairV = some Foo ∧
    c.sortOf (.ctor pairS [leafV, leafV]) = some Foo := by decide +kernel

theorem fns_nil : c.fns = [] := rfl
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-- **One model of the theory, whose steps are the semantics' steps, holds both projections'
equations** at `pair(leaf, pair(leaf, leaf))`. -/
theorem eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Faithful.Γc c ∪ Faithful.Γstep c)) ∧
      (I ⊧ᴵ (symP left ⬝ den c pairV ≡ den c leafV)) ∧
      (I ⊧ᴵ (symP right ⬝ den c pairV ≡ den c (.ctor pairS [leafV, leafV]))) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨hl, hp, hp2⟩ := sorts
  obtain ⟨I, h1, h2, h3⟩ := model_with_eqns_step c coreOK fnHyp argNames argG rooted arg_free arg_spare
  refine ⟨I, h1, h2 _ (by simp [argNames, names]) _ _ _ _ hp hl ?_,
    h2 _ (by simp [argNames, names]) _ _ _ _ hp hp2 ?_, h3⟩
  · simp only [argG, ↓reduceIte, pairV, argFn_ctor]
    rfl
  · have h : right ≠ left := by decide
    simp only [argG, h, ↓reduceIte, pairV, argFn_ctor]
    rfl

end HandArg

/-! ## Without kernel decisions of the theory's lists

`GenEqs.rootedListsB_holds` gives rootedness of every semantics, and `GenEqs.nameFree_of_argProj`
freeness of a constructor argument's projection from the conditions the account's arm checks of its
name; `GenEqs.model_with_eqns_argProj` puts them together with `spareSymB_of_argProj`. -/

namespace General

/-- Every semantics' lists are rooted. -/
example (c : Semantics) : rootedListsB c = true := rootedListsB_holds c

/-- The symbols a premise holds are the semantics' own, `inj`, `Lblite`, or the head of a symbol of
the semantics named as an instance. -/
example (c : Semantics) (h : c.coreOK = true) :
    ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → ∀ n, KoreAML.Sym.symbol n ∈ psyms φ →
      n ∈ regSymNames ++ c.symNames ∨ n = "" ∨ n = "inj" ∨ n = "Lblite" ∨ c.instHeadFree n = false :=
  premise_symbols c h

/-- `HandArg`'s model, from the arm's conditions on the two names alone. -/
theorem handArg_eqns :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem,
      (I ⊧ᴵP (Faithful.Γc HandArg.c ∪ Faithful.Γstep HandArg.c)) ∧
      (I ⊧ᴵ (symP HandArg.left ⬝ den HandArg.c HandArg.pairV ≡ den HandArg.c HandArg.leafV)) ∧
      ∀ x y : Config HandArg.c, Step HandArg.c x y ↔
        ¬ (I ⊧ᴵ (den HandArg.c x.val ⇒ ∼ KoreAML.sNext (den HandArg.c y.val))) := by
  obtain ⟨hl, hp, -⟩ := HandArg.sorts
  obtain ⟨I, h1, h2, h3⟩ := model_with_eqns_argProj HandArg.c HandArg.coreOK HandArg.fnHyp HandArg.argNames
    HandArg.argG (fun n hn => by
      simp only [HandArg.argNames, HandArg.names, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> exact ⟨by decide, by decide +kernel, by decide +kernel, by decide +kernel⟩)
  refine ⟨I, h1, h2 _ (by simp [HandArg.argNames, HandArg.names]) _ _ _ _ hp hl ?_, h3⟩
  simp only [HandArg.argG, ↓reduceIte, HandArg.pairV, argFn_ctor]
  rfl

end General

/-! ## A registry-numbered projection the arm refuses (`RegProj`)

`HandArg`'s shape without `pair`, with a parameter symbol numbered as the registry's `project:Int`.
`coreOK` holds and the name is none of the semantics' own, so `predProjOK?` accepts the selector-domain
axiom of `project:Int`; but the parameter's arity item, a premise of the theory, names it
(`GenEqs.kernelSym_named`), so the equation's symbol is not free. The arm's decided check refuses it
(`Parse.predProjAcc`, `Parse.regProjFree`). -/

namespace RegProj

open KCore.Faithful.SortsWitness (cellSorts cellCtors cellSubsorts)

def Foo : Srt := nRegSorts + 2
def leafS : Sym := nRegSyms + 5
def projK : CtorSig := ⟨projectSym Srt.int, [Srt.k], Srt.int⟩

def c : Semantics :=
  { lib := {}, sortNames := ["KCell", "KCellOpt", "Foo"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisFoo", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblleaf"]
    userSorts := cellSorts ++ [Foo]
    ctors := cellCtors ++ [⟨leafS, [], Foo⟩], fns := []
    params := [{ sig := projK }]
    userSubsorts := cellSubsorts, pgmSort := Srt.k, rules := [] }

theorem coreOK : c.coreOK = true := by decide_coreOK

def projInt : String := "Lblproject'Coln'Int"

theorem name : c.symName projK.name = projInt := by decide +kernel

/-- `project:Int`'s selector-domain axiom, as the reader reads it. -/
def e : Parse.RawEqn :=
  { fn := projInt, pats := [], req := none, competitors := none, rhs := .top KoreAML.R, attrs := [], ens := none,
    dom := true }

def N : Parse.Names := { sorts := [], syms := [] }

/-- `predProjOK?` accepts it: Int is a registry sort and the name is none of the semantics' own. -/
theorem pred_ok : Parse.predProjOK? N "" [e] c e = some true := by decide +kernel

/-- **A premise of the theory names `project:Int`**: the parameter's arity item. -/
theorem named : ∃ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ ∧ KoreAML.Sym.symbol projInt ∈ psyms φ := by
  have := kernelSym_named (c := c) (k := projK) (by decide +kernel) (by decide +kernel)
  rwa [name] at this

/-- **The arm refuses it**: `freeB c [projectSym Int]` is false. -/
theorem refused : Parse.predProjAcc N "" [e] c e = false := by decide +kernel

end RegProj

/-- info: 'GenEqsLemmas.Hand.std_in_Γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.std_in_Γ
/-- info: 'GenEqsLemmas.Hand.ow_in_Γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ow_in_Γ
/-- info: 'GenEqsLemmas.Hand.ow_excl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ow_excl
/-- info: 'GenEqsLemmas.HandArg.eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandArg.eqns
/-- info: 'KCore.GenEqs.rootedListsB_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rootedListsB_holds
/-- info: 'KCore.GenEqs.premise_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms premise_symbols
/-- info: 'KCore.GenEqs.argProj_free_of_genEqClassOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms argProj_free_of_genEqClassOK
/-- info: 'KCore.GenEqs.sortProj_free_of_predProjOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortProj_free_of_predProjOK
/-- info: 'KCore.GenEqs.sortProj_free_of_predProjAcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortProj_free_of_predProjAcc
/-- info: 'GenEqsLemmas.RegProj.named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RegProj.named
/-- info: 'GenEqsLemmas.General.handArg_eqns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms General.handArg_eqns

end GenEqsLemmas
