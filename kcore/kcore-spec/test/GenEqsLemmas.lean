/-
  Instances of `KcoreSpec/GenEqsConservative.lean` on corpus-shaped texts. Run from the package
  root: `lake env lean -j1 test/GenEqsLemmas.lean`.

  ## Sort predicates (`Hand`, as `test/PredContent.lean`'s)

  One own sort Foo with `pair(Foo, Foo) : Foo`, and the two equations kompile writes for its
  predicate: `std`, `isFoo(kseq(inj{Foo,KItem}(V), dotk)) = true`, and `ow [dStd]`,
  `isFoo(K) = false [owise]` whose one disjunct excludes `std`. `predProjOK?` accepts both
  (`decide +kernel`), so by `GenEqs.sortPredEqn_in_Γ` each is read as a clause of `isFoo`'s
  `sortPreds` function whose equation is a premise of `Γ` (`std_in_Γ`, `ow_in_Γ`), and the `[owise]`
  one's disjunct pairs with the clause it negates, `std`'s, read back as that clause
  (`ow_excl`, by `GenEqs.predEqnOK_clause`).

  ## Registry projections (`Nx`, `f2-examples/owisenx.kompile.kore`)

  The text declares the projections of the registry sorts it holds (`project:Int`, `project:K`,
  `project:KItem`, ...) and holds their generated equations; no sentence it reads applies one. The
  registry's `projectSym X` of every registry sort X whose number names `project:X` (`regProjs`) is
  free of the theory (`free`, `GenEqs.freeB`, a kernel decision), so no premise of `Γc c ∪ Γstep c`
  applies `project:Int`, `project:K` or `project:KItem` (`int_free`, `k_free`, `kitem_free`).
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

namespace Nx

definition_of defn from "f2-examples/owisenx.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide +kernel

/-- The registry's projections whose number names `project:X`. -/
noncomputable def regProjs : List Sym :=
  ((List.range nRegSorts).filter fun X => c.symName (projectSym X) == "Lblproject'Coln'" ++ c.sortName X).map projectSym

theorem names : c.symName (projectSym Srt.int) = "Lblproject'Coln'Int" ∧
    c.symName (projectSym Srt.k) = "Lblproject'Coln'K" ∧ c.symName (projectSym Srt.kitem) = "Lblproject'Coln'KItem" := by
  decide +kernel

theorem mems : projectSym Srt.int ∈ regProjs ∧ projectSym Srt.k ∈ regProjs ∧ projectSym Srt.kitem ∈ regProjs := by
  decide +kernel

/-- **No premise of the theory applies a registry projection** (decided). -/
theorem free : freeB c regProjs = true := by decide +kernel

theorem int_free : ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol "Lblproject'Coln'Int" ∉ psyms φ := by
  have := sym_free c regProjs coreOK free mems.1
  rwa [names.1] at this

theorem k_free : ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol "Lblproject'Coln'K" ∉ psyms φ := by
  have := sym_free c regProjs coreOK free mems.2.1
  rwa [names.2.1] at this

theorem kitem_free : ∀ φ, (Faithful.Γc c ∪ Faithful.Γstep c) φ → KoreAML.Sym.symbol "Lblproject'Coln'KItem" ∉ psyms φ := by
  have := sym_free c regProjs coreOK free mems.2.2
  rwa [names.2.2] at this

end Nx

/-- info: 'GenEqsLemmas.Hand.std_in_Γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.std_in_Γ
/-- info: 'GenEqsLemmas.Hand.ow_in_Γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ow_in_Γ
/-- info: 'GenEqsLemmas.Hand.ow_excl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ow_excl
/-- info: 'GenEqsLemmas.Nx.int_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.int_free
/-- info: 'GenEqsLemmas.Nx.k_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.k_free
/-- info: 'GenEqsLemmas.Nx.kitem_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Nx.kitem_free

end GenEqsLemmas
