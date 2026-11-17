/-
  The equality symbols' predicate equations on `f2-examples/ens.kompile.kore`, entailed at values
  (`EntailsAtValues`, direction Ev) for every interpretation H, from the library's statements
  (`LibEv.intEqPred_ev`, `LibEv.kEqPred_ev`, KcoreSpec/LibEvPred.lean).
  Run from the package root: `lake env lean test/LibEvPredEns.lean`.

  - `predIdx`: the 16 `simplification` sentences over the sort variables `R`, `Q0` of the form
    `\implies{R}(\top{R}(), \equals{Q0, R}(\equals{SortBool, Q0}(f(K1, K2), b), \and{Q0}(φ, \top{Q0}())))`
    (the literal `b` on either side), `f` one of `==Int`, `=/=Int` (domains.md 1405 to 1412) and
    `==K`, `=/=K` (2339 to 2346), φ the equation `\equals{s, Q0}(K1, K2)` or its `\not{Q0}`.
  - `pred_checked`: each is the pattern of one of the sixteen equations `LibEv.eqPred` (one kernel
    decision over the list).
  - `pred_entailed`: each is entailed at values, for every H.

  Not among them: the eight sentences of this form over set variables (139, 140, 141, 142, 147,
  148, 153, 154: `notBool`, `andBool`, `orBool` at `@B`, domains.md 1176 to 1184).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvPredEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- The indices of the sentences. -/
def predIdx : List Nat := [131, 132, 133, 134, 135, 136, 137, 138, 143, 144, 145, 146, 149, 150, 151, 152]

/-- The sentences, in text order. -/
noncomputable def predText : List AxiomDecl := U.all.filter fun ad => predIdx.contains ad.index

theorem predText_length : predText.length = 16 := by decide +kernel

/-- The choices of symbol (equality or difference), literal and side of the literal. -/
def choices : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

/-- The eight equations of `==Int` and `=/=Int`. -/
def intCands : List LibEv.PredEqn :=
  choices.map fun x => LibEv.eqPred Srt.int (if x.1 then intNe else intEq) x.1 x.2.1 x.2.2

/-- The eight equations of `==K` and `=/=K`. -/
def kCands : List LibEv.PredEqn :=
  choices.map fun x => LibEv.eqPred Srt.k (if x.1 then kNe else kEq) x.1 x.2.1 x.2.2

/-- The sentence is one of the sixteen equations, over the sort variables `R` and `Q0`. -/
def predOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv, LibEv.Q0v]) &&
    (intCands ++ kCands).any fun E => decide (ad.ax.pattern = E.patR)

theorem pred_checked : predText.all predOK = true := by decide +kernel

/-- Each of the sixteen equations is the pattern of one of the sentences. -/
theorem pred_all : (intCands ++ kCands).all (fun E => predText.any fun ad => decide (ad.ax.pattern = E.patR)) = true := by
  decide +kernel

/-- None of the 16 reads a declaration or an alias. -/
theorem pred_trS : predText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **Ev for the equality symbols' predicate equations**: each of the 16 holds in every model of Γ
at every valuation sending its variables to values, for every H. -/
theorem pred_entailed (H : HookParams) : ∀ ad ∈ predText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp pred_trS ad had)]
  have hok := List.all_eq_true.mp pred_checked ad had
  simp only [predOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_append] at hok
  obtain ⟨hsv, E, hE, hp⟩ := hok
  rcases hE with hE | hE
  · simp only [intCands, List.mem_map] at hE
    obtain ⟨x, -, rfl⟩ := hE
    exact LibEv.intEqPred_ev (coreOKH H) (shapesOKH H) x.1 x.2.1 x.2.2 ad hp hsv
  · simp only [kCands, List.mem_map] at hE
    obtain ⟨x, -, rfl⟩ := hE
    exact LibEv.kEqPred_ev (coreOKH H) x.1 x.2.1 x.2.2 ad hp hsv

end KCore.LibEvPredEns

#check @KCore.LibEv.PredEqn.entailed
#check @KCore.LibEv.Pred.den
/-- info: 'KCore.LibEvPredEns.pred_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvPredEns.pred_entailed
