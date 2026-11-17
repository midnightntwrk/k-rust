/-
  An `[owise]` library equation on `f2-examples/silentflt.kompile.kore`, entailed at values
  (`EntailsAtValues`, direction Ev) for every interpretation H, from the library's statement
  (`KcoreSpec/LibEvFnOwise.lean`, through `LibEv.FnEqn.entailed_owise_reg`): the text's axiom is
  compared with the equation's pattern over the registry's names, `owise` premise included, and its
  translation with the text's declarations with the translation `FnEqn.entailed_owise` is about.
  Run from the package root: `lake env lean test/LibEvFnOwiseFlt.lean`.

  - 373 (`replace(Source, _, _, Count) => Source requires Count >=Int 0 [owise]`, domains.md 1915):
    `ev373`.
  - The same equation without the premise does not hold: at `replace("a", "a", "b", 1)` the left
    side is "b" (`fnReplaceEq_not_holds`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvFnOwiseFlt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

theorem ev373 (H : HookParams) : EntailsAtValues (cH H) U.ax373 (trS U.ax373).pat := by
  rw [(by decide +kernel : (trS U.ax373).pat = (trAxiom [] [] U.ax373).pat)]
  exact LibEv.fnReplaceOw_ev (coreOKH H) (shapesOKH H) U.ax373 (by decide +kernel) (by decide +kernel)

/-- The substitution `Source = "a"`, `_Gen0 = "a"`, `_Gen1 = "b"`, `Count = 1`, the argument
variables at the same values. -/
def σa : Subst :=
  [(0, LibEv.foS "a"), (1, LibEv.foS "a"), (2, LibEv.foS "b"), (3, int 1),
   (4, LibEv.foS "a"), (5, LibEv.foS "a"), (6, LibEv.foS "b"), (7, int 1)]

/-- **Without the `owise` premise the equation is false**: at `σa`, whose values have their sorts,
the `requires` holds and the patterns match, `replace("a", "a", "b", 1)` is "b", not "a". -/
theorem fnReplaceEq_not_holds (H : HookParams) : ¬ LibEv.fnReplaceEq.Holds (cH H) := by
  intro hE
  have hs : ∀ i p, LibEv.fnReplaceEq.av[i]? = some p → ∃ v, σa.lookup i = some v ∧ (cH H).sortOf v = some p.2 := by
    intro i p hp
    have hS : (cH H).sortOf (LibEv.foS "a") = some Srt.string := by
      rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
    have hS' : (cH H).sortOf (LibEv.foS "b") = some Srt.string := by
      rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
    have hI : (cH H).sortOf (int 1) = some Srt.int := by
      rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
    match i, hp with
    | 0, hp => cases hp; exact ⟨_, rfl, hS⟩
    | 1, hp => cases hp; exact ⟨_, rfl, hS⟩
    | 2, hp => cases hp; exact ⟨_, rfl, hS'⟩
    | 3, hp => cases hp; exact ⟨_, rfl, hI⟩
    | 4, hp => cases hp; exact ⟨_, rfl, hS⟩
    | 5, hp => cases hp; exact ⟨_, rfl, hS⟩
    | 6, hp => cases hp; exact ⟨_, rfl, hS'⟩
    | 7, hp => cases hp; exact ⟨_, rfl, hI⟩
  have hq : ∀ q, LibEv.fnReplaceEq.req = some q → LibEv.val (cH H) σa q = some (bool true) := by
    intro q hq; cases hq; rfl
  have hm : LibEv.FnEqn.Matches (cH H) σa LibEv.fnReplaceEq.vars.length LibEv.fnReplaceEq.pats := by
    refine ⟨rfl, (fun _ h => by cases h), rfl, (fun _ h => by cases h), rfl, (fun _ h => by cases h), rfl,
      (fun _ h => by cases h), trivial⟩
  have := hE σa hs hq hm
  rw [show LibEv.val (cH H) σa LibEv.fnReplaceEq.lhs = some (LibEv.foS "b") from
    (LibEv.fo_hv_stringReplace (c := cH H) "a" "a" "b" (k := 1) (by decide)).trans (by decide +kernel)] at this
  exact absurd this (by show ¬ some (LibEv.foS "b") = some (LibEv.foS "a"); decide)

end KCore.LibEvFnOwiseFlt

#check @KCore.LibEv.FnEqn.entailed_owise
#check @KCore.LibEv.FnEqn.entailed_owise_reg
/-- info: 'KCore.LibEvFnOwiseFlt.ev373' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnOwiseFlt.ev373
/-- info: 'KCore.LibEvFnOwiseFlt.fnReplaceEq_not_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvFnOwiseFlt.fnReplaceEq_not_holds
