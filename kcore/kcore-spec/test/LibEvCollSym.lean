/-
  The lemmas of MAP-KORE-SYMBOLIC and SET-KORE-SYMBOLIC (domains.md, K 7.1.337) over element
  variables on `f2-examples/collsym.kompile.kore`, entailed at values (`EntailsAtValues`) for every
  interpretation H, each from the library's one statement of it (KcoreSpec/LibEvCollSym.lean):
  the text's axiom is compared with the statement's pattern over the registry's names.
  Run from the package root: `lake env lean test/LibEvCollSym.lean`.

  - Without an `ensures` (`LibEv.Eqn`): 417, 418, 419, 426, 434, 439, 441, 444, 445 of MAP;
    835, 836, 854 (both argument orders), 855, 864 (both), 865, 876 of SET.
  - With an `ensures` (`LibEv.EqnE`): 425, 432, 437 of MAP; 837, 839, 841, 843, 857 (both), 867
    (both), 871, 877, 886, 888 of SET.

  - Over a set variable (`LibEv.SvEqn`), entailed at set values (`EntailsAtSetValues`): 449, 450.

  - With a `requires` comparing two KItem variables, `K1 =/=K K2` or `K1 ==K K2 orBool ...`
    (`LibEv.EqnK`, KcoreSpec/LibEvCollSymK.lean), entailed at values: 422, 429, 433, 435, 438,
    440, 446, 447 (433 and 438 with an `ensures`).

  Not entailed: four lemmas over set variables are refuted at values; for each sentence `n`,
  `sn_at` (in every model of Γ the sentence fails at a valuation meeting `AtValues` and
  `SetVarsAtValues`), `sn_refuted` (Γ with it has no model) and `sn_one` (it holds at every valuation
  at values whose set variables hold at most one element):
  - 137 (domains.md 411, `#Ceil(@M [@K])`), at `@K = {0}`, `@M = {.Map, 0 |-> 0}`;
  - 138 (830, `#Ceil(@S SetItem(@E))`), at `@E = {0}`, `@S = {.Set, SetItem(0)}`;
  - 158 (451) and 149 (452, the flip), `{false #Equals @Key in_keys(Key' |-> Val @M)} => ...`,
    at `@Key = {1}`, `Key' = Val = 0`, `@M = {.Map, 0 |-> 0 1 |-> 0}`.
  (0 and 1 are the KItem injections of the Ints.)
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvCollSym

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/collsym.kompile.kore"
definition_of defn from "f2-examples/collsym.kompile.kore"
user_axioms U from "f2-examples/collsym.kompile.kore" module "COLLSYM"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- domains.md 417 (`LibEv.msUpdConcat`). -/
theorem ev179 (H : HookParams) : EntailsAtValues (cH H) U.ax179 (trS U.ax179).pat := by
  rw [(by decide +kernel : (trS U.ax179).pat = (trAxiom [] [] U.ax179).pat)]
  exact LibEv.msUpdConcat_ev (coreOKH H) (shapesOKH H) U.ax179 (by decide +kernel) (by decide +kernel)

/-- domains.md 418 (`LibEv.msUpdFresh`). -/
theorem ev177 (H : HookParams) : EntailsAtValues (cH H) U.ax177 (trS U.ax177).pat := by
  rw [(by decide +kernel : (trS U.ax177).pat = (trAxiom [] [] U.ax177).pat)]
  exact LibEv.msUpdFresh_ev (coreOKH H) (shapesOKH H) U.ax177 (by decide +kernel) (by decide +kernel)

/-- domains.md 419 (`LibEv.msUpdUpd`). -/
theorem ev178 (H : HookParams) : EntailsAtValues (cH H) U.ax178 (trS U.ax178).pat := by
  rw [(by decide +kernel : (trS U.ax178).pat = (trAxiom [] [] U.ax178).pat)]
  exact LibEv.msUpdUpd_ev (coreOKH H) (shapesOKH H) U.ax178 (by decide +kernel) (by decide +kernel)

/-- domains.md 426 (`LibEv.msRemFresh`). -/
theorem ev215 (H : HookParams) : EntailsAtValues (cH H) U.ax215 (trS U.ax215).pat := by
  rw [(by decide +kernel : (trS U.ax215).pat = (trAxiom [] [] U.ax215).pat)]
  exact LibEv.msRemFresh_ev (coreOKH H) (shapesOKH H) U.ax215 (by decide +kernel) (by decide +kernel)

/-- domains.md 434 (`LibEv.msLookupUpd`). -/
theorem ev169 (H : HookParams) : EntailsAtValues (cH H) U.ax169 (trS U.ax169).pat := by
  rw [(by decide +kernel : (trS U.ax169).pat = (trAxiom [] [] U.ax169).pat)]
  exact LibEv.msLookupUpd_ev (coreOKH H) (shapesOKH H) U.ax169 (by decide +kernel) (by decide +kernel)

/-- domains.md 439 (`LibEv.msLookupDefUpd`). -/
theorem ev174 (H : HookParams) : EntailsAtValues (cH H) U.ax174 (trS U.ax174).pat := by
  rw [(by decide +kernel : (trS U.ax174).pat = (trAxiom [] [] U.ax174).pat)]
  exact LibEv.msLookupDefUpd_ev (coreOKH H) (shapesOKH H) U.ax174 (by decide +kernel) (by decide +kernel)

/-- domains.md 441 (`LibEv.msLookupDefUnit`). -/
theorem ev172 (H : HookParams) : EntailsAtValues (cH H) U.ax172 (trS U.ax172).pat := by
  rw [(by decide +kernel : (trS U.ax172).pat = (trAxiom [] [] U.ax172).pat)]
  exact LibEv.msLookupDefUnit_ev (coreOKH H) U.ax172 (by decide +kernel) (by decide +kernel)

/-- domains.md 444 (`LibEv.msInKeysRem`). -/
theorem ev233 (H : HookParams) : EntailsAtValues (cH H) U.ax233 (trS U.ax233).pat := by
  rw [(by decide +kernel : (trS U.ax233).pat = (trAxiom [] [] U.ax233).pat)]
  exact LibEv.msInKeysRem_ev (coreOKH H) (shapesOKH H) U.ax233 (by decide +kernel) (by decide +kernel)

/-- domains.md 445 (`LibEv.msInKeysUpd`). -/
theorem ev232 (H : HookParams) : EntailsAtValues (cH H) U.ax232 (trS U.ax232).pat := by
  rw [(by decide +kernel : (trS U.ax232).pat = (trAxiom [] [] U.ax232).pat)]
  exact LibEv.msInKeysUpd_ev (coreOKH H) (shapesOKH H) U.ax232 (by decide +kernel) (by decide +kernel)

/-- domains.md 835 (`LibEv.ssDiffUnit`). -/
theorem ev181 (H : HookParams) : EntailsAtValues (cH H) U.ax181 (trS U.ax181).pat := by
  rw [(by decide +kernel : (trS U.ax181).pat = (trAxiom [] [] U.ax181).pat)]
  exact LibEv.ssDiffUnit_ev (coreOKH H) (shapesOKH H) U.ax181 (by decide +kernel) (by decide +kernel)

/-- domains.md 836 (`LibEv.ssUnitDiff`). -/
theorem ev183 (H : HookParams) : EntailsAtValues (cH H) U.ax183 (trS U.ax183).pat := by
  rw [(by decide +kernel : (trS U.ax183).pat = (trAxiom [] [] U.ax183).pat)]
  exact LibEv.ssUnitDiff_ev (coreOKH H) (shapesOKH H) U.ax183 (by decide +kernel) (by decide +kernel)

/-- domains.md 854 (`LibEv.ssUnionUnit`). -/
theorem ev250 (H : HookParams) : EntailsAtValues (cH H) U.ax250 (trS U.ax250).pat := by
  rw [(by decide +kernel : (trS U.ax250).pat = (trAxiom [] [] U.ax250).pat)]
  exact LibEv.ssUnionUnit_ev (coreOKH H) (shapesOKH H) U.ax250 (by decide +kernel) (by decide +kernel)

/-- domains.md 854 (`LibEv.ssUnitUnion`). -/
theorem ev252 (H : HookParams) : EntailsAtValues (cH H) U.ax252 (trS U.ax252).pat := by
  rw [(by decide +kernel : (trS U.ax252).pat = (trAxiom [] [] U.ax252).pat)]
  exact LibEv.ssUnitUnion_ev (coreOKH H) (shapesOKH H) U.ax252 (by decide +kernel) (by decide +kernel)

/-- domains.md 855 (`LibEv.ssUnionSelf`). -/
theorem ev249 (H : HookParams) : EntailsAtValues (cH H) U.ax249 (trS U.ax249).pat := by
  rw [(by decide +kernel : (trS U.ax249).pat = (trAxiom [] [] U.ax249).pat)]
  exact LibEv.ssUnionSelf_ev (coreOKH H) (shapesOKH H) U.ax249 (by decide +kernel) (by decide +kernel)

/-- domains.md 864 (`LibEv.ssInterUnit`). -/
theorem ev263 (H : HookParams) : EntailsAtValues (cH H) U.ax263 (trS U.ax263).pat := by
  rw [(by decide +kernel : (trS U.ax263).pat = (trAxiom [] [] U.ax263).pat)]
  exact LibEv.ssInterUnit_ev (coreOKH H) (shapesOKH H) U.ax263 (by decide +kernel) (by decide +kernel)

/-- domains.md 864 (`LibEv.ssUnitInter`). -/
theorem ev264 (H : HookParams) : EntailsAtValues (cH H) U.ax264 (trS U.ax264).pat := by
  rw [(by decide +kernel : (trS U.ax264).pat = (trAxiom [] [] U.ax264).pat)]
  exact LibEv.ssUnitInter_ev (coreOKH H) (shapesOKH H) U.ax264 (by decide +kernel) (by decide +kernel)

/-- domains.md 865 (`LibEv.ssInterSelf`). -/
theorem ev262 (H : HookParams) : EntailsAtValues (cH H) U.ax262 (trS U.ax262).pat := by
  rw [(by decide +kernel : (trS U.ax262).pat = (trAxiom [] [] U.ax262).pat)]
  exact LibEv.ssInterSelf_ev (coreOKH H) (shapesOKH H) U.ax262 (by decide +kernel) (by decide +kernel)

/-- domains.md 876 (`LibEv.ssInUnit`). -/
theorem ev190 (H : HookParams) : EntailsAtValues (cH H) U.ax190 (trS U.ax190).pat := by
  rw [(by decide +kernel : (trS U.ax190).pat = (trAxiom [] [] U.ax190).pat)]
  exact LibEv.ssInUnit_ev (coreOKH H) U.ax190 (by decide +kernel) (by decide +kernel)

/-- domains.md 425 (`LibEv.msRemConcat`). -/
theorem ev216 (H : HookParams) : EntailsAtValues (cH H) U.ax216 (trS U.ax216).pat := by
  rw [(by decide +kernel : (trS U.ax216).pat = (trAxiom [] [] U.ax216).pat)]
  exact LibEv.msRemConcat_ev (coreOKH H) (shapesOKH H) U.ax216 (by decide +kernel) (by decide +kernel)

/-- domains.md 432 (`LibEv.msLookupConcat`). -/
theorem ev170 (H : HookParams) : EntailsAtValues (cH H) U.ax170 (trS U.ax170).pat := by
  rw [(by decide +kernel : (trS U.ax170).pat = (trAxiom [] [] U.ax170).pat)]
  exact LibEv.msLookupConcat_ev (coreOKH H) (shapesOKH H) U.ax170 (by decide +kernel) (by decide +kernel)

/-- domains.md 437 (`LibEv.msLookupDefConcat`). -/
theorem ev175 (H : HookParams) : EntailsAtValues (cH H) U.ax175 (trS U.ax175).pat := by
  rw [(by decide +kernel : (trS U.ax175).pat = (trAxiom [] [] U.ax175).pat)]
  exact LibEv.msLookupDefConcat_ev (coreOKH H) (shapesOKH H) U.ax175 (by decide +kernel) (by decide +kernel)

/-- domains.md 837 (`LibEv.ssItemDiffConcat`). -/
theorem ev184 (H : HookParams) : EntailsAtValues (cH H) U.ax184 (trS U.ax184).pat := by
  rw [(by decide +kernel : (trS U.ax184).pat = (trAxiom [] [] U.ax184).pat)]
  exact LibEv.ssItemDiffConcat_ev (coreOKH H) (shapesOKH H) U.ax184 (by decide +kernel) (by decide +kernel)

/-- domains.md 839 (`LibEv.ssDiffConcat`). -/
theorem ev182 (H : HookParams) : EntailsAtValues (cH H) U.ax182 (trS U.ax182).pat := by
  rw [(by decide +kernel : (trS U.ax182).pat = (trAxiom [] [] U.ax182).pat)]
  exact LibEv.ssDiffConcat_ev (coreOKH H) (shapesOKH H) U.ax182 (by decide +kernel) (by decide +kernel)

/-- domains.md 841 (`LibEv.ssConcatDiff`). -/
theorem ev185 (H : HookParams) : EntailsAtValues (cH H) U.ax185 (trS U.ax185).pat := by
  rw [(by decide +kernel : (trS U.ax185).pat = (trAxiom [] [] U.ax185).pat)]
  exact LibEv.ssConcatDiff_ev (coreOKH H) (shapesOKH H) U.ax185 (by decide +kernel) (by decide +kernel)

/-- domains.md 843 (`LibEv.ssConcatDiffItem`). -/
theorem ev186 (H : HookParams) : EntailsAtValues (cH H) U.ax186 (trS U.ax186).pat := by
  rw [(by decide +kernel : (trS U.ax186).pat = (trAxiom [] [] U.ax186).pat)]
  exact LibEv.ssConcatDiffItem_ev (coreOKH H) (shapesOKH H) U.ax186 (by decide +kernel) (by decide +kernel)

/-- domains.md 857 (`LibEv.ssItemUnionConcat`). -/
theorem ev253 (H : HookParams) : EntailsAtValues (cH H) U.ax253 (trS U.ax253).pat := by
  rw [(by decide +kernel : (trS U.ax253).pat = (trAxiom [] [] U.ax253).pat)]
  exact LibEv.ssItemUnionConcat_ev (coreOKH H) (shapesOKH H) U.ax253 (by decide +kernel) (by decide +kernel)

/-- domains.md 857 (`LibEv.ssConcatUnionItem`). -/
theorem ev254 (H : HookParams) : EntailsAtValues (cH H) U.ax254 (trS U.ax254).pat := by
  rw [(by decide +kernel : (trS U.ax254).pat = (trAxiom [] [] U.ax254).pat)]
  exact LibEv.ssConcatUnionItem_ev (coreOKH H) (shapesOKH H) U.ax254 (by decide +kernel) (by decide +kernel)

/-- domains.md 867 (`LibEv.ssItemInterConcat`). -/
theorem ev265 (H : HookParams) : EntailsAtValues (cH H) U.ax265 (trS U.ax265).pat := by
  rw [(by decide +kernel : (trS U.ax265).pat = (trAxiom [] [] U.ax265).pat)]
  exact LibEv.ssItemInterConcat_ev (coreOKH H) (shapesOKH H) U.ax265 (by decide +kernel) (by decide +kernel)

/-- domains.md 867 (`LibEv.ssConcatInterItem`). -/
theorem ev266 (H : HookParams) : EntailsAtValues (cH H) U.ax266 (trS U.ax266).pat := by
  rw [(by decide +kernel : (trS U.ax266).pat = (trAxiom [] [] U.ax266).pat)]
  exact LibEv.ssConcatInterItem_ev (coreOKH H) (shapesOKH H) U.ax266 (by decide +kernel) (by decide +kernel)

/-- domains.md 871 (`LibEv.ssInterConcat2`). -/
theorem ev267 (H : HookParams) : EntailsAtValues (cH H) U.ax267 (trS U.ax267).pat := by
  rw [(by decide +kernel : (trS U.ax267).pat = (trAxiom [] [] U.ax267).pat)]
  exact LibEv.ssInterConcat2_ev (coreOKH H) (shapesOKH H) U.ax267 (by decide +kernel) (by decide +kernel)

/-- domains.md 877 (`LibEv.ssInConcat`). -/
theorem ev187 (H : HookParams) : EntailsAtValues (cH H) U.ax187 (trS U.ax187).pat := by
  rw [(by decide +kernel : (trS U.ax187).pat = (trAxiom [] [] U.ax187).pat)]
  exact LibEv.ssInConcat_ev (coreOKH H) (shapesOKH H) U.ax187 (by decide +kernel) (by decide +kernel)

/-- domains.md 886 (`LibEv.ssInUnionL`). -/
theorem ev189 (H : HookParams) : EntailsAtValues (cH H) U.ax189 (trS U.ax189).pat := by
  rw [(by decide +kernel : (trS U.ax189).pat = (trAxiom [] [] U.ax189).pat)]
  exact LibEv.ssInUnionL_ev (coreOKH H) (shapesOKH H) U.ax189 (by decide +kernel) (by decide +kernel)

/-- domains.md 888 (`LibEv.ssInUnionR`). -/
theorem ev188 (H : HookParams) : EntailsAtValues (cH H) U.ax188 (trS U.ax188).pat := by
  rw [(by decide +kernel : (trS U.ax188).pat = (trAxiom [] [] U.ax188).pat)]
  exact LibEv.ssInUnionR_ev (coreOKH H) (shapesOKH H) U.ax188 (by decide +kernel) (by decide +kernel)

/-- domains.md 449 (`LibEv.msInKeysUnitSv false`), over the set variable `@Key`: entailed at set values. -/
theorem ev157 (H : HookParams) : EntailsAtSetValues (cH H) U.ax157 (trS U.ax157).pat := by
  rw [(by decide +kernel : (trS U.ax157).pat = (trAxiom [] [] U.ax157).pat)]
  exact LibEv.msInKeysUnitSv_ev (coreOKH H) false U.ax157 (by decide +kernel) (by decide +kernel)

/-- domains.md 450 (`LibEv.msInKeysUnitSv true`). -/
theorem ev148 (H : HookParams) : EntailsAtSetValues (cH H) U.ax148 (trS U.ax148).pat := by
  rw [(by decide +kernel : (trS U.ax148).pat = (trAxiom [] [] U.ax148).pat)]
  exact LibEv.msInKeysUnitSv_ev (coreOKH H) true U.ax148 (by decide +kernel) (by decide +kernel)

/-! ## A `requires` comparing two KItem variables with `=/=K` or `==K` (`LibEv.EqnK`) -/

/-- domains.md 435 (`LibEv.msLookupUpdNe`). -/
theorem ev168 (H : HookParams) : EntailsAtValues (cH H) U.ax168 (trS U.ax168).pat := by
  rw [(by decide +kernel : (trS U.ax168).pat = (trAxiom [] [] U.ax168).pat)]
  exact LibEv.msLookupUpdNe_ev (coreOKH H) (shapesOKH H) U.ax168 (by decide +kernel) (by decide +kernel)

/-- domains.md 440 (`LibEv.msLookupDefUpdNe`). -/
theorem ev173 (H : HookParams) : EntailsAtValues (cH H) U.ax173 (trS U.ax173).pat := by
  rw [(by decide +kernel : (trS U.ax173).pat = (trAxiom [] [] U.ax173).pat)]
  exact LibEv.msLookupDefUpdNe_ev (coreOKH H) (shapesOKH H) U.ax173 (by decide +kernel) (by decide +kernel)

/-- domains.md 433 (`LibEv.msLookupConcatNe`). -/
theorem ev171 (H : HookParams) : EntailsAtValues (cH H) U.ax171 (trS U.ax171).pat := by
  rw [(by decide +kernel : (trS U.ax171).pat = (trAxiom [] [] U.ax171).pat)]
  exact LibEv.msLookupConcatNe_ev (coreOKH H) (shapesOKH H) U.ax171 (by decide +kernel) (by decide +kernel)

/-- domains.md 438 (`LibEv.msLookupDefConcatNe`). -/
theorem ev176 (H : HookParams) : EntailsAtValues (cH H) U.ax176 (trS U.ax176).pat := by
  rw [(by decide +kernel : (trS U.ax176).pat = (trAxiom [] [] U.ax176).pat)]
  exact LibEv.msLookupDefConcatNe_ev (coreOKH H) (shapesOKH H) U.ax176 (by decide +kernel) (by decide +kernel)

/-- domains.md 422 (`LibEv.msUpdConcatNe`). -/
theorem ev180 (H : HookParams) : EntailsAtValues (cH H) U.ax180 (trS U.ax180).pat := by
  rw [(by decide +kernel : (trS U.ax180).pat = (trAxiom [] [] U.ax180).pat)]
  exact LibEv.msUpdConcatNe_ev (coreOKH H) (shapesOKH H) U.ax180 (by decide +kernel) (by decide +kernel)

/-- domains.md 429 (`LibEv.msRemConcatNe`). -/
theorem ev217 (H : HookParams) : EntailsAtValues (cH H) U.ax217 (trS U.ax217).pat := by
  rw [(by decide +kernel : (trS U.ax217).pat = (trAxiom [] [] U.ax217).pat)]
  exact LibEv.msRemConcatNe_ev (coreOKH H) (shapesOKH H) U.ax217 (by decide +kernel) (by decide +kernel)

/-- domains.md 447 (`LibEv.msInKeysUpdNe`). -/
theorem ev234 (H : HookParams) : EntailsAtValues (cH H) U.ax234 (trS U.ax234).pat := by
  rw [(by decide +kernel : (trS U.ax234).pat = (trAxiom [] [] U.ax234).pat)]
  exact LibEv.msInKeysUpdNe_ev (coreOKH H) (shapesOKH H) U.ax234 (by decide +kernel) (by decide +kernel)

/-- domains.md 446 (`LibEv.msInKeysUpdOr`). -/
theorem ev235 (H : HookParams) : EntailsAtValues (cH H) U.ax235 (trS U.ax235).pat := by
  rw [(by decide +kernel : (trS U.ax235).pat = (trAxiom [] [] U.ax235).pat)]
  exact LibEv.msInKeysUpdOr_ev (coreOKH H) (shapesOKH H) U.ax235 (by decide +kernel) (by decide +kernel)

/-! ## Over set variables, refuted at values, and the companions at sets of at most one value -/

/-- What a refutation at values gives: Γ with the sentence has no model. -/
theorem refuted_of_at {c' : Semantics} {ad : AxiomDecl} {φ : KoreAML.P}
    (hat : ∀ (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' →
      ∃ e : Valuation M, AtValues c' I e ad.ax ∧ SetVarsAtValues c' I e ad.ax ∧ ¬ φ.interpret I e default) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' → ¬ (I ⊧ᴵ φ) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := hat M I hI
  exact hn (hax e default)

/-- The KItem injections of 0 and 1. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)
def k1 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 1)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_k1 (H : HookParams) : (cH H).sortOf k1 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_m2 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0), (k1, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_s0 (H : HookParams) : (cH H).sortOf (.set Srt.set []) = some Srt.set := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel
theorem sort_s1 (H : HookParams) : (cH H).sortOf (.set Srt.set [k0]) = some Srt.set := by
  rw [Semantics.sortOf_withHooks_rawFree c H rfl]; decide +kernel

theorem t137 : (trS U.ax137).pat = (trAxiom [] [] U.ax137).pat := by decide +kernel
theorem t138 : (trS U.ax138).pat = (trAxiom [] [] U.ax138).pat := by decide +kernel
theorem t149 : (trS U.ax149).pat = (trAxiom [] [] U.ax149).pat := by decide +kernel
theorem t158 : (trS U.ax158).pat = (trAxiom [] [] U.ax158).pat := by decide +kernel

/-- domains.md 411 (`LibEv.msLookupCeilSv`): at `@K = {0}`, `@M = {.Map, 0 |-> 0}` the left side
holds (`(0 |-> 0) [ 0 ]` is `0`) and `0 in_keys(.Map)` is `false`. -/
theorem s137_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax137.ax ∧ SetVarsAtValues (cH H) I e U.ax137.ax ∧
      ¬ (trS U.ax137).pat.interpret I e default := by
  rw [t137]
  exact LibEv.msLookupCeilSv_refuted_at (coreOKH H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax137 (by decide +kernel) (by decide +kernel) hI

theorem s137_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax137).pat) := refuted_of_at (s137_at H)

theorem s137_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax137 (trS U.ax137).pat := by
  rw [t137]
  exact LibEv.msLookupCeilSv_one (coreOKH H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax137 (by decide +kernel) (by decide +kernel)

/-- domains.md 830 (`LibEv.ssConcatCeilSv`): at `@E = {0}`, `@S = {.Set, SetItem(0)}` the left side
holds (`.Set SetItem(0)` has a value) and `0 in SetItem(0)` is `true`. -/
theorem s138_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax138.ax ∧ SetVarsAtValues (cH H) I e U.ax138.ax ∧
      ¬ (trS U.ax138).pat.interpret I e default := by
  rw [t138]
  exact LibEv.ssConcatCeilSv_refuted_at (coreOKH H) (by decide +kernel) (by rfl) k0 [] [k0] (sort_k0 H)
    (sort_s0 H) (sort_s1 H) rfl (by decide +kernel) U.ax138 (by decide +kernel) (by decide +kernel) hI

theorem s138_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax138).pat) := refuted_of_at (s138_at H)

theorem s138_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax138 (trS U.ax138).pat := by
  rw [t138]
  exact LibEv.ssConcatCeilSv_one (coreOKH H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.set = true) U.ax138 (by decide +kernel) (by decide +kernel)

/-- domains.md 451 (`LibEv.msInKeysConcatSv false`): at `@Key = {1}`, `Key' = Val = 0` and
`@M = {.Map, 0 |-> 0 1 |-> 0}` the left side holds (`0 |-> 0 .Map` has no key 1, and
`0 |-> 0 (0 |-> 0 1 |-> 0)` no value) and `1 in_keys(0 |-> 0 1 |-> 0)` is `true`. -/
theorem s158_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax158.ax ∧ SetVarsAtValues (cH H) I e U.ax158.ax ∧
      ¬ (trS U.ax158).pat.interpret I e default := by
  rw [t158]
  exact LibEv.msInKeysConcatSv_refuted_at (coreOKH H) false (by decide +kernel) (by rfl) k1 k0 k0 []
    [(k0, k0), (k1, k0)] (sort_k1 H) (sort_k0 H) (sort_k0 H) (sort_m0 H) (sort_m2 H) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) U.ax158 (by decide +kernel) (by decide +kernel) hI

theorem s158_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax158).pat) := refuted_of_at (s158_at H)

theorem s158_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax158 (trS U.ax158).pat := by
  rw [t158]
  exact LibEv.msInKeysConcatSv_one (coreOKH H) (shapesOKH H) false (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax158 (by decide +kernel) (by decide +kernel)

/-- domains.md 452 (`LibEv.msInKeysConcatSv true`), at the same sets. -/
theorem s149_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax149.ax ∧ SetVarsAtValues (cH H) I e U.ax149.ax ∧
      ¬ (trS U.ax149).pat.interpret I e default := by
  rw [t149]
  exact LibEv.msInKeysConcatSv_refuted_at (coreOKH H) true (by decide +kernel) (by rfl) k1 k0 k0 []
    [(k0, k0), (k1, k0)] (sort_k1 H) (sort_k0 H) (sort_k0 H) (sort_m0 H) (sort_m2 H) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) U.ax149 (by decide +kernel) (by decide +kernel) hI

theorem s149_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax149).pat) := refuted_of_at (s149_at H)

theorem s149_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax149 (trS U.ax149).pat := by
  rw [t149]
  exact LibEv.msInKeysConcatSv_one (coreOKH H) (shapesOKH H) true (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax149 (by decide +kernel) (by decide +kernel)

end KCore.LibEvCollSym

/-- info: 'KCore.LibEvCollSym.ev179' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev179
/-- info: 'KCore.LibEvCollSym.ev177' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev177
/-- info: 'KCore.LibEvCollSym.ev178' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev178
/-- info: 'KCore.LibEvCollSym.ev215' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev215
/-- info: 'KCore.LibEvCollSym.ev169' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev169
/-- info: 'KCore.LibEvCollSym.ev174' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev174
/-- info: 'KCore.LibEvCollSym.ev172' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev172
/-- info: 'KCore.LibEvCollSym.ev233' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev233
/-- info: 'KCore.LibEvCollSym.ev232' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev232
/-- info: 'KCore.LibEvCollSym.ev181' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev181
/-- info: 'KCore.LibEvCollSym.ev183' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev183
/-- info: 'KCore.LibEvCollSym.ev250' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev250
/-- info: 'KCore.LibEvCollSym.ev252' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev252
/-- info: 'KCore.LibEvCollSym.ev249' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev249
/-- info: 'KCore.LibEvCollSym.ev263' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev263
/-- info: 'KCore.LibEvCollSym.ev264' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev264
/-- info: 'KCore.LibEvCollSym.ev262' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev262
/-- info: 'KCore.LibEvCollSym.ev190' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev190
/-- info: 'KCore.LibEvCollSym.ev216' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev216
/-- info: 'KCore.LibEvCollSym.ev170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev170
/-- info: 'KCore.LibEvCollSym.ev175' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev175
/-- info: 'KCore.LibEvCollSym.ev184' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev184
/-- info: 'KCore.LibEvCollSym.ev182' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev182
/-- info: 'KCore.LibEvCollSym.ev185' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev185
/-- info: 'KCore.LibEvCollSym.ev186' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev186
/-- info: 'KCore.LibEvCollSym.ev253' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev253
/-- info: 'KCore.LibEvCollSym.ev254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev254
/-- info: 'KCore.LibEvCollSym.ev265' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev265
/-- info: 'KCore.LibEvCollSym.ev266' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev266
/-- info: 'KCore.LibEvCollSym.ev267' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev267
/-- info: 'KCore.LibEvCollSym.ev187' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev187
/-- info: 'KCore.LibEvCollSym.ev189' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev189
/-- info: 'KCore.LibEvCollSym.ev188' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev188
/-- info: 'KCore.LibEvCollSym.ev157' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev157
/-- info: 'KCore.LibEvCollSym.ev148' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev148
/-- info: 'KCore.LibEvCollSym.ev168' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev168
/-- info: 'KCore.LibEvCollSym.ev173' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev173
/-- info: 'KCore.LibEvCollSym.ev171' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev171
/-- info: 'KCore.LibEvCollSym.ev176' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev176
/-- info: 'KCore.LibEvCollSym.ev180' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev180
/-- info: 'KCore.LibEvCollSym.ev217' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev217
/-- info: 'KCore.LibEvCollSym.ev234' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev234
/-- info: 'KCore.LibEvCollSym.ev235' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.ev235
/-- info: 'KCore.LibEvCollSym.s137_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s137_refuted
/-- info: 'KCore.LibEvCollSym.s137_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s137_one
/-- info: 'KCore.LibEvCollSym.s138_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s138_refuted
/-- info: 'KCore.LibEvCollSym.s138_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s138_one
/-- info: 'KCore.LibEvCollSym.s158_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s158_refuted
/-- info: 'KCore.LibEvCollSym.s158_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s158_one
/-- info: 'KCore.LibEvCollSym.s149_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s149_refuted
/-- info: 'KCore.LibEvCollSym.s149_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCollSym.s149_one
