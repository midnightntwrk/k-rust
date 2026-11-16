# aml-port: aml-lean's MatchingLogic core on Lean v4.34.0, without Mathlib

This is a port of the ILDS aml-lean `MatchingLogic` library (applicative matching μ-logic: patterns, a Hilbert-style proof system, and its soundness) to Lean `v4.34.0`, with no Mathlib and no Batteries dependency.

Upstream: <https://gitlab.com/ilds/aml-lean/MatchingLogic>, commit `f814358465e4015134bc31daa23f51e5cb7537fa` (2024-09-27, "Towards equivalence congruence"), written for Lean `v4.12.0-rc1` with `import Mathlib`.
The upstream MIT `LICENSE` and the per-file copyright headers are kept.

## Scope

Exactly the modules reachable from upstream's root `MatchingLogic.lean`: `Util`, `Variable`, `Pattern`, `PrettyPrinterOptions`, `Substitution`, `Positivity`, `AppContext`, `Premises`, `Tautology`, `Proof`, `Definedness`, `DeductionTheorem`, `Semantics`, `Soundness`.
`Sorted.lean`, `SortedPattern.lean`, `SubstContext.lean` and `Sorts.lean` are not reachable from the root and are left out.

## What changed and why

The statements are unchanged: `Pattern`, `Pattern.interpret`, `entails`, `Proof`, the definedness notions, `Proof.deductionTheorem` and `Proof.soundness : Γ ⊢ φ → Γ ⊧ φ` say the same thing as upstream.
Only proofs changed, plus the following.

- `MatchingLogic/Prelude.lean` (new) replaces `import Mathlib` in `Util.lean`.
  It restates the Mathlib definitions the library uses, with Mathlib's definitions: `ℕ`, `Set α := α → Prop` with `∈`, `⊆`, `∪`, `{a}` and `Set.image`, and the dependent `Function.update`.
  It adds the few lemmas the proofs need (`update_same`, `update_noteq`, `update_apply`, `update_comm`, `update_idem`, `not_imp_not`).
- Mathlib tactics are replaced: `simp_rw` by `simp only`; `aesop`/`tauto` on propositional tautologies by a small `taut_morphism` macro (in `Tautology.lean`) that unfolds the morphism laws and calls core `grind`; `use` and `lemma` by core equivalents.
- `Premises.lean`: upstream's `attribute [reducible] Premises in instance ...` already made `Premises` globally reducible; Lean `v4.34.0` rejects the misleading `in`, so the attribute is now written globally.
- `DeductionTheorem.lean` gains two helper lemmas about `⌊ψ⌋` (`total_muClosed`, `total_not_free_evar`) that replace `simp [*] at *` calls which no longer close those goals.
- `Soundness.lean`: upstream had a live `#exit` just before `prefixpoint_sound`, so `prefixpoint_sound`, `substitution_sound`, `knasterTarski_sound` and `Proof.soundness` were never checked upstream.
  The port removes the `#exit`; that code then checks without modification.
  The proofs of `only_free_var_relevant`, `subf_xy_eq_eval_xey`, `𝓕𝓖_monotone` and `subf_Xδ_eq_eval_Xeδ` were rewritten, because their Mathlib-era `simp` scripts no longer go through.
- `Positivity.lean`: the four sanity-check `example`s use `decide` instead of `native_decide`.
- Many small proofs were repaired for renamed core lemmas and changed `simp` behaviour.

## Checking

```sh
lake build
lake env lean <file containing: import MatchingLogic / #print axioms ML.Proof.soundness>
```

`#print axioms ML.Proof.soundness` reports `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit` or `axiom` declaration occurs outside comments.
