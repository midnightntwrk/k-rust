/-
  The statements of C10 (kore.k's `succs` against the object semantics), pinned on the package
  `kcore gen --core` writes for kore.k read from kompile's own KORE
  (examples/ref-kk/RefKk/definition.kore), with the User modules of examples/ref-kk up to
  User.KkThree built over it. Each is checked by its proof term at the type written out:

  - the three statements, `KK.succs_sound : SuccsSound KK.sig`, `KK.succs_stuck : SuccsStuck KK.sig`,
    `KK.succs_complete : SuccsComplete KK.sig` (the propositions of KcoreSpec/KKStatements.lean),
    and `KK.kk_step`, their conjunction;
  - `KK.sig`, equal by `rfl` to its seven fields named: kore.k's semantics `RefKk.defn.sem`, the
    symbol 510 of `succs` (`KK.succs_name` states its KORE name), the embeddings `emb`, `embD`,
    `embSt`, the encoding `enc` of a configuration and `encDef` of a definition;
  - what the statements rest on: `KK.enc_injective` (two configurations of `d₀ d` with one encoding
    are one, under `encDef d = some E`), `KK.emb_injective`, `KK.embSt_injective`, `KK.emb_sorted`,
    `KK.embD_sorted` (the embeddings are values of kore.k's sorts `Term` and `Def`) and
    `KK.encDef_isSome` (`encDef` has a value exactly where `encodable` holds);
  - `KK.encodable`, equal by `rfl` to its eleven conjuncts named (`ovlsOK`, `paramsOK`, `appsOK`,
    `headsOK`, `litsOK`, `subsortsOK`, `colPatsOK`, `asOK`, `ensOK`, `shapesOK`, `collFormOK`):
    a condition added to it narrows the hypothesis `encDef d = some E` of the three statements, and
    fails this file.

  Their axioms are within `propext`, `Classical.choice`, `Quot.sound` (the loop at the end).
  test/pins-kk.sh generates the package under the namespace `RefKk` into .lake/pins/kk, builds it
  with the User modules and checks this file against it:

      gen/gen.sh examples/ref-kk/RefKk/definition.kore .lake/pins/kk RefKk --core
      gen/build.sh .lake/pins/kk User.Coherent … User.KkThree
      LEAN_PATH=.lake/pins/kk/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) lean test/PinsKk.lean
-/
import User.KkThree

set_option autoImplicit false

namespace KCore.KK.PinsKk

open KCore KCore.KK

/-! ## The three statements -/

example : SuccsSound sig := succs_sound
example : SuccsStuck sig := succs_stuck
example : SuccsComplete sig := succs_complete
example : SuccsSound sig ∧ SuccsStuck sig ∧ SuccsComplete sig := kk_step

/-! ## `KK.sig` and its fields -/

example : sig = ⟨RefKk.defn.sem, 510, emb, embD, embSt, enc, encDef⟩ := rfl
example : sig.K = RefKk.defn.sem := rfl
example : sig.succs = 510 := rfl
example : sig.emb = emb := rfl
example : sig.embD = embD := rfl
example : sig.embSt = embSt := rfl
example : sig.enc = enc := rfl
example : sig.encDef = encDef := rfl

example : RefKk.defn.sem.symName sig.succs =
    "Lblsuccs'LParUndsCommUndsRParUnds'KORE'Unds'Step'Unds'Def'Unds'Term" := succs_name

/-! ## What the statements rest on -/

example : ∀ {d : Semantics} {E : D}, encDef d = some E → ∀ {x y : Config (d₀ d)},
    enc x.val = enc y.val → x = y := @enc_injective
example : Function.Injective emb := emb_injective
example : Function.Injective embSt := embSt_injective
example : ∀ t : T, (K₀ sig).sortOf (emb t) = some 33 := emb_sorted
example : ∀ E : D, (K₀ sig).sortOf (embD E) = some 45 := embD_sorted
example : ∀ d : Semantics, (encDef d).isSome = encodable d := encDef_isSome
example (d : Semantics) : encodable d = (ovlsOK d && paramsOK d && appsOK d && headsOK d &&
    litsOK d && subsortsOK d && colPatsOK d && asOK d && ensOK d && shapesOK d && collFormOK d) :=
  rfl

/-! ## Axioms -/

open Lean in
#eval show CoreM Unit from do
  for n in [``succs_sound, ``succs_stuck, ``succs_complete, ``kk_step, ``sig, ``succs_name,
      ``enc_injective, ``emb_injective, ``embSt_injective, ``emb_sorted, ``embD_sorted,
      ``encDef_isSome] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"
  IO.println "pins on kk: 12 declarations within propext, Classical.choice, Quot.sound"

end KCore.KK.PinsKk
