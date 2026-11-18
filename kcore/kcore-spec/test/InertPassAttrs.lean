/-
  The C2 evidence of the inert compile pass addCoolLikeAtt (E7), which writes `cool-like{}()` on
  each cooling rule and no sentence, beyond the tie of those rules (test/TieE1Sentences.lean,
  `rule0_from_text` to `rule3_from_text`: Γ's item of each of the four cooling rules, sentences 182
  to 185, is a consequence of the sentence).
  Run from the package root: `lake env lean -j1 test/InertPassAttrs.lean`. Nothing reads
  `Parse.parse` or `emit`.

  - `CoolLike`: `f2-examples/e1-sentences.kompile.kore`, fixture e1-sentences' kompiled text with its
    paths restored, against `f2-examples/e1-sentences-nocoollike.kore`, the same text with the
    attribute removed from its four cooling rules (and from their `// rule` comments) by hand: the
    two have one semantics (`sem_eq`), so at every H one Γ and one `Step` (`withHooks_eq`,
    `gamma_eq`). The translation of a sentence does not read its attributes
    (`InertSemPairs.trS_attrs`), so the four sentences' translations are the same in both texts.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.InertPassAttrs

open KCore ML Faithful KoreAML

namespace CoolLike

namespace Text
definition_of defn from "f2-examples/e1-sentences.kompile.kore"
end Text
namespace NoAttr
definition_of defn from "f2-examples/e1-sentences-nocoollike.kore"
end NoAttr

/-- **`cool-like` leaves the semantics as it is.** -/
theorem sem_eq : Text.defn.sem = NoAttr.defn.sem := rfl
theorem withHooks_eq (H : HookParams) : Text.defn.sem.withHooks H = NoAttr.defn.sem.withHooks H :=
  congrArg (Semantics.withHooks · H) sem_eq
theorem gamma_eq (H : HookParams) : Γ (Text.defn.sem.withHooks H) = Γ (NoAttr.defn.sem.withHooks H) := by
  rw [withHooks_eq]

end CoolLike

end KCore.InertPassAttrs

#check @KCore.InertPassAttrs.CoolLike.sem_eq
#print axioms KCore.InertPassAttrs.CoolLike.sem_eq
#print axioms KCore.InertPassAttrs.CoolLike.withHooks_eq
#print axioms KCore.InertPassAttrs.CoolLike.gamma_eq
