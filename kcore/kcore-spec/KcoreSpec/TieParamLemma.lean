/-
  KCore, tooling (compiled, not reviewed). The sentences of the tie class `parameter lemma`
  (`tieClasses`): a lemma, which the reader leaves out of Γ (`InertReason.simplification`), that
  applies a parameter symbol no registry hook interprets (`impl = none`). Such a symbol's value is
  the interpretation's at every argument list, so whether the lemma holds depends on `H`: it is owed
  as a hypothesis on `H`, the sentence itself at the member (`Γ (c.withHooks H) ⊧ tr s`). The
  account (`kcore account`) and test/constructs/tiegen.py's probe class a sentence by these two
  definitions.
-/
import KcoreSpec.TieHeads

set_option autoImplicit false

namespace KCore

/-- The pattern applies a parameter symbol of `c` that no registry hook interprets (`impl = none`),
at the head at which Γ applies that symbol (`gammaHead`). -/
def appliesNoImplParam (c : Semantics) (p : Kore.Pattern) : Bool :=
  (appHeadsOf p).any fun h =>
    c.params.any fun k => k.impl.isNone && decide (gammaHead c k.sig.name = h)

/-- The sentence `s`, of the reader's class `cl`, is of the tie class `parameter lemma`: a lemma
(`InertReason.simplification`, no item of Γ) applying a parameter symbol without `impl`. -/
def isParamLemma (c : Semantics) (cl : Parse.SentenceClass) (s : Kore.Sentence) : Bool :=
  cl == .inert .simplification && match s with
    | .axiom a => appliesNoImplParam c a.pattern
    | _ => false

end KCore
