/-
  KCore, tooling (compiled, not reviewed). The sentences of the tie class `parameter lemma`
  (`tieClasses`): a lemma, which the reader leaves out of Γ (`InertReason.simplification`), that
  applies a parameter symbol no registry hook interprets (`impl = none`). Such a symbol's value is
  the interpretation's at every argument list, so whether the lemma holds depends on `H`: it is owed
  as a hypothesis on `H`, the sentence itself at the member (`Γ (c.withHooks H) ⊧ tr s`). The
  account (`kcore account`) and test/constructs/tiegen.py's probe class a sentence by these two
  definitions.

  Beside it, the tie class `parameter functional`: the `functional` sentence of a parameter symbol
  that no registry hook interprets and that the text declares total (`Definition.totalParams`). The
  reader reads the sentence as that declaration; `Γ` states the parameter's graph at values from
  the interpretation (`ΓDomains`: its application to values denotes `paramVal`'s value, or nothing),
  so the sentence holds at values where `H` gives the parameter a value of its sort at every argument
  list of its sorts. The statements take that of `H` as a hypothesis (`ParamsTotal`): the sentence is
  owed as it.
-/
import KcoreSpec.TieHeads
import KcoreSpec.ParamsTotal

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

/-- The axiom `a` is the `functional` sentence `\exists(V, \equals(V, f(…)))` of a symbol `f`
without sort arguments named in `ns`. -/
def functionalOfNamed (ns : List String) (a : Kore.Axiom) : Bool :=
  AttrsAgree.has a.attributes "functional" && match a.pattern with
    | .exist _ _ (.equals _ _ _ (.app h [] _)) => ns.contains h.ident.name
    | _ => false

/-- The axiom `a` is of the tie class `parameter functional`: the `functional` sentence of a
parameter symbol that no registry hook interprets and that `d` declares total
(`Definition.totalParams`), owed as `ParamsTotal`. -/
def isParamFunctional (d : Definition) (a : Kore.Axiom) : Bool :=
  functionalOfNamed (d.totalParams.map d.sem.symName) a

end KCore
