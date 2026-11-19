/-
  KCore, tooling (compiled, not reviewed). The sentences of the tie class `parameter lemma`
  (`tieClasses`): a lemma, which the reader leaves out of Γ (`InertReason.simplification`), that
  applies a parameter symbol no registry hook interprets (`impl = none`) (`isParamLemma`), and a
  `simplification` sentence of K's builtin library that applies one (`isLibParamLemma`): the reader
  reads it as the library's text (`read`) and Γ holds no item of it (Γ's premises are the signature,
  constructor, domain, collection and fallback families and the function and rule items), so it
  rests on the parameter's value as a user's lemma does, and is not of the class `library`, whose
  sentences hold at values over symbols Γ interprets for every `H`. Such a symbol's value is
  the interpretation's at every argument list, so whether the lemma holds depends on `H`: it is owed
  as a hypothesis on `H` at values: some `H` meets the hypothesis on the functions (`FnHyp`) and
  at it every sentence of the class holds at the valuations sending its variables to values
  (`EntailsAtValues (c.withHooks H) s (tr s)`). `Γ` states the parameter's graph at values only and
  says nothing of it at an element of its sort that is no value's, where a model of `Γ` may give it
  nothing, so the sentence is not owed at every valuation. The account (`kcore account`) classes a
  sentence by these definitions, and test/constructs/tiegen.py's probe by the same conditions.

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

/-- The sentence `s`, of the reader's class `cl`, is of the tie class `parameter lemma` as a lemma
of the text: a lemma (`InertReason.simplification`, no item of Γ) applying a parameter symbol
without `impl`. The class's other sentences are the builtin library's (`isLibParamLemma`). -/
def isParamLemma (c : Semantics) (cl : Parse.SentenceClass) (s : Kore.Sentence) : Bool :=
  cl == .inert .simplification && match s with
    | .axiom a => appliesNoImplParam c a.pattern
    | _ => false

/-- The sentence `s`, of the reader's class `cl`, is of the tie class `parameter lemma` as a
sentence of K's builtin library: a `simplification` sentence of a K installation's builtin file
(`Parse.isKBuiltin`) that the reader reads as the library's text (`read`; Γ holds no item of it)
and that applies a parameter symbol of `c` without `impl`. Its truth depends on `H` as that of a
lemma `isParamLemma` classes does. -/
def isLibParamLemma (c : Semantics) (cl : Parse.SentenceClass) (s : Kore.Sentence) : Bool :=
  cl == .read && match s with
    | .axiom a => Parse.isKBuiltin a.attributes && AttrsAgree.has a.attributes "simplification" &&
        appliesNoImplParam c a.pattern
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
