/-
  KCore, tooling (compiled, not reviewed). The sentences of the tie class `parameter lemma`
  (`tieClasses`): a lemma, which the reader leaves out of Γ (`InertReason.simplification`), or a
  `simplification` sentence of K's builtin library, which the reader reads as the library's text
  (`read`) and of which Γ holds no item (Γ's premises are the signature, constructor, domain,
  collection and fallback families and the function and rule items), whose truth at values reads a
  value the interpretation gives. It reads one where it applies a parameter symbol no registry hook
  interprets (`impl = none`), whose value is the interpretation's at every argument list; or a
  function of the semantics at argument lists none of its clauses decides, where Γ states the
  function's rest (`Semantics.fnRest`) from the interpretation (`ΓFallback`); or a hook at a point its
  text leaves open (`Semantics.fallback`), where Γ states the interpretation's value. Whether the
  lemma holds then depends on `H`: it is owed as a hypothesis on `H` at values: some `H` meets the
  hypothesis on the functions (`FnHyp`) and at it every sentence of the class holds at the
  valuations sending its variables to values (`EntailsAtValues (c.withHooks H) s (tr s)`). `Γ` states
  a parameter's graph, a function's rest and a hook's open point at values only and says nothing of
  them at an element of a sort that is no value's, where a model of `Γ` may give them nothing, so the
  sentence is not owed at every valuation.

  `isParamLemma` (a lemma of the text) and `isLibParamLemma` (a sentence of the builtin library) are
  sufficient shapes of the class, not its definition: they decide the first case. Whether a lemma
  reads a function's rest or a hook's open point no shape of it decides (it depends on where the
  clauses and the hook's text decide, and a lemma that applies such a symbol need not depend on what
  `H` gives there); the tie's author names such a lemma (test/constructs/tiegen.py `--reads-h`), and
  the tie decides of it the necessary condition `appliesHRead`: it applies, at a head Γ has, a symbol
  through which evaluation may read the interpretation (`Parse.lawReadsFL`). The account
  (`kcore account`) classes a sentence by the shapes, and test/constructs/tiegen.py's probe by the
  same conditions.

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
import KcoreSpec.Account

set_option autoImplicit false

namespace KCore

/-- The pattern applies a parameter symbol of `c` that no registry hook interprets (`impl = none`),
at the head at which Γ applies that symbol (`gammaHead`). -/
def appliesNoImplParam (c : Semantics) (p : Kore.Pattern) : Bool :=
  (appHeadsOf p).any fun h =>
    c.params.any fun k => k.impl.isNone && decide (gammaHead c k.sig.name = h)

/-- The fuel `appliesHRead` gives `Parse.lawReadsFL`'s search from one symbol: each step searches one
symbol, so the search ends before it on a text of fewer symbols; where it does not, the search has
not ruled the interpretation out and `appliesHRead` holds. -/
def appliesHReadFuel : Nat := 100000

/-- The pattern applies, at a head Γ has (`gammaHead` of a symbol of `kernelSyms`), a symbol through
which evaluation may read the interpretation (`Parse.lawReadsFL`): a parameter without `impl`, a
function not shown to be decided by its clauses at every argument list (its rest), a hook at a point
its text leaves open, or a symbol whose clauses or overloads apply one. It is necessary, not
sufficient, for the truth at values of a sentence of the pattern to depend on the interpretation. -/
def appliesHRead (c : Semantics) (p : Kore.Pattern) : Bool :=
  (appHeadsOf p).any fun h =>
    (Faithful.kernelSyms c).any fun k =>
      decide (gammaHead c k.name = h) && (Parse.lawReadsFL c appliesHReadFuel [] [k.name]).isSome

/-- Γ's heads with their symbols: `gammaHead` of each symbol of `kernelSyms`. -/
def appliesHReadHeads (c : Semantics) : List ((String × List Kore.KSort) × Sym) :=
  (Faithful.kernelSyms c).map fun k => (gammaHead c k.name, k.name)

/-- What the first head of `p` that `appliesHRead` finds reads of the interpretation
(`Parse.lawReadsFL`'s answer), over the heads `gk` (`appliesHReadHeads c`, computed once by the
account for all its sentences); `none` where `appliesHRead c p` fails. -/
def appliesHReadWhat (c : Semantics) (gk : List ((String × List Kore.KSort) × Sym))
    (p : Kore.Pattern) : Option String :=
  (appHeadsOf p).findSome? fun h =>
    gk.findSome? fun (h', g) => if h' = h then Parse.lawReadsFL c appliesHReadFuel [] [g] else none

/-- The sentence `s`, of the reader's class `cl`, is of the tie class `parameter lemma` as a lemma
of the text by its shape: a lemma (`InertReason.simplification`, no item of Γ) applying a parameter
symbol without `impl`. A sufficient condition of the class: the class also holds the builtin
library's such sentences (`isLibParamLemma`) and the lemmas the tie names (`appliesHRead`). -/
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
