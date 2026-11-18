/-
  KCore. `parse : Kore.Definition → Except Refusal Definition`. NOT part of the reviewed layer
  (Tie.lean checks what it returns). It numbers the definition: the registry's names
  (FixedSignature.lean) and the definition's own sorts and symbols, in Core.lean's order, and it
  reads every name of a sentence as its number (`Names`). It reads the builtin modules the
  definition imports off its builtin sentences: krust's (`Source(krust-builtin://F)`) by their
  sources and lines (Builtins.lean); a K installation's (`…/include/kframework/builtin/F`) by the
  library sentence each equals up to its `Source` and `Location` (`kBuiltinModule?`), a sentence
  equal to none being refused. It takes the core's library and its builtin parameter symbols from
  them. Literals are read by their sort: an Int literal's text must be canonical, a Bool's `true`
  or `false`, a Float's one of K's Float literals, read as the datum it rounds to (`floatLit?`).

  Every sentence of the user module has a class (`classify`, from the sentence alone): read, inert
  with the reason the semantics does not read it, or refused with the reason. `parse` scans the
  sentences classified read and no other (`scan`). A text it does not read gives a `Refusal`: the
  sentence's position in the file, its head, and the reason, one of `RefusalReason`'s.
-/
import KcoreSpec.Emit
import KcoreSpec.Kore.Read
import KcoreSpec.FaithOK
import KcoreSpec.RightHeld
import KcoreSpec.ParseAttr

set_option autoImplicit false

namespace KCore.Parse

open KoreAML.Parse (dropPrefix? sortName? attrStr? hasAttr loc? source? info? eqnFuel argPats disjuncts
  binders)
open KoreAML (Var)

/-! ## Refusals and the classes of sentences -/

/-- Why the reader refuses a KORE text: one constructor for each place where reading fails. -/
inductive RefusalReason where
  /-- The definition has no module. -/
  | noModule
  /-- The modules before the last are not K's prelude (`preludeModules`), whose symbols the
  registry stands for. -/
  | preludeDiffers
  /-- The user module has no `Source` attribute. -/
  | moduleSource
  /-- The user module has no well-formed `Location` attribute. -/
  | moduleLocation
  /-- No `<generatedTop>` cell tree whose last cell is the counter, or no `<k>` cell. -/
  | configuration
  /-- A cell symbol whose arguments are neither all cells nor one sort. -/
  | cellShape
  /-- An equation the reader reads is missing: a sort's `isX` or `projectX`, a cell's initializer,
  `getGeneratedCounterCell`'s. -/
  | missingEquation
  /-- `getGeneratedCounterCell`'s equation is not over the top cell's cells as variables. -/
  | counterShape
  /-- No cell initializer's equation projects `$PGM` to a sort, or two project it to different
  sorts (`pgmSortOf`). -/
  | pgmSort
  /-- A sentence with a builtin source whose source and line are in no library module. -/
  | builtinModule
  /-- A sentence of a K installation's builtin file (`…/include/kframework/builtin/F`) that,
  without its `Source` and `Location`, is no sentence of the library's text: it states something
  the library does not. -/
  | builtinText
  /-- A library module the text holds sentences of, one of whose sentences in the library's text
  the text does not hold (`Account.missingBuiltin`): the library would read a declaration or axiom
  the text does not state. -/
  | builtinIncomplete
  /-- A symbol declared `macro`, `macro-rec`, `alias` or `alias-rec`: its applications stand for
  its macro's expansion, which the text does not give as equations, so it is not a function
  without clauses. -/
  | macroSymbol
  /-- An axiom classified inert as a constructor axiom (`distinctCtors`, `injectivity`, `noJunk`)
  that is not, up to variable names and the order of conjuncts and disjuncts, one the definition's
  constructors induce (`Account.uninduced`): it states something the semantics does not. -/
  | inertMismatch
  /-- An application of `inj{XCell, XCellMap}` (or a cell set's or list's): the subsort of a cell
  into its collection sort, which the reader does not read (`UnreadReason.cellCollectionInjection`);
  or a sentence classified so whose sorts are not a collection of the definition and its cell. -/
  | cellCollectionInjection
  /-- An alias declaration: KCore reads no alias, whose applications stand for its body. -/
  | aliasDeclaration
  /-- An axiom kompile writes for a `symbol-overload` pair that is not an equation `f(p̄) = r` of
  its first symbol f (`overloadEqn?`), or whose first symbol is neither an overloading symbol
  (`overloadForm` for one that is) nor a function of the definition (whose clause it is, aside, of
  priority 0: `overloadEqn?`). -/
  | overloadAxiom
  /-- An axiom of no form the reader reads or knows inert, of a form kompile 7.1.337 writes (a form
  it does not write at the top is `unkompiledForm`). -/
  | axiomShape
  /-- A sort with parameters, or a sort variable; a subsort axiom at an instance of a
  sort-parametric sort (`isParametricSubsort`). -/
  | parametricSort
  /-- A sort the definition does not have. -/
  | unknownSort
  /-- A sort declared under the name of a library module's sort (`syntax Bytes ::= ".Bytes"`,
  kompile's `sort SortBytes{} []`) by a text that imports no module declaring that sort. Names are
  numbered registry first, so the declaration would read as the library's sort, which the
  definition does not have; read as a sort of its own it would carry a registry sort's name, which
  the numbered sorts' names being apart excludes. -/
  | registrySortName
  /-- A symbol the definition does not have. -/
  | unknownSymbol
  /-- An application of an alias of K's prelude: in a term, or heading a rewrite axiom's right side
  (`weakAlwaysFinally{S}(\and(rhs, ens))`, kompile's form of a rule of a module carrying all-path or
  one-path; the detail names the alias) where the alias is not at one sort and one argument or the
  text's alias sentence for it is not the identity on its argument (`aliasIsIdentity`; where it is,
  the right side is read as the argument, `ReadingNote.identityAlias`). Refused by name and not
  expanded: the refusal states nothing of the sentence. -/
  | aliasApplication
  /-- A symbol applied with sort arguments (other than `inj` and `ite`) that is not an instance the
  definition has (`instName`): a hooked or constructor instance, one of a symbol outside the user's
  files, or one at sorts the definition does not have. -/
  | parametricSymbol
  /-- `inj` not applied to two sorts and one argument. -/
  | injShape
  /-- `ite` not applied to one sort. -/
  | iteShape
  /-- A connective that no term has, of those kompile 7.1.337 writes: `\or`, `\not`, `\ceil`,
  `\exists`, … (the others are `unkompiledForm`). -/
  | patternConnective
  /-- An element variable not named `Var…`. -/
  | variableName
  /-- One variable at two sorts. -/
  | variableSort
  /-- A domain value not written as its sort's values are (an Int not canonical, a Bool other
  than `true` and `false`). -/
  | literal
  /-- A `requires` that is not `\equals{SortBool{},S}(r, \dv{SortBool{}}("true"))` or `\top`. -/
  | requiresShape
  /-- A rewrite axiom not of the form `\rewrites(\and(lhs, req), \and(rhs, ens))` with `ens` `\top`
  or an `ensures`, `\equals{SortBool{},S}(C, \dv{SortBool{}}("true"))`. -/
  | ruleShape
  /-- An `[owise]` equation's exclusion of the other equations not of kompile's form. -/
  | exclusionShape
  /-- A function with an `[owise]` equation and another equation of priority 200 or more. The
  text's `[owise]` premise excludes every other equation, so it orders the `[owise]` equation
  after that one; the reading gives the `[owise]` equation priority 200, after the smaller
  priorities only, and two equations of one priority are unordered. The two differ wherever
  both equations apply. -/
  | owisePriority
  /-- A rule's left side or a clause's argument pattern that applies a function symbol (a function
  or sort predicate of the definition, a parameter that is no open generator, a hooked symbol of the
  registry), neither a constructor nor a collection's symbol: K's `List:set(L, I, J)` in a cell. A pattern denotes the
  values it matches; a function's application denotes the values the function takes at some
  arguments, and matching it needs what the function's inverse says, which no part of the semantics
  gives (the account's check, `Account.functionInPattern`). -/
  | functionInPattern
  /-- A rule or equation without a unique id or a well-formed location. -/
  | sentenceInfo
  /-- A declaration without the `Location` or `Source` attribute the reader reads. -/
  | location
  /-- A hooked symbol without a `hook` attribute. -/
  | hookAttribute
  /-- A collection sort whose element symbol is missing or of another arity than its kind's. -/
  | collectionShape
  /-- A sentence classified read that the definition `parse` builds does not account for: a
  declaration of a sort or symbol it does not have, an equation of no function it reads, a
  `functional` axiom of a function it does not read total, a `subsort` axiom of sorts it does not
  order so (the generator's check, `Account.consumed`). -/
  | unaccounted
  /-- A symbol-overload axiom of an overloading symbol (a user symbol declared `anywhere`, neither
  a constructor nor a function) that is not the overload the kernel states (`OvlSig`,
  `KoreAML.Cons.ovlEqItem`): `f(lift x̄) = lift (g(x̄))`, `x̄` distinct variables of g's argument
  sorts, `lift` an injection between two different sorts and nothing between equal ones, g a
  constructor, an overloading symbol or a function of the definition
  (`ReadingNote.overloadFunction`), the overloads acyclic. The detail names what the axiom has
  that this form has not. -/
  | overloadForm
  /-- A projection with a selector-domain axiom (`ReadingNote.projectionDomainAsClause`) read as a
  function whose equations are not the one equation `project:X(kseq(inj{X,KItem}(V), dotk)) = V`
  without `requires`, or with more than one such axiom: the axiom then says more than the read
  clause would. -/
  | projectionDomainShape
  /-- A symbol of a user's file declared neither `function` nor `constructor` (nor `anywhere`, nor a
  cell, macro or alias): kompile declares so a production with `assoc`, `comm` or `idem`, `functional`
  alone, and states its laws (`assoc`, `unit`, `idem`) as axioms of the symbol. Such a symbol builds
  values of its sort that the laws equate: a generator with laws, of which the semantics has no
  reading (its values of a user sort are the free terms over the constructors, and a function
  without clauses would be no generator at all). The detail names the symbol and the law axioms the
  text states of it (`isOpenGenerator`). A symbol of this shape that the text declares `functional`
  is read as an open generator (`ParamSig.raw`, a parameter symbol listed among its result sort's
  generators) where that sort is a constructor sort whose constructors take no argument and that
  no overloading symbol or subsort ends at (`openGenFault`, `Faithful.genWf`); otherwise it is
  refused, the detail naming the symbol and why: its result sort is no constructor sort, or its
  sort has a constructor with arguments, an overloading symbol or a subsort. -/
  | openGenerator
  /-- An `[assoc]`, `[comm]`, `[unit]` or `[idem]` axiom whose symbol is neither the concatenation
  of a collection of the definition (an `[idem]` axiom: of a set) nor a function of the definition
  or a parameter no hook implements and no open generator (`fnLawHead`, read into
  `Presentation.laws`): the law of another symbol, which no reading of the collections states
  (`Account.lawUnmatched`); or a function's law that is no equation between terms (`fnLawOf`) or
  whose sides are of no one sort of the definition (`fnLawSortedOf`). The detail names the symbol and the law. -/
  | lawAxiom
  /-- A sort declaration with an attribute that is neither its place, `hasDomainValues`, `token`
  (a token sort), nor `label` (a name, which says nothing of the sort's values): an attribute whose
  meaning for the sort the reader does not read (`sortAttrOK`). The detail names it. -/
  | sortAttribute
  /-- A hooked sort of the user's text whose hook is no collection's (`MAP.Map`, `SET.Set`,
  `LIST.List`) and that is no library sort's declaration (`placelessModule?`): a sort the hook
  says is interpreted, by a domain the reader does not give it (`syntax MyInt [hook(INT.Int)]`).
  The detail names the sort and the hook. -/
  | userHookedSort
  /-- A rewrite axiom's attribute that `attrVerdict` refuses at class `rule` (`ruleAttrFault?`): one
  that changes where or how the rule applies, or of no meaning any text states for a rule, or a name
  that is no key of the construct table's E2 rows; or `owise` beside `priority{}("n")` with n other
  than 200, two priorities of the rule (`ruleOwisePrioFault?`). The detail names the attribute, or
  both keys, and why. -/
  | ruleAttribute
  /-- A quantifier or a `\floor` of a term over a sort the text may leave unconfined (no sentence
  of the text states which elements it has), in a condition: its truth at given values differs
  between models of the text. The reader refuses one over every sort but Bool: which sorts a text confines
  is decided on the read definition (`Semantics.confined`), not while reading a sentence. The
  detail names the sort. -/
  | openExtent
  /-- A variable the left side does not bind, of a sort the text leaves unconfined, in a condition
  that also holds a bound variable, or in a closed condition neither witnessed nor refuted: the
  condition's truth at given values differs between models of the text. The detail names the
  variable and its sort. -/
  | openRequires
  /-- An `\exists` on an equation's right side in an alternative of an `\or`, at a sort that the
  test of a value given to `hoistExists` does not accept (`hoistEx`, ReadFns.lean). Moving the
  binder over the `\or`, `(∃x:s. φ) ∨ ψ = ∃x:s. (φ ∨ ψ)`, is an equality only where s has an
  element, which a value of s shows; without one, the alternative ranges over elements of s that
  no value names, and models of the text that differ there can give the function different values.
  The detail names the variable and its sort. Only `hoistExists` refuses with it, and no stage of
  the reader calls `hoistExists` (`clauseBody` calls none of the reading functions of ReadFns.lean):
  no account prints it. -/
  | existentialEquation
  /-- An open generator (a symbol the text declares total, lists among its result sort's
  generators and gives no constructor axiom) applied in a rule's left side or a clause's argument
  pattern (`Account.openGeneratorInPattern`): the pattern matches a value where the interpretation
  sends some arguments to it, which the text leaves open beyond the laws it writes. One row, two
  reasons, by the generator's result sort S (`Semantics.confined`): where S is not confined (it is
  recursive or reaches an unconfined sort), an element of S that is no value's may be the
  generator's image of other such elements, so the arguments that match depend on elements the
  text does not name; where S is confined, the arguments that match are values, the value's
  preimage under the interpretation's graph, which the semantics does not build. The detail names
  the symbol, S and the reason. A rule's left side is read through the cut (`ovlCut`), the
  application a fresh variable and its membership in the application a conjunct of `pre`: there
  the reason is printed where S is not confined and a variable of the arguments is held by no other
  part of the left side (`openCutRefusal`); the account's row remains for a clause's pattern and
  for an application whose arguments hold `#as`, which is not cut. -/
  | openGeneratorPattern
  /-- A range-map symbol binding a variable in a left side: the range's bounds are of KItem
  (`RangeMap:Range(KItem, KItem)`), the entry's value of KItem and the rest of RangeMap, all
  unconfined; and the entry symbol at a range that is empty, inverted or not of Ints is silent, so
  at an element that is no value's the text says nothing of it. The detail names the symbol. -/
  | rangeMapPattern
  /-- A law axiom of an open generator other than its associativity and idempotence sentences
  (`openLawRead`): a unit law, for which `ParamSig` has no field and `lawHooks` no form. The detail
  names the symbol and the laws. -/
  | openLaw
  /-- A rewrite axiom with a variable that a rule read from it would not hold, of a sort of which the
  reader exhibits no value applying no open generator (`exhibit?`): one bound by `\exists` in the
  left side and absent from its body (`existsAsVariable`), or one held by a disjunct of the left
  side, or of a `requires A #Or B` (`orSplit`, `requiresOrSplit`), and by nothing else of the rule
  read from another disjunct. The axiom holds for every element of the variable's sort, so where
  the sort has none it states nothing, while the rule without the variable would step; `Γ` entails
  neither an element of such a sort nor its emptiness. The text does entail an element: it is a
  theory of sorted matching logic, whose models give every sort a nonempty carrier
  (introduction-to-matching-logic.tex:705-707), and `Γ` does not state that. Where the sort has
  an exhibited value, `Γ` entails an element of it (`Faithful.inhabited_of_value`) and the rule is
  read. The detail names the variable, its sort and this reason. -/
  | unheldVariable
  /-- An equation whose right side holds, under applications, a connective of several elements or
  none at a point: `\or` (neither side `\bottom`) or `\exists` where the function is not `total`,
  or more than 8 alternatives, or where the patterns do not bind every variable of every
  alternative; `\top`; `\not`. A function's clause gives one value: `\or` of a function that is not
  total gives it every element of each side, more than one where they differ, which no clause
  states and the text does not exclude; `\top` and `\not` make the value a sort's extent or a
  complement in it. The detail names the connective. -/
  | manyValuedRightSide
  /-- A set variable (`@X`): a pattern of any set of elements, where the semantics reads patterns
  of at most one element. A function equation's two memberships in one are read as dropped
  (`ReadingNote.setVarInDropped`); every other place is refused, and for an equation the detail
  names the variable and why (`svinShape`; on the left side, under the function's application,
  `lhsSetVar?`), elsewhere the variable. -/
  | setVariable
  /-- A variable no left side binds, or an existential one, of a sort the text leaves unconfined,
  that the right side, the `ensures` or a `post` holds under no constructor and that no condition
  holds: under a function or hooked symbol (`c() => d(f(?Z:Int))`) the successor is a value through
  an element that is no value's; under a collection's symbols the arm that would decide it is not
  built. The detail names the variable and its sort. -/
  | openRight
  /-- A symbol a user file declares (a constructor, function or hooked symbol with the file's
  `Source`) under the name of a registry symbol (`regSymNames`: `symbol(_+Int_)`, kompile's
  `Lbl'UndsPlus'Int'Unds'`). A library module's declaration carries the library's source, so this
  one is no imported module's. Names are numbered registry first, so the declaration would read as
  the registry symbol, with its arity, sorts and interpretation, which are not the declaration's;
  read as a symbol of its own it would carry a registry symbol's name, which the numbered symbols'
  names being apart excludes. The detail is the name. -/
  | registrySymbolName
  /-- A function equation's attribute that `attrVerdict` refuses at class `equation`
  (`eqnAttrFault?`): one whose meaning for the equation no text states, so that reading the equation
  without it states no more than the text cannot be shown, or a name that is no key of the construct
  table's E2 rows. The detail names the attribute and why. -/
  | equationAttribute
  /-- An equation of the form the reader reads as a function's (`rawEqn?`) whose left side is
  headed by a constructor (`eqnHeadFault?`): `a(X) = b(X)`, `a(X) = a(0)`, `a(X) = f(X)`. The
  semantics' values of a constructor's sort are the free terms over the constructors, as the
  text's own constructor axioms state (two constructors build distinct values, a constructor is
  injective). With another constructor heading the right side the equation and the distinctness
  axiom have no common model; with the same constructor, injectivity equates the arguments at every
  element, so the sort's values that differ there are one element, which no free term model is;
  with a function or a variable on the right side the text can have a model, in which the
  constructor's application is an element some other term also denotes, while the semantics reads
  it as a value apart from every other. No part of the semantics states the equation, and it is no
  clause of a function. The detail names the constructor and what heads the right side. -/
  | constructorEquation
  /-- An equation whose left side is headed by an open generator (a symbol of a user's file declared
  neither function nor constructor, its declaration refused `openGenerator`): a law between terms the
  generator builds, which no part of the semantics states and which is no clause of a function. The
  detail names the symbol. -/
  | openGeneratorEquation
  /-- An axiom `∃B. (f(x̄) = B ∧ E)`, a conjunct of its body equating an application to the variable
  it binds (`existentialAxiom?`; K's `?B` on a function's equation, quantified at the top of the
  sentence): f(x̄) is some element satisfying E, which the text does not name. Where several
  elements satisfy E the text has a model for each choice and entails no value; where none does it
  has no model. A function's clause states one value and a parameter's value is unconstrained, so
  no part of the semantics states a function the text constrains without defining. The detail
  names the symbol and the variable. -/
  | existentialAxiom
  /-- A constructor of the text whose result sort is no constructor sort (`Faithful.consSorts`): a
  library sort whose values are no constructor terms (Int, Map, MInt: literals, collections, or no
  generator the library has), a sort of the text hooked to a library carrier, a collection sort of
  the text, or a token sort. Such a sort's values are given otherwise (the builtin prose, the
  collection's representation, the tokens), and no sentence of the text relates the constructor's
  applications to them: whether `k(1, 2)` is one of those values or an element apart from all of
  them differs between models of the text, while the semantics' values of a sort are of one kind.
  `Faithful.genWf` (its first conjunct) excludes such a definition; this is its message. The detail
  names the constructor, the sort and which of these it is. -/
  | ctorResultSort
  /-- An equation (`eqnHeadFault?`) whose left side is headed by a hooked symbol of the text whose
  hook a registry hook interprets, or that is a collection sort's unit, element or concatenation
  symbol, or that has no hook attribute, or, written in a user's file, by a symbol of the registry.
  (A hooked symbol of the text whose hook no registry hook interprets and that is no collection
  symbol is read as a function with its equations, `hookFnSym`.) The sentence is a premise about
  an interpreted symbol at every element of its sorts. `Γ` states such a symbol's graph at values
  only, so it does not entail the premise (a model may hold elements of an argument sort that are
  no value's, where the symbol is unconstrained), and the semantics has no place for the premise or
  for the obligation that the graph satisfies it. The detail names the symbol and which it is. -/
  | hookEquation
  /-- A rule or equation whose read `requires` or `ensures` holds an equality `_==K_` or `_==Int_`
  that the reader writes for what the text states (an equation's strict conjunction, `conjTerms`;
  `t ∧ u` on a rule's right side, `sideConds`), in a text that declares that hooked
  symbol without its `functional` axiom or without the sentence `((K1 σ K2) = true) = (K1 = K2)`
  over two distinct variables of its sort (`hookEqSentence`). The reading's sentence is the text's
  only with both: the first makes `K1 σ K2` one element, the second makes `true` its value exactly
  where K1 and K2 are one; a text that declares the symbol without them can give it `true` at two
  distinct elements that are no values. The detail names the symbol and the missing sentence. -/
  | hookEqualityUnstated
  /-- An equation without a user source (kompile's) of a symbol of the registry, of a sort
  predicate or of a projection that `d` does not read as a function's clause and that is none of
  the three classes `Account.genEqClassOK` accounts for (a sort predicate's equation that is its
  `Semantics.sortPreds` clause, an `[owise]` one with its exclusion; a sort's projection equation
  or selector-domain axiom where `d` does not number the projection; a constructor argument's
  projection equation, the projection no symbol of `d`), and no sentence of `kconfigModule`'s text
  where `d` imports it (`Account.kconfigOwnSentence`). The sentence says more or other of a symbol
  than `Γ` states; the detail names the symbol and the shape. A sort predicate's or a sort's
  projection's is refused by the reader (`coreOf`, `predEqnFaults`), the others by the account
  (`Account.unconsumed`). -/
  | generatedEquation
  /-- An attribute of a symbol declaration, of an axiom carrying `simplification`, of a claim or of
  the module that no kompiled text carries there: a key the frontend erases, a key whose K text
  the frontend refuses, or a key K admits at no sentence of that class (`attrVerdict`, the construct
  table's E2 rows). Only a KORE text written by hand carries it, and no text gives it a meaning
  there. The detail names the attribute and the class. -/
  | attrOutsideE2
  /-- A form of KORE pattern that no text kompile 7.1.337 writes: `\mu`, `\nu`, `\next`, `\iff`,
  `\left-assoc`, `\right-assoc`, or a string pattern (a string literal outside `\dv`)
  (`isUnkompiledForm`), as a term (`term`) or at an axiom's top (`classifyAxiom`). The semantics
  reads none of them: a fixpoint, a step, an equivalence, an application form the KORE syntax
  abbreviates, or a pattern of no sort. The detail names the form. -/
  | unkompiledForm
  /-- An attribute of a symbol or hooked-symbol declaration whose name is no key of the construct
  table's E2 rows (`AttrKeyE2`): no text gives it a meaning at a symbol, so that reading the
  declaration with it dropped states no more than the text cannot be shown (`attrFault?`). The
  detail names the attribute. -/
  | symbolAttrUnkeyed
  deriving Repr, DecidableEq, Inhabited

/-- The reason the reader refuses with, for a key `attrVerdict` refuses. -/
def AttrRefusalE2.reason : AttrRefusalE2 → RefusalReason
  | .ruleAttribute => .ruleAttribute
  | .equationAttribute => .equationAttribute
  | .sortAttribute => .sortAttribute
  | .openGenerator => .openGenerator
  | .outsideE2 => .attrOutsideE2
  | .symbolAttribute => .symbolAttrUnkeyed

/-- The verdict on an attribute whose head is spelled `n` at a sentence of class `c`: its key's
(`attrVerdict`), and for a name that spells no key of `AttrKeyE2`, refused with `r`. -/
def attrVerdictOf (c : AttrClassE2) (r : AttrRefusalE2) (n : String) : AttrVerdict :=
  match AttrKeyE2.ofName? n with
  | some k => attrVerdict c k
  | none => .refused r "the name is no attribute key of E2's rows (K 7.1.337 admits no key so spelled at this sentence): no text gives it a meaning here, so that reading the sentence with it dropped states no more than the text cannot be shown"

/-- The first attribute of `as` that `attrVerdictOf c r` refuses, as the reason it gives and the
attribute's name with why (`r` for a name that is no key). -/
def attrFault? (c : AttrClassE2) (r : AttrRefusalE2) (as : List Kore.AppPattern) : Option (RefusalReason × String) :=
  as.findSome? fun ap =>
    let n := ap.head.ident.name
    match attrVerdictOf c r n with
    | .refused r' w => some (r'.reason, s!"{n}: {w}")
    | _ => none

/-- Whether `as` holds an attribute of key `k`. -/
def hasKey (as : List Kore.AppPattern) (k : AttrKeyE2) : Bool := hasAttr as k.kore

/-- The string argument of `as`'s attribute of key `k`. -/
def keyStr? (as : List Kore.AppPattern) (k : AttrKeyE2) : Option String := attrStr? as k.kore


/-- Why the semantics does not read a sentence. -/
inductive InertReason where
  /-- An import: the user module holds the sentences of the modules it imports (kompile writes
  them into it), and K's prelude, which it imports, is read as a whole. -/
  | import
  /-- A claim: a statement to prove, not an axiom of the theory. -/
  | claim
  /-- A `[simplification]` axiom other than a `\rewrites` axiom: a lemma, which K's semantics
  requires to follow from the definition's other sentences; it defines nothing. (A `\rewrites`
  axiom carrying the key states a step and is refused, `RefusalReason.ruleAttribute`.) -/
  | simplification
  /-- `\not(\and(c(x̄), d(ȳ)))` [constructor]: two constructors build distinct values, as KCore's
  values, the free terms over the constructors, do. -/
  | distinctCtors
  /-- `\implies(\and(c(x̄), c(ȳ)), c(x̄ ∧ ȳ))` [constructor]: a constructor is injective, as on
  KCore's values. -/
  | injectivity
  /-- `\or(…)` [constructor] of a sort other than KItem: the sort's values are built by its
  constructors and injections, as KCore's values of the sort are. -/
  | noJunk
  /-- An `[assoc]`, `[comm]` or `[unit]` axiom of a collection's concatenation: a law KCore's
  collection values satisfy, a map's, set's or list's by their representation, a range map's at its
  values through `_RangeMap_`'s hook (`rmConcat_assoc`, `rmConcat_unit`: the hook gives a value
  only where no ranges overlap, and associativity holds as an equality of patterns, both sides
  without a value of the hook or one value). Where ranges overlap the text states no value
  (`silentTable`) and Γ states the interpretation's: there the law is a condition on the
  interpretation, met by one that gives no value there (`HookParams.none`, `HookParams.lib`).
  Classified by the sentence's form; the account refuses one whose symbol is not a collection's
  concatenation (`RefusalReason.lawAxiom`). -/
  | collectionLaw
  /-- `\exists(v, \equals(v, f{S…}(…)))` [functional] of a sort-parametric symbol: the totality of
  `ite{S}`, which KCore's `kIte` is, of a symbol of the library's parametric sorts (`MInt{W}`), or
  of a user's sort-parametric function declared `total`, at every instance: each instance the
  definition has (`instName`) is total, a function with `Fn.total` or a parameter with
  `ParamPres.total`. -/
  | parametricFunctional
  /-- A rewrite axiom whose left side is empty (`vacuous`: `\bottom` under applications, conjunctions
  and `\exists`, or a disjunction of such): `C[⊥] = ⊥`, and `⊥ → •R` holds in every model. -/
  | vacuousLeft
  deriving Repr, DecidableEq, Inhabited

/-- Why a sentence that states something is deliberately not part of the reading. -/
inductive UnreadReason where
  /-- The subsort of a cell into its cell collection's sort (`XCell < XCellMap`, a set's or a
  list's), its subsort axiom, and the collection sort's no-junk axiom, which says every
  collection is an injected cell. Read as a subsort it gives a second value, `inj(cell)`, for what
  the collection denotes as a one-entry collection, and the no-junk axiom is false of the empty
  collection and of two entries: the collection sort holds collections and nothing else. A read
  sentence that applies the injection is refused (`cellCollectionInjection`). -/
  | cellCollectionInjection
  /-- A macro or alias symbol: its applications stand for the macro's expansion, which kompile has
  done. It is part of the reading only through an application, which is refused (`macroSymbol`,
  at the applying sentence). -/
  | macroUnused
  /-- A sort-parametric symbol declared in a user's file (`syntax {S} S ::= pair(S, S)`, KORE's
  `symbol pair{S}(S, S) : S`), or K-REFLECTION's hooked `#unparseKORE{S}` (`isReflectionSentence`):
  a symbol at each sort. The declaration is part of the reading only through the instances a read
  sentence applies: each instance at sorts of the definition is a symbol of the definition's own
  (`instName`), a function with the text's equations of that instance as its clauses, or a parameter
  symbol when the text states none at it (total when the declaration is); an application of a
  hooked or constructor instance, or at sorts the definition does not have, is refused
  (`parametricSymbol`). -/
  | parametricUnused
  /-- The `[idem]` axiom of a set's concatenation, `\equals(_Set_(K, K), K)` (the library's `Set`,
  a cell set's). KCore reads `_Set_` as the union of two sets with no member in common, undefined
  where they share one, as `_Map_` is undefined where two maps share a key: K's own sources state
  that reading (domains.md:704-709 calls the sets nilpotent, a concatenation with a common element
  `#False`, and names `|Set` for an element that may be present; `|Set` is defined as `S1 (S2 -Set S1)`, a concatenation of disjoint sets; the `#Ceil`
  lemma of SET-KORE-SYMBOLIC says `S SetItem(E)` is defined exactly when E is not in S). The
  idempotence axiom contradicts them (it makes `_Set_(K, K)` defined and equal to K for every
  set) and is the one statement of the text that does not hold of the reading; under it
  `SetItem(X) REST` would also match a set S with REST = S, a match that removes nothing. The
  two sentences cannot both hold of a set with an element, and the reading is a choice between
  them. The collection axioms of `Γ` (`ΓColls`) state what K's text says of the sorts: for Set,
  a collection of unique items whose concatenation on a common element is `#False`
  (domains.md:704-705); for Map, an associative, commutative map with one value per key whose
  concatenation on a common key is `#False` (domains.md:205-207, 223-229). They are written from
  those sentences, not read from the text's axioms. This axiom is the one sentence of a text that
  `Γ` denies: `Γ` with it has no model under any interpretation of the hooks, since the graph of
  `_Set_` states `_Set_(S, S) = ⊥` at a set S with a member, a point that is not silent. Under the
  definedness of its left side, `⌈_Set_(K, K)⌉ → _Set_(K, K) = K`, it holds at every set value. -/
  | setIdempotence
  /-- The distinctness `¬(f(X̄) ∧ g(Ȳ))` of two symbols of one sort whose overload closures meet
  (`Semantics.ovlClosure`: one overloads the other, or both overload a third): wherever an overload
  applies to both the two are equal, so the axiom holds only where the overloaded symbol's argument
  sorts have no element. Two sentences of the text are in conflict here: this no-confusion axiom
  and the overload axiom `g(inj(x̄)) = inj(h(x̄))`, which identifies the two applications at the
  smaller symbol's arguments, as user_manual.md:387-390 says in words (a term of the one production
  is a restriction of one of the other). Where those argument sorts have elements the two have no
  common model, and the reading is a choice between them: the overload axiom is kept, and of this
  axiom what remains beside it, the distinctness at uncovered arguments only
  (`KoreAML.Cons.distUncItem`). Stated by the text and not read (`Parse.overloadConfusions`). -/
  | overloadConfusion
  /-- The sort predicate `isX` of a registry sort X to which the registry gives no predicate
  symbol (`predOf X = none`) and that is itself no registry symbol (`isNoPredName`). K and KItem
  have no `predOf` symbol but `isK` and `isKItem` are registry symbols, and every other registry
  sort but MInt has a predicate, so the one such name is `isMInt`. Its declaration, its
  `functional` axiom and its equations are stated by the text and not read: the theory has no
  such symbol (`Semantics.sortPreds` writes `isX` only for a sort with a predicate), so it says
  nothing of `isX(t)`, less than the text (`isNoPredSentence`). -/
  | noSortPredicate
  deriving Repr, DecidableEq, Inhabited

/-- How a sentence is read when it is not read as it is written. -/
inductive ReadingNote where
  /-- A sentence of K's K-REFLECTION module (`domains.md`), recognised by its content
  (`isReflectionSentence`), read as a sentence of the definition's own: the library holds no
  K-REFLECTION. Its hooked symbols (`#sort`, `#fresh`, `getsymbol`, `#getenv`,
  `#kompiledDirectory`, `#argv`, `#configuration`) are read as the definition's parameter symbols, as
  a user's hooked symbols are: the text declares each a `function` (at most one value for each
  argument list) and states nothing else of it, no hook of the semantics interprets it, and every
  theorem holds for every interpretation. K's documentation (`domains.md`) gives `#configuration` a
  meaning that depends on the state, the configuration the term is evaluated in; a parameter
  symbol's interpretation is one value fixed for every configuration, so no interpretation here is
  that meaning, and a theorem about a rule applying it holds of each fixed value, not of the
  documented one. Under `HookParams.none` it has no value, and a rule whose right side applies it
  gives no step. Its constructor `#noParse` is a constructor of K-IO's `IOError` beside the
  library's. The sort-parametric `#unparseKORE` (`UnreadReason.parametricUnused`) is not read. -/
  | reflectionAsOwn
  /-- A rewrite rule of K's stream modules (`STDIN-STREAM`, `STDOUT-STREAM` of `domains.md`, its
  `label` naming the module, `isStreamRule`): kompile instantiates the module's rules on the
  definition's own cells declared `stream="stdin"` or `stream="stdout"` and writes them into the
  user module as rewrite axioms of the definition's top cell, with the builtin file as `Source`.
  The text states a rule of the definition; it is read as a user's rule is, the K-IO hooks it applies
  (`#getc`, `#write`) the library's parameter symbols. -/
  | streamRule
  /-- A rewrite rule `\rewrites(lhs ∧ req, rhs ∧ ens)`, read in `Γ` with two premises the text does
  not write (`Faithful.prioRuleK`): no rule of a smaller priority applies, and `⌈rhs ∧ ens⌉`, the right
  side has an element. The text's axiom entails the read one (each premise only narrows where it
  speaks), for every interpretation of the points the text leaves open, so `Γ` states no more than the
  text. Where a rule matches with its `requires` true and its right side is empty (an `/Int` by a
  matched variable that is zero, an `ensures` that is not `true`), the text's axiom states that the
  configuration has a successor in the empty set, which no model gives a configuration's element; the
  read axiom states nothing there, and `Step` gives that configuration no successor by the rule. Every
  rule is read so; the account prints their number (`rulesRightDefined`). No sentence is classified
  so (`classify`): the premise is `Γ`'s for every rule, hand-built semantics' as well, not a reading
  of one sentence. -/
  | ruleRightDefined
  /-- The selector-domain axiom of a sort X's projection (`projectionDomain?`),
  `\implies{R}(\top, \equals{R,R}(\ceil{X,R}(project:X(K)), \exists{R}(V:X, \equals{K,R}(K,
  kseq(inj{X,KItem}(V), dotk)))))`: `project:X(K)` has a value exactly where K is an injected X.
  Where the projection is a function of the definition (a projection with an equation that a sentence
  applies, `Presentation.libProjs`), the axiom is read as one more clause of it,
  `project:X(K) = project:X(K) ensures false`, of priority 200, its pattern a variable K of sort K.
  The projection's equation must then be its only one, `project:X(kseq(inj{X,KItem}(V), dotk)) = V`
  (`kseq(V, dotk)` for KItem, `V` for K: `selectorPat`) without `requires` (otherwise the text is refused, `projectionDomainShape`). Where the equation
  applies it decides, with the value V, where the axiom says the projection is defined; elsewhere
  the read clause decides and its `ensures` is not `true`, so the projection has no value there
  (`Eval.ensFails`) under every interpretation, where the axiom says it has none. In `Γ` the read
  clause's equation is `¬ ∃V. X0 ∈ kseq(inj(V), dotk) ∧ X0 ∈ K → project:X(X0) = r ∧ ⌈false =
  true⌉`, whose right side is empty; with the projection's equation it states what the axiom
  states. The right side r is never read: it has sort X, as the clause's equation needs. Where the
  projection is no function of the definition (no sentence applies it), no clause is read: the axiom
  is one `emit` writes from the signature with the projection's equation, as that equation is
  (`Account.consumed`). -/
  | projectionDomainAsClause
  /-- A rewrite axiom whose left side holds `\or` under applications and conjunctions, read as one
  rule per disjunct (`splitRule`): application is pointwise (`C[φ ∨ ψ] = C[φ] ∨ C[ψ]`), and
  `(φ ∨ ψ) → •R` is `(φ → •R) ∧ (ψ → •R)`. Each rule has the axiom's priority, `requires`, right side
  and `ensures`; a variable of them it does not bind is an open variable of that rule
  (`openRefusal`). An empty disjunct
  (`vacuous`) is dropped: `φ ∨ ⊥ = φ`. -/
  | orSplit
  /-- `\top{S}()` under applications and conjunctions of a rule's left side, read as a variable of
  the rule of sort S that no other part of the axiom holds (`lhsBind`): `C[⊤] = ∃z. C[z]`, and
  `(∃z. φ) → •R` is `∀z. (φ → •R)` for z not free in R. -/
  | topAsVariable
  /-- `\exists{_}(Y, φ)` under applications and conjunctions of a rule's left side, read as φ with Y
  renamed to a variable of the rule that no other part of the axiom holds (`lhsBind`):
  `C[∃y. φ] = ∃y. C[φ]` for y not free in C, and `(∃y. φ) → •R` is `∀y. (φ → •R)` for y not free
  in R. -/
  | existsAsVariable
  /-- A right side holding, under applications, `t ∧ \equals{SortBool{},S}(B, true)` (`hoist`): for
  a predicate P, `σ(…, φ ∧ P, …) = σ(…, φ, …) ∧ P`, so it is t with the `ensures` B, an equality in
  every model. A rule's right side holding `t ∧ u` of two terms is `andTermsWeaker`. An equation's
  `t ∧ u` of two terms is refused (`clauseBody`): it is `t ∩ u`, which `t` with the `ensures`
  `t ==K u` is not where t or u has two elements. Several `ensures` of an equation are one strict
  conjunction (`conjTerms`); of a rule the first is its `ensures` and each other a conjunct `B = true`
  of `post` (`andAtBool`). The `ensures` written are the text's under the `functional` axiom and the sentence
  `((K1 σ K2) = true) = (K1 = K2)` of each hooked equality σ written (`_==Int_`, `_==K_`), which a
  text declaring σ must hold (`hookEqualityUnstated`). -/
  | andAsEnsures
  /-- A rule's right side holding, under applications, `t ∧ u` of two terms (`hoist`), read as t
  with the `ensures` `t ==K u` (`==Int` at Int). The text's sentence entails the rule's sentence in
  every model of the signature: the `ensures` is an equality, which is all of its sort or nothing,
  so where it holds `C[t ∧ u] ⊆ C[t]` lies inside the read right side, and next is monotone. The
  two right sides are not equal: where t and u have a common element and one of them has two
  elements, the read right side holds `C[z]` for an element z of t that is not one of u, or is
  empty where the text's is not. -/
  | andTermsWeaker
  /-- A right side holding `\bottom` under applications and conjunctions (`hoist`): `σ(…, ⊥, …) = ⊥`,
  so the right side is empty, read as the `ensures` false. The rule (the equation) still applies
  where its left side matches and its `requires` holds, so it blocks the larger priorities, and it
  gives no successor (no value). In the right side's place: for a rule its left side without
  `#as` (a value at every match, applying nothing the left side does not), for an equation a
  value of the result sort that applies no function (`eqnPlaceholder`), else the function's call
  at the clause's arguments; with the `ensures` false neither gives a successor or a value. -/
  | bottomAsEnsures
  /-- `t ∨ ⊥` (or `⊥ ∨ t`) in a right side, read as t: `φ ∨ ⊥ = φ`. -/
  | orBottom
  /-- A `requires` or `ensures` `\equals{SortBool{},S}(B, true)` whose B is a predicate at sort Bool
  (`isPred`: `\ceil`, `\floor`, `\equals`, `\in`, `\top`, `\bottom`, and connectives and
  quantifiers of predicates): B is `\top{SortBool{}}` or `\bottom{SortBool{}}`, and neither is
  `true`: the first holds `false`, which is apart from `true`, the second holds nothing. The
  condition never holds; it is read as the literal `false`. -/
  | predicateAtBool
  /-- A `requires` or `ensures` `\equals{SortBool{},S}(\and{SortBool{}}(B₁, …, Bₙ), true)` of terms:
  `\and{SortBool{}}` is an intersection, `B₁ ∩ … ∩ Bₙ = {true}`. The conjunction `⌈B₁ = true⌉ ∧ … ∧
  ⌈Bₙ = true⌉` entails it with no premise (each Bᵢ is `{true}`, and so is their intersection) and is
  it where each Bᵢ has at most one element; where a Bᵢ has `true` and a second element the
  intersection can be `{true}` and the conjunction not.
  On a rule the conjunction is read conjunct by conjunct, with no hooked symbol
  (`ruleCondTermsCnj`): of the `requires`, B₁ is `req` and each other Bᵢ the conjunct `Bᵢ = true` of
  `pre`; of the right side's conditions (the `ensures`' conjuncts, then those `hoist` lifts), the
  first is `ens` and each other the conjunct `B = true` of `post`. So the read left side (the
  `requires` and `pre`) is the text's or inside it, and so is the read right side (the `ensures`
  and `post`); both are the text's where each Bᵢ has at most one element.
  An equation reads the conjunction as the strict conjunction of the Bᵢ (`conjTerms`), the K
  sequence of the Bᵢ `_==K_` that of as many `true`, which is `⌈B₁ = true⌉ ∧ … ∧ ⌈Bₙ = true⌉` under
  `_==K_`'s `functional` axiom and its sentence `((K1 ==K K2) = true) = (K1 = K2)`, which a text
  declaring `_==K_` must hold (`hookEqualityUnstated`). An equation's `ensures`, and its `requires`
  under the negation of an `[owise]` or larger-priority equation, ask the converse of the
  entailment too, so an equation reads the conjunction only where every Bᵢ is `singleValued`
  (`eqnCondTerm`). -/
  | andAtBool
  /-- A `requires` `\equals{SortBool{},S}(\and{SortBool{}}(\or{SortBool{}}(A₁, …, Aₙ), G), true)`,
  kompile's `requires A₁ #Or … #Or Aₙ` with G a Bool variable that occurs nowhere else
  (`reqOrSplit?`), read as n rules of the axiom's priority, left side, right side and `ensures`, the
  i-th with the `requires` Aᵢ. Each Aᵢ is a term (at most one element), so `(A₁ ∪ … ∪ Aₙ) ∩ {g}` is
  `{true}` exactly when g is `true` and some Aᵢ is `true`: the axiom's instance at g := `true` (an
  element of Bool, `ΓDomains`) has the premise `⌈A₁ = true⌉ ∨ … ∨ ⌈Aₙ = true⌉`, and every other
  instance a false one. The conjunction of the n rules' sentences is that instance, and one of them
  applies exactly where its premise holds, so a rule of larger priority is blocked where the axiom
  blocks it. It is not `A₁ orBool … orBool Aₙ`, which has no value where one Aᵢ is `true` and another
  has none. A variable one Aᵢ holds and nothing else of the rule does is a variable of the other
  rules' that they do not hold (`unheldVariable`). -/
  | requiresOrSplit
  /-- A function equation whose first two arguments are memberships in one set variable that stands
  nowhere else in the axiom, as kompile writes `rule f(@S, @S, …) => r`:
  `\implies(\and(Q, \and(\in(X₀, @S), \and(\in(X₁, @S), T))), \equals(f(X₀, X₁, …), r ∧ E))`,
  read as the clause whose first two patterns are two distinct variables (`svinRead?`). As an
  axiom the sentence holds for every set `S` inside the arguments' sort; with `S` free in none of Q,
  T, r and E it holds at a point exactly where the sentence with the two memberships dropped holds,
  since the set `{X₀, X₁}` holds both elements (`KCore.setvar_in_drop`, stated on the translated
  sentence). So `f(a, b) = r` for all a and b, equal or not. Beside an `[owise]` equation of the
  function, its disjunct for this one is matched in one of two forms (`svinExcl?`), one of them
  read with a narrower premise (`owiseDisjunctNarrower`). Every other sentence holding a set
  variable outside `[simplification]` is refused (`setVariable`, the detail saying why). -/
  | setVarInDropped
  /-- A rule whose left side holds a map key applying a function of the definition (`keyCut`), read
  with a fresh variable Key in the key's place and the membership `Key ∈ f(t̄)` a conjunct of its
  `pre`, its `requires` and right side as written. The read rule is the text's in every
  interpretation, with no premise: the text's left side is `∃Key. C[Key] ∧ Key ∈ f(t̄)` (the block of
  `keyCut` says why). No sentence is classified so (`classify` reads a sentence alone, and which
  symbols are the definition's functions it does not know): the account lists the rules read so
  (`keysAsMember`). -/
  | keyFunctionAsMember
  /-- A function equation of priority p (`priority{}("p")`, 50 without the attribute) read in `Γ`
  with the premise that no executable clause of the function of a smaller priority applies
  (`Faithful.prioEquation`, `lowerClauses`); the text writes the equation without that premise.
  The equation of the smallest priority has no such clause and is read as written; each other one
  is read with the premise.
  The text's equation entails the read one (the premise only narrows where it speaks), for every
  interpretation, so `Γ` states no more than the text. The entailment is a weakening, and it would
  hold as well if another of the equations were the one narrowed: it selects no value. Where a
  clause of a smaller priority also applies and gives another value, the text states both values
  there and the read equations the smaller priority's only. Where those values are distinct values,
  the equations as written with `ΓDomains` (each value one element, distinct values distinct, the
  hooks' graphs) have no model: there, that `Γ` states no more than them is true and is evidence
  for no value. Which equation speaks there is the meaning of the attribute, as K's user manual
  states it ("`owise` and `priority` attributes"): "Rules are tried in increasing order of
  priority", and "a rule with no attributes indicating its priority is assigned the priority 50".
  The order is held in `Faithful.lowerClauses` and in `Eval.clause`'s `hprio` (`cl'.prio < cl.prio`),
  the 50 in `eqnPrio`: definitions of the attribute's meaning, not statements about the text.
  No sentence is classified so: the account prints the number of equations read with the premise
  (`equationsUnderPriority`). -/
  | equationPriority
  /-- An `[owise]` equation, whose premise in the text negates one disjunct `∃ȳᵢ. ⌈reqᵢ⌉ ∧ X̄ ∈ p̄ᵢ`
  for each other executable equation of the function, read as a clause of priority 200 (`eqnPrio`),
  whose premise in `Γ` negates the executable clauses of a smaller priority (`prioEquation`). The two
  premises are one by what the reader checks (`fnFrom`, `fnPairs`, `excludes`): each disjunct is
  matched to the equation it excludes up to the names of its variables, the disjuncts are as many as
  the executable equations, and every other equation has a priority below 200. They are not one
  where a disjunct excludes an equation read through `setVarInDropped` and holds one element
  variable at both of its first two arguments (`svinExcl?`): there the text's premise is the wider
  and `Γ`'s the narrower (`owiseDisjunctNarrower`). A second `[owise]`
  equation is a clause of priority 200 beside the first, its exclusion matched the same way. No
  sentence is classified so: the account prints the number of `[owise]` equations read
  (`owiseEquations`). -/
  | owiseAsPriority
  /-- An `[owise]` equation one of whose exclusion disjuncts is narrower than the equation it
  excludes as read: the excluded equation's two memberships in one set variable are read as dropped
  (`setVarInDropped`), so it applies at every pair of its first two arguments, and the disjunct,
  written with one element variable at both, holds only where the two are equal
  (`KCore.owise_diag_svin`). `Γ` negates the equation as read (`Faithful.prioEquation`), so its
  premise for the `[owise]` clause is the text's narrowed: the text's sentence entails `Γ`'s
  (`KCore.owise_disjunct_narrower`, stated on the translated sentences with the disjunct as read,
  `svinExcl?`), and `Γ` leaves out what the text's states where the two arguments differ. There the
  text states the `[owise]` equation's value and the excluded equation's; where those differ the
  text has no model, which `Γ` does not refute. No sentence is classified so (`classify` reads a
  sentence alone, and the `[owise]` sentence alone is also the one written beside an equation whose
  disjunct is exact): the account lists the `[owise]` equations read so (`owiseNarrowed`). -/
  | owiseDisjunctNarrower
  /-- A rewrite axiom whose right side is an application `σ{S}(φ)` of an alias of K's prelude
  (`preludeAliases`; kompile writes `weakAlwaysFinally{S}(\and(rhs, ens))` for a rule of a module
  carrying all-path, `weakExistsFinally` for one-path), read as the axiom with φ in its place
  (`unaliasRule`). The text defines the alias by its own alias sentence, and the reading is made
  only where every alias sentence of that name in the text is `σ{A}(X:A) := X:A` (`aliasIsIdentity`,
  checked on the sentence; `identityAliases`): an alias application denotes its body with the
  argument for the parameter, here the argument itself, so the two axioms denote the same at every
  interpretation. The right side otherwise headed by such an alias (another body, more than one
  argument or sort) is refused `aliasApplication`. An alias applied inside a term is refused
  `aliasApplication` (`Names.symE`). The same under the right side's `\exists` binders: the alias
  application is then the binders' body, and denotes its argument there as at the root. -/
  | identityAlias
  /-- A rewrite axiom `\rewrites(lhs ∧ req, ∃Z:s. B)` one of whose right-side binders has a name
  that the left side or the `requires` holds, at any sort (`exRenamed`), read with that binder and
  the occurrences it binds renamed to a name the axiom does not hold (`exApart`, `rhsApart`). A
  variable of the text is a name and a sort, a binder's scope is its body, and the left side and
  the `requires` are outside every binder of the right side: the Z they hold is free in the axiom
  and is another variable than the Z the binder binds. The reader numbers a rule's variables by
  name, so it reads the axiom's α-variant `\rewrites(lhs ∧ req, ∃Z':s. B[Z'/Z])`, Z' fresh, which
  denotes what the text's axiom denotes in every interpretation; the rule's presentation carries
  the name Z' (`RulePres.names`), so the sentence written back is the α-variant. The renamed binder
  is then a binder as any other: an existential variable of the rule (`Rule.exs`), or one that binds
  nothing (`existsDropped`). -/
  | existsRenamedApart
  /-- A rewrite axiom `\rewrites(lhs ∧ req, ∃Z:s. B)` one of whose right-side binders binds nothing
  in what is read of its body (`exKept`): no variable of the binder's name and sort is free in the
  right side or the `ensures` (Z absent, Z there at another sort only, which is another variable and
  free in the axiom, or Z bound again by a binder inside this one), or the right side is empty
  (`bottomAsEnsures`) and the `ensures` does not hold it. Read without that binder: it is in neither
  the rule's existential variables nor its variables, at every sort s. For Z:s not free in B,
  `∃Z:s. B` is B where s has an element and is empty where s has none; so the read sentence
  `lhs ∧ req → •B` is the text's where the binder's sort has an element, and is entailed by the
  text where it has none: there the text's right side is empty, next of the empty pattern is empty,
  and the text states that the left side has no instance, of which the read sentence, holding for
  want of an instance, is a consequence. `Γ` states no more than the text. -/
  | existsDropped
  /-- The `functional` axiom, the injectivity axiom and the distinctness axioms of an overloading
  symbol f one of whose overloads is a function g of the definition (a function-overloaded symbol,
  `Semantics.fnOvlSyms`), read at the arguments no overload of f covers
  (`KoreAML.Cons.funUncItem`, `injUncItem`, `distUncItem`). At covered arguments the overload
  equation `f(inj x̄) = inj(g(x̄))` gives the application g's value, so there the three sentences
  hold in a model only if g is total, injective and apart from the other generators of f's sort;
  where g is not, the text has no model. What is read is each sentence restricted to fewer
  arguments, which the sentence entails; whether g is so is not decided
  (`Parse.overloadFunctions`). -/
  | overloadFunction
  /-- A sort X of the definition that KItem's no-junk axiom (`\or{SortKItem{}}(…)`, `scanOr`) does
  not list, read below KItem all the same; where the text states no `subsort{X, KItem}` axiom
  either (a token sort whose name begins with `#`, `syntax #Tok [token]`), the reading adds the
  subsort X < KItem. Every sort of the definition is below KItem (`Semantics.sortsBelowKItem`,
  `Semantics.subsorts`), so `inj{X, KItem}` is one of KItem's generators (`Semantics.gens`) and
  `Γ`'s no-junk item of KItem lists it. K's text states that every sort is a KItem
  (user_manual.md:504, 515; kast.md:363 `syntax {Sort} KItem ::= Sort`), and the text itself applies
  `inj{X, KItem}` (in the equations of the sort predicate `isX`), which denotes elements of KItem
  only with X below KItem. The text's sentence entails `Γ`'s item (an item over more generators is
  a consequence, `Faithful.noJunkItem_of_subset`), not conversely: where X has an element (a token's
  domain value), `inj{X, KItem}` of it is an element of KItem (Cons-Fun) apart from the image of
  every other generator (Cons-Dist), and the text's sentence says it is in one of them, so the
  text's sentence with `Γ` has no model. The reading keeps the subsort that the text's application
  of `inj{X, KItem}` needs and leaves out the sentence's exclusion. No sentence is classified so
  (`classify` reads a sentence alone, and which sorts the definition has it does not know): the
  account lists the sentences and the sorts (`tokKItemOmitted`). -/
  | tokKItem
  deriving Repr, DecidableEq, Inhabited

/-- A sentence of the user module: read, read in another form than written (`readAs`, with the
note saying how), inert, deliberately not read, or refused. -/
inductive SentenceClass where
  | read
  | readAs (r : ReadingNote)
  | inert (r : InertReason)
  | unread (r : UnreadReason)
  | refused (r : RefusalReason)
  deriving Repr, DecidableEq, Inhabited

/-- A refusal: the sentence the reader refuses, and why. -/
structure Refusal where
  /-- The sentence's position in the file, its modules' sentences counted in order from 0;
  `none` when the refusal is of the user module as a whole (a sentence it needs is missing). -/
  index : Option Nat
  /-- The sentence's head symbol or sort as the KORE writes it (the module's name for the module). -/
  head : String
  reason : RefusalReason
  /-- The name the reason concerns (an unknown symbol, a missing equation's function), or "". -/
  detail : String
  deriving Repr, Inhabited

/-- Where a stage of `parse` fails: a sentence, an equation by its attributes, a builtin sentence
by its source and line, or not yet said (the caller says; the module when none does). -/
inductive Site where
  | unset
  | sentence (s : Kore.Sentence)
  | attrs (as : List Kore.AppPattern)
  | builtin (src : String) (line : Nat)
  deriving Inhabited

/-- A stage's failure: its reason, the name it concerns, and where. -/
structure Fault where
  reason : RefusalReason
  detail : String
  site : Site
  deriving Inhabited

/-- A stage of `parse`: its result, or the reason it fails. -/
abbrev Rd := Except Fault

def fail {α : Type} (r : RefusalReason) (detail : String := "") : Rd α := .error ⟨r, detail, .unset⟩

/-- The value of `o`, or the failure `r`. -/
def need {α : Type} (o : Option α) (r : RefusalReason) (detail : String := "") : Rd α :=
  match o with
  | some a => .ok a
  | none => fail r detail

/-- The failures of `x` not yet placed, placed at `s`. -/
def Rd.within {α : Type} (s : Site) (x : Rd α) : Rd α :=
  match x with
  | .ok a => .ok a
  | .error f => .error (match f.site with | .unset => { f with site := s } | _ => f)

/-! ## Names to numbers -/

/-- The numbers of the names a definition uses: the registry's, then its own. -/
structure Names where
  sorts : List String
  syms : List String
  /-- the macro symbols, whose applications are refused by name (`macroSymbol`) -/
  macros : List String := []
  /-- the names the registry has that are the definition's own symbols: the library sorts'
  projections read as functions -/
  own : List String := []
  /-- the definition's own functions, not its parameter symbols, with their result sorts' names
  (`keyCut`) -/
  keyFns : List (Sym × String) := []
  /-- a value of each sort it lists, by name, applying no function: a constructor of the text's
  applied to `litValue?` of each argument sort (`eqnPlaceholder`) -/
  ctorVals : List (String × Kore.Pattern) := []
  /-- the definition's sorts hooked to a library carrier and the carrier's name (`scanCarrier`):
  their literals are read as the carrier's -/
  carriers : List (String × String) := []
  /-- the symbols a `functional` axiom of the text states single-valued, each with whether at every
  instance of its sort arguments (`Scan.fnls`, `singleValued`) -/
  fnlSyms : List (String × Bool) := []
  /-- the hooked equalities the reader writes (`readerEqs`) that the text declares without their
  `functional` axiom or their sentence `hookEqSentence`, each with what is missing
  (`hookEqualityUnstated`) -/
  eqUnstated : List (Sym × String) := []
  /-- the overloading symbols one of whose own overloads is a function of the definition, each with
  its result sort's name: a rule's left side applying one is read through the cut (`ovlCut`) -/
  ovlCutSyms : List (Sym × String) := []
  /-- the open generators (`isOpenGenerator`, read as `raw` parameters), each with its result
  sort's name: a rule's left side applying one is read through the cut (`ovlCut`), which
  `openCutRefusal` refuses where the generator's sort is not confined -/
  openCutSyms : List (Sym × String) := []

/-- The aliases K's prelude declares: their applications are refused by name, except as a rewrite
axiom's right side where the alias sentence is the identity (`identityAliases`, `unaliasRule`). -/
def preludeAliases : List String := ["weakExistsFinally", "weakAlwaysFinally", "allPathGlobally"]

/-- The alias sentence is the identity on its argument: `alias σ{A}(A) : A where σ{A}(X:A) := X:A`,
one sort variable A, one argument sort and the result sort A, the left side σ applied at A to one
variable of sort A (an element or a set variable), and the body that variable. An application
`σ{S}(φ)` then denotes φ. -/
def aliasIsIdentity (a : Kore.SentenceAlias) : Bool :=
  match a.alias.sortVars, a.sorts, a.app.args with
  | [A], [s], [.var x] =>
    let xs := match x with
      | .evar v => v.sort
      | .svar v => v.sort
    decide (s = .var A) && decide (a.sort = .var A) && decide (xs = .var A) &&
      decide (a.app.head = a.alias.ident) && decide (a.app.sorts = [.var A]) &&
      decide (a.body = .var x)
  | _, _, _ => false

/-- The aliases of `preludeAliases` that the prelude modules define each by alias sentences all
`aliasIsIdentity` (at least one). `parse` reads a text only where its modules before the user module
are `preludeModules` and refuses an alias sentence of the user module (`aliasDeclaration`), so these
are the text's own alias sentences. -/
def identityAliases : List String :=
  let als := (preludeModules.flatMap (·.sentences)).filterMap fun
    | .alias a => some a
    | _ => none
  preludeAliases.filter fun n =>
    let own := als.filter (·.alias.ident.ident.name == n)
    !own.isEmpty && own.all aliasIsIdentity

/-- A rewrite axiom's right side `σ{S}(φ)` with σ in `identityAliases`, one sort argument and one
argument: φ, itself so unwrapped; under `\exists` binders, the binders around their body so
unwrapped (an alias application denotes its body under a binder as at the root); `none` for a
right side not so headed. -/
def unaliasRhs? : Kore.Pattern → Option Kore.Pattern
  | .app h [_] [φ] =>
    -- the name first: no other right side reads the prelude
    if preludeAliases.contains h.ident.name && identityAliases.contains h.ident.name then
      some ((unaliasRhs? φ).getD φ)
    else none
  | .exist s x φ => (unaliasRhs? φ).map (.exist s x)
  | _ => none

/-- A rewrite axiom with its right side read through the identity aliases (`unaliasRhs?`,
`ReadingNote.identityAlias`); any other axiom as itself. -/
def unaliasRule (a : Kore.Axiom) : Kore.Axiom :=
  match a.pattern with
  | .rewrites s l r => match unaliasRhs? r with
    | some φ => { a with pattern := .rewrites s l φ }
    | none => a
  | _ => a

namespace Names
def sym? (N : Names) (n : String) : Option Sym :=
  let reg := fun (_ : Unit) => match regSymNames.idxOf? n with
    | some i => some i
    | none => (N.syms.idxOf? n).map (nRegSyms + ·)
  match N.own with
  | [] => reg ()
  | own => if own.contains n then (N.syms.idxOf? n).map (nRegSyms + ·) else reg ()
def srt? (N : Names) (n : String) : Option Srt :=
  match regSortNames.idxOf? n with
  | some i => some i
  | none => (N.sorts.idxOf? n).map (nRegSorts + ·)
def sortOf? (N : Names) (s : Kore.KSort) : Option Srt := sortName? s >>= N.srt?
/-- The number of the symbol `n`, or why it has none. -/
def symE (N : Names) (n : String) : Rd Sym :=
  need (N.sym? n) (if preludeAliases.contains n then .aliasApplication
    else if N.macros.contains n then .macroSymbol else .unknownSymbol) n
/-- The number of the sort named `n`, or why it has none. -/
def srtE (N : Names) (n : String) : Rd Srt := need (N.srt? n) .unknownSort n
/-- The reader writes the hooked equality `f` (`readerEqs`): refused `hookEqualityUnstated` where
the text declares it without the sentences its reading rests on (`eqUnstated`). -/
def hookEqE (N : Names) (f : Sym) : Rd Unit :=
  match N.eqUnstated.lookup f with
  | some d => fail .hookEqualityUnstated d
  | none => pure ()
/-- The number of the sort `s`, or why it has none. -/
def sortE (N : Names) (s : Kore.KSort) : Rd Srt := do
  N.srtE (← need (sortName? s) .parametricSort)
end Names

/-- A sort's name, or why it has none. -/
def sortNameE (s : Kore.KSort) : Rd String := need (sortName? s) .parametricSort

/-- `a` is a cell sort `XCell` and `b` its collection's sort `XCellMap`, `XCellSet` or
`XCellList`, as kompile names them. -/
def isCellCollPair (a b : String) : Bool :=
  let ac := a.toList
  ac.reverse.take 4 == "lleC".toList &&
    (b.toList == ac ++ "Map".toList || b.toList == ac ++ "Set".toList || b.toList == ac ++ "List".toList)

/-! ## Float literals -/

/-- The format a Float literal's suffix names, and the text before it: `f`/`F` binary32
`(24, 8)`, `d`/`D` or none binary64 `(53, 11)`, `pNxM` precision N and exponent width M, each of
`p` and `x` in either case (K's FLOAT-SYNTAX, domains.md:1495-1497: `[fFdD]|([pP][0-9]+[xX][0-9]+)`). -/
def floatSuffix (cs : List Char) : Option (List Char × Nat × Nat) :=
  match cs.reverse with
  | 'f' :: r | 'F' :: r => some (r.reverse, 24, 8)
  | 'd' :: r | 'D' :: r => some (r.reverse, 53, 11)
  | _ =>
    let isP := fun (c : Char) => c == 'p' || c == 'P'
    let isX := fun (c : Char) => c == 'x' || c == 'X'
    if cs.any isP then
      let body := cs.takeWhile (!isP ·)
      let fmt := (cs.dropWhile (!isP ·)).drop 1
      let pd := fmt.takeWhile (!isX ·)
      let ed := (fmt.dropWhile (!isX ·)).drop 1
      if pd.isEmpty || ed.isEmpty then none else do
        pure (body, ← digitsVal pd 0, ← digitsVal ed 0)
    else some (cs, 53, 11)

/-- The digits of an exponent `[+-]?d+` as an Int. -/
def expDigits? : List Char → Option Int
  | '-' :: ds => if ds.isEmpty then none else (digitsVal ds 0).map fun n => -(n : Int)
  | '+' :: ds => if ds.isEmpty then none else (digitsVal ds 0).map fun n => (n : Int)
  | ds => if ds.isEmpty then none else (digitsVal ds 0).map fun n => (n : Int)

/-- An optional exponent `[eE][+-]?d+`, as the power of ten (0 when absent). -/
def expPart? : List Char → Option Int
  | [] => some 0
  | c :: es => if c == 'e' || c == 'E' then expDigits? es else none

/-- An unsigned decimal `d+[.d*]?` or `.d+`, with an optional exponent `[eE][+-]?d+`: its digits as
one natural `m` and the power of ten `x` with value `m·10^x`. -/
def decimal? (cs : List Char) : Option (Nat × Int) :=
  let ip := cs.takeWhile Char.isDigit
  let r := cs.dropWhile Char.isDigit
  let (fp, r) := match r with
    | '.' :: r' => (r'.takeWhile Char.isDigit, r'.dropWhile Char.isDigit)
    | _ => ([], r)
  if ip.isEmpty && fp.isEmpty then none
  else (digitsVal (ip ++ fp) 0).bind fun m => (expPart? r).map fun x => (m, x - fp.length)

/-- A Float literal's text as the literal of its datum, for a string of one of K's FLOAT-SYNTAX
productions (domains.md:1495-1497) before a suffix (`floatSuffix`): a decimal, `[+-]?d+(.d*)?` or
`.d+` (a sign only before a digit), with an optional exponent `[eE][+-]?d+`; `[+-]?Infinity`;
`NaN` unsigned. A decimal's value is its value rounded to the nearest value of the format where the
text states which that is (`KFloat.ofDecimal?`, domains.md 1478-1483), the sign applied after
(rounding is symmetric, and `-0.0` is negative zero), encoded (`KFloat.packBits`); `Infinity` and
`NaN` are the format's infinity and canonical NaN. `none` for another text (`+.5`, `-.5`, `+NaN`,
`1.0p24`: no production holds them), a format without a model, and a decimal whose datum the text
does not state: one halfway between two data of the format, above its largest finite value, or
nonzero and rounding to zero. -/
def floatLit? (text : String) : Option Lit := do
  let (body, p, e) ← floatSuffix text.toList
  let s ← KFloat.spec? p e
  let s' ← KFloat.spec? (p + 1) e
  let (neg, mag) := match body with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let signed := mag.length != body.length
  let u ← if body == "NaN".toList then some Float.Model.UnpackedFloat.notANumber
    else if mag == "Infinity".toList then some (Float.Model.UnpackedFloat.infinity .positive)
    else if signed && !((mag.head?.map Char.isDigit).getD false) then none
    else (decimal? mag).bind fun (m, x) => KFloat.ofDecimal? s s' m x
  pure (.float p e (KFloat.packBits s (if neg then u.neg else u)))

/-- A literal of sort `s`, read from its text. -/
def lit? (s : Srt) (text : String) : Option Lit :=
  if s == Srt.int then (intLit? text).map .int
  else if s == Srt.bool then (boolLit? text).map .bool
  else if s == Srt.float then floatLit? text
  else some (.tok text)

/-! ## Terms -/

/-- The name of `ite` at the sort X (K-EQUAL's `ite{SortX{}}`): an own parameter symbol of the
definition, implemented by the registry's `kIte` (FixedSignature.lean). -/
def iteName (X : String) : String := "Lblite{" ++ X ++ "}"

/-- The name of the instance of a sort-parametric symbol `f{S₁,…,Sₙ}` at the sorts `X₁ … Xₙ`
(`Sort` dropped): `f{X₁,…,Xₙ}`. In KORE the instances of a sort-parametric symbol are distinct
symbols, related by no sentence the text does not state; each instance a read sentence applies is a
symbol of the definition's own (`envOf`). KORE's identifiers hold no brace or comma, so the name is
no other symbol's. (`ite`'s instances keep their own reading, `iteName`, implemented by the
registry's `kIte`.) -/
def instName (f : String) (xs : List String) : String := f ++ "{" ++ ",".intercalate xs ++ "}"

/-- The functions kompile generates and a user axiom may apply: K's `append`, the projections
`project:X`, a collection cell's initializer `initXCell`. `envOf` numbers those its axioms apply. A
projection the text gives an equation, a library sort's or a user sort's, is a function with the
text's equations as its clauses (`Presentation.libProjs`); an initializer outside the top cell
tree with an equation is a function with it (`Env.genSyms`); so are `append`, with the prelude's
equations (`appendEqns`), and an initializer of the top cell tree, with the text's equation
(`Env.genFns`). A projection the text gives no equation is a parameter symbol without
interpretation, of which the text states nothing. -/
def isGenFn (n : String) : Bool :=
  n == "append" || (dropPrefix? "Lblproject'Coln'" n).isSome ||
    ((dropPrefix? "Lblinit" n).isSome && (n.toList.reverse.take 4 == "lleC".toList))

def varIndex (vs : List Var) (x : Kore.EVar) : Rd (Nat × List Var) := do
  let n ← need (dropPrefix? "Var" x.var.ident.name) .variableName x.var.ident.name
  let s ← sortNameE x.sort
  match vs.findIdx? (·.name == n) with
  | some i => if (vs.getD i default).sort == s then pure (i, vs) else fail .variableSort n
  | none => pure (vs.length, vs ++ [⟨n, s⟩])

/-- The connective at the root of a pattern, as KORE writes it. -/
def connective : Kore.Pattern → String
  | .var (.evar _) => "element variable"
  | .var (.svar _) => "set variable"
  | .app h _ _ => h.ident.name
  | .string _ => "string"
  | .top _ => "\\top"
  | .bottom _ => "\\bottom"
  | .not .. => "\\not"
  | .and .. => "\\and"
  | .or .. => "\\or"
  | .implies .. => "\\implies"
  | .iff .. => "\\iff"
  | .exist .. => "\\exists"
  | .forall .. => "\\forall"
  | .mu .. => "\\mu"
  | .nu .. => "\\nu"
  | .ceil .. => "\\ceil"
  | .floor .. => "\\floor"
  | .equals .. => "\\equals"
  | .in .. => "\\in"
  | .next .. => "\\next"
  | .rewrites .. => "\\rewrites"
  | .dv .. => "\\dv"
  | .leftAssoc .. => "\\left-assoc"
  | .rightAssoc .. => "\\right-assoc"

/-- A form of pattern no text kompile 7.1.337 writes (`RefusalReason.unkompiledForm`). -/
def isUnkompiledForm : Kore.Pattern → Bool
  | .mu .. | .nu .. | .next .. | .iff .. | .leftAssoc .. | .rightAssoc .. | .string _ => true
  | _ => false

mutual
  def term (N : Names) (vs : List Var) : Kore.Pattern → Rd (Term × List Var)
    | .var (.evar x) => do let (i, vs) ← varIndex vs x; pure (.var i, vs)
    | .app h ss ps =>
      if h.ident.name == "inj" then match ss, ps with
        | [A, B], [p] => do
          let a ← sortNameE A
          let b ← sortNameE B
          if isCellCollPair a b then fail .cellCollectionInjection b
          let (t, vs) ← term N vs p
          pure (.inj (← N.srtE a) (← N.srtE b) t, vs)
        | _, _ => fail .injShape
      else if ss.isEmpty then do
        let (ts, vs) ← terms N vs ps
        pure (.app (← N.symE h.ident.name) ts, vs)
      else if preludeAliases.contains h.ident.name then fail .aliasApplication h.ident.name
      else if h.ident.name == "Lblite" then match ss with
        | [S] => do
          let (ts, vs) ← terms N vs ps
          pure (.app (← N.symE (iteName (← sortNameE S))) ts, vs)
        | _ => fail .iteShape
      -- an instance of a sort-parametric symbol at sorts of the definition (`instName`): a symbol of
      -- the definition's own when `envOf` numbered it, refused otherwise
      else match (ss.mapM sortName?).bind fun xs => N.sym? (instName h.ident.name xs) with
        | some f => do
          let (ts, vs) ← terms N vs ps
          pure (.app f ts, vs)
        | none => fail .parametricSymbol h.ident.name
    | .and _ [p, .var (.evar x)] => do
      let (t, vs) ← term N vs p
      let (i, vs) ← varIndex vs x
      pure (.as t i, vs)
    | .dv s text => do
      let b := ((N.carriers.find? (fun p => some p.1 == sortName? s)).bind fun p => N.srt? p.2)
      let s ← N.sortE s
      pure (.dv s (← need (lit? (b.getD s) text) .literal text), vs)
    -- a quantifier or a `\floor` of a term over a sort other than Bool: which elements the sort
    -- has decides its truth, and the reader does not decide it (`openExtent`)
    | .forall s x p => match sortName? x.sort with
      | some X => if X == "Bool" then fail .patternConnective (connective (.forall s x p)) else fail .openExtent X
      | none => fail .patternConnective "\\forall"
    | .floor s r p => match sortName? s with
      | some X => if X == "Bool" then fail .patternConnective (connective (.floor s r p)) else fail .openExtent X
      | none => fail .patternConnective "\\floor"
    | .var (.svar x) => fail .setVariable x.var.ident.name
    | p => fail (if isUnkompiledForm p then .unkompiledForm else .patternConnective) (connective p)
    termination_by structural p => p
  def terms (N : Names) (vs : List Var) : List Kore.Pattern → Rd (List Term × List Var)
    | [] => pure ([], vs)
    | p :: ps => do
      let (t, vs) ← term N vs p
      let (ts, vs) ← terms N vs ps
      pure (t :: ts, vs)
    termination_by structural ps => ps
end

/-- The numbers of a variable list's sorts. -/
def varSorts (N : Names) (vs : List Var) : Rd (List Srt) := vs.mapM (N.srtE ·.sort)

mutual
  def Term.reindex (f : Nat → Nat) : Term → Term
    | .var i => .var (f i)
    | .app g ts => .app g (Term.reindexList f ts)
    | .inj a b t => .inj a b (Term.reindex f t)
    | .as t i => .as (Term.reindex f t) (f i)
    | .dv s lit => .dv s lit
    termination_by structural t => t
  def Term.reindexList (f : Nat → Nat) : List Term → List Term
    | [] => []
    | t :: ts => Term.reindex f t :: Term.reindexList f ts
    termination_by structural ts => ts
end

/-! ## A function's application as a map key in a rule's left side

A rule's left side is a pattern: at a valuation of its variables it denotes the configurations it
matches. A map key `f(t̄) |-> V` in it, `f` a function, denotes the maps with the key `f(t̄)`'s value
(none where `f` has no value there). When every variable of `t̄` occurs in the left side outside such
applications (`<base> B </base> … <mem> idx(B, I) |-> V … </mem>`), the rest of the left side fixes
`t̄`'s value, so the left side matches exactly what it matches with a fresh variable `X` as the key and
the condition that `X` is `f(t̄)`'s value. The rule is read so: the key replaced by `X`, and
`X ==Int f(t̄)` (`==K` of `X` and `f(t̄)`, each in a one-item K sequence, for another sort) conjoined
to its `requires`. `Step` applies a rule where its left side denotes the configuration and its
`requires` evaluates to `true`, and the rule blocks the rules of larger priorities except where every
match makes its `requires` evaluate to something other than `true`, no value included
(`NotApplies`). The conjunct is `true` exactly where `X` is `f(t̄)`'s value, `false` where `f(t̄)`
has another value, and has no value where `f(t̄)` has none: where the text's left side matches, the
read rule's `requires` is the written one's value, and elsewhere it is not `true`, so the rule
applies, and blocks, exactly where the text's does, provided `f`'s evaluation has a result (a value
or none) at the arguments, which is what the statements assume of every function (`FnHyp`, its first
conjunct). The conjunction is strict: `⟨R, C₁, …, Cₙ⟩ ==K ⟨true, …, true⟩` over one-item K
sequences, which no short-circuiting evaluation skips a part of (`Lazy.lean`), so no argument
obligation is added. Read so: only a map key of `Map`'s `_|->_`, only in a rule (a function's
equation is not read so), only an application of a function of the definition's own, not a
parameter symbol (`Names.keyFns`), whose arguments hold no `#as`; any other function application in a left side stays
refused (`functionInPattern`). -/

mutual
  /-- No `#as` binding in `t`. -/
  def asFree : Term → Bool
    | .var _ => true
    | .app _ ts => asFreeList ts
    | .inj _ _ t => asFree t
    | .as _ _ => false
    | .dv _ _ => true
    termination_by structural t => t
  def asFreeList : List Term → Bool
    | [] => true
    | t :: ts => asFree t && asFreeList ts
    termination_by structural ts => ts
end

mutual
  /-- The variables of a term outside the applications of the functions of `fs`. -/
  def keyOutside (fs : List (Sym × String)) : Term → List Nat
    | .var i => [i]
    | .app f ts => if (fs.lookup f).isSome then [] else keyOutsideList fs ts
    | .inj _ _ t => keyOutside fs t
    | .as t i => i :: keyOutside fs t
    | .dv _ _ => []
    termination_by structural t => t
  def keyOutsideList (fs : List (Sym × String)) : List Term → List Nat
    | [] => []
    | t :: ts => keyOutside fs t ++ keyOutsideList fs ts
    termination_by structural ts => ts
end

/-- A map key that `keyCut` reads as a fresh variable: an application of a function of `fs`,
injected or not, whose arguments have their variables in `B` and no `#as`; the function and its
result sort's name. -/
def keyApp? (fs : List (Sym × String)) (B : List Nat) (t : Term) : Option (Sym × String) :=
  let app? := fun (f : Sym) (ts : List Term) => match fs.lookup f with
    | some X => if (varOccsList ts).all B.contains && asFreeList ts then some (f, X) else none
    | none => none
  match t with
  | .app f ts => app? f ts
  | .inj _ _ (.app f ts) => app? f ts
  | _ => none

mutual
  /-- `t` with each map key `keyApp?` accepts replaced by a fresh variable, numbered from `n`
  (under the key's injection): the term, the next number, and each fresh variable with the
  function, its result sort's name and the application it stands for. -/
  def cutKeys (fs : List (Sym × String)) (B : List Nat) (n : Nat) : Term → Term × Nat × List (Nat × Sym × String × Term)
    | .app f ts => let (ts', m, cs) := cutKeysList fs B n (f == mapElem) ts; (.app f ts', m, cs)
    | .inj a b t => let (t', m, cs) := cutKeys fs B n t; (.inj a b t', m, cs)
    | .as t i => let (t', m, cs) := cutKeys fs B n t; (.as t' i, m, cs)
    | t => (t, n, [])
    termination_by structural t => t
  /-- `cutKeys` on each term of `ts`; with `key`, the first is a map key. -/
  def cutKeysList (fs : List (Sym × String)) (B : List Nat) (n : Nat) (key : Bool) :
      List Term → List Term × Nat × List (Nat × Sym × String × Term)
    | [] => ([], n, [])
    | t :: ts =>
      let (t', m, cs) := match key, keyApp? fs B t with
        | true, some (f, X) => match t with
          | .inj a b app => (Term.inj a b (.var n), n + 1, [(n, f, X, app)])
          | app => (Term.var n, n + 1, [(n, f, X, app)])
        | _, _ => cutKeys fs B n t
      let (ts', m', cs') := cutKeysList fs B m false ts
      (t' :: ts', m', cs ++ cs')
    termination_by structural ts => ts
end

/-- The map keys of a rule's left side `lhs` that apply a function of `fs` (`keyApp?`, the
variables bound by the rest of the left side): `cutKeys` from `n`. -/
def keyCuts (fs : List (Sym × String)) (lhs : Term) (n : Nat) : Term × Nat × List (Nat × Sym × String × Term) :=
  cutKeys fs (keyOutside fs lhs) n lhs

/-- A variable name no variable of `vs` has: `x`, primed until it is new. -/
def freshName (vs : List Var) : Nat → String → String
  | 0, x => x
  | fuel + 1, x => if vs.any (·.name == x) then freshName vs fuel (x ++ "'") else x

/-- A rule's left side `lhs` and its variables `vs`, read with each map key that applies a function
of the definition's own cut (`keyCuts`): the left side, the variables with the fresh ones after them
(`Key0`, `Key1`, …, primed until new), and the memberships `Key ∈ f(t̄)` of the fresh variables in
their applications (`Cond.mem` at the function's result sort, the variable first), in the order of
the text.

The text's left side `C[f(t̄)]` is `∃Key. C[Key] ∧ Key ∈ f(t̄)` in every interpretation: an
application is pointwise over the elements its arguments hold, and `f(t̄)` is inside f's result
sort, Key's (`KCore.cut_identity`). Key is fresh, so it is in neither the right side nor the
`requires`, and `(∃Key. C[Key] ∧ Key ∈ f(t̄)) ∧ req → •R` is `∀Key. (C[Key] ∧ req ∧ Key ∈ f(t̄) → •R)`:
the rule read with Key a variable, the written `requires` as `req` and the membership a conjunct of
`pre`, is the text's rule, with no premise. The right side is read as the text writes it, an
application of f there included: the cut is of the left side only. -/
def keyCut (N : Names) (lhs : Term) (vs : List Var) : Rd (Term × List Var × List Cond) :=
  match N.keyFns with
  | [] => pure (lhs, vs, [])
  | fs => match keyCuts fs lhs vs.length with
    | (_, _, []) => pure (lhs, vs, [])
    | (lhs', _, cs) => do
      let vs' := cs.foldl (fun acc (_, _, X, _) =>
        acc ++ [⟨freshName acc (acc.length + 1) ("Key" ++ toString (acc.length - vs.length)), X⟩]) vs
      let mems ← cs.mapM fun (i, _, X, app) => do pure (Cond.mem (← N.srtE X) (.var i) app)
      pure (lhs', vs', mems)

/-! ## A function-overloaded symbol in a rule's left side

An overloading symbol g one of whose own overloads is a function of the definition
(`Semantics.fnOvlSyms`) denotes, at arguments an overload covers, the injected value of that
function, and elsewhere its own application; matching `g(P̄)` against a value would need the
function's inverse. A left side `C[g(P̄)]`, the hole under applications, is `∃V. C[V] ∧ V ∈ g(P̄)` in
every interpretation, V fresh of g's sort: an application is pointwise over the elements its
arguments hold (the cut, `KCore.cut_identity`). With V not in the right side or the `ensures`,
`(∃V. C[V] ∧ V ∈ g(P̄)) ∧ req → •R` is `∀V. (C[V] ∧ req ∧ V ∈ g(P̄) → •R)`. So the reader reads the
application as a fresh variable V and conjoins `V ∈ g(P̄)` to the rule's `pre` (`Cond.mem`, whose
term is evaluated, not matched): the left side so read applies no function-overloaded symbol.
Outermost applications are cut, left to right; an inner one stays in the term. An application whose
arguments hold `#as` is not cut, since an `#as` names a matched subterm and the cut's term is not
matched: it stays in the left side, refused (`functionInPattern`). The variables of P̄ that the rest of
the left side does not hold are then variables the left side does not bind, decided as any such
(`rulesPlain`; `openRefusal` names the symbol).

An open generator g (`Names.openCutSyms`, a `raw` parameter) is cut the same way: `C[g(P̄)]` is
`∃V. C[V] ∧ V ∈ g(P̄)` in every interpretation, and the membership's term is evaluated through the
interpretation's value of g (`Semantics.paramVal`), where matching `g(P̄)` would need the preimage
of a value under that interpretation. Where g's sort is confined, every argument sort of g is
confined (`Semantics.confinedAt`: the generators of a confined sort take arguments of confined
sorts), so the variables the cut leaves open are of confined sorts and `rulesPlain` reads them.
Where it is not, a variable of P̄ that the rest of the left side does not hold may be matched by an
element that is no value's which the interpretation sends to a value, and which elements those are
the text does not say: `openCutRefusal` refuses such a rule (`openGeneratorPattern`). -/

mutual
  /-- `t` with each outermost application of a symbol of `cs` whose arguments hold no `#as`
  replaced by a fresh variable numbered from `n`: the term, the next number, and each fresh
  variable with the symbol's result sort's name and the application it stands for, left to
  right. -/
  def cutOvlApps (cs : List (Sym × String)) (n : Nat) : Term → Term × Nat × List (Nat × String × Term)
    | .app f ts => match cs.lookup f with
      | some X => if asFreeList ts then (.var n, n + 1, [(n, X, .app f ts)]) else (.app f ts, n, [])
      | none => let (ts', m, xs) := cutOvlAppsList cs n ts; (.app f ts', m, xs)
    | .inj a b t => let (t', m, xs) := cutOvlApps cs n t; (.inj a b t', m, xs)
    | .as t i => let (t', m, xs) := cutOvlApps cs n t; (.as t' i, m, xs)
    | t => (t, n, [])
    termination_by structural t => t
  /-- `cutOvlApps` on each term of `ts`, the numbers continuing. -/
  def cutOvlAppsList (cs : List (Sym × String)) (n : Nat) :
      List Term → List Term × Nat × List (Nat × String × Term)
    | [] => ([], n, [])
    | t :: ts =>
      let (t', m, xs) := cutOvlApps cs n t
      let (ts', m', xs') := cutOvlAppsList cs m ts
      (t' :: ts', m', xs ++ xs')
    termination_by structural ts => ts
end

/-- The conjunction of the conditions, `\top` for none. -/
def ovlCutConj : List Cond → Cond
  | [] => .top
  | [p] => p
  | p :: ps => .and p (ovlCutConj ps)

/-- A rule's left side `lhs` and its variables `vs`, read with each application of a
function-overloaded symbol (`Names.ovlCutSyms`) or of an open generator (`Names.openCutSyms`) cut
(`cutOvlApps`): the left side, the variables with the fresh ones after them (`Ovl0`, `Ovl1`, … for
the first, `Open0`, `Open1`, … for the second, numbered by position among the fresh ones, primed until
new), and the conjunction of the memberships `V ∈ g(P̄)` of the fresh variables in their
applications, `\top` where nothing is cut. -/
def ovlCut (N : Names) (lhs : Term) (vs : List Var) : Rd (Term × List Var × Cond) :=
  match N.ovlCutSyms ++ N.openCutSyms with
  | [] => pure (lhs, vs, .top)
  | cs => match cutOvlApps cs vs.length lhs with
    | (_, _, []) => pure (lhs, vs, .top)
    | (lhs', _, xs) => do
      let pfx := fun (app : Term) => match app with
        | .app f _ => if (N.ovlCutSyms.lookup f).isSome then "Ovl" else "Open"
        | _ => "Ovl"
      let vs' := xs.foldl (fun acc (_, X, app) =>
        acc ++ [⟨freshName acc (acc.length + 1) (pfx app ++ toString (acc.length - vs.length)), X⟩]) vs
      let mems ← xs.mapM fun (i, X, app) => do pure (Cond.mem (← N.srtE X) (.var i) app)
      pure (lhs', vs', ovlCutConj mems)

/-! ## Connectives with a term's reading

A rewrite axiom's or an equation's sides may hold matching-logic connectives where kompile copies the
K text's `#Or`, `#And`, `#Top`, `#Bottom`, `#Exists`, `#Ceil`, `{_ #Equals _}`. Some of them denote
what a term with a condition denotes, by laws of matching logic that hold in every model; the
reader reads those so, each with its note (`ReadingNote`), and refuses the others.

- Left side (`orSplit`, `topAsVariable`, `existsAsVariable`): application is pointwise, so under
  symbol applications and conjunctions `C[φ ∨ ψ] = C[φ] ∨ C[ψ]`, `C[⊤] = ∃z. C[z]` and
  `C[∃y. φ] = ∃y. C[φ]` (y not free in C); and `(φ ∨ ψ) → •R` is `(φ → •R) ∧ (ψ → •R)`,
  `(∃y. φ) → •R` is `∀y. (φ → •R)` for y not free in R. So a disjunction is one rule per disjunct,
  of the rule's priority, `requires`, right side and `ensures` (`splitRule`), and `⊤` and `∃y` are
  variables of the rule (`lhsBound`), each given a name the axiom does not hold. A disjunct that is
  empty (`vacuous`) is dropped: `φ ∨ ⊥ = φ`. Both laws of `∀` need the variable's sort to have an
  element where the variable is in no rule read: a variable some disjunct's rule does not hold, or
  `∃y. φ` with y not in φ, stands as an `\exists` around that rule's left side (`splitRule`), and the
  rule is read without it where the reader exhibits a value of its sort (`exhibit?`), refused
  `unheldVariable` otherwise (`unheldRefusal`).
- `requires` (`requiresOrSplit`): `\equals{SortBool{},S}(\and{SortBool{}}(\or(A₁, …, Aₙ), G), true)`,
  G a Bool variable free nowhere else and each Aᵢ a term, is n rules, the i-th with `requires` Aᵢ
  (`reqOrSplit?`, `splitRule`).
- Left side empty (`InertReason.vacuousLeft`): `C[⊥] = ⊥`, and `⊥ → •R` holds in every model.
- Right side (`andAsEnsures`, `andTermsWeaker`, `bottomAsEnsures`, `orBottom`): for a predicate P
  (a pattern that is everything or nothing) `σ(…, φ ∧ P, …) = σ(…, φ, …) ∧ P`, and
  `σ(…, ⊥, …) = ⊥`, for every symbol σ. So `\equals{SortBool{},S}(B, true)` conjoined to a part of
  the right side is an `ensures` B of the whole, the equality reading being for that predicate
  conjunct; on a rule's right side `t ∧ u` of two terms is read as t with the `ensures` `t ==K u`
  (`==Int` at Int; strict: no value where either has none), a weakening the text entails
  (`R′ = C[t] ∧ (t ==K u) ⊇ C[t ∧ u]` where the `ensures` holds, and `•` is monotone) and not one
  equal to it (`andTermsWeaker`); on an equation's right side it is refused
  `patternConnective` (`\and`): `t ∧ u` is `t ∩ u`, and t with that `ensures` is not `t ∩ u` where
  t or u has two elements, which no sentence of the text excludes for a function it leaves open;
  `⊥` anywhere under applications makes the right side empty, which is the `ensures` false
  (the rule or equation still applies there: it blocks larger priorities and gives no successor or
  value); and `t ∨ ⊥ = t`. Several `ensures` of an equation are one strict conjunction (`conjTerms`),
  of a rule the first its `ensures` and the others conjuncts `B = true` of `post`. `t ∧ X` of a
  term and a variable is the second case (a right side binds nothing, so it is not `t #as X`).
  An equation's right side holding `\or`, `\top`, `\not` or `\exists` under applications is
  refused (`manyValuedRightSide`).
- A rule's right side under `\exists` (`existsRenamedApart`, `existsDropped`): the sentence is
  `lhs ∧ req → •(∃x̄. (rhs ∧ ens))`, and the binders x̄ are the rule's existential variables
  (`Rule.exs`). A variable is a name and a sort, and a binder's scope is its body, so a variable
  of a binder's name that the left side or the `requires` holds is free in the axiom and another
  variable than the bound one: the binder is renamed apart, with the occurrences it binds
  (`rhsApart`), the α-variant denoting the same. A binder whose variable is free in no part of its
  body that is read binds nothing (`exKept`): `∃Z:s. φ` is then φ where s has an element and empty
  where it has none, so the text's sentence entails `lhs ∧ req → •(rhs ∧ ens)` (next of the empty
  pattern is empty: where s is empty the text says the left side has no instance) and is it where s
  has an element; the binder is dropped at every sort. This is not the left side's case
  (`unheldVariable`): there the sentence with the binder states nothing where the sort is empty, so
  the rule without it would state more than the text.
- `requires` and `ensures` (`predicateAtBool`, `andAtBool`), written `\equals{SortBool{},S}(B,
  true)`: where B is a predicate at sort Bool it is `\top{SortBool{}}` or `\bottom{SortBool{}}`,
  and neither equals `true`: the first holds `false`, which is apart from `true`, the second holds
  nothing. So the condition never holds, and it is read as the literal `false`. Where B is
  `\and{SortBool{}}(B₁, …, Bₙ)` of terms, B is the intersection of the Bᵢ (`B ∧ X` of a variable
  among them), which `⌈B₁ = true⌉ ∧ … ∧ ⌈Bₙ = true⌉` entails and is where each Bᵢ has at most one
  element. A rule's is read so conjunct by conjunct, B₁ its `requires` (`ensures`) and the others
  conjuncts `Bᵢ = true` of `pre` (`post`); an equation's as the strict conjunction of the Bᵢ, and
  only where every Bᵢ is `singleValued` (`eqnCondTerm`), refused `patternConnective` (`\and`)
  otherwise. A conjunction
  under an application of a condition is refused (`patternConnective`).

A quantifier `\forall` or `\floor` of a term over a sort other than Bool is refused `openExtent`
with its sort (`RefusalReason.openExtent`); a set variable, `setVariable`. -/

mutual
  /-- The element variables' names a pattern holds, bound or free. -/
  def evarNames : Kore.Pattern → List String
    | .var (.evar x) => [x.var.ident.name]
    | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => evarNamesList ps
    | .not _ p | .next _ p | .ceil _ _ p | .floor _ _ p | .mu _ p | .nu _ p => evarNames p
    | .exist _ x p | .forall _ x p => x.var.ident.name :: evarNames p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      evarNames p ++ evarNames q
    | _ => []
    termination_by structural p => p
  def evarNamesList : List Kore.Pattern → List String
    | [] => []
    | p :: ps => evarNames p ++ evarNamesList ps
    termination_by structural ps => ps
end

/-- `x`, primed until no name of `used` is it. -/
def freshIn (used : List String) : Nat → String → String
  | 0, x => x
  | fuel + 1, x => if used.contains x then freshIn used fuel (x ++ "'") else x

mutual
  /-- `p` with the free occurrences of the variable `x` replaced by `y`. -/
  def renameEVar (x y : Kore.EVar) : Kore.Pattern → Kore.Pattern
    | .var (.evar z) => .var (.evar (if decide (z = x) then y else z))
    | .app h ss ps => .app h ss (renameEVarList x y ps)
    | .and s ps => .and s (renameEVarList x y ps)
    | .or s ps => .or s (renameEVarList x y ps)
    | .not s p => .not s (renameEVar x y p)
    | .exist s z p => if decide (z = x) then .exist s z p else .exist s z (renameEVar x y p)
    | .forall s z p => if decide (z = x) then .forall s z p else .forall s z (renameEVar x y p)
    | .ceil s r p => .ceil s r (renameEVar x y p)
    | .floor s r p => .floor s r (renameEVar x y p)
    | .equals s r p q => .equals s r (renameEVar x y p) (renameEVar x y q)
    | .in s r p q => .in s r (renameEVar x y p) (renameEVar x y q)
    | .implies s p q => .implies s (renameEVar x y p) (renameEVar x y q)
    | p => p
    termination_by structural p => p
  def renameEVarList (x y : Kore.EVar) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => renameEVar x y p :: renameEVarList x y ps
    termination_by structural ps => ps
end

mutual
  /-- A disjunction under applications and conjunctions. -/
  def hasOr : Kore.Pattern → Bool
    | .or .. => true
    | .app _ _ ps | .and _ ps => hasOrList ps
    | _ => false
    termination_by structural p => p
  def hasOrList : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => hasOr p || hasOrList ps
    termination_by structural ps => ps
end

mutual
  /-- `\top` or `\exists` under applications and conjunctions: the first, `true`, or the second. -/
  def binderKinds : Kore.Pattern → List Bool
    | .top _ => [true]
    | .exist .. => [false]
    | .app _ _ ps | .and _ ps => binderKindsList ps
    | _ => []
    termination_by structural p => p
  def binderKindsList : List Kore.Pattern → List Bool
    | [] => []
    | p :: ps => binderKinds p ++ binderKindsList ps
    termination_by structural ps => ps
end

mutual
  /-- The pattern is `\bottom` by the laws `σ(…, ⊥, …) = ⊥`, `φ ∧ ⊥ = ⊥`, `∃y. ⊥ = ⊥` and
  `⊥ ∨ ⊥ = ⊥`. -/
  def vacuous : Kore.Pattern → Bool
    | .bottom _ => true
    | .app _ _ ps | .and _ ps => anyVacuous ps
    | .exist _ _ p => vacuous p
    | .or _ ps => allVacuous ps
    | _ => false
    termination_by structural p => p
  def anyVacuous : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => vacuous p || anyVacuous ps
    termination_by structural ps => ps
  def allVacuous : List Kore.Pattern → Bool
    | [] => true
    | p :: ps => vacuous p && allVacuous ps
    termination_by structural ps => ps
end

mutual
  /-- The disjuncts of a left side, the disjunctions under applications and conjunctions
  distributed (`C[φ ∨ ψ] = C[φ] ∨ C[ψ]`). -/
  def orAlts : Kore.Pattern → List Kore.Pattern
    | .or _ ps => orAltsOr ps
    | .app h ss ps => (orAltsList ps).map (.app h ss)
    | .and s ps => (orAltsList ps).map (.and s)
    | p => [p]
    termination_by structural p => p
  def orAltsOr : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => orAlts p ++ orAltsOr ps
    termination_by structural ps => ps
  def orAltsList : List Kore.Pattern → List (List Kore.Pattern)
    | [] => [[]]
    | p :: ps => (orAlts p).flatMap fun a => (orAltsList ps).map (a :: ·)
    termination_by structural ps => ps
end

mutual
  /-- The element variables free in a pattern, those of `bound` left out. -/
  def freeEVars (bound : List String) : Kore.Pattern → List String
    | .var (.evar x) => if bound.contains x.var.ident.name then [] else [x.var.ident.name]
    | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => freeEVarsList bound ps
    | .not _ p | .next _ p | .ceil _ _ p | .floor _ _ p | .mu _ p | .nu _ p => freeEVars bound p
    | .exist _ x p | .forall _ x p => freeEVars (x.var.ident.name :: bound) p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      freeEVars bound p ++ freeEVars bound q
    | _ => []
    termination_by structural p => p
  def freeEVarsList (bound : List String) : List Kore.Pattern → List String
    | [] => []
    | p :: ps => freeEVars bound p ++ freeEVarsList bound ps
    termination_by structural ps => ps
end

mutual
  /-- A variable bound by `\exists` under applications and conjunctions and free in no part of its
  body. -/
  def exUnheld? : Kore.Pattern → Option String
    | .exist _ x p =>
      if (freeEVars [] p).contains x.var.ident.name then exUnheld? p else some x.var.ident.name
    | .app _ _ ps | .and _ ps => exUnheldList? ps
    | _ => none
    termination_by structural p => p
  def exUnheldList? : List Kore.Pattern → Option String
    | [] => none
    | p :: ps => (exUnheld? p).orElse fun _ => exUnheldList? ps
    termination_by structural ps => ps
end

mutual
  /-- `\top{S}()` as a fresh variable of sort S and `\exists{_}(Y, φ)` as φ with Y a fresh
  variable, under applications and conjunctions (`topAsVariable`, `existsAsVariable`): names not
  in `used`, the n-th and later. -/
  def lhsBind (used : List String) (n : Nat) : Kore.Pattern → Kore.Pattern × Nat
    | .top s => (KoreAML.ev (freshIn used (used.length + 1) s!"Var'Hash'Top{n}") s, n + 1)
    | .exist _ x p =>
      let y := KoreAML.evar (freshIn used (used.length + 1) s!"Var'Hash'Ex{n}") x.sort
      let (p', m) := lhsBind used (n + 1) p
      (renameEVar x y p', m)
    | .app h ss ps => let (ps', m) := lhsBindList used n ps; (.app h ss ps', m)
    | .and s ps => let (ps', m) := lhsBindList used n ps; (.and s ps', m)
    | p => (p, n)
    termination_by structural p => p
  def lhsBindList (used : List String) (n : Nat) : List Kore.Pattern → List Kore.Pattern × Nat
    | [] => ([], n)
    | p :: ps =>
      let (p', m) := lhsBind used n p
      let (ps', k) := lhsBindList used m ps
      (p' :: ps', k)
    termination_by structural ps => ps
end

/-- The left side `l` of the rewrite axiom whose pattern is `ax`, with `lhsBind`'s variables. -/
def lhsBound (ax l : Kore.Pattern) : Kore.Pattern :=
  if (binderKinds l).isEmpty then l else (lhsBind (evarNames ax) 0 l).1

/-- A condition a right side's conjunction states: a Bool term that must be `true`, or two
patterns of the sort `s` that must have one value. -/
inductive SideCond where
  | isTrue (b : Kore.Pattern)
  | same (s : Kore.KSort) (t u : Kore.Pattern)

/-- `\equals{SortBool{},S}(B, \dv{SortBool{}}("true"))`'s B. -/
def isTrueOf? : Kore.Pattern → Option Kore.Pattern
  | .equals bs _ b (.dv bs' "true") => if sortName? bs == some "Bool" && sortName? bs' == some "Bool" then some b else none
  | _ => none

mutual
  /-- A right side with its conjunctions with `\equals(B, true)` and between two patterns lifted
  out of its applications, and `t ∨ ⊥` read as t: the side, the conditions, and whether it is empty
  (`vacuous` parts under applications). -/
  def hoist : Kore.Pattern → Kore.Pattern × List SideCond × Bool
    | .bottom s => (.bottom s, [], true)
    | .app h ss ps => let (ps', cs, b) := hoistList ps; (.app h ss ps', cs, b)
    | .or s [t, u] => match t, u with
      | _, .bottom _ => hoist t
      | .bottom _, _ => hoist u
      | _, _ => (.or s [t, u], [], false)
    | .and s [t, u] => match isTrueOf? u, isTrueOf? t, u with
      | some b, _, _ => let (t', cs, e) := hoist t; (t', cs ++ [.isTrue b], e)
      | none, some b, _ => let (u', cs, e) := hoist u; (u', cs ++ [.isTrue b], e)
      -- two patterns, a variable among them: a right side binds nothing (no `#as`)
      | none, none, _ =>
        let (t', cs, e) := hoist t
        let (u', cs', e') := hoist u
        (t', cs ++ cs' ++ [.same s t' u'], e || e')
    | p => (p, [], false)
    termination_by structural p => p
  def hoistList : List Kore.Pattern → List Kore.Pattern × List SideCond × Bool
    | [] => ([], [], false)
    | p :: ps =>
      let (p', cs, e) := hoist p
      let (ps', cs', e') := hoistList ps
      (p' :: ps', cs ++ cs', e || e')
    termination_by structural ps => ps
end

mutual
  /-- The first connective under applications of a pattern that has several elements or none at a
  point: `\or`, `\top`, `\not`, `\exists` (`manyValuedRightSide`). -/
  def manyValued? : Kore.Pattern → Option String
    | .or .. => some "\\or"
    | .top _ => some "\\top"
    | .not .. => some "\\not"
    | .exist .. => some "\\exists"
    | .app _ _ ps => manyValuedList? ps
    | _ => none
    termination_by structural p => p
  def manyValuedList? : List Kore.Pattern → Option String
    | [] => none
    | p :: ps => (manyValued? p).orElse fun _ => manyValuedList? ps
    termination_by structural ps => ps
end

mutual
  /-- A disjunction with `\bottom` under applications and conjunctions (`orBottom`). -/
  def hasOrBottom : Kore.Pattern → Bool
    | .or _ [_, .bottom _] | .or _ [.bottom _, _] => true
    | .app _ _ ps | .and _ ps => hasOrBottomList ps
    | _ => false
    termination_by structural p => p
  def hasOrBottomList : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => hasOrBottom p || hasOrBottomList ps
    termination_by structural ps => ps
end

mutual
  /-- A predicate: a pattern that is everything or nothing at its sort. -/
  def isPred : Kore.Pattern → Bool
    | .ceil .. | .floor .. | .equals .. | .in .. | .top _ | .bottom _ => true
    | .not _ p | .exist _ _ p | .forall _ _ p => isPred p
    | .implies _ p q | .iff _ p q => isPred p && isPred q
    | .and _ ps | .or _ ps => isPredList ps
    | _ => false
    termination_by structural p => p
  def isPredList : List Kore.Pattern → Bool
    | [] => true
    | p :: ps => isPred p && isPredList ps
    termination_by structural ps => ps
end

mutual
  /-- The element variables free in a pattern, with their sorts, those named in `bound` left out
  (`freeEVars` with the sorts). -/
  def freeEVarsS (bound : List String) : Kore.Pattern → List Kore.EVar
    | .var (.evar x) => if bound.contains x.var.ident.name then [] else [x]
    | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => freeEVarsSList bound ps
    | .not _ p | .next _ p | .ceil _ _ p | .floor _ _ p | .mu _ p | .nu _ p => freeEVarsS bound p
    | .exist _ x p | .forall _ x p => freeEVarsS (x.var.ident.name :: bound) p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      freeEVarsS bound p ++ freeEVarsS bound q
    | _ => []
    termination_by structural p => p
  def freeEVarsSList (bound : List String) : List Kore.Pattern → List Kore.EVar
    | [] => []
    | p :: ps => freeEVarsS bound p ++ freeEVarsSList bound ps
    termination_by structural ps => ps
end

mutual
  /-- A pattern with each `\exists` under applications and conjunctions whose variable is free in
  no part of its body taken out, and those binders: `C[∃y. φ]` is `∃y. C[φ]` for y not free in C,
  so the binder may stand around the whole pattern once renamed apart from its names
  (`splitRule`). -/
  def dropUnheldEx : Kore.Pattern → Kore.Pattern × List Kore.EVar
    | .exist s x p =>
      let (p', xs) := dropUnheldEx p
      if (freeEVars [] p).contains x.var.ident.name then (.exist s x p', xs) else (p', x :: xs)
    | .app h ss ps => let (ps', xs) := dropUnheldExList ps; (.app h ss ps', xs)
    | .and s ps => let (ps', xs) := dropUnheldExList ps; (.and s ps', xs)
    | p => (p, [])
    termination_by structural p => p
  def dropUnheldExList : List Kore.Pattern → List Kore.Pattern × List Kore.EVar
    | [] => ([], [])
    | p :: ps =>
      let (p', xs) := dropUnheldEx p
      let (ps', ys) := dropUnheldExList ps
      (p' :: ps', xs ++ ys)
    termination_by structural ps => ps
end

mutual
  /-- The disjuncts of a disjunction, nested ones flattened. -/
  def orFlat : Kore.Pattern → List Kore.Pattern
    | .or _ ps => orFlatList ps
    | p => [p]
    termination_by structural p => p
  def orFlatList : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => orFlat p ++ orFlatList ps
    termination_by structural ps => ps
end

/-- `\equals{SortBool{},S}(\and{SortBool{}}(o, G), true)` (or with G first) as `requiresOrSplit`
reads it, where `ax` is the axiom: o a disjunction of at least two terms (no predicate at Bool and
no `\or`, `\top`, `\not` or `\exists` under the applications of one: each has at most one element),
G a variable of sort Bool free nowhere else in `ax`. G's name, and each disjunct's `requires`. -/
def reqOrParts? (ax : Kore.Pattern) (bs s bs' bt : Kore.KSort) (o : Kore.Pattern) (g : Kore.EVar) :
    Option (String × List Kore.Pattern) :=
  let ds := orFlat o
  let isBool := fun (k : Kore.KSort) => sortName? k == some "Bool"
  let g' := g.var.ident.name
  match o with
  | .or .. =>
    if isBool bs && isBool bs' && isBool bt && isBool g.sort && 2 ≤ ds.length &&
        ds.all (fun d => !isPred d && (manyValued? d).isNone) &&
        ((freeEVars [] ax).filter (· == g')).length == 1 then
      some (g', ds.map fun d => .equals bs s d (.dv bt "true"))
    else none
  | _ => none

/-- kompile's `requires A₁ #Or … #Or Aₙ` (`requiresOrSplit`): the `requires` of each disjunct's
rule, and the name of the variable kompile conjoins (`reqOrParts?`). -/
def reqOrSplit? (ax : Kore.Pattern) : Kore.Pattern → Option (String × List Kore.Pattern)
  | .equals bs s (.and bs' [o, .var (.evar g)]) (.dv bt "true") => reqOrParts? ax bs s bs' bt o g
  | .equals bs s (.and bs' [.var (.evar g), o]) (.dv bt "true") => reqOrParts? ax bs s bs' bt o g
  | _ => none

/-- Each element variable of `xs` once, by name, the first kept. -/
def evarsOnce (xs : List Kore.EVar) : List Kore.EVar :=
  xs.foldl (fun acc x => if acc.any (·.var.ident.name == x.var.ident.name) then acc else acc ++ [x]) []

/-- The rules of a rewrite axiom `\rewrites(lhs ∧ req, rhs ∧ ens)`, each an axiom with the axiom's
attributes:
- one per disjunct of the left side that is not empty (`orSplit`: `C[φ ∨ ψ] = C[φ] ∨ C[ψ]`,
  `(φ ∨ ψ) → •R` is `(φ → •R) ∧ (ψ → •R)`, `φ ∨ ⊥ = φ`), and within each one per disjunct of a
  `requires A₁ #Or … #Or Aₙ` (`requiresOrSplit`, its variable G dropped);
- with each variable of the axiom that such a rule does not hold (neither its left side, nor its
  `requires`, right side or `ensures`), and each `\exists` of the left side whose variable is free in
  no part of its body (renamed apart), as an `\exists` around the rule's left side. The axiom's
  sentence for that rule is `∀x̄. (L → •R)` with x̄ not in L or R, which is `(∃x̄. L) → •R`, and
  `∃x. L` is L where x's sort has an element and empty where it has none. `coreOf` reads those
  binders (`unheldBinders`): the rule is read without them where each sort has a value the reader
  exhibits, and refused `unheldVariable` otherwise.
Any other axiom as itself. -/
def splitRule (a : Kore.Axiom) : List Kore.Axiom :=
  match a.pattern with
  | .rewrites s (.and s' [l, r0]) r =>
    let ro := reqOrSplit? a.pattern r0
    if ro.isNone && !hasOr l && (exUnheld? l).isNone then [a]
    else
      let ls := if hasOr l then (orAlts l).filter (!vacuous ·) else [l]
      let reqs := (ro.map (·.2)).getD [r0]
      let consumed := (ro.map (·.1)).toList
      let used := evarNames a.pattern
      let vars := evarsOnce ((freeEVarsS [] a.pattern).filter fun x => !consumed.contains x.var.ident.name)
      ls.flatMap fun l' => reqs.map fun q =>
        let (l'', hs) := dropUnheldEx l'
        let held := freeEVars [] (.rewrites s (.and s' [l'', q]) r)
        let dropped := vars.filter fun x => !held.contains x.var.ident.name
        let hoisted := hs.map fun x => KoreAML.evar (freshIn used (used.length + 1) x.var.ident.name) x.sort
        { a with pattern := .rewrites s (.and s' [(dropped ++ hoisted).foldr (Kore.Pattern.exist s') l'', q]) r }
  | _ => [a]

/-- The binders `splitRule` puts around a rule's left side `l`: its `\exists`s, outermost first,
while each one's variable is free in no part of its body. -/
def unheldBinders : Kore.Pattern → List Kore.EVar
  | .exist _ x p => if (freeEVars [] p).contains x.var.ident.name then [] else x :: unheldBinders p
  | _ => []

mutual
  /-- The conjuncts of `\and{SortBool{}}`, nested ones flattened (a variable among them is a
  conjunct: a condition binds nothing, so `B ∧ X` is not `B #as X`). -/
  def boolConj : Kore.Pattern → List Kore.Pattern
    | .and _ ps => boolConjList ps
    | p => [p]
    termination_by structural p => p
  def boolConjList : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => boolConj p ++ boolConjList ps
    termination_by structural ps => ps
end

/-- The strict conjunction of Bool terms: none for none, the one, or the K sequence of their values
`==K` that of as many `true` (no short-circuiting evaluation skips a part of it). -/
def conjTerms : List Term → Option Term
  | [] => none
  | [c] => some c
  | cs =>
    let seqOf := fun (ts : List Term) =>
      ts.foldr (fun t acc => Term.app kseq [.inj Srt.bool Srt.kitem t, acc]) (Term.app dotk [])
    some (Term.app kEq [seqOf cs, seqOf (cs.map fun _ => .dv Srt.bool (.bool true))])

mutual
  /-- A conjunction under applications. -/
  def hasAnd : Kore.Pattern → Bool
    | .and .. => true
    | .app _ _ ps => hasAndList ps
    | _ => false
    termination_by structural p => p
  def hasAndList : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => hasAnd p || hasAndList ps
    termination_by structural ps => ps
end

/-- An equation's `requires` or `ensures` B (`\equals{SortBool{},S}(B, true)`) as a Bool term (a
rule's is `ruleCondTermsCnj`): `false` where B is
a predicate (`predicateAtBool`), the strict conjunction of B's conjuncts where B is `\and{SortBool{}}`
of several (`andAtBool`), else B. A conjunction under an application of a conjunct is refused
(`patternConnective`): `term` reads `\and(t, X)` as `t #as X`, a binding, which only a left side
makes. -/
def condTerm (N : Names) (vs : List Var) (b : Kore.Pattern) : Rd (Term × List Var) :=
  if isPred b then pure (.dv Srt.bool (.bool false), vs)
  else if (boolConj b).any hasAnd then fail .patternConnective "\\and"
  else match boolConj b with
    | [_] => term N vs b
    | bs => do
      let (ts, vs) ← terms N vs bs
      if ts.length > 1 then N.hookEqE kEq
      pure ((conjTerms ts).getD (.dv Srt.bool (.bool true)), vs)

mutual
  /-- A pattern with at most one element in every model of the text: an element variable, a domain
  value, or the application of a symbol a `functional` axiom of the text states single-valued
  (`Names.fnlSyms`; at its sort arguments, if any, by an axiom over sort variables) to such
  patterns. -/
  def singleValued (N : Names) : Kore.Pattern → Bool
    | .var (.evar _) => true
    | .dv _ _ => true
    | .app h ss ps => N.fnlSyms.contains (h.ident.name, !ss.isEmpty) && singleValuedList N ps
    | _ => false
    termination_by structural p => p
  def singleValuedList (N : Names) : List Kore.Pattern → Bool
    | [] => true
    | p :: ps => singleValued N p && singleValuedList N ps
    termination_by structural ps => ps
end

/-- A condition B (`condTerm`) that an equation reads: not `\and{SortBool{}}` of two or more terms
one of which is not `singleValued`. The conjunction is an intersection: `B₁ ∩ … ∩ Bₙ = {true}` is
`⌈B₁ = true⌉ ∧ … ∧ ⌈Bₙ = true⌉` where each Bᵢ has at most one element, and is not where a Bᵢ has
`true` and another element; the strict conjunction read (`conjTerms`) states the second, which an
equation's `ensures`, and its `requires` under the negation of an `[owise]` or larger-priority
equation, must not strengthen. -/
def eqnCondOK (N : Names) (b : Kore.Pattern) : Bool :=
  isPred b || (boolConj b).length ≤ 1 || (boolConj b).all (singleValued N)

/-- An equation's `requires` or `ensures` B: `condTerm`, refused `patternConnective` (`\and`) where
`eqnCondOK` fails. -/
def eqnCondTerm (N : Names) (vs : List Var) (b : Kore.Pattern) : Rd (Term × List Var) := do
  let r ← condTerm N vs b
  unless eqnCondOK N b do fail .patternConnective "\\and"
  pure r

/-- The conditions `hoist` lifted out of a right side, as Bool terms: B (`condTerm`), and `t ==Int
u` at Int, otherwise `==K` of t and u each a one-item K sequence (`kseq(inj{S,KItem}(t), dotk)`,
`kseq(t, dotk)` at KItem, t at K). The second, `.same`, is reached from a rule's right side only,
where it is a weakening the text entails (`ReadingNote.andTermsWeaker`); `clauseBody` refuses an
equation's. -/
def sideConds (N : Names) : List Var → List SideCond → Rd (List Term × List Var)
  | vs, [] => pure ([], vs)
  | vs, .isTrue b :: cs => do
    let (t, vs) ← condTerm N vs b
    let (ts, vs) ← sideConds N vs cs
    pure (t :: ts, vs)
  | vs, .same s t u :: cs => do
    let (t, vs) ← term N vs t
    let (u, vs) ← term N vs u
    let X ← sortNameE s
    N.hookEqE (if X == "Int" then intEq else kEq)
    let c ← if X == "Int" then pure (Term.app intEq [t, u]) else do
      let s ← N.srtE X
      let wrap := fun (x : Term) => if X == "K" then x
        else Term.app kseq [if X == "KItem" then x else .inj s Srt.kitem x, .app dotk []]
      pure (Term.app kEq [wrap t, wrap u])
    let (ts, vs) ← sideConds N vs cs
    pure (c :: ts, vs)

mutual
  /-- A term without its `#as` bindings. -/
  def stripAs : Term → Term
    | .var i => .var i
    | .app g ts => .app g (stripAsList ts)
    | .inj a b t => .inj a b (stripAs t)
    | .as t _ => stripAs t
    | .dv s lit => .dv s lit
    termination_by structural t => t
  def stripAsList : List Term → List Term
    | [] => []
    | t :: ts => stripAs t :: stripAsList ts
    termination_by structural ts => ts
end

/-- `0` at Int, `false` at Bool, `dotk` at K: a value applying no function. -/
def litValue? (X : String) : Option Kore.Pattern :=
  if X == "Int" then some (.dv (KoreAML.srt X) "0") else if X == "Bool" then some (.dv (KoreAML.srt X) "false")
  else if X == "K" then some (KoreAML.ap "dotk" []) else none

/-- A pattern of the sort `s` that has a value at every match and applies no function: a variable
of `vs` of that sort, else `litValue?`. -/
def valueAt (vs : List Var) (s : Kore.KSort) : Option Kore.Pattern :=
  (sortName? s).bind fun X =>
    match vs.find? (·.sort == X) with
    | some x => some (KoreAML.ev ("Var" ++ x.name) s)
    | none => litValue? X

/-- The right side read in the place of an equation's empty right side `r` (`bottomAsEnsures`), of
the function `f`'s result sort X (`Names.keyFns`, else the sort of `r` when it is `\bottom`): a
pattern with a value at every match that applies no function, `valueAt` else a constructor's value
(`Names.ctorVals`). None when the reader names none of X; the clause then holds `f`'s call at its
arguments. -/
def eqnPlaceholder (N : Names) (vs : List Var) (f : Sym) (r : Kore.Pattern) : Option Kore.Pattern :=
  let X? := (N.keyFns.lookup f).orElse fun _ => match r with
    | .bottom s => sortName? s
    | _ => none
  X?.bind fun X => (valueAt vs (KoreAML.srt X)).orElse fun _ => N.ctorVals.lookup X

/-! ## Equations and rules -/

/-- `\top` (no `requires`) or `\equals{SortBool{},S}(req, \dv{SortBool{}}("true"))`. -/
def req? : Kore.Pattern → Option (Option Kore.Pattern)
  | .top _ => some none
  | .equals _ _ r (.dv _ "true") => some (some r)
  | _ => none

structure RawEqn where
  fn : String
  pats : List Kore.Pattern
  req : Option Kore.Pattern
  competitors : Option (List Kore.Pattern)
  rhs : Kore.Pattern
  attrs : List Kore.AppPattern
  /-- the `ensures` (`Clause.ens`) -/
  ens : Option Kore.Pattern
  /-- read from a projection's selector-domain axiom (`projDomainEqn?`), not from an equation -/
  dom : Bool

/-- The element variables kompile's argument conjunction `\and(\in(X0, p₀), \and(…, \top))`
binds, in order: each membership's left operand; `none` where one is no element variable. -/
def memberVars_lhs : Nat → Kore.Pattern → Option (List Kore.EVar)
  | _, .top _ => some []
  | fuel + 1, .and _ [.in _ _ (.var (.evar x)) _, rest] => do pure (x :: (← memberVars_lhs fuel rest))
  | _, _ => none

/-- Whether an equation's left side `f(ls)` applies `f` to exactly the distinct element variables
the premise's argument conjunction `args` binds, in order. The memberships `Xᵢ ∈ pᵢ` are what the
reader reads as the clause's patterns (`argPats`); the sentence states the value of `f` at the
left side's arguments, so the patterns are the clause's own only where those arguments are the
`Xᵢ` themselves: then `(⋀ Xᵢ ∈ pᵢ) → f(X₀, …) = r` holds at a valuation exactly where the clause
`f(p₀, …) = r` gives its value. Any other left side states the value at other arguments: with a
set variable `@S` there (`f(@S, @S)`), the value at every set's elements (refused `setVariable`,
`lhsSetVar?`); with a repeated variable, another order or a term, the value at other points than
the patterns', which no clause read from the memberships states (not read as an equation). -/
def lhsArgsOK_lhs (ls : List Kore.Pattern) (args : Kore.Pattern) : Bool :=
  match memberVars_lhs eqnFuel args with
  | some xs => decide xs.Nodup && decide (ls = xs.map fun x => .var (.evar x))
  | none => false

def rawEqn? (a : Kore.Axiom) : Option RawEqn :=
  match a.pattern with
  | .implies _ prem (.equals _ _ (.app f ss ls) (.and _ [rhs, en])) => do
    -- the function: `f`, or the instance of a sort-parametric `f` at the sorts `ss` (`instName`)
    let fn ← if ss.isEmpty then some f.ident.name else (ss.mapM sortName?).map (instName f.ident.name)
    -- `\top`, or the `ensures` C as `\equals{SortBool{},S}(C, \dv{SortBool{}}("true"))`
    let ens ← req? en
    match prem with
    | .and _ [.not _ ds, .and _ [r, args]] => do
      guard (lhsArgsOK_lhs ls args)
      pure ⟨fn, ← argPats eqnFuel args, ← req? r, some (← disjuncts eqnFuel ds), rhs, a.attributes, ens, false⟩
    | .and _ [r, args] => do
      guard (lhsArgsOK_lhs ls args)
      pure ⟨fn, ← argPats eqnFuel args, ← req? r, none, rhs, a.attributes, ens, false⟩
    | _ => none
  | _ => none

/-- The pattern of X's projection's equation, at the variable `v`: `kseq(inj{X,KItem}(v), dotk)`,
`kseq(v, dotk)` for KItem, `v` for K. -/
def selectorPat (X : String) (v : Kore.Pattern) : Kore.Pattern :=
  if X == "K" then v else if X == "KItem" then KoreAML.kseq1 v else KoreAML.asK X v

/-- The sort X of a projection's selector-domain axiom (`ReadingNote.projectionDomainAsClause`):
`\implies{R}(\top{R}(), \equals{R,R}(\ceil{X,R}(project:X(K:SortK{})), \exists{R}(V:X,
\equals{SortK{},R}(K:SortK{}, P))))`, K and V variables, P the projection's equation's pattern at V
(`selectorPat`). -/
def projectionDomain? (a : Kore.Axiom) : Option String :=
  match a.pattern with
  | .implies _ (.top _) (.equals _ _ (.ceil sx _ (.app h [] [.var (.evar k)]))
      (.exist _ v (.equals sk _ (.var (.evar k')) body))) => do
    let X ← dropPrefix? "Lblproject'Coln'" h.ident.name
    if sortName? sx == some X && sortName? k.sort == some "K" && sortName? sk == some "K" &&
        decide (k = k') && sortName? v.sort == some X && decide (body = selectorPat X (.var (.evar v)))
    then some X else none
  | _ => none

/-- A selector-domain axiom as the clause it is read as, `project:X(K) = project:X(K) ensures
false` with K a variable of sort K, of priority 200 (`eqnPrio`): `ReadingNote.projectionDomainAsClause`. -/
def projDomainEqn? (a : Kore.Axiom) : Option RawEqn := do
  let X ← projectionDomain? a
  let f := KoreAML.projLabel X
  let k := KoreAML.ev "VarSelectorInput" (KoreAML.srt "K")
  pure ⟨f, [k], none, none, KoreAML.ap f [k], a.attributes, some (.dv (KoreAML.srt "Bool") "false"), true⟩

/-- The equation `project:X(P) = V` of X's projection, P its pattern at the variable V of sort X
(`selectorPat`), without `requires` or `ensures`: the one equation a projection with a
selector-domain axiom may have (`projectionDomainShape`). -/
def projEqnShape (X : String) (e : RawEqn) : Bool :=
  e.req.isNone && e.ens.isNone && e.competitors.isNone && !e.dom &&
  match e.pats, e.rhs with
  | [p], .var (.evar v) => sortName? v.sort == some X && decide (p = selectorPat X (.var (.evar v)))
  | _, _ => false

mutual
  /-- `p` and `q` are one pattern up to a renaming of their element variables that extends `ρ`
  (pairs of a name in `p` and a name in `q`, one-to-one, at one sort): the extended renaming. -/
  def alpha (ρ : List (String × String)) : Kore.Pattern → Kore.Pattern → Option (List (String × String))
    | .var (.evar x), .var (.evar y) =>
      let a := x.var.ident.name
      let b := y.var.ident.name
      if decide (x.sort = y.sort) then
        match ρ.lookup a, ρ.find? (·.2 == b) with
        | some b', _ => if b' == b then some ρ else none
        | none, some _ => none
        | none, none => some ((a, b) :: ρ)
      else none
    | .app f ss ps, .app g ts qs => if decide (f = g) && decide (ss = ts) then alphaList ρ ps qs else none
    | .and s ps, .and t qs => if decide (s = t) then alphaList ρ ps qs else none
    | .equals a b p p', .equals c d q q' =>
      if decide (a = c) && decide (b = d) then (alpha ρ p q).bind (alpha · p' q') else none
    | .in a b p p', .in c d q q' =>
      if decide (a = c) && decide (b = d) then (alpha ρ p q).bind (alpha · p' q') else none
    | p, q => if decide (p = q) then some ρ else none
    termination_by structural p => p
  def alphaList (ρ : List (String × String)) : List Kore.Pattern → List Kore.Pattern → Option (List (String × String))
    | [], [] => some ρ
    | p :: ps, q :: qs => (alpha ρ p q).bind (alphaList · ps qs)
    | _, _ => none
    termination_by structural ps => ps
end

/-! ## A set variable in a function equation's memberships

kompile writes `rule f(@S, @S) => r` as `\in(X₀, @S) ∧ \in(X₁, @S) → f(X₀, X₁) = r`: the set
variable stands as the pattern of the two arguments' memberships (`RawEqn.pats`). The sentence holds
for every set `S` inside the sort; where `S` stands nowhere else, it is the sentence with the two
memberships dropped (`KCore.setvar_in_drop`), read as the clause `f(A, B) => r` with two distinct
variables (`ReadingNote.setVarInDropped`). The lemma states exactly that shape: one conjunct (the
`requires`) before two adjacent memberships in one set variable, then any conjuncts in which it is
not free; so the reader reads only the first two arguments' memberships so, and refuses every other
sentence holding a set variable (`setVariable`), the detail saying why. -/

mutual
  /-- Every variable a pattern holds, a quantifier's or fixpoint's binder included, in pre-order. -/
  def varsOf_svin : Kore.Pattern → List Kore.VarPattern
    | .var v => [v]
    | .app _ _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps | .and _ ps | .or _ ps => varsOfList_svin ps
    | .not _ p | .next _ p | .ceil _ _ p | .floor _ _ p => varsOf_svin p
    | .exist _ x p | .forall _ x p => .evar x :: varsOf_svin p
    | .mu X p | .nu X p => .svar X :: varsOf_svin p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      varsOf_svin p ++ varsOf_svin q
    | .string _ | .top _ | .bottom _ | .dv _ _ => []
    termination_by structural p => p
  def varsOfList_svin : List Kore.Pattern → List Kore.VarPattern
    | [] => []
    | p :: ps => varsOf_svin p ++ varsOfList_svin ps
    termination_by structural ps => ps
end

/-- The set variables among `vs`, each occurrence. -/
def svarsOf_svin (vs : List Kore.VarPattern) : List Kore.SVar :=
  vs.filterMap fun v => match v with
    | .svar X => some X
    | .evar _ => none

/-- The function and the first set variable of an axiom `P → f(ls) = R` whose left side applies
`f` to a set variable, at any depth of its arguments (`f(@S, @S)`, with or without memberships in
the premise): refused `setVariable` (`classifyAxiom`, outside `[simplification]`). As an axiom the
sentence holds at every valuation of `@S`, a set of elements, and `f(@S, @S)` is the union of
`f`'s values at the pairs of its elements; so it states `f(a, a) = r` at a singleton and, at
`{a, b}` with `a ≠ b`, only that `f(a, b)` is `r` or undefined. A clause states one value at every
match of its patterns, and no clause states that. -/
def lhsSetVar? (a : Kore.Axiom) : Option (String × String) :=
  match a.pattern with
  | .implies _ _ (.equals _ _ (.app f _ ls) _) =>
    (svarsOf_svin (varsOfList_svin ls)).head?.map fun X => (f.ident.name, X.var.ident.name)
  | _ => none

/-- An equation's parts other than its arguments' patterns: the `requires`, the right side, the
`ensures` and an `[owise]` equation's exclusion. -/
def RawEqn.rest_svin (e : RawEqn) : List Kore.Pattern :=
  e.req.toList ++ [e.rhs] ++ e.ens.toList ++ e.competitors.getD []

/-- Whether the reader reads an equation through `setVarInDropped`: `.ok none` when it holds no set
variable, `.ok (some X)` when its first two arguments' patterns are the set variable `X` and no other
part of it holds a set variable, and otherwise the refusal's detail. -/
def svinShape (e : RawEqn) : Except String (Option Kore.SVar) :=
  let inPats := svarsOf_svin (varsOfList_svin e.pats)
  let inRest := svarsOf_svin (varsOfList_svin e.rest_svin)
  match inPats ++ inRest with
  | [] => .ok none
  | X :: _ =>
    let n := X.var.ident.name
    let tops := e.pats.zipIdx.filterMap fun (p, i) => match p with
      | .var (.svar Y) => some (Y, i)
      | _ => none
    if !inRest.isEmpty then
      .error s!"{n}: in the right side, the requires, the ensures or an exclusion: the sentence \
        states the function's value at every set holding the arguments; with the set as the value \
        it has no model at a sort with two elements, otherwise its truth reads every subset of the \
        sort"
    else if e.competitors.isSome then
      .error s!"{n}: in an [owise] equation, whose premise is not the shape the memberships are \
        read as dropped in (setvar_in_drop: a requires, then two memberships)"
    else if decide (tops = [(X, 0), (X, 1)]) && inPats.length == 2 then .ok (some X)
    else
      .error s!"{n}: occurrences {inPats.length}, as an argument's whole pattern at the arguments \
        {tops.map (·.2)}: the memberships are read as dropped only for two in \
        one set variable at the first two arguments, the set variable standing nowhere else \
        (setvar_in_drop)"

/-- The disjunct `d` of an `[owise]` equation's exclusion excludes the equation `e`: under its
binders, its arguments and its `requires` are `e`'s up to the names of the variables. -/
def excludes (e : RawEqn) (d : Kore.Pattern) : Bool :=
  match binders eqnFuel d with
  | (_, .and _ [r, args]) => match argPats eqnFuel args, req? r with
    | some ps, some rq => match alphaList [] ps e.pats with
      | some ρ => match rq, e.req with
        | none, none => true
        | some p, some q => (alpha ρ p q).isSome
        | _, _ => false
      | none => false
    | _, _ => false
  | _ => false

/-! ### The disjunct for an equation read through `setVarInDropped`

kompile writes the `[owise]` exclusion's disjunct for `rule f(@S, @S) => r` with one element
variable `G` bound in the set variable's place, `∃G. ⌈req⌉ ∧ X₀ ∈ G ∧ X₁ ∈ G ∧ …`, which holds only
where the two arguments are equal (`KCore.owise_diag_svin`); the equation as read applies at every
pair, and its own disjunct has two distinct variables there. `excludes` matches neither (the
equation's patterns are the set variable). The text's disjunct entails the read one, so the text's
`[owise]` sentence entails the one `Γ` reads (`KCore.owise_disjunct_narrower`): the pair is read,
the `[owise]` equation with the narrower premise (`ReadingNote.owiseDisjunctNarrower`). -/

/-- An element variable named as `g` with the fewest primes appended that is no variable `d` holds. -/
def svinFresh (d : Kore.Pattern) (g : Kore.EVar) : Kore.EVar :=
  let held := (varsOf_svin d).map fun v => match v with
    | .evar x => x.var.ident.name
    | .svar X => X.var.ident.name
  let n := g.var.ident.name
  let cand := fun (j : Nat) => n ++ String.ofList (List.replicate (j + 1) '\'')
  -- each held name is at most one candidate, so one of the first `held.length + 1` is free
  let j := ((List.range (held.length + 1)).find? fun j => !held.contains (cand j)).getD held.length
  ⟨⟨⟨cand j⟩⟩, g.sort⟩

/-- kompile's disjunct as read: `g'` bound just after `g`, in the second argument's membership in
`g`'s place. -/
def svinSplit (g g' : Kore.EVar) : Nat → Kore.Pattern → Kore.Pattern
  | fuel + 1, .exist s x p =>
    if decide (x = g) then .exist s x (.exist s g' (svinSplit g g' fuel p))
    else .exist s x (svinSplit g g' fuel p)
  | _, .and s [r, .and s₀ [m₀, .and s₁ [.in a b x₁ _, rest]]] =>
    .and s [r, .and s₀ [m₀, .and s₁ [.in a b x₁ (.var (.evar g')), rest]]]
  | _, p => p

/-- The disjunct `d` of an `[owise]` equation's exclusion for an equation `e` read through
`setVarInDropped` (`svinShape`, the set variable X): under its binders, its first two argument
patterns are bound element variables of X's sort that stand nowhere else in its arguments and
`requires`, and its other arguments and its `requires` are `e`'s up to the names of the variables
(`alphaList`, `alpha`, as `excludes`). `some (true, d')` when the two are one variable, kompile's
form, `d'` the disjunct as read (`svinSplit`, a fresh variable at the second): the text's premise is
then wider than `Γ`'s (`ReadingNote.owiseDisjunctNarrower`). `some (false, d)` when they are two
distinct variables: the disjunct as read. -/
def svinExcl? (e : RawEqn) (d : Kore.Pattern) : Option (Bool × Kore.Pattern) :=
  match e.pats with
  | .var (.svar _) :: .var (.svar _) :: rest => match svinShape e with
    | .ok (some X) => match binders eqnFuel d with
      | (bs, .and _ [r, args]) => match argPats eqnFuel args, req? r with
        | some (.var (.evar g₀) :: .var (.evar g₁) :: ps), some rq =>
          let others := varsOfList_svin (ps ++ rq.toList)
          let elsewhere := fun (g : Kore.EVar) => others.any fun v => decide (v = .evar g)
          let ok := decide (g₀.sort = X.sort) && decide (g₁.sort = X.sort) &&
            (bs.countP fun b => decide (b = g₀)) == 1 && (bs.countP fun b => decide (b = g₁)) == 1 &&
              !elsewhere g₀ && !elsewhere g₁
          match ok, alphaList [] ps rest with
          | true, some ρ =>
            let reqOk := match rq, e.req with
              | none, none => true
              | some p, some q => (alpha ρ p q).isSome
              | _, _ => false
            if !reqOk then none
            else if decide (g₀ = g₁) then some (true, svinSplit g₀ (svinFresh d g₀) eqnFuel d)
            else some (false, d)
          | _, _ => none
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none

/-- The first disjunct of `ds` that is `svinExcl?`'s for `e`, by its index, as read. -/
def svinPair? (e : RawEqn) (ds : List Kore.Pattern) : Option (Nat × Kore.Pattern) :=
  match e.pats with
  | .var (.svar _) :: .var (.svar _) :: _ =>
    (ds.zipIdx.findSome? fun (d, i) => (svinExcl? e d).map fun (_, d') => (i, d'))
  | _ => none

/-- What an equation no disjunct excludes is paired with: a pattern no exclusion is
(`clauseBody` refuses it, `exclusionShape`). -/
def unexcluded : Kore.Pattern := .bottom (KoreAML.srt "K")

/-- Each equation of `es` with the first disjunct of `ds` not yet taken that excludes it, or with
`unexcluded` when none does. -/
def pairExcl : List RawEqn → List Kore.Pattern → List (RawEqn × Option Kore.Pattern)
  | [], _ => []
  | e :: es, ds => match ds.findIdx? (excludes e) with
    | some i => (e, ds[i]?) :: pairExcl es (ds.eraseIdx i)
    | none => match svinPair? e ds with
      | some (i, d) => (e, some d) :: pairExcl es (ds.eraseIdx i)
      | none => (e, some unexcluded) :: pairExcl es ds

/-- The two symbols of a symbol-overload axiom. -/
def overloadSyms? (as : List Kore.AppPattern) : Option (String × String) :=
  match as with
  | [⟨⟨⟨"symbol-overload"⟩⟩, [], [.app f [] [], .app g [] []]⟩] => some (f.ident.name, g.ident.name)
  | _ => none

/-- An equation that no premise of the text negates, read as an `aside` clause: one declared
`non-executable`, which kompile's `[owise]` premise does not negate, or a symbol-overload axiom
(`overloadEqn?`), which states its equation with no premise and which no `[owise]` premise
negates (the premise's disjuncts are as many as the other equations, `fnFrom`). A symbol-overload
axiom is an equation whose one attribute is `symbol-overload{}(f(), g())` (`overloadSyms?`), as
`overloadEqn?` reads it and `ClausePres.overload` records it; an equation `P → f(p̄) = r` that
carries the attribute beside others states its equation under its premise as any equation does,
and the attribute adds no sentence. -/
def nonExec (e : RawEqn) : Bool := hasAttr e.attrs "non-executable" || (overloadSyms? e.attrs).isSome

/-- As `pairExcl`, the equations declared `non-executable` (`nonExec`) with no disjunct: no
disjunct of an `[owise]` equation's exclusion excludes them. -/
def pairExclAside : List RawEqn → List Kore.Pattern → List (RawEqn × Option Kore.Pattern)
  | [], _ => []
  | e :: es, ds => if nonExec e then (e, none) :: pairExclAside es ds else
    match ds.findIdx? (excludes e) with
    | some i => (e, ds[i]?) :: pairExclAside es (ds.eraseIdx i)
    | none => match svinPair? e ds with
      | some (i, d) => (e, some d) :: pairExclAside es (ds.eraseIdx i)
      | none => (e, some unexcluded) :: pairExclAside es ds

mutual
  /-- `p` with each element variable `X` not named `Var…` renamed `VarX`: an overload axiom's
  variables are `K0`, `K1`, … -/
  def varNamed : Kore.Pattern → Kore.Pattern
    | .var (.evar x) => match dropPrefix? "Var" x.var.ident.name with
      | some _ => .var (.evar x)
      | none => .var (.evar { x with var := { ident := { name := "Var" ++ x.var.ident.name } } })
    | .app h ss ps => .app h ss (varNamedList ps)
    | .and s ps => .and s (varNamedList ps)
    | p => p
    termination_by structural p => p
  def varNamedList : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => varNamed p :: varNamedList ps
    termination_by structural ps => ps
end

/-- K's `append` (`append(K1, K2)`, the concatenation of two K sequences) as the text states it: the
equations of the prelude's module KSEQ, which every text holds (`preludeModules`), `append(dotk, T) =
T` and `append(kseq(K, KS), T) = kseq(K, append(KS, T))`, read as a user's equations are, their
variables named `Var…` (`varNamed`) and each given the id `KSEQ.append.i`: the prelude writes neither.
The clauses of `append` where a read sentence applies it (`envOf`, `Env.genFns`). -/
def appendEqns : List RawEqn :=
  let eqs := (preludeModules.flatMap (·.sentences)).filterMap fun s => match s with
    | .axiom a => (rawEqn? a).bind fun e => if e.fn == "append" then some e else none
    | _ => none
  eqs.zipIdx.map fun (e, i) =>
    { e with pats := varNamedList e.pats, rhs := varNamed e.rhs,
             attrs := [⟨⟨⟨"UNIQUE'Unds'ID"⟩⟩, [], [.string s!"KSEQ.append.{i}"]⟩] }

/-- A symbol-overload axiom as an equation of the overloading symbol `f`:
`\equals(f(p̄), r) [symbol-overload{}(f(), g())]` states `f(p̄) = r` (`f(inj{Int,Gas}(K)) =
inj{Int,Gas}(g(K))`). When `f` is a function (`envOf`) it is a clause of `f`, `aside` (`nonExec`)
and of priority 0 (`eqnPrio`): the sentence states `f(p̄) = r` wherever `p̄` matches, with no
premise, so its clause is the one below which no clause is (`Eval.clause` reads no clause
before it) and which no other clause's premise negates. -/
def overloadEqn? (a : Kore.Axiom) : Option RawEqn :=
  match a.attributes, a.pattern with
  | [⟨⟨⟨"symbol-overload"⟩⟩, [], [.app f [] [], .app _ [] []]⟩], .equals _ _ (.app h [] args) rhs =>
    if h.ident.name == f.ident.name then some ⟨f.ident.name, varNamedList args, none, none, varNamed rhs, a.attributes, none, false⟩
    else none
  | _, _ => none

/-- The argument `lift A B x` of an overload equation's left side, x a variable of sort A: the variable
itself when A = B, `inj{A,B}(x)` otherwise; the variable's name. -/
def liftVar? (A B : String) : Kore.Pattern → Option String
  | .var (.evar x) => if A == B && sortName? x.sort == some A then some x.var.ident.name else none
  | .app h [S, T] [.var (.evar x)] =>
    if A != B && h.ident.name == "inj" && sortName? S == some A && sortName? T == some B &&
      sortName? x.sort == some A then some x.var.ident.name else none
  | _ => none

/-- What the symbol-overload axiom `e` (`overloadEqn?`) of the overloading symbol `fd` over the
symbol `gd` has that the kernel's overload equation `f(lift x̄) = lift (g(x̄))` (`OvlSig`,
`KoreAML.Cons.ovlEqItem`) has not, or `none`: as many arguments as g has, the i-th `lift Aᵢ Bᵢ xᵢ`
(`liftVar?`) for g's i-th argument sort Aᵢ and f's Bᵢ, the variables distinct, and the right side
`lift Rg Rf (g(x̄))` for g's result sort Rg and f's Rf. -/
def ovlEqMissing (fd gd : Kore.SentenceSymbol) (e : RawEqn) : Option String :=
  let g := gd.symbol.ident.ident.name
  match fd.sorts.mapM sortName?, gd.sorts.mapM sortName?, sortName? fd.sort, sortName? gd.sort with
  | some bs, some as, some rf, some rg =>
    if as.length != bs.length then some s!"{g} has {as.length} arguments, the overloading symbol {bs.length}"
    else if e.pats.length != as.length then some "an argument count other than the symbols'"
    else match ((as.zip bs).zip e.pats).mapM (fun ((A, B), p) => liftVar? A B p) with
      | none => some "an argument other than a variable of the overloaded symbol's argument sort (injected where the argument sorts differ)"
      | some xs =>
        if xs.eraseDups.length != xs.length then some "a variable repeated among the arguments"
        else
          let inner := if rg == rf then some e.rhs else match e.rhs with
            | .app h [S, T] [q] =>
              if h.ident.name == "inj" && sortName? S == some rg && sortName? T == some rf then some q else none
            | _ => none
          match inner with
          | some (.app h [] qs) =>
            if h.ident.name == g && qs.mapM (fun q => match q with
                | .var (.evar x) => some x.var.ident.name
                | _ => none) == some xs then none
            else some s!"a right side other than {g} applied to the arguments' variables"
          | _ => some s!"a right side other than an application of {g} (injected where the result sorts differ)"
  | _, _, _, _ => some "a sort-parametric symbol"

/-- The overloading symbols in an order in which each comes after the overloading symbols it
overloads (`overloadsOK`): rounds placing, in their order, those whose overloaded overloading
symbols are placed; `none` when a round places none (the overloads are cyclic). -/
def ovlOrder : Nat → List String → List (String × List String) → Option (List String)
  | _, done, [] => some done
  | 0, _, _ :: _ => none
  | n + 1, done, pend =>
    match pend.filter (fun (_, gs) => gs.all done.contains) with
    | [] => none
    | ready => ovlOrder n (done ++ ready.map (·.1)) (pend.filter fun (_, gs) => !gs.all done.contains)

/-- The location of a sentence written without one (a generated function and its equations). -/
def noLoc : KoreAML.Loc := ⟨0, 0, 0, 0⟩

/-- An equation's unique id and location; for an equation without a source, which kompile
generates without a location, its id and `noLoc`. -/
def eqnInfo? (as : List Kore.AppPattern) : Option KoreAML.Meta :=
  (info? as).orElse fun _ => if (source? as).isNone then
    match attrStr? as "UNIQUE'Unds'ID" with
    | some u => some ⟨u, noLoc⟩
    -- a symbol-overload axiom has neither id nor place
    | none => if (overloadSyms? as).isSome then some ⟨"", noLoc⟩ else none
  else none

/-- A sentence's source when it is not the main module's `msrc`. -/
def srcOver (msrc : String) (attrs : List Kore.AppPattern) : Option String :=
  (source? attrs).bind fun s => if s == msrc then none else some s

/-- An equation's priority, with it where the text writes it `priority{}("n")`
(`ClausePres.prioAttr`): `priority{}("n")`'s n; otherwise 0 for a symbol-overload axiom
(`overloadEqn?`, `overloadSyms?`: the attribute is its one attribute, which `emit` writes back,
`ClausePres.overload`), 200
for an `[owise]` equation (one with competitors) and 50 for the others. -/
def eqnPrio (e : RawEqn) : Option Nat × Nat :=
  -- `digitsVal`, not `String.toNat?` (`ruleBody`)
  let explicit := (attrStr? e.attrs "priority").bind fun s => digitsVal s.toList 0
  (explicit, explicit.getD (if (overloadSyms? e.attrs).isSome then 0
    else if e.competitors.isSome || e.dom then 200 else 50))

/-- The names of the two variables read in the set variable `X`'s place (`svinShape`): `X`'s name
with primes and 0, 1, the fewest primes for which neither is an element variable the equation
holds, so that neither is merged with a variable of the text. -/
def svinNames (e : RawEqn) (X : Kore.SVar) : String × String :=
  let held := (varsOfList_svin (e.pats ++ e.rest_svin)).filterMap fun v => match v with
    | .evar x => some x.var.ident.name
    | .svar _ => none
  let base := (dropPrefix? "Var" X.var.ident.name).getD X.var.ident.name
  let cand := fun (j i : Nat) => base ++ String.ofList (List.replicate (j + 1) '\'') ++ toString i
  -- each held name is at most one candidate, so one of the first `held.length + 1` is free
  let j := ((List.range (held.length + 1)).find? fun j =>
    !held.contains ("Var" ++ cand j 0) && !held.contains ("Var" ++ cand j 1)).getD held.length
  (cand j 0, cand j 1)

/-- The first attribute of a function equation that `attrVerdict` refuses at class `equation`
(`equationAttribute`), with its name and why. An inert key is one whose verdict is that the
equation states what it states with it or without it; the others are read. -/
def eqnAttrFault? (as : List Kore.AppPattern) : Option String :=
  as.findSome? fun ap =>
    let n := ap.head.ident.name
    match attrVerdictOf .equation .equationAttribute n with
    | .refused _ w => some s!"{n} on a function equation: {w}"
    | _ => none

/-- An equation's argument patterns as terms: through `setVarInDropped` the first two are two
variables (`svinShape`, `svinNames`). Beside an `[owise]` equation the disjunct paired with it is
one of `svinExcl?`'s forms, handed on as read (`pairExcl`); any other is `exclusionShape`
(`clauseBody`). -/
def svinPats (N : Names) (e : RawEqn) : Rd (List Term × List Var) :=
  match svinShape e with
  | .error d => fail .setVariable d
  | .ok none => terms N [] e.pats
  | .ok (some X) => do
    let s ← sortNameE X.sort
    let (n₀, n₁) := svinNames e X
    let (ts, vs) ← terms N [⟨n₀, s⟩, ⟨n₁, s⟩] (e.pats.drop 2)
    pure (.var 0 :: .var 1 :: ts, vs)

def clauseBody (N : Names) (msrc : String) (e : RawEqn) (excl : Option Kore.Pattern) : Rd (Clause × ClausePres) := do
  if let some d := eqnAttrFault? e.attrs then fail .equationAttribute d
  let (pats, vs) ← svinPats N e
  let np := vs.length
  let (req, vs) ← match e.req with
    | none => pure (none, vs)
    | some r => do let (t, vs) ← eqnCondTerm N vs r; pure (some t, vs)
  -- a variable the arguments do not bind is read; in a condition the values do not decide it is
  -- refused once the definition is built (`clauseRefusal`)
  -- the `ensures`, the clause's `ens`: part of the right side, not of whether it applies
  let (ens, vs) ← match e.ens with
    | none => pure (none, vs)
    | some c => do let (t, vs) ← eqnCondTerm N vs c; pure (some t, vs)
  -- the right side's conjunctions as `ensures`, and an empty right side as the `ensures` false
  -- (`hoist`); in its place a value of the result sort applying no function, else the call at the
  -- arguments (`eqnPlaceholder`)
  let (r, conds, empty) := hoist e.rhs
  let (rhs, ens, vs) ← if empty then do
      let f ← N.symE e.fn
      match eqnPlaceholder N vs f r with
      | some r' => do let (t, vs) ← term N vs r'; pure (t, some (Term.dv Srt.bool (.bool false)), vs)
      | none => pure (Term.app f (stripAsList pats), some (Term.dv Srt.bool (.bool false)), vs)
    else do
      if let some c := manyValued? r then fail .manyValuedRightSide c
      -- `t ∧ u` of two terms is `t ∩ u`: no clause's `rhs` and `ens` state it (`andAsEnsures`)
      if conds.any (fun c => match c with | .same .. => true | .isTrue _ => false) then
        fail .patternConnective "\\and"
      let (rhs, vs) ← term N vs r
      let (cs, vs) ← sideConds N vs conds
      -- a lifted condition is part of the `ensures`: its `\and{SortBool{}}` as `eqnCondTerm`'s
      unless conds.all (fun c => match c with | .isTrue b => eqnCondOK N b | .same .. => true) do
        fail .patternConnective "\\and"
      if ens.toList.length + cs.length > 1 then N.hookEqE kEq
      pure (rhs, if cs.isEmpty then ens else conjTerms (ens.toList ++ cs), vs)
  let m ← need (eqnInfo? e.attrs) .sentenceInfo
  let (explicit, prio) := eqnPrio e
  -- a `non-executable` equation: a clause that no `[owise]` premise negates (`Clause.aside`)
  let aside := nonExec e
  match excl with
  | none => pure ({ vars := ← varSorts N vs, pats, req, rhs, ens, prio, aside },
      ⟨vs.map (·.name), m, vs.map (·.name), attrStr? e.attrs "label", srcOver msrc e.attrs, explicit.isSome,
       (overloadSyms? e.attrs).map (·.2)⟩)
  | some ex =>
    let (bs, body) := binders eqnFuel ex
    let (_, evs) ← match body with
      | .and _ [r, args] => do
        let (ps, evs) ← terms N [] (← need (argPats eqnFuel args) .exclusionShape)
        match ← need (req? r) .requiresShape with
        | none => pure (ps, evs)
        | some rq => do let (_, evs) ← condTerm N evs rq; pure (ps, evs)
      | _ => fail .exclusionShape
    let π ← need (bs.mapM fun b => do
      let n ← dropPrefix? "Var" b.var.ident.name
      evs.findIdx? (·.name == n)) .exclusionShape
    -- every variable of the disjunct is bound: a free one would name the `[owise]` equation's
    unless (List.range evs.length).all (π.contains ·) do fail .exclusionShape
    let inv := fun (i : Nat) => (π.idxOf? i).getD i
    -- the disjunct's variables in its binders' order, then those only the right side or the
    -- `ensures` holds, at their places (`inv` keeps an index past the disjunct's), in the names of
    -- both the clause and its exclusion
    let vs' := π.map (vs.getD · default) ++ vs.drop evs.length
    let vars ← varSorts N vs'
    pure ({ vars, pats := Term.reindexList inv pats, req := req.map (Term.reindex inv),
            rhs := Term.reindex inv rhs, ens := ens.map (Term.reindex inv), prio, aside },
          ⟨vs'.map (·.name), m, π.map (fun i => (evs.getD i default).name) ++ (vs.drop evs.length).map (·.name),
           attrStr? e.attrs "label",
           srcOver msrc e.attrs, explicit.isSome, (overloadSyms? e.attrs).map (·.2)⟩)

/-- A function's clause from its equation (and the `[owise]` equation's exclusion of it). -/
def clause? (N : Names) (msrc : String) (e : RawEqn) (excl : Option Kore.Pattern) : Rd (Clause × ClausePres) :=
  Rd.within (.attrs e.attrs) (clauseBody N msrc e excl)

/-- The equations of the function `label` that become clauses, each with the disjunct of the
`owise` equation's exclusion that excludes it (if the function has an `owise` equation): matched
by content, whatever the disjuncts' order; a `non-executable` equation with none (`pairExclAside`). -/
def fnPairs (eqs : List RawEqn) (label : String) : List (RawEqn × Option Kore.Pattern) :=
  let eqs := eqs.filter fun e => e.fn == label && !e.dom
  let plain := eqs.filter (·.competitors.isNone)
  match (eqs.find? (·.competitors.isSome)).bind (·.competitors) with
  | none => plain.map (·, none)
  | some comps => pairExclAside plain comps

def clauseOf (N : Names) (msrc : String) : RawEqn × Option Kore.Pattern → Rd (Clause × ClausePres)
  | (e, ex) => clause? N msrc e ex

/-- The clauses of the function `label`. -/
def fnClauses (N : Names) (msrc : String) (eqs : List RawEqn) (label : String) :
    Rd (List (Clause × ClausePres)) :=
  (fnPairs eqs label).mapM (clauseOf N msrc)

/-- The function `label`, from its clauses `cl` (`fnClauses`, or a list proved equal to it). -/
def fnFrom (N : Names) (msrc : String) (fsrc : Option String) (eqs : List RawEqn)
    (cl : Rd (List (Clause × ClausePres))) (label : String) (kywd : Option String)
    (args : List String) (res : String) (l : KoreAML.Loc) (total : Bool) : Rd (Fn × FnPres) := do
  let own := eqs.filter fun e => e.fn == label && !e.dom
  -- the clauses read from selector-domain axioms (`ReadingNote.projectionDomainAsClause`)
  let doms := eqs.filter fun e => e.fn == label && e.dom
  -- the `[owise]` equations, in text order
  let ows := own.filter (·.competitors.isSome)
  -- each `[owise]` equation's exclusion names the function's other equations but those declared
  -- `non-executable` (`nonExec`), and nothing else: one disjunct for each (each is matched to the
  -- one it excludes, `fnPairs` for the first)
  let plain := own.filter (·.competitors.isNone)
  let exec := plain.filter (!nonExec ·)
  for e in ows do
    unless (e.competitors.getD []).length == exec.length do
      Rd.within (.attrs e.attrs) (fail .exclusionShape)
    -- the exclusion orders the `[owise]` equation after every other one; priority 200 orders it
    -- after the smaller priorities only, so it must have priority 200 and no other 200 or more
    unless (eqnPrio e).2 == 200 do
      Rd.within (.attrs e.attrs) (fail .owisePriority)
  if !ows.isEmpty then
    if let some e' := plain.find? (fun e' => 200 ≤ (eqnPrio e').2) then
      Rd.within (.attrs e'.attrs) (fail .owisePriority)
  -- the second and later `[owise]` equations' exclusions, matched by content as the first's is
  -- (`fnPairs`, checked by `clauseBody`): an `[owise]` equation's premise negates the other
  -- equations, not the other `[owise]` equations, so these are clauses of priority 200 beside the
  -- first, unordered among themselves as any clauses of one priority are
  for e in ows.drop 1 do
    let _ ← (pairExcl exec (e.competitors.getD [])).mapM (clauseOf N msrc)
  let clauses ← cl
  -- the `[owise]` equations: clauses of priority 200, after the others
  let owise ← ows.mapM fun e => clause? N msrc e none
  -- a selector-domain axiom: the projection's one equation is `project:X(kseq(inj{X,KItem}(V),
  -- dotk)) = V` without `requires`, and the axiom is one; then its clause, of priority 200, last
  if let some d := doms.head? then
    unless doms.length == 1 && ows.isEmpty && plain.length == 1 && plain.all (projEqnShape res ·) do
      Rd.within (.attrs d.attrs) (fail .projectionDomainShape label)
  let domCls ← doms.mapM fun e => clause? N msrc e none
  let cls := clauses ++ owise ++ domCls
  pure (⟨← N.symE label, ← args.mapM N.srtE, ← N.srtE res, cls.map (·.1), total⟩,
        ⟨kywd, l, cls.map (·.2), fsrc, none⟩)

def fn? (N : Names) (msrc : String) (fsrc : Option String) (eqs : List RawEqn) (label : String) (kywd : Option String)
    (args : List String) (res : String) (l : KoreAML.Loc) (total : Bool) : Rd (Fn × FnPres) :=
  fnFrom N msrc fsrc eqs (fnClauses N msrc eqs label) label kywd args res l total

/-- A rewrite axiom's `ensures`: `\top` (none) or `\equals{SortBool{},S}(C, \dv{SortBool{}}("true"))`
(`some C`). -/
def ruleEns? (a : Kore.Axiom) : Option (Option Kore.Pattern) :=
  match a.pattern with
  | .rewrites _ _ (.and _ [_, en]) => req? en
  | _ => none

/-- The first attribute of a rewrite axiom that `attrVerdict` refuses at class `rule`
(`ruleAttribute`), with its name and why. The keys read are its unique id, label, priority, place
and `owise` (priority 200; beside `priority{}("n")` with n other than 200 refused,
`ruleOwisePrioFault?`); the inert ones say nothing of where or how the rule applies, and are kept
in the presentation (`inertRuleAttrs`, `inertArgAttrs`, with no argument or a string). -/
def ruleAttrFault? (as : List Kore.AppPattern) : Option String :=
  as.findSome? fun ap =>
    let n := ap.head.ident.name
    match attrVerdictOf .rule .ruleAttribute n with
    | .refused _ w => some s!"{n} on a \\rewrites axiom: {w}"
    | _ => none

/-- A rewrite axiom carrying `owise{}()` beside `priority{}("n")` with n other than 200
(`ruleAttribute`), with why. Each key is a mark of the rule's priority: `owise` sets it to 200,
`priority` to n, and no sentence of the text says which holds when both are written. Where n is
not 200 the two readings give different steps: a rule of a priority p between n and 200 (either end
included where the other is strictly ordered) that matches the same configuration is tried before
the rule under one reading and after it, or beside it, under the other. With n = 200 the two marks
state the same priority and the rule is read with it. -/
def ruleOwisePrioFault? (as : List Kore.AppPattern) : Option String :=
  if as.any (fun ap => ap.head.ident.name == "owise") then
    match attrStr? as "priority" with
    | some s =>
      if digitsVal s.toList 0 == some 200 then none
      else some s!"owise and priority\{}(\"{s}\") on a \\rewrites axiom: owise sets the rule's priority to 200 and priority to {s}, two priorities that order the rule differently against a rule of a priority between them matching the same configuration, and no sentence of the text chooses between them"
    | none => none
  else none

/-- The binders of `\exists` around a pattern, outermost first, and the pattern under them. -/
def peelExists : Kore.Pattern → List Kore.EVar × Kore.Pattern
  | .exist _ x p => (x :: (peelExists p).1, (peelExists p).2)
  | p => ([], p)

/-- The `\exists` binders heading a rewrite axiom's right side renamed apart: each binder whose
name is one of `outer` (the names the left side and the `requires` hold) gets, with the occurrences
it binds, its name primed until no name of `used` is it (`freshIn`, as `lhsBind` names its
variables); the pattern and the names then used. The innermost binder first, so a name chosen for
one binder is not chosen for one around it; `renameEVar` compares name and sort and stops at a
binder of the same variable, so of two binders of one variable the inner one's occurrences are
renamed with the inner one. (`ReadingNote.existsRenamedApart`) -/
def exApart (outer : List String) : List String → Kore.Pattern → Kore.Pattern × List String
  | used, .exist s x p =>
    let (p', used) := exApart outer used p
    if outer.contains x.var.ident.name then
      let y := KoreAML.evar (freshIn used (used.length + 1) x.var.ident.name) x.sort
      (.exist s y (renameEVar x y p'), y.var.ident.name :: used)
    else (.exist s x p', used)
  | used, p => (p, used)

/-- A right-side binder of the rewrite axiom whose left side is `l`, `requires` `r0` and right
side `rx` has a name the left side or the `requires` holds (`ReadingNote.existsRenamedApart`). -/
def exRenamed (l r0 rx : Kore.Pattern) : Bool :=
  (peelExists rx).1.any fun x => (evarNames l ++ evarNames r0).contains x.var.ident.name

/-- The right side `rx` of the rewrite axiom whose pattern is `ax`, left side `l` and `requires`
`r0`, with its binders renamed apart from the names `l` and `r0` hold (`exApart`). The fresh names
are none of the axiom's nor of the left side as read (`lhsBound`, whose fresh names are primed
from the axiom's names too). -/
def rhsApart (ax l r0 rx : Kore.Pattern) : Kore.Pattern :=
  if exRenamed l r0 rx then
    (exApart (evarNames l ++ evarNames r0) (evarNames ax ++ evarNames (lhsBound ax l)) rx).1
  else rx

/-- The patterns of a rule's right side `r` and `ensures` `en` whose variables the reader reads:
the `ensures`' term unless it is a predicate (`predicateAtBool`, read as `false`), and, unless the
right side is empty (`hoist`; `bottomAsEnsures`, it is then not read), the right side without its
conjunctions and their conditions (`sideConds`). -/
def rhsReadParts (r en : Kore.Pattern) : List Kore.Pattern :=
  let cond := fun (b : Kore.Pattern) => if isPred b then [] else [b]
  let (r', conds, empty) := hoist r
  (match req? en with
    | some (some b) => cond b
    | _ => []) ++
  if empty then [] else r' :: conds.flatMap fun (c : SideCond) => match c with
    | .isTrue b => cond b
    | .same _ t u => [t, u]

/-- The binders `xs` (outermost first) of a right side `\exists(x̄, \and(r, en))` that bind
something: those whose variable, name and sort, is free in a part the reader reads
(`rhsReadParts`), and of several binders of one variable the innermost. The others bind nothing
and are read dropped (`ReadingNote.existsDropped`). -/
def exKept (xs : List Kore.EVar) (r en : Kore.Pattern) : List Kore.EVar :=
  let held := (rhsReadParts r en).flatMap (freeEVarsS [])
  let rec last : List Kore.EVar → List Kore.EVar
    | [] => []
    | x :: xs => if xs.any (fun y => decide (y = x)) then last xs else x :: last xs
  last (xs.filter fun x => held.any fun y => decide (y = x))

/-- The indices in `vs` of the binders `xs` of a right side, in the text's order of nesting: each
looked up by name and sort among the variables read after the left side's and the `requires`'
(index at least `n0`). A binder not found there binds nothing and has no index. -/
def exIndices (vs : List Var) (n0 : Nat) (xs : List Kore.EVar) : List Nat :=
  xs.filterMap fun x =>
    match dropPrefix? "Var" x.var.ident.name, sortName? x.sort with
    | some n, some s => match vs.findIdx? (·.name == n) with
      | some i => if n0 ≤ i && (vs.getD i default).sort == s then some i else none
      | none => none
    | _, _ => none

/-- A rule's `requires` or `ensures` B (`\equals{SortBool{},S}(B, true)`) as the list of its
conjuncts, Bool terms: `[false]` where B is a predicate (`predicateAtBool`), each conjunct of B
where B is `\and{SortBool{}}` of several (`andAtBool`), else `[B]`. A conjunction under an
application of a conjunct is refused (`patternConnective`), as by `condTerm`. -/
def ruleCondTermsCnj (N : Names) (vs : List Var) (b : Kore.Pattern) : Rd (List Term × List Var) :=
  if isPred b then pure ([.dv Srt.bool (.bool false)], vs)
  else if (boolConj b).any hasAnd then fail .patternConnective "\\and"
  else do
    let (ts, vs) ← terms N vs (boolConj b)
    pure (if ts.isEmpty then [.dv Srt.bool (.bool true)] else ts, vs)

/-- The conditions `hoist` lifted out of a rule's right side, as Bool terms: each conjunct of a
`{B #Equals true}` (`ruleCondTermsCnj`), and the term `sideConds` writes for a `t ∧ u` of two terms
(`.same`). -/
def ruleSideCondsCnj (N : Names) : List Var → List SideCond → Rd (List Term × List Var)
  | vs, [] => pure ([], vs)
  | vs, .isTrue b :: cs => do
    let (ts, vs) ← ruleCondTermsCnj N vs b
    let (us, vs) ← ruleSideCondsCnj N vs cs
    pure (ts ++ us, vs)
  | vs, c :: cs => do
    let (ts, vs) ← sideConds N vs [c]
    let (us, vs) ← ruleSideCondsCnj N vs cs
    pure (ts ++ us, vs)

/-- The conjunction of the conditions `B = true`, one per term B, `\top` for none. -/
def ruleEqTrueCnj (ts : List Term) : Cond :=
  ovlCutConj (ts.map fun t => Cond.equals Srt.bool t (.dv Srt.bool (.bool true)))

/-- A rewrite axiom `\rewrites(\and(lhs, req), \exists(x̄, \and(rhs, ens)))`, x̄ possibly empty and
renamed apart from the names the left side and the `requires` hold (`rhsApart`). -/
def ruleBodyAnd (N : Names) (msrc : String) (a : Kore.Axiom) (l r0 : Kore.Pattern) (xs : List Kore.EVar)
    (r en : Kore.Pattern) : Rd (Rule × RulePres) := do
    let ens ← need (req? en) .ruleShape
    if let some d := ruleAttrFault? a.attributes then fail .ruleAttribute d
    if let some d := ruleOwisePrioFault? a.attributes then fail .ruleAttribute d
    -- `\top` and `\exists` in the left side as variables of the rule (`lhsBound`)
    let (lhs, vs) ← term N [] (lhsBound a.pattern l)
    -- a variable the left side does not bind (in the `requires`, the `ensures` or the right side)
    -- is read after the left side's; where the values do not decide the rule it is refused once
    -- the definition is built (`openRefusal`)
    -- the `requires`' conjuncts: the first is `req`, each other `B = true` a conjunct of `pre`
    let (reqs, vs) ← match ← need (req? r0) .requiresShape with
      | none => pure ([], vs)
      | some q => ruleCondTermsCnj N vs q
    let n0 := vs.length
    let (enss, vs) ← match ens with
      | none => pure ([], vs)
      | some e => ruleCondTermsCnj N vs e
    -- the right side's binders that bind something
    let kept := exKept xs r en
    -- the right side's conjunctions as conditions, and an empty right side as the `ensures` false
    -- (`hoist`), the left side without `#as` in its place (after `keyCut`); of the right side's
    -- conditions (the `ensures`' conjuncts, then the lifted ones) the first is `ens`, each other
    -- `B = true` a conjunct of `post`
    let (r, conds, empty) := hoist r
    let (rhs, ens, post, vs) ← if empty then
        pure (stripAs lhs, some (Term.dv Srt.bool (.bool false)), Cond.top, vs)
      else do
        let (rhs, vs) ← term N vs r
        let (cs, vs) ← ruleSideCondsCnj N vs conds
        let es := enss ++ cs
        pure (rhs, es.head?, ruleEqTrueCnj es.tail, vs)
    -- the right side's existential variables, in the text's order of nesting: the binders that
    -- bind something, looked up before `keyCut` adds its variables
    let exs := exIndices vs n0 kept
    -- a map key of the left side applying a function of the definition's own: a fresh variable,
    -- its membership in the application a conjunct of `pre` (`keyCut`)
    let (lhs, vs, keys) ← keyCut N lhs vs
    -- an application of a function-overloaded symbol in the left side: a fresh variable, its
    -- membership in the application a conjunct of `pre` (`ovlCut`)
    let (lhs, vs, pre) ← ovlCut N lhs vs
    let pre := ovlCutConj (keys ++ (if pre.isTop then [] else [pre]) ++
      (if reqs.length ≤ 1 then [] else [ruleEqTrueCnj reqs.tail]))
    let req := reqs.head?
    let rhs := if empty then stripAs lhs else rhs
    let plain := a.attributes.filterMap fun ap =>
      if ap.sorts.isEmpty && ap.args.isEmpty then some ap.head.ident.name else none
    -- `digitsVal`, not `String.toNat?`: the latter reaches an opaque well-founded fixpoint in
    -- Lean v4.34.0's string iterators, which the kernel cannot unfold (test/OpaqueAudit.lean)
    let explicit := (attrStr? a.attributes "priority").bind fun s => digitsVal s.toList 0
    let prio := match explicit with
      | some n => n
      | none => if plain.contains "owise" then 200 else 50
    pure ({ vars := ← varSorts N vs, lhs, req, rhs, ens, prio, exs, pre, post },
          ⟨vs.map (·.name), ← need (info? a.attributes) .sentenceInfo, attrStr? a.attributes "label",
           plain.filter (· != "owise"), explicit.isSome,
           a.attributes.filterMap (fun ap => match ap.sorts, ap.args with
             | [], [.string v] =>
               let n := ap.head.ident.name
               if ["UNIQUE'Unds'ID", "label", "priority", "org'Stop'kframework'Stop'attributes'Stop'Location",
                   "org'Stop'kframework'Stop'attributes'Stop'Source"].contains n then none else some (n, v)
             | _, _ => none),
           srcOver msrc a.attributes⟩)

/-- A rewrite axiom's rule: its left side, its `requires`, its right side and its `ensures` as
written, `\rewrites(lhs ∧ req, ∃x̄. (rhs ∧ ens))` with `req` and `ens` each `\top` (none) or
`\equals{SortBool{},S}(C, true)` (`some C`), and x̄ the rule's existential variables (`exs`, in the
text's order of nesting). The `ensures` is part of the right side (`Step.rule`'s `hens`): it does
not decide where the rule applies (`NotApplies` reads the left side and the `requires`).

The right side's `\exists` binders are peeled before the form is chosen: the left side and the
body under the binders are read, or refused, as those of the axiom without binders. A binder is
read by the sentence's scoping: one whose name the left side or the `requires` holds is renamed
apart (`rhsApart`, `ReadingNote.existsRenamedApart`), and one that binds nothing is dropped
(`exKept`, `ReadingNote.existsDropped`); no binder is refused. -/
def ruleBodyRead (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  match a.pattern with
  | .rewrites s (.and s' [l, r0]) rx =>
    match peelExists (rhsApart a.pattern l r0 rx) with
    | (xs, .and _ [r, en]) => ruleBodyAnd N msrc a l r0 xs r en
    | (_, b) => ruleBodyOther N (.rewrites s (.and s' [l, r0]) b)
  | .rewrites s l rx => ruleBodyOther N (.rewrites s l (peelExists rx).2)
  | p => ruleBodyOther N p
where
  /-- A rewrite axiom of no other shape the reader reads, its right side without its binders. -/
  ruleBodyOther (N : Names) : Kore.Pattern → Rd (Rule × RulePres)
  -- a left side that is an application of a symbol the definition does not have, not `\and(lhs,
  -- req)`: an alias's (kompile's `ruleNLHS`, under --enable-kore-antileft)
  | .rewrites _ (.app h [] _) _ =>
    if (N.sym? h.ident.name).isNone then fail .aliasApplication h.ident.name else fail .ruleShape
  -- a right side headed by an alias of K's prelude (`preludeAliases`): kompile's right side for a
  -- rule of a module carrying all-path or one-path, `weakAlwaysFinally{S}(\and(rhs, ens))`
  -- `scanRewrites` has read the right side through it where its alias sentence is the identity
  -- (`unaliasRule`); here at another body, or not one sort and one argument
  | .rewrites _ _ (.app h _ _) =>
    if preludeAliases.contains h.ident.name then
      fail .aliasApplication s!"{h.ident.name}: an alias of K's prelude heading the right side of the \
        rewrite axiom (the form kompile writes for a rule of a module carrying all-path or one-path), \
        not at one sort and one argument or not defined by the text as the identity on its argument \
        (aliasIsIdentity); not read as its argument"
    else fail .ruleShape
  | _ => fail .ruleShape

/-! ## A set variable in a rewrite axiom

A set variable `@S` of sort s ranges over every set of elements of s, and an axiom holding it holds
at each. Where `@S` stands in the left side and the right side under applications only (in neither
the `requires` nor the `ensures`, under no other connective), each side at S is the union of its
instances at one element of S per occurrence, an application being pointwise over the elements its
arguments hold. A configuration the left side matches at S is matched at the set of the elements of
one choice ā, one per left occurrence, and the right side at that set is contained in the right side
at S. So the axiom at every S is its instance at those sets:
`∀ā. L[ā] → •∃z̄. R[z̄] ∧ ⋀ⱼ ⋁ᵢ zⱼ ∈ aᵢ`, one variable aᵢ per left occurrence and one zⱼ per right
occurrence (`KCore.setvar_rewrite_singleton`, stated on denotations in every interpretation). The rule
is read so (`svRewrite?`): each left occurrence a fresh variable, each right occurrence a fresh
existential variable of the rule (`exs`), and `post` the conjunction, over the right occurrences, of
the disjunction, over the left ones, of the memberships `zⱼ ∈ aᵢ`. With no right occurrence `post` is
`\top` and the rule is `L[ā] → •R`.

Refused (`setVariable`, the detail saying why): a set variable in the `requires` or the `ensures`,
whose truth at a larger set is not entailed by its truth at a smaller one, so the sentence reads every
subset of the sort; one under a connective that is no application, or in a right side under
`\exists`, which the reading does not cover; one in the right side and not in the left, where the
right side at the empty set is empty and the axiom states that its left side matches nothing; and
two set variables or more, which the reading, stated for one, does not cover. -/

mutual
  /-- The first connective other than an application above an occurrence of a set variable in `p`,
  `none` where every occurrence stands under applications only. -/
  def svConn? : Kore.Pattern → Option String
    | .var (.svar _) => none
    | .app _ _ ps => svConnList? ps
    | p => if (svarsOf_svin (varsOf_svin p)).isEmpty then none else some (connective p)
    termination_by structural p => p
  def svConnList? : List Kore.Pattern → Option String
    | [] => none
    | p :: ps => (svConn? p).orElse fun _ => svConnList? ps
    termination_by structural ps => ps
end

mutual
  /-- `p` with each occurrence of a set variable under applications replaced by the element
  variable `mk i`, numbered from `n` left to right; the pattern and the next number. -/
  def svReplace (mk : Nat → Kore.EVar) (n : Nat) : Kore.Pattern → Kore.Pattern × Nat
    | .var (.svar _) => (.var (.evar (mk n)), n + 1)
    | .app h ss ps => let (ps', m) := svReplaceList mk n ps; (.app h ss ps', m)
    | p => (p, n)
    termination_by structural p => p
  def svReplaceList (mk : Nat → Kore.EVar) (n : Nat) : List Kore.Pattern → List Kore.Pattern × Nat
    | [] => ([], n)
    | p :: ps =>
      let (p', m) := svReplace mk n p
      let (ps', m') := svReplaceList mk m ps
      (p' :: ps', m')
    termination_by structural ps => ps
end

mutual
  /-- Whether `p` holds a `\mu` or `\nu` binder. -/
  def svFix : Kore.Pattern → Bool
    | .mu _ _ | .nu _ _ => true
    | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => svFixList ps
    | .not _ p | .next _ p | .ceil _ _ p | .floor _ _ p | .exist _ _ p | .forall _ _ p => svFix p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q => svFix p || svFix q
    | .var _ | .string _ | .top _ | .bottom _ | .dv _ _ => false
    termination_by structural p => p
  def svFixList : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => svFix p || svFixList ps
    termination_by structural ps => ps
end

/-- The disjunction of the conditions, `\bottom` for none. -/
def svDisj : List Cond → Cond
  | [] => .bot
  | [p] => p
  | p :: ps => .or p (svDisj ps)

/-- A rewrite axiom `\rewrites(\and(l, req), rhs)` holding a set variable, read as the block above
says: the axiom with each left occurrence the fresh variable `Var<S>'Hash'L<i>`, and each right
occurrence the fresh variable `Var<S>'Hash'R<j>` bound by `\exists` around the right side, with the
set variable and the names (without `Var`) of the left and of the right variables; `.error` with the
refusal's detail where the reading does not cover the axiom; `none` for an axiom holding no set
variable, holding a `\mu` or `\nu` binder (whose set variable is bound; the connective is refused
as such), or of another form. -/
def svRewrite? (a : Kore.Axiom) :
    Option (Except String (Kore.Axiom × Kore.SVar × List String × List String)) :=
  match a.pattern with
  | .rewrites s (.and s' [l, r0]) rx =>
    let holds := fun (p : Kore.Pattern) => !(svarsOf_svin (varsOf_svin p)).isEmpty
    match if svFix a.pattern then [] else svarsOf_svin (varsOf_svin a.pattern) with
    | [] => none
    | X :: xs => some (
      let n := X.var.ident.name
      let why := "its truth at a larger set is not entailed by its truth at a smaller one, so the \
        sentence reads every subset of the sort"
      let uncovered := "the axiom is read through its instances at one element per occurrence only \
        where every occurrence stands under applications"
      if !(xs.all fun Y => decide (Y = X)) then
        .error s!"{n}: one of two set variables or more: the reading is stated for one"
      else if holds r0 then .error s!"{n}: in the requires: {why}"
      else match peelExists rx with
        | (bs, .and s'' [r, en]) =>
          if holds en then .error s!"{n}: in the ensures: {why}"
          else match svConn? l, svConn? r with
            | some c, _ => .error s!"{n}: under {c} in the left side: {uncovered}"
            | none, some c => .error s!"{n}: under {c} in the right side: {uncovered}"
            | none, none =>
              let base := (dropPrefix? "Var" n).getD n
              let used := evarNames a.pattern
              let mk := fun (side : String) (i : Nat) =>
                KoreAML.evar (freshIn used (used.length + 1) s!"Var{base}'Hash'{side}{i}") X.sort
              let (l', nl) := svReplace (mk "L") 0 l
              let (r', nr) := svReplace (mk "R") 0 r
              let name := fun (x : Kore.EVar) => (dropPrefix? "Var" x.var.ident.name).getD x.var.ident.name
              if nl == 0 then
                .error s!"{n}: in the right side and not in the left: the right side at the empty set \
                  is empty, so the axiom states that its left side matches nothing"
              else if nr != 0 && !bs.isEmpty then
                .error s!"{n}: in a right side under \\exists: {uncovered}"
              else
                let zs := (List.range nr).map (mk "R")
                let rx' := if nr == 0 then rx else zs.foldr (fun z p => .exist s'' z p) (.and s'' [r', en])
                .ok ({ a with pattern := .rewrites s (.and s' [l', r0]) rx' }, X,
                  (List.range nl).map (name ∘ mk "L"), zs.map name)
        | (_, p) => .error s!"{n}: under {connective p} in the right side: {uncovered}")
  | _ => none

/-- A rewrite axiom's rule (`ruleBodyRead`), a set variable read where `svRewrite?` reads it: the
axiom it gives is read, and `post` gains, for each right variable, the disjunction of its
memberships in the left variables. Where `svRewrite?` refuses the axiom, it is refused
`setVariable` with its detail. -/
def ruleBody (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  match svRewrite? a with
  | none => ruleBodyRead N msrc a
  | some (.error d) => fail .setVariable d
  | some (.ok (a', X, ls, rs)) => do
    let (r, p) ← ruleBodyRead N msrc a'
    let s ← N.sortE X.sort
    let idx := fun (x : String) => need (p.names.idxOf? x) .setVariable x
    let ais ← ls.mapM idx
    let zis ← rs.mapM idx
    let post := ovlCutConj (zis.map fun z => svDisj (ais.map fun i => Cond.mem s (.var z) (.var i)))
    pure ({ r with post := if r.post.isTop then post else .and r.post post }, p)

/-- The rule of a rewrite axiom. -/
def ruleOf (N : Names) (msrc : String) (a : Kore.Axiom) : Rd (Rule × RulePres) :=
  Rd.within (.sentence (.axiom a)) (ruleBody N msrc a)

/-! ## The configuration -/


def cellName? (label : String) : Option String := do
  let rest ← dropPrefix? "Lbl'-LT-'" label
  let cs := rest.toList
  let suf := "'-GT-'".toList
  if cs.drop (cs.length - suf.length) == suf then some (String.ofList (cs.take (cs.length - suf.length)))
  else none

/-- The cell symbol whose result sort is `X`. -/
def cellSym? (syms : List Kore.SentenceSymbol) (X : String) : Option Kore.SentenceSymbol :=
  syms.find? fun s => hasKey s.attributes .cell && sortName? s.sort == some X

/-- A cell as the text names it, before numbering; `coll` a node's child that is a cell collection
(`Cell.coll`). -/
inductive RCell where
  | leaf (name content : String)
  | node (name : String) (children : List RCell)
  | coll (content : String)
  deriving Inhabited

namespace RCell
def name : RCell → String
  | .leaf n _ => n
  | .node n _ => n
  | .coll _ => ""
/-- Each word capitalized, the dashes dropped. -/
def capList : Bool → List Char → List Char
  | _, [] => []
  | _, '-' :: chs => capList true chs
  | b, ch :: chs => (if b then ch.toUpper else ch) :: capList false chs
/-- `state` ↦ `State`, `exit-code` ↦ `ExitCode`: kompile's sort name of a cell. -/
def cap (n : String) : String := String.ofList (capList true n.toList)
/-- kompile's names of a cell's sorts and symbols. -/
def sort (x : RCell) : String := cap x.name ++ "Cell"
def optSort (x : RCell) : String := x.sort ++ "Opt"
def fragSort (x : RCell) : String := x.sort ++ "Fragment"
def label (x : RCell) : String := "Lbl'-LT-'" ++ x.name ++ "'-GT-'"
def noLabel (x : RCell) : String := "Lblno" ++ x.sort
def fragLabel (x : RCell) : String := x.label ++ "-fragment"

mutual
  /-- Its sorts and its descendants', in `Cell.sortsList`'s order. -/
  def sorts : RCell → List String
    | .leaf n c => [(RCell.leaf n c).sort, (RCell.leaf n c).optSort]
    | .node n cs => [(RCell.node n cs).sort, (RCell.node n cs).optSort, (RCell.node n cs).fragSort] ++ sortsList cs
    | .coll _ => []
  def sortsList : List RCell → List String
    | [] => []
    | x :: xs => sorts x ++ sortsList xs
end

mutual
  /-- Its symbols and its descendants', in `Cell.symsList`'s order. -/
  def syms : RCell → List String
    | .leaf n c => [(RCell.leaf n c).label, (RCell.leaf n c).noLabel]
    | .node n cs => [(RCell.node n cs).label, (RCell.node n cs).noLabel, (RCell.node n cs).fragLabel] ++ symsList cs
    | .coll _ => []
  def symsList : List RCell → List String
    | [] => []
    | x :: xs => syms x ++ symsList xs
end

mutual
  /-- The numbered cell. -/
  def num (N : Names) : RCell → Rd Cell
    | .leaf n c => do
      let x := RCell.leaf n c
      let ids : CellIds := ⟨← N.srtE x.sort, some (← N.srtE x.optSort), none, ← N.symE x.label,
        some (← N.symE x.noLabel), none⟩
      pure (.leaf n (← N.srtE c) ids)
    | .node n cs => do
      let x := RCell.node n cs
      let ids : CellIds := ⟨← N.srtE x.sort, some (← N.srtE x.optSort), some (← N.srtE x.fragSort),
        ← N.symE x.label, some (← N.symE x.noLabel), some (← N.symE x.fragLabel)⟩
      pure (.node n (← numList N cs) ids)
    | .coll c => do pure (.coll (← N.srtE c))
  def numList (N : Names) : List RCell → Rd (List Cell)
    | [] => pure []
    | x :: xs => do pure ((← num N x) :: (← numList N xs))
end
end RCell

/-- The cell tree below the cell of sort `X` (fuel: the depth; `cellFuelOfR` for the text's
configuration), `colls` the text's collection sorts: a node where the cell's arguments are cell
sorts, or cell sorts and collection sorts with at least one cell sort (a collection argument is a
`*` cell's collection beside its siblings: `RCell.coll`); a leaf of one argument otherwise. -/
def cellOf (syms : List Kore.SentenceSymbol) (colls : List String) : Nat → String → Rd RCell
  | 0, X => fail .configuration X
  | fuel + 1, X => do
    let s ← need (cellSym? syms X) .configuration X
    Rd.within (.sentence (.symbol s)) do
      let n ← need (cellName? s.symbol.ident.ident.name) .cellShape
      let args ← s.sorts.mapM sortNameE
      let isCell := fun (a : String) => (cellSym? syms a).isSome
      if args.any isCell && args.all (fun a => isCell a || colls.contains a) then
        pure (.node n (← args.mapM fun a => if isCell a then cellOf syms colls fuel a else pure (.coll a)))
      else match args with
        | [a] => pure (.leaf n a)
        | _ => fail .cellShape

/-- `cellOf`'s fuel for the text's configuration: the number of its cell symbols, plus one. Each
step of `cellOf` descends from a cell to a cell symbol's argument sort, so a tree of distinct cells
is read to its full depth; a cell sort below itself (no tree) exhausts it (`configuration`). -/
def cellFuelOfR (syms : List Kore.SentenceSymbol) : Nat :=
  (syms.filter fun s => hasKey s.attributes .cell).length + 1

/-- The user's configuration: the children of `<generatedTop>` before the counter, `colls` the text's
collection sorts. -/
def configOf (syms : List Kore.SentenceSymbol) (colls : List String) : Rd (List RCell) := do
  match ← cellOf syms colls (cellFuelOfR syms) "GeneratedTopCell" with
  | .node _ cs => match cs.getLast? with
    | some (.leaf "generatedCounter" "Int") => if cs.length ≥ 2 then pure cs.dropLast else fail .configuration
    | _ => fail .configuration "GeneratedCounterCell"
  | _ => fail .configuration "GeneratedTopCell"

/-- `x` is one of `xs` (by the decided equality: the kernel evaluates it). -/
def evarIn (xs : List Kore.EVar) (x : Kore.EVar) : Bool := xs.any fun y => decide (x = y)

/-- No two of `xs` are the same variable. -/
def evarsDistinct : List Kore.EVar → Bool
  | [] => true
  | x :: xs => !evarIn xs x && evarsDistinct xs

/-- The element variables `ps` are, where each is one and no two are the same. -/
def distinctEVars? (ps : List Kore.Pattern) : Option (List Kore.EVar) := do
  let xs ← ps.mapM fun
    | .var (.evar x) => some x
    | _ => none
  if evarsDistinct xs then some xs else none

/-- The variables standing for the top-level cells in `getGeneratedCounterCell`'s premise: its
pattern is an application to distinct element variables and its right side is the last of them
(`counterShape` otherwise); the others are the top-level cells'. -/
def counterVarsOf (eqs : List RawEqn) : Rd (List String) := do
  let e ← need (eqs.find? fun e => e.fn == "LblgetGeneratedCounterCell" && e.competitors.isNone)
    .missingEquation "LblgetGeneratedCounterCell"
  Rd.within (.attrs e.attrs) (match e.pats, e.rhs with
    | [.app _ [] ps], .var (.evar v) => match distinctEVars? ps with
      | some xs => if decide (xs.getLast? = some v) then pure (xs.dropLast.map (·.var.ident.name))
        else fail .counterShape
      | none => fail .counterShape
    | _, _ => fail .counterShape)

/-- The unique id of the first equation of `f` (its `[owise]` equation when `owise`). -/
def uidOf (eqs : List RawEqn) (f : String) (owise : Bool) : Rd String := do
  let e ← need (eqs.find? fun e => e.fn == f && e.competitors.isSome == owise && !e.dom) .missingEquation f
  Rd.within (.attrs e.attrs) (need (attrStr? e.attrs "UNIQUE'Unds'ID") .sentenceInfo)

/-- The unique id of the first equation of the cell initializer `f`. -/
def initUidOf (eqs : List RawEqn) (f : String) : Rd String := do
  let e ← need (eqs.find? (·.fn == f)) .missingEquation f
  Rd.within (.attrs e.attrs) (need (attrStr? e.attrs "UNIQUE'Unds'ID") .sentenceInfo)

/-- The unique id of the first equation of the projection `project:X`, or `""` when the text
states no projection equation of X: kompile declares none for a sort whose name begins with `#`
(wasm's `syntax #Layout [token]`), and no sentence can then apply one; and a symbol the text
declares under the projection's label with no equation (`pe(K) [function, symbol(project:X)]`)
is a function of which the text states its declaration only, a parameter symbol (`isGenFn`), and
no projection equation is presented for X. -/
def projUidOf (_syms : List Kore.SentenceSymbol) (eqs : List RawEqn) (X : String) : Rd String :=
  match eqs.find? fun e => e.fn == KoreAML.projLabel X && e.competitors.isNone && !e.dom with
  | some e => Rd.within (.attrs e.attrs) (need (attrStr? e.attrs "UNIQUE'Unds'ID") .sentenceInfo)
  | none => pure ""

def sortUidOf (syms : List Kore.SentenceSymbol) (eqs : List RawEqn) (X : String) : Rd SortUids := do
  pure ⟨← projUidOf syms eqs X, ← uidOf eqs (KoreAML.isLabel X) false,
        ← uidOf eqs (KoreAML.isLabel X) true⟩

/-- The pattern holds the configuration variable `$PGM`, `\dv{SortKConfigVar{}}("$PGM")` (fuel: the
depth searched). -/
def holdsPgm : Nat → Kore.Pattern → Bool
  | 0, _ => false
  | _ + 1, .dv s v => v == "$PGM" && sortName? s == some "KConfigVar"
  | n + 1, .app _ _ ps => ps.any (holdsPgm n)
  | n + 1, .and _ ps => ps.any (holdsPgm n)
  | _, _ => false

/-- The sort `$PGM` is projected to in a cell initializer's right-hand side: `S` of the first
`project:S` applied to a pattern holding `$PGM` (fuel: the depth searched). -/
def pgmIn : Nat → Kore.Pattern → Option String
  | 0, _ => none
  | n + 1, .app h _ ps => match dropPrefix? "Lblproject'Coln'" h.ident.name with
    | some S => if ps.any (holdsPgm n) then some S else ps.findSome? (pgmIn n)
    | none => ps.findSome? (pgmIn n)
  | n + 1, .and _ ps => ps.findSome? (pgmIn n)
  | _, _ => none

/-- The sort of `$PGM`: the text's initializer equations (`Lblinit…`) state which cell holds which
configuration variable, and the one whose right-hand side projects `$PGM` states its sort
(`pgmIn`), whichever cell it initializes (`<k>`, or another: K does not require `$PGM` in `<k>`).
Where no initializer holds `$PGM` (`configuration <k> foo </k>`) the text states no such sort and
no cell holds it (`Presentation.pgmCell` is `none`): the sort is K, which no sentence `emit` writes
reads. Refused (`pgmSort`) where an initializer holds `$PGM` and none projects it, or two project it
to different sorts. -/
def pgmSortOf (N : Names) (eqs : List RawEqn) : Rd Srt := do
  let inits := eqs.filter fun e => (dropPrefix? "Lblinit" e.fn).isSome
  let found := inits.filterMap fun e => (pgmIn 16 e.rhs).map (e, ·)
  match found with
  | [] => if inits.any (holdsPgm 16 ·.rhs) then fail .pgmSort "no cell initializer projects $PGM" else pure Srt.k
  | (e, S) :: rest => Rd.within (.attrs e.attrs) do
    if rest.all (·.2 == S) then N.srtE S else fail .pgmSort "$PGM projected to several sorts"

/-- A leaf cell's initial value: the argument of the cell in its initializer's right-hand side,
when it is a term. The value is the presentation's only (`emit` writes the initializer with it);
no theorem reads it, and a value that is not a term (a configuration variable's projection that
no axiom applies) is not kept. -/
def valueOf (N : Names) (eqs : List RawEqn) (init : String) : Option Term := do
  let e ← eqs.find? (·.fn == init)
  match e.rhs with
  | .app _ [] [v] => (term N [] v).toOption.map (·.1)
  | _ => none

/-! ## The definition -/

mutual
  /-- The symbols a term applies. -/
  def Term.heads : Term → List Sym
    | .app f ts => f :: Term.headsList ts
    | .inj _ _ t => Term.heads t
    | .as t _ => Term.heads t
    | _ => []
  def Term.headsList : List Term → List Sym
    | [] => []
    | t :: ts => Term.heads t ++ Term.headsList ts
end

/-- The imported modules' parameter symbols the rules and functions apply, in a left side, a
`requires`, a right side or an `ensures`: those `Step` can read (`wf` checks each is one of the
imports', `Definition.paramsOK`). -/
def usedLibParams (imports : List Nat) (fns : List Fn) (rules : List Rule) : List ParamSig :=
  let opt := fun (o : Option Term) => (o.map Term.heads).getD []
  let hs := rules.flatMap (fun r => Term.heads r.lhs ++ Term.heads r.rhs ++ opt r.req ++ opt r.ens) ++
    fns.flatMap fun f => f.clauses.flatMap fun cl => Term.headsList cl.pats ++ opt cl.req ++ Term.heads cl.rhs ++
      opt cl.ens
  let used := NatMap.ofList (hs.map fun f => (f, ()))
  (libParams imports).filter fun k => (used.find k.sig.name).isSome

def mergeProds (pending : List Prod) : List (Sum Sym (Srt × Srt)) → List Prod
  | [] => pending
  | .inr (a, b) :: es => .subsort a b :: mergeProds pending es
  | .inl c :: es =>
    let isC := fun (p : Prod) => match p with | .ctor c' _ => c'.name == c | _ => false
    let before := pending.takeWhile (!isC ·)
    let after := pending.dropWhile (!isC ·)
    before ++ after.take 1 ++ mergeProds (after.drop 1) es

def prodKind : Prod → ProdKind
  | .ctor .. => .ctor
  | .fn .. => .fn
  | .subsort .. => .subsort

/-- The number of disjuncts before the first fixed KItem constructor (the library's, or
`#KConfigValue`) in KItem's no-junk axiom (`ors`: the disjuncts of each `\or` axiom of sort KItem,
in text order). -/
def kconfigPosOf (fixedK : List String) (ors : List (List Kore.Pattern)) : Nat :=
  let isKcv : Kore.Pattern → Bool := fun d => match binders eqnFuel d with
    | (_, .app h _ _) => fixedK.contains h.ident.name
    | _ => false
  (ors.findSome? fun ds => ds.findIdx? isKcv).getD 0

/-- The directory of a K installation's builtin files, reversed. -/
def kBuiltinDirRev : List Char := "/include/kframework/builtin/".toList.reverse

/-- `F` when `src` is a path `…/include/kframework/builtin/F`: a file of a K installation's builtin
library, whose sentences are the library's (Builtins.lean) up to their `Source` and `Location`. -/
def kBuiltinFile? (src : String) : Option String :=
  let rev := src.toList.reverse
  let file := rev.takeWhile (· != '/')
  if !file.isEmpty && (rev.drop file.length).take kBuiltinDirRev.length == kBuiltinDirRev then
    some (String.ofList file.reverse)
  else none

/-- A sentence from a K installation's builtin file. -/
def isKBuiltin (attrs : List Kore.AppPattern) : Bool :=
  match source? attrs with
  | some s => (kBuiltinFile? s).isSome
  | none => false

/-- A symbol from a user file (any file but krust's builtins and a K installation's): the
definition may span several files (`requires "expr.k"`). -/
def isUserSource (attrs : List Kore.AppPattern) : Bool :=
  match source? attrs with
  | some s => (dropPrefix? "krust-builtin://" s).isNone && (kBuiltinFile? s).isNone
  | none => false

/-- A sentence of a builtin module (krust's library, whose text Builtins.lean holds). -/
def isBuiltinSource (attrs : List Kore.AppPattern) : Bool :=
  match source? attrs with
  | some s => (dropPrefix? "krust-builtin://" s).isSome
  | none => false

/-- The attributes that say where a sentence was written, and nothing about what it states. -/
def isPlaceAttr (ap : Kore.AppPattern) : Bool :=
  ap.head.ident.name == "org'Stop'kframework'Stop'attributes'Stop'Source" ||
    ap.head.ident.name == "org'Stop'kframework'Stop'attributes'Stop'Location"

/-- A sentence without its `Source` and `Location` attributes. -/
def bare : Kore.Sentence → Kore.Sentence
  | .sort s => .sort { s with attributes := s.attributes.filter (!isPlaceAttr ·) }
  | .hookedSort s => .hookedSort { s with attributes := s.attributes.filter (!isPlaceAttr ·) }
  | .symbol s => .symbol { s with attributes := s.attributes.filter (!isPlaceAttr ·) }
  | .hookedSymbol s => .hookedSymbol { s with attributes := s.attributes.filter (!isPlaceAttr ·) }
  | .alias a => .alias { a with attributes := a.attributes.filter (!isPlaceAttr ·) }
  | .axiom a => .axiom { a with attributes := a.attributes.filter (!isPlaceAttr ·) }
  | .claim c => .claim { c with attributes := c.attributes.filter (!isPlaceAttr ·) }
  | s => s

/-- The library's sentences without their places, each with its module's number in `library`, in
both of the text's forms (`builtinText`). -/
def libraryBare : List (Nat × Kore.Sentence) :=
  [false, true].flatMap fun arg => (List.range library.length).flatMap fun i =>
    (moduleText arg i).map fun s => (i, bare s)

/-- The library module of a sentence of a K installation's builtin file: the module whose text
holds the sentence up to its `Source` and `Location`, which say where it was written and nothing
of what it states. -/
def kBuiltinModule? (s : Kore.Sentence) : Option Nat :=
  let b := bare s
  (libraryBare.find? fun (_, t) => decide (t = b)).map (·.1)

set_option maxRecDepth 100000 in
kore_definition reflectionModuleDef from "prelude/kreflection.kore"

-- the elaborator would unfold the text whenever it compares two terms holding it
attribute [irreducible] reflectionModuleDef

/-- The SHA-256 of prelude/kreflection.kore, which `reflectionModuleDef` reads: Lake rebuilds this
module and its importers when it changes. -/
def reflectionTextHash : String := "0ee64118993fd568e5f0fb4a5506fc5aec0c11918dff73d4c046b4f92e1bc690"

/-- The sentences of K's K-REFLECTION module (`domains.md`) as K 7.1.337's kompile writes them,
without their `Source` and `Location` (prelude/kreflection.kore). -/
def reflectionModuleText : List Kore.Sentence := (reflectionModuleDef.modules.getD 0 default).sentences

/-- A sentence of a K installation's `domains.md` that is, up to its place, a sentence of the
K-REFLECTION module (`reflectionModuleText`): read as the definition's own
(`ReadingNote.reflectionAsOwn`). -/
def isReflectionSentence (s : Kore.Sentence) : Bool :=
  let as := match s with
    | .symbol x => x.attributes
    | .hookedSymbol x => x.attributes
    | _ => []
  (match source? as with
    | some src => kBuiltinFile? src == some "domains.md"
    | none => false) &&
  let b := bare s
  reflectionModuleText.any fun t => decide (t = b)

/-- A rewrite axiom of K's stream modules as kompile writes it into the user module: a rule of a K
installation's `domains.md` labelled `STDIN-STREAM.…` or `STDOUT-STREAM.…`, without an `ensures`
(`ReadingNote.streamRule`). -/
def isStreamRule (a : Kore.Axiom) : Bool :=
  (match source? a.attributes with
    | some src => kBuiltinFile? src == some "domains.md"
    | none => false) &&
  (match attrStr? a.attributes "label" with
    | some l => (dropPrefix? "STDIN-STREAM." l).isSome || (dropPrefix? "STDOUT-STREAM." l).isSome
    | none => false) &&
  match a.pattern with
  | .rewrites _ _ (.and _ [_, .top _]) => true
  | _ => false

/-- A sentence of a K installation's builtin file that is read as the definition's own: one of
K-REFLECTION's (`isReflectionSentence`) or a stream module's rule (`isStreamRule`). -/
def isOwnLibrarySentence (s : Kore.Sentence) : Bool :=
  match s with
  | .axiom a => isStreamRule a
  | _ => isReflectionSentence s

/-- A symbol declared as a macro or an alias. -/
def isMacroDecl (attrs : List Kore.AppPattern) : Bool :=
  hasAttr attrs "macro" || hasAttr attrs "macro-rec" || hasAttr attrs "alias" || hasAttr attrs "alias-rec"

/-- A constructor `strict` generates: a freezer, declared without source. -/
def isFreezer (s : Kore.SentenceSymbol) : Bool :=
  (dropPrefix? "Lbl'Hash'freezer" s.symbol.ident.ident.name).isSome && hasAttr s.attributes "constructor" &&
    (source? s.attributes).isNone

/-- The library's KItem constructors and `#KConfigValue`, by name. -/
def fixedKNames (lib : Lib) : List String :=
  (lib.kitemCtors.filter (·.name != kconfigValue) ++ lib.ctors.filter (·.name == kconfigValue)).map
    fun k => regSymNames.getD k.name ""

/-! ## One pass over the user module's sentences

Everything `parse` reads off the user module's sentences is a `filterMap` over the sentences
classified read, collected in `Scan`; the rest of `parse` (`finish`) reads only the scan. A scan of
a concatenation is the concatenation of the scans (`scan_append`), so the tie checks the scan a
segment of the module at a time. -/

/-- What `parse` reads off the user module's sentences, in text order. -/
structure Scan where
  /-- The symbol declarations. -/
  syms : List Kore.SentenceSymbol
  /-- The axioms read as function equations. -/
  eqs : List RawEqn
  /-- The names of the sort declarations without attributes, `Sort` dropped. -/
  plainSorts : List String
  /-- The constructors and functions of a user file (no cell), and the freezers. -/
  userSyms : List Kore.SentenceSymbol
  /-- The hooked symbols of a user file. -/
  userHooked : List Kore.HookedSymbol
  /-- The builtin sentences' sources and lines. -/
  builtin : List (String × Nat)
  /-- The library modules of the sentences of a K installation's builtin files (`kBuiltinModule?`),
  and of the library's hooked sorts declared without a place (`placelessModule?`). -/
  kbuiltin : List Nat
  /-- The axioms whose `simplification` attribute is written `simplification{}("")`. -/
  simpArg : List Unit
  /-- The rewrite axioms. -/
  rewrites : List Kore.Axiom
  /-- The `subsort` axioms' sort names and the `functional` axioms' constructor labels. -/
  events : List (Sum String (String × String))
  /-- The disjuncts of each `\or` axiom of sort KItem. -/
  ors : List (List Kore.Pattern)
  /-- The user's collection sorts (a hooked sort with hook `MAP.Map`, `SET.Set` or `LIST.List`
  outside the library, as K declares for a cell of multiplicity `*`): name, kind, and the names of
  its unit, element and concatenation symbols. -/
  colls : List (String × CollKind × String × String × String)
  /-- The names a user axiom applies that `envOf` numbers from their use: `ite` at a sort
  (`iteName`), the generated functions (`isGenFn`), and the instances of sort-parametric symbols
  (`instName`); one list per axiom that applies some. -/
  heads : List (List String)
  /-- The sorts of a user file declared with their location (`sort SortX{} [Location, Source]`):
  name, location, source. -/
  locSorts : List (String × KoreAML.Loc × String)
  /-- The sentences `classify` refuses: the reason, and the sentence's head. -/
  refused : List (RefusalReason × String)
  /-- The macro symbols declared (`UnreadReason.macroUnused`), whose applications are refused. -/
  macros : List String
  /-- The constructors and functions declared without a source that are neither cells nor
  freezers (`envOf` keeps those it does not number otherwise: the fragments, optional cells and
  initializers of a cell collection's cells, `XCellMapKey`). -/
  genSyms : List Kore.SentenceSymbol
  /-- The names of the sorts declared token sorts (`scanTokenSort`), `Sort` dropped. -/
  tokenSorts : List String
  /-- The sort-parametric functions declared in a user's file (`UnreadReason.parametricUnused`),
  whose instances `envOf` numbers from their use. -/
  paramDecls : List Kore.SentenceSymbol
  /-- The user's sorts hooked under their own name to a library carrier (`scanCarrier`): the
  sort's name, `Sort` dropped, and the carrier's. -/
  carriers : List (String × String) := []
  /-- The symbols an axiom of the text states single-valued and defined (`functionalSym?`), of every
  sentence, its class aside. -/
  fnls : List (String × Bool) := []
  /-- Of the hooked equalities the reader writes, `_==K_` and `_==Int_` (`readerEqs`): `(σ, false)`
  for a declaration of σ, `(σ, true)` for its sentence `hookEqSentence`, of every sentence. -/
  hookEqFacts : List (String × Bool) := []

def scanSym : Kore.Sentence → Option Kore.SentenceSymbol
  | .symbol s => some s
  | _ => none

def scanEqn : Kore.Sentence → Option RawEqn
  | .axiom a => ((rawEqn? a).orElse fun _ => overloadEqn? a).orElse fun _ =>
      if (source? a.attributes).isNone then projDomainEqn? a else none
  | _ => none

mutual
  /-- The names of `Scan.heads` a pattern applies. -/
  def extraHeads : Kore.Pattern → List String
    | .app h ss ps =>
      (if h.ident.name == "Lblite" then (match ss with
          | [S] => (sortName? S).toList.map iteName
          | _ => [])
       else if ss.isEmpty then (if isGenFn h.ident.name then [h.ident.name] else [])
       else if h.ident.name == "inj" then []
       -- an instance of a sort-parametric symbol at sorts (`instName`)
       else ((ss.mapM sortName?).map (instName h.ident.name)).toList) ++ extraHeadsList ps
    | .not _ p => extraHeads p
    | .exist _ _ p => extraHeads p
    | .forall _ _ p => extraHeads p
    | .mu _ p => extraHeads p
    | .nu _ p => extraHeads p
    | .ceil _ _ p => extraHeads p
    | .floor _ _ p => extraHeads p
    | .next _ p => extraHeads p
    | .and _ ps => extraHeadsList ps
    | .or _ ps => extraHeadsList ps
    | .implies _ p q => extraHeads p ++ extraHeads q
    | .iff _ p q => extraHeads p ++ extraHeads q
    | .equals _ _ p q => extraHeads p ++ extraHeads q
    | .in _ _ p q => extraHeads p ++ extraHeads q
    | .rewrites _ p q => extraHeads p ++ extraHeads q
    | .leftAssoc _ _ ps => extraHeadsList ps
    | .rightAssoc _ _ ps => extraHeadsList ps
    | _ => []
    termination_by structural p => p
  def extraHeadsList : List Kore.Pattern → List String
    | [] => []
    | p :: ps => extraHeads p ++ extraHeadsList ps
    termination_by structural ps => ps
end

def scanHeads : Kore.Sentence → Option (List String)
  | .axiom a => if isUserSource a.attributes || isStreamRule a then
      (match extraHeads a.pattern with | [] => none | hs => some hs) else none
  | _ => none

/-- The attributes of a token sort's declaration besides its place: `hasDomainValues{}()`, and
`token{}()` when the user's file declares the sort `syntax X [token]`. -/
def isTokenSortAttr (a : Kore.AppPattern) : Bool :=
  (a.head.ident.name == "hasDomainValues" || a.head.ident.name == "token") && a.sorts.isEmpty && a.args.isEmpty

/-- A sort declaration's `label`: a name, which states nothing of the sort's values. -/
def isLabelAttr (a : Kore.AppPattern) : Bool := a.head.ident.name == "label"

/-- A sort declaration's attributes but its `label`s (`isLabelAttr`). -/
def sortAttrs (s : Kore.SentenceSort) : List Kore.AppPattern := s.attributes.filter (!isLabelAttr ·)

def scanLocSort : Kore.Sentence → Option (String × KoreAML.Loc × String)
  | .sort s => if isUserSource s.attributes && ((sortAttrs s).filter (!isPlaceAttr ·)).all isTokenSortAttr &&
      (s.attributes.filter isPlaceAttr).length == 2 then do
      pure (← dropPrefix? "Sort" s.sort.ident.name, ← loc? s.attributes, ← source? s.attributes)
    else none
  | _ => none

/-- The library sort whose literals a sort hooked to `h` has: `INT.Int`, `BOOL.Bool`,
`FLOAT.Float`, `STRING.String`, `BYTES.Bytes`. -/
def carrierOf? : String → Option String
  | "INT.Int" => some "Int" | "BOOL.Bool" => some "Bool" | "FLOAT.Float" => some "Float"
  | "STRING.String" => some "String" | "BYTES.Bytes" => some "Bytes"
  | _ => none

/-- A sort of the user's file hooked under its own name to a library carrier
(`syntax MyInt [hook(INT.Int)]`): its name and its carrier's. -/
def scanCarrier : Kore.Sentence → Option (String × String)
  | .hookedSort s => if isUserSource s.attributes then
      (do pure (← dropPrefix? "Sort" s.sort.ident.name, ← (attrStr? s.attributes "hook").bind carrierOf?))
    else none
  | _ => none

def scanPlainSort : Kore.Sentence → Option String
  | .hookedSort s => (scanCarrier (.hookedSort s)).map (·.1)
  | .sort s =>
      -- `hasDomainValues{}()` compared field by field: the derived `BEq` of patterns is opaque to the kernel
      let plain := match sortAttrs s with
        | [] => true
        | [a] => a.head.ident.name == "hasDomainValues" && a.sorts.isEmpty && a.args.isEmpty
        | _ => false
      if plain then dropPrefix? "Sort" s.sort.ident.name else none
  | _ => none

/-- A token sort of the definition: a sort declared with domain values (`hasDomainValues`), from
the user's file (`syntax X [token]`, with its place and `token{}()`) or without a place (a sort K
infers from a token production, `syntax X ::= r"…" [token]`): its values are its literals. -/
def scanTokenSort : Kore.Sentence → Option String
  | .sort s => if hasAttr s.attributes "hasDomainValues" && (isUserSource s.attributes || (sortAttrs s).length == 1) &&
      ((sortAttrs s).filter (!isPlaceAttr ·)).all isTokenSortAttr then dropPrefix? "Sort" s.sort.ident.name else none
  | _ => none

/-- A constructor or function of the user's files (no cell), a freezer, or a constructor of
K-REFLECTION (`isReflectionSentence`), read as the user's. -/
def scanUserSym : Kore.Sentence → Option Kore.SentenceSymbol
  | .symbol s => if (isUserSource s.attributes && !hasAttr s.attributes "cell") || isFreezer s ||
      (isKBuiltin s.attributes && isReflectionSentence (.symbol s)) then some s else none
  | _ => none

/-- A hooked symbol of the user's file, one K generates for a collection sort (no source), or one
of K-REFLECTION (`isReflectionSentence`), read as the user's. -/
def scanUserHooked : Kore.Sentence → Option Kore.HookedSymbol
  | .hookedSymbol h => if isUserSource h.attributes || (source? h.attributes).isNone ||
      (isKBuiltin h.attributes && isReflectionSentence (.hookedSymbol h)) then some h else none
  | _ => none

/-- A sort-parametric function declared in a user's file (`UnreadReason.parametricUnused`): not a
macro, not a constructor. -/
def scanParamDecl : Kore.Sentence → Option Kore.SentenceSymbol
  | .symbol s => if !s.symbol.sortVars.isEmpty && isUserSource s.attributes && !isMacroDecl s.attributes &&
      hasAttr s.attributes "function" && !hasAttr s.attributes "constructor" then some s else none
  | _ => none

def sentenceAttrs : Kore.Sentence → List Kore.AppPattern
  | .sort s => s.attributes
  | .hookedSort s => s.attributes
  | .symbol s => s.attributes
  | .hookedSymbol s => s.attributes
  | .axiom a => a.attributes
  | _ => []

def scanBuiltin (s : Kore.Sentence) : Option (String × Nat) := do
  let as := sentenceAttrs s
  let src ← source? as
  let _ ← dropPrefix? "krust-builtin://" src
  let l ← loc? as
  pure (src, l.l1)

/-- The library's sentences that its text writes with a place, without it, each with its module's
number (`placelessModule?`). -/
def libraryPlaced : List (Nat × Kore.Sentence) :=
  [false, true].flatMap fun arg => (List.range library.length).flatMap fun i =>
    (moduleText arg i).filterMap fun s => if (sentenceAttrs s).any isPlaceAttr then some (i, bare s) else none

/-- The library module of a hooked sort's declaration written without any place that is, up to its
place, a declaration the library's text writes with one: a library sort the user declares again
(wasm's `syntax Int` in `wasm-data/int-type.k`), which kompile then writes without `Source` and
`Location`. Recognised by content, as `kBuiltinModule?` recognises a sentence of a K installation's
file. -/
def placelessModule? (s : Kore.Sentence) : Option Nat :=
  match s with
  | .hookedSort h => if (sentenceAttrs s).any isPlaceAttr then none
      else (libraryPlaced.find? fun (_, t) => decide (t = s)).map (·.1)
  | _ => none

def scanKBuiltin (s : Kore.Sentence) : Option Nat :=
  if isKBuiltin (sentenceAttrs s) then kBuiltinModule? s else placelessModule? s

def scanSimpArg : Kore.Sentence → Option Unit
  | .axiom a => if a.attributes.any (fun ap => ap.head.ident.name == "simplification" && !ap.args.isEmpty) then some () else none
  | _ => none

def scanRewrite : Kore.Sentence → Option Kore.Axiom
  | .axiom a => match a.pattern with | .rewrites .. => some a | _ => none
  | _ => none

/-- The rules of a rewrite axiom: one per disjunct of its left side (`splitRule`, `orSplit`), its right
side read through the identity aliases (`unaliasRule`, `identityAlias`). -/
def scanRewrites (s : Kore.Sentence) : List Kore.Axiom :=
  match scanRewrite s with
  | some a => splitRule (unaliasRule a)
  | none => []

def scanEvent : Kore.Sentence → Option (Sum String (String × String))
  | .axiom a => match a.attributes, a.pattern with
    | [⟨⟨⟨"subsort"⟩⟩, [A, B], []⟩], _ => match sortName? A, sortName? B with
      | some x, some y => some (Sum.inr (x, y))
      | _, _ => none
    | [⟨⟨⟨"functional"⟩⟩, [], []⟩], .exist _ _ (.equals _ _ _ (.app c [] _)) => some (Sum.inl c.ident.name)
    | _, _ => none
  | _ => none

/-- The symbol f of an axiom `∃v. v = f(x₁, …, xₙ)` [functional], the xᵢ distinct element variables
other than v: f's application to any arguments has exactly one element. With it, whether the axiom
states it at every instance (f's sort arguments are distinct sort variables of the axiom) or f has
no sort arguments. -/
def functionalSym? : Kore.Sentence → Option (String × Bool)
  | .axiom a => match a.attributes, a.pattern with
    | [⟨⟨⟨"functional"⟩⟩, [], []⟩], .exist _ v (.equals _ _ (.var (.evar w)) (.app f ss ps)) =>
      let xs := ps.filterMap fun p => match p with
        | .var (.evar x) => some x.var.ident.name
        | _ => none
      let svs := ss.filterMap fun s => match s with
        | .var x => if a.sortVars.any (·.ident.ident.name == x.ident.ident.name) then some x.ident.ident.name else none
        | _ => none
      if decide (w = v) && xs.length == ps.length && xs.eraseDups.length == xs.length &&
          !xs.contains v.var.ident.name && svs.length == ss.length && svs.eraseDups.length == svs.length then
        some (f.ident.name, !ss.isEmpty)
      else none
    | _, _ => none
  | _ => none

/-- The hooked equalities the reader writes: `_==K_` at K and `_==Int_` at Int, each with its name
and its sort's name. -/
def readerEqs : List (Sym × String × String) :=
  [(kEq, regSymNames.getD kEq "", "K"), (intEq, regSymNames.getD intEq "", "Int")]

/-- The axiom `((K1 σ K2) = true) = (K1 = K2)`, K1 and K2 distinct element variables of the sort X:
`\equals(\equals{SortBool{},Q}(σ(K1, K2), \dv{SortBool{}}("true")), E)` with E `K1 = K2` (or
`K2 = K1`) at X, alone or conjoined with `\top`, the whole alone or under `\implies(\top, …)`. -/
def hookEqSentence (σ X : String) (a : Kore.Axiom) : Bool :=
  let body := match a.pattern with
    | .implies _ (.top _) p => p
    | p => p
  match body with
  | .equals _ _ (.equals b _ (.app f [] [.var (.evar k1), .var (.evar k2)]) (.dv b' "true")) rhs =>
    let eq := match rhs with
      | .and _ [e, .top _] => some e
      | .equals .. => some rhs
      | _ => none
    match eq with
    | some (.equals s _ (.var (.evar l1)) (.var (.evar l2))) =>
      f.ident.name == σ && sortName? b == some "Bool" && sortName? b' == some "Bool" &&
        sortName? s == some X && sortName? k1.sort == some X && sortName? k2.sort == some X &&
        k1.var.ident.name != k2.var.ident.name &&
        ((decide (l1 = k1) && decide (l2 = k2)) || (decide (l1 = k2) && decide (l2 = k1)))
    | _ => false
  | _ => false

/-- A sentence's fact of a reader's hooked equality σ (`readerEqs`): `(σ, false)` for a declaration
of σ, `(σ, true)` for its sentence `hookEqSentence`. -/
def hookEqFact? : Kore.Sentence → Option (String × Bool)
  | .symbol d => (readerEqs.find? (·.2.1 == d.symbol.ident.ident.name)).map fun (_, σ, _) => (σ, false)
  | .hookedSymbol d => (readerEqs.find? (·.2.1 == d.symbol.ident.ident.name)).map fun (_, σ, _) => (σ, false)
  | .axiom a => (readerEqs.find? fun (_, σ, X) => hookEqSentence σ X a).map fun (_, σ, _) => (σ, true)
  | _ => none

def scanOr : Kore.Sentence → Option (List Kore.Pattern)
  | .axiom a => match a.pattern with
    -- `decide (· = ·)`, not `==`: Lean derives `BEq` for the nested `Kore.KSort` as an opaque
    -- (partial) function, which compiled code runs and the kernel cannot unfold
    | .or s ds => if decide (s = KoreAML.srt "KItem") then some ds else none
    | _ => none
  | _ => none

/-- The symbol named by a sort attribute such as `unit{}(Lbl'Stop'Map{}())`. -/
def attrSym? (as : List Kore.AppPattern) (n : String) : Option String :=
  match as.find? (·.head.ident.name == n) with
  | some ⟨_, [], [.app h [] []]⟩ => some h.ident.name
  | _ => none

def collKind? : String → Option CollKind
  | "MAP.Map" => some .map
  | "SET.Set" => some .set
  | "LIST.List" => some .list
  | _ => none

def scanColl : Kore.Sentence → Option (String × CollKind × String × String × String)
  | .hookedSort s => do
    let X ← dropPrefix? "Sort" s.sort.ident.name
    if regSortNames.contains X then none else
    let k ← collKind? (← attrStr? s.attributes "hook")
    pure (X, k, ← attrSym? s.attributes "unit", ← attrSym? s.attributes "element",
      ← attrSym? s.attributes "concat")
  | _ => none

/-! ## The class of a sentence

`classify` reads one sentence. A sentence is read when `parse` reads it: a declaration, a
rewrite axiom, a function equation, a `subsort` or `functional` axiom, KItem's no-junk axiom
(whose order the presentation keeps), or a sentence of a builtin module (whose source and line
name the module the definition imports). It is inert when the semantics does not read it, for
the reason given; refused otherwise. -/

/-- The kind of a `[constructor]` axiom, by its connective. -/
def ctorAxiomClass (a : Kore.Axiom) : Option InertReason :=
  match a.pattern with
  | .not _ (.and _ [.app _ [] _, .app _ [] _]) => some .distinctCtors
  | .implies _ (.and _ [.app c [] _, .app c' [] _]) (.app c'' [] _) =>
    if c.ident.name == c'.ident.name && c'.ident.name == c''.ident.name then some .injectivity else none
  | .or _ _ => some .noJunk
  | _ => none


/-- `\exists(v, \equals(v, f{S…}(…)))` [functional] with sort arguments. -/
def isParametricFunctional (a : Kore.Axiom) : Bool :=
  match a.attributes, a.pattern with
  | [⟨⟨⟨"functional"⟩⟩, [], []⟩], .exist _ _ (.equals _ _ _ (.app _ (_ :: _) _)) => true
  | _, _ => false

/-- An `[assoc]`, `[comm]`, `[unit]` or `[idem]` equation between applications of one symbol. -/
def isCollectionLaw (a : Kore.Axiom) : Bool :=
  (hasAttr a.attributes "assoc" || hasAttr a.attributes "comm" || hasAttr a.attributes "unit" ||
    hasAttr a.attributes "idem") &&
  match a.pattern with
  | .equals _ _ (.app _ [] _) _ => true
  | _ => false

/-- The `[idem]` equation of a concatenation, `\equals(f(K, K), K)`: K declares `idem` on a set's
concatenation only (`_Set_` and the cell sets'). -/
def isIdemLaw (a : Kore.Axiom) : Bool := hasAttr a.attributes "idem" && isCollectionLaw a

/-- The symbol of a law axiom (`isCollectionLaw`): the head of its equation's left side. -/
def lawHead? (a : Kore.Axiom) : Option String :=
  match a.pattern with
  | .equals _ _ (.app h [] _) _ => some h.ident.name
  | _ => none

/-- The law attributes of an axiom, among `assoc`, `comm`, `unit`, `idem`. -/
def lawKeys (a : Kore.Axiom) : List String :=
  ["assoc", "comm", "unit", "idem"].filter (hasAttr a.attributes ·)

/-- A symbol of a user's file declared neither `function` nor `constructor`, nor `anywhere` (an
overloading symbol's mark), nor a cell (`RefusalReason.openGenerator`; macros are classified before):
an open generator, read as a `raw` parameter where the text declares it `functional`. -/
def isOpenGenerator (s : Kore.SentenceSymbol) : Bool :=
  isUserSource s.attributes && !hasKey s.attributes .function && !hasKey s.attributes .constructor &&
    !hasKey s.attributes .anywhere && !hasKey s.attributes .cell

/-- The associativity sentence of the symbol `f` of sort `s`, as `[assoc]` writes it:
`axiom{R} \equals{S, R}(f(f(K1, K2), K3), f(K1, f(K2, K3)))`, attributes aside. -/
def openAssocAx (f : String) (s : Kore.KSort) : Kore.Axiom :=
  let K1 := KoreAML.ev "K1" s
  let K2 := KoreAML.ev "K2" s
  let K3 := KoreAML.ev "K3" s
  { sortVars := [KoreAML.Rv]
    pattern := .equals s KoreAML.R (KoreAML.ap f [KoreAML.ap f [K1, K2], K3]) (KoreAML.ap f [K1, KoreAML.ap f [K2, K3]])
    attributes := [] }

/-- The idempotence sentence of the symbol `f` of sort `s`, as `[idem]` writes it:
`axiom{R} \equals{S, R}(f(K, K), K)`, attributes aside. -/
def openIdemAx (f : String) (s : Kore.KSort) : Kore.Axiom :=
  let K := KoreAML.ev "K" s
  { sortVars := [KoreAML.Rv]
    pattern := .equals s KoreAML.R (KoreAML.ap f [K, K]) K
    attributes := [] }

/-- The axiom `a` is the law sentence `ax` with the attribute `key`. -/
def lawSentenceIs (key : String) (ax : Kore.Axiom) (a : Kore.Axiom) : Bool :=
  hasAttr a.attributes key && decide ({ a with attributes := [] } = ax)

/-- The sentences `ss` hold the law sentence `ax` with the attribute `key`. -/
def holdsLaw (ss : List Kore.Sentence) (key : String) (ax : Kore.Axiom) : Bool :=
  ss.any fun s => match s with
    | .axiom a => lawSentenceIs key ax a
    | _ => false

/-- A sentence of a K installation's builtin file: read when it is a sentence of the library's
text up to its place; read as the definition's own when it is one of K-REFLECTION's
(`reflectionAsOwn`; the sort-parametric `#unparseKORE`'s declaration not read) or a stream module's
rule (`streamRule`); refused otherwise. -/
def classifyKBuiltin (s : Kore.Sentence) : SentenceClass :=
  if (kBuiltinModule? s).isSome then .read
  else match s with
    | .axiom a => if isStreamRule a then .readAs .streamRule else .refused .builtinText
    | .hookedSymbol h => if !isReflectionSentence s then .refused .builtinText
        else if !h.symbol.sortVars.isEmpty then .unread .parametricUnused
        else .readAs .reflectionAsOwn
    | _ => if isReflectionSentence s then .readAs .reflectionAsOwn else .refused .builtinText

/-- The cell `<k>` of `kast.md`'s module `DEFAULT-CONFIGURATION` (`configuration <k> $PGM:K </k>`),
which K imports into a definition that declares no configuration, as kompile declares it, without
its place. -/
def defaultConfigCell : String :=
  "symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [cell{}(), constructor{}(), functional{}(), injective{}()]"

/-- The declaration of the default configuration's cell `<k>`: a sentence of a K installation's
`kast.md` that is, up to its place, `defaultConfigCell`. The default configuration is an ordinary
configuration that a library file declares; its cell is read as the definition's configuration
cell (`configOf`), as a user's `<k>` cell is, and not as a library module's sentence. -/
def isDefaultConfig (s : Kore.Sentence) : Bool :=
  match s with
  | .symbol x => (match source? x.attributes with
      | some src => kBuiltinFile? src == some "kast.md"
      | none => false) && Kore.Printer.sentence (bare s) == defaultConfigCell
  | _ => false

/-- The sort names of `inj{A, B}`. -/
def injSorts? : Kore.Pattern → Option (String × String)
  | .app h [A, B] [_] => if h.ident.name == "inj" then do pure (← sortName? A, ← sortName? B) else none
  | _ => none

/-- The subsort axiom of a cell into its collection's sort (`[subsort{XCell, XCellMap}()]`), or the
collection sort's no-junk axiom, a disjunction of injected cells. -/
def isCellCollAxiom (a : Kore.Axiom) : Bool :=
  match a.attributes, a.pattern with
  | [⟨⟨⟨"subsort"⟩⟩, [A, B], []⟩], _ => match sortName? A, sortName? B with
    | some x, some y => isCellCollPair x y
    | _, _ => false
  | [⟨⟨⟨"constructor"⟩⟩, [], []⟩], .or _ ds => ds.any fun d => match injSorts? (binders eqnFuel d).2 with
    | some (x, y) => isCellCollPair x y
    | none => false
  | _, _ => false

/-- Every note a rewrite axiom or an equation is read through, from the sentence alone, in the order
`identityAlias` (the right side read through an alias, `unaliasRule`; the rest of a rewrite axiom's
notes are then of the axiom so read), for a rewrite axiom whose right side is under `\exists`
`existsRenamedApart` and `existsDropped` and no other (the connectives' notes are of a right side
without binders), `orSplit`, `topAsVariable` / `existsAsVariable` (in each disjunct), for an equation
`setVarInDropped` (`svinShape`), the right side's
(`bottomAsEnsures`, else `andAsEnsures`, `andTermsWeaker` and the notes of the conditions it
lifts: a lifted predicate is `andAsEnsures`; on a rule a lifted `t ∧ u` of two terms is
`andTermsWeaker`, on an equation it is refused), the `requires`'
(`requiresOrSplit` and its disjuncts', else `predicateAtBool`, `andAtBool`) and the `ensures`',
`orBottom`; each once. -/
def connNotes (a₀ : Kore.Axiom) : List ReadingNote :=
  let a := unaliasRule a₀
  let al := match a₀.pattern with
    | .rewrites _ _ r => if (unaliasRhs? r).isSome then [ReadingNote.identityAlias] else []
    | _ => []
  let cond := fun (b : Kore.Pattern) =>
    if isPred b then [ReadingNote.predicateAtBool]
    else if (boolConj b).length > 1 then [ReadingNote.andAtBool] else []
  -- `eqn`: an equation's `t ∧ u` of two terms is refused (`clauseBody`), so it gives no note
  let side := fun (eqn : Bool) (r : Kore.Pattern) =>
    let (_, cs, e) := hoist r
    let isPredC := fun (c : SideCond) => match c with | .isTrue _ => true | .same .. => false
    let cs := if eqn then cs.filter isPredC else cs
    if e then [ReadingNote.bottomAsEnsures]
    else (if cs.any isPredC then [ReadingNote.andAsEnsures] else []) ++
      (if cs.any (!isPredC ·) then [ReadingNote.andTermsWeaker] else []) ++
      cs.flatMap fun (c : SideCond) => match c with | .isTrue b => cond b | .same .. => []
  let conds := fun (ps : List (Option Kore.Pattern)) => ps.flatMap fun p => match p with
    | some b => cond b
    | none => []
  let orB := fun (r : Kore.Pattern) => if hasOrBottom r then [ReadingNote.orBottom] else []
  let notes := match a.pattern with
    | .rewrites _ (.and _ [l, r0]) (.and _ [r, en]) =>
      let reqNotes := match reqOrSplit? a.pattern r0 with
        | some (_, qs) => ReadingNote.requiresOrSplit :: conds (qs.map fun q => (req? q).bind id)
        | none => conds [(req? r0).bind id]
      (if hasOr l then [ReadingNote.orSplit] else []) ++
        ((orAlts l).flatMap binderKinds).map (fun (b : Bool) => if b then ReadingNote.topAsVariable else ReadingNote.existsAsVariable) ++
        side false r ++ reqNotes ++ conds [(req? en).bind id] ++ orB r
    -- a right side under `\exists`: the binders' notes
    | .rewrites _ (.and _ [l, r0]) (.exist s x p) =>
      let rx := Kore.Pattern.exist s x p
      (if exRenamed l r0 rx then [ReadingNote.existsRenamedApart] else []) ++
        (match peelExists (rhsApart a.pattern l r0 rx) with
          | (xs, .and _ [r, en]) => if (exKept xs r en).length != xs.length then [ReadingNote.existsDropped] else []
          | _ => [])
    | _ => match rawEqn? a with
      | some e =>
        (if (svinShape e).toOption.join.isSome then [ReadingNote.setVarInDropped] else []) ++
          side true e.rhs ++ conds [e.req, e.ens] ++ orB e.rhs
      | none => []
  (al ++ notes).eraseDups

/-- The note of a rewrite axiom or an equation read through a connective: the first of
`connNotes`. -/
def connNote? (a : Kore.Axiom) : Option ReadingNote := (connNotes a).head?

/-- The symbol and the variable of an axiom `∃B. (φ₁ ∧ … ∧ φₙ)`, n ≥ 2, one of whose conjuncts is
`f(x̄) = B` or `B = f(x̄)`, with B the variable bound (`existentialAxiom`). A conjunction: a
`functional` or `subsort` axiom, `∃B. B = f(x̄)`, states that the application has one element. -/
def existentialAxiom? (a : Kore.Axiom) : Option (String × String) :=
  match a.pattern with
  | .exist _ v (.and _ cs@(_ :: _ :: _)) =>
    cs.findSome? fun c => match c with
      | .equals _ _ (.app f _ _) (.var (.evar w)) =>
        if decide (w = v) then some (f.ident.name, v.var.ident.name) else none
      | .equals _ _ (.var (.evar w)) (.app f _ _) =>
        if decide (w = v) then some (f.ident.name, v.var.ident.name) else none
      | _ => none
  | _ => none

/-- `isX` for a registry sort X with no predicate symbol (`predOf X = none`) that is itself no
registry symbol (`isK` and `isKItem` are): `UnreadReason.noSortPredicate`. -/
def isNoPredName (n : String) : Bool :=
  match dropPrefix? "Lblis" n with
  | some X => match regSortNames.idxOf? X with
    | some i => (predOf i).isNone && !regSymNames.contains n
    | none => false
  | none => false

/-- A generated sentence (no user source) of such a predicate: its declaration, its `functional`
axiom, or one of its equations. -/
def isNoPredSentence (s : Kore.Sentence) : Bool :=
  match s with
  | .symbol x => !isUserSource x.attributes && isNoPredName x.symbol.ident.ident.name
  | .axiom a => !isUserSource a.attributes && (match scanEvent s with
      | some (.inl f) => isNoPredName f
      | _ => match a.pattern with
        | .implies _ _ (.equals _ _ (.app f [] _) _) => isNoPredName f.ident.name
        | _ => false)
  | _ => false

/-- A subsort axiom (`[subsort{A, B}()]`) one of whose sorts is an instance of a sort-parametric
sort (`subsort{SortMInt{Sort8{}}, SortKItem{}}`), which has no sort name (`sortName?`): refused
`parametricSort`, as the declarations of such sorts are. -/
def isParametricSubsort (a : Kore.Axiom) : Bool :=
  match a.attributes with
  | [⟨⟨⟨"subsort"⟩⟩, [A, B], []⟩] => (sortName? A).isNone || (sortName? B).isNone
  | _ => false

def classifyAxiom (a : Kore.Axiom) : SentenceClass :=
  let s := Kore.Sentence.axiom a
  if isBuiltinSource a.attributes then .read
  else if isNoPredSentence s then .unread .noSortPredicate
  else if isKBuiltin a.attributes then classifyKBuiltin s
  else if isCellCollAxiom a then .unread .cellCollectionInjection
  -- a `\rewrites` axiom carrying `simplification` states a step: it is read, and `ruleBody`
  -- refuses it (`ruleAttrFault?`) instead of the step being dropped as an inert lemma
  else if hasAttr a.attributes "simplification" && (scanRewrite s).isNone then .inert .simplification
  -- an equation applying its function to a set variable on the left side (`lhsSetVar?`)
  else if (lhsSetVar? a).isSome then .refused .setVariable
  else if hasAttr a.attributes "symbol-overload" then
    if (overloadEqn? a).isSome then .read else .refused .overloadAxiom
  else if (source? a.attributes).isNone && (projectionDomain? a).isSome then .readAs .projectionDomainAsClause
  else if (match a.pattern with
      | .rewrites _ (.and _ [l, _]) _ => vacuous l
      | _ => false) then .inert .vacuousLeft
  else if (scanRewrite s).isSome || (scanEqn s).isSome then
    match connNote? a with
    | some n => .readAs n
    | none => .read
  else if (scanEvent s).isSome || (scanOr s).isSome then .read
  else if (source? a.attributes).isNone && hasAttr a.attributes "constructor" then
    match ctorAxiomClass a with
    | some r => .inert r
    | none => .refused .axiomShape
  else if (source? a.attributes).isNone && isIdemLaw a then .unread .setIdempotence
  else if (source? a.attributes).isNone && isCollectionLaw a then .inert .collectionLaw
  else if (source? a.attributes).isNone && isParametricFunctional a then .inert .parametricFunctional
  else if (existentialAxiom? a).isSome then .refused .existentialAxiom
  else if isParametricSubsort a then .refused .parametricSort
  else if isUnkompiledForm a.pattern then .refused .unkompiledForm
  else .refused .axiomShape

/-- An attribute of a sort declaration that is no refusal: `attrVerdict` at class `sort` rules it
inert (`label`, a name, says nothing of the sort's values), or reads it and the reader of a sort
declaration reads it (its place, `hasDomainValues`, `token`: `isPlaceAttr`, `isTokenSortAttr`).
A key read at a sort that a sort declaration does not carry here (`hook`, `concat`: a hooked sort's,
`classify`'s `.hookedSort` arm) and a name that is no key are refused (`sortAttribute`). -/
def sortAttrOK (a : Kore.AppPattern) : Bool :=
  match attrVerdictOf .sort .sortAttribute a.head.ident.name with
  | .refused .. => false
  | .inert _ => true
  | .read => isPlaceAttr a || isTokenSortAttr a

/-- Why `assoc` or `comm` on the declaration of a function is refused: kompile writes neither key
on a function's declaration. It writes a function production's `assoc` as the associativity axiom,
which the reader reads as a law of the function (`fnLaw`, owed as `FnLaws`), and its `comm` as no
sentence (e2-fn-assoc/kore.txt:4, 62; c3-fn-comm/kore.txt:4). -/
def fnDeclLawWhy : String :=
  "kompile writes the key on no function's declaration: a function production's assoc is the associativity axiom it writes beside the declaration, which the reader reads as a law of the function (fnLaw, owed as FnLaws), and its comm no sentence (e2-fn-assoc/kore.txt:4, 62; c3-fn-comm/kore.txt:4); only a KORE text written by hand carries it, and no text gives it a meaning on the declaration"

/-- The first attribute of a symbol or hooked-symbol declaration the reader refuses, as the reason
and the attribute's name with why: `attrFault?` at class `symbol`, except that on the declaration
of a function (`function{}()`) `assoc` and `comm` are refused `attrOutsideE2` (`fnDeclLawWhy`).
`attrVerdict` refuses them `openGenerator`, which is the case of a symbol that is no function: a
generator under a law. -/
def symAttrFault? (as : List Kore.AppPattern) : Option (RefusalReason × String) :=
  if hasKey as .function then
    as.findSome? fun ap =>
      let n := ap.head.ident.name
      if n == AttrKeyE2.assoc.kore || n == AttrKeyE2.comm.kore then some (.attrOutsideE2, s!"{n}: {fnDeclLawWhy}")
      else match attrVerdictOf .symbol .symbolAttribute n with
        | .refused r' w => some (r'.reason, s!"{n}: {w}")
        | _ => none
  else attrFault? .symbol .symbolAttribute as

/-- The class of a sentence of the user module, from the sentence alone. -/
def classify : Kore.Sentence → SentenceClass
  | .import _ => .inert .import
  | .claim c => match attrFault? .claim .outsideE2 c.attributes with
      | some (r, _) => .refused r
      | none => .inert .claim
  | .alias _ => .refused .aliasDeclaration
  | .symbol s => if isMacroDecl s.attributes then .unread .macroUnused
      else if isKBuiltin s.attributes && !isDefaultConfig (.symbol s) then classifyKBuiltin (.symbol s)
      else if !s.symbol.sortVars.isEmpty && isUserSource s.attributes then .unread .parametricUnused
      -- an open generator is read where the text declares it `functional`: a parameter symbol
      -- that is a generator of its sort (`ParamSig.raw`)
      else if isOpenGenerator s && !hasAttr s.attributes "functional" then .refused .openGenerator
      else if isNoPredSentence (.symbol s) then .unread .noSortPredicate
      else match symAttrFault? s.attributes with
        | some (r, _) => .refused r
        | none => .read
  | .hookedSymbol s => if isMacroDecl s.attributes then .unread .macroUnused
      else if isKBuiltin s.attributes then classifyKBuiltin (.hookedSymbol s)
      else match symAttrFault? s.attributes with
        | some (r, _) => .refused r
        | none => .read
  | .sort s => if isKBuiltin s.attributes then classifyKBuiltin (.sort s)
      else if (s.attributes.all sortAttrOK) then .read else .refused .sortAttribute
  | .hookedSort s => if isKBuiltin s.attributes then classifyKBuiltin (.hookedSort s)
      else if isBuiltinSource s.attributes || ((attrStr? s.attributes "hook").bind collKind?).isSome ||
        (placelessModule? (.hookedSort s)).isSome || (scanCarrier (.hookedSort s)).isSome then .read
      else .refused .userHookedSort
  | .axiom a => classifyAxiom a

def isRead (s : Kore.Sentence) : Bool :=
  match classify s with
  | .read | .readAs _ => true
  | _ => false

mutual
  /-- The first symbol a pattern applies, in pre-order. -/
  def firstHead : Kore.Pattern → Option String
    | .app h _ _ => some h.ident.name
    | .not _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p | .ceil _ _ p | .floor _ _ p
    | .next _ p => firstHead p
    | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => firstHeadList ps
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      (firstHead p).or (firstHead q)
    | _ => none
    termination_by structural p => p
  def firstHeadList : List Kore.Pattern → Option String
    | [] => none
    | p :: ps => (firstHead p).or (firstHeadList ps)
    termination_by structural ps => ps
end

/-- An axiom's head: an equation's function, a rule's label, or else the first symbol it applies. -/
def axiomHead (a : Kore.Axiom) : String :=
  match rawEqn? a with
  | some e => e.fn
  | none => match attrStr? a.attributes "label" with
    | some l => l
    | none => (firstHead a.pattern).getD (connective a.pattern)

/-- A sentence's head: the sort or symbol it declares, the module it imports, its axiom's head. -/
def headOf : Kore.Sentence → String
  | .import i => i.module.ident.name
  | .sort s => s.sort.ident.name
  | .hookedSort s => s.sort.ident.name
  | .symbol s => s.symbol.ident.ident.name
  | .hookedSymbol s => s.symbol.ident.ident.name
  | .alias a => a.alias.ident.ident.name
  | .axiom a => axiomHead a
  | .claim c => (firstHead c.pattern).getD (connective c.pattern)

def scanMacro : Kore.Sentence → Option String
  | .symbol x => if isMacroDecl x.attributes then some x.symbol.ident.ident.name else none
  | .hookedSymbol x => if isMacroDecl x.attributes then some x.symbol.ident.ident.name else none
  | _ => none

/-- A constructor or function declared without a source, neither a cell nor a freezer. -/
def scanGenSym : Kore.Sentence → Option Kore.SentenceSymbol
  | .symbol x => if (source? x.attributes).isNone && !hasAttr x.attributes "cell" && !isFreezer x &&
      (hasAttr x.attributes "constructor" || hasAttr x.attributes "function") then some x else none
  | _ => none

def scanRefused (s : Kore.Sentence) : Option (RefusalReason × String) :=
  match classify s with
  | .refused r => some (r, headOf s)
  | _ => none

/-- The scan of the sentences `l`: each part from the sentences classified read, and the refused
ones. -/
def scan (l : List Kore.Sentence) : Scan :=
  let r := l.filter isRead
  ⟨r.filterMap scanSym, r.filterMap scanEqn, r.filterMap scanPlainSort, r.filterMap scanUserSym,
   r.filterMap scanUserHooked, r.filterMap scanBuiltin, r.filterMap scanKBuiltin, r.filterMap scanSimpArg,
   r.flatMap scanRewrites,
   r.filterMap scanEvent, r.filterMap scanOr, r.filterMap scanColl, r.filterMap scanHeads,
   r.filterMap scanLocSort, l.filterMap scanRefused, l.filterMap scanMacro, r.filterMap scanGenSym,
   r.filterMap scanTokenSort, l.filterMap scanParamDecl, r.filterMap scanCarrier, l.filterMap functionalSym?,
   l.filterMap hookEqFact?⟩

def Scan.append (a b : Scan) : Scan :=
  ⟨a.syms ++ b.syms, a.eqs ++ b.eqs, a.plainSorts ++ b.plainSorts, a.userSyms ++ b.userSyms,
   a.userHooked ++ b.userHooked, a.builtin ++ b.builtin, a.kbuiltin ++ b.kbuiltin, a.simpArg ++ b.simpArg,
   a.rewrites ++ b.rewrites,
   a.events ++ b.events, a.ors ++ b.ors, a.colls ++ b.colls, a.heads ++ b.heads,
   a.locSorts ++ b.locSorts, a.refused ++ b.refused, a.macros ++ b.macros, a.genSyms ++ b.genSyms,
   a.tokenSorts ++ b.tokenSorts, a.paramDecls ++ b.paramDecls, a.carriers ++ b.carriers, a.fnls ++ b.fnls,
   a.hookEqFacts ++ b.hookEqFacts⟩

theorem scan_append (l l' : List Kore.Sentence) : scan (l ++ l') = (scan l).append (scan l') := by
  simp only [scan, Scan.append, List.filter_append, List.filterMap_append, List.flatMap_append]

/-- The scan of the segments `a` to `a + n` of a module's sentences is `S`. -/
def ScanIs (segs : List (List Kore.Sentence)) (a n : Nat) (S : Scan) : Prop :=
  scan ((segs.drop a).take n).flatten = S

theorem ScanIs.join {segs : List (List Kore.Sentence)} {a n m k : Nat} {S₁ S₂ : Scan}
    (h₁ : ScanIs segs a n S₁) (h₂ : ScanIs segs (a + n) m S₂) (hk : n + m = k) :
    ScanIs segs a k (S₁.append S₂) := by
  subst hk
  unfold ScanIs at *
  rw [List.take_add, List.flatten_append, scan_append, h₁, List.drop_drop, h₂]

theorem ScanIs.all {segs : List (List Kore.Sentence)} {n : Nat} {S : Scan}
    (hn : segs.length = n) (h : ScanIs segs 0 n S) : scan segs.flatten = S := by
  subst hn
  unfold ScanIs at h
  rwa [List.drop_zero, List.take_length] at h

/-- A hooked symbol of the text read as a function: its hook is one no registry hook interprets
(`regHookOf`), it is no unit, element or concatenation symbol of a collection sort of the text,
and the text gives it an equation (a symbol-overload or selector-domain axiom aside; a
`simplification` axiom is inert, never among `Scan.eqs`). The registry states nothing of such a
symbol, so what the theory holds of it is what the text states: its equations, as of a function's,
and where none applies the interpretation's value (`Semantics.fnRest`), as for a parameter
(`Semantics.paramVal`). A hooked symbol is never an open generator (`classify` reads every hooked
symbol that is no macro). -/
def hookFnSym (S : Scan) (h : Kore.HookedSymbol) : Bool :=
  let n := h.symbol.ident.ident.name
  (match keyStr? h.attributes .hook with
   | some hk => (regHookOf hk).isNone
   | none => false) &&
  !S.colls.any (fun (_, _, u, el, cc) => n == u || n == el || n == cc) &&
  S.eqs.any fun e => e.fn == n && !e.dom && !hasKey e.attrs .symbolOverload

/-- The library sorts of `hookSigs` that the builtin texts declare with a `hook` attribute
(`hooked-sort SortInt{} … hook{}("INT.Int")`, and so `BOOL.Bool`, `LIST.List`, `MAP.Map`, `SET.Set`,
`STRING.String`, `FLOAT.Float`, `BYTES.Bytes`, `RANGEMAP.RangeMap`). K, KItem, Range, Endianness and
Signedness are declared without one. -/
def hookedLibSorts : List Srt :=
  [Srt.bool, Srt.int, Srt.list, Srt.map, Srt.set, Srt.string, Srt.float, Srt.bytes, Srt.rangeMap]

/-- The library sort whose sort hook the sort `s` carries, `stands` listing the definition's sorts
declared with a library sort's hook under their own name, each with that library sort (a
collection sort of the text with its kind's, a sort hooked to a library carrier with the carrier):
a library sort is itself, a sort of the definition off `stands` carries none and is itself. -/
def hookSortOf (stands : List (Srt × Srt)) (s : Srt) : Srt :=
  if s < nRegSorts then s else ((stands.find? (·.1 == s)).map (·.2)).getD s

/-- The registry hook of a symbol the text declares at `k` with the attribute `hook{}(hk)`: the
one of that name (`regHookOf`), where the symbol has that hook's number of arguments and, at each
argument and at the result where the library's symbol has a hooked sort (`hookedLibSorts`), a sort
carrying that sort's hook. The builtin text describes a hooked sort and its symbols together (the
Map of MAP is the sort declared `hook(MAP.Map)` and `_Map_` its concatenation), so a sort declared
with that sort hook is that domain by the same description, and a symbol declared on it with one
of the domain's symbol hooks is that symbol of the domain (`_MtCellMap_`, `hook(MAP.concat)`, on a
sort declared `hook(MAP.Map)`). Of a symbol that names a symbol hook at a sort without the sort
hook no text says anything: it has no registry hook here and is a parameter without one, whose
value is the interpretation's. -/
def hookImplAt (stands : List (Srt × Srt)) (hk : String) (k : CtorSig) : Option Sym :=
  (regHookOf hk).filter fun g => match lookupSig hookSigs g with
    | some r => r.args.length == k.args.length &&
        ((r.result :: r.args).zip (k.result :: k.args)).all fun (rs, s) =>
          !hookedLibSorts.contains rs || hookSortOf stands s == rs
    | none => false

/-- `hookFnSym`'s symbols as declarations of the function path (`prodSyms`, `symProd`). -/
def hookFnDecls (S : Scan) : List Kore.SentenceSymbol :=
  (S.userHooked.filter (hookFnSym S)).map fun h => ⟨h.symbol, h.sorts, h.sort, h.attributes⟩

/-- The refusal of an equation by the symbol heading its left side, with its detail: a hooked
symbol of the text not read as a function (`hookFnSym`), or a registry symbol where the equation is written in a user's file
(`hookEquation`), a constructor (`constructorEquation`) or an open generator
(`openGeneratorEquation`); none for an equation of any other symbol, a symbol-overload axiom or a
selector-domain axiom. -/
def eqnHeadFault? (S : Scan) (e : RawEqn) : Option (RefusalReason × String) :=
  if e.dom || hasAttr e.attrs "symbol-overload" then none
  else
    let isCtor := fun (n : String) =>
      S.syms.any fun s => s.symbol.ident.ident.name == n && hasAttr s.attributes "constructor"
    let hooked := ((S.userHooked.filter (!hookFnSym S ·)).find? (·.symbol.ident.ident.name == e.fn)).map fun h =>
      let hk := (attrStr? h.attributes "hook").getD ""
      (RefusalReason.hookEquation, s!"{e.fn}: a hooked symbol of the text, " ++
        if (attrStr? h.attributes "hook").isNone then "without a hook attribute"
        else if (regHookOf hk).isSome then s!"hook {hk} interpreted by the registry"
        else s!"hook {hk}, a unit, element or concatenation symbol of a collection sort")
    if hooked.isSome then hooked
    else if isUserSource e.attrs && regSymNames.contains e.fn then
      some (.hookEquation, s!"{e.fn}: a symbol of the registry")
    else if isCtor e.fn then
      let right := match e.rhs with
        | .app h _ _ =>
          if h.ident.name == e.fn then "the same constructor"
          else if isCtor h.ident.name then s!"the constructor {h.ident.name}"
          else s!"{h.ident.name}, no constructor"
        | .var _ => "a variable"
        | _ => "no application"
      some (.constructorEquation, s!"{e.fn}: a constructor; right side headed by {right}")
    else if S.refused.any (fun (r, n) => r == .openGenerator && n == e.fn) ||
        S.userSyms.any (fun s => isOpenGenerator s && s.symbol.ident.ident.name == e.fn) then
      some (.openGeneratorEquation, s!"{e.fn}: an open generator")
    else none

/-- Every equation `eqnHeadFault?` refuses, as a stage's failure at the equation. -/
def eqnHeadFaults (S : Scan) : List Fault :=
  S.eqs.filterMap fun e => (eqnHeadFault? S e).map fun (r, d) => ⟨r, d, .attrs e.attrs⟩

/-- What `finish` reads off the scan before the productions and rules: the module's source, its
configuration, its imported builtin modules, its names, its parameter symbols. -/
structure Env where
  src : String
  rconfig : List RCell
  imports : List Nat
  simpArg : Bool
  userSortNames : List String
  N : Names
  params : List (ParamSig × ParamPres)
  config : List Cell
  userSorts : List Srt
  /-- the cells of the collections (`<account>` in `<accounts>`): constructors of the user's
  sorts, as K declares them, outside the configuration's cells -/
  collCells : List Kore.SentenceSymbol
  colls : List CollSig
  /-- the constructors and functions declared without a source that nothing else numbers
  (`Scan.genSyms`): constructors, and functions with equations -/
  genSyms : List Kore.SentenceSymbol
  /-- the functions without an equation and without `total` or `functional`: parameter symbols,
  of which the text says nothing -/
  clauseless : List String
  /-- the sorts whose projection is read as a function (`Presentation.libProjs`) -/
  libProjs : List Srt
  /-- the definition's token sorts (`scanTokenSort`): sorts of it whose values are their literals,
  the semantics' token sorts after the library's -/
  tokenSorts : List Srt
  /-- the instances of the user's sort-parametric functions that the user's axioms apply
  (`instDecl?`): each declared by its declaration at the instance's sorts -/
  instSyms : List Kore.SentenceSymbol
  /-- the overloading symbols' names, numbered after every other symbol of the definition's own -/
  ovlNames : List String
  /-- the overloading symbols (`Semantics.ovls`), in that order -/
  ovls : List OvlSig
  /-- the generated functions a read sentence applies whose equations the text states outside the
  user module's productions, with their presentations: K's `append` (`appendEqns`, the prelude's)
  and the top cell tree's initializers (whose declarations and equations `emit` writes with the
  cells, `Presentation.generatedFns`), after the functions of the productions -/
  genFns : List (Fn × FnPres)
  /-- the definition's sorts hooked to a library carrier, with the carrier (`scanCarrier`) -/
  carriers : List (Srt × Srt) := []
  /-- the hooked symbols of the text read as functions (`hookFnSym`), by name -/
  hookFns : List String := []

/-- The user symbols that have a production: the user file's constructors and functions (those
without equations aside, which are parameters), the collections' cells, the constructors and
functions declared without a source (`Env.genSyms`), the instances of sort-parametric functions
that have equations (`Env.instSyms`), then the hooked symbols read as functions (`hookFnDecls`). -/
def prodSyms (S : Scan) (E : Env) : List Kore.SentenceSymbol :=
  S.userSyms.filter (fun s => !E.clauseless.contains s.symbol.ident.ident.name &&
    !E.ovlNames.contains s.symbol.ident.ident.name) ++ E.collCells ++ E.genSyms ++
    E.instSyms.filter (fun s => !E.clauseless.contains s.symbol.ident.ident.name) ++ hookFnDecls S

/-- `cs` cut at each `,`. -/
def splitCommas : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => match splitCommas cs with
    | w :: ws => if c == ',' then [] :: w :: ws else (c :: w) :: ws
    | [] => [[c]]

/-- A sort with its variables replaced by the sorts `σ` names (`Sort` dropped). -/
def substSort (σ : List (String × String)) : Kore.KSort → Kore.KSort
  | .var v => match σ.lookup v.ident.ident.name with
    | some x => .ctor ⟨⟨"Sort" ++ x⟩⟩ []
    | none => .var v
  | k => k

/-- The declaration of the instance `n` (`instName`) of the sort-parametric declaration `d`: `d`
named `n`, without sort variables, its argument and result sorts at the instance's sorts. -/
def instDecl? (n : String) (d : Kore.SentenceSymbol) : Option Kore.SentenceSymbol := do
  let rest ← dropPrefix? (d.symbol.ident.ident.name ++ "{") n
  let cs := rest.toList
  let xs := (splitCommas cs.dropLast).map String.ofList
  if cs.getLast? == some '}' && xs.length == d.symbol.sortVars.length && !xs.any (·.isEmpty) then
    let σ := (d.symbol.sortVars.map (·.ident.ident.name)).zip xs
    pure { d with symbol := { d.symbol with ident := ⟨⟨n⟩⟩, sortVars := [] }
                  sorts := d.sorts.map (substSort σ), sort := substSort σ d.sort }
  else none

/-- A collection sort's signature, from its scanned names and its element symbol's arguments. -/
def collSigOf (N : Names) (hooked : List Kore.HookedSymbol) :
    String × CollKind × String × String × String → Rd CollSig
  | (X, k, u, e, cc) => do
    let h ← need (hooked.find? (·.symbol.ident.ident.name == e)) .collectionShape X
    let args ← h.sorts.mapM sortNameE
    let (key, val) ← match k, args with
      | .map, [a, b] => pure (a, some b)
      | .set, [a] => pure (a, none)
      | .list, [a] => pure (a, none)
      | _, _ => fail .collectionShape X
    pure ⟨← N.srtE X, k, ← N.srtE key, ← val.mapM N.srtE, ← N.symE u, ← N.symE e, ← N.symE cc⟩

def envOf (m : Kore.Module) (S : Scan) : Rd Env := do
  let src ← need (source? m.attributes) .moduleSource
  -- the module's attributes, as `attrVerdict` rules them at class `module`
  if let some (r, d) := attrFault? .module .outsideE2 m.attributes then fail r d
  let rconfig ← configOf S.syms (S.colls.map (·.1))
  -- the builtin modules with a sentence in the text, in the library's order
  let mods ← S.builtin.mapM fun (s, l) =>
    Rd.within (.builtin s l) (need (moduleAt s l) .builtinModule s)
  -- `#KConfigValue`'s module when the text declares it
  let mods := mods ++ S.kbuiltin ++
    (if S.syms.any (·.symbol.ident.ident.name == "Lbl'Hash'KConfigValue") then [kconfigIdx] else [])
  let imports := (List.range library.length).filter mods.contains
  -- a sort the text declares under the name of a library module's sort when no imported module
  -- declares it (`registrySortName`)
  let importedSorts := (importsOf imports).flatMap (·.sorts)
  let foreign := fun (X : String) => match regSortNames.idxOf? X with
    | some n => library.any (·.sorts.contains n) && !importedSorts.contains n
    | none => false
  match (S.plainSorts ++ S.locSorts.map (·.1)).find? foreign with
  | some X => Rd.within (match m.sentences.find? (fun s => match s with
        | .sort d => d.sort.ident.name == "Sort" ++ X
        | _ => false) with
      | some s => .sentence s
      | none => .unset) (fail .registrySortName X)
  | none => pure ()
  -- a symbol a user file declares under the name of a registry symbol (`registrySymbolName`)
  let userDecls : List (String × Kore.Sentence) :=
    (S.userSyms.filter (isUserSource ·.attributes)).map (fun s => (s.symbol.ident.ident.name, .symbol s)) ++
    (S.userHooked.filter (isUserSource ·.attributes)).map (fun h => (h.symbol.ident.ident.name, .hookedSymbol h))
  match userDecls.find? (fun d => regSymNames.contains d.1) with
  | some (n, s) => Rd.within (.sentence s) (fail .registrySymbolName n)
  | none => pure ()
  -- an equation of a symbol that is no function (`eqnHeadFault?`)
  match eqnHeadFaults S with
  | f :: _ => .error f
  | [] => pure ()
  let cellSortNames := RCell.sortsList rconfig
  let userSortNames := S.plainSorts.filter (fun X => !cellSortNames.contains X && !regSortNames.contains X)
    ++ S.locSorts.map (·.1) ++ S.colls.map (·.1)
  let isCtorDecl := fun (s : Kore.SentenceSymbol) => isFreezer s || hasAttr s.attributes "constructor"
  let ownSortNames := cellSortNames ++ userSortNames
  -- the configuration's cells, the generated top and counter cells included
  let configSyms := match cellOf S.syms (S.colls.map (·.1)) (cellFuelOfR S.syms) "GeneratedTopCell" with
    | .ok t => RCell.symsList [t]
    | .error _ => RCell.symsList rconfig
  let collCells := S.syms.filter fun s => hasAttr s.attributes "cell" && isUserSource s.attributes &&
    !configSyms.contains s.symbol.ident.ident.name
  -- the symbols declared without a source that nothing else numbers: constructors (the fragments
  -- and optional cells of a cell collection's cells), and functions with equations (a collection's
  -- `XCellMapKey`, its cells' initializers); projections, sort predicates, the counter's getter
  -- and the configuration's initializers are read as such
  let treeInits := (RCell.sortsList rconfig ++ ["GeneratedTopCell", "GeneratedCounterCell"]).map ("Lblinit" ++ ·)
  -- the cheap tests first: the kernel evaluates this for every such declaration of a tied text
  let known := fun (n : String) =>
    -- a sort predicate `isX`; a sort's projection `project:X` and a named argument's `project:#c:x`
    (dropPrefix? "Lblis" n).isSome || (dropPrefix? "Lblproject'Coln" n).isSome ||
    n == "LblgetGeneratedCounterCell" || ((dropPrefix? "Lblinit" n).isSome && treeInits.contains n) ||
    configSyms.contains n || (regSymNames.idxOf? n).isSome
  -- the names of `Scan.heads` (ite at a sort, the generated functions) that the equations of the
  -- initializers read as functions apply (a cell's outside the top tree, `initXCell(Init) =
  -- <x>(project:S(…))`), besides those of the user's axioms
  let initFns := (S.genSyms.filter fun s => let n := s.symbol.ident.ident.name
    (dropPrefix? "Lblinit" n).isSome && !known n).map (·.symbol.ident.ident.name)
  -- the top cell tree's initializers a user sentence applies, and those their equations apply
  -- (a node's initializer applies its children's): functions with the text's equations
  let isTreeInit := fun (n : String) => treeInits.contains n && S.eqs.any (·.fn == n)
  let treeHeads := fun (n : String) => (S.eqs.filter (·.fn == n)).flatMap fun e => extraHeads e.rhs
  let treeFns := Nat.repeat (fun (acc : List String) => (acc ++ (acc.flatMap treeHeads).filter isTreeInit).eraseDups)
    treeInits.length ((S.heads.flatten).eraseDups.filter isTreeInit)
  let heads := S.heads ++ (S.eqs.filter (fun e => initFns.contains e.fn || treeFns.contains e.fn)).filterMap fun e =>
    match extraHeads e.rhs with
    | [] => none
    | hs => some hs
  -- `append`, where a sentence applies it: a function with the prelude's equations
  let genFnNames := (if (heads.flatten).contains "append" then ["append"] else []) ++ treeFns
  -- a sort's projection `project:X` that a user sentence or such an initializer applies: a function
  -- with the text's equation `project:X(kseq(inj{X,KItem}(V), dotk)) = V` (without an equation, a
  -- parameter: `genDecls`); a library sort's is numbered as the definition's own (`Names.own`)
  let projNames := (heads.flatten).eraseDups.filter fun n => (dropPrefix? "Lblproject'Coln'" n).isSome
  let libProjNames := projNames.filter fun n => (regSymNames.idxOf? n).isSome
  -- the instances of the user's sort-parametric functions that a user sentence applies: each a
  -- function of the definition's own at its sorts (a parameter when the text gives it no equation)
  let instSyms := match S.paramDecls with
    | [] => []
    | ds =>
      let ownSorts : Names := { sorts := ownSortNames, syms := [] }
      ((heads.flatten).eraseDups.filterMap fun n => ds.findSome? (instDecl? n)).filter fun d =>
        (d.sort :: d.sorts).all fun X => (ownSorts.sortOf? X).isSome
  let libProjDecls := projNames.filterMap fun n =>
    if S.eqs.any (fun e => e.fn == n && !e.dom) then S.genSyms.find? (·.symbol.ident.ident.name == n) else none
  let genSyms := S.genSyms.filter (fun s =>
    let n := s.symbol.ident.ident.name
    !known n && (hasAttr s.attributes "constructor" || S.eqs.any (·.fn == n))) ++ libProjDecls
  -- a function without an equation and without `total` or `functional` is a parameter symbol: the
  -- text gives it no meaning, and a parameter's value is the interpretation's (`Semantics.paramVal`),
  -- as a function without clauses would have its rest, the interpretation's, everywhere
  let isTotalDecl := fun (s : Kore.SentenceSymbol) => hasAttr s.attributes "total" || hasAttr s.attributes "functional"
  -- the overloading symbols (`Semantics.ovls`): user symbols declared `anywhere`, neither
  -- constructors nor functions, that a symbol-overload axiom names first; each overloads the
  -- symbols its axioms name second. They are no functions, and are numbered last.
  let ovlAxs := S.eqs.filterMap fun e => (overloadSyms? e.attrs).map fun (f, g) => (f, g)
  let ovlDecls : List Kore.SentenceSymbol := match ovlAxs with
    | [] => []
    | _ => S.userSyms.filter fun s => hasAttr s.attributes "anywhere" && !isCtorDecl s &&
        !hasAttr s.attributes "function" && ovlAxs.any (·.1 == s.symbol.ident.ident.name)
  let ovlDeclNames := ovlDecls.map (·.symbol.ident.ident.name)
  let notOvl := fun (ns : List String) => match ovlDeclNames with
    | [] => ns
    | os => ns.filter (!os.contains ·)
  -- an instance without an equation is one whatever its totality: the declaration's `total`, which
  -- kompile states of every instance by one axiom quantified over the sort variables
  -- (`InertReason.parametricFunctional`), is the parameter's (`ParamPres.total`)
  -- an open generator (`isOpenGenerator`, declared `functional`) is a parameter without equations
  let clauseless := ((S.userSyms ++ collCells).filter fun s => !isCtorDecl s && (!isTotalDecl s || isOpenGenerator s) &&
    !S.eqs.any (·.fn == s.symbol.ident.ident.name)).map (·.symbol.ident.ident.name) ++
    (instSyms.filter fun s => !S.eqs.any (·.fn == s.symbol.ident.ident.name)).map (·.symbol.ident.ident.name)
  let ctorNames := ((S.userSyms ++ collCells ++ genSyms).filter isCtorDecl).map (·.symbol.ident.ident.name)
  -- the hooked symbols read as functions (`hookFnSym`), after the other functions
  let hookFnNames := (hookFnDecls S).map (·.symbol.ident.ident.name)
  let fnNames := notOvl (((S.userSyms ++ genSyms ++ instSyms).filter (!isCtorDecl ·)).map (·.symbol.ident.ident.name) |>.filter
    (!clauseless.contains ·)) ++ hookFnNames
  -- the definition's own hooked symbols are its parameter symbols, but those read as functions
  let paramNames := (S.userHooked.filter (!hookFnSym S ·)).map (·.symbol.ident.ident.name)
  -- an overload axiom of an overloading symbol is the kernel's overload equation (`ovlEqMissing`) of
  -- a constructor, an overloading symbol or a function with equations; one whose first symbol is a
  -- function is a clause of that function (`overloadEqn?`), whatever the second symbol is
  let fnDecls := notOvl (((S.userSyms ++ genSyms).filter (!isCtorDecl ·)).map (·.symbol.ident.ident.name))
  let _ ← S.eqs.mapM fun e => match overloadSyms? e.attrs with
    | some (f, g) =>
      if ovlDeclNames.contains f then Rd.within (.attrs e.attrs) (
        match ovlDecls.find? (·.symbol.ident.ident.name == f), S.syms.find? (·.symbol.ident.ident.name == g) with
        | some fd, some gd =>
          if isCtorDecl gd || ovlDeclNames.contains g || fnNames.contains g then match ovlEqMissing fd gd e with
            | none => pure ()
            | some m => fail .overloadForm m
          else fail .overloadForm s!"{g}: neither a constructor, an overloading symbol nor a function of the definition"
        | _, _ => fail .overloadForm s!"{g}: neither a constructor, an overloading symbol nor a function of the definition")
      else if fnDecls.contains f then pure ()
      else Rd.within (.attrs e.attrs) (fail .overloadAxiom f)
    | none => pure ()
  let N₀ : Names := { sorts := ownSortNames, macros := S.macros, own := libProjNames, carriers := S.carriers
                      syms := ownSortNames.map KoreAML.isLabel ++ RCell.symsList rconfig ++ ctorNames ++ fnNames ++
                        -- the generated functions after the productions' (`coreOf`), before the parameters
                        genFnNames ++ paramNames }
  -- the names applied that are numbered from their use: `ite` at its sorts, and the generated
  -- functions the KORE declares that have no number yet
  let extra := (heads.flatten).eraseDups.filter fun n => (N₀.sym? n).isNone
  let iteNames := extra.filter fun n => (dropPrefix? "Lblite{" n).isSome
  -- a generated function's argument and result sort names: its declaration's, or K's for
  -- `append`, which the kernel module declares
  let genDecls := (extra.filter (!iteNames.contains ·)).filterMap fun n =>
    match S.syms.find? (·.symbol.ident.ident.name == n) with
    | some s => (do pure (n, ← s.sorts.mapM sortName?, ← sortName? s.sort, isTotalDecl s))
    | none => none
  -- the definition's own functions, not its parameter symbols, with their result sorts (`keyCut`)
  let keyFns := ((S.userSyms ++ genSyms ++ instSyms ++ hookFnDecls S).filter fun s => !isCtorDecl s &&
    !clauseless.contains s.symbol.ident.ident.name && !ovlDeclNames.contains s.symbol.ident.ident.name).filterMap fun s =>
      do pure (← N₀.sym? s.symbol.ident.ident.name, ← sortName? s.sort)
  -- the overloading symbols, each after those it overloads
  let ovlOver := fun (f : String) => ((ovlAxs.filter (·.1 == f)).map (·.2)).eraseDups
  let ovlNames ← need (ovlOrder ovlDeclNames.length []
    (ovlDeclNames.map fun f => (f, (ovlOver f).filter ovlDeclNames.contains))) .overloadForm "overloads that are cyclic"
  -- the parameters without equations are numbered after the other parameters, in the order of
  -- `params`, and the overloading symbols last (`Semantics.ownSyms`)
  -- a value of each sort a constructor of the text's builds from `litValue?` arguments
  -- (`eqnPlaceholder`)
  let ctorVals := S.userSyms.filterMap fun s => if !hasAttr s.attributes "constructor" then none else do
    let X ← sortName? s.sort
    let args ← s.sorts.mapM fun A => (sortName? A).bind litValue?
    pure (X, KoreAML.ap s.symbol.ident.ident.name args)
  let N : Names := { N₀ with syms := N₀.syms ++ iteNames ++ genDecls.map (·.1) ++ clauseless ++ ovlNames,
                             keyFns := keyFns, ctorVals := ctorVals, fnlSyms := S.fnls,
                             eqUnstated := readerEqs.filterMap fun (f, σ, _) =>
                               if !S.hookEqFacts.contains (σ, false) then none else
                               match S.fnls.contains (σ, false), S.hookEqFacts.contains (σ, true) with
                               | true, true => none
                               | F, E => some (f, s!"{σ}: declared without " ++ " and ".intercalate
                                   ((if F then [] else ["its functional axiom"]) ++
                                    (if E then [] else [s!"((K1 {σ} K2) = true) = (K1 = K2)"]))) }
  -- the overloading symbols one of whose own overloads is a function of the definition, with
  -- their result sorts (`ovlCut`)
  let ovlCutSyms := ovlDecls.filterMap fun (d : Kore.SentenceSymbol) =>
    match (ovlOver d.symbol.ident.ident.name).any (fnNames.contains ·), N.sym? d.symbol.ident.ident.name,
        sortName? d.sort with
    | true, some g, some X => some (g, X)
    | _, _, _ => none
  -- the open generators (the `raw` parameters below), with their result sorts (`ovlCut`)
  let openCutSyms := ((S.userSyms ++ collCells ++ instSyms).filter fun h =>
      clauseless.contains h.symbol.ident.ident.name && isOpenGenerator h).filterMap fun h =>
    match N.sym? h.symbol.ident.ident.name, sortName? h.sort with
    | some g, some X => some (g, X)
    | _, _ => none
  let N : Names := { N with ovlCutSyms := ovlCutSyms, openCutSyms := openCutSyms }
  -- the definition's sorts declared with a library sort's hook, each with that sort (`hookImplAt`)
  let stands := (← S.colls.mapM fun (x, k, _) => do pure (← N.srtE x, (builtinColl k).sort)) ++
    (← (S.carriers.filter (userSortNames.contains ·.1)).mapM fun (x, b) => do pure (← N.srtE x, ← N.srtE b))
  let userParams ← (S.userHooked.filter (!hookFnSym S ·)).mapM fun h => Rd.within (.sentence (.hookedSymbol h)) do
    let hk ← need (attrStr? h.attributes "hook") .hookAttribute
    let sig : CtorSig := ⟨← N.symE h.symbol.ident.ident.name, ← h.sorts.mapM N.sortE, ← N.sortE h.sort⟩
    let pp : ParamPres := ⟨hk, attrStr? h.attributes "symbol'Kywd'", loc? h.attributes, srcOver src h.attributes,
      hasAttr h.attributes "total" || hasAttr h.attributes "functional"⟩
    pure (({ sig, impl := hookImplAt stands hk sig } : ParamSig), pp)
  let iteParams ← iteNames.mapM fun n => do
    let X ← N.srtE (String.ofList ((((dropPrefix? "Lblite{" n).getD "").toList).dropLast))
    let sig : CtorSig := ⟨← N.symE n, [Srt.bool, X, X], X⟩
    pure (({ sig, impl := some kIte } : ParamSig), (⟨"KEQUAL.ite", none, none, none, false⟩ : ParamPres))
  let genParams ← genDecls.mapM fun (n, args, res, tot) => do
    let sig : CtorSig := ⟨← N.symE n, ← args.mapM N.srtE, ← N.srtE res⟩
    pure (({ sig } : ParamSig), (⟨"", none, none, none, tot⟩ : ParamPres))
  let clauselessParams ← ((S.userSyms ++ collCells ++ instSyms).filter (clauseless.contains ·.symbol.ident.ident.name)).mapM
    fun h => Rd.within (.sentence (.symbol h)) do
      let sig : CtorSig := ⟨← N.symE h.symbol.ident.ident.name, ← h.sorts.mapM N.sortE, ← N.sortE h.sort⟩
      -- an open generator is a generator of its result sort (`Semantics.gens`), with the laws
      -- whose sentences the text writes (`Faithful.lawItemsK`)
      let raw := isOpenGenerator h
      let f := h.symbol.ident.ident.name
      let assoc := raw && holdsLaw m.sentences "assoc" (openAssocAx f h.sort)
      let idem := raw && holdsLaw m.sentences "idem" (openIdemAx f h.sort)
      pure (({ sig, raw, assoc, idem } : ParamSig),
        (⟨"", attrStr? h.attributes "symbol'Kywd'", loc? h.attributes, srcOver src h.attributes,
          isTotalDecl h⟩ : ParamPres))
  let params := userParams ++ iteParams ++ genParams ++ clauselessParams
  let ovls ← ovlNames.mapM fun f => do
    let d ← need (ovlDecls.find? (·.symbol.ident.ident.name == f)) .overloadForm f
    pure (⟨⟨← N.symE f, ← d.sorts.mapM N.sortE, ← N.sortE d.sort⟩, ← (ovlOver f).mapM N.symE⟩ : OvlSig)
  let genFns ← genFnNames.mapM fun n =>
    if n == "append" then
      fnFrom N src none appendEqns (fnClauses N src appendEqns n) n none ["K", "K"] "K" noLoc true
    else do
      let d ← need (S.syms.find? (·.symbol.ident.ident.name == n)) .missingEquation n
      Rd.within (.sentence (.symbol d)) (fnFrom N src (srcOver src d.attributes) S.eqs (fnClauses N src S.eqs n) n
        none (← d.sorts.mapM sortNameE) (← sortNameE d.sort) ((loc? d.attributes).getD noLoc) (isTotalDecl d))
  let config ← RCell.numList N rconfig
  let userSorts ← userSortNames.mapM N.srtE
  let colls ← S.colls.mapM (collSigOf N S.userHooked)
  pure ⟨src, rconfig, imports, !S.simpArg.isEmpty, userSortNames, N, params, config, userSorts,
    collCells, colls, genSyms, clauseless,
    ← libProjDecls.mapM fun s => N.srtE (((dropPrefix? "Lblproject'Coln'" s.symbol.ident.ident.name).getD "")),
    ← (S.tokenSorts.filter userSortNames.contains).mapM N.srtE, instSyms, ovlNames, ovls, genFns,
    ← (S.carriers.filter (userSortNames.contains ·.1)).mapM fun (x, b) => do pure (← N.srtE x, ← N.srtE b),
    hookFnNames⟩

/-- `symProdT`, its failures not yet placed. -/
def symProdBody (E : Env) (eqs : List RawEqn) (ov : List (String × List (Clause × ClausePres)))
    (s : Kore.SentenceSymbol) : Rd Prod := do
  let N := E.N
  let argNames ← s.sorts.mapM sortNameE
  let resName ← sortNameE s.sort
  let kywd := keyStr? s.attributes .symbol
  let label := s.symbol.ident.ident.name
  let sig : CtorSig := ⟨← N.symE label, ← argNames.mapM N.srtE, ← N.srtE resName⟩
  -- a constructor declared without a source (a freezer, a cell collection's fragment or optional
  -- cell) has no location
  if (source? s.attributes).isNone && hasKey s.attributes .constructor then pure (Prod.ctor sig ⟨kywd, none, none⟩)
  else do
    -- a function declared without a source has none either (`noLoc`)
    let l ← if (source? s.attributes).isNone then pure ((loc? s.attributes).getD noLoc)
      else need (loc? s.attributes) .location
    if hasKey s.attributes .constructor then pure (Prod.ctor sig ⟨kywd, some l, srcOver E.src s.attributes⟩)
    else do
      let cl := match ov.lookup label with
        | some C => Except.ok C
        | none => fnClauses N E.src eqs label
      -- `functional` is K's earlier name of `total`: a function with exactly one value at every argument
      let (f, fp) ← fnFrom N E.src (srcOver E.src s.attributes) eqs cl label kywd argNames resName l
        (hasKey s.attributes .total || hasKey s.attributes .functional)
      -- a hooked symbol read as a function keeps its hook, which its declaration is written with
      pure (Prod.fn f (if E.hookFns.contains label then { fp with hook := keyStr? s.attributes .hook } else fp))

/-- The production of a user symbol, with the clauses of the functions `ov` names given: `ov` is
a table of labels and clause lists, each proved equal to its `fnClauses` (`symProdT_eq`), so that
a function with many clauses is checked a block of clauses at a time. A failure is placed at the
symbol's declaration, a `hooked-symbol` sentence for a hooked symbol read as a function. -/
def symProdT (E : Env) (eqs : List RawEqn) (ov : List (String × List (Clause × ClausePres)))
    (s : Kore.SentenceSymbol) : Rd Prod :=
  Rd.within (.sentence (if E.hookFns.contains s.symbol.ident.ident.name
      then .hookedSymbol ⟨s.symbol, s.sorts, s.sort, s.attributes⟩ else .symbol s))
    (symProdBody E eqs ov s)

/-- The production of a user symbol: a constructor, a freezer, or a function with its clauses. -/
def symProd (E : Env) (eqs : List RawEqn) : Kore.SentenceSymbol → Rd Prod := symProdT E eqs []

theorem lookup_mem {β : Type} : ∀ {l : List (String × β)} {a : String} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: l, a, b, h => by
    by_cases hx : a = x
    · subst hx; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · have : (a == x) = false := by simp [hx]
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A table of clause lists, each its function's `fnClauses`, gives `symProd`. -/
theorem symProdT_eq {E : Env} {eqs : List RawEqn} {ov : List (String × List (Clause × ClausePres))}
    (h : ∀ p ∈ ov, fnClauses E.N E.src eqs p.1 = .ok p.2) : symProdT E eqs ov = symProd E eqs := by
  funext s
  have hcl : ∀ label : String, (match ov.lookup label with
      | some C => Except.ok C
      | none => fnClauses E.N E.src eqs label) = fnClauses E.N E.src eqs label := by
    intro label
    cases hl : ov.lookup label with
    | none => rfl
    | some C => exact (h _ (lookup_mem hl)).symm
  have h0 : ∀ label : String, (match ([] : List (String × List (Clause × ClausePres))).lookup label with
      | some C => Except.ok C
      | none => fnClauses E.N E.src eqs label) = fnClauses E.N E.src eqs label := fun _ => rfl
  simp only [symProd, symProdT, symProdBody, hcl, h0]

/-- A declaration event of the module, numbered: a subsort declaration between sorts the definition
has (its own or an imported module's, below one of its own), or a user constructor's declaration;
`none` for any other. -/
def eventOf (E : Env) (symProds : List Prod) : Sum String (String × String) → Option (Sum Sym (Srt × Srt))
  | .inr (x, y) =>
      let libNames := ((importsOf E.imports).flatMap (·.sorts)).map (regSortNames.getD · "")
      -- into one of the definition's sorts; from one of its sorts into a library sort; between
      -- library sorts, when the library's data does not hold it (the text's own declaration)
      let libSubs := ((importsOf E.imports).flatMap (·.subsorts)).map fun (a, b) => (regSortNames.getD a "", regSortNames.getD b "")
      -- or from one of the configuration's cell sorts into one of the user's sorts (`KCell < Pgm`)
      if (E.userSortNames.contains x || libNames.contains x) && E.userSortNames.contains y ||
          E.userSortNames.contains x && libNames.contains y ||
          libNames.contains x && libNames.contains y && !libSubs.contains (x, y) ||
          E.userSortNames.contains y && (RCell.sortsList E.rconfig).contains x then
        match E.N.srt? x, E.N.srt? y with
        | some a, some b => some (Sum.inr (a, b))
        | _, _ => none
      else none
  | .inl c =>
    match E.N.sym? c with
    | some f => if symProds.any (fun | .ctor c' _ => c'.name == f | _ => false) then some (Sum.inl f) else none
    | none => none

/-- The productions in the module's order: the user symbols' productions with the subsort
declarations merged in where the module declares them. -/
def prodsOf (S : Scan) (E : Env) (symProds : List Prod) : List Prod :=
  mergeProds symProds (S.events.filterMap (eventOf E symProds))

/-- `l.filterMap f`, a slice at a time: the `n` elements of `l` from `a` give `r`. -/
def FilterIs {α β : Type} (f : α → Option β) (l : List α) (a n : Nat) (r : List β) : Prop :=
  ((l.drop a).take n).filterMap f = r

theorem FilterIs.join {α β : Type} {f : α → Option β} {l : List α} {a n m k : Nat} {r₁ r₂ : List β}
    (h₁ : FilterIs f l a n r₁) (h₂ : FilterIs f l (a + n) m r₂) (hk : n + m = k) :
    FilterIs f l a k (r₁ ++ r₂) := by
  subst hk
  unfold FilterIs at *
  rw [List.take_add, List.filterMap_append, h₁, List.drop_drop, h₂]

theorem FilterIs.all {α β : Type} {f : α → Option β} {l : List α} {n : Nat} {r : List β}
    (hn : l.length = n) (h : FilterIs f l 0 n r) : l.filterMap f = r := by
  subst hn
  unfold FilterIs at h
  rwa [List.drop_zero, List.take_length] at h

theorem prodsOf_of_events {S : Scan} {E : Env} {sp : List Prod} {es : List (Sum Sym (Srt × Srt))}
    (h : S.events.filterMap (eventOf E sp) = es) : prodsOf S E sp = mergeProds sp es := by
  rw [prodsOf, h]

/-- The symbol f of the first top-level conjunct `V ∈ f(…)` of a condition with V among `bound`
whose term holds the variable i; `none` where there is none. -/
def openRefusalCutSym (bound : List Nat) (i : Nat) : Cond → Option Sym
  | .and p q => (openRefusalCutSym bound i p).orElse fun _ => openRefusalCutSym bound i q
  | .mem _ (.var v) (.app f as) =>
    if bound.contains v && (varOccs (.app f as)).contains i then some f else none
  | _ => none

/-- Why a rule whose left side leaves a variable open is not read, with the variable, its sort and
where it occurs; `none` where it is read. A variable the left side does not bind is read where the
values decide it (`rulesPlain`, Tie.lean): held by the right side under constructors, of a confined
sort, or held by closed conditions no variable of which the right side, the `ensures` or `post`
holds; and a rule that competes with a larger one has open condition variables of confined sorts,
or closed conditions. Otherwise the truth of a condition (`openRequires`) or the successor
(`openRight`) at given values differs between models of the text. For a variable in closed
conditions the detail names the first variable of the conditions that the rest of the rule holds;
for a variable in the term of a membership `V ∈ f(…)` of `pre`, V bound by the left side (a cut),
it names the symbol f (`openRefusalCutSym`). -/
def openRefusal (c : Semantics) (r : Rule) (names : List String) : Option (RefusalReason × String) :=
  let conf := fun i => (r.vars[i]?.map c.confined).getD false
  let what := fun i => s!"Var{names.getD i ""}:{c.sortName (r.vars.getD i 0)}"
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  let cut := fun i => match openRefusalCutSym (varOccs r.lhs) i r.pre with
    | some f => s!" (V ∈ {c.symName f}(…)), under {c.symName f}"
    | none => ""
  match r.opens.find? (fun i => !((ctorOccs c r.rhs).contains i || conf i ||
      (r.condVars.contains i && condApart))) with
  | some i =>
    if r.condVars.contains i then
      some (.openRequires, if r.reqClosed then
          let j := (r.condVars.find? rest.contains).getD i
          s!"{what i}: in a closed condition that holds {what j}, which the right side, the ensures or post holds; of a sort the text leaves unconfined"
        else s!"{what i}: in a condition with a variable the left side binds{cut i}, of a sort the text leaves unconfined")
    else some (.openRight, if r.exs.contains i then
        s!"{what i}: bound by \\exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's"
      else
        s!"{what i}: in the right side or the ensures under no constructor, not bound by the left side, of a sort the text leaves unconfined: the successor is a value through an element that is no value's")
  | none =>
    if r.reqOpen && c.rules.any (fun r' => r.prio < r'.prio) && !r.openCondVars.all conf && !r.reqClosed then
      let i := (r.openCondVars.find? (fun i => !conf i)).getD 0
      some (.openRequires,
        s!"{what i}: in a condition with a variable the left side binds{cut i}, of a sort the text leaves unconfined, in a rule of a priority below another's")
    else none

/-! ### Exhibited values

A rule read without a variable of the axiom it comes from (`splitRule`, `unheldBinders`) needs an
element of the variable's sort. The reader asks the search of Exhibit.lean for a value (`exhibit?`):
one applying no open generator, of which the built semantics gives the sort at every interpretation
of the parameters, where `Γ` entails an element of the sort in every model
(`Faithful.inhabited_of_exhibit_withHooks`). A sort without one found is refused
(`unheldVariable`): the search may miss a value, and a refusal states nothing. -/

/-- Why a rule read from a rewrite axiom without some of its variables (`unheldBinders` of its left
side, `splitRule`) is not read: a variable whose sort has no value the reader exhibits
(`exhibit?`), with the variable, its sort and the reason; `none` where every such sort has one. -/
def unheldRefusal (c : Semantics) (N : Names) (a : Kore.Axiom) : Option (RefusalReason × String) :=
  match a.pattern with
  | .rewrites _ (.and _ [l, _]) _ => match l with
    | .exist .. => (unheldBinders l).findSome? fun x =>
      let ok := match N.sortOf? x.sort with
        | some s => (exhibit? c s).isSome
        | none => false
      if ok then none else some (.unheldVariable,
        s!"{x.var.ident.name}:{((sortName? x.sort).getD "?")}: a variable of the axiom that a rule read from it does not hold, of a sort of which the reader exhibits no value: the axiom holds for every element of the sort, so where the sort has none it states nothing while the rule would step, and Γ entails neither an element of the sort nor its emptiness (the text's sorted theory gives every sort an element, which Γ does not state)")
    | _ => none
  | _ => none

/-- Why a function's clause is not read, with the variable, its sort and where it occurs; `none`
where it is read. A variable the arguments do not bind is read where the values decide the clause:
in its conditions, where they are closed or each such variable of them is of a confined sort
(`clausesPlain`'s conjunct, else `openRequires`: the condition's truth at given arguments differs
between models of the text). One held only by the right side or the `ensures` is read at every
sort: it is universal over the elements of its sort, so on values the clause has an instance for
each value of the sort and none where the sort has no value; the function is then named
(`Semantics.heldObligations`) where the sort has no exhibited value. -/
def clauseRefusal (c : Semantics) (cl : Clause) (names : List String) : Option (RefusalReason × String) :=
  let conf := fun i => (cl.vars[i]?.map c.confined).getD false
  let what := fun i => s!"Var{names.getD i ""}:{c.sortName (cl.vars.getD i 0)}"
  if !(!cl.reqOpen || cl.reqClosed || cl.openCondVars.all conf) then
    let i := (cl.openCondVars.find? (fun i => !conf i)).getD 0
    some (.openRequires,
      s!"{what i}: in a condition with a variable the arguments bind, not bound by the arguments, of a sort the text leaves unconfined")
  else none

/-- The memberships `V ∈ g(P̄)` among the top-level conjuncts of a condition, V a variable: each
with V, g and P̄. -/
def openCutMemsOf : Cond → List (Nat × Sym × List Term)
  | .and p q => openCutMemsOf p ++ openCutMemsOf q
  | .mem _ (.var v) (.app g as) => [(v, g, as)]
  | _ => []

/-- Why a rule read through the cut of an open generator (`ovlCut`) is not read, or `none`: a
membership `V ∈ g(P̄)` of `pre`, V bound by the left side and g an open generator whose sort is not
confined, whose arguments hold a variable that no other part of the left side holds
(`openGeneratorPattern`). Such a variable ranges over elements of g's argument sorts that the
interpretation may send to a value, elements that are no value's among them, and which those are
the text does not say. Where every variable of P̄ is held elsewhere in the left side, the
membership is a condition over bound variables and the rule is decided as any other. -/
def openCutRefusal (c : Semantics) (r : Rule) (names : List String) : Option (RefusalReason × String) :=
  let held := varOccs r.lhs
  (openCutMemsOf r.pre).findSome? fun (v, g, as) =>
    match c.params.find? (fun k => k.raw && k.sig.name == g) with
    | some k =>
      if held.contains v && !c.confined k.sig.result then
        ((varOccs (.app g as)).find? (!held.contains ·)).map fun i =>
          let sn := c.sortName k.sig.result
          (.openGeneratorPattern, s!"{c.symName g}: its sort {sn} is recursive or reaches an unconfined sort: the arguments it matches depend on elements of {sn} the text does not name (Var{names.getD i ""}:{c.sortName (r.vars.getD i 0)}, under {c.symName g}, held by no other part of the left side)")
      else none
    | none => none

/-- Why a rule is not read (`unheldRefusal`, then `openCutRefusal`, then `openRefusal`), or
`none`. -/
def ruleRefusal (c : Semantics) (N : Names) (a : Kore.Axiom) (r : Rule) (names : List String) :
    Option (RefusalReason × String) :=
  ((unheldRefusal c N a).orElse fun _ => openCutRefusal c r names).orElse fun _ => openRefusal c r names

/-- The core from the productions and the rules, before the rules are checked (`coreOf`). -/
def coreBase (S : Scan) (E : Env) (prods : List Prod) (rules : List (Rule × RulePres)) : Rd Semantics := do
  let ctors := prods.filterMap fun | .ctor k kp => some (k, kp) | _ => none
  let fns := prods.filterMap (fun | .fn f fp => some (f, fp) | _ => none) ++ E.genFns
  let pgm ← pgmSortOf E.N S.eqs
  let lib := libOf E.imports
  let core : Semantics :=
       { lib := { lib with tokenSorts := lib.tokenSorts ++ E.tokenSorts, carriers := E.carriers }, sortNames := E.N.sorts, symNames := E.N.syms
         userSorts := Cell.topSorts E.config ++ E.userSorts
         ctors := Cell.topSigs E.config ++ ctors.map (·.1), fns := fns.map (·.1)
         userSubsorts := Cell.topSubs E.config ++ prods.filterMap fun | .subsort a b => some (a, b) | _ => none
         pgmSort := pgm, rules := rules.map (·.1)
         params := usedLibParams E.imports (fns.map (·.1)) (rules.map (·.1)) ++ E.params.map (·.1)
         colls := E.colls, ovls := E.ovls }
  pure core

/-- The character `c` as it is written inside a string literal: `\n`, `\t`, `\\` and `\"` escaped,
another character below 32 and DEL as `\x` and two hexadecimal digits, any other as itself. -/
def charLit_skel (c : Char) : String :=
  if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else if c = '\\' then "\\\\"
  else if c = '\"' then "\\\""
  else if c.toNat ≤ 31 ∨ c = '\x7f' then "\\x" ++ hexDigitRepr (c.toNat / 16) ++ hexDigitRepr (c.toNat % 16)
  else String.singleton c

/-- The string `s` as a string literal: in double quotes, each character as `charLit_skel` writes
it (the text `String.quote` gives, by functions the kernel unfolds). -/
def strLit_skel (s : String) : String :=
  "\"" ++ String.join (s.toList.map charLit_skel) ++ "\""

/-- A pattern's symbols, variables as `_` and domain values as their text, `fuel` levels deep. -/
def eqnSkel : Nat → Kore.Pattern → String
  | 0, _ => "…"
  | _, .var (.evar _) => "_"
  | _, .dv _ v => strLit_skel v
  | n + 1, .app h _ ps => h.ident.name ++ (if ps.isEmpty then "" else "(" ++ ", ".intercalate (ps.map (eqnSkel n)) ++ ")")
  | n + 1, .and _ ps => "\\and(" ++ ", ".intercalate (ps.map (eqnSkel n)) ++ ")"
  | n + 1, .equals _ _ p q => "\\equals(" ++ eqnSkel n p ++ ", " ++ eqnSkel n q ++ ")"
  | _, p => connective p

/-- An equation's shape: its left side, right side, `requires` and `ensures` (`eqnSkel`, four levels),
`[owise]` when it has competitors, `[selector-domain]` for a projection's selector-domain axiom. -/
def eqnShape (e : RawEqn) : String :=
  s!"{e.fn}({", ".intercalate (e.pats.map (eqnSkel 4))}) = {eqnSkel 4 e.rhs}" ++
    (match e.req with | some r => s!" requires {eqnSkel 4 r}" | none => "") ++
    (match e.ens with | some r => s!" ensures {eqnSkel 4 r}" | none => "") ++
    (if e.competitors.isSome then " [owise]" else "") ++ (if e.dom then " [selector-domain]" else "")

/-- Two clauses are one, for clauses without a predicate: every field but `pre` and `post` equal,
and those `\top` in both (false of two equal clauses with another predicate). -/
def clauseSame (a b : Clause) : Bool :=
  let opt := fun (x y : Option Term) => match x, y with
    | none, none => true
    | some t, some u => Term.beq t u
    | _, _ => false
  a.vars == b.vars && Term.beqList a.pats b.pats && opt a.req b.req && Term.beq a.rhs b.rhs && opt a.ens b.ens &&
    a.prio == b.prio && a.aside == b.aside && a.exs == b.exs &&
    a.pre.isTop && a.post.isTop && b.pre.isTop && b.post.isTop

/-- The equation `e` of the text, of the sort predicate `fn` (a function of
`Semantics.sortPreds`), is a sentence `Γ` states (`ΓFns` over `allFns`), `eqs` the text's
equations:
- `e` has no `requires` and no `ensures`, and read as a function's clause (`clause?`, an `[owise]`
  one at its priority) it is a clause `cl` of `fn` (`clauseSame`);
- where `e` is an `[owise]` equation, its exclusion has exactly one disjunct for each clause of
  `fn` that is before `cl` (not `aside`, of a smaller priority: `Faithful.lowerClauses`), and each
  of those clauses is read from an equation of the text with its disjunct, the disjuncts matched to
  the equations by content (`pairExcl`, as a function's are, `fnFrom`).
`Γ` reads `cl` as applying where no clause before it does, and the text's sentence applies where
no disjunct holds. With a disjunct for no clause of `fn` the sentence is silent where `Γ` gives a
value; with a clause of `fn` that no disjunct excludes the sentence gives a value where `Γ` gives
that clause's. -/
def predEqnOK (N : Names) (msrc : String) (eqs : List RawEqn) (fn : Fn) (e : RawEqn) : Bool :=
  let plain := fun (e' : RawEqn) =>
    if e'.req.isNone && e'.ens.isNone && !e'.dom then (clause? N msrc e' none).toOption.map (·.1) else none
  match plain e with
  | none => false
  | some cl => fn.clauses.any (clauseSame cl) &&
    match e.competitors with
    | none => true
    | some ds =>
      let before := fn.clauses.filter fun cl' => !cl'.aside && cl'.prio < cl.prio
      let own := eqs.filter fun e' => e'.fn == e.fn && e'.competitors.isNone
      -- for each clause before `cl`, an equation of the text that reads to it
      match before.mapM fun lc => (own.find? fun e' => (plain e').any (clauseSame · lc)).map (·, lc) with
      | none => false
      | some es => ds.length == es.length &&
        ((pairExcl (es.map (·.1)) ds).zip es).all fun ((e', ex), (_, lc)) =>
          match clause? N msrc e' ex with
          | .ok (cl', _) => clauseSame cl' lc
          | .error _ => false

/-- Whether an equation of a sort's predicate or of a sort's projection, where no function of `c`
holds it as a clause, is a sentence `c` accounts for; `none` for an equation of another symbol.
- A sort predicate's (`isX`, a function of `Semantics.sortPreds`): `predEqnOK`.
- A sort X's projection `project:X` (X a library sort or one of `c`'s): the equation
  `project:X(P) = V`, P the pattern of `selectorPat` at the variable V of sort X (`projEqnShape`),
  or its selector-domain axiom (`projDomainEqn?`, whose form `projectionDomain?` checks:
  `project:X(K)` is defined exactly where K is such a P), where `c` does not number `project:X`
  (no sentence `c` reads applies it; one that does makes it a function of `c` with this equation,
  `Presentation.libProjs`): the symbol is in no sentence of `Γ` (the registry's `projectSym X`,
  or, for a library sort whose projection the registry numbers no symbol for, such as Range and
  RangeMap, a symbol of no signature `Γ` has), and the equation defines it on the image of the
  injection. -/
def predProjOK? (N : Names) (msrc : String) (eqs : List RawEqn) (c : Semantics) (e : RawEqn) : Option Bool :=
  match dropPrefix? "Lblproject'Coln'" e.fn with
  | some X =>
    if regSortNames.contains X || c.sortNames.contains X then
      some (!c.symNames.contains e.fn && (projEqnShape X e || e.dom))
    else none
  | none =>
    if (dropPrefix? "Lblis" e.fn).isSome then
      (c.sortPreds.find? (c.symName ·.label == e.fn)).map (predEqnOK N msrc eqs · e)
    else none

/-- The equations of the text of a sort's predicate or projection that the core `c` does not
state: no function of `c` holds the equation as a clause and it is none of the sentences
`predProjOK?` accepts. Each is a failure at the equation: `generatedEquation` with the symbol and
the shape (`eqnShape`), or `unaccounted` for an equation written in a user's file. -/
def predEqnFaults (N : Names) (msrc : String) (eqs : List RawEqn) (c : Semantics) : List Fault :=
  eqs.filterMap fun e =>
    if predProjOK? N msrc eqs c e == some false && !c.fns.any (c.symName ·.label == e.fn) then
      some (if isUserSource e.attrs then
          ⟨.unaccounted, s!"equation of {e.fn}, which the definition reads from its sorts: {eqnShape e}", .attrs e.attrs⟩
        else ⟨.generatedEquation, s!"{e.fn}: {eqnShape e}", .attrs e.attrs⟩)
    else none

/-- The open generator `k`'s sort is flat and no constructor or overloading symbol bears its
name: `Faithful.genWf`'s last conjunct at `k`. -/
def openFlat (c : Semantics) (k : ParamSig) : Bool :=
  c.ctorSigs.all (fun g => g.name != k.sig.name && (g.result != k.sig.result || g.args.isEmpty)) &&
  c.ovlSigs.all (fun g => g.name != k.sig.name && g.result != k.sig.result) &&
  c.subsorts.all (fun p => p.2 != k.sig.result)

/-- The ways the open generator `k`'s sort is not flat, or `k` bears another symbol's name. -/
def openFlatFaults (c : Semantics) (k : ParamSig) : List String :=
  let s := k.sig.result
  (if c.ctorSigs.any (fun g => g.result == s && !g.args.isEmpty) then ["a constructor with arguments"] else []) ++
  (if c.ovlSigs.any (fun g => g.result == s) then ["an overloading symbol"] else []) ++
  (if c.subsorts.any (fun p => p.2 == s) then ["a subsort"] else []) ++
  (if c.ctorSigs.any (·.name == k.sig.name) || c.ovlSigs.any (·.name == k.sig.name) then
    ["a constructor or an overloading symbol of its name"] else [])

/-- Why the open generator `k` of `c` is not read, or `none`. Its sort's values are the
applications of the sort's generators, among them `k`'s (the no-junk sentence the text writes),
which `Γ` states of a constructor sort only. And the text writes no sentence that keeps the
generator's applications out of a constructor's or an injection's image at an element no term
denotes: where the sort has a constructor with arguments or a subsort, a model of the text may
send an application of `k` to such an image (`s(z)` for an element `z` that is no value's, or an
injected Int that is no literal), where no rule's match at values sees it, and a sentence's truth
there needs that element to be a value's. Where the sort is flat (every constructor of it nullary,
no overloading symbol into it and no subsort below it) an application of `k` to values is a value
apart from every other value of the sort. These are `Faithful.genWf`'s conjuncts for a `raw`
parameter (`openGenFault_none`). -/
def openGenFault (c : Semantics) (k : ParamSig) : Option String :=
  if !(Faithful.consSorts c).contains k.sig.result then some "its result sort is no constructor sort"
  else if !openFlat c k then
    some s!"its sort {c.sortName k.sig.result} has a constructor with arguments, an overloading symbol or a subsort (here {", ".intercalate (openFlatFaults c k)}): the text writes no sentence that keeps the generator's applications out of the constructor's or the injection's image at an element no term denotes"
  else none

/-- An open generator the reader reads meets `Faithful.genWf`'s conjuncts for a `raw` parameter. -/
theorem openGenFault_none {c : Semantics} {k : ParamSig} (h : openGenFault c k = none) :
    (Faithful.consSorts c).contains k.sig.result = true ∧ openFlat c k = true := by
  cases hc : (Faithful.consSorts c).contains k.sig.result with
  | false => unfold openGenFault at h; rw [hc] at h; simp at h
  | true =>
    cases hf : openFlat c k with
    | false => unfold openGenFault at h; rw [hc, hf] at h; simp at h
    | true => exact ⟨rfl, rfl⟩

/-- The core from the productions and the rules. The configuration's cells are ordinary sorts,
constructors and subsorts of it, before the user's (`Cell.topSorts`, `Cell.topSigs`,
`Cell.topSubs` of the cell tree). The definition's token sorts (`Env.tokenSorts`) are token sorts
of the semantics after the imported modules' (`Lib.tokenSorts`): their values are their literals.
A rule that is not read (`ruleRefusal`) is refused at its axiom; then the first clause of a
function that is not read (`clauseRefusal`), at its equation; then the first equation of a sort's
predicate or projection that the core does not state (`predEqnFaults`), at that equation: the core
defines the sort predicates from the sorts (`Semantics.sortPreds`), so a text whose equations of
one are others is a text one of whose sentences the core would not state. -/
def coreOf (S : Scan) (E : Env) (prods : List Prod) (rules : List (Rule × RulePres)) : Rd Semantics := do
  let core ← coreBase S E prods rules
  -- a constructor of the text into a sort that is no constructor sort (`ctorResultSort`)
  match core.ctors.find? (fun k => !(Faithful.consSorts core).contains k.result) with
  | some k =>
    let n := core.symName k.name
    let s := k.result
    let kind := if core.colls.any (·.sort == s) then "a collection sort of the text"
      else if (core.collOf s).isSome then "a collection sort of the library"
      else if core.lib.tokenSorts.contains s then "a token sort"
      else if core.lib.carriers.any (·.1 == s) then "a sort hooked to a library carrier"
      else "a library sort whose values are no constructor terms"
    let site := match S.syms.find? (·.symbol.ident.ident.name == n) with
      | some d => Site.sentence (.symbol d)
      | none => .unset
    Rd.within site (fail .ctorResultSort s!"{n}: result sort {core.sortName s}, {kind}")
  | none => pure ()
  -- an open generator into a sort that is no flat constructor sort (`openGenFault`)
  match core.params.findSome? (fun k => if k.raw then (openGenFault core k).map (k, ·) else none) with
  | some (k, why) =>
    let n := core.symName k.sig.name
    let site := match S.syms.find? (·.symbol.ident.ident.name == n) with
      | some d => Site.sentence (.symbol d)
      | none => .unset
    Rd.within site (fail .openGenerator s!"{n}: {why}")
  | none => pure ()
  match (S.rewrites.zip rules).findSome? (fun (a, r, rp) => (ruleRefusal core E.N a r rp.names).map (a, ·)) with
  | some (a, reason, detail) => Rd.within (.sentence (.axiom a)) (fail reason detail)
  | none =>
    let fnCls := prods.flatMap fun | .fn f fp => withPres f.clauses fp.clauses | _ => []
    match fnCls.findSome? (fun (cl, cp) => (clauseRefusal core cl cp.names).map (cp, ·)) with
    | some (cp, reason, detail) =>
      -- the equation the clause is read from, found by its id
      match S.eqs.find? (fun e => (eqnInfo? e.attrs).any (·.uid == cp.info.uid)) with
      | some e => Rd.within (.attrs e.attrs) (fail reason detail)
      | none => fail reason detail
    | none => match predEqnFaults E.N E.src S.eqs core with
      | f :: _ => .error f
      | [] => pure core

/-! ## The counter's getter and the cell tree's initializers

`getGeneratedCounterCell` and the initializer `initXCell` of a cell of the top cell tree are, where
no read sentence applies them, symbols of neither the registry nor the definition: `Γ` holds no
sentence naming them. The text's sentences naming such a symbol f state nothing over `Γ`'s
signature exactly where every model of `Γ` extends by an interpretation of f satisfying them. One
equation `x̄ ∈ p̄ → f(x̄) = t` without conditions, the variables of `t` among those of `p̄`, each
point matched at one valuation at most, and `t` over symbols that have an interpretation already,
is satisfied by taking f to be `t`'s value. A second equation states that two right sides agree,
an `ensures` is stated under the premise whatever f is, and a right-side variable no pattern holds
makes `f(x̄) = y` hold of every `y`: each a sentence over `Γ`'s signature. A `functional` axiom of
f states with the equation that `t` has exactly one value. -/

/-- The name of the counter's getter. -/
def getterName : String := "LblgetGeneratedCounterCell"

mutual
  /-- The symbols a pattern of applications, element variables and domain values applies, each
  with its sort arguments, and the variables it holds; `none` where it holds anything else. -/
  def initAtoms : Kore.Pattern → Option (List (String × List Kore.KSort) × List Kore.EVar)
    | .var (.evar x) => some ([], [x])
    | .dv _ _ => some ([], [])
    | .app h ss ps => (initAtomsList ps).map fun (hs, xs) => ((h.ident.name, ss) :: hs, xs)
    | _ => none
    termination_by structural p => p
  def initAtomsList : List Kore.Pattern → Option (List (String × List Kore.KSort) × List Kore.EVar)
    | [] => some ([], [])
    | p :: ps => match initAtoms p, initAtomsList ps with
      | some (hs, xs), some (hs', xs') => some (hs ++ hs', xs ++ xs')
      | _, _ => none
    termination_by structural ps => ps
end

/-- `f` is a symbol of the registry or of `c`. -/
def symOfDefn (c : Semantics) (f : String) : Bool := regSymNames.contains f || c.symNames.contains f

/-- **The getter's equation is the one the account takes** (`e` among the text's equations `eqs`):
it is the only equation of the getter, it has no `requires`, no `ensures` and no exclusion, its
one pattern is the top cell's constructor at distinct element variables, and its right side is the
last of them. The constructor is injective, so the equation defines the getter on the
constructor's image and states nothing of another symbol. -/
def getterEqnOK (c : Semantics) (eqs : List RawEqn) (e : RawEqn) : Bool :=
  e.fn == getterName && (eqs.filter (·.fn == getterName)).length == 1 &&
  e.req.isNone && e.ens.isNone && e.competitors.isNone && !e.dom &&
  match e.pats, e.rhs with
  | [.app h [] args], .var (.evar v) =>
    h.ident.name == c.symName topLabel &&
    match distinctEVars? args with
    | some xs => decide (xs.getLast? = some v)
    | none => false
  | _, _ => false

/-- The initializers of the cells strictly below `x`. -/
def initsBelow (c : Semantics) (x : Cell) : List String := (x.all.drop 1).map (·.initLabel c)

/-- **The equation of the initializer of the cell `x` is one the account takes** (`e` among the
text's equations `eqs`): it is the only equation of the initializer, it has no `requires`, no
`ensures` and no exclusion, its patterns are distinct element variables, every variable of its
right side is one of them, and its right side applies only `inj`, symbols of the registry or of
`c` (an instance of a sort-parametric symbol by its instance's name), initializers of cells
strictly below `x`, and sort projections each of whose equations `predProjOK?` accounts. The
initializers below are checked at their own equations, so the order is the tree's. -/
def initEqnOK (N : Names) (msrc : String) (eqs : List RawEqn) (c : Semantics) (x : Cell) (e : RawEqn) : Bool :=
  let L := x.initLabel c
  e.fn == L && (eqs.filter (·.fn == L)).length == 1 &&
  e.req.isNone && e.ens.isNone && e.competitors.isNone && !e.dom &&
  match distinctEVars? e.pats, initAtoms e.rhs with
  | some xs, some (hs, ys) =>
    ys.all (evarIn xs) &&
    hs.all fun (h, ss) =>
      if h == "inj" then true
      else if !ss.isEmpty then match ss.mapM sortName? with
        | some ns => symOfDefn c (if h == "Lblite" then (ns.head?.map iteName).getD "" else instName h ns)
        | none => false
      else symOfDefn c h || (initsBelow c x).contains h ||
        ((dropPrefix? "Lblproject'Coln'" h).isSome &&
          (eqs.filter (·.fn == h)).all fun e' => predProjOK? N msrc eqs c e' == some true)
  | _, _ => false

/-- The symbol named `h` is interpreted and total: a registry hook outside `partialHooks`, or a
parameter of `c` whose `impl` is one (it has that hook's meaning). -/
def totalInterp (c : Semantics) (h : String) : Bool :=
  let tot := fun (g : Sym) => hookSigs.any (·.name == g) && !partialHooks.contains g
  (match regSymNames.idxOf? h with
    | some g => tot g
    | none => false) ||
  c.params.any fun k => c.symName k.sig.name == h && match k.impl with
    | some g => tot g
    | none => false

/-- **The right side of the equation `e` of the initializer of `x` has exactly one value at every
valuation**, which is what a `functional` axiom of the initializer states with the equation: it
applies only `inj`, constructors of `c`, interpreted total symbols (`totalInterp`) and
initializers of cells strictly below `x` whose own `functional` axiom the text holds (`funcs`:
the symbols of the text's `functional` axioms). No projection, no function of `c`, no parameter
without a meaning. -/
def initTotalOK (funcs : List String) (c : Semantics) (x : Cell) (e : RawEqn) : Bool :=
  match initAtoms e.rhs with
  | some (hs, _) => hs.all fun (h, ss) =>
      h == "inj" || (ss.isEmpty &&
        (c.ctorSigs.any (c.symName ·.name == h) || totalInterp c h ||
          ((initsBelow c x).contains h && funcs.contains h)))
  | none => false

mutual
  /-- The value of a ground term of literals, injections, constructors of `c` and interpreted
  symbols (a registry hook, or a parameter of `c` whose `impl` is one), each hook applied to
  values where it gives one (`hook`); `none` otherwise. -/
  def initGroundVal (c : Semantics) : Term → Option GroundTerm
    | .dv s l => some (.dv s l)
    | .inj a b t => (initGroundVal c t).map (.inj a b)
    | .app f ts => do
      let vs ← initGroundVals c ts
      if c.ctorSigs.any (·.name == f) then some (.ctor f vs)
      else
        let g := match c.params.find? (·.sig.name == f) with
          | some k => k.impl
          | none => some f
        match g.bind (hook · vs) with
        | some (some v) => some v
        | _ => none
    | _ => none
    termination_by structural t => t
  /-- `initGroundVal` of each term. -/
  def initGroundVals (c : Semantics) : List Term → Option (List GroundTerm)
    | [] => some []
    | t :: ts => do pure ((← initGroundVal c t) :: (← initGroundVals c ts))
    termination_by structural ts => ts
end

/-- The right side of the equation `e` has exactly one value because it is ground and its value is
computed: literals, injections, constructors, and interpreted symbols each applied to values where
its meaning gives a value (a partial hook among them, `<s> SetItem(1) SetItem(2) </s>`). `Γ` states
each interpreted symbol's graph on values, so the term denotes that value. -/
def initGroundOK (N : Names) (c : Semantics) (e : RawEqn) : Bool :=
  match term N [] e.rhs with
  | .ok (t, []) => (initGroundVal c t).isSome
  | _ => false

/-- The `functional` axiom of the initializer of `x` is one the account takes: the initializer's
equation is (`initEqnOK`) and its right side has exactly one value (`initTotalOK`, or
`initGroundOK`). -/
def initFunctionalOK (N : Names) (msrc : String) (eqs : List RawEqn) (funcs : List String) (c : Semantics)
    (x : Cell) : Bool :=
  match eqs.find? (·.fn == x.initLabel c) with
  | some e => initEqnOK N msrc eqs c x e && (initTotalOK funcs c x e || initGroundOK N c e)
  | none => false

/-- The symbols of the text's `functional` axioms. -/
def functionalSyms (events : List (Sum String (String × String))) : List String :=
  events.filterMap fun
    | .inl f => some f
    | .inr _ => none

/-- The sentences of the getter and of the initializers of the cell tree `top`, each no symbol of
the registry or of `c`, that the account does not take, as failures: an equation outside
`getterEqnOK` or `initEqnOK`, `generatedEquation` with the symbol and the shape (`eqnShape`), at
the equation; a `functional` axiom outside `initFunctionalOK`, `generatedEquation` with the symbol
and what the axiom states, at the axiom. An initializer that is a function of `c` has its
equations as clauses and is not listed. -/
def initFaults (N : Names) (msrc : String) (sents : List Kore.Sentence) (eqs : List RawEqn)
    (funcs : List String) (c : Semantics) (top : Cell) : List Fault :=
  -- the equations of the getter and of the initializers: the others are not looked at again
  let ieqs := eqs.filter fun e => e.fn == getterName || (dropPrefix? "Lblinit" e.fn).isSome
  let eqFault := fun (e : RawEqn) => (⟨.generatedEquation, s!"{e.fn}: {eqnShape e}", .attrs e.attrs⟩ : Fault)
  let getter := if symOfDefn c getterName then [] else
    (ieqs.filter fun e => e.fn == getterName && !getterEqnOK c ieqs e).map eqFault
  let cells := top.all.filter fun x => !symOfDefn c (x.initLabel c)
  let inits := cells.flatMap fun x =>
    (ieqs.filter fun e => e.fn == x.initLabel c && !initEqnOK N msrc eqs c x e).map eqFault
  let fns := cells.filterMap fun x =>
    let L := x.initLabel c
    if funcs.contains L && !initFunctionalOK N msrc eqs funcs c x then
      some (⟨.generatedEquation, s!"{L}: functional axiom of a cell's initializer whose equation's right side the definition does not give exactly one value at every argument",
        match sents.find? (fun s => scanEvent s == some (.inl L)) with
        | some s => .sentence s
        | none => .unset⟩ : Fault)
    else none
  getter ++ inits ++ fns

/-! ## The laws of functions

An `[assoc]`, `[comm]`, `[unit]` or `[idem]` axiom whose symbol is a function of the definition and
no collection's concatenation states an equation between applications of the function for every
element: `f(f(K1, K2), K3) = f(K1, f(K2, K3))` and the like. The function's value is its clauses'
where one applies and the interpretation's elsewhere (`Semantics.fnRest`), so the equation reads
the interpretation. It is read as a `LawEq` of `Presentation.laws`, which `Γ` does not hold: the
statements take it at values, under `FnLaws`, which the account lists as owed. -/

/-- The symbol named `h` is a function of `c`, or a parameter that no registry hook implements and
that is no open generator (a `function` production without equations), and no collection's
concatenation. -/
def fnLawHead (c : Semantics) (h : String) : Bool :=
  (c.fns.any (c.symName ·.label == h) ||
    c.params.any fun k => k.impl.isNone && !k.raw && c.symName k.sig.name == h) &&
  !c.allColls.any (c.symName ·.concat == h)

/-- The law axioms of the sentences `ss` whose symbol is a function of `c` and no collection's
concatenation (`fnLawHead`), each with its position: the axioms classified as a collection's laws
(`InertReason.collectionLaw`, `UnreadReason.setIdempotence`) by their shape alone. -/
def fnLawAxioms (c : Semantics) (ss : List Kore.Sentence) : List (Nat × Kore.Axiom) :=
  ss.zipIdx.filterMap fun (s, i) => match s, classify s with
    | .axiom a, .inert .collectionLaw | .axiom a, .unread .setIdempotence =>
      if (lawHead? a).any (fnLawHead c) then some (i, a) else none
    | _, _ => none

/-! ### The laws of open generators

An `[assoc]` or `[idem]` axiom of an open generator (a `raw` parameter) is the law sentence `Γ`
holds for it (`Faithful.lawItemsK`, `Faithful.assocAxK`, `Faithful.idemAxK`): the reader sets
`ParamSig.assoc` or `ParamSig.idem` where the text writes that sentence (`openAssocAx`,
`openIdemAx`), and the interpretations the statements speak of satisfy it at values (`OpenLaws`,
owed). Both laws together are read (`lawHooks` exhibits an interpretation satisfying both). A unit
law of an open generator is refused `openLaw`: `ParamSig` has no field for it. -/

/-- The law axiom `a` is the associativity or idempotence sentence of an open generator of `c`
whose law the semantics holds (`ParamSig.assoc`, `ParamSig.idem`). -/
def openLawRead (c : Semantics) (a : Kore.Axiom) : Bool :=
  c.params.any fun k =>
    let f := c.symName k.sig.name
    let s := KoreAML.srt (c.sortName k.sig.result)
    k.raw && ((k.assoc && lawSentenceIs "assoc" (openAssocAx f s) a) ||
      (k.idem && lawSentenceIs "idem" (openIdemAx f s) a))

/-- The law axioms of the sentences `ss` read as the laws of an open generator of `c`
(`openLawRead`), each with its position. -/
def openLawAxioms (c : Semantics) (ss : List Kore.Sentence) : List (Nat × Kore.Axiom) :=
  ss.zipIdx.filterMap fun (s, i) => match s, classify s with
    | .axiom a, .inert .collectionLaw | .axiom a, .unread .setIdempotence =>
      if openLawRead c a then some (i, a) else none
    | _, _ => none

mutual
  /-- The pattern with each element variable `K` named `VarK`, the names `term` reads; `none`
  where it holds anything but applications, element variables and domain values. -/
  def lawVarsNamed : Kore.Pattern → Option Kore.Pattern
    | .var (.evar x) => some (.var (.evar { x with var := { x.var with ident := { x.var.ident with name := "Var" ++ x.var.ident.name } } }))
    | .dv s t => some (.dv s t)
    | .app h ss ps => (lawVarsNamedList ps).map (.app h ss ·)
    | _ => none
    termination_by structural p => p
  def lawVarsNamedList : List Kore.Pattern → Option (List Kore.Pattern)
    | [] => some []
    | p :: ps => match lawVarsNamed p, lawVarsNamedList ps with
      | some q, some qs => some (q :: qs)
      | _, _ => none
    termination_by structural ps => ps
end

/-- Both sides of the law have one sort in the context of right sides, that sort is one of the
definition's, and each of its variables occurs in one of them: `Faithful`'s `lawSorted`, which this
module does not import, by the same body (test/OpenGenerator.lean checks the two are equal). -/
def fnLawSorted (c : Semantics) (l : LawEq) : Bool :=
  let x := c.rhsCtx (c.fns.map Fn.sig)
  (sortOfTerm x l.vars l.lhs).any (· < nRegSorts + c.sortNames.length) &&
    sortOfTerm x l.vars l.lhs == sortOfTerm x l.vars l.rhs &&
    binds l.vars.length (varOccs l.lhs ++ varOccs l.rhs)

/-- The law the axiom `a` states, `\equals{S,R}(lhs, rhs)` over its free element variables. -/
def fnLawOf (N : Names) (a : Kore.Axiom) : Rd LawEq := Rd.within (.sentence (.axiom a)) do
  match a.pattern with
  | .equals _ _ l r =>
    let detail := s!"{(lawHead? a).getD ""}: {", ".intercalate (lawKeys a)}: a side that is no term"
    let l ← need (lawVarsNamed l) .lawAxiom detail
    let r ← need (lawVarsNamed r) .lawAxiom detail
    let (lt, vs) ← term N [] l
    let (rt, vs) ← term N vs r
    pure { vars := ← varSorts N vs, lhs := lt, rhs := rt }
  | _ => fail .lawAxiom s!"{(lawHead? a).getD ""}: no equation"

/-- The law the axiom `a` states (`fnLawOf`), where both its sides are of one sort and every variable
is in a side (`fnLawSorted`): the law's sentence is then `Faithful.lawPattern`'s, whose model
`consistent_with_laws` exhibits. -/
def fnLawSortedOf (c : Semantics) (N : Names) (a : Kore.Axiom) : Rd LawEq := do
  let l ← fnLawOf N a
  if fnLawSorted c l then pure l
  else Rd.within (.sentence (.axiom a)) (fail .lawAxiom
    s!"{(lawHead? a).getD ""}: {", ".intercalate (lawKeys a)}: its sides are of no one sort")

/-- The presentation's per-sort and per-cell parts: the sorts' unique ids, the cell sorts' unique
ids, the cells' initializers' ids, and the leaf cells' initial values. -/
structure CellParts where
  sortUids : List SortUids
  cellUids : List (Srt × SortUids)
  cellInits : List (String × String)
  cellValues : List (String × Term)
  pgmCell : Option String
  deriving Repr

/-- The presentation's per-sort and per-cell parts. -/
def cellPartsOf (S : Scan) (E : Env) (core : Semantics) : Rd CellParts := do
  let eqs := S.eqs
  let cells := Cell.all (Cell.top E.config)
  -- the leaf whose initializer's right-hand side holds `$PGM` (`pgmSortOf` reads its sort there)
  let pgmCell := (cells.findSome? fun x => match x with
    | .leaf n _ _ => if (eqs.find? (·.fn == x.initLabel core)).any (holdsPgm 16 ·.rhs) then some n else none
    | _ => none)
  pure { sortUids := ← E.userSortNames.mapM (sortUidOf S.syms eqs)
         cellUids := ← (Cell.topSorts E.config).mapM fun X => do pure (X, ← sortUidOf S.syms eqs (core.sortName X))
         cellInits := ← cells.mapM fun x => do pure (x.name, ← initUidOf eqs (x.initLabel core))
         cellValues := cells.filterMap fun x => match x with
           | .leaf n _ _ => if pgmCell == some n || n == "generatedCounter" then none
                            else (valueOf E.N eqs (x.initLabel core)).map (n, ·)
           | _ => none
         pgmCell }

/-- The presentation from the productions, the rules, the core and its cell parts. -/
def presOf (m : Kore.Module) (S : Scan) (E : Env) (prods : List Prod) (rules : List (Rule × RulePres))
    (core : Semantics) (cp : CellParts) : Rd Presentation := do
  let eqs := S.eqs
  -- the configuration's place: its `<k>` cell's, or, without one, the first cell's of the configuration
  -- whose declaration has a place
  let kSym ← need ((cellSym? S.syms "KCell").orElse fun _ => (Cell.all (Cell.top E.config)).findSome? fun x =>
    (cellSym? S.syms (core.sortName x.sort)).filter fun s => (loc? s.attributes).isSome) .configuration "KCell"
  -- the getter's and the tree's initializers' sentences are those the account takes
  match initFaults E.N E.src m.sentences eqs (functionalSyms S.events) core (Cell.top E.config) with
  | f :: _ => .error f
  | [] => pure ()
  pure { source := E.src, moduleName := m.name.ident.name, moduleLoc := ← need (loc? m.attributes) .moduleLocation
         imports := E.imports, simpArg := E.simpArg
         sortUids := cp.sortUids
         order := prods.map prodKind
         ctors := prods.filterMap (fun | .ctor _ kp => some kp | _ => none)
         fns := prods.filterMap (fun | .fn _ fp => some fp | _ => none) ++ E.genFns.map (·.2)
         rules := rules.map (·.2)
         configLoc := ← Rd.within (.sentence (.symbol kSym)) (need (loc? kSym.attributes) .location)
         configSource := ← Rd.within (.sentence (.symbol kSym)) (need (source? kSym.attributes) .location)
         cellUids := cp.cellUids, cellInits := cp.cellInits, cellValues := cp.cellValues, pgmCell := cp.pgmCell
         counterUid := ← uidOf eqs "LblgetGeneratedCounterCell" false
         counterVars := ← counterVarsOf eqs
         kconfigPos := kconfigPosOf (fixedKNames core.lib) S.ors
         params := E.params.map (·.2)
         config := E.config
         sortLocs := ← S.locSorts.mapM fun (X, l, src) => do pure (← E.N.srtE X, l, src)
         libProjs := E.libProjs
         generatedFns := E.genFns.map (·.1.label)
         laws := ← (fnLawAxioms core m.sentences).mapM fun (_, a) => fnLawSortedOf core E.N a }

/-- The certificates: for each function, its first decreasing argument. -/
def certOf (core : Semantics) : Certificates :=
  ⟨core.fns.map core.decArg⟩

/-- The definition from the scan, the names, the productions and the rules, in four parts that the
tie checks one at a time (`assemble_of_parts`). -/
def assemble (m : Kore.Module) (S : Scan) (E : Env) (symProds : List Prod) (rules : List (Rule × RulePres)) :
    Rd Definition := do
  let prods := prodsOf S E symProds
  let core ← coreOf S E prods rules
  let cp ← cellPartsOf S E core
  let pres ← presOf m S E prods rules core cp
  pure ⟨core, pres, certOf core⟩

theorem assemble_of_parts {m : Kore.Module} {S : Scan} {E : Env} {sp ps : List Prod}
    {rs : List (Rule × RulePres)} {d : Definition} {cp : CellParts}
    (h₁ : prodsOf S E sp = ps) (h₂ : coreOf S E ps rs = .ok d.sem) (h₃ : cellPartsOf S E d.sem = .ok cp)
    (h₄ : presOf m S E ps rs d.sem cp = .ok d.pres) (h₅ : certOf d.sem = d.cert) :
    assemble m S E sp rs = .ok d := by
  simp only [assemble, h₁, h₂, bind, Except.bind, h₃, h₄, h₅]
  rfl

/-- `parse` after the scan: the names, the productions and the rules (each a `mapM`, which the
tie checks a slice at a time), then the definition. -/
def finish (m : Kore.Module) (S : Scan) : Rd Definition := do
  let E ← envOf m S
  let symProds ← (prodSyms S E).mapM (symProd E S.eqs)
  let rules ← S.rewrites.mapM (ruleOf E.N E.src)
  assemble m S E symProds rules

theorem finish_of_stages {m : Kore.Module} {S : Scan} {E : Env} {sp : List Prod}
    {rs : List (Rule × RulePres)} {d : Definition}
    (h₁ : envOf m S = .ok E) (h₂ : (prodSyms S E).mapM (symProd E S.eqs) = .ok sp)
    (h₃ : S.rewrites.mapM (ruleOf E.N E.src) = .ok rs) (h₄ : assemble m S E sp rs = .ok d) :
    finish m S = .ok d := by
  simp only [finish, h₁, bind, Except.bind, h₂, h₃, h₄]

/-- `l.mapM f`, a slice at a time: the `n` elements of `l` from `a` map to `r`. -/
def MapIs {α β : Type} (f : α → Rd β) (l : List α) (a n : Nat) (r : List β) : Prop :=
  ((l.drop a).take n).mapM f = .ok r

theorem MapIs.join {α β : Type} {f : α → Rd β} {l : List α} {a n m k : Nat} {r₁ r₂ : List β}
    (h₁ : MapIs f l a n r₁) (h₂ : MapIs f l (a + n) m r₂) (hk : n + m = k) : MapIs f l a k (r₁ ++ r₂) := by
  subst hk
  unfold MapIs at *
  rw [List.take_add, List.mapM_append, h₁, List.drop_drop, h₂]
  rfl

theorem MapIs.all {α β : Type} {f : α → Rd β} {l : List α} {n : Nat} {r : List β}
    (hn : l.length = n) (h : MapIs f l 0 n r) : l.mapM f = .ok r := by
  subst hn
  unfold MapIs at h
  rwa [List.drop_zero, List.take_length] at h

/-! ## Refusals placed in the file -/

/-- The position of the first sentence of `l` satisfying `p`. -/
def firstIdx (l : List Kore.Sentence) (p : Kore.Sentence → Bool) : Option Nat := l.findIdx? p

/-- The refusal a stage's failure gives, its sentence found in the user module `m`, whose first
sentence is at position `off` of the file. -/
def Fault.toRefusal (off : Nat) (m : Kore.Module) (f : Fault) : Refusal :=
  let locate := fun (p : Kore.Sentence → Bool) =>
    match firstIdx m.sentences p with
    | some i => (some (off + i), headOf (m.sentences.getD i default))
    | none => (none, m.name.ident.name)
  let (i, h) := match f.site with
    | .unset => (none, m.name.ident.name)
    -- a disjunct's axiom (`splitRule`) is no sentence of the module: the axiom with its attributes
    | .sentence s => match firstIdx m.sentences (fun s' => decide (s' = s)), s with
      | none, .axiom a => locate fun
        | .axiom a' => decide (a'.attributes = a.attributes)
        | _ => false
      | _, _ => locate fun s' => decide (s' = s)
    | .attrs as => locate fun
      | .axiom a => decide (a.attributes = as)
      | _ => false
    | .builtin src line => locate fun s => scanBuiltin s == some (src, line)
  ⟨i, h, f.reason, f.detail⟩

/-- The detail of a refusal `classify` gives the sentence `s` of the user module `m`: for an open
generator (`openGenerator`, `isOpenGenerator`), the law axioms `m` states of the symbol (kompile
writes none for `comm`);
for a set variable on an equation's left side (`setVariable`, `lhsSetVar?`), the variable, the
function and why; for an attribute of a declaration (`symAttrFault?`, also an `openGenerator`
refusal of a symbol that is no open generator) or of a claim (`attrFault?`), the attribute and
why; "" for the other reasons. -/
def classDetail (m : Kore.Module) (s : Kore.Sentence) (r : RefusalReason) : String :=
  match r, s with
  | .openGenerator, .symbol x =>
    let n := x.symbol.ident.ident.name
    if !isOpenGenerator x then ((symAttrFault? x.attributes).map fun (_, d) => s!"{n}: {d}").getD "" else
    let laws := (m.sentences.filterMap fun t => match t with
      | .axiom a => if isCollectionLaw a && lawHead? a == some n then some (lawKeys a) else none
      | _ => none).flatten.eraseDups
    s!"{n}: neither function nor constructor; law axioms: {if laws.isEmpty then "none" else ", ".intercalate laws}"
  | .sortAttribute, .sort x =>
    s!"{x.sort.ident.name}: {", ".intercalate ((x.attributes.filter (!sortAttrOK ·)).map (·.head.ident.name))}"
  | _, .symbol x => ((symAttrFault? x.attributes).map fun (_, d) =>
      s!"{x.symbol.ident.ident.name}: {d}").getD ""
  | _, .hookedSymbol x => ((symAttrFault? x.attributes).map fun (_, d) =>
      s!"{x.symbol.ident.ident.name}: {d}").getD ""
  | _, .claim c => ((attrFault? .claim .outsideE2 c.attributes).map (·.2)).getD ""
  | .userHookedSort, .hookedSort x => s!"{x.sort.ident.name}: hook {(attrStr? x.attributes "hook").getD "(none)"}"
  | .existentialAxiom, .axiom a => match existentialAxiom? a with
    | some (f, b) => s!"{f}: {f}(…) = {b}, {b} bound by \\exists at the top of the axiom"
    | none => ""
  | .setVariable, .axiom a => match lhsSetVar? a with
    | some (f, X) => s!"{X}: an argument of {f} on the equation's left side: the sentence states \
        {f} at every set's elements, at a set of two elements a, b only that {f}(a, b) is the right \
        side or undefined; no clause states that"
    | none => ""
  | _, _ => ""

/-- The first sentence of the user module that `classify` refuses, as a refusal. -/
def classRefusal (off : Nat) (m : Kore.Module) : Refusal :=
  let refusedAt := fun (si : Kore.Sentence × Nat) => match classify si.1 with
    | .refused r => some (⟨some (off + si.2), headOf si.1, r, classDetail m si.1 r⟩ : Refusal)
    | _ => none
  ((m.sentences.zipIdx).findSome? refusedAt).getD ⟨none, m.name.ident.name, .axiomShape, ""⟩

/-- Where the modules before the last differ from K's prelude: the first sentence that differs. -/
def preludeRefusal (k : Kore.Definition) : Refusal :=
  let ss := (k.modules.dropLast.map (·.sentences)).flatten
  let ps := (preludeModules.map (·.sentences)).flatten
  let i := ((ss.zip ps).findIdx? fun (a, b) => !decide (a = b)).getD (min ss.length ps.length)
  ⟨some i, (ss[i]?.map headOf).getD "", .preludeDiffers, ""⟩

/-- The number of sentences in the modules before the user module. -/
def preludeLength (k : Kore.Definition) : Nat := (k.modules.dropLast.map (·.sentences.length)).sum

/-- KCore's reading of a KORE text: its last module is the user module, the modules before it K's
prelude; the user module's sentences classified read are scanned, and the definition is built from
the scan (`finish`). -/
def parse (k : Kore.Definition) : Except Refusal Definition :=
  match k.modules.getLast? with
  | none => .error ⟨none, "", .noModule, ""⟩
  | some m =>
    if k.modules.dropLast = preludeModules then
      let S := scan m.sentences
      match S.refused with
      | [] => (finish m S).mapError (Fault.toRefusal (preludeLength k) m)
      | _ :: _ => .error (classRefusal (preludeLength k) m)
    else .error (preludeRefusal k)

/-- `parse` from its stages: the prelude, the scan of the user module's sentences (none refused),
and `finish`. -/
theorem parse_of_scan {k : Kore.Definition} {m : Kore.Module} {S : Scan} {d : Definition}
    (h₁ : k.modules.getLast? = some m) (h₀ : k.modules.dropLast = preludeModules)
    (h₂ : scan m.sentences = S) (hr : S.refused = []) (h₃ : finish m S = .ok d) :
    parse k = .ok d := by
  simp only [parse, h₁, h₀, ite_true, h₂, hr, h₃]
  rfl

end KCore.Parse
