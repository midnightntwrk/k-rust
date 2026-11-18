/-
  KCore. The attribute keys of the construct table's list E2 that reach a KORE text, and the
  reader's verdict on each at each class of sentence. NOT part of the reviewed layer.

  E2 (test/constructs/rows.toml) has one row per attribute key of K 7.1.337 and class of sentence
  the key is admitted at: `NAME(name)@class`. A row of class `frontend` is a key no KORE sentence
  carries. `AttrKeyE2` has one constructor for each name of the other rows, `AttrClassE2` their
  classes, and `attrVerdict` what the row decides, for every class and key, with no default: the
  row of the key at the class, else the key's row at class `any` (a key admitted at every
  sentence), else refused, K admitting the key at no sentence of the class. A row decides
  supported (`read`), inert (`inert`), or refused or erased (`refused`): the frontend erases the
  key of an erased row, so only a KORE text written by hand carries it.
-/

set_option autoImplicit false

namespace KCore.Parse

/-- The attribute names of the E2 rows whose class is not `frontend`: the keys a KORE sentence
may carry. -/
inductive AttrKeyE2 where
  /-- `alias` -/
  | alias
  /-- `alias-rec` -/
  | aliasRec
  /-- `anywhere` -/
  | anywhere
  /-- `assoc` -/
  | assoc
  /-- `binder` -/
  | binder
  /-- `bracket` -/
  | bracket
  /-- `cell` -/
  | cell
  /-- `circularity` -/
  | circularity
  /-- `colors` -/
  | colors
  /-- `comm` -/
  | comm
  /-- `concat` -/
  | concat
  /-- `concrete` -/
  | concrete
  /-- `constructor` -/
  | constructor
  /-- `cool` -/
  | cool
  /-- `cool-like` -/
  | coolLike
  /-- `depends` -/
  | depends
  /-- `deprecated` -/
  | deprecated
  /-- `element` -/
  | element
  /-- `format` -/
  | format
  /-- `freshGenerator` -/
  | freshGenerator
  /-- `function` -/
  | function
  /-- `functional` -/
  | functional
  /-- `hasDomainValues` -/
  | hasDomainValues
  /-- `hook` -/
  | hook
  /-- `idem` -/
  | idem
  /-- `impure` -/
  | impure
  /-- `injective` -/
  | injective
  /-- `klabel` -/
  | klabel
  /-- `label` -/
  | label
  /-- `left` -/
  | left
  /-- `macro` -/
  | macroKey
  /-- `macro-rec` -/
  | macroRec
  /-- `memo` -/
  | memo
  /-- `nat` -/
  | nat
  /-- `no-evaluators` -/
  | noEvaluators
  /-- `non-executable` -/
  | nonExecutable
  /-- `org.kframework.attributes.Location` -/
  | location
  /-- `org.kframework.attributes.Source` -/
  | source
  /-- `owise` -/
  | owise
  /-- `preserves-definedness` -/
  | preservesDefinedness
  /-- `priorities` -/
  | priorities
  /-- `priority` -/
  | priority
  /-- `right` -/
  | right
  /-- `simplification` -/
  | simplification
  /-- `smt-hook` -/
  | smtHook
  /-- `smt-lemma` -/
  | smtLemma
  /-- `smtlib` -/
  | smtlib
  /-- `symbol` -/
  | symbol
  /-- `symbol-overload` -/
  | symbolOverload
  /-- `symbolic` -/
  | symbolic
  /-- `syntactic` -/
  | syntactic
  /-- `terminals` -/
  | terminals
  /-- `token` -/
  | token
  /-- `total` -/
  | total
  /-- `trusted` -/
  | trusted
  /-- `UNIQUE_ID` -/
  | uniqueId
  /-- `unit` -/
  | unit
  /-- `update` -/
  | update
  deriving Repr, DecidableEq, Inhabited

/-- Every key, in the order of the declaration. -/
def AttrKeyE2.all : List AttrKeyE2 :=
  [.alias, .aliasRec, .anywhere, .assoc, .binder, .bracket, .cell, .circularity,
   .colors, .comm, .concat, .concrete, .constructor, .cool, .coolLike, .depends,
   .deprecated, .element, .format, .freshGenerator, .function, .functional, .hasDomainValues, .hook,
   .idem, .impure, .injective, .klabel, .label, .left, .macroKey, .macroRec,
   .memo, .nat, .noEvaluators, .nonExecutable, .location, .source, .owise, .preservesDefinedness,
   .priorities, .priority, .right, .simplification, .smtHook, .smtLemma, .smtlib, .symbol,
   .symbolOverload, .symbolic, .syntactic, .terminals, .token, .total, .trusted, .uniqueId,
   .unit, .update]

/-- The key's name in K. -/
def AttrKeyE2.name : AttrKeyE2 → String
  | .alias => "alias"
  | .aliasRec => "alias-rec"
  | .anywhere => "anywhere"
  | .assoc => "assoc"
  | .binder => "binder"
  | .bracket => "bracket"
  | .cell => "cell"
  | .circularity => "circularity"
  | .colors => "colors"
  | .comm => "comm"
  | .concat => "concat"
  | .concrete => "concrete"
  | .constructor => "constructor"
  | .cool => "cool"
  | .coolLike => "cool-like"
  | .depends => "depends"
  | .deprecated => "deprecated"
  | .element => "element"
  | .format => "format"
  | .freshGenerator => "freshGenerator"
  | .function => "function"
  | .functional => "functional"
  | .hasDomainValues => "hasDomainValues"
  | .hook => "hook"
  | .idem => "idem"
  | .impure => "impure"
  | .injective => "injective"
  | .klabel => "klabel"
  | .label => "label"
  | .left => "left"
  | .macroKey => "macro"
  | .macroRec => "macro-rec"
  | .memo => "memo"
  | .nat => "nat"
  | .noEvaluators => "no-evaluators"
  | .nonExecutable => "non-executable"
  | .location => "org.kframework.attributes.Location"
  | .source => "org.kframework.attributes.Source"
  | .owise => "owise"
  | .preservesDefinedness => "preserves-definedness"
  | .priorities => "priorities"
  | .priority => "priority"
  | .right => "right"
  | .simplification => "simplification"
  | .smtHook => "smt-hook"
  | .smtLemma => "smt-lemma"
  | .smtlib => "smtlib"
  | .symbol => "symbol"
  | .symbolOverload => "symbol-overload"
  | .symbolic => "symbolic"
  | .syntactic => "syntactic"
  | .terminals => "terminals"
  | .token => "token"
  | .total => "total"
  | .trusted => "trusted"
  | .uniqueId => "UNIQUE_ID"
  | .unit => "unit"
  | .update => "update"

/-- The key as kompile spells it at the head of a KORE attribute: K's name with `.` written
`'Stop'` and `_` written `'Unds'`, and `'Kywd'` after a name that is a keyword of KORE (`symbol`,
`alias`). -/
def AttrKeyE2.kore : AttrKeyE2 → String
  | .alias => "alias'Kywd'"
  | .aliasRec => "alias-rec"
  | .anywhere => "anywhere"
  | .assoc => "assoc"
  | .binder => "binder"
  | .bracket => "bracket"
  | .cell => "cell"
  | .circularity => "circularity"
  | .colors => "colors"
  | .comm => "comm"
  | .concat => "concat"
  | .concrete => "concrete"
  | .constructor => "constructor"
  | .cool => "cool"
  | .coolLike => "cool-like"
  | .depends => "depends"
  | .deprecated => "deprecated"
  | .element => "element"
  | .format => "format"
  | .freshGenerator => "freshGenerator"
  | .function => "function"
  | .functional => "functional"
  | .hasDomainValues => "hasDomainValues"
  | .hook => "hook"
  | .idem => "idem"
  | .impure => "impure"
  | .injective => "injective"
  | .klabel => "klabel"
  | .label => "label"
  | .left => "left"
  | .macroKey => "macro"
  | .macroRec => "macro-rec"
  | .memo => "memo"
  | .nat => "nat"
  | .noEvaluators => "no-evaluators"
  | .nonExecutable => "non-executable"
  | .location => "org'Stop'kframework'Stop'attributes'Stop'Location"
  | .source => "org'Stop'kframework'Stop'attributes'Stop'Source"
  | .owise => "owise"
  | .preservesDefinedness => "preserves-definedness"
  | .priorities => "priorities"
  | .priority => "priority"
  | .right => "right"
  | .simplification => "simplification"
  | .smtHook => "smt-hook"
  | .smtLemma => "smt-lemma"
  | .smtlib => "smtlib"
  | .symbol => "symbol'Kywd'"
  | .symbolOverload => "symbol-overload"
  | .symbolic => "symbolic"
  | .syntactic => "syntactic"
  | .terminals => "terminals"
  | .token => "token"
  | .total => "total"
  | .trusted => "trusted"
  | .uniqueId => "UNIQUE'Unds'ID"
  | .unit => "unit"
  | .update => "update"

/-- The key a KORE attribute's head spells, if any. -/
def AttrKeyE2.ofName? (s : String) : Option AttrKeyE2 := AttrKeyE2.all.find? (·.kore == s)

/-- The classes of sentence of the E2 rows: a symbol declaration (hooked or not), a sort
declaration (hooked or not), a rewrite axiom, a function equation, an axiom carrying
`simplification`, a claim, the module, and `any`, the class of a key admitted at every sentence. -/
inductive AttrClassE2 where
  | symbol | sort | rule | equation | simplification | claim | module | any
  deriving Repr, DecidableEq, Inhabited

/-- Every class, in the order of the declaration. -/
def AttrClassE2.all : List AttrClassE2 :=
  [.symbol, .sort, .rule, .equation, .simplification, .claim, .module, .any]

/-- The class's name in an E2 row's key. -/
def AttrClassE2.name : AttrClassE2 → String
  | .symbol => "symbol" | .sort => "sort" | .rule => "rule" | .equation => "equation"
  | .simplification => "simplification" | .claim => "claim" | .module => "module" | .any => "any"

/-- The reason a key is refused with: a rewrite axiom's (`RefusalReason.ruleAttribute`), a function
equation's (`equationAttribute`), a sort declaration's (`sortAttribute`), `assoc` or `comm` on a
symbol that is no function (`openGenerator`: a generator under a law), and, at a symbol
declaration, a simplification axiom, a claim or the module, a key that no kompiled text carries
there (`attrOutsideE2`), and a name that is no key on a symbol declaration (`symbolAttrUnkeyed`; no
verdict gives it). `AttrRefusalE2.reason` (Parse.lean) is the map. -/
inductive AttrRefusalE2 where
  | ruleAttribute | equationAttribute | sortAttribute | openGenerator | outsideE2 | symbolAttribute
  deriving Repr, DecidableEq, Inhabited

/-- What the reader does with an attribute: reads it; reads the sentence with the key saying
nothing the semantics reads, with why; or refuses the sentence, with the reason and why. -/
inductive AttrVerdict where
  | read
  | inert (why : String)
  | refused (r : AttrRefusalE2) (why : String)
  deriving Repr, DecidableEq, Inhabited

/-- Why, for a verdict the row gives no shorter sentence for: the row decides it. -/
def ruled (row : String) : String := s!"as the construct table's row E2 {row} decides, with its reason"

/-- Why a key of an erased row is refused. -/
def erased (row : String) : String :=
  s!"no kompiled text carries the key (the frontend erases it, row E2 {row}): only a KORE text written by hand does"

/-- Why a key is refused whose K text the frontend refuses. -/
def unkompiled (row : String) : String :=
  s!"no K text is written to a sentence carrying the key here (the frontend refuses the text, row E2 {row}): only a KORE text written by hand carries it"

/-- Why a key is refused at a class K does not admit it at. -/
def unwritten : String :=
  "K admits the key at no sentence of this class (no row of E2): only a KORE text written by hand carries it"

/-- Why a printing attribute of a production is inert on a rewrite axiom. -/
def printedForm : String :=
  "a printing form of the production the rule is generated from (how its terms are printed): kompile copies the production's attributes onto the heating and cooling rules of a strict production (c3-strict-result/kore.txt:283 carries format); it says nothing of where or how the rule applies; the axiom states the rule"

/-- Why the KORE name of a production is inert on a rewrite axiom. -/
def productionName : String :=
  "the name of the production the rule is generated from: kompile copies the production's attributes onto the heating and cooling rules of a strict production (c3-strict-result/kore.txt:283); a name says nothing of where or how the rule applies; the axiom states the rule"

/-- Why a key of a declaration is refused on a rewrite axiom or an equation. -/
def declarationKey : String :=
  "the key states a property of a symbol or sort declaration (a collection's concatenation, a sort's domain values, a symbol's overload), where the reader reads it; no text gives it a meaning on this sentence, so that reading the sentence with the key dropped states no more than the text cannot be shown"

/-- The verdict on key `k` at a sentence of class `c`: what the E2 row of `k` at `c` decides, else
the row of `k` at class `any`, else refused. Every class and key is an arm. Four exceptions, where
a row's verdict would not be the reader's:
- at a rewrite axiom, `format`, `colors` and `symbol` are inert, which no row admits there: the
  production's attributes that kompile copies onto the heating and cooling rules it generates;
- at a rewrite axiom, `concat`, `hasDomainValues` and `symbol-overload`, and at an equation `concat`
  and `hasDomainValues`, are refused, where the rows at class `any` read them: the reader reads them
  at a declaration (and `symbol-overload` at an equation), and no text gives them a meaning at the
  sentence;
- at a symbol declaration, `anywhere` is read, which no row admits there: kompile writes it on the
  declaration of an overloaded production's symbol (86 declarations of the corpus and the fixtures'
  texts), and the reader reads it (an overloading symbol, `Parse.isOpenGenerator`);
- at an equation, `anywhere` is refused as its row decides, with a why of its own: the row's is the
  frontend's refusal under the haskell backend, while kompile writes the key on an equation under
  another backend. -/
def attrVerdict : AttrClassE2 → AttrKeyE2 → AttrVerdict
  -- symbol
  -- a macro key: the reader reads it (`Parse.isMacroDecl`: the declaration is not read, and an
  -- application of the symbol is refused)
  | .symbol, .alias => .read
  | .symbol, .aliasRec => .read
  | .symbol, .circularity | .symbol, .cool | .symbol, .depends
  | .symbol, .nonExecutable | .symbol, .owise | .symbol, .preservesDefinedness
  | .symbol, .simplification | .symbol, .smtLemma | .symbol, .syntactic | .symbol, .trusted =>
    .refused .outsideE2 unwritten
  | .symbol, .anywhere => .read
  | .symbol, .assoc => .refused .openGenerator (ruled "ASSOC(assoc)@symbol")
  | .symbol, .binder => .inert (ruled "BINDER(binder)@symbol")
  | .symbol, .bracket => .refused .outsideE2 (erased "BRACKET(bracket)@symbol")
  | .symbol, .cell | .symbol, .concat | .symbol, .constructor | .symbol, .element
  | .symbol, .function | .symbol, .functional | .symbol, .hasDomainValues | .symbol, .hook
  | .symbol, .idem | .symbol, .location | .symbol, .source | .symbol, .symbolOverload
  | .symbol, .token | .symbol, .total | .symbol, .uniqueId | .symbol, .unit =>
    .read
  | .symbol, .colors => .refused .outsideE2 (erased "COLORS(colors)@symbol")
  | .symbol, .comm => .refused .openGenerator (ruled "COMM(comm)@symbol")
  | .symbol, .concrete => .inert (ruled "CONCRETE(concrete)@symbol")
  | .symbol, .coolLike => .inert (ruled "COOL_LIKE(cool-like)@any")
  | .symbol, .deprecated => .inert (ruled "DEPRECATED(deprecated)@symbol")
  | .symbol, .format => .refused .outsideE2 (erased "FORMAT(format)@symbol")
  | .symbol, .freshGenerator => .inert (ruled "FRESH_GENERATOR(freshGenerator)@symbol")
  | .symbol, .impure => .inert (ruled "IMPURE(impure)@symbol")
  | .symbol, .injective => .inert (ruled "INJECTIVE(injective)@symbol")
  | .symbol, .klabel => .inert (ruled "KLABEL(klabel)@symbol")
  | .symbol, .label => .inert (ruled "LABEL(label)@symbol")
  | .symbol, .left => .refused .outsideE2 (erased "LEFT_INTERNAL(left)@any")
  | .symbol, .macroKey => .read
  | .symbol, .macroRec => .read
  | .symbol, .memo => .inert (ruled "MEMO(memo)@symbol")
  | .symbol, .nat => .refused .outsideE2 (ruled "NAT(nat)@any")
  | .symbol, .noEvaluators => .inert (ruled "NO_EVALUATORS(no-evaluators)@symbol")
  | .symbol, .priorities => .refused .outsideE2 (erased "PRIORITIES(priorities)@any")
  | .symbol, .priority => .inert (ruled "PRIORITY(priority)@symbol")
  | .symbol, .right => .refused .outsideE2 (erased "RIGHT_INTERNAL(right)@any")
  | .symbol, .smtHook => .inert (ruled "SMT_HOOK(smt-hook)@symbol")
  | .symbol, .smtlib => .inert (ruled "SMTLIB(smtlib)@symbol")
  | .symbol, .symbol => .inert (ruled "SYMBOL(symbol)@symbol")
  | .symbol, .symbolic => .inert (ruled "SYMBOLIC(symbolic)@symbol")
  | .symbol, .terminals => .refused .outsideE2 (erased "TERMINALS(terminals)@any")
  | .symbol, .update => .inert (ruled "UPDATE(update)@symbol")
  -- sort
  | .sort, .alias | .sort, .aliasRec | .sort, .anywhere | .sort, .assoc | .sort, .binder
  | .sort, .bracket | .sort, .cell | .sort, .circularity | .sort, .colors | .sort, .comm
  | .sort, .concrete | .sort, .constructor | .sort, .cool | .sort, .depends | .sort, .deprecated
  | .sort, .element | .sort, .format | .sort, .freshGenerator | .sort, .function
  | .sort, .functional | .sort, .idem | .sort, .impure | .sort, .injective | .sort, .klabel
  | .sort, .macroKey | .sort, .macroRec | .sort, .memo | .sort, .noEvaluators
  | .sort, .nonExecutable | .sort, .owise | .sort, .preservesDefinedness | .sort, .priority
  | .sort, .simplification | .sort, .smtHook | .sort, .smtLemma | .sort, .smtlib | .sort, .symbol
  | .sort, .symbolic | .sort, .syntactic | .sort, .total | .sort, .trusted | .sort, .unit
  | .sort, .update =>
    .refused .sortAttribute unwritten
  | .sort, .concat | .sort, .hasDomainValues | .sort, .hook | .sort, .location | .sort, .source
  | .sort, .symbolOverload | .sort, .token | .sort, .uniqueId =>
    .read
  | .sort, .coolLike => .inert (ruled "COOL_LIKE(cool-like)@any")
  | .sort, .label => .inert (ruled "LABEL(label)@sort")
  | .sort, .left => .refused .sortAttribute (erased "LEFT_INTERNAL(left)@any")
  | .sort, .nat => .refused .sortAttribute (ruled "NAT(nat)@any")
  | .sort, .priorities => .refused .sortAttribute (erased "PRIORITIES(priorities)@any")
  | .sort, .right => .refused .sortAttribute (erased "RIGHT_INTERNAL(right)@any")
  | .sort, .terminals => .refused .sortAttribute (erased "TERMINALS(terminals)@any")
  -- rule
  | .rule, .alias | .rule, .aliasRec | .rule, .assoc | .rule, .binder | .rule, .bracket
  | .rule, .cell | .rule, .circularity | .rule, .constructor | .rule, .depends
  | .rule, .deprecated | .rule, .element | .rule, .freshGenerator
  | .rule, .function | .rule, .functional | .rule, .hook | .rule, .idem | .rule, .impure
  | .rule, .injective | .rule, .klabel | .rule, .macroKey | .rule, .macroRec | .rule, .memo
  | .rule, .noEvaluators | .rule, .smtHook | .rule, .smtlib | .rule, .token
  | .rule, .total | .rule, .trusted | .rule, .unit | .rule, .update =>
    .refused .ruleAttribute unwritten
  | .rule, .colors | .rule, .format => .inert printedForm
  | .rule, .symbol => .inert productionName
  | .rule, .concat | .rule, .hasDomainValues | .rule, .symbolOverload => .refused .ruleAttribute declarationKey
  | .rule, .anywhere => .refused .ruleAttribute "the key's meaning is the rule applied in every context of the configuration, an equation's closure under contexts, which the axiom, one rewrite at the top cell, does not state; reading the axiom with the key dropped would assert its step without that meaning"
  | .rule, .comm => .inert "K gives comm on a rule no meaning (it is a production's attribute); the axiom states the rule"
  | .rule, .label | .rule, .location | .rule, .source | .rule, .owise | .rule, .priority
  | .rule, .uniqueId =>
    .read
  | .rule, .concrete => .inert "which terms a prover applies the rule to (concrete values of the named variables): no statement of the theory; the axiom states the rule"
  | .rule, .cool => .inert "marks a cooling rule of a strictness declaration; the axiom states the rule"
  | .rule, .coolLike => .inert "marks a rule as cooling-like for strictness; the axiom states the rule"
  | .rule, .left => .refused .ruleAttribute (erased "LEFT_INTERNAL(left)@any")
  | .rule, .nat => .refused .ruleAttribute (ruled "NAT(nat)@any")
  | .rule, .nonExecutable => .refused .ruleAttribute "the key may leave the axiom a rule like any other, or leave it out of what a rule of a larger priority number excludes (as it does for an equation, Clause.aside); the two give different steps where the rule overlaps such a rule, and no sentence of the text chooses between them (a priority is an attribute)"
  | .rule, .preservesDefinedness => .inert "no K text gives it a meaning (kore-syntax.md:223-229; the user manual has no occurrence); kompile writes it on the axiom and no sentence beside it (e2-rule/kore.txt:193-199); the axiom states the rule"
  | .rule, .priorities => .refused .ruleAttribute (erased "PRIORITIES(priorities)@any")
  | .rule, .right => .refused .ruleAttribute (erased "RIGHT_INTERNAL(right)@any")
  | .rule, .simplification => .refused .ruleAttribute "the axiom states a step, which classing it a lemma (inert) would drop, while the key says the axiom is a lemma and no rule of the definition, which reading it as a rule would drop"
  | .rule, .smtLemma => .refused .ruleAttribute "kompile writes no definition for an smt-lemma rule"
  | .rule, .symbolic => .inert "which terms a prover applies the rule to (symbolic values of the named variables): no statement of the theory; the axiom states the rule"
  | .rule, .syntactic => .refused .ruleAttribute "no text gives the key a meaning, so that reading the axiom with the key dropped states no more than the text cannot be shown"
  | .rule, .terminals => .refused .ruleAttribute (erased "TERMINALS(terminals)@any")
  -- equation
  | .equation, .alias | .equation, .aliasRec | .equation, .assoc | .equation, .binder
  | .equation, .bracket | .equation, .cell | .equation, .circularity | .equation, .colors
  | .equation, .constructor | .equation, .depends | .equation, .deprecated | .equation, .element
  | .equation, .format | .equation, .freshGenerator | .equation, .function | .equation, .functional
  | .equation, .hook | .equation, .idem | .equation, .impure | .equation, .injective
  | .equation, .klabel | .equation, .macroKey | .equation, .macroRec | .equation, .memo
  | .equation, .noEvaluators | .equation, .smtHook | .equation, .smtlib | .equation, .symbol
  | .equation, .token | .equation, .total | .equation, .trusted | .equation, .unit
  | .equation, .update =>
    .refused .equationAttribute unwritten
  | .equation, .anywhere => .refused .equationAttribute "K gives anywhere its meaning on a rule, the rewrite applied in every context (the frontend refuses the key on a function's rule under the haskell backend, row E2 ANYWHERE(anywhere)@equation); on a function equation no text gives the key a meaning, so that reading the equation with the key dropped states no more than the text cannot be shown"
  | .equation, .comm => .inert (ruled "COMM(comm)@equation")
  | .equation, .cool | .equation, .label | .equation, .nonExecutable | .equation, .location
  | .equation, .source | .equation, .owise | .equation, .priority | .equation, .symbolOverload
  | .equation, .uniqueId =>
    .read
  | .equation, .concat | .equation, .hasDomainValues => .refused .equationAttribute declarationKey
  | .equation, .concrete => .inert (ruled "CONCRETE(concrete)@equation")
  | .equation, .coolLike => .inert (ruled "COOL_LIKE(cool-like)@any")
  | .equation, .left => .refused .equationAttribute (erased "LEFT_INTERNAL(left)@any")
  | .equation, .nat => .refused .equationAttribute (ruled "NAT(nat)@any")
  | .equation, .preservesDefinedness => .inert (ruled "PRESERVES_DEFINEDNESS(preserves-definedness)@equation")
  | .equation, .priorities => .refused .equationAttribute (erased "PRIORITIES(priorities)@any")
  | .equation, .right => .refused .equationAttribute (erased "RIGHT_INTERNAL(right)@any")
  | .equation, .simplification => .inert (ruled "SIMPLIFICATION(simplification)@equation")
  | .equation, .smtLemma => .inert (ruled "SMT_LEMMA(smt-lemma)@equation")
  | .equation, .symbolic => .inert (ruled "SYMBOLIC(symbolic)@equation")
  | .equation, .syntactic => .refused .equationAttribute "no text gives the key a meaning, so that reading the equation with the key dropped states no more than the text cannot be shown"
  | .equation, .terminals => .refused .equationAttribute (erased "TERMINALS(terminals)@any")
  -- simplification
  | .simplification, .alias | .simplification, .aliasRec | .simplification, .assoc
  | .simplification, .binder | .simplification, .bracket | .simplification, .cell
  | .simplification, .circularity | .simplification, .colors | .simplification, .constructor
  | .simplification, .depends | .simplification, .deprecated | .simplification, .element
  | .simplification, .format | .simplification, .freshGenerator | .simplification, .function
  | .simplification, .functional | .simplification, .hook | .simplification, .idem
  | .simplification, .impure | .simplification, .injective | .simplification, .klabel
  | .simplification, .macroKey | .simplification, .macroRec | .simplification, .memo
  | .simplification, .noEvaluators | .simplification, .smtHook | .simplification, .smtlib
  | .simplification, .symbol | .simplification, .token | .simplification, .total
  | .simplification, .trusted | .simplification, .unit | .simplification, .update =>
    .refused .outsideE2 unwritten
  | .simplification, .anywhere => .refused .outsideE2 (unkompiled "ANYWHERE(anywhere)@simplification")
  | .simplification, .comm => .inert (ruled "COMM(comm)@simplification")
  | .simplification, .concat | .simplification, .hasDomainValues | .simplification, .label
  | .simplification, .location | .simplification, .source | .simplification, .symbolOverload
  | .simplification, .uniqueId =>
    .read
  | .simplification, .concrete => .inert (ruled "CONCRETE(concrete)@simplification")
  | .simplification, .cool => .inert (ruled "COOL(cool)@simplification")
  | .simplification, .coolLike => .inert (ruled "COOL_LIKE(cool-like)@any")
  | .simplification, .left => .refused .outsideE2 (erased "LEFT_INTERNAL(left)@any")
  | .simplification, .nat => .refused .outsideE2 (ruled "NAT(nat)@any")
  | .simplification, .nonExecutable => .inert (ruled "NON_EXECUTABLE(non-executable)@simplification")
  | .simplification, .owise => .refused .outsideE2 (unkompiled "OWISE(owise)@simplification")
  | .simplification, .preservesDefinedness => .inert (ruled "PRESERVES_DEFINEDNESS(preserves-definedness)@simplification")
  | .simplification, .priorities => .refused .outsideE2 (erased "PRIORITIES(priorities)@any")
  | .simplification, .priority => .refused .outsideE2 (unkompiled "PRIORITY(priority)@simplification")
  | .simplification, .right => .refused .outsideE2 (erased "RIGHT_INTERNAL(right)@any")
  | .simplification, .simplification => .inert (ruled "SIMPLIFICATION(simplification)@simplification")
  | .simplification, .smtLemma => .inert (ruled "SMT_LEMMA(smt-lemma)@simplification")
  | .simplification, .symbolic => .inert (ruled "SYMBOLIC(symbolic)@simplification")
  | .simplification, .syntactic => .inert (ruled "SYNTACTIC(syntactic)@simplification")
  | .simplification, .terminals => .refused .outsideE2 (erased "TERMINALS(terminals)@any")
  -- claim
  | .claim, .alias | .claim, .aliasRec | .claim, .anywhere | .claim, .assoc | .claim, .binder
  | .claim, .bracket | .claim, .cell | .claim, .colors | .claim, .comm | .claim, .concrete
  | .claim, .constructor | .claim, .cool | .claim, .deprecated | .claim, .element | .claim, .format
  | .claim, .freshGenerator | .claim, .function | .claim, .functional | .claim, .hook
  | .claim, .idem | .claim, .impure | .claim, .injective | .claim, .klabel | .claim, .macroKey
  | .claim, .macroRec | .claim, .memo | .claim, .noEvaluators | .claim, .nonExecutable
  | .claim, .owise | .claim, .preservesDefinedness | .claim, .priority | .claim, .simplification
  | .claim, .smtHook | .claim, .smtLemma | .claim, .smtlib | .claim, .symbol | .claim, .symbolic
  | .claim, .syntactic | .claim, .token | .claim, .total | .claim, .unit | .claim, .update =>
    .refused .outsideE2 unwritten
  | .claim, .circularity => .inert (ruled "CIRCULARITY(circularity)@claim")
  | .claim, .concat | .claim, .hasDomainValues | .claim, .location | .claim, .source
  | .claim, .symbolOverload | .claim, .uniqueId =>
    .read
  | .claim, .coolLike => .inert (ruled "COOL_LIKE(cool-like)@any")
  | .claim, .depends => .inert (ruled "DEPENDS(depends)@claim")
  | .claim, .label => .inert (ruled "LABEL(label)@claim")
  | .claim, .left => .refused .outsideE2 (erased "LEFT_INTERNAL(left)@any")
  | .claim, .nat => .refused .outsideE2 (ruled "NAT(nat)@any")
  | .claim, .priorities => .refused .outsideE2 (erased "PRIORITIES(priorities)@any")
  | .claim, .right => .refused .outsideE2 (erased "RIGHT_INTERNAL(right)@any")
  | .claim, .terminals => .refused .outsideE2 (erased "TERMINALS(terminals)@any")
  | .claim, .trusted => .inert (ruled "TRUSTED(trusted)@claim")
  -- module
  | .module, .alias | .module, .aliasRec | .module, .anywhere | .module, .assoc | .module, .binder
  | .module, .bracket | .module, .cell | .module, .circularity | .module, .colors | .module, .comm
  | .module, .constructor | .module, .cool | .module, .depends | .module, .deprecated
  | .module, .element | .module, .format | .module, .freshGenerator | .module, .function
  | .module, .functional | .module, .hook | .module, .idem | .module, .impure | .module, .injective
  | .module, .klabel | .module, .label | .module, .macroKey | .module, .macroRec | .module, .memo
  | .module, .noEvaluators | .module, .nonExecutable | .module, .owise
  | .module, .preservesDefinedness | .module, .priority | .module, .simplification
  | .module, .smtHook | .module, .smtLemma | .module, .smtlib | .module, .symbol
  | .module, .syntactic | .module, .token | .module, .total | .module, .trusted | .module, .unit
  | .module, .update =>
    .refused .outsideE2 unwritten
  | .module, .concat | .module, .hasDomainValues | .module, .location | .module, .source
  | .module, .symbolOverload | .module, .uniqueId =>
    .read
  | .module, .concrete => .refused .outsideE2 (erased "CONCRETE(concrete)@module")
  | .module, .coolLike => .inert (ruled "COOL_LIKE(cool-like)@any")
  | .module, .left => .refused .outsideE2 (erased "LEFT_INTERNAL(left)@any")
  | .module, .nat => .refused .outsideE2 (ruled "NAT(nat)@any")
  | .module, .priorities => .refused .outsideE2 (erased "PRIORITIES(priorities)@any")
  | .module, .right => .refused .outsideE2 (erased "RIGHT_INTERNAL(right)@any")
  | .module, .symbolic => .refused .outsideE2 (erased "SYMBOLIC(symbolic)@module")
  | .module, .terminals => .refused .outsideE2 (erased "TERMINALS(terminals)@any")
  -- any
  | .any, .alias | .any, .aliasRec | .any, .anywhere | .any, .assoc | .any, .binder
  | .any, .bracket | .any, .cell | .any, .circularity | .any, .colors | .any, .comm
  | .any, .concrete | .any, .constructor | .any, .cool | .any, .depends | .any, .deprecated
  | .any, .element | .any, .format | .any, .freshGenerator | .any, .function | .any, .functional
  | .any, .hook | .any, .idem | .any, .impure | .any, .injective | .any, .klabel | .any, .label
  | .any, .macroKey | .any, .macroRec | .any, .memo | .any, .noEvaluators | .any, .nonExecutable
  | .any, .owise | .any, .preservesDefinedness | .any, .priority | .any, .simplification
  | .any, .smtHook | .any, .smtLemma | .any, .smtlib | .any, .symbol | .any, .symbolic
  | .any, .syntactic | .any, .token | .any, .total | .any, .trusted | .any, .unit | .any, .update =>
    .refused .outsideE2 unwritten
  | .any, .concat | .any, .hasDomainValues | .any, .location | .any, .source
  | .any, .symbolOverload | .any, .uniqueId =>
    .read
  | .any, .coolLike => .inert (ruled "COOL_LIKE(cool-like)@any")
  | .any, .left => .refused .outsideE2 (erased "LEFT_INTERNAL(left)@any")
  | .any, .nat => .refused .outsideE2 (ruled "NAT(nat)@any")
  | .any, .priorities => .refused .outsideE2 (erased "PRIORITIES(priorities)@any")
  | .any, .right => .refused .outsideE2 (erased "RIGHT_INTERNAL(right)@any")
  | .any, .terminals => .refused .outsideE2 (erased "TERMINALS(terminals)@any")

end KCore.Parse
