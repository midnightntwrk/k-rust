/-
  KCore, tooling (compiled, not reviewed). The account of a KORE text's reading: each sentence's
  class (`classify`), every refusal the reader gives (`refusals`: past the first wherever the
  reader can go on), and the sentences classified read that the definition does not account for
  (`unconsumed`), which the generator requires to be none; and the rules and clauses whose
  `CondDecided` the text leaves owed (`owedCondDecided`, `owedClauseCondDecided`).
-/
import KcoreSpec.Parse
import KcoreSpec.Statements
import KcoreSpec.UniqLists
import KcoreSpec.DetachedB

set_option autoImplicit false

namespace KCore.Parse

open KoreAML.Parse (dropPrefix? source? loc? sortName? binders eqnFuel attrStr? hasAttr)

/-- A constructor's name without its type's namespace. -/
private def lastName (s : String) : String := ((s.splitOn ".").getLast?).getD s

def RefusalReason.name (r : RefusalReason) : String := lastName (reprStr r)
def InertReason.name (r : InertReason) : String := lastName (reprStr r)
def UnreadReason.name (r : UnreadReason) : String := lastName (reprStr r)
def ReadingNote.name (r : ReadingNote) : String := lastName (reprStr r)

def SentenceClass.name : SentenceClass → String
  | .read => "read"
  | .readAs r => s!"read {r.name}"
  | .inert r => s!"inert {r.name}"
  | .unread r => s!"unread {r.name}"
  | .refused r => s!"refused {r.name}"

def Refusal.toText (r : Refusal) : String :=
  let place := match r.index with
    | some i => s!"sentence {i}"
    | none => "the module"
  s!"{place} ({r.head}): {r.reason.name}{if r.detail.isEmpty then "" else s!" ({r.detail})"}"

/-- Every rule `coreOf` refuses `unheldVariable` (`unheldRefusal`), where the productions, the rules
and the core are read: each one, not only the first. -/
def unheldFaults (S : Scan) (E : Env) : List Fault :=
  match (prodSyms S E).mapM (symProd E S.eqs), S.rewrites.mapM (ruleOf E.N E.src) with
  | .ok sp, .ok rules => match coreBase S E (prodsOf S E sp) rules with
    | .ok core => S.rewrites.filterMap fun a =>
        (unheldRefusal core E.N a).map fun (r, d) => (⟨r, d, .sentence (.axiom a)⟩ : Fault)
    | .error _ => []
  | _, _ => []

/-- Every equation of a sort's predicate or projection that the core does not state
(`predEqnFaults`), where the productions, the rules and the core are read. -/
def predFaults (S : Scan) (E : Env) : List Fault :=
  match (prodSyms S E).mapM (symProd E S.eqs), S.rewrites.mapM (ruleOf E.N E.src) with
  | .ok sp, .ok rules => match coreBase S E (prodsOf S E sp) rules with
    | .ok core => predEqnFaults E.N E.src S.eqs core
    | .error _ => []
  | _, _ => []

/-- Every sentence of the counter's getter and of the cell tree's initializers that the reader
refuses (`initFaults`), where the productions, the rules and the core are read. -/
def initContentFaults (m : Kore.Module) (S : Scan) (E : Env) : List Fault :=
  match (prodSyms S E).mapM (symProd E S.eqs), S.rewrites.mapM (ruleOf E.N E.src) with
  | .ok sp, .ok rules => match coreOf S E (prodsOf S E sp) rules with
    | .ok core => initFaults E.N E.src m.sentences S.eqs (functionalSyms S.events) core (Cell.top E.config)
    | .error _ => []
  | _, _ => []

/-- Every refusal of the text: the prelude's, each sentence `classify` refuses, and the stages'
on the sentences read: the names, then each production and each rule (all of them), then the
assembly when those pass. -/
def refusals (k : Kore.Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => [⟨none, "", .noModule, ""⟩]
  | some m =>
    let off := preludeLength k
    let pre := if k.modules.dropLast = preludeModules then [] else [preludeRefusal k]
    let cls := m.sentences.zipIdx.filterMap fun (s, i) => match classify s with
      | .refused r => some (⟨some (off + i), headOf s, r, classDetail m s r⟩ : Refusal)
      | _ => none
    let S := scan m.sentences
    let toR := Fault.toRefusal off m
    let stages := match envOf m S with
      -- every equation refused by its head (`eqnHeadFaults`), not only the first
      | .error f => match eqnHeadFaults S with
        | fs@(f' :: _) => if f'.reason == f.reason && f'.detail == f.detail then fs.map toR else [toR f]
        | [] => [toR f]
      | .ok E =>
        let ps := (prodSyms S E).filterMap fun s => match symProd E S.eqs s with
          | .error f => some (toR f)
          | .ok _ => none
        let rs := S.rewrites.filterMap fun a => match ruleOf E.N E.src a with
          | .error f => some (toR f)
          | .ok _ => none
        if ps.isEmpty && rs.isEmpty then
          match finish m S with
          | .error f => match f.reason, unheldFaults S E, predFaults S E with
            | .unheldVariable, us@(_ :: _), _ => us.map toR
            -- every equation `coreOf` refuses by `predEqnFaults`, not only the first
            | _, _, ps@(p :: _) => if p.reason == f.reason && p.detail == f.detail then ps.map toR else [toR f]
            -- every sentence `presOf` refuses by `initFaults`, not only the first
            | _, _, _ => match initContentFaults m S E with
              | is@(p :: _) => if p.reason == f.reason && p.detail == f.detail then is.map toR else [toR f]
              | [] => [toR f]
          | .ok _ => []
        else ps ++ rs
    pre ++ cls ++ stages

/-- A sort's projection `project:X` whose name the registry numbers is that registry symbol: an
equation of it that `predProjOK?` accepts is accounted only where no premise of `Γ` names the
symbol (`GenEqs.freeB`, decided). `predProjOK?` checks that the name is none of the definition's own,
which does not exclude that the semantics lists or applies the registry's symbol of that name (a
parameter symbol numbered as it, for example). Any other name: no check. -/
def regProjFree (c : Semantics) (fn : String) : Bool :=
  if (dropPrefix? "Lblproject'Coln'" fn).isSome then
    match regSymNames.idxOf? fn with
    | some i => GenEqs.freeB c [i]
    | none => true
  else true

/-- An equation `predProjOK?` accepts, a registry-numbered sort projection's where its symbol is
free of `Γ` (`regProjFree`). -/
def predProjAcc (N : Names) (msrc : String) (eqs : List RawEqn) (c : Semantics) (e : RawEqn) : Bool :=
  predProjOK? N msrc eqs c e == some true && regProjFree c e.fn

/-- The equations that `consumed` accounts for without a function of `d` holding them as clauses,
by three classes, each checked, `eqs` the text's equations:
- a sort predicate's equation that is a clause of that predicate's `Semantics.sortPreds` function,
  an `[owise]` one with its exclusion (`predProjOK?`, `predEqnOK`): the sentence is a clause `Γ`
  states (`ΓFns` over `allFns`);
- a sort X's projection `project:X(P) = V` or its selector-domain axiom, where `d` does not number
  `project:X` (`predProjOK?`) and, where the registry numbers a symbol of that name, no premise of
  `Γ` names it (`regProjFree`, `predProjAcc`): the symbol is in no sentence of `Γ`, and the equation
  defines it on the image of the injection;
- a constructor argument's projection `project:c:x(c(x₁, …, xₙ)) = xᵢ`, the projection no symbol
  of the registry or of `d`, c a constructor of the definition (`Semantics.ctorSigs`), the xᵢ
  distinct variables: the symbol is outside `Γ`'s signature, and the equation defines it on c's
  image, where c is injective. -/
def genEqClassOK (E : Env) (d : Definition) (eqs : List RawEqn) (e : RawEqn) : Bool :=
  let c := d.sem
  let noReq := e.req.isNone && e.ens.isNone && !e.dom
  let argProj := (dropPrefix? "Lblproject'Coln" e.fn).isSome && noReq && e.competitors.isNone &&
    !regSymNames.contains e.fn && !c.symNames.contains e.fn &&
    match e.pats, e.rhs with
    | [.app h [] args], .var (.evar v) =>
      c.ctorSigs.any (c.symName ·.name == h.ident.name) &&
      args.all (fun a => match a with | .var (.evar _) => true | _ => false) &&
      args.eraseDups.length == args.length && args.contains (.var (.evar v))
    | _, _ => false
  predProjAcc E.N E.src eqs c e || argProj

/-- A sentence of `kconfigModule`'s text (the kernel text's sentences naming `#KConfigValue` or
`#unboxKConfigValue`, `namesKconfig`), compared with that text in the form the definition selects
(`kernelText`), where the definition imports `kconfigModule` (`Env.imports`): the library module's
own sentence, which `emit` writes with the module (`#unboxKConfigValue(#KConfigValue(X)) = X`). -/
def kconfigOwnSentence (E : Env) (s : Kore.Sentence) : Bool :=
  E.imports.contains kconfigIdx && namesKconfig s && (kernelText E.simpArg).contains s

/-- The sentence classified read that the definition `d` read off the user module `m` (scanned
as `S`, named as `E`) accounts for:
- a builtin module's sentence with a location names a library module (the definition imports
  it); so does a sentence of a K installation's builtin file, which is a library module's
  sentence up to its place (`kBuiltinModule?`), but for the default configuration's cell
  (`isDefaultConfig`), a symbol declaration of `d`, and the sentences read as the definition's own
  (`isOwnLibrarySentence`: K-REFLECTION's, a stream module's rule), which are accounted for as the
  user's;
- a sort or symbol declaration declares a sort or symbol of `d` (the registry's or its own), or
  a projection `project:…` (a sort's, or a named argument's), a cell's initializer or the
  counter's getter, which K declares (none is applied unless `d` numbers it, as a parameter);
- a rewrite axiom is one of `d`'s rules (every one is, `finish`);
- a symbol-overload axiom of an overloading symbol is one of `d`'s overloads (`Semantics.ovls`: the
  symbol, and the symbol it overloads among its `over`), which `Γ` states (`KoreAML.Cons.ovlEqItem`);
- a function equation is one of `d`'s functions' clauses (each `[owise]` equation of a function is
  one), or the equation of `getGeneratedCounterCell` or of a cell's initializer, each no symbol of
  `d`, of the shape under which it states nothing of another symbol (`getterEqnOK`, `initEqnOK`); or an equation of a sort predicate `isX` that is a clause
  of that predicate (which KCore defines from the sort order), or an instance of such a clause at a
  constructor pattern, or that predicate's `[owise]` equation whose exclusion names those
  instances too (`predInstAcc`), or of a sort's projection that `d`
  does not read (`predProjOK?`; a projection a sentence applies is a function of `d` with its
  equation, `Presentation.libProjs`) and that, where the registry numbers it, no premise of `Γ`
  names (`predProjAcc`); or, generated (without a user source), a constructor
  argument's projection's equation (`genEqClassOK`) or a sentence of `kconfigModule`'s text
  (`kconfigOwnSentence`); any other generated equation is refused
  (`RefusalReason.generatedEquation`);
- a `functional` axiom is a constructor's (its place among the productions), a cell
  initializer's whose equation's right side has exactly one value (`initFunctionalOK`), a projection's (none is declared total, and a projection applied is a function
  with its equation or, without one, a parameter), or a function's of `d` that `d` reads total: one of
  its own declared `total` (`Fn.total`, whose totality is decided or an obligation) or one of the
  registry's; or a parameter's: the registry's, or one of `d`'s own declared `total`
  (`ParamPres.total`), which the statements' interpretations are total on (`ParamsTotal`); or an
  open generator's, stated at values under `OpenTotal` (`Definition.totalParams` leaves it out:
  the sentence reads the sort at the interpretation's values, and `Γ` holds no functionality item
  for it), which the account lists (`openFunctionalSentences`);
- a `subsort` axiom is one of `d`'s subsorts or one of the library's below a sort of `d` (its
  place, `eventOf`), one of the library's (`Lib.subsorts`) or of the cells' (`cellSubsorts`), or
  a sort of `d` below KItem, as every sort is in KCore;
- KItem's no-junk axiom gives the presentation's place of the fixed constructors; a sort of `d`
  below KItem that it does not list is read below KItem all the same (`ReadingNote.tokKItem`,
  listed by `tokKItemOmitted`). -/
def consumedWith (generated : Bool) (S : Scan) (E : Env) (d : Definition) (s : Kore.Sentence) : Bool :=
  let c := d.sem
  let sortHas := fun (X : String) => regSortNames.contains X || c.sortNames.contains X
  let symHas := fun (f : String) => regSymNames.contains f || c.symNames.contains f
  let sortOfName := fun (n : String) => (dropPrefix? "Sort" n).getD n
  let cells := Cell.all d.pres.topCell
  let initLabels := cells.map (·.initLabel c)
  -- the cell whose initializer `f` is, where that is no symbol of the registry or of `d`
  let initCell := fun (f : String) => if symOfDefn c f then none else cells.find? (·.initLabel c == f)
  let fnLabels := c.fns.map fun f => c.symName f.label
  -- `project:X` and a named argument's `project:#c:x` (`Lblproject'ColnHash'…`)
  let isProj := fun (f : String) => (dropPrefix? "Lblproject'Coln" f).isSome
  let isPredOrProj := fun (f : String) => isProj f || match dropPrefix? "Lblis" f with
    | some X => sortHas X
    | none => false
  -- the definition's own parameters and their presentations: a `functional` axiom of one is what
  -- its declared `total` states (`ParamPres.total`, `Definition.totalParams`)
  let ownParams := withPres (c.params.filter fun k => decide (nRegSyms ≤ k.sig.name)) d.pres.params
  let paramNotTotal := fun (f : String) => ownParams.any fun (k, kp) => c.symName k.sig.name == f && !kp.total
  -- an open generator's `functional` axiom reads the sort at the interpretation's values: it is
  -- stated at values under `OpenTotal`, not a parameter's declared total (`Definition.totalParams`
  -- leaves it out)
  let openGen := fun (f : String) => c.params.any fun k => k.raw && c.symName k.sig.name == f
  -- the overloading symbol f overloads g (`Semantics.ovls`)
  let ovlPair := fun (as : List Kore.AppPattern) => match overloadSyms? as with
    | some (f, g) => c.ovls.any fun o => c.symName o.sig.name == f && o.over.any (c.symName · == g)
    | none => false
  match scanBuiltin s with
  | some (src, l) => (moduleAt src l).isSome
  | none => if isKBuiltin (sentenceAttrs s) && !isDefaultConfig s && !isOwnLibrarySentence s then (kBuiltinModule? s).isSome else match s with
  | .sort x => sortHas (sortOfName x.sort.ident.name)
  | .hookedSort x => sortHas (sortOfName x.sort.ident.name)
  | .symbol x => let f := x.symbol.ident.ident.name
    symHas f || isProj f || initLabels.contains f || f == "LblgetGeneratedCounterCell"
  | .hookedSymbol x => symHas x.symbol.ident.ident.name
  | .axiom a =>
    if (scanRewrite s).isSome then true
    else match ((rawEqn? a).orElse fun _ => overloadEqn? a).orElse fun _ => projDomainEqn? a with
    | some e =>
      -- every equation of a function is one of its clauses, each `[owise]` one among them (a
      -- selector-domain axiom: a clause of the projection, or generated with it)
      fnLabels.contains e.fn || ovlPair a.attributes ||
      -- the getter's equation and a tree initializer's, by their content
      (!symOfDefn c getterName && getterEqnOK c S.eqs e) ||
      ((initCell e.fn).any fun x => initEqnOK E.N E.src S.eqs c x e) ||
      -- a sort predicate's equation that is its clause, or an instance of one at a constructor
      -- pattern with its `[owise]` equation (`predInstAcc`), or a sort's projection's that no symbol
      -- of `d` reads and, registry-numbered, no premise of `Γ` names (`predProjAcc`), whoever
      -- wrote it; or, generated (no user source), a
      -- constructor argument's projection's (`genEqClassOK`) or a sentence of `kconfigModule`'s
      -- text where `d` imports that module (`kconfigOwnSentence`)
      (generated && (predProjAcc E.N E.src S.eqs c e || predInstAcc E.N E.src S.eqs c e ||
        (!isUserSource a.attributes && (genEqClassOK E d S.eqs e || kconfigOwnSentence E s))))
    | none => match scanEvent s with
      -- a macro symbol's functional axiom: of a symbol that is not part of the reading
      | some (.inl f) => S.macros.contains f || c.ctors.any (fun k => c.symName k.name == f) ||
        (symHas f && (c.fns.all fun fn => c.symName fn.label != f || fn.total) && !paramNotTotal f) ||
        openGen f ||
        ((initCell f).any fun x => initFunctionalOK E.N E.src S.eqs (functionalSyms S.events) c x) ||
        isProj f
      | some (.inr (x, y)) =>
        let libNames := ((importsOf E.imports).flatMap (·.sorts)).map (regSortNames.getD · "")
        ((E.userSortNames.contains x || libNames.contains x) && E.userSortNames.contains y) ||
        (E.userSortNames.contains x && libNames.contains y) ||
        c.userSubsorts.any (fun (a, b) => c.sortName a == x && c.sortName b == y) ||
        -- every sort of `d` is below KItem; the library's subsorts are `d.sem.lib`'s
        (y == "KItem" && sortHas x) ||
        d.pres.cellSubsorts.any (fun (a, b) => c.sortName a == x && c.sortName b == y) ||
        c.lib.subsorts.any fun (a, b) => c.sortName a == x && c.sortName b == y
      | none => (scanOr s).isSome
  | _ => false

/-- `consumedWith`, the arm for the equations no function of `d` holds (a sort predicate's or a
projection's, and those without a user source) among the arms when `generated`. -/
def consumed (S : Scan) (E : Env) (d : Definition) (s : Kore.Sentence) : Bool :=
  consumedWith true S E d s

/-- The user module's equations `consumed` accounts for by its arm for generated equations alone
(`consumedWith false` does not): the sentence's index, the function, the shape (`eqnShape`). -/
def generatedEqs (k : Kore.Definition) (d : Definition) : List (Nat × String × String) :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let S := scan m.sentences
    match envOf m S with
    | .error _ => []
    | .ok E =>
      let off := preludeLength k
      m.sentences.zipIdx.filterMap fun (s, i) =>
        if isRead s && consumed S E d s && !consumedWith false S E d s then
          match s with
          | .axiom a => (((rawEqn? a).orElse fun _ => overloadEqn? a).orElse fun _ => projDomainEqn? a).map
              fun e => (off + i, e.fn, eqnShape e)
          | _ => none
        else none

/-- What a sentence classified read is, as `consumed` reads it. -/
def readKind (s : Kore.Sentence) : String :=
  if (scanBuiltin s).isSome || (isKBuiltin (sentenceAttrs s) && !isDefaultConfig s && !isOwnLibrarySentence s) then
    "builtin sentence" else match s with
  | .sort _ | .hookedSort _ => "sort declaration"
  | .symbol _ | .hookedSymbol _ => "symbol declaration"
  | .axiom a =>
    if (scanRewrite s).isSome then "rewrite axiom"
    else match (rawEqn? a).orElse fun _ => overloadEqn? a with
    -- a user's equation of a symbol of the registry (`_List_`'s, `rule (5 => 6) : _` with `:` a
    -- macro for `ListItem(I) L`): the registry fixes the symbol's meaning (Hooks.lean), and the
    -- equation states more of it, here that two distinct lists are one; no function of the
    -- definition has it as a clause
    | some e => if isUserSource a.attributes && regSymNames.contains e.fn then
        "equation of a symbol the registry interprets" else "equation"
    | none => match scanEvent s with
      | some (.inl _) => "functional axiom"
      | some (.inr _) => "subsort axiom"
      | none => "KItem no-junk axiom"
  | _ => "sentence"

/-- The reason and detail of a read sentence `consumed` does not account for: a generated equation
(no user source) of a registry symbol, sort predicate or projection outside `genEqClassOK`'s classes
is `generatedEquation`, naming the symbol and the shape (`eqnShape`); any other is `unaccounted`,
saying what the sentence is (`readKind`). -/
def unconsumedWhy (s : Kore.Sentence) : RefusalReason × String :=
  match s with
  | .axiom a => match (rawEqn? a).orElse fun _ => projDomainEqn? a with
    | some e =>
      if !isUserSource a.attributes && (regSymNames.contains e.fn || (dropPrefix? "Lblis" e.fn).isSome ||
          (dropPrefix? "Lblproject'Coln" e.fn).isSome) then
        (.generatedEquation, s!"{e.fn}: {eqnShape e}")
      else (.unaccounted, readKind s)
    | none => (.unaccounted, readKind s)
  | _ => (.unaccounted, readKind s)

/-- The user module's sentences classified read that `d` does not account for (`consumed`), as
refusals (`unconsumedWhy`: `unaccounted` with what the sentence is, or `generatedEquation`). -/
def unconsumed (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let S := scan m.sentences
    match envOf m S with
    | .error _ => []
    | .ok E =>
      let off := preludeLength k
      m.sentences.zipIdx.filterMap fun (s, i) =>
        if isRead s && !consumed S E d s then
          let (r, why) := unconsumedWhy s
          some ⟨some (off + i), headOf s, r, why⟩
        else none

/-! ## Rules with an `ensures`

A rewrite rule with an `ensures` C, `\rewrites(lhs ∧ req, rhs ∧ (C = true))`, is read with C as its
`ens` (`Rule.ens`): its right side is rhs where C evaluates to `true`, and where it applies (its left
side matches and its `requires` is true) it blocks the rules of a larger priority, C or not
(`Step.rule`, `NotApplies`). -/

/-- The number of the definition's rules with an `ensures`. -/
def rulesWithEnsures (d : Definition) : Nat :=
  d.sem.rules.countP (·.ens.isSome)

/-- The number of the definition's rules, each read in `Γ` with the premise `⌈rhs ∧ ens⌉`
(`ReadingNote.ruleRightDefined`). -/
def rulesRightDefined (d : Definition) : Nat := d.sem.rules.length

/-- The number of conjuncts `B = true` (`Cond.equals` at Bool with the literal `true`) of a
condition's conjunction. -/
def eqTrueConjunctsCnj : Cond → Nat
  | .and p q => eqTrueConjunctsCnj p + eqTrueConjunctsCnj q
  | .equals s _ (.dv s' (.bool true)) => if s == Srt.bool && s' == Srt.bool then 1 else 0
  | _ => 0

/-- The definition's rules read with conjuncts `B = true` in `pre` or `post`
(`ReadingNote.andAtBool`: the conjuncts after the first of a `requires`, or of the right side's
conditions): each one's index and its numbers of such conjuncts in `pre` and in `post`. -/
def rulesCondConjCnj (d : Definition) : List (Nat × Nat × Nat) :=
  d.sem.rules.zipIdx.filterMap fun (r, i) =>
    let np := eqTrueConjunctsCnj r.pre
    let nq := eqTrueConjunctsCnj r.post
    if np + nq == 0 then none else some (i, np, nq)

/-- The number of the definition's function clauses, other than those written `[owise]`
(`Emit.writtenOwise`: priority 200 without a `priority` attribute, `ReadingNote.owiseAsPriority`),
that `Γ` reads with the premise that no executable clause of a smaller priority applies
(`Faithful.lowerClauses`, `ReadingNote.equationPriority`). -/
def equationsUnderPriority (d : Definition) : Nat :=
  ((withPres d.sem.fns d.pres.fns).map fun (f, fp) =>
    (withPres f.clauses fp.clauses).countP fun (cl, cp) => !writtenOwise cl cp &&
      f.clauses.any fun cl' => !cl'.aside && cl'.prio < cl.prio).sum

/-- The number of the user module's `[owise]` equations of the definition's functions, each read
as a clause of priority 200 (`ReadingNote.owiseAsPriority`). -/
def owiseEquations (k : Kore.Definition) (d : Definition) : Nat :=
  let fnLabels := d.sem.fns.map fun f => d.sem.symName f.label
  match k.modules.getLast? with
  | none => 0
  | some m => m.sentences.countP fun s => isRead s && match s with
    | .axiom a => match rawEqn? a with
      | some e => e.competitors.isSome && fnLabels.contains e.fn
      | none => false
    | _ => false

/-- The user module's `[owise]` equations of the definition's functions read with a premise
narrower than the text's (`ReadingNote.owiseDisjunctNarrower`): each with its place, its function,
and the place of the equation read through `setVarInDropped` whose disjunct holds one element
variable at both of its first two arguments (`svinExcl?`). -/
def owiseNarrowed (k : Kore.Definition) (d : Definition) : List (Nat × String × Nat) :=
  let fnLabels := d.sem.fns.map fun f => d.sem.symName f.label
  match k.modules.getLast? with
  | none => []
  | some m =>
    let off := preludeLength k
    let eqs := m.sentences.zipIdx.filterMap fun (s, i) => if !isRead s then none else match s with
      | .axiom a => (rawEqn? a).bind fun e => if fnLabels.contains e.fn then some (e, i) else none
      | _ => none
    eqs.flatMap fun (o, i) => match o.competitors with
      | none => []
      | some ds => eqs.filterMap fun (e, j) =>
        if e.fn == o.fn && e.competitors.isNone && !nonExec e &&
            ds.any (fun d => ((svinExcl? e d).map (·.1)).getD false)
        then some (off + i, o.fn, off + j) else none

/-- The sort X a disjunct `\exists{KItem}(V:X, inj{X, KItem}(V))` of KItem's no-junk axiom names. -/
def tokKItemDisjunctSort? : Kore.Pattern → Option String
  | .exist _ _ (.app h [A, _] _) => if h.ident.name == "inj" then sortName? A else none
  | _ => none

/-- The user module's KItem no-junk axioms read (`scanOr`) that leave out a sort of `d` below KItem
(`ReadingNote.tokKItem`): each with its place and the sorts X whose `inj{X, KItem}` is one of
KItem's generators (`Semantics.gens`) and none of its disjuncts, each with whether the text states
the subsort (a `subsort{X, KItem}` axiom). -/
def tokKItemOmitted (k : Kore.Definition) (d : Definition) : List (Nat × List (String × Bool)) :=
  let c := d.sem
  let srcs := (c.gens Srt.kitem).filterMap fun g => match g with
    | .inj b => some (c.sortName b)
    | .ctor _ => none
  match k.modules.getLast? with
  | none => []
  | some m =>
    let off := preludeLength k
    let stated := m.sentences.filterMap fun s => match scanEvent s with
      | some (.inr (x, y)) => if y == "KItem" then some x else none
      | _ => none
    m.sentences.zipIdx.filterMap fun (s, i) => if !isRead s then none else match scanOr s with
      | some ds =>
        let named := ds.filterMap tokKItemDisjunctSort?
        match srcs.filter (!named.contains ·) with
        | [] => none
        | xs => some (off + i, xs.map fun x => (x, stated.contains x))
      | none => none

/-! ## A function symbol in a left side

A rule's left side and a clause's argument patterns are patterns, which the matcher reads as
constructors, injections, variables, literals and the collections' symbols (`patCtxAll`). A
function symbol applied there (`List:set(L, I, J)` in a list cell's left side) denotes the values
the function takes at some arguments: the pattern matches a value when some arguments give it, and
matching it needs what the function's inverse says (for `List:set`, that the element at I is J),
which no part of the semantics gives. Such a sentence is refused with a reason of its own, the
function named; it is not read. The collections' symbols (a set's concatenation and element, a cell
set's element) are not named here: they are collection patterns, which the pattern context
decides (`collPatternHooks`). -/

/-- The rules and clauses that apply a function symbol (a function or sort predicate of `d`, a
parameter that is no open generator, a hooked symbol of the registry, or an overloading symbol that
overloads a function, `Semantics.fnOvlSyms`, whose application at covered arguments is that
function's value; no constructor, no collection's symbol and no open generator, which
`openGeneratorInPattern` names) in their left side: one refusal (`functionInPattern`) for each, the
symbol named. -/
def functionInPattern (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    let off := preludeLength k
    let collSyms := c.allColls.flatMap fun cs => [cs.unit, cs.elem, cs.concat]
    let isFn := fun (g : Sym) => !collSyms.contains g && !c.ctorSigs.any (·.name == g) &&
      (c.fns.any (·.label == g) || c.sortPreds.any (·.label == g) ||
        c.params.any (fun k => !k.raw && k.sig.name == g) ||
        hookSigs.any (·.name == g) || c.fnOvlSyms.contains g)
    let named := fun (ts : List Term) => ((Term.headsList ts).filter isFn).eraseDups.map c.symName
    -- the rewrite axioms read, each as many times as it has rules (`scanRewrites`), in the order of
    -- `d`'s rules
    let rws := (m.sentences.zipIdx.flatMap fun (s, i) =>
      if isRead s then (scanRewrites s).map fun _ => (s, i) else []).zip c.rules
    let ruleRs := rws.flatMap fun ((s, i), r) =>
      (named [r.lhs]).map fun f => (⟨some (off + i), headOf s, .functionInPattern, f⟩ : Refusal)
    -- each clause's equation, found by its unique id
    let locate := fun (uid : String) => m.sentences.zipIdx.find? fun (s, _) => match s with
      | .axiom a => uid != "" && attrStr? a.attributes "UNIQUE'Unds'ID" == some uid
      | _ => false
    let clauseRs := (withPres c.fns d.pres.fns).flatMap fun (fn, fp) =>
      (withPres fn.clauses fp.clauses).flatMap fun (cl, cp) =>
        (named cl.pats).map fun f =>
          let (i, h) := match locate cp.info.uid with
            | some (s, j) => (some (off + j), headOf s)
            | none => (none, c.symName fn.label)
          (⟨i, h, .functionInPattern, f⟩ : Refusal)
    ruleRs ++ clauseRs

/-! ## An open generator in a left side

An open generator (`ParamSig.raw`: a symbol the text declares total, lists among its result sort's
generators and gives no constructor axiom) applied in a rule's left side or a clause's argument
pattern: the pattern matches a value v exactly where some arguments are sent to v by the
interpretation, which the text leaves open beyond the laws it writes. The pattern context sorts no
open generator (`patCtxAll`), so such a rule or clause is not sorted. It is refused with a reason
of its own (`RefusalReason.openGeneratorPattern`), the symbol named with the reason that applies at
its result sort S:
- S is not confined (`Semantics.confined`: S is recursive, as through the generator itself, or
  reaches a sort whose elements the text does not state): an element of S that is no value's may be
  the generator's image of other such elements, so which arguments match depends on elements of S
  the text does not name;
- S is confined: every element of S is a value's and the arguments that match are values, a finite
  preimage of the value under the interpretation's graph, which the semantics does not build.
A rule's left side is read through the cut (`Parse.ovlCut`), so it applies an open generator only
where the application's arguments hold `#as`; the reader refuses a cut rule whose generator's sort
is not confined itself (`Parse.openCutRefusal`). -/

/-- The rules and clauses whose left side applies an open generator of `d`: one refusal
(`openGeneratorPattern`) for each, the symbol named with its result sort and the reason that
applies there (`Semantics.confined`). -/
def openGeneratorInPattern (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    let off := preludeLength k
    let opens := c.params.filter (·.raw)
    let why := fun (g : Sym) => match opens.find? (·.sig.name == g) with
      | some k =>
        let s := k.sig.result
        let sn := c.sortName s
        if c.confined s then
          s!"{c.symName g}: its sort {sn} is confined: the arguments it matches at a value are the value's preimage under the interpretation's graph, which the semantics does not build"
        else
          s!"{c.symName g}: its sort {sn} is recursive or reaches an unconfined sort: the arguments it matches depend on elements of {sn} the text does not name"
      | none => c.symName g
    let named := fun (ts : List Term) =>
      ((Term.headsList ts).filter (fun g => opens.any (·.sig.name == g))).eraseDups.map why
    let rws := (m.sentences.zipIdx.flatMap fun (s, i) =>
      if isRead s then (scanRewrites s).map fun _ => (s, i) else []).zip c.rules
    let ruleRs := rws.flatMap fun ((s, i), r) =>
      (named [r.lhs]).map fun f => (⟨some (off + i), headOf s, .openGeneratorPattern, f⟩ : Refusal)
    let locate := fun (uid : String) => m.sentences.zipIdx.find? fun (s, _) => match s with
      | .axiom a => uid != "" && attrStr? a.attributes "UNIQUE'Unds'ID" == some uid
      | _ => false
    let clauseRs := (withPres c.fns d.pres.fns).flatMap fun (fn, fp) =>
      (withPres fn.clauses fp.clauses).flatMap fun (cl, cp) =>
        (named cl.pats).map fun f =>
          let (i, h) := match locate cp.info.uid with
            | some (s, j) => (some (off + j), headOf s)
            | none => (none, c.symName fn.label)
          (⟨i, h, .openGeneratorPattern, f⟩ : Refusal)
    ruleRs ++ clauseRs

/-! ## A range-map symbol binding a variable in a left side

A range map's unit, element and concatenation (`.RangeMap`, `_r|->_`, `_RangeMap_`) are collection
symbols, which `functionInPattern` does not name; but the pattern context sorts none of them
(`patternHooks` and `collPatternHooks` hold no range-map symbol), so a rule or clause whose left side
applies one to arguments holding a variable is not sorted. It is refused with a reason of its own
(`RefusalReason.rangeMapPattern`), the symbol named. -/

mutual
  /-- The symbols of `rms` that `t` applies to arguments holding a variable. -/
  def rmBindersRM (rms : List Sym) : Term → List Sym
    | .app f ts => (if rms.contains f && !(varOccsList ts).isEmpty then [f] else []) ++ rmBindersListRM rms ts
    | .inj _ _ t => rmBindersRM rms t
    | .as t _ => rmBindersRM rms t
    | _ => []
  /-- `rmBindersRM` of each term. -/
  def rmBindersListRM (rms : List Sym) : List Term → List Sym
    | [] => []
    | t :: ts => rmBindersRM rms t ++ rmBindersListRM rms ts
end

/-- The rules and clauses whose left side applies a range-map symbol (the unit, element or
concatenation of a collection of kind `.rangeMap`) to arguments holding a variable: one refusal
(`rangeMapPattern`) for each, the symbol named. -/
def rangeMapInPattern (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    let off := preludeLength k
    let rms := (c.allColls.filter (·.kind == .rangeMap)).flatMap fun cs => [cs.unit, cs.elem, cs.concat]
    let named := fun (ts : List Term) => (rmBindersListRM rms ts).eraseDups.map c.symName
    let rws := (m.sentences.zipIdx.flatMap fun (s, i) =>
      if isRead s then (scanRewrites s).map fun _ => (s, i) else []).zip c.rules
    let ruleRs := rws.flatMap fun ((s, i), r) =>
      (named [r.lhs]).map fun f => (⟨some (off + i), headOf s, .rangeMapPattern, f⟩ : Refusal)
    let locate := fun (uid : String) => m.sentences.zipIdx.find? fun (s, _) => match s with
      | .axiom a => uid != "" && attrStr? a.attributes "UNIQUE'Unds'ID" == some uid
      | _ => false
    let clauseRs := (withPres c.fns d.pres.fns).flatMap fun (fn, fp) =>
      (withPres fn.clauses fp.clauses).flatMap fun (cl, cp) =>
        (named cl.pats).map fun f =>
          let (i, h) := match locate cp.info.uid with
            | some (s, j) => (some (off + j), headOf s)
            | none => (none, c.symName fn.label)
          (⟨i, h, .rangeMapPattern, f⟩ : Refusal)
    ruleRs ++ clauseRs

/-- The rules read with a map key of their left side as a fresh variable and its membership in the
key a conjunct of `pre` (`Parse.keyCut`, `ReadingNote.keyFunctionAsMember`): each rule's place and
the functions so read. -/
def keysAsMember (k : Kore.Definition) : List (Nat × List String) :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    match envOf m (scan m.sentences) with
    | .error _ => []
    | .ok E =>
      let N := E.N
      let off := preludeLength k
      match N.keyFns with
      | [] => []
      | fs => m.sentences.zipIdx.filterMap fun (s, i) => match s with
        | .axiom a => if !isRead s then none else match a.pattern with
          | .rewrites _ (.and _ [l, _]) _ => match term N [] l with
            | .ok (lhs, _) => match (keyCuts fs lhs 0).2.2 with
              | [] => none
              | cs => some (off + i, (cs.map fun (_, f, _, _) => N.syms.getD (f - nRegSyms) "").eraseDups)
            | .error _ => none
          | _ => none
        | _ => none

/-! ## The cell collections' injections are the definition's

A sentence classified `unread cellCollectionInjection` by the names of its sorts (`XCell`,
`XCellMap`) is accepted only when the definition has the collection: a collection sort of that
name whose element (a map's value, a set's or list's element) is that cell sort. -/

/-- The sentences classified as a cell collection's injection whose sorts are not a collection of
`d` and its cell: one refusal (`cellCollectionInjection`) for each. -/
def cellCollUnmatched (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    let pairs := c.colls.map fun cs => (c.sortName ((cs.val.getD cs.key)), c.sortName cs.sort)
    let sortsOf : Kore.Axiom → List (String × String) := fun a => match a.attributes, a.pattern with
      | [⟨⟨⟨"subsort"⟩⟩, [A, B], []⟩], _ => match sortName? A, sortName? B with
        | some x, some y => [(x, y)]
        | _, _ => []
      | _, .or _ ds => ds.filterMap fun dj => injSorts? (binders eqnFuel dj).2
      | _, _ => []
    let off := preludeLength k
    m.sentences.zipIdx.filterMap fun (s, i) => match s, classify s with
      | .axiom a, .unread .cellCollectionInjection =>
        if (sortsOf a).all pairs.contains then none
        else some ⟨some (off + i), headOf s, .cellCollectionInjection, "not a collection of the definition and its cell"⟩
      | _, _ => none

/-! ## The collection laws are the collections'

A sentence classified a collection law (`inert collectionLaw`) or a set's idempotence (`unread
setIdempotence`) by its form is accepted only when its symbol is the concatenation of a collection
of the definition (the library's `Map`, `Set`, `List`, `RangeMap`, or its own), and an idempotence
axiom only of a set's: the reading's map, set and list values satisfy those laws by their
representation (and contradict the idempotence, `UnreadReason.setIdempotence`). A range map's are
stated at its values, through the hook of `_RangeMap_`, which gives a value only on range maps whose
ranges do not overlap: associativity as an equality of patterns, both sides without a value of the
hook or one value (`rmConcat_assoc`), and `.RangeMap` a unit on either side (`rmConcat_unit`); where
ranges overlap the text states no value (`silentTable`), Γ states the interpretation's, and the law
there is a condition on the interpretation. The same law of another
symbol states something of that symbol which no reading of the collections states. -/

/-- The law axioms read by none of the readings, in this order: the concatenation of a
collection of `d` (an idempotence axiom: of a set), an open generator's associativity or
idempotence sentence (`openLawRead`, read into `ParamSig.assoc`, `ParamSig.idem`), a function of
`d` or a parameter no hook implements and no open generator (`fnLawHead`; whose laws `presOf` reads
into `Presentation.laws`, `fnLawAxioms`). One refusal for each other: `openLaw` for another law of
an open generator, `lawAxiom` for the law of any other symbol, the symbol and the law named, with,
for the idempotence of a symbol that kept `constructor`, that it contradicts the constructor's
no-confusion axioms (`f(x, x) = x` against the distinctness of `f` and `x`). -/
def lawUnmatched (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    let off := preludeLength k
    let concatOf := fun (h : String) (set : Bool) =>
      c.allColls.any fun cs => c.symName cs.concat == h && (!set || cs.kind == .set)
    let openGen := fun (h : String) => c.params.any fun k => k.raw && c.symName k.sig.name == h
    let ctor := fun (h : String) => c.ctors.any fun k => c.symName k.name == h
    m.sentences.zipIdx.filterMap fun (s, i) => match s, classify s with
      | .axiom a, .inert .collectionLaw | .axiom a, .unread .setIdempotence =>
        let h := (lawHead? a).getD ""
        let keys := ", ".intercalate (lawKeys a)
        if concatOf h (hasAttr a.attributes "idem") || openLawRead c a || fnLawHead c h then none
        else if openGen h then some ⟨some (off + i), headOf s, .openLaw, s!"{h}: {keys}"⟩
        else if ctor h && hasAttr a.attributes "idem" then
          some ⟨some (off + i), headOf s, .lawAxiom, s!"{h}: {keys}: idempotence of a constructor contradicts its no-confusion axioms"⟩
        else some ⟨some (off + i), headOf s, .lawAxiom, s!"{h}: {keys}"⟩
      | _, _ => none

/-- The law axioms of the open generators of `d` (`openLawAxioms`), each an axiom of `Γ`
(`Faithful.lawItemsK`): the sentence's index, the symbol and the laws named. The interpretations
the statements speak of satisfy each at values (`OpenLaws`, owed). -/
def openLawSentences (k : Kore.Definition) (d : Definition) : List (Nat × String × List String) :=
  match k.modules.getLast? with
  | none => []
  | some m => (openLawAxioms d.sem m.sentences).map fun (i, a) =>
    (preludeLength k + i, (lawHead? a).getD "", lawKeys a)

/-- The law axioms on the functions of `d` (`fnLawAxioms`), each read as the law of
`Presentation.laws` at its place: the sentence's index, the symbol and the laws named. Each is
stated at values under `FnLaws`, owed. -/
def fnLawSentences (k : Kore.Definition) (d : Definition) : List (Nat × String × List String) :=
  match k.modules.getLast? with
  | none => []
  | some m => (fnLawAxioms d.sem m.sentences).map fun (i, a) =>
    (preludeLength k + i, (lawHead? a).getD "", lawKeys a)

/-! ## What a law of a function reads of the interpretation

`LawAt c l` compares the results `EvalTerm` gives the two sides at values. Those results depend on
the interpretation `c.hooks` only through a function's rest (`Semantics.fnRest`: where every clause
fails), a parameter symbol no hook implements (`paramVal`), and a library hook at a point its text
leaves open (`hookRes` at a `silent` point, also as a parameter's hook). Where evaluating the law's
sides reaches none of these, `LawAt` is one fact, the same at every interpretation: true at every
one or at none. -/

/-- The symbols the terms of a condition apply. -/
def condSymOccsFL : Cond → List Sym
  | .ceil _ t => symOccs t
  | .equals _ t u | .mem _ t u => symOccs t ++ symOccs u
  | .exMatch _ _ p t b => symOccs p ++ symOccs t ++ condSymOccsFL b
  | .not p | .ex _ p | .all _ p => condSymOccsFL p
  | .and p q | .or p q | .implies p q => condSymOccsFL p ++ condSymOccsFL q
  | .top | .bot => []

/-- The symbols a clause applies: in its patterns, right side, `requires`, `ensures` and
predicates. -/
def clauseSymOccsFL (cl : Clause) : List Sym :=
  symOccsList cl.pats ++ symOccs cl.rhs ++ (cl.req.toList ++ cl.ens.toList).flatMap symOccs ++
    condSymOccsFL cl.pre ++ condSymOccsFL cl.post

/-- Some clause of `f` applies at every argument list of its sorts: the clauses without a
`requires`, without a predicate `pre` and without a repeated pattern variable cover `f`'s argument
sorts (`covers`). Such a clause does not fail where its patterns match (`Fails` asks a `requires`
or a `pre` that fails), so the clauses of `f` never all fail at values and its rest (`Eval.rest`)
is never read. A function this does not confirm is taken to read its rest. -/
def fnCoveredFL (c : Semantics) (f : Fn) : Bool :=
  c.covers (Semantics.coverFuel f) f.args
    ((f.clauses.filter fun cl => cl.req.isNone && cl.pre.isTop && nodup (varOccsList cl.pats)).map (·.pats))

/-- What the symbols `gs` read of the interpretation, `seen` those already searched. Each symbol is
taken as `EvalTerm` takes its application: a constructor reads nothing; a library hook reads the
interpretation where it has points its text leaves open (`silentKey`); a parameter reads it where
no hook implements it, else where its hook has such points (`paramVal`); an overloading symbol
reads what the functions it overloads read (`ovlFn`); a function (`lookupFn`) reads its rest where
it is not `fnCoveredFL`, and otherwise what its clauses apply. `none` where none is reached. Each
step uses one unit of the fuel; with none left the search has not ruled the interpretation out,
and the answer says so. -/
def lawReadsFL (c : Semantics) : Nat → List Sym → List Sym → Option String
  | 0, _, _ => some "what a search that stopped did not rule out"
  | _, _, [] => none
  | n + 1, seen, g :: gs =>
    if seen.contains g || c.isCtor g then lawReadsFL c n seen gs
    else if isHook g then
      if silentKey g then some s!"{c.symName g} at the points its hook's text leaves open"
      else lawReadsFL c n (g :: seen) gs
    else match c.lookupParam g with
    | some k => match k.impl with
      | none => some s!"the parameter {c.symName g}: its value is the interpretation's"
      | some h =>
        if silentKey h then some s!"the parameter {c.symName g} at the points its hook's text leaves open"
        else lawReadsFL c n (g :: seen) gs
    | none =>
      if c.isOvl g then lawReadsFL c n (g :: seen) (gs ++ ((c.lookupOvl g).map (·.over)).getD [])
      else match c.lookupFn g with
      | some f =>
        if fnCoveredFL c f then lawReadsFL c n (g :: seen) (gs ++ f.clauses.flatMap clauseSymOccsFL)
        else some s!"the rest of {c.symName g}: its value where its clauses are not shown to apply is the interpretation's"
      | none => lawReadsFL c n (g :: seen) gs

/-- What the law reads of the interpretation (`lawReadsFL` from the symbols of its two sides);
`none` where it reads nothing of it. -/
def lawReads (c : Semantics) (l : LawEq) : Option String :=
  lawReadsFL c 100000 [] (symOccs l.lhs ++ symOccs l.rhs)

/-- The account's entry for a law under `FnLaws`. Where the law reads the interpretation it is a
condition on the interpretation, met by some and not by others, and `HookParams.none` does not
discharge it. Otherwise it is owed and open: one fact at every interpretation, not decided here.
It is never printed false: where one side has no result and the other the result `none`, `LawAt`
is false though both sides are empty and the law holds. -/
def fnLawEntry (c : Semantics) (l : LawEq) : String :=
  match lawReads c l with
  | some r => s!"FnLaws owed: a condition on the interpretation (the law reads {r}); not discharged at HookParams.none"
  | none => "FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here"

/-- The `functional` axioms of the open generators of `d` (`ParamSig.raw`): the sentence's index and
the symbol. Each is stated at values under `OpenTotal` (the interpretation gives the generator a
value at every argument list of its sorts), owed: `Γ` holds no functionality item for an open
generator, and `ΓDomains` states its application to values to be the interpretation's value, or
nothing where the interpretation gives none. -/
def openFunctionalSentences (k : Kore.Definition) (d : Definition) : List (Nat × String) :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    let off := preludeLength k
    m.sentences.zipIdx.filterMap fun (s, i) =>
      if isRead s then match scanEvent s with
        | some (.inl f) => if c.params.any (fun k => k.raw && c.symName k.sig.name == f) then some (off + i, f) else none
        | _ => none
      else none

/-- The `unit` attributes the reader ignores: a symbol declaration of the user module carrying
`unit{}(u)` whose symbol `d` reads as a constructor or an open generator, where no axiom of the
module with the attribute `unit` states a law of that symbol (`lawHead?`): the sentence's index, the
symbol and the unit named. A theory is its sentences, and an attribute is no sentence: with no
sentence `f(K, u) = K` or `f(u, K) = K` the text states no unit law of `f`, so the declaration read
without the attribute reads the theory the text states. Nothing is added for it (`ParamSig` has no
unit; `Γ` holds no unit item). Where the text writes the unit sentences (of a function, read into
`Presentation.laws`; of a collection's concatenation) the attribute is not listed. -/
def unitIgnored (k : Kore.Definition) (d : Definition) : List (Nat × String × String) :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    let off := preludeLength k
    let named := fun (f : String) =>
      c.ctors.any (fun g => c.symName g.name == f) ||
        c.params.any (fun g => g.raw && c.symName g.sig.name == f)
    let unitSentence := fun (f : String) => m.sentences.any fun s => match s with
      | .axiom a => hasAttr a.attributes "unit" && lawHead? a == some f
      | _ => false
    m.sentences.zipIdx.filterMap fun (s, i) => match s with
      | .symbol ss =>
        let f := ss.symbol.ident.ident.name
        match ss.attributes.find? (·.head.ident.name == "unit") with
        | some u =>
          if named f && !unitSentence f then
            let us := match u.args with
              | [.app h _ _] => h.ident.name
              | _ => ""
            some (off + i, f, us)
          else none
        | none => none
      | _ => none

/-! ## The library's modules in a K installation's text

A sentence of a K installation's builtin file is read as the library module's sentence it equals
up to its place. The library then reads the whole module (its sorts, constructors, subsorts and
parameter symbols, `libOf`, `libParams`); so the text must hold every sentence of the module's
text, else the library would read a declaration or axiom the text does not state. krust's text
names its modules by source and line and holds them whole by the tie (`emit` writes them). -/

/-- The sentences of the library modules a K installation's text holds sentences of that the text
does not hold, up to their places: one refusal (`builtinIncomplete`) for each, its module named.
A module text's
lemma written without a place (`classify`: `inert simplification`) is not required: it is not a
sentence of the module's file but one the compiler generates from the module's symbols (MAP's
definedness lemma of a concatenation), which a text may hold or not, and a lemma states nothing the
reading reads (`libraryUnstated` does not compare one either). The same of K-REFLECTION, read as the
definition's own (`reflectionAsOwn`): a text holding one of its sentences holds all of them, so the
reading of the module is the reading of its whole text. -/
def missingBuiltin (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let S := scan m.sentences
    let held := m.sentences.map bare
    let refl := if m.sentences.any isReflectionSentence then
        reflectionModuleText.filterMap fun t =>
          if held.any (fun s => decide (s = t)) then none
          else some (⟨none, "K-REFLECTION", .builtinIncomplete, Kore.Printer.sentence t⟩ : Refusal)
      else []
    refl ++ (S.kbuiltin.eraseDups.flatMap fun i =>
      (moduleText d.pres.simpArg i).filterMap fun t =>
        -- a lemma without a place (MAP's `#Ceil` of a concatenation) is no sentence of the module's
        -- file, and states nothing the reading reads (`InertReason.simplification`)
        if classify t == .inert .simplification then none
        else if held.any (fun s => decide (s = bare t)) then none
        else some ⟨none, (library.getD i default).name, .builtinIncomplete, Kore.Printer.sentence (bare t)⟩)

/-! ## Inert constructor axioms are the induced ones

An axiom classified inert as a constructor axiom (`distinctCtors`, `injectivity`, `noJunk`) is
accepted only when it is one the definition's constructors induce: one of `emit`'s, which writes
them from the semantics, up to the names of its variables and the order of the arguments of each
`\and` and `\or`. A renaming of the variables that is one-to-one, and a reordering or regrouping
of a conjunction's or disjunction's arguments, change nothing an axiom states, and neither does an
argument repeated (`\or(A, A, B)` and `\or(A, B)` denote one set, as do `\and(A, A)` and `A`'s
conjunction); the comparison is of normal forms (`canon`) under all three, so equal normal forms are
such a renaming, reordering and repetition of each other. (`emit` writes a no-junk axiom's injections
from the subsort closure, which lists a pair once per path: wasm's `EmptyStmt < Instr < Stmt` and
`EmptyStmt < Defn < Stmt` give `inj{EmptyStmt, Stmt}` twice, the text once.)

`emit` writes a library constructor's distinctness from the later constructors of its sort in the
library only; a constructor of the definition's own whose sort is a library sort (K-REFLECTION's
`#noParse` of K-IO's `IOError`) is distinct from each of that sort's library constructors as well,
as KCore's values, the free terms over all the constructors, are; those axioms are induced too.

`emit` writes a cell's constructor with no distinctness axiom (a cell's sort has one constructor,
the cell). The sort of a cell that may be absent (`multiplicity="?"`) has a second, the constant
kompile declares for the absent cell (`.OneCell` of `<one>`), and the text states the two distinct.
Both are constructors of the definition, so `Γ` states their distinctness (`consItemsK`: Cons-Dist
of each pair of generators of a sort that are no open generators, unguarded where neither is a
function-overloaded symbol and their overload closures do not meet); those axioms are induced too. -/

/-- `ps` without an argument printed as the one before it. -/
def dedupAdj : List Kore.Pattern → List Kore.Pattern
  | [] => []
  | a :: tl@(b :: _) => if Kore.Printer.pattern a == Kore.Printer.pattern b then dedupAdj tl else a :: dedupAdj tl
  | [a] => [a]

mutual
  /-- `p` with its element variables renamed by `f` (name and sort to name), and the arguments of
  each `\and` and `\or` flattened into it when of its connective and sort, sorted by `key`, and an
  argument printed as the one before it dropped (`dedupAdj`). -/
  def normPat (f : String → Kore.KSort → String) (key : Kore.Pattern → String) : Kore.Pattern → Kore.Pattern
    | .var (.evar x) => .var (.evar { x with var := { ident := { name := f x.var.ident.name x.sort } } })
    | .app h ss ps => .app h ss (normList f key ps)
    | .not s p => .not s (normPat f key p)
    | .and s ps => .and s (dedupAdj ((normList f key ps).flatMap (fun
        | .and s' qs => if decide (s' = s) then qs else [.and s' qs]
        | q => [q]) |>.mergeSort fun a b => decide (key a ≤ key b)))
    | .or s ps => .or s (dedupAdj ((normList f key ps).flatMap (fun
        | .or s' qs => if decide (s' = s) then qs else [.or s' qs]
        | q => [q]) |>.mergeSort fun a b => decide (key a ≤ key b)))
    | .implies s p q => .implies s (normPat f key p) (normPat f key q)
    | .iff s p q => .iff s (normPat f key p) (normPat f key q)
    | .exist s x p => .exist s { x with var := { ident := { name := f x.var.ident.name x.sort } } } (normPat f key p)
    | .forall s x p => .forall s { x with var := { ident := { name := f x.var.ident.name x.sort } } } (normPat f key p)
    | .mu v p => .mu v (normPat f key p)
    | .nu v p => .nu v (normPat f key p)
    | .ceil a b p => .ceil a b (normPat f key p)
    | .floor a b p => .floor a b (normPat f key p)
    | .equals a b p q => .equals a b (normPat f key p) (normPat f key q)
    | .in a b p q => .in a b (normPat f key p) (normPat f key q)
    | .next s p => .next s (normPat f key p)
    | .rewrites s p q => .rewrites s (normPat f key p) (normPat f key q)
    | .leftAssoc h ss ps => .leftAssoc h ss (normList f key ps)
    | .rightAssoc h ss ps => .rightAssoc h ss (normList f key ps)
    | p => p
  def normList (f : String → Kore.KSort → String) (key : Kore.Pattern → String) :
      List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => normPat f key p :: normList f key ps
end

mutual
  /-- The element variables of a pattern, binders included, in the order met (with repeats). -/
  def evarsOf : Kore.Pattern → List (String × Kore.KSort)
    | .var (.evar x) => [(x.var.ident.name, x.sort)]
    | .app _ _ ps | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => evarsList ps
    | .not _ p | .mu _ p | .nu _ p | .ceil _ _ p | .floor _ _ p | .next _ p => evarsOf p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q => evarsOf p ++ evarsOf q
    | .exist _ x p | .forall _ x p => (x.var.ident.name, x.sort) :: evarsOf p
    | _ => []
  def evarsList : List Kore.Pattern → List (String × Kore.KSort)
    | [] => []
    | p :: ps => evarsOf p ++ evarsList ps
end

/-- The normal form of an axiom's pattern: its conjunctions and disjunctions ordered by their
arguments with the variables' names erased, then its variables renamed `V0`, `V1`, … in the order
met (one-to-one: distinct name-and-sort pairs get distinct names), then ordered again. -/
def canon (p : Kore.Pattern) : String :=
  let erased := normPat (fun _ _ => "_") Kore.Printer.pattern
  let p₁ := normPat (fun n _ => n) (fun q => Kore.Printer.pattern (erased q)) p
  let names := (evarsOf p₁).eraseDups
  let ren := fun (n : String) (s : Kore.KSort) => s!"V{(names.idxOf? (n, s)).getD names.length}"
  Kore.Printer.pattern (normPat (fun n _ => n) Kore.Printer.pattern (normPat ren (fun _ => "") p₁))

mutual
  /-- `p` with its element variables renamed by `f` (name and sort to name), binders included,
  nothing else changed. -/
  def renamePat (f : String → Kore.KSort → String) : Kore.Pattern → Kore.Pattern
    | .var (.evar x) => .var (.evar { x with var := { ident := { name := f x.var.ident.name x.sort } } })
    | .app h ss ps => .app h ss (renameList f ps)
    | .not s p => .not s (renamePat f p)
    | .and s ps => .and s (renameList f ps)
    | .or s ps => .or s (renameList f ps)
    | .implies s p q => .implies s (renamePat f p) (renamePat f q)
    | .iff s p q => .iff s (renamePat f p) (renamePat f q)
    | .exist s x p => .exist s { x with var := { ident := { name := f x.var.ident.name x.sort } } } (renamePat f p)
    | .forall s x p => .forall s { x with var := { ident := { name := f x.var.ident.name x.sort } } } (renamePat f p)
    | .mu v p => .mu v (renamePat f p)
    | .nu v p => .nu v (renamePat f p)
    | .ceil a b p => .ceil a b (renamePat f p)
    | .floor a b p => .floor a b (renamePat f p)
    | .equals a b p q => .equals a b (renamePat f p) (renamePat f q)
    | .in a b p q => .in a b (renamePat f p) (renamePat f q)
    | .next s p => .next s (renamePat f p)
    | .rewrites s p q => .rewrites s (renamePat f p) (renamePat f q)
    | .leftAssoc h ss ps => .leftAssoc h ss (renameList f ps)
    | .rightAssoc h ss ps => .rightAssoc h ss (renameList f ps)
    | p => p
  def renameList (f : String → Kore.KSort → String) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => renamePat f p :: renameList f ps
end

/-- A sentence up to the names of its element variables, printed without its place (`bare`): an
axiom's or claim's variables renamed `V0`, `V1`, … in the order met (one-to-one: distinct
name-and-sort pairs get distinct names). Two sentences have one key exactly when they are one up to
a one-to-one renaming of their variables, which changes nothing a sentence states. -/
def alphaKey (s : Kore.Sentence) : String :=
  let ren := fun (p : Kore.Pattern) =>
    let names := (evarsOf p).eraseDups
    renamePat (fun n s => s!"V{(names.idxOf? (n, s)).getD names.length}") p
  Kore.Printer.sentence (match bare s with
    | .axiom a => .axiom { a with pattern := ren a.pattern }
    | .claim c => .claim { c with pattern := ren c.pattern }
    | t => t)

/-- The sentences every definition holds (`kernelText`, with `#KConfigValue`'s when the definition
holds it) that the text does not, up to their places and the names of their variables (`alphaKey`):
kompile numbers its generated variables (`Var'Unds'GenN`) differently from run to run, so two runs
of one K text give one account. A K installation's text has not the projections' selector axioms
that krust writes. Not a refusal: those axioms are lemmas (`simplification`) and the domains of the
kernel's projections (of K and KItem), which no clause is read from: the semantics reads those
projections as no function. -/
def kernelAbsent (k : Kore.Definition) (d : Definition) : List Kore.Sentence :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let held := m.sentences.map alphaKey
    (kernelText d.pres.simpArg (hasKconfig d.sem)).filter fun t => !held.contains (alphaKey t)

/-- An inert constructor axiom's reason. -/
def ctorInert? (s : Kore.Sentence) : Option InertReason :=
  match classify s with
  | .inert .distinctCtors => some .distinctCtors
  | .inert .injectivity => some .injectivity
  | .inert .noJunk => some .noJunk
  | _ => none

/-- The symbol of `c` named `n`, by its number. -/
def symOfName (c : Semantics) (n : String) : Option Sym := (c.symNames.idxOf? n).map (nRegSyms + ·)

/-- The symbols f reaches along the overloads in at most `n` steps, f among them (as
`Semantics.ovlReach`). -/
def ovlReachA (c : Semantics) : Nat → Sym → List Sym
  | 0, f => [f]
  | n + 1, f => f :: match c.lookupOvl f with
    | some o => o.over.flatMap (ovlReachA c n)
    | none => []

/-- Two symbols whose overload closures meet (`Semantics.ovlClosure`, the reach in one step more
than there are overloading symbols): one overloads the other, or both a third (for two symbols that
overload none: the same symbol). -/
def ovlMeet (c : Semantics) (f g : Sym) : Bool :=
  (ovlReachA c (c.ovls.length + 1) f).any (ovlReachA c (c.ovls.length + 1) g).contains

/-- A distinctness axiom `¬(f(X̄) ∧ g(Ȳ))` of two symbols of `c` whose overload closures meet
(`UnreadReason.overloadConfusion`). -/
def ovlConfused (c : Semantics) (a : Kore.Axiom) : Bool :=
  !c.ovls.isEmpty && match a.pattern with
    | .not _ (.and _ [.app f [] _, .app g [] _]) => match symOfName c f.ident.name, symOfName c g.ident.name with
      | some f', some g' => ovlMeet c f' g'
      | _, _ => false
    | _ => false

/-- The constructor axioms the overloading symbols induce, as `Γ` states them (`consItemsK`: an
overloading symbol is a generator of its sort): each one's injectivity (Cons-Inj), its distinctness
from each other constructor or overloading symbol of its sort whose overload closure does not meet
its own (Cons-Dist, which `distGuarded` leaves unguarded; where the closures meet `Γ` states it at
uncovered arguments only, `overloadConfusion`), and the no-junk axiom of each of their sorts with
them among its generators (Cons-NoJunk). `emit` writes none of them (it writes no overloading
symbol). -/
def ovlInduced (c : Semantics) : List Kore.Sentence :=
  let gens := fun (N : Srt) => (c.ctorSigs ++ c.ovlSigs).filter (·.result == N)
  let own := c.ovls.flatMap fun o =>
    let k := o.sig
    (if k.args.isEmpty then [] else [KoreAML.injectivityAx (toK c k)]) ++
      ((gens k.result).filter fun k' => k'.name != k.name && !ovlMeet c k.name k'.name).map
        fun k' => KoreAML.distinctnessAx (toK c k) (toK c k')
  own ++ (c.ovls.map (·.sig.result)).eraseDups.map fun N =>
    let gs := (gens N).map Gen.ctor ++ ((c.subsorts.filter (·.2 == N)).map (·.1)).map Gen.inj
    KoreAML.axiom0 (.or (srtOf c N) (KoreAML.noJunkDisjuncts (c.sortName N) [] (gs.map (Gen.toK c))))
      [KoreAML.attr "constructor"]

/-- The no-junk axiom of each open generator's result sort, as `Γ` states it (`consItemsK`: an open
generator is a generator of its sort, with no functionality, injectivity or distinctness item):
over the sort's generators (`Semantics.gens`), the open generators among them. `emit` writes it
without them. -/
def openInduced (c : Semantics) : List Kore.Sentence :=
  ((c.params.filter (·.raw)).map (·.sig.result)).eraseDups.map fun N =>
    KoreAML.axiom0 (.or (srtOf c N) (KoreAML.noJunkDisjuncts (c.sortName N) [] ((c.gens N).map (Gen.toK c))))
      [KoreAML.attr "constructor"]

/-- The axioms of the user module classified inert as constructor axioms that are not, up to the
names of their variables and the order of conjuncts and disjuncts, one the definition's
constructors, overloading symbols and open generators induce (`emit`'s of the same class,
`ovlInduced`, `openInduced`), nor an
overload's confusion (`ovlConfused`): one refusal (`inertMismatch`) for each. -/
def uninduced (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let c := d.sem
    -- the distinctness of each own constructor of a library sort from that sort's library constructors
    let mixed := c.ctors.flatMap fun k => (c.lib.ctors.filter (·.result == k.result)).map fun f =>
      KoreAML.distinctnessAx (toK c f) (toK c k)
    -- the distinctness of each cell's constructor from the other constructors of its sort
    let cellDist := d.pres.cellCtors.flatMap fun k =>
      (c.ctors.filter fun k' => k'.result == k.result && k'.name != k.name &&
        !c.isOpenGen (.ctor k) && !c.isOpenGen (.ctor k') &&
        !c.fnOvl (.ctor k) && !c.fnOvl (.ctor k') && !ovlMeet c k.name k'.name).map fun k' =>
        KoreAML.distinctnessAx (toK c k) (toK c k')
    -- the no-junk axiom of an open generator's result sort is `openInduced`'s alone: `emit`'s,
    -- without the open generators, would take a text whose axiom does not list them
    let rawSorts := ((c.params.filter (·.raw)).map (·.sig.result)).map (srtOf c)
    let emitted := (userModule d.sem d.pres).sentences.filter fun s => match s, ctorInert? s with
      | .axiom a, some .noJunk => match a.pattern with
        | .or S _ => !rawSorts.any fun T => decide (S = T)
        | _ => true
      | _, _ => true
    let induced := (emitted ++ mixed ++ cellDist ++ ovlInduced c ++ openInduced c).filterMap fun s => match s, ctorInert? s with
      | .axiom a, some r => some (r.name, canon a.pattern)
      | _, _ => none
    let off := preludeLength k
    m.sentences.zipIdx.filterMap fun (s, i) => match s, ctorInert? s with
      | .axiom a, some r =>
        if induced.contains (r.name, canon a.pattern) || (r == .distinctCtors && ovlConfused c a) then none
        else some ⟨some (off + i), headOf s, .inertMismatch, r.name⟩
      | _, _ => none

/-- The distinctness axioms of the user module between two symbols whose overload closures meet
(`ovlConfused`, `UnreadReason.overloadConfusion`): stated by the text and not read. Their places
and heads. -/
def overloadConfusions (k : Kore.Definition) (d : Definition) : List (Nat × String) :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let off := preludeLength k
    m.sentences.zipIdx.filterMap fun (s, i) => match s, ctorInert? s with
      | .axiom a, some .distinctCtors => if ovlConfused d.sem a then some (off + i, headOf s) else none
      | _, _ => none

/-- The overloading symbols of `d` that overload a function (`Semantics.fnOvlSyms`,
`ReadingNote.overloadFunction`), each with the functions among the symbols it overloads, by name. -/
def overloadFunctions (d : Definition) : List (String × List String) :=
  let c := d.sem
  (c.ovls.filter fun o => c.fnOvlSyms.contains o.sig.name).map fun o =>
    (c.symName o.sig.name, (o.over.filter fun g => c.fns.any (·.label == g)).map c.symName)

/-- The sentences `emit` writes from the library's data for the modules the definition imports (its
sorts' declarations, predicates, projections and no-junk axioms, its constructors' axioms, its
subsorts, its total symbols' functional axioms: `libBlocks` less the modules' and the kernel's
texts) that the text does not hold, up to their places and, for an axiom, up to the names of its
variables and the order of its conjunctions' and disjunctions' arguments: one refusal
(`builtinIncomplete`, the sentence as `emit` writes it) for each. The library's data must state
only what its modules' texts state. A lemma (`[simplification]`) and a projection's domain
(`projectionDomainAsClause`, read only as a clause of a projection the definition reads as a
function, where `emit` writes it with that function's equations) are not compared: krust writes
both for every sort, K 7.1.337 neither. -/
def libraryUnstated (k : Kore.Definition) (d : Definition) : List Refusal :=
  match k.modules.getLast? with
  | none => []
  | some m =>
    let arg := d.pres.simpArg
    let texts := kernelModule arg ++ d.pres.imports.flatMap (moduleText arg)
    let held := m.sentences.map bare
    let heldCanon := m.sentences.filterMap fun s => match s with
      | .axiom a => some (canon a.pattern)
      | _ => none
    (libBlocks d.sem d.pres).flatten.filterMap fun t =>
      if texts.any (fun u => decide (u = t)) then none
      else if classify t == .inert .simplification || classify t == .readAs .projectionDomainAsClause then none
      else if held.any (fun s => decide (s = bare t)) then none
      else match t with
        | .axiom a => if heldCanon.contains (canon a.pattern) then none
            else some ⟨none, "library data", .builtinIncomplete, Kore.Printer.sentence t⟩
        | _ => some ⟨none, "library data", .builtinIncomplete, Kore.Printer.sentence t⟩

/-- The account's refusals of a text the reader reads as `d`: the inert constructor axioms not
induced, the library modules not whole in the text, the cell collections' injections and the laws
of no collection of `d`, the library's data the text does not state, the left sides applying a
function symbol or an open generator, or binding a variable under a range-map symbol. -/
def accountRefusals (k : Kore.Definition) (d : Definition) : List Refusal :=
  uninduced k d ++ missingBuiltin k d ++ cellCollUnmatched k d ++ libraryUnstated k d ++
    functionInPattern k d ++ lawUnmatched k d ++ rangeMapInPattern k d ++ openGeneratorInPattern k d

/-! ## Connective readings and `#configuration`

A sentence read through several connective readings (`connNotes`) is classified by the first; the
account lists every one of them per sentence. K-REFLECTION's `#configuration` is read as a parameter
symbol (`ReadingNote.reflectionAsOwn`), whose value is one fixed for every configuration, not the one
K's documentation gives it; the account lists the read sentences applying it. -/

/-- The read rewrite axioms and equations of the user module read through a connective, each with
its position in the file and every note it is read through (`connNotes`). -/
def connReadings (k : Kore.Definition) : List (Nat × List ReadingNote) :=
  match k.modules.getLast? with
  | none => []
  | some m => m.sentences.zipIdx.filterMap fun (s, i) => match s with
    | .axiom a => if isRead s && !(connNotes a).isEmpty then some (preludeLength k + i, connNotes a) else none
    | _ => none

mutual
  /-- The pattern applies the symbol named `n`. -/
  def appliesSym (n : String) : Kore.Pattern → Bool
    | .app h _ ps => h.ident.name == n || appliesSymList n ps
    | .and _ ps | .or _ ps | .leftAssoc _ _ ps | .rightAssoc _ _ ps => appliesSymList n ps
    | .not _ p | .next _ p | .ceil _ _ p | .floor _ _ p | .mu _ p | .nu _ p | .exist _ _ p
    | .forall _ _ p => appliesSym n p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      appliesSym n p || appliesSym n q
    | _ => false
    termination_by structural p => p
  def appliesSymList (n : String) : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => appliesSym n p || appliesSymList n ps
    termination_by structural ps => ps
end

/-- K-REFLECTION's `#configuration` symbol, as KORE names it. -/
def configurationSym : String := "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K"

/-- The read axioms of the user module that apply `#configuration`, by position in the file; none
when the user module does not declare the symbol. -/
def configurationUses (k : Kore.Definition) : Option (List Nat) :=
  match k.modules.getLast? with
  | none => none
  | some m =>
    if m.sentences.any (fun s => match s with
        | .hookedSymbol h => h.symbol.ident.ident.name == configurationSym
        | .symbol h => h.symbol.ident.ident.name == configurationSym
        | _ => false) then
      some (m.sentences.zipIdx.filterMap fun (s, i) => match s with
        | .axiom a => if isRead s && appliesSym configurationSym a.pattern then some (preludeLength k + i) else none
        | _ => none)
    else none

/-- The user module's sentences counted by class, the classes in the order first met. -/
def classCounts (k : Kore.Definition) : List (String × Nat) :=
  let ss := (k.modules.getLast?.map (·.sentences)).getD []
  let names := ss.map fun s => (classify s).name
  names.eraseDups.map fun n => (n, names.count n)

/-! ## Facts the text leaves open

A rule whose conditions are closed over a variable the left side does not bind, of a sort the text
leaves unconfined (`Rule.needsWitness`), applies at every configuration its left side matches or at
none, by one fact the values do not decide: some values satisfy the conditions (`Rule.Witnessed`),
or the theory refutes them (`Rule.Refuted`). That fact, `Rule.CondDecided`, is a conjunct of
`OpenDecided`, which `FnHyp` holds and the statements take. The text may hold it or not: it is owed,
and open until a witness or a refutation is given. A function's clause of that shape
(`Clause.needsWitness`) owes the same fact, `Clause.CondDecided`: some values satisfy its conditions
and at them its `requires` has no result but `true` (`Clause.Witnessed`), or the theory refutes them
(`Clause.Refuted`). -/

/-- The rules whose `CondDecided` is owed (`Rule.needsWitness`), by position among the definition's
rules, each with its open condition variables of an unconfined sort. -/
def owedCondDecided (c : Semantics) : List (Nat × List Nat) :=
  c.rules.zipIdx.filterMap fun (r, i) =>
    if r.needsWitness c then
      some (i, r.openCondVars.filter fun j => !(r.vars[j]?.map c.confined).getD false)
    else none

/-- The clauses whose `CondDecided` is owed (`Clause.needsWitness`), by the position of their function
among the definition's and their own among its clauses, each with its open condition variables of
an unconfined sort. -/
def owedClauseCondDecided (c : Semantics) : List (Nat × Nat × List Nat) :=
  c.fns.zipIdx.flatMap fun (f, i) => f.clauses.zipIdx.filterMap fun (cl, j) =>
    if cl.needsWitness c then
      some (i, j, cl.openCondVars.filter fun k => !(cl.vars[k]?.map c.confined).getD false)
    else none

/-! ## Clauses holding existential variables

A clause with existential variables (`Clause.exs`) states its function's value at a match as the
union of its instances: the right side at every value of those variables at which the right-side
predicate holds. That is one result where the instances are decided (the predicate has a truth
value at each) and those that hold give one result; the text does not state that they are. So the
fact is owed of each such clause, as its match obligation (`MatchIndependent`, named by
`Semantics.matchObligationsL`): no list beside that one. -/

/-- The clauses holding existential variables (`Clause.exs`), by the position of their function
among the definition's and their own among its clauses, each with those variables and whether
`Semantics.matchObligationsL` names the clause. -/
def owedExsClauses (c : Semantics) : List (Nat × Nat × List Nat × Bool) :=
  c.fns.zipIdx.flatMap fun (f, i) => f.clauses.zipIdx.filterMap fun (cl, j) =>
    if cl.exs.isEmpty then none else some (i, j, cl.exs, c.matchObligationsL.contains (f.label, j))

/-- The account's line for one clause of `owedExsClauses`: its function's name through `decode`,
its position, label and source line, its existential variables with their sorts, and a warning
where `matchObligationsL` does not name it, so that no statement takes its fact. -/
def owedExsLine (d : Definition) (decode : String → String) (x : Nat × Nat × List Nat × Bool) : String :=
  let f := d.sem.fns[x.1]?
  let fp := d.pres.fns[x.1]?
  let cp := fp.bind (·.clauses[x.2.1]?)
  let fname := match f with | some f => decode (d.sem.symName f.label) | none => "?"
  let lbl := match cp.bind (·.label) with | some l => s!" (`{l}`)" | none => ""
  let src := ((cp.bind (·.src)).getD ((fp.bind (·.src)).getD d.pres.source)).splitOn "/" |>.getLast!
  let ln := (cp.map (·.info.loc.l1)).getD 0
  let names := (cp.map (·.names)).getD []
  let sorts := ((f.bind (·.clauses[x.2.1]?)).map (·.vars)).getD []
  let vs := x.2.2.1.map fun k => s!"Var{names.getD k ""}:{d.sem.sortName (sorts.getD k 0)}"
  let warn := if x.2.2.2 then "" else "; NOT named by matchObligationsL: no statement takes this fact"
  s!"      function {fname}, clause {x.2.1}{lbl} at {src}:{ln}: MatchIndependent open, existential {", ".intercalate vs}{warn}"

/-- The account's lines for `owedExsClauses`, none where no clause holds an existential variable:
a heading with the fact owed of each clause, a line for each clause (`owedExsLine`), and the
statements that are stated only under these facts. -/
def owedExsText (d : Definition) (decode : String → String) : List String :=
  let ow := owedExsClauses d.sem
  if ow.isEmpty then [] else
  s!"clauses holding existential variables, each a match obligation (the package's match_named, Semantics.matchObligationsL; not a condition of wf: owed of each is MatchIndependent, that its instances are decided and give one result at each match where it decides): {ow.length}" ::
    (ow.map (owedExsLine d decode) ++
      ["sound_hyp and complete_hyp (the package's sound_defn and complete_defn) are stated of this text only under these facts as hypotheses, each named with its function and clause (FnHyp's fourth conjunct; match_named of FnObligations)"])

end KCore.Parse
