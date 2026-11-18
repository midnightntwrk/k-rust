/-
  KCore. `emit`: the KORE text of a definition (KCORE-SPEC.md §7). Reviewed layer.
  - Every name it writes is a number's name, read off the registry or the definition's name
    tables (`Semantics.symName`, `sortName`); a sort predicate is written under the name of its
    number (`predOf`), so the text's `isX` is the function `Step` reads by construction.
  - The builtin part (`libBlocks`): the kernel text and each imported module's text (Builtins.lean),
    then the axioms kompile generates for the library's sorts, constructors, subsorts and total
    symbols, written from the signature by the same generators as the user's.
  - KItem's fixed constructors are the library's KItem constructors and `#KConfigValue` (when the
    text declares it: krust's text does, K 7.1.337's does not), placed as
    one block after the first `kconfigPos` user KItem constructors (`#systemResult` of K-IO comes
    first); their distinctness from each user KItem constructor is written accordingly.
  - A generated constructor (a freezer) has no location and no source.
  - A rule's or an equation's priority is written `owise{}()` (200) or `priority{}("n")`
    (`RulePres.prioAttr`, `ClausePres.prioAttr`). An `[owise]` equation's premise negates the
    equations of a smaller priority, as kompile writes it; an equation with `priority{}("n")` has
    its premise only. A symbol-overload axiom read as a clause (`ClausePres.overload`) is written
    with its `symbol-overload{}(f(), g())` attribute alone, which gives its priority 0.
  - The selector-inverse lemma's attribute is `simplification{}("")` or `simplification{}()`
    (`Presentation.simpArg`).
-/
import KcoreSpec.DefinitionWf
import KcoreSpec.Prelude
import KcoreSpec.Builtins
import KcoreSpec.Kore.Build

set_option autoImplicit false

namespace KCore

open KoreAML (srt R evar ev ap injP kseq1 attr attrStr locAttr srcAttr uidAttr kywdAttr axiomR axiom0
  symbolDecl numbered vars existsAll functionalAx subsortAx argsConj anyOf equationAx varList varAt
  projLabel asK)

/-- The name of a sort as a KORE sort. -/
def srtOf (c : Semantics) (s : Srt) : Kore.KSort := srt (c.sortName s)

def toK (c : Semantics) (k : CtorSig) : KoreAML.CtorSig := ⟨c.symName k.name, k.args.map c.sortName, c.sortName k.result⟩

def Gen.toK (c : Semantics) : Gen → KoreAML.Gen
  | .ctor k => .ctor (KCore.toK c k)
  | .inj a => .inj (c.sortName a)

/-- The definition holds `#KConfigValue` (its library is `kconfigModule`'s, `libOf`). -/
def hasKconfig (c : Semantics) : Bool := c.lib.ctors.any (·.name == kconfigValue)

/-- `#KConfigValue` when the definition holds it. -/
def kconfigCtors (c : Semantics) : List CtorSig := if hasKconfig c then [kconfigCtor] else []

/-- KItem's fixed constructors: the library's, then `#KConfigValue` when the definition holds it. -/
def fixedKItemCtors (c : Semantics) : List CtorSig :=
  c.lib.kitemCtors.filter (·.name != kconfigValue) ++ kconfigCtors c

/-- The user's constructors: the core's after the cells' (`Presentation.cellCtors`, which `emit`
writes from the cell tree). -/
def userCtors (c : Semantics) (p : Presentation) : List CtorSig := c.ctors.drop p.cellCtors.length

/-- The user's sorts: the core's after the cell sorts. -/
def userSortsOf (c : Semantics) (p : Presentation) : List Srt := c.userSorts.drop p.cellSorts.length

/-- The user's declared subsorts: the core's after the cells' `XCell < XCellOpt`. -/
def userSubsortsOf (c : Semantics) (p : Presentation) : List (Srt × Srt) :=
  c.userSubsorts.drop p.cellSubsorts.length

/-- KItem's constructors in kompile's order: the user's, with the fixed ones after the first
`kconfigPos` of them. -/
def kitemCtors (c : Semantics) (p : Presentation) : List CtorSig :=
  let us := (userCtors c p).filter (·.result == Srt.kitem)
  us.take p.kconfigPos ++ fixedKItemCtors c ++ us.drop p.kconfigPos

/-- The generators of a sort in kompile's order (`Semantics.gens`, with KItem's constructors as
above). -/
def gensInOrder (c : Semantics) (p : Presentation) (N : Srt) : List Gen :=
  -- kompile orders the injections by their source sort's name (`gens` orders them by number)
  let injs := (sortBy c.sortName ((c.subsorts.filter (·.2 == N)).map (·.1))).map Gen.inj
  if N == Srt.kitem then (kitemCtors c p).map .ctor ++ injs
  else (c.ctorSigs.filter (·.result == N)).map .ctor ++ injs

def noJunkAx (c : Semantics) (p : Presentation) (N : Srt) : List Kore.Sentence :=
  match gensInOrder c p N with
  | [] => []
  | gs => [axiom0 (.or (srtOf c N) (KoreAML.noJunkDisjuncts (c.sortName N) [] (gs.map (Gen.toK c)))) [attr "constructor"]]

/-- The distinctness of each user KItem constructor from each fixed one, the earlier first. -/
def kconfigDistinct (c : Semantics) (p : Presentation) : List Kore.Sentence :=
  let us := (userCtors c p).filter (·.result == Srt.kitem)
  (us.take p.kconfigPos).flatMap (fun k => (fixedKItemCtors c).map fun f => KoreAML.distinctnessAx (toK c k) (toK c f)) ++
  (fixedKItemCtors c).flatMap (fun f => (us.drop p.kconfigPos).map fun k => KoreAML.distinctnessAx (toK c f) (toK c k))

/-- `\equals{SortBool{},S}(req, \dv{SortBool{}}("true"))`, or `\top{S}()` without a `requires`. -/
def reqPat (S : Kore.KSort) : Option Kore.Pattern → Kore.Pattern
  | none => .top S
  | some r => .equals (srt "Bool") S r (.dv (srt "Bool") "true")

def premise (args : List String) (req : Option Kore.Pattern) (pats : List Kore.Pattern) : Kore.Pattern :=
  .and R [reqPat R req, argsConj 0 (args.zip pats)]

/-- The sort X of an own symbol named `ite{X}` (`Parse.iteName`), which K writes `Lblite{SortX{}}`.
A name `Lblite{…}` holding a comma has none: it is an instance at several sorts of a sort-parametric
symbol the text names `Lblite` (`Parse.instName`), and `ite` takes one sort. -/
def iteSort? (n : String) : Option String :=
  match n.toList with
  | 'L' :: 'b' :: 'l' :: 'i' :: 't' :: 'e' :: '{' :: rest =>
    if rest.contains ',' then none else some (String.ofList rest.dropLast)
  | _ => none

mutual
  def Term.kore (c : Semantics) (vs : List KoreAML.Var) : Term → Kore.Pattern
    | .var i => varAt vs i
    | .app f ts => match iteSort? (c.symName f) with
      | some X => .app ⟨⟨"Lblite"⟩⟩ [srt X] (Term.koreList c vs ts)
      | none => .app ⟨⟨c.symName f⟩⟩ [] (Term.koreList c vs ts)
    | .inj a b t => injP (c.sortName a) (c.sortName b) (Term.kore c vs t)
    | .as t i => .and (srt (vs.getD i default).sort) [Term.kore c vs t, varAt vs i]
    | .dv s lit => .dv (srtOf c s) lit.text
    termination_by structural t => t
  def Term.koreList (c : Semantics) (vs : List KoreAML.Var) : List Term → List Kore.Pattern
    | [] => []
    | t :: ts => Term.kore c vs t :: Term.koreList c vs ts
    termination_by structural ts => ts
end

/-- The variable a binder of a condition binds at the index i: `V<i>` of the sort s. -/
def Cond.binder (c : Semantics) (i : Nat) (s : Srt) : KoreAML.Var := ⟨"V" ++ toString i, c.sortName s⟩

/-- A condition as a predicate at the sort S, `vs` the variables in scope. -/
def Cond.kore (c : Semantics) (vs : List KoreAML.Var) (S : Kore.KSort) : Cond → Kore.Pattern
  | .top => .top S
  | .bot => .bottom S
  | .not p => .not S (Cond.kore c vs S p)
  | .and p q => .and S [Cond.kore c vs S p, Cond.kore c vs S q]
  | .or p q => .or S [Cond.kore c vs S p, Cond.kore c vs S q]
  | .implies p q => .implies S (Cond.kore c vs S p) (Cond.kore c vs S q)
  | .ceil s t => .ceil (srtOf c s) S (Term.kore c vs t)
  | .equals s t u => .equals (srtOf c s) S (Term.kore c vs t) (Term.kore c vs u)
  | .mem s t u => .in (srtOf c s) S (Term.kore c vs t) (Term.kore c vs u)
  | .exMatch ys s p t body =>
      let bs := ((List.range ys.length).zip ys).map fun (j, y) => Cond.binder c (vs.length + j) y
      KoreAML.existsAll S (bs.map KoreAML.Var.kore)
        (.and S [.in (srtOf c s) S (Term.kore c vs t) (Term.kore c (vs ++ bs) p),
                 Cond.kore c (vs ++ bs) S body])
  | .ex s body =>
      let b := Cond.binder c vs.length s
      .exist S b.kore (Cond.kore c (vs ++ [b]) S body)
  | .all s body =>
      let b := Cond.binder c vs.length s
      .forall S b.kore (Cond.kore c (vs ++ [b]) S body)

/-- The conjuncts a condition adds to a sentence: none for `\top`. -/
def Cond.conj (c : Semantics) (vs : List KoreAML.Var) (S : Kore.KSort) (p : Cond) : List Kore.Pattern :=
  if p.isTop then [] else [Cond.kore c vs S p]

inductive Prod where
  | ctor (k : CtorSig) (kp : CtorPres)
  | fn (f : Fn) (fp : FnPres)
  | subsort (sub sup : Srt)

def interleave : List ProdKind → List (CtorSig × CtorPres) → List (Fn × FnPres) →
    List (Srt × Srt) → List Prod
  | .ctor :: ks, (k, kp) :: ctors, fns, subs => .ctor k kp :: interleave ks ctors fns subs
  | .fn :: ks, ctors, (f, fp) :: fns, subs => .fn f fp :: interleave ks ctors fns subs
  | .subsort :: ks, ctors, fns, (a, b) :: subs => .subsort a b :: interleave ks ctors fns subs
  | _ :: ks, ctors, fns, subs => interleave ks ctors fns subs
  | [], ctors, fns, subs =>
    ctors.map (fun (k, kp) => .ctor k kp) ++ fns.map (fun (f, fp) => .fn f fp) ++
    subs.map fun (a, b) => .subsort a b

def prods (c : Semantics) (p : Presentation) : List Prod :=
  interleave p.order (withPres (userCtors c p) p.ctors)
    ((withPres c.fns p.fns).filter fun (f, _) => !p.generatedFns.contains f.label) (userSubsortsOf c p)

/-- kompile writes a sentence's attributes sorted by name. -/
def sortAttrs (as : List Kore.AppPattern) : List Kore.AppPattern := sortBy (·.head.ident.name) as

def metaAttrs (p : Presentation) (m : Meta) (label : Option String) (src : Option String := none) :
    List Kore.AppPattern :=
  sortAttrs ([uidAttr m.uid, locAttr m.loc, srcAttr (src.getD p.source)] ++
    (label.map fun l => [attrStr "label" l]).getD [])

def kywdAttrs : Option String → List Kore.AppPattern
  | some k => [kywdAttr k]
  | none => []

def prodSymbol (c : Semantics) (p : Presentation) : Prod → List Kore.Sentence
  | .ctor k kp => [symbolDecl (c.symName k.name) (k.args.map c.sortName) (c.sortName k.result)
      ([attr "constructor", attr "functional", attr "injective"] ++
       (match kp.loc with | some l => [locAttr l, srcAttr (kp.src.getD p.source)] | none => []) ++
       kywdAttrs kp.kywd)]
  | .fn f fp => match fp.hook with
    | none => [symbolDecl (c.symName f.label) (f.args.map c.sortName) (c.sortName f.result)
      ([attr "function"] ++ (if f.total then [attr "functional"] else []) ++
       [locAttr fp.loc, srcAttr (fp.src.getD p.source)] ++ kywdAttrs fp.kywd ++
       (if f.total then [attr "total"] else []))]
    -- a function declared `hooked-symbol`: the same attributes with its hook after `functional`
    | some h => [.hookedSymbol
      { symbol := { ident := ⟨⟨c.symName f.label⟩⟩, sortVars := [] }
        sorts := f.args.map fun s => KoreAML.srt (c.sortName s)
        sort := KoreAML.srt (c.sortName f.result)
        attributes := [attr "function"] ++ (if f.total then [attr "functional"] else []) ++
          [attrStr "hook" h, locAttr fp.loc, srcAttr (fp.src.getD p.source)] ++ kywdAttrs fp.kywd ++
          (if f.total then [attr "total"] else []) }]
  | .subsort _ _ => []

/-- The user's parameter symbols' declarations: hooked function symbols, with no axiom (the
imported modules' are in their text). -/
def paramDecls (c : Semantics) (p : Presentation) : List Kore.Sentence :=
  ((withPres (c.params.filter fun k => decide (nRegSyms ≤ k.sig.name)) p.params).filter
    fun (_, pp) => pp.hook != "" && pp.hook != "KEQUAL.ite").map fun (k, pp) =>
    let hs : Kore.HookedSymbol :=
      { symbol := { ident := ⟨⟨c.symName k.sig.name⟩⟩, sortVars := [] }
        sorts := k.sig.args.map fun s => KoreAML.srt (c.sortName s)
        sort := KoreAML.srt (c.sortName k.sig.result)
        attributes := [attr "function", attrStr "hook" pp.hook] ++
          (match pp.loc with | some l => [locAttr l, srcAttr (pp.src.getD p.source)] | none => []) ++
          kywdAttrs pp.kywd }
    .hookedSymbol hs

/-- Each production's axioms, one block per production: a constructor's no-confusion with the
constructors after it, a subsort's axiom, a total function's `functional` axiom. -/
def prodAxiomBlocks (c : Semantics) : List Prod → List (List Kore.Sentence)
  | [] => []
  | .ctor k _ :: ps =>
    let later := ps.filterMap fun | .ctor k' _ => some (toK c k') | _ => none
    KoreAML.ctorAxioms (toK c k) later :: prodAxiomBlocks c ps
  | .subsort a b :: ps => [subsortAx (c.sortName a) (c.sortName b)] :: prodAxiomBlocks c ps
  | .fn f _ :: ps => (if f.total then [functionalAx (c.symName f.label) (f.args.map c.sortName) (c.sortName f.result)] else []) ::
      prodAxiomBlocks c ps

/-- A clause's premise with its predicate, `prem ∧ pre` at the sort variable `R`, `vs` the clause's
variables: the premise `prem` alone where the predicate is `\top`. -/
def withPre (c : Semantics) (vs : List KoreAML.Var) (cl : Clause) (prem : Kore.Pattern) : Kore.Pattern :=
  if cl.pre.isTop then prem else .and R [prem, Cond.kore c vs R cl.pre]

/-- The premise of a clause whose predicate is `\top` is the premise without a predicate. -/
theorem withPre_top {c : Semantics} {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern}
    (h : cl.pre = .top) : withPre c vs cl prem = prem := by
  unfold withPre; rw [h]; rfl

/-- `withPre_top` from `Cond.isTop`. -/
theorem withPre_isTop {c : Semantics} {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern}
    (h : cl.pre.isTop = true) : withPre c vs cl prem = prem := if_pos h

/-- `∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre`: the arguments a clause applies to, the variables of its
patterns and conditions bound (a variable outside them does not bear on whether it applies);
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄` where the clause's predicate is `\top` (`withPre`). -/
def exclusion (c : Semantics) (f : Fn) (cl : Clause) (cp : ClausePres) : Kore.Pattern :=
  let ren := varList (cl.vars.map c.sortName) cp.exclNames
  let bound := (List.range cl.vars.length).filter cl.leftVars.contains |>.filterMap (ren[·]?)
  existsAll R (bound.map KoreAML.Var.kore)
    (withPre c ren cl (premise (f.args.map c.sortName) (cl.req.map (Term.kore c ren)) (Term.koreList c ren cl.pats)))

/-- An equation's priority as kompile writes it: `priority{}("n")` when the presentation says so,
otherwise `owise{}()` for 200 and nothing for 50. -/
def clausePrioAttrs (cl : Clause) (cp : ClausePres) : List Kore.AppPattern :=
  if cp.prioAttr then [attrStr "priority" (toString cl.prio)]
  else if cl.prio == 200 then [attr "owise"] else []

/-- `symbol-overload{}(f(), g())`. -/
def overloadAttr (f g : String) : Kore.AppPattern :=
  ⟨⟨⟨"symbol-overload"⟩⟩, [], [ap f [], ap g []]⟩

/-- A clause's equation's attributes: for a symbol-overload axiom (`ClausePres.overload`) its
`symbol-overload{}(f(), g())` alone, the text's only attribute of it (no id, place or priority:
the attribute gives the clause priority 0 and `aside`); otherwise its id, place, label and
priority. -/
def clauseAttrs (c : Semantics) (p : Presentation) (f : Fn) (cl : Clause) (cp : ClausePres) :
    List Kore.AppPattern :=
  match cp.overload with
  | some g => [overloadAttr (c.symName f.label) g]
  | none => match clausePrioAttrs cl cp with
    | [] => metaAttrs p cp.info cp.label cp.src
    | as => sortAttrs (metaAttrs p cp.info cp.label cp.src ++ as)

/-- An equation written `owise{}()`: of priority 200, with no `priority{}` attribute. -/
def writtenOwise (cl : Clause) (cp : ClausePres) : Bool := cl.prio == 200 && !cp.prioAttr

/-- A clause's equation, `premise → f(p̄) = rhs ∧ ens`, the premise `⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre`
(`withPre`: `⌈req = true⌉ ∧ X̄ ∈ p̄` where the clause's predicate is `\top`, `clauseAx_top`), the
predicate its competitors' `exclusion` carries. The premise of an `[owise]` equation negates
every equation of a smaller priority that is not `aside` (`exclusion`),
`¬ ⋁ competitors ∧ (⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre)`. -/
def clauseAx (c : Semantics) (p : Presentation) (f : Fn) (fp : FnPres) (cl : Clause) (cp : ClausePres) :
    Kore.Sentence :=
  let vs := varList (cl.vars.map c.sortName) cp.names
  let prem := withPre c vs cl
    (premise (f.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats))
  let comps := ((withPres f.clauses fp.clauses).filter fun x => !x.1.aside && x.1.prio < cl.prio).map fun (cl', cp') =>
    exclusion c f cl' cp'
  equationAx (c.symName f.label) (f.args.map c.sortName) (c.sortName f.result)
    (if writtenOwise cl cp then .and R [.not R (anyOf comps), prem] else prem)
    (Term.kore c vs cl.rhs) (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c vs))) (clauseAttrs c p f cl cp)

/-- The equation of a clause whose predicate is `\top` has the premise without a predicate,
`⌈req = true⌉ ∧ X̄ ∈ p̄` (under `¬ ⋁ competitors` for an `[owise]` equation): the text `clauseAx`
had before a clause's premise carried its predicate. -/
theorem clauseAx_top {c : Semantics} {p : Presentation} {f : Fn} {fp : FnPres} {cl : Clause} {cp : ClausePres}
    (h : cl.pre = .top) :
    clauseAx c p f fp cl cp =
      (let vs := varList (cl.vars.map c.sortName) cp.names
       let prem := premise (f.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats)
       let comps := ((withPres f.clauses fp.clauses).filter fun x => !x.1.aside && x.1.prio < cl.prio).map fun (cl', cp') =>
         exclusion c f cl' cp'
       equationAx (c.symName f.label) (f.args.map c.sortName) (c.sortName f.result)
         (if writtenOwise cl cp then .and R [.not R (anyOf comps), prem] else prem)
         (Term.kore c vs cl.rhs) (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c vs))) (clauseAttrs c p f cl cp)) := by
  unfold clauseAx; simp only [withPre_top h]

/-- A rule's condition `q` (its `requires` or its `ensures`) with a predicate of the rule, at the
sort `C`, `vs` the rule's variables: `\and{C}(q, p)`, and `q` alone where the predicate is `\top`. -/
def rulePredPat (c : Semantics) (vs : List KoreAML.Var) (C : Kore.KSort) (p : Cond) (q : Kore.Pattern) :
    Kore.Pattern :=
  if p.isTop then q else .and C [q, Cond.kore c vs C p]

/-- `rulePredPat` at the predicate `\top` is the condition alone. -/
theorem rulePredPat_top {c : Semantics} {vs : List KoreAML.Var} {C : Kore.KSort} {p : Cond}
    {q : Kore.Pattern} (h : p = .top) : rulePredPat c vs C p q = q := by
  subst h; rfl

/-- `\rewrites{C}(\and{C}(lhs, \and{C}(req, pre)), \exists{C}(?ē, \and{C}(rhs, \and{C}(ens, post))))`,
`req` and `ens` being `\top{C}()` without a `requires` or an `ensures`, `pre` (the predicate of the
left side) beside the `requires` and `post` (the predicate of the right side, under the binders of
the existential variables) beside the `ensures`, each left out where it is `\top` (`rulePredPat`); the
existential variables bound in the order of `exs` (the first outermost) under the presentation's
names; with no existential variable, the right side's `\and{C}` alone. -/
def rulePattern (c : Semantics) (vs : List KoreAML.Var) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  .rewrites C (.and C [Term.kore c vs r.lhs, rulePredPat c vs C r.pre (reqPat C (r.req.map (Term.kore c vs)))])
    ((r.exs.filterMap (vs[·]?)).foldr (fun v p => .exist C v.kore p)
      (.and C [Term.kore c vs r.rhs, rulePredPat c vs C r.post (reqPat C (r.ens.map (Term.kore c vs)))]))

/-- A rule whose predicates `pre` and `post` are `\top` is emitted as
`\rewrites{C}(\and{C}(lhs, req), \exists{C}(?ē, \and{C}(rhs, ens)))`: the predicates add nothing to
its text. -/
theorem rulePattern_top (c : Semantics) (vs : List KoreAML.Var) (r : Rule) (hpre : r.pre = .top)
    (hpost : r.post = .top) :
    rulePattern c vs r =
      .rewrites (srtOf c topCellSort)
        (.and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs))])
        ((r.exs.filterMap (vs[·]?)).foldr (fun v p => .exist (srtOf c topCellSort) v.kore p)
          (.and (srtOf c topCellSort) [Term.kore c vs r.rhs, reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs))])) := by
  simp only [rulePattern, rulePredPat_top hpre, rulePredPat_top hpost]

/-- A rule with no existential variable is emitted as `\rewrites{C}(\and{C}(lhs, \and{C}(req, pre)),
\and{C}(rhs, \and{C}(ens, post)))`, each predicate left out where it is `\top`. -/
theorem rulePattern_noExs (c : Semantics) (vs : List KoreAML.Var) (r : Rule) (h : r.exs = []) :
    rulePattern c vs r =
      .rewrites (srtOf c topCellSort)
        (.and (srtOf c topCellSort) [Term.kore c vs r.lhs,
          rulePredPat c vs (srtOf c topCellSort) r.pre (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs)))])
        (.and (srtOf c topCellSort) [Term.kore c vs r.rhs,
          rulePredPat c vs (srtOf c topCellSort) r.post (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs)))]) := by
  simp [rulePattern, h]

def ruleAttrs (p : Presentation) (rp : RulePres) : List Kore.AppPattern :=
  sortAttrs (metaAttrs p rp.info rp.label ++ rp.attrs.map attr)

/-- The rule's priority as kompile writes it: nothing for 50, `owise{}()` for 200, or
`priority{}("n")` when the presentation says so. -/
def prioAttrs (r : Rule) (rp : RulePres) : List Kore.AppPattern :=
  if rp.prioAttr then [attrStr "priority" (toString r.prio)]
  else if r.prio == 200 then [attr "owise"] else []

def ruleSentences (c : Semantics) (p : Presentation) : List Kore.Sentence :=
  (withPres c.rules p.rules).map fun (r, rp) =>
    axiom0 (rulePattern c (varList (r.vars.map c.sortName) rp.names) r)
      (sortAttrs (metaAttrs p rp.info rp.label rp.src ++ rp.attrs.map attr ++ prioAttrs r rp ++ rp.argAttrs.map fun (a, v) => attrStr a v))

/-- kompile writes the selector-inverse lemma's `simplification` attribute as `simplification{}()`,
or as `simplification{}("")` when some sentence gives the attribute an argument (Builtins.lean).
The translation reads the attribute's name only (D-attributes). -/
def simpAttr (arg : Bool) : Kore.AppPattern :=
  if arg then attrStr "simplification" "" else attr "simplification"

/-- The selector domain of X's projection and its inverse, `h` the id of its equation. -/
def projDomainAxs (arg : Bool) (X h : String) : List Kore.Sentence :=
  let vk := ev "VarK" (srt X)
  let si := ev "SelectorInput" (srt "K")
  let proj := ap (projLabel X) [si]
  [axiomR (.implies R (.top R) (.equals R R (.ceil (srt X) R proj)
     (.exist R (evar "VarK" (srt X)) (.equals (srt "K") R si (asK X vk)))))
     [uidAttr (h ++ ".selector-domain")],
   axiomR (.implies R (.ceil (srt X) R proj)
     (.equals (srt "K") R (asK X proj) (.and (srt "K") [si, .top (srt "K")])))
     [uidAttr (h ++ ".selector-inverse"), simpAttr arg]]

/-- `projectX(kseq(inj(K), dotk)) = K`, its selector domain and its inverse. -/
def projEquations (arg : Bool) (X h : String) : List Kore.Sentence :=
  let vk := ev "VarK" (srt X)
  equationAx (projLabel X) ["K"] X (KoreAML.premise ["K"] [asK X vk]) vk (.top (srt X)) [uidAttr h] ::
    projDomainAxs arg X h

/-- The id `h` of a projection's equation when the clause is read from its selector-domain axiom
(`Parse.ReadingNote.projectionDomainAsClause`: priority 200, an `ensures`, the id `h.selector-domain`). -/
def domainClauseId? (cl : Clause) (cp : ClausePres) : Option String :=
  let u := cp.info.uid.toList
  let sfx := ".selector-domain".toList
  if cl.prio == 200 && cl.ens.isSome && sfx.length ≤ u.length && u.drop (u.length - sfx.length) == sfx then
    some (String.ofList (u.take (u.length - sfx.length)))
  else none

/-- A function's equations; a clause read from a projection's selector-domain axiom is written as
that axiom, with the projection's selector-inverse lemma. -/
def fnEquations (c : Semantics) (p : Presentation) (f : Fn) (fp : FnPres) : List Kore.Sentence :=
  (withPres f.clauses fp.clauses).flatMap fun (cl, cp) => match domainClauseId? cl cp with
    | some h => projDomainAxs p.simpArg (c.sortName f.result) h
    | none => [clauseAx c p f fp cl cp]

/-! ## The configuration's text -/

/-- The ids of a sort's `isX`/`projectX` equations: a user sort's by position, a cell sort's by
name. -/
def uidsOf (c : Semantics) (p : Presentation) (X : Srt) : SortUids :=
  match (withPres (userSortsOf c p) p.sortUids).lookup X with
  | some u => u
  | none => (p.cellUids.lookup X).getD default

namespace Cell

mutual
  /-- A cell and its descendants (not the cell collections among them, which are no cells). -/
  def all : Cell → List Cell
    | .leaf n s i => [.leaf n s i]
    | .node n cs i => .node n cs i :: allList cs
    | .coll _ => []
    termination_by structural x => x
  def allList : List Cell → List Cell
    | [] => []
    | x :: xs => all x ++ allList xs
    termination_by structural xs => xs
end

/-- The cell holds a configuration variable (it is, or contains, the leaf holding `$PGM`
(`pgmCell`), or a leaf whose initial value reads `Init`, as `<env> $ENV:Map </env>` does), so its
initializer reads `Init`. -/
def readsInit (p : Presentation) (x : Cell) : Bool := x.all.any fun
  | .leaf n _ _ => p.pgmCell == some n || ((p.cellValues.lookup n).map fun t => !(varOccs t).isEmpty).getD false
  | _ => false

/-- `initXCell`: not a function of the semantics, named from the cell's sort. -/
def initLabel (c : Semantics) (x : Cell) : String := "Lblinit" ++ c.sortName x.sort

/-- `initX(Init)` or `initX()`; for a cell collection, its unit `.XCellSet()` (no cell of a
multiplicity `*` cell at the start). -/
def initCall (c : Semantics) (p : Presentation) (x : Cell) : Kore.Pattern :=
  match x with
  | .coll s => ap (c.symName (((c.colls.find? (·.sort == s)).map (·.unit)).getD default)) []
  | _ => ap (x.initLabel c) (if x.readsInit p then [ev "VarInit" (srt "Map")] else [])

end Cell

mutual
  /-- A term of constructors and total interpreted symbols only: its value is always defined. -/
  def Term.total (c : Semantics) : Term → Bool
    | .var _ => false
    | .app f ts => ((lookupSig c.ctorSigs f).isSome ||
        (hookSigs.any (·.name == f) && !partialHooks.contains f && f != setConcat)) && Term.totalList c ts
    | .inj _ _ t => Term.total c t
    | .as _ _ => false
    | .dv _ _ => true
    termination_by structural t => t
  def Term.totalList (c : Semantics) : List Term → Bool
    | [] => true
    | t :: ts => Term.total c t && Term.totalList c ts
    termination_by structural ts => ts
end

/-- kompile declares a cell's initializer `functional` and `total`, and states its functional
axiom, when the cell's initial value is always defined: no `$PGM` below it, and a leaf's value a
total term (the counter's is 0). -/
def initTotal (c : Semantics) (p : Presentation) (x : Cell) : Bool :=
  !x.readsInit p && x.all.all fun
    | .leaf "generatedCounter" _ _ => true
    | .leaf n _ _ => ((p.cellValues.lookup n).map (Term.total c)).getD false
    | _ => true

/-- The generated cells (the top cell and the counter) carry no location; the user's carry the
configuration's. -/
def isGenerated (x : Cell) : Bool := x.name == "generatedTop" || x.name == "generatedCounter"

def cellSymbols (c : Semantics) (p : Presentation) (x : Cell) : List Kore.Sentence :=
  -- with several top-level cells, `<generatedTop>` stands for the user's configuration and carries
  -- its location
  let gen := isGenerated x && !(x.name == "generatedTop" && !Cell.counterOpt p.config)
  let ctorAttrs := [attr "constructor", attr "functional", attr "injective"]
  let args := match x with
    | .leaf _ s _ => [s]
    | .node _ cs _ => cs.map Cell.sort
    | .coll _ => []
  [symbolDecl (c.symName x.label) (args.map c.sortName) (c.sortName x.sort)
    ([attr "cell"] ++ ctorAttrs ++ (if gen then [] else [locAttr p.configLoc, srcAttr p.configSource]))] ++
  (match x with
    | .node _ cs i =>
      let cs := if x.name == "generatedTop" && !Cell.counterOpt p.config then cs.dropLast else cs
      (Cell.fragCtor cs i).toList.map fun k =>
        symbolDecl (c.symName k.name) (k.args.map c.sortName) (c.sortName k.result) ctorAttrs
    | _ => []) ++
  (if x.name == "generatedCounter" && !Cell.counterOpt p.config then []
   else x.noCtor.toList.map fun k => symbolDecl (c.symName k.name) [] (c.sortName k.result) ctorAttrs) ++
  [if x.readsInit p then symbolDecl (x.initLabel c) ["Map"] (c.sortName x.sort) [attr "function"]
   else if initTotal c p x then symbolDecl (x.initLabel c) [] (c.sortName x.sort) [attr "function", attr "functional", attr "total"]
   else symbolDecl (x.initLabel c) [] (c.sortName x.sort) [attr "function"]] ++
  (if p.topCell.name == x.name then
    [symbolDecl "LblgetGeneratedCounterCell" ["GeneratedTopCell"] "GeneratedCounterCell" [attr "function"]]
   else [])

/-- The initializer's equation: a leaf's initial value (`$PGM` projected to `pgmSort` for the leaf
`pgmCell`, as a K where its content is K; 0 for the counter; the presentation's value otherwise),
a node's children's initializers. -/
def initAx (c : Semantics) (p : Presentation) (x : Cell) : Kore.Sentence :=
  let uid := uidAttr ((p.cellInits.lookup x.name).getD "")
  let body : Kore.Pattern := match x with
    | .leaf n s _ =>
      if p.pgmCell == some n then
        let S := c.pgmSort
        let pgm := ap "LblMap'Coln'lookup" [ev "VarInit" (srt "Map"),
          injP "KConfigVar" "KItem" (.dv (srt "KConfigVar") "$PGM")]
        -- the value of `$PGM` as a K term: krust's text unboxes `#KConfigValue`, K 7.1.337's (which
        -- has none) wraps it in `kseq`
        let v := ap (projLabel (c.sortName S)) [if hasKconfig c then ap "Lbl'Hash'unboxKConfigValue" [pgm] else kseq1 pgm]
        ap (c.symName x.label) [if s == S || S == Srt.k then v else if S == Srt.kitem then kseq1 v else asK (c.sortName S) v]
      else if n == "generatedCounter" then ap (c.symName x.label) [.dv (srt "Int") "0"]
      else ap (c.symName x.label)
        [((p.cellValues.lookup n).map (Term.kore c [⟨"Init", "Map"⟩])).getD (.top (srt "K"))]
    | .node _ cs _ => ap (c.symName x.label) (cs.map (Cell.initCall c p))
    | .coll _ => .top (srt "K")
  if x.readsInit p then
    equationAx (x.initLabel c) ["Map"] (c.sortName x.sort) (KoreAML.premise ["Map"] [ev "VarInit" (srt "Map")]) body
      (.top (srt (c.sortName x.sort))) [uid]
  else equationAx (x.initLabel c) [] (c.sortName x.sort) (KoreAML.premise [] []) body (.top (srt (c.sortName x.sort))) [uid]

/-- `getGeneratedCounterCell(<generatedTop>(_, Cell)) = Cell`. -/
def counterAx (c : Semantics) (p : Presentation) : Kore.Sentence :=
  let roots := (p.config.zip p.counterVars).map fun (r, n) => ev n (srtOf c r.sort)
  let cell := ev "VarCell" (srt "GeneratedCounterCell")
  equationAx "LblgetGeneratedCounterCell" ["GeneratedTopCell"] "GeneratedCounterCell"
    (KoreAML.premise ["GeneratedTopCell"]
      [ap (c.symName p.topCell.label) (roots ++ [cell])]) cell (.top (srt "GeneratedCounterCell"))
    [uidAttr p.counterUid]

/-- Everything the configuration declares and states, but `isX`/`projectX` and the no-junk
axioms, which `userModule` writes for the cell sorts with the user's sorts. -/
def cellSentences (c : Semantics) (p : Presentation) : List Kore.Sentence :=
  let cells := p.topCell.all
  cells.flatMap (cellSymbols c p) ++
  p.cellCtors.flatMap (fun k => KoreAML.ctorAxioms (toK c k) []) ++
  (cells.filter (initTotal c p)).map (fun x => functionalAx (x.initLabel c) [] (c.sortName x.sort)) ++
  p.cellSubsorts.map (fun (a, b) => subsortAx (c.sortName a) (c.sortName b)) ++
  cells.map (initAx c p) ++ [counterAx c p]

/-! ## The definition -/

/-- The sorts with generated `isX`/`projectX`: the definition's (the cell sorts, then the user's). -/
def helperSorts (c : Semantics) : List Srt := c.userSorts

/-- `isX` and `projectX` declared, `isX` under the name of its number (`predOf`), when X has one. -/
def helperDecls (c : Semantics) (X : Srt) : List Kore.Sentence × Kore.Sentence :=
  ((predOf X).toList.map fun p =>
     symbolDecl (c.symName p) ["K"] "Bool" [attr "function", attr "functional", attr "total"],
   symbolDecl (projLabel (c.sortName X)) ["K"] (c.sortName X) [attr "function"])

/-- The functional axiom of X's predicate, when X has one. -/
def predFunctionalAx (c : Semantics) (X : Srt) : List Kore.Sentence :=
  (predOf X).toList.map fun p => functionalAx (c.symName p) ["K"] "Bool"

/-- `isX(kseq(inj(x), dotk)) = true`, and `isX(K) = false [owise]` (F0's `isEquations`, under the
name of X's predicate; none when X has no predicate). -/
def isEquations (c : Semantics) (X : Srt) (uTrue uFalse : String) : List Kore.Sentence :=
  match predOf X with
  | none => []
  | some p =>
    let n := c.sortName X
    let isL := c.symName p
    let gen := evar "Var'Unds'Gen0" (srt n)
    [equationAx isL ["K"] "Bool" (KoreAML.premise ["K"] [asK n (ev ("Var" ++ n) (srt n))])
       (KoreAML.dv "Bool" "true") (.top (srt "Bool")) [uidAttr uTrue],
     equationAx isL ["K"] "Bool"
       (KoreAML.owisePremise ["K"] [existsAll R [gen] (KoreAML.premise ["K"] [asK n (.var (.evar gen))])]
         [ev "VarK" (srt "K")])
       (KoreAML.dv "Bool" "false") (.top (srt "Bool")) [uidAttr uFalse, attr "owise"]]

/-- `⊤ ∨ ⊥`: the no-junk axiom of a sort with domain values. -/
def topBotAx (c : Semantics) (X : Srt) : Kore.Sentence :=
  axiom0 (.or (srtOf c X) [.top (srtOf c X), .bottom (srtOf c X)]) [attr "constructor"]

/-- The builtin part of the user module, in blocks: the kernel text and each imported module's text,
a sentence per block; then, for the library's sorts, constructors, subsorts and total symbols, the
axioms kompile generates from the signature: a sort's declaration (when its text has none), its
`isX` and `project:X` and their equations, its subsort of KItem, its no-junk axiom (`⊤ ∨ ⊥` with
domain values); each constructor's functional, injectivity and no-confusion axioms (with the later
constructors of its sort, and `#KConfigValue` after them); each subsort's
axiom; each total symbol's functional axiom. -/
def libBlocks (c : Semantics) (p : Presentation) : List (List Kore.Sentence) :=
  let arg := p.simpArg
  let ms := importsOf p.imports
  let us := ms.flatMap (·.uids)
  let cs := c.lib.ctors.filter (·.name != kconfigValue)
  (kernelText arg (hasKconfig c)).map (fun s => [s])
  ++ p.imports.flatMap (fun i => (moduleText arg i).map fun s => [s])
  ++ [(ms.flatMap (·.plainSorts)).map (fun X => Kore.Sentence.sort { sort := ⟨⟨"Sort" ++ c.sortName X⟩⟩, sortVars := [], attributes := [] })]
  ++ us.map (fun (X, u) =>
      (helperDecls c X).1 ++ (if u.proj == "" || p.libProjs.contains X then [] else [(helperDecls c X).2]) ++
      predFunctionalAx c X ++ [subsortAx (c.sortName X) "KItem"] ++
      isEquations c X u.isTrue u.isFalse ++
      (if u.proj == "" || p.libProjs.contains X then [] else projEquations arg (c.sortName X) u.proj) ++
      (if (ms.any (·.dvSorts.contains X)) then [topBotAx c X] else noJunkAx c p X))
  ++ (List.range cs.length).map (fun i =>
      let k := cs.getD i default
      KoreAML.ctorAxioms (toK c k) ((cs.drop (i + 1) ++ kconfigCtors c).map (toK c)))
  ++ [c.lib.subsorts.map fun (a, b) => subsortAx (c.sortName a) (c.sortName b)]
  ++ [(ms.flatMap (·.totals)).map fun k => functionalAx (c.symName k.name) (k.args.map c.sortName) (c.sortName k.result)]

/-- A user sort's declaration attributes: its location and source, when K writes them. -/
def sortLocAttrs (p : Presentation) (X : Srt) : List Kore.AppPattern :=
  match p.sortLocs.find? (·.1 == X) with
  | some (_, l, src) => [locAttr l, srcAttr src]
  | none => []

/-- A user sort's declaration attributes: a token sort's are `hasDomainValues{}()`, its place and
`token{}()` when the user's file declares it (it then has a place), `hasDomainValues{}()` alone when
K infers it from a token production; another sort's are its place. -/
def userSortAttrs (c : Semantics) (p : Presentation) (X : Srt) : List Kore.AppPattern :=
  if c.lib.tokenSorts.contains X then
    sortAttrs ([attr "hasDomainValues"] ++ sortLocAttrs p X ++ (if (p.sortLocs.find? (·.1 == X)).isSome then [attr "token"] else []))
  else sortLocAttrs p X

/-- A user sort's no-junk axiom: `⊤ ∨ ⊥` for a token sort and a sort hooked to a library carrier,
its generators' otherwise. -/
def userNoJunkAx (c : Semantics) (p : Presentation) (X : Srt) : List Kore.Sentence :=
  if c.lib.tokenSorts.contains X || c.lib.carriers.any (·.1 == X) then [topBotAx c X] else noJunkAx c p X

/-- The user module's sentences in blocks, in emit's order: the builtin part (`libBlocks`), and one
block per production, sort, function equation and rule for the parts that grow with the definition. The tie
compares the KORE with these blocks a slice at a time (`KoreAML.Blocks`). -/
def userBlocks (c : Semantics) (p : Presentation) : List (List Kore.Sentence) :=
  let U := helperSorts c
  libBlocks c p
  ++ [U.map (fun X => Kore.Sentence.sort { sort := ⟨⟨"Sort" ++ c.sortName X⟩⟩, sortVars := [], attributes := userSortAttrs c p X })]
  ++ (prods c p).map (prodSymbol c p)
  ++ [paramDecls c p, U.flatMap (fun X => (helperDecls c X).1),
      (U.filter fun X => !p.libProjs.contains X && (uidsOf c p X).proj != "").map (fun X => (helperDecls c X).2)]
  ++ prodAxiomBlocks c (prods c p)
  ++ [U.flatMap (predFunctionalAx c),
      U.map (fun X => subsortAx (c.sortName X) "KItem")]
  ++ (sortBy c.sortName (Srt.kitem :: U)).map (userNoJunkAx c p)
  ++ [kconfigDistinct c p, cellSentences c p]
  ++ ((withPres c.fns p.fns).filter fun (f, _) => !p.generatedFns.contains f.label).flatMap
      (fun (f, fp) => (fnEquations c p f fp).map (fun s => [s]))
  ++ (ruleSentences c p).map (fun s => [s])
  ++ U.map (fun X => let u := (uidsOf c p X).proj
      if p.libProjs.contains X || u == "" then [] else projEquations p.simpArg (c.sortName X) u)
  ++ U.map (fun X => let u := uidsOf c p X; isEquations c X u.isTrue u.isFalse)

def userModule (c : Semantics) (p : Presentation) : Kore.Module :=
  { name := ⟨⟨p.moduleName⟩⟩
    sentences := (userBlocks c p).flatten
    attributes := [locAttr p.moduleLoc, srcAttr p.source] }

def emit (c : Semantics) (p : Presentation) : Kore.Definition :=
  { attributes := [⟨⟨⟨"topCellInitializer"⟩⟩, [], [ap "LblinitGeneratedTopCell" []]⟩, srcAttr p.source]
    modules := preludeModules ++ [userModule c p] }

def Definition.emit (d : Definition) : Kore.Definition := KCore.emit d.sem d.pres

end KCore
