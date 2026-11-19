/-
  KCore. The matching-logic theory of a semantics, built from `Semantics` alone, and the
  statements that the step relation is faithful to it.

  `Γ c` reads the kernel's data and its interpretation of the parameter symbols (`c.hooks`); it
  reads no presentation and no KORE text. It is the union of seven parts, each a definition of its
  own:
  - `ΓSig`: the axioms of the encoding (definedness, the sorts, the arity of every symbol, the
    definedness symbols, next, domain values);
  - `ΓCons`: the constructor sorts' axioms (`consItemsK`, the collection sorts left out);
  - `ΓDomains`: the graphs of the interpreted and parameter symbols, that every value is one
    element, distinctness of values, no junk in each collection sort;
  - `ΓColls`: what each collection sort's unit, element and concatenation are on any elements of
    their sorts (a union of maps, a concatenation of lists, a union of sets);
  - `ΓFns`: each function's equations, one per clause with the clauses of a smaller priority
    negated;
  - `ΓRules`: each rule's axiom, the rules of a smaller priority negated;
  - `ΓFallback`: what the interpretation decides where the text is silent: an interpreted
    symbol's value at its silent points, a function's where every clause fails (its rest).
  `Γstep c` is the step's closure axiom.

  Variables of clauses and rules are named canonically (`V0`, `V1`, …): a name only fixes an
  index of the translation. Every axiom is translated by `trAxiom` with no declarations and no
  aliases: it reads declarations only for the sort of an application at the top of an axiom, and
  aliases only at an alias application; no axiom here has either.

  `StepSound`, `StepComplete` and `HasModel` state what the theory is for; `Hyp` is what they
  assume. They are statements only.
-/
import KcoreSpec.Statements
import KcoreSpec.SubjectReduction

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (R)

/-! ## Canonical variables -/

/-- `V0, V1, …, V(n-1)`. -/
def canonNames (n : Nat) : List String := (List.range n).map fun i => "V" ++ toString i

/-- The variables of a clause or rule of sorts `sorts`, named canonically. -/
def canonVars (c : Semantics) (sorts : List Srt) : List KoreAML.Var :=
  KoreAML.varList (sorts.map c.sortName) (canonNames sorts.length)

/-- A rule's variable names, canonical; nothing else of a rule's presentation is read here. -/
def canonRulePres (r : Rule) : RulePres :=
  { (default : RulePres) with names := canonNames r.vars.length }

/-- A clause's variable names, canonical, the same names for its exclusion (an exclusion binds its
variables, so it may reuse the names of the equation it occurs in). -/
def canonClausePres (cl : Clause) : ClausePres :=
  { (default : ClausePres) with names := canonNames cl.vars.length, exclNames := canonNames cl.vars.length }

/-- A function's variable names, canonical. -/
def canonFnPres (f : Fn) : FnPres :=
  { (default : FnPres) with clauses := f.clauses.map canonClausePres }

/-- The items of the axioms among `ss`, each translated by `trAxiom` with no declarations and no
aliases. -/
def kernelItems (ss : List Kore.Sentence) : List KoreAML.Item :=
  ss.filterMap fun
    | .axiom a => some (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩)
    | _ => none

/-- An application of `f` as `Term.kore` writes it: `Lblite{SortX}(…)` for a symbol named
`ite{X}`, `f(…)` with no sort argument otherwise. The registry's `kIte` is named `Lblite`, with no
sort in its name, so `Term.kore` applies it, if at all, as the sortless `Lblite(…)` written here;
a definition applies `ite` at a sort through its own parameter symbol `ite{X}`. -/
def symApp (c : Semantics) (f : Sym) (args : List Kore.Pattern) : Kore.Pattern :=
  match iteSort? (c.symName f) with
  | some X => .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt X] args
  | none => .app ⟨⟨c.symName f⟩⟩ [] args

/-- `symApp` writes a symbol named `n` at the head `h` and the sort names `xs`: `n` itself at no
sort, or the head and the sort names the decoder reads from `n` (`instDecode?`). -/
def _root_.KCore.InstHeadOf (n h : String) (xs : List String) : Prop :=
  (xs = [] ∧ h = n) ∨ (xs ≠ [] ∧ instDecode? n = some (h, xs))

/-- `symApp c f` applies one head at one list of sorts, whatever the arguments: the symbol's name
at no sort, or the head and the sorts the decoder reads from the name. -/
theorem symApp_head (c : Semantics) (f : Sym) :
    ∃ h xs, InstHeadOf (c.symName f) h xs ∧
      ∀ ps, symApp c f ps = .app ⟨⟨h⟩⟩ (xs.map KoreAML.srt) ps := by
  unfold symApp
  cases hX : iteSort? (c.symName f) with
  | some X => exact ⟨"Lblite", [X], .inr ⟨List.cons_ne_nil _ _, iteSort?_eq_some.1 hX⟩, fun _ => rfl⟩
  | none => exact ⟨c.symName f, [], .inl ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- A symbol whose name the decoder reads as no instance is applied at its name, at no sort. -/
theorem symApp_noInst {c : Semantics} {f : Sym} {ps : List Kore.Pattern}
    (h : instDecode? (c.symName f) = none) : symApp c f ps = .app ⟨⟨c.symName f⟩⟩ [] ps := by
  unfold symApp; rw [iteSort?_none_of_instDecode h]

/-- `Term.kore` writes an application as `symApp` does. -/
theorem kore_app (c : Semantics) (vs : List KoreAML.Var) (f : Sym) (ts : List Term) :
    Term.kore c vs (.app f ts) = symApp c f (Term.koreList c vs ts) := by
  rw [Term.kore]; unfold symApp; rfl

/-- `KoreAML.srt` is injective. -/
theorem srt_inj_iha {a b : String} (h : KoreAML.srt a = KoreAML.srt b) : a = b := by
  simpa [KoreAML.srt] using h

/-- `KoreAML.srt` is injective on lists. -/
theorem srts_inj_iha : ∀ {xs ys : List String}, xs.map KoreAML.srt = ys.map KoreAML.srt → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [srt_inj_iha h.1, srts_inj_iha h.2]

/-- Two writings of `symApp c f` as one head at sorts agree on the head and on the sorts. -/
theorem symApp_writes_eq_iha {c : Semantics} {f : Sym} {h h' : String} {xs xs' : List String}
    (hw : ∀ ps, symApp c f ps = .app ⟨⟨h⟩⟩ (xs.map KoreAML.srt) ps)
    (hw' : ∀ ps, symApp c f ps = .app ⟨⟨h'⟩⟩ (xs'.map KoreAML.srt) ps) : h = h' ∧ xs = xs' := by
  have he := (hw []).symm.trans (hw' [])
  simp only [Kore.Pattern.app.injEq] at he
  exact ⟨by simpa using he.1, srts_inj_iha he.2.1⟩

/-! ## 1. The signature -/

/-- A sort as a declaration without parameters, under its KORE name `SortX`. -/
def sortDeclOf (c : Semantics) (s : Srt) : KoreAML.SortDecl := ⟨"Sort" ++ c.sortName s, [], false⟩

/-- G-arity of a symbol, `f ⟦s₁⟧ … ⟦sₙ⟧ ⊆ ⟦s⟧`, at the head `Term.kore` applies: `arityItem` of
its declaration for an ordinary symbol; for a symbol named `ite{X}`, the same inclusion with the
head `Lblite` applied to the sort `SortX`, which is how the translation of a term applies it. -/
def symArityItem (c : Semantics) (k : CtorSig) : KoreAML.Item :=
  match iteSort? (c.symName k.name) with
  | none => KoreAML.arityItem ⟨c.symName k.name, [], k.args.map (srtOf c), srtOf c k.result, false, []⟩
  | some X =>
    { label := "arity Lblite at Sort" ++ X, rule := "G-arity", names := []
      pat := KoreAML.appList (KoreAML.sym (.symbol "Lblite") ⬝ sortP X)
          (k.args.map fun s => KoreAML.inhOf (sortP (c.sortName s))) ⊆⊆
        KoreAML.inhOf (sortP (c.sortName k.result)) }

/-- A symbol whose name the decoder reads as no instance has the arity item of its declaration. -/
theorem symArityItem_noInst {c : Semantics} {k : CtorSig} (h : instDecode? (c.symName k.name) = none) :
    symArityItem c k =
      KoreAML.arityItem ⟨c.symName k.name, [], k.args.map (srtOf c), srtOf c k.result, false, []⟩ := by
  unfold symArityItem; rw [iteSort?_none_of_instDecode h]

/-- The signature's items: definedness; per sort, that its name denotes one sort (G-sort); per
symbol, its arity; the arity and definedness of the definedness symbols; the arity of next at the
configuration sort.

No sort is said to be inhabited (G-nonempty). A sort is interpreted by its values, and a numbered
sort may have none (a sort of the definition without constructor, or a library sort whose module's
constructors are not imported); G-nonempty would put an element in such a sort, at which the equations of a function on a
supersort are read although the function is evaluated at values only. A sort that has a value is
inhabited without it: the value denotes an element of the sort (`ΓDomains`). -/
def sigItems (c : Semantics) : List KoreAML.Item :=
  [KoreAML.definednessItem] ++
  (kernelSorts c).map (fun s => KoreAML.sortConstantItem (sortDeclOf c s)) ++
  (kernelSyms c).map (symArityItem c) ++
  [KoreAML.ceilArityItem, KoreAML.ceilDefItem, KoreAML.nextArityItem [] (srtOf c topCellSort)]

/-- **The signature.** The axioms that make the encoding of sorted matching logic in applicative
matching logic mean what it should: `⌈_⌉` is definedness, each sort is a sort,
each symbol maps arguments of its argument sorts into its result sort, `⌈_⌉{s,s'}` behaves as
definedness, next keeps a configuration a configuration, and a domain value of any literal lies in
its sort (`dvArityAll`, for every literal, since a ground value may carry any). These are the items
`Theory.ofDefinition` builds from a text's declarations, built from the semantics' lists of sorts
and symbols instead, less G-nonempty (`sigItems`). -/
def ΓSig (c : Semantics) : Premises KoreAML.Sym := fun φ =>
  KoreAML.itemsPremises (sigItems c) φ ∨ KoreAML.dvArityAll φ

/-! ## 2. The constructors -/

/-- Two generators whose applications may denote one element where an overloading symbol's
arguments are covered: an overloading symbol and an injection, or two constructor generators, one a
function-overloaded symbol (`fnOvl`: at covered arguments its application is the function's value,
which may be any element of the sort), or one an overloading symbol and their overload closures
meet (`ovlClosure`). Their distinctness is stated at uncovered arguments only. -/
def _root_.KCore.Semantics.distGuarded (c : Semantics) : Gen → Gen → Bool
  | .ctor k, .ctor k' => c.fnOvl (.ctor k) || c.fnOvl (.ctor k') ||
      (c.isOvl k.name || c.isOvl k'.name) && (c.ovlClosure k.name).any (c.ovlClosure k'.name).contains
  | .ctor k, .inj _ => c.isOvl k.name
  | .inj _, .ctor k' => c.isOvl k'.name
  | .inj _, .inj _ => false

/-- The associativity sentence the text writes for the open generator `k` (`[assoc]`):
`axiom{R} \equals{S, R}(f(f(K1, K2), K3), f(K1, f(K2, K3)))`, S its result sort. -/
def assocAxK (c : Semantics) (k : ParamSig) : Kore.Axiom :=
  let f := c.symName k.sig.name
  let s := KoreAML.srt (c.sortName k.sig.result)
  let K1 := KoreAML.ev "K1" s
  let K2 := KoreAML.ev "K2" s
  let K3 := KoreAML.ev "K3" s
  { sortVars := [KoreAML.Rv]
    pattern := .equals s R (KoreAML.ap f [KoreAML.ap f [K1, K2], K3]) (KoreAML.ap f [K1, KoreAML.ap f [K2, K3]])
    attributes := [] }

/-- The idempotence sentence the text writes for the open generator `k` (`[idem]`):
`axiom{R} \equals{S, R}(f(K, K), K)`, S its result sort. -/
def idemAxK (c : Semantics) (k : ParamSig) : Kore.Axiom :=
  let s := KoreAML.srt (c.sortName k.sig.result)
  let K := KoreAML.ev "K" s
  { sortVars := [KoreAML.Rv]
    pattern := .equals s R (KoreAML.ap (c.symName k.sig.name) [K, K]) K
    attributes := [] }

/-- The law sentences the text writes for its open generators, each translated as written
(`trAxiom`): the associativity sentence of each `raw`, `assoc` parameter and the idempotence
sentence of each `raw`, `idem` one. -/
def lawItemsK (c : Semantics) : List KoreAML.Item :=
  c.params.flatMap fun k => if k.raw then
    (if k.assoc then [KoreAML.trAxiom [] [] ⟨0, "kernel", assocAxK c k⟩] else []) ++
    (if k.idem then [KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxK c k⟩] else [])
  else []

/-- The constructors' items, over `consSorts`: per sort, the functionality and injectivity of each
generator that is no open generator (`isOpenGen`: the text states neither of an open generator),
at uncovered arguments only for a function-overloaded symbol (`fnOvl`, with the argument sorts of
every overload: at covered arguments the overload equation gives the application the function's
value, of which the function's own equations say whether it exists and what it is),
the distinctness of each pair of those (Cons-Dist for constructors and for injections without a
common lower bound, Cons-Dist′ with one, `distLbItem`; none for comparable injections; at uncovered
arguments for a pair `distGuarded` names), and no-junk over every generator; then the coherence
triangles of every chain of `subsorts` (which holds the closure of the declared pairs), each
overload equation, and the law sentences of the open generators (`lawItemsK`). -/
def consItemsK (c : Semantics) : List KoreAML.Item :=
  let n := c.sortName
  let ovlArgs := fun (g : Gen) => match g with
    | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o => (c.ovlOver o).map fun kg => kg.args.map n
      else none
    | .inj _ => none
  let perSort := (consSorts c).flatMap fun N =>
    let gs := c.gens N
    let fr := gs.filter (!c.isOpenGen ·)
    (fr.map fun g =>
      if c.fnOvl g then KoreAML.Cons.funUncItem (n N) (Gen.toK c g) ((ovlArgs g).getD [])
      else KoreAML.Cons.funItem (n N) (Gen.toK c g)) ++
    ((fr.filter fun g => !(Gen.toK c g).argSorts.isEmpty).map fun g =>
      if c.fnOvl g then KoreAML.Cons.injUncItem (n N) (Gen.toK c g) ((ovlArgs g).getD [])
      else KoreAML.Cons.injItem (n N) (Gen.toK c g)) ++
    (pairs fr).flatMap (fun (g, g') => match g, g' with
      | .inj a, .inj b =>
        if c.le a b || c.le b a then []
        else match c.lowerBounds a b with
          | [] => [KoreAML.Cons.distItem (n N) (Gen.toK c g) (Gen.toK c g')]
          | lbs => [distLbItem (n N) (n a) (n b) (lbs.map n)]
      | _, _ =>
        if c.distGuarded g g' then
          [KoreAML.Cons.distUncItem (n N) (Gen.toK c g) (Gen.toK c g') (ovlArgs g) (ovlArgs g')]
        else [KoreAML.Cons.distItem (n N) (Gen.toK c g) (Gen.toK c g')]) ++
    (if gs.isEmpty then [] else [KoreAML.Cons.noJunkItem (n N) (gs.map (Gen.toK c))])
  let coh := c.subsorts.flatMap fun (a, b) =>
    (c.subsorts.filter (·.1 == b)).map fun (_, e) => KoreAML.Cons.cohItem (n a) (n b) (n e)
  let ovlEqs := c.ovls.flatMap fun o => (c.ovlOver o).map fun kg => KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg)
  perSort ++ coh ++ ovlEqs ++ lawItemsK c

/-- No generator is a function-overloaded symbol in a semantics without one. -/
theorem fnOvl_eq_false {c : Semantics} (h : c.fnOvlSyms = []) (g : Gen) : c.fnOvl g = false := by
  cases g <;> simp [Semantics.fnOvl, h]

/-- For a semantics without a function-overloaded symbol, `distGuarded` names a pair of constructor
generators exactly where one is an overloading symbol and their overload closures meet. -/
theorem distGuarded_eq_of_noFnOvl {c : Semantics} (h : c.fnOvlSyms = []) (k k' : CtorSig) :
    c.distGuarded (.ctor k) (.ctor k') =
      ((c.isOvl k.name || c.isOvl k'.name) && (c.ovlClosure k.name).any (c.ovlClosure k'.name).contains) := by
  simp [Semantics.distGuarded, fnOvl_eq_false h]

/-- For a semantics without a function-overloaded symbol, the constructors' items are the
functionality and the injectivity of each generator at every argument. -/
theorem consItemsK_eq_of_noFnOvl {c : Semantics} (h : c.fnOvlSyms = []) :
    consItemsK c =
      let n := c.sortName
      let ovlArgs := fun (g : Gen) => match g with
        | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o => (c.ovlOver o).map fun kg => kg.args.map n
          else none
        | .inj _ => none
      let perSort := (consSorts c).flatMap fun N =>
        let gs := c.gens N
        let fr := gs.filter (!c.isOpenGen ·)
        (fr.map (Gen.toK c)).map (KoreAML.Cons.funItem (n N)) ++
        ((fr.map (Gen.toK c)).filter (!·.argSorts.isEmpty)).map (KoreAML.Cons.injItem (n N)) ++
        (pairs fr).flatMap (fun (g, g') => match g, g' with
          | .inj a, .inj b =>
            if c.le a b || c.le b a then []
            else match c.lowerBounds a b with
              | [] => [KoreAML.Cons.distItem (n N) (Gen.toK c g) (Gen.toK c g')]
              | lbs => [distLbItem (n N) (n a) (n b) (lbs.map n)]
          | _, _ =>
            if c.distGuarded g g' then
              [KoreAML.Cons.distUncItem (n N) (Gen.toK c g) (Gen.toK c g') (ovlArgs g) (ovlArgs g')]
            else [KoreAML.Cons.distItem (n N) (Gen.toK c g) (Gen.toK c g')]) ++
        (if gs.isEmpty then [] else [KoreAML.Cons.noJunkItem (n N) (gs.map (Gen.toK c))])
      let coh := c.subsorts.flatMap fun (a, b) =>
        (c.subsorts.filter (·.1 == b)).map fun (_, e) => KoreAML.Cons.cohItem (n a) (n b) (n e)
      let ovlEqs := c.ovls.flatMap fun o => (c.ovlOver o).map fun kg => KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg)
      perSort ++ coh ++ ovlEqs ++ lawItemsK c := by
  unfold consItemsK
  simp only [fnOvl_eq_false h, Bool.false_eq_true, ↓reduceIte, List.map_map, List.filter_map]
  rfl

/-- **The constructors.** Per constructor sort, each generator is a total function, injective, and
apart from the others, and the sort holds nothing but what its generators build where it has a
generator (the text writes no such sentence for a sort without one); injections
compose along every chain of subsorts.

The definition's own collection sorts are left out of the sorts it ranges over. The elements of a collection sort are not built by constructors: its unit, element
and concatenation symbols are parameter symbols, so its only generators are injections from its
subsorts, and a no-junk item over those would exclude the empty collection and every collection
of two or more elements. Its elements are pinned by the domains instead: every value is one
element, distinct values are distinct, and `collNoJunk`. -/
def ΓCons (c : Semantics) : Premises KoreAML.Sym := KoreAML.itemsPremises (consItemsK c)

/-! ## 3. The domains -/

/-- No junk in the collection sort of `k`: `⟦S⟧ ⊆ μX. unit ∨ concat(elem(⟦K⟧, ⟦V⟧), X)` for a map or a range map,
`⟦S⟧ ⊆ μX. unit ∨ concat(elem(⟦K⟧), X)` for a set or a list, with `k`'s symbols and sorts. Every
element of the sort is built from its unit by adding elements one at a time. -/
def collNoJunk (c : Semantics) (k : CollSig) : KoreAML.P :=
  let X : SVar := ⟨1⟩
  let el := match k.kind with
    | .map | .rangeMap => KoreAML.appList (symP (c.symName k.elem))
        [KoreAML.inhOf (sortP (c.sortName k.key)), KoreAML.inhOf (sortP (c.sortName (valSort k)))]
    | _ => KoreAML.appList (symP (c.symName k.elem)) [KoreAML.inhOf (sortP (c.sortName k.key))]
  KoreAML.inhOf (sortP (c.sortName k.sort)) ⊆⊆
    .mu X (symP (c.symName k.unit) ⋁ KoreAML.appList (symP (c.symName k.concat)) [el, .svar X])

/-- **The domains.** What the semantics says of its values and of the symbols it interprets:
- the graph of every interpreted hooked symbol on ground values of its argument sorts, ⊥ where it
  is undefined, except at its silent points (`silent`), where `ΓFallback` holds the
  interpretation's value; the graph of every parameter symbol under the semantics' interpretation of its
  parameters (`paramVal`, which reads `c.hooks`), ⊥ where that is undefined; each written as the
  translation of a term writes the application (`symApp`), so the graph of `ite` at a sort is
  about `Lblite` applied to that sort;
- every ground value of a sort denotes exactly one element of that sort, `∃y:s. ⟦v⟧ = y`;
- distinct values of one sort among `distinctSorts` denote distinct elements;
- no junk in each collection sort (`collNoJunk`).

That a value is an element follows from the constructors' functionality for a constructor term;
for a collection nothing else gives it. -/
def ΓDomains (c : Semantics) : Premises KoreAML.Sym := fun φ =>
  (∃ (k : CtorSig) (vs : List GroundTerm) (r : Option GroundTerm),
      k ∈ hookSigs ∧ c.sortsOf vs = some k.args ∧ hook k.name vs = some r ∧
      (r = none → silent k.name vs = false) ∧
      φ = (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match r with
        | some v => den c v
        | none => ⊥))) ∨
  (∃ (k : ParamSig) (vs : List GroundTerm),
      k ∈ c.params ∧ c.sortsOf vs = some k.sig.args ∧
      φ = (KoreAML.den (symApp c k.sig.name (GroundTerm.koreList c vs)) ≡
        (match c.paramVal k.sig.name vs with
          | some v => den c v
          | none => ⊥))) ∨
  (∃ (v : GroundTerm) (s : Srt), c.sortOf v = some s ∧
      φ = KoreAML.sExists ⟨1⟩ (sortP (c.sortName s)) (den c v ≡ .evar ⟨1⟩)) ∨
  (∃ (v w : GroundTerm) (s : Srt),
      (distinctSorts c).contains s = true ∧
      c.sortOf v = some s ∧ c.sortOf w = some s ∧ GroundTerm.cmp v w ≠ .eq ∧
      φ = ∼(den c v ⋀ den c w)) ∨
  (∃ k ∈ c.allColls, φ = collNoJunk c k)

/-- **What the interpretation decides where the text is silent.** At a silent point of an
interpreted symbol (`silent`, where `hook` gives no value), the interpretation's value of the
result sort (`Semantics.fallback`), ⊥ where it gives none; at values of a function's argument
sorts where every clause fails, its rest (`Semantics.fnRest`), ⊥ where that is undefined. Each
written as `ΓDomains` writes a graph. -/
def ΓFallback (c : Semantics) : Premises KoreAML.Sym := fun φ =>
  (∃ (k : CtorSig) (vs : List GroundTerm),
    k ∈ hookSigs ∧ c.sortsOf vs = some k.args ∧ hook k.name vs = some none ∧ silent k.name vs = true ∧
    φ = (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match c.fallback k.name vs with
      | some v => den c v
      | none => ⊥))) ∨
  (∃ (fn : Fn) (vs : List GroundTerm),
    fn ∈ c.allFns ∧ c.sortsOf vs = some fn.args ∧ (∀ cl ∈ fn.clauses, Fails c vs cl) ∧
    φ = (KoreAML.den (symApp c fn.label (GroundTerm.koreList c vs)) ≡ (match c.fnRest fn vs with
      | some v => den c v
      | none => ⊥)))

/-! ## 4. The collections

The axioms that say what a collection sort's unit, element and concatenation symbols are on
elements that need not be values' elements. `ΓDomains` gives their graphs on values only; a
negated premise reads a collection pattern at any elements of its sorts (FaithfulColl.lean has a
model of the other parts in which a map pattern holds of a map it does not match). Each axiom is
true of the intended model: a map sort's elements are the finite maps from its key sort's
elements to its value sort's, `elem(a, b)` the map of one entry `a ↦ b`, the unit the empty map,
`concat` the union of two maps with disjoint keys and nothing (`∅`) where their keys overlap; a
list sort's elements are the finite sequences of its element sort's elements, `elem(a)` the
sequence `[a]`, the unit `[]`, `concat` concatenation (total); a set sort's elements are the finite
sets of its element sort's elements, `elem(a)` the set `{a}`, the unit `∅`, `concat` the union of
two sets with no member in common and nothing (`∅`) where they share one. A set is read as a map
whose entries carry no value: its axioms are the map's, with `elem(a)` for `elem(a, b)`. -/

section
variable (c : Semantics) (k : CollSig)

/-- The unit of the collection `k`, as the KORE of a value writes it. -/
def collU : KoreAML.P := symP (c.symName k.unit)
/-- `elem(a, b)`: an entry of the map collection `k`. -/
def collE (a b : KoreAML.P) : KoreAML.P := KoreAML.appList (symP (c.symName k.elem)) [a, b]
/-- `concat(a, b)` in the collection `k`. -/
def collC (a b : KoreAML.P) : KoreAML.P := KoreAML.appList (symP (c.symName k.concat)) [a, b]
/-- The inhabitants of the sort `s`. -/
def inSort (s : Srt) : KoreAML.P := KoreAML.inhOf (sortP (c.sortName s))

/-- **A map's unit is a union of units only.** `∀ m₁ m₂ : S. ⌈unit ∧ concat(m₁, m₂)⌉ → m₁ = unit ∧
m₂ = unit`. True of finite maps: if `m₁ ∪ m₂` is defined and empty, both have no key, so both are
the empty map. -/
def mapUnitSplitAx : KoreAML.P :=
  let m₁ : EVar := ⟨1⟩
  let m₂ : EVar := ⟨2⟩
  KoreAML.guarded [m₁ ∈∈ inSort c k.sort, m₂ ∈∈ inSort c k.sort]
    (⌈collU c k ⋀ collC c k (.evar m₁) (.evar m₂)⌉ ⇒ ((.evar m₁ ≡ collU c k) ⋀ (.evar m₂ ≡ collU c k)))

/-- **An entry is not the unit.** `∀ a : K, b : V. ¬⌈unit ∧ elem(a, b)⌉`. True of finite maps:
`a ↦ b` has the key `a`, the empty map has none. -/
def mapElemNotUnitAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let b : EVar := ⟨2⟩
  KoreAML.guarded [a ∈∈ inSort c k.key, b ∈∈ inSort c (valSort k)]
    (∼⌈collU c k ⋀ collE c k (.evar a) (.evar b)⌉)

/-- **An entry is atomic.** `∀ a a' : K, b b' : V, r : S.
⌈elem(a', b') ∧ concat(elem(a, b), r)⌉ → a = a' ∧ b = b' ∧ r = unit`. True of finite maps: if
`{a' ↦ b'} = {a ↦ b} ∪ r` with disjoint keys, the union has the key `a` with the value `b`, so
`a = a'` and `b = b'`, and `r` has no key besides `a`, which it does not have, so `r` is empty. -/
def mapElemAtomAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let b : EVar := ⟨2⟩
  let a' : EVar := ⟨3⟩
  let b' : EVar := ⟨4⟩
  let r : EVar := ⟨5⟩
  KoreAML.guarded [a ∈∈ inSort c k.key, b ∈∈ inSort c (valSort k), a' ∈∈ inSort c k.key, b' ∈∈ inSort c (valSort k),
      r ∈∈ inSort c k.sort]
    (⌈collE c k (.evar a') (.evar b') ⋀ collC c k (collE c k (.evar a) (.evar b)) (.evar r)⌉ ⇒
      ((.evar a ≡ .evar a') ⋀ (.evar b ≡ .evar b') ⋀ (.evar r ≡ collU c k)))

/-- **An entry of a union is an entry of one part.** `∀ a : K, b : V, r m₁ m₂ : S.
⌈concat(elem(a, b), r) ∧ concat(m₁, m₂)⌉ → (∃y:S. m₁ = concat(elem(a, b), y) ∧ r = concat(y, m₂)) ∨
(∃y:S. m₂ = concat(elem(a, b), y) ∧ r = concat(m₁, y))`. True of finite maps: let
`M = {a ↦ b} ∪ r = m₁ ∪ m₂`, both unions defined. `M` has the key `a`, so one part has it, say
`m₁`, with the value `M(a) = b`; take `y = m₁` without `a`. Then `m₁ = {a ↦ b} ∪ y` (defined: `y`
lacks `a`), and `y ∪ m₂` is defined (`y ⊆ m₁`, whose keys are apart from `m₂`'s) and is `M`
without `a`, which is `r` (`r` lacks `a`, and `M = {a ↦ b} ∪ r`). Symmetrically when `m₂` has
`a`. -/
def mapDecompAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let b : EVar := ⟨2⟩
  let r : EVar := ⟨3⟩
  let m₁ : EVar := ⟨4⟩
  let m₂ : EVar := ⟨5⟩
  let y : EVar := ⟨6⟩
  let ab := collE c k (.evar a) (.evar b)
  KoreAML.guarded [a ∈∈ inSort c k.key, b ∈∈ inSort c (valSort k), r ∈∈ inSort c k.sort, m₁ ∈∈ inSort c k.sort,
      m₂ ∈∈ inSort c k.sort]
    (⌈collC c k ab (.evar r) ⋀ collC c k (.evar m₁) (.evar m₂)⌉ ⇒
      (KoreAML.sExists y (sortP (c.sortName k.sort))
          ((.evar m₁ ≡ collC c k ab (.evar y)) ⋀ (.evar r ≡ collC c k (.evar y) (.evar m₂))) ⋁
        KoreAML.sExists y (sortP (c.sortName k.sort))
          ((.evar m₂ ≡ collC c k ab (.evar y)) ⋀ (.evar r ≡ collC c k (.evar m₁) (.evar y)))))

/-- The axioms of a map collection. -/
def mapCollAxioms : List KoreAML.P :=
  [mapUnitSplitAx c k, mapElemNotUnitAx c k, mapElemAtomAx c k, mapDecompAx c k]

/-- `elem(a)`: an item of the list collection `k`. -/
def collI (a : KoreAML.P) : KoreAML.P := KoreAML.appList (symP (c.symName k.elem)) [a]

/-- **A list's unit is a concatenation of units only.** `∀ l₁ l₂ : S. ⌈unit ∧ concat(l₁, l₂)⌉ →
l₁ = unit ∧ l₂ = unit`. True of finite sequences: `l₁ ++ l₂ = []` has length `|l₁| + |l₂| = 0`, so
both are empty. -/
def listUnitSplitAx : KoreAML.P :=
  let l₁ : EVar := ⟨1⟩
  let l₂ : EVar := ⟨2⟩
  KoreAML.guarded [l₁ ∈∈ inSort c k.sort, l₂ ∈∈ inSort c k.sort]
    (⌈collU c k ⋀ collC c k (.evar l₁) (.evar l₂)⌉ ⇒ ((.evar l₁ ≡ collU c k) ⋀ (.evar l₂ ≡ collU c k)))

/-- **An item is not the unit.** `∀ a : K. ¬⌈unit ∧ elem(a)⌉`. True of finite sequences: `[a]` has
length one, `[]` length zero. -/
def listElemNotUnitAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  KoreAML.guarded [a ∈∈ inSort c k.key] (∼⌈collU c k ⋀ collI c k (.evar a)⌉)

/-- **An item is atomic, from the front.** `∀ a a' : K, r : S. ⌈elem(a') ∧ concat(elem(a), r)⌉ →
a = a' ∧ r = unit`. True of finite sequences: if `[a'] = a :: r`, the heads are equal and the
tail `r` is the tail of `[a']`, which is empty. -/
def listElemAtomAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let a' : EVar := ⟨2⟩
  let r : EVar := ⟨3⟩
  KoreAML.guarded [a ∈∈ inSort c k.key, a' ∈∈ inSort c k.key, r ∈∈ inSort c k.sort]
    (⌈collI c k (.evar a') ⋀ collC c k (collI c k (.evar a)) (.evar r)⌉ ⇒
      ((.evar a ≡ .evar a') ⋀ (.evar r ≡ collU c k)))

/-- **An item is atomic, from the back.** `∀ a a' : K, r : S. ⌈elem(a') ∧ concat(r, elem(a))⌉ →
a = a' ∧ r = unit`. True of finite sequences: if `[a'] = r ++ [a]`, the lengths give `|r| = 0`, so
`r` is empty and `[a'] = [a]`. -/
def listElemAtomBackAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let a' : EVar := ⟨2⟩
  let r : EVar := ⟨3⟩
  KoreAML.guarded [a ∈∈ inSort c k.key, a' ∈∈ inSort c k.key, r ∈∈ inSort c k.sort]
    (⌈collI c k (.evar a') ⋀ collC c k (.evar r) (collI c k (.evar a))⌉ ⇒
      ((.evar a ≡ .evar a') ⋀ (.evar r ≡ collU c k)))

/-- **A concatenation's first item is the first part's, or the second's when the first is empty.**
`∀ a : K, r l₁ l₂ : S. ⌈concat(elem(a), r) ∧ concat(l₁, l₂)⌉ →
(l₁ = unit ∧ l₂ = concat(elem(a), r)) ∨ (∃y:S. l₁ = concat(elem(a), y) ∧ r = concat(y, l₂))`. True
of finite sequences: let `a :: r = l₁ ++ l₂`. If `l₁` is empty, `l₂ = a :: r`. Otherwise `l₁` has
a head, which is the head `a` of `l₁ ++ l₂`; take `y` its tail, so `l₁ = a :: y`, and the tails of
`a :: r = a :: (y ++ l₂)` are equal, `r = y ++ l₂`. A value is decomposed from its first item, so
this front form is the one that splits a value's element along any concatenation; a pattern that
takes an item from the back (`L ListItem(_)`) is a concatenation like any other. -/
def listDecompAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let r : EVar := ⟨2⟩
  let l₁ : EVar := ⟨3⟩
  let l₂ : EVar := ⟨4⟩
  let y : EVar := ⟨5⟩
  let ia := collI c k (.evar a)
  KoreAML.guarded [a ∈∈ inSort c k.key, r ∈∈ inSort c k.sort, l₁ ∈∈ inSort c k.sort, l₂ ∈∈ inSort c k.sort]
    (⌈collC c k ia (.evar r) ⋀ collC c k (.evar l₁) (.evar l₂)⌉ ⇒
      (((.evar l₁ ≡ collU c k) ⋀ (.evar l₂ ≡ collC c k ia (.evar r))) ⋁
        KoreAML.sExists y (sortP (c.sortName k.sort))
          ((.evar l₁ ≡ collC c k ia (.evar y)) ⋀ (.evar r ≡ collC c k (.evar y) (.evar l₂)))))

/-- The axioms of a list collection. -/
def listCollAxioms : List KoreAML.P :=
  [listUnitSplitAx c k, listElemNotUnitAx c k, listElemAtomAx c k, listElemAtomBackAx c k, listDecompAx c k]

/-- **A set's unit is a union of units only.** `∀ s₁ s₂ : S. ⌈unit ∧ concat(s₁, s₂)⌉ → s₁ = unit ∧
s₂ = unit`. True of finite sets: if `s₁ ∪ s₂` is defined and empty, both have no member, so both
are the empty set. -/
def setUnitSplitAx : KoreAML.P :=
  let s₁ : EVar := ⟨1⟩
  let s₂ : EVar := ⟨2⟩
  KoreAML.guarded [s₁ ∈∈ inSort c k.sort, s₂ ∈∈ inSort c k.sort]
    (⌈collU c k ⋀ collC c k (.evar s₁) (.evar s₂)⌉ ⇒ ((.evar s₁ ≡ collU c k) ⋀ (.evar s₂ ≡ collU c k)))

/-- **A set's element is not the unit.** `∀ a : K. ¬⌈unit ∧ elem(a)⌉`. True of finite sets: `{a}`
has the member `a`, `∅` none. -/
def setElemNotUnitAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  KoreAML.guarded [a ∈∈ inSort c k.key] (∼⌈collU c k ⋀ collI c k (.evar a)⌉)

/-- **A set's element is atomic.** `∀ a a' : K, r : S. ⌈elem(a') ∧ concat(elem(a), r)⌉ → a = a' ∧
r = unit`. True of finite sets: if `{a'} = {a} ∪ r` with `a` not in `r`, the union has the member
`a`, so `a = a'`, and `r` has no member besides `a`, which it does not have, so `r` is empty. -/
def setElemAtomAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let a' : EVar := ⟨2⟩
  let r : EVar := ⟨3⟩
  KoreAML.guarded [a ∈∈ inSort c k.key, a' ∈∈ inSort c k.key, r ∈∈ inSort c k.sort]
    (⌈collI c k (.evar a') ⋀ collC c k (collI c k (.evar a)) (.evar r)⌉ ⇒
      ((.evar a ≡ .evar a') ⋀ (.evar r ≡ collU c k)))

/-- **A member of a union is a member of one part.** `∀ a : K, r s₁ s₂ : S.
⌈concat(elem(a), r) ∧ concat(s₁, s₂)⌉ → (∃y:S. s₁ = concat(elem(a), y) ∧ r = concat(y, s₂)) ∨
(∃y:S. s₂ = concat(elem(a), y) ∧ r = concat(s₁, y))`. True of finite sets: let
`T = {a} ∪ r = s₁ ∪ s₂`, both unions of disjoint sets. `T` has the member `a`, so one part has it,
say `s₁`; take `y = s₁` without `a`. Then `s₁ = {a} ∪ y` (disjoint: `y` lacks `a`), and `y ∪ s₂`
is a union of disjoint sets (`y ⊆ s₁`, which is apart from `s₂`) and is `T` without `a`, which is
`r` (`r` lacks `a`, and `T = {a} ∪ r`). Symmetrically when `s₂` has `a`. -/
def setDecompAx : KoreAML.P :=
  let a : EVar := ⟨1⟩
  let r : EVar := ⟨2⟩
  let s₁ : EVar := ⟨3⟩
  let s₂ : EVar := ⟨4⟩
  let y : EVar := ⟨5⟩
  let ia := collI c k (.evar a)
  KoreAML.guarded [a ∈∈ inSort c k.key, r ∈∈ inSort c k.sort, s₁ ∈∈ inSort c k.sort, s₂ ∈∈ inSort c k.sort]
    (⌈collC c k ia (.evar r) ⋀ collC c k (.evar s₁) (.evar s₂)⌉ ⇒
      (KoreAML.sExists y (sortP (c.sortName k.sort))
          ((.evar s₁ ≡ collC c k ia (.evar y)) ⋀ (.evar r ≡ collC c k (.evar y) (.evar s₂))) ⋁
        KoreAML.sExists y (sortP (c.sortName k.sort))
          ((.evar s₂ ≡ collC c k ia (.evar y)) ⋀ (.evar r ≡ collC c k (.evar s₁) (.evar y)))))

/-- The axioms of a set collection: the map's (`mapCollAxioms`), each with an element in place of
an entry. -/
def setCollAxioms : List KoreAML.P :=
  [setUnitSplitAx c k, setElemNotUnitAx c k, setElemAtomAx c k, setDecompAx c k]

/-- The axioms of the collection `k`, by its kind (none for a range map). -/
def collAxioms : List KoreAML.P :=
  match k.kind with
  | .map => mapCollAxioms c k
  | .set => setCollAxioms c k
  | .list => listCollAxioms c k
  | .rangeMap => []

end

/-- **The collections.** For every collection sort of the semantics (the library's `Map`, `Set`,
`List`, and the definition's own, `c.allColls`), the axioms of its kind (`collAxioms`). -/
def ΓColls (c : Semantics) : Premises KoreAML.Sym := fun φ =>
  ∃ k ∈ c.allColls, φ ∈ collAxioms c k

/-! ## 5. The functions -/

/-- `premise → f(X̄) = rhs ∧ ens` as an axiom over the sort variable `R` (`equationAt`, no
attributes). The left side is `f` applied to the formal arguments as `symApp` writes an application
of `f`, so a function's equations speak of the head its applications are written at. -/
def eqnSentence (c : Semantics) (f : Fn) (prem rhs ens : Kore.Pattern) : Kore.Sentence :=
  KoreAML.equationAt (symApp c f.label (KoreAML.vars (KoreAML.numbered "X" 0 (f.args.map c.sortName))))
    (c.sortName f.result) prem rhs ens []

/-- For a function whose name the decoder reads as no instance, the equation is `equationAx`'s at
the function's name. -/
theorem eqnSentence_plain {c : Semantics} {f : Fn} (h : instDecode? (c.symName f.label) = none)
    (prem rhs ens : Kore.Pattern) :
    eqnSentence c f prem rhs ens =
      KoreAML.equationAx (c.symName f.label) (f.args.map c.sortName) (c.sortName f.result) prem rhs ens [] := by
  unfold eqnSentence; rw [symApp_noInst h]; rfl

/-- The premise of an equation that competes with other clauses: none of them applies, its own
`requires` holds and its patterns match, `¬ ⋁ competitors ∧ ⌈req = true⌉ ∧ X̄ ∈ p̄`: the premise
`clauseAx` (Emit.lean) writes for an `[owise]` equation. -/
def competingPremise (args : List String) (competitors : List Kore.Pattern) (req : Option Kore.Pattern)
    (pats : List Kore.Pattern) : Kore.Pattern :=
  .and R [.not R (KoreAML.anyOf competitors), premise args req pats]

/-- The right side and the `ensures` part of a clause's equations. Without existential variables:
`rhs` and `ens`, `ens` being `⌈E = true⌉` for an `ensures` E, `⊤` without one. With existential
variables ē (`exs`) the right side is under their binder, `∃ē. (rhs ∧ ens ∧ post)`, as a rule's
(`ruleRight`), and the `ensures` part is `⊤`: the function's elements at the arguments are those of
the instances of `rhs` over ē at which `ens` and `post` hold. -/
def clauseRhs (c : Semantics) (f : Fn) (cl : Clause) : Kore.Pattern × Kore.Pattern :=
  let vs := canonVars c cl.vars
  let S := srtOf c f.result
  if cl.exs.isEmpty then (Term.kore c vs cl.rhs, reqPat S (cl.ens.map (Term.kore c vs)))
  else ((cl.exs.filterMap (vs[·]?)).foldr (fun v p => .exist S v.kore p)
      (.and S ([Term.kore c vs cl.rhs, reqPat S (cl.ens.map (Term.kore c vs))] ++ Cond.conj c vs S cl.post)),
    reqPat S none)

/-- Without existential variables the pair is `rhs` and `ens`, whatever `post` is. -/
theorem clauseRhs_nil {c : Semantics} {f : Fn} {cl : Clause} (h : cl.exs = []) :
    clauseRhs c f cl = (Term.kore c (canonVars c cl.vars) cl.rhs,
      reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) := by
  unfold clauseRhs; rw [h]; rfl

/-- No clause of a function of a plain definition has an existential variable: the user's by
`plain`, the generated sort predicates' by their text. -/
theorem _root_.KCore.Semantics.exs_of_plain_mem {c : Semantics} (hp : c.plain = true) {fn : Fn}
    (hfn : fn ∈ c.allFns) : ∀ cl ∈ fn.clauses, cl.exs = [] := by
  simp only [Semantics.allFns, List.mem_append] at hfn
  rcases hfn with hfn | hfn
  · simp only [Semantics.plain, Bool.and_eq_true, List.all_eq_true] at hp
    intro cl hcl
    exact List.isEmpty_iff.mp (hp.1.1.1.2 fn hfn cl hcl).1.1.1.2
  · exact Semantics.sortPreds_exs hfn

/-- A clause with no competitor: `⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre → f(X̄) = right ∧ ens'`, the pair
`(right, ens')` being `clauseRhs`'s: `rhs` and `ens` for a clause without existential variables
(`clauseRhs_nil`). Where moreover the clause's predicate `pre` is `\top` the premise is
`⌈req = true⌉ ∧ X̄ ∈ p̄` (`withPre`, `clauseEquation_top`), the equation `clauseAx` writes. -/
def clauseEquation (c : Semantics) (f : Fn) (cl : Clause) : Kore.Sentence :=
  let vs := canonVars c cl.vars
  eqnSentence c f
    (withPre c vs cl (premise (f.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats)))
    (clauseRhs c f cl).1 (clauseRhs c f cl).2

/-- A clause under the negation of the clauses `others`: it applies where none of them does, its
own `requires` holds, its patterns match and its predicate holds,
`¬ ⋁ competitors ∧ (⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre)`; where the predicate is `\top` the premise is
`competingPremise`'s (`competingEquation_top`). Its right side is `clauseEquation`'s (`clauseRhs`). -/
def competingEquation (c : Semantics) (f : Fn) (others : List Clause) (cl : Clause) : Kore.Sentence :=
  let vs := canonVars c cl.vars
  eqnSentence c f
    (.and R [.not R (KoreAML.anyOf (others.map fun cl' => exclusion c f cl' (canonClausePres cl'))),
      withPre c vs cl (premise (f.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats))])
    (clauseRhs c f cl).1 (clauseRhs c f cl).2

/-- The equation of a clause without existential variables whose predicate is `\top` has the
premise `⌈req = true⌉ ∧ X̄ ∈ p̄` and the right side `rhs ∧ ens`. -/
theorem clauseEquation_top {c : Semantics} {f : Fn} {cl : Clause} (h : cl.pre = .top) (hex : cl.exs = []) :
    clauseEquation c f cl =
      eqnSentence c f (premise (f.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
          (Term.koreList c (canonVars c cl.vars) cl.pats))
        (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) := by
  unfold clauseEquation; simp only [withPre_top h, clauseRhs_nil hex]

/-- The competing equation of a clause without existential variables whose predicate is `\top` has
the premise `competingPremise` writes, `¬ ⋁ competitors ∧ ⌈req = true⌉ ∧ X̄ ∈ p̄`, and the right side
`rhs ∧ ens`. -/
theorem competingEquation_top {c : Semantics} {f : Fn} {others : List Clause} {cl : Clause} (h : cl.pre = .top)
    (hex : cl.exs = []) :
    competingEquation c f others cl =
      eqnSentence c f
        (competingPremise (f.args.map c.sortName) (others.map fun cl' => exclusion c f cl' (canonClausePres cl'))
          (cl.req.map (Term.kore c (canonVars c cl.vars))) (Term.koreList c (canonVars c cl.vars) cl.pats))
        (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) := by
  unfold competingEquation competingPremise; simp only [withPre_top h, clauseRhs_nil hex]

/-- The clauses of f of a smaller priority than cl's that are not `aside`: those that apply
before it. -/
def lowerClauses (f : Fn) (cl : Clause) : List Clause :=
  f.clauses.filter fun cl' => !cl'.aside && cl'.prio < cl.prio

/-- A clause's equation, `premise ∧ ¬ ⋁ lower → f(X̄) = rhs`: the clauses of a smaller priority
negated (`competingEquation`), and where there is none, the clause's premise alone
(`clauseEquation`). -/
def prioEquation (c : Semantics) (f : Fn) (cl : Clause) : Kore.Sentence :=
  if (lowerClauses f cl).isEmpty then clauseEquation c f cl
  else competingEquation c f (lowerClauses f cl) cl

/-- A function's equations: one per clause (`prioEquation`). The equations of the clauses of one
priority do not exclude one another: where two apply they are coherent (`ClausesAgree`,
`MatchIndependent`, assumed by `Hyp`), which is what lets `Eval`'s unordered reading of them be
the meaning of the set of equations. An `[owise]` equation is the clause of priority 200, its
competitors the clauses of a smaller priority, which is how kompile writes it (`clauseAx`,
Emit.lean). -/
def fnEquationsK (c : Semantics) (f : Fn) : List Kore.Sentence := f.clauses.map (prioEquation c f)

def fnItems (c : Semantics) : List KoreAML.Item :=
  c.allFns.flatMap fun f => kernelItems (fnEquationsK c f)

/-- **The functions.** For every function of the semantics, the user's and the generated sort
predicates alike: its equations (`fnEquationsK`).

The equations say what `f` is where a clause applies and nothing where none does. At values where
every clause fails, `Eval` gives `f` its rest (`Semantics.fnRest`, the interpretation's value), and
`ΓFallback` states that value's graph there, ⊥ where the interpretation gives none: a rule whose
competitor's `requires` calls `f` at such a point is then read in every model as `Step` reads
it. -/
def ΓFns (c : Semantics) : Premises KoreAML.Sym := KoreAML.itemsPremises (fnItems c)

/-! ## 6. The rules -/

/-- A rule's right side under its binder: `∃ē. (rhs ∧ ens ∧ post)`, ē the `exs`. -/
def ruleRight (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  (r.exs.filterMap (vs[·]?)).foldr (fun v p => .exist C v.kore p)
    (.and C ([Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))] ++ Cond.conj c vs C r.post))

/-- A rule's axiom with its priority read: `\rewrites(lhs ∧ ⌈req = true⌉ ∧ pre ∧ ¬ ⋁ competitors ∧
⌈right⌉, right)`, the competitors being the rules of a smaller priority (`applies`), none when it has
none, and `right` the rule's right side under its binder (`ruleRight`): `∃ē. (rhs ∧ ens ∧ post)`,
`ens` being `⌈E = true⌉`, or `⊤` without an `ensures`.

The premise `⌈right⌉` says what `Step.rule` asks: the rule fires only where its right-hand
side evaluates to a value and its `ensures` to `true`. Without it, a configuration (reachable or
not) at which a rule applies and its right side is empty (an `/Int` by a matched variable that is
zero, or a false `ensures`) would have to have a successor in the empty set, so it could not
exist, and the theory of the whole definition would be inconsistent, which is not what the kernel
means: there the rule gives no step. The competitors' `applies` has no such conjunct, since
`NotApplies` does not read a competitor's right side: a rule that applies blocks the rules of a
larger priority even where its right side is empty. -/
def prioRuleK (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let right := ruleRight c r
  let rightDef : Kore.Pattern := .ceil C C right
  let left := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre
  if comps.isEmpty then .rewrites C (.and C (left ++ [rightDef])) right
  else .rewrites C (.and C (left ++ [.not C (anyOfC C comps), rightDef])) right

/-- The axiom of a rule without existential variables and with `\top` predicates:
`\rewrites(lhs ∧ ⌈req = true⌉ ∧ ¬ ⋁ competitors ∧ ⌈rhs ∧ ens⌉, rhs ∧ ens)`. -/
theorem prioRuleK_top {c : Semantics} {r : Rule} (hex : r.exs = []) (hpre : r.pre = .top)
    (hpost : r.post = .top) :
    prioRuleK c r =
      (let C := srtOf c topCellSort
       let vs := canonVars c r.vars
       let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
       let right : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
       let rightDef : Kore.Pattern := .ceil C C right
       if comps.isEmpty then
         .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), rightDef]) right
       else .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
           .not C (anyOfC C comps), rightDef]) right) := by
  simp only [prioRuleK, ruleRight, hex, hpre, hpost, Cond.conj, Cond.isTop, if_true,
    List.filterMap_nil, List.foldr_nil, List.append_nil, List.cons_append, List.nil_append]

def ruleItems (c : Semantics) : List KoreAML.Item :=
  c.rules.map fun r =>
    KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩

/-- **The rules.** Each rule's axiom: a configuration that its left-hand side matches, where its
`requires` holds, no rule of a smaller priority applies and its right-hand side is defined, has the
right-hand side as a successor. -/
def ΓRules (c : Semantics) : Premises KoreAML.Sym := KoreAML.itemsPremises (ruleItems c)

/-! ## Γ and the step's closure -/

/-- **The theory of a semantics**: the signature, the constructors, the domains, the collections,
the functions, the rules, and the interpretation's values at silent points. It reads the semantics
and its interpretation of the parameter symbols and silent points, never a presentation, and holds
no axiom about a symbol the semantics does not have. -/
def Γ (c : Semantics) : Premises KoreAML.Sym :=
  ΓSig c ∪ ΓCons c ∪ ΓDomains c ∪ ΓColls c ∪ ΓFns c ∪ ΓRules c ∪ ΓFallback c

/-- The step's closure axiom, `∀y. •y ⊆ ⋁_r ∃x̄_r. (L_r ∧ y ∈ R_r)`, over the rules' axioms
(`prioRuleK`): a configuration has a successor only by a rule, whose left-hand side with its
priority read matches it, and the successor is in its right-hand side. The rules' variables
have canonical names, and no alias is read. -/
def stepClosureItem (c : Semantics) : KoreAML.Item :=
  let pats := c.rules.map (prioRuleK c)
  let total := pats.foldl (fun n p => n + (KoreAML.tableOf [] p).length) 0
  let y : EVar := ⟨total + 1⟩
  let (names, disjuncts, _) := pats.foldl (fun (acc : List String × List KoreAML.P × Nat) p =>
      let (ns, φ) := KoreAML.closureDisjunct [] acc.2.2 y p
      (acc.1 ++ ns, acc.2.1 ++ [φ], acc.2.2 + ns.length)) ([], [], 0)
  { label := s!"closure ({pats.length} rules)", rule := "Closure", names := names ++ ["y"]
    pat := ∀∀ y (KoreAML.sNext (.evar y) ⊆⊆ KoreAML.disjList disjuncts) }

/-- **The step's closure**: every successor of a configuration is one some rule gives. Not part of
`Γ`: soundness does not need it; completeness and the existence of a model state it beside `Γ`. -/
def Γstep (c : Semantics) : Premises KoreAML.Sym := fun φ => φ = (stepClosureItem c).pat

/-- Every element of Bool is `true` or `false`. -/
def boolClosed (c : Semantics) : KoreAML.P :=
  KoreAML.inhOf (sortP (c.sortName Srt.bool)) ⊆⊆
    (den c (.dv Srt.bool (.bool true)) ⋁ den c (.dv Srt.bool (.bool false)))

/-- **The closure axiom** (`boolClosed`), for a definition that reads a confined sort and whose
Bool holds only its literals. -/
def Γcl (c : Semantics) : Premises KoreAML.Sym := fun φ =>
  c.readsConfined = true ∧ c.litSort Srt.bool = true ∧ φ = boolClosed c

/-- **The theory the statements are about.** -/
def Γc (c : Semantics) : Premises KoreAML.Sym := Γ c ∪ Γcl c

/-- A definition that reads no confined sort has the theory `Γ`. -/
theorem Γc_plain {c : Semantics} (h : c.readsConfined = false) : Γc c = Γ c := by
  funext φ
  apply propext
  show φ ∈ Γ c ∨ Γcl c φ ↔ φ ∈ Γ c
  simp [Γcl, h]

/-! ## The families of an application -/

/-- `Vᵢ = ⟦σ i⟧` for each listed variable that σ gives a value. -/
def fixK (c : Semantics) (r : Rule) (σ : Subst) (is : List Nat) : List Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  is.filterMap fun i => match vs[i]?, r.vars[i]?, σ.lookup i with
    | some v, some s, some g => some (.equals (srtOf c s) C (.var (.evar v.kore)) (g.kore c))
    | _, _, _ => none

/-- **The instances of an application.** `∃ē. (rhs ∧ ens ∧ post)` with every variable but the
`exs` fixed to its value under σ. -/
def famEx (c : Semantics) (r : Rule) (σ : Subst) : KoreAML.P :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let fixed := (List.range r.vars.length).filter fun i => !r.exs.contains i
  KoreAML.denB (KoreAML.existsAll C ((fixed.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C (fixK c r σ fixed ++ [ruleRight c r])))

/-- **The outcomes of a match.** `∃ō. (⌈req⌉ ∧ pre ∧ ∃ē. (rhs ∧ ens ∧ post))` with the variables
the left side binds fixed to their values under σ, ō the others less `exs`. -/
def famOpen (c : Semantics) (r : Rule) (σ : Subst) : KoreAML.P :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let outer := (List.range r.vars.length).filter fun i => !r.exs.contains i
  KoreAML.denB (KoreAML.existsAll C ((outer.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C (fixK c r σ (varOccs r.lhs) ++ [reqPat C (r.req.map (Term.kore c vs))] ++
      Cond.conj c vs C r.pre ++ [ruleRight c r])))

/-! ## The statements -/

/-- No constructor is named like `ite` at a sort (`iteSort?`): `Term.kore` and the KORE of a value
then write a constructor's application alike. -/
def NamesPlain (c : Semantics) : Prop := ∀ k ∈ c.ctorSigs, iteSort? (c.symName k.name) = none

/-- The well-formedness of names and sort numbers that the soundness proof reads: no constructor
is named like `ite` at a sort (so `Term.kore` and the KORE of a value write its applications
alike), no symbol that an overloading symbol overloads is (an overload's equation, `ovlEqItem`,
writes the overloaded symbol under its name with no sort argument, which is how `symApp` writes it
then), and the sorts of every function are numbered sorts (so `ΓSig` says that each denotes one
sort). A function no symbol overloads may be named like `ite` at a sort: its equations
(`eqnSentence`) and its applications are both written by `symApp`. -/
def NamesNumbered (c : Semantics) : Prop :=
  NamesPlain c ∧ (∀ o ∈ c.ovls, ∀ g ∈ o.over, iteSort? (c.symName g) = none) ∧
  ∀ fn ∈ c.allFns, ∀ s ∈ fn.result :: fn.args, s < nRegSorts + c.sortNames.length

/-- Under `NamesPlain`, `symApp` writes a constructor at its name, at no sort. This is the one
lemma that reads `NamesPlain`'s condition on the name; the readers of `NamesPlain` go through it. -/
theorem namesPlain_writes_irs {c : Semantics} (hnm : NamesPlain c) {k : CtorSig} (hk : k ∈ c.ctorSigs) :
    ∀ ps, symApp c k.name ps = .app ⟨⟨c.symName k.name⟩⟩ [] ps := by
  intro ps; unfold symApp; rw [hnm k hk]

/-- Under `NamesNumbered`, `symApp` writes a symbol an overloading symbol overloads at its name, at
no sort. The one lemma that reads the overload conjunct's condition on the name. -/
theorem namesNumbered_over_writes_irs {c : Semantics} (hnn : NamesNumbered c) {o : OvlSig} (ho : o ∈ c.ovls)
    {g : Sym} (hg : g ∈ o.over) : ∀ ps, symApp c g ps = .app ⟨⟨c.symName g⟩⟩ [] ps := by
  intro ps; unfold symApp; rw [hnn.2.1 o ho g hg]

theorem namesNumbered_spec {c : Semantics} (h : namesNumbered c = true) : NamesNumbered c := by
  simp only [namesNumbered, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none,
    decide_eq_true_eq] at h
  exact ⟨fun k hk => iteSort?_none_of_instDecode (h.1.1 k hk),
    fun o ho g hg => iteSort?_none_of_instDecode (h.1.2 o ho g hg), h.2⟩

/-- What the statements assume of a semantics: it is well formed (`okAll`), its function labels
are distinct and its subsorts closed (`srReady`), and what the decided conditions do not settle
holds of every function of the definition: it terminates at every argument list of its sorts (has
a result, defined or not), a function declared total has a defined result there, any two of its
equations of one priority are coherent where both apply (`ClausesAgree`), and each of its clauses
gives one result for any two of its matches at one argument list (`MatchIndependent`).

These obligations are stated for every function, not only for those the decided checks leave
open. They follow from `wf` and `Obligations` (`hyp_of`, HypWf.lean).

Last, the names and sort numbers are well formed (`NamesNumbered`), which is decidable on the data.
Its sort-number part is what `idsOK` checks. Its name part exists only because `Term.kore` writes a
symbol named `Lblite{X}` with a sort argument, as `Lblite{SortX}(…)`, where the KORE of a value and
a function's equations write a symbol under its name. -/
def Hyp (c : Semantics) : Prop :=
  c.okAll = true ∧ c.srReady = true ∧
  (∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c fn.label vs r) ∧
  (∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) ∧
  (∀ fn ∈ c.fns, ClausesAgree c fn) ∧
  (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) ∧
  NamesNumbered c

/-- `Hyp` with `sortedOK` in place of `okAll`: the well-formedness its proofs read of the
clauses and rules (their sorts and variables, not the shape of their map patterns), of the subsorts,
and nothing of declarations, of the sorts' values or of clause-less functions. -/
def HypCore (c : Semantics) : Prop :=
  c.sortedOK = true ∧ c.srReady = true ∧
  (∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c fn.label vs r) ∧
  (∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) ∧
  (∀ fn ∈ c.fns, ClausesAgree c fn) ∧
  (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) ∧
  NamesNumbered c

/-- `Hyp` gives `HypCore` where no pattern applies a function-overloaded symbol (`ovlPatsOK`). -/
theorem Hyp.core {c : Semantics} (h : Hyp c) (hov : c.ovlPatsOK = true) : HypCore c :=
  ⟨Semantics.sortedOK_of_okAll h.1 hov, h.2⟩

/-- **Step soundness**: every step is a theorem of `Γ`, `⟦x⟧ → •⟦y⟧`: in every model of `Γ`, the
configuration x has the configuration y as a successor. -/
def StepSound (c : Semantics) : Prop :=
  Hyp c → ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val))

/-- **Step completeness**, for a step function `ref` that lists `Step`'s successors: with the
step's closure, every successor of x is one `ref` lists, `⟦x⟧ → ◦ ⋁_{y ∈ ref x} ⟦y⟧` (`◦⊥`, no
successor, where it lists none). -/
def StepComplete (c : Semantics) (ref : StepFn) : Prop :=
  Hyp c → StepIs c ref → ∀ x : Config c,
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c))))

/-- **Model existence**: `Γ` with the step's closure has a model, so the two statements above are
not vacuous. -/
def HasModel (c : Semantics) : Prop :=
  Hyp c → ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c)

end Faithful

open Faithful ML

/-- The pattern of an outcome: a value's, or the family of a match (`famOpen`). -/
def Outcome.pat (c : Semantics) : Outcome → KoreAML.P
  | .val y => den c y
  | .fam r σ => famOpen c r σ

/-! ## Conditions over variables the left side does not bind, in the theory -/

/-- `∃ō. (⌈req = true⌉ ∧ pre)`, ō the variables of the conditions: closed where `reqClosed`. -/
def Rule.condK (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  KoreAML.existsAll C
    ((((List.range r.vars.length).filter r.condVars.contains).filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and C ([reqPat C (r.req.map (Term.kore c vs))] ++ Cond.conj c vs C r.pre))
/-- No element of any model satisfies the rule's conditions. -/
def Rule.Refuted (c : Semantics) (r : Rule) : Prop := Γc c ⊧ ∼ KoreAML.denB (r.condK c)
/-- The text decides the rule's conditions. -/
def Rule.CondDecided (c : Semantics) (r : Rule) : Prop := r.Witnessed c ∨ r.Refuted c

/-- `∃ō. (⌈req = true⌉ ∧ pre)` at Bool, ō the variables of the conditions. -/
def Clause.condK (c : Semantics) (cl : Clause) : Kore.Pattern :=
  let B := srtOf c Srt.bool
  let vs := canonVars c cl.vars
  KoreAML.existsAll B
    ((((List.range cl.vars.length).filter cl.condVars.contains).filterMap (vs[·]?)).map KoreAML.Var.kore)
    (.and B ([reqPat B (cl.req.map (Term.kore c vs))] ++ Cond.conj c vs B cl.pre))
/-- No element of any model satisfies the clause's conditions. -/
def Clause.Refuted (c : Semantics) (cl : Clause) : Prop := Γc c ⊧ ∼ KoreAML.denB (cl.condK c)
/-- The text decides the clause's conditions. -/
def Clause.CondDecided (c : Semantics) (cl : Clause) : Prop := cl.Witnessed c ∨ cl.Refuted c

/-- Every closed open condition of the definition is decided by the text. -/
def OpenDecided (c : Semantics) : Prop :=
  (∀ r ∈ c.rules, r.needsWitness c = true → r.CondDecided c) ∧
  (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)

/-! ## The laws of open generators -/

/-- The interpretation satisfies `f(f(a,b),d) = f(a,f(b,d))` at values of the sort s. -/
def OpenAssoc (c : Semantics) (f : Sym) (s : Srt) : Prop :=
  ∀ a b d, c.sortsOf [a, b, d] = some [s, s, s] →
    (c.paramVal f [a, b]).bind (fun ab => c.paramVal f [ab, d]) =
    (c.paramVal f [b, d]).bind (fun bd => c.paramVal f [a, bd])
/-- The interpretation satisfies `f(a,a) = a` at values of the sort s. -/
def OpenIdem (c : Semantics) (f : Sym) (s : Srt) : Prop :=
  ∀ a, c.sortOf a = some s → c.paramVal f [a, a] = some a
/-- The interpretation satisfies the laws the text writes for its open generators. -/
def OpenLaws (c : Semantics) : Prop :=
  ∀ k ∈ c.params, k.raw = true →
    (k.assoc = true → OpenAssoc c k.sig.name k.sig.result) ∧
    (k.idem = true → OpenIdem c k.sig.name k.sig.result)

/-- The interpretation gives each open generator a value at every argument list of its sorts:
the text's `functional` sentence for it, at values. -/
def OpenTotal (c : Semantics) : Prop :=
  ∀ k ∈ c.params, k.raw = true → ∀ vs, c.sortsOf vs = some k.sig.args →
    (c.paramVal k.sig.name vs).isSome = true

/-! ## The laws of functions -/

/-- The law at values: under every well-sorted substitution the two sides have the same results. -/
def LawAt (c : Semantics) (l : LawEq) : Prop :=
  ∀ σ, c.WellSorted l.vars σ → ∀ r, EvalTerm c σ l.lhs r ↔ EvalTerm c σ l.rhs r

/-- The interpretation satisfies, at values, the laws the text writes. -/
def FnLaws (c : Semantics) (ls : List LawEq) : Prop := ∀ l ∈ ls, LawAt c l

/-- Both sides of the law have one sort in the context of right sides, that sort is one of the
definition's, and each of the law's variables occurs in a side. A sort that is none of the
definition's has no name of its own (`sortName` gives every such sort one name), so a sentence
over it would speak of whichever sort of the definition bears that name. -/
def lawSorted (c : Semantics) (l : LawEq) : Bool :=
  let x := c.rhsCtx (c.fns.map Fn.sig)
  (sortOfTerm x l.vars l.lhs).any (· < nRegSorts + c.sortNames.length) &&
    sortOfTerm x l.vars l.lhs == sortOfTerm x l.vars l.rhs &&
    binds l.vars.length (varOccs l.lhs ++ varOccs l.rhs)

/-- The law's sentence, `axiom{R} \equals{S,R}(lhs, rhs)` (S the sort of its left side; its
variables free, so universal), translated as `kernelItems` translates an axiom. -/
def lawPattern (c : Semantics) (l : LawEq) : KoreAML.P :=
  let vs := canonVars c l.vars
  let S := srtOf c ((sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) l.vars l.lhs).getD 0)
  (KoreAML.trAxiom [] [] ⟨0, "kernel",
    { sortVars := [KoreAML.Rv], pattern := .equals S KoreAML.R (Term.kore c vs l.lhs) (Term.kore c vs l.rhs),
      attributes := [] }⟩).pat

end KCore
