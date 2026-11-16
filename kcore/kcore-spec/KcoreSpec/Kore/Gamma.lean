/-
  Γ_D's generated parts: Γ_cons's items (constructors, injections, no junk, domain values), the
  closure disjunct of a rule, the denotation of a ground pattern and all-path next. Reviewed
  layer (kept from F0's Curate, Closure and Statements when F0 was removed, P1.4); the core's
  statements (Statements.lean) assemble Γ_D from them.
-/
import KcoreSpec.Kore.Print
import KcoreSpec.Kore.Build

set_option autoImplicit false

namespace KoreAML

open ML

open ML

namespace Cons

/-- The AML sort constant of a sort name (`Nat` ↦ the symbol `SortNat`, as `trSort` gives). -/
def sortP (n : String) : P := sym (.sort ("Sort" ++ n))

def xs (offset n : Nat) : List EVar := (List.range n).map fun i => ⟨offset + i + 1⟩

/-- The pattern a generator of sort `N` builds from argument patterns. -/
def genPat (N : String) : Gen → List P → P
  | .ctor c, args => appList (sym (.symbol c.name)) args
  | .inj A, args => appList (sym (.symbol "inj")) ([sortP A, sortP N] ++ args)

def genName (N : String) : Gen → String
  | .ctor c => Print.unmangle (Print.dropPrefix "Lbl" c.name)
  | .inj A => "inj Sort" ++ A ++ " Sort" ++ N

def memGuards (vs : List EVar) (sorts : List String) : List P :=
  (vs.zip sorts).map fun (x, s) => x ∈∈ inhOf (sortP s)

def names (pre : String) (n : Nat) : List String := (List.range n).map fun i => s!"{pre}{i + 1}"

/-- Cons-Fun: a generator is a total function on its argument sorts,
`x̄ ∈ ⟦s̄⟧ → ∃y:N. g x̄ = y` ([FoSSaCS] §4.1 item 4, p. 208, (Function) form). -/
def funItem (N : String) (g : Gen) : Item :=
  let n := g.argSorts.length
  let x := xs 0 n
  let y : EVar := ⟨n + 1⟩
  { label := s!"cons-fun {genName N g}", rule := "Cons-Fun", names := names "x" n ++ ["y"]
    pat := guarded (memGuards x g.argSorts)
      (sExists y (sortP N) (genPat N g (x.map .evar) ≡ .evar y)) }

/-- Cons-Inj: `g x̄ = g ȳ → x̄ = ȳ` ([FoSSaCS] §4.2 item 1, p. 210). -/
def injItem (N : String) (g : Gen) : Item :=
  let n := g.argSorts.length
  let x := xs 0 n
  let y := xs n n
  { label := s!"cons-inj {genName N g}", rule := "Cons-Inj", names := names "x" n ++ names "y" n
    pat := guarded (memGuards x g.argSorts ++ memGuards y g.argSorts)
      ((genPat N g (x.map .evar) ≡ genPat N g (y.map .evar)) ⇒
        conjList ((x.zip y).map fun (a, b) => .evar a ≡ .evar b)) }

/-- Cons-Dist: `g x̄ ≠ g' ȳ` for two generators of one sort ([FoSSaCS] §4.2 item 2, p. 210). -/
def distItem (N : String) (g g' : Gen) : Item :=
  let n := g.argSorts.length
  let m := g'.argSorts.length
  let x := xs 0 n
  let y := xs n m
  { label := s!"cons-dist {genName N g} / {genName N g'}", rule := "Cons-Dist"
    names := names "x" n ++ names "y" m
    pat := guarded (memGuards x g.argSorts ++ memGuards y g'.argSorts)
      (notEqual (genPat N g (x.map .evar)) (genPat N g' (y.map .evar))) }

/-- x, of sort B, lies in the sort A below B: `∃z:A. x = inj{A,B}(z)`. -/
def liesP (A B : String) (x : P) (z : EVar) : P :=
  sExists z (sortP A) (x ≡ appList (sym (.symbol "inj")) [sortP A, sortP B, .evar z])

/-- The arguments x̄ of sorts `bs` are covered by no overload whose argument sorts are among
`covs`: for each, some argument does not lie in its sort there (a position where that sort is the
argument's own is always covered). -/
def uncoveredP (bs : List String) (covs : List (List String)) (x : List EVar) (z : EVar) : P :=
  conjList (covs.map fun as => disjList (((as.zip bs).zip x).filterMap fun ((A, B), xi) =>
    if A == B then none else some (∼(liesP A B (.evar xi) z))))

/-- Cons-Dist at uncovered arguments: `g x̄ ≠ g' ȳ` where the arguments of each overloading
generator among the two are covered by none of its overloads (`ug`, `ug'`: the argument sorts of
its overloads, `none` for a generator that is no overloading symbol). -/
def distUncItem (N : String) (g g' : Gen) (ug ug' : Option (List (List String))) : Item :=
  let n := g.argSorts.length
  let m := g'.argSorts.length
  let x := xs 0 n
  let y := xs n m
  let z : EVar := ⟨n + m + 1⟩
  let unc := fun (u : Option (List (List String))) (bs : List String) (vs : List EVar) => match u with
    | some covs => [uncoveredP bs covs vs z]
    | none => []
  { label := s!"cons-dist-uncovered {genName N g} / {genName N g'}", rule := "Cons-Dist-Unc"
    names := names "x" n ++ names "y" m
    pat := guarded (memGuards x g.argSorts ++ memGuards y g'.argSorts ++ unc ug g.argSorts x ++
        unc ug' g'.argSorts y)
      (notEqual (genPat N g (x.map .evar)) (genPat N g' (y.map .evar))) }

/-- An overload equation: `f(lift ā) = lift (g(ā))` for the symbol `f` overloading `g`, `lift`
the injection between two different sorts. -/
def ovlEqItem (f g : CtorSig) : Item :=
  let n := g.args.length
  let x := xs 0 n
  let liftP := fun (A B : String) (φ : P) =>
    if A == B then φ else appList (sym (.symbol "inj")) [sortP A, sortP B, φ]
  { label := s!"ovl-eq {genName "" (.ctor f)} / {genName "" (.ctor g)}", rule := "Ovl-Eq"
    names := names "x" n
    pat := guarded (memGuards x g.args)
      (appList (sym (.symbol f.name)) (((g.args.zip f.args).zip x).map fun ((A, B), xi) => liftP A B (.evar xi)) ≡
        liftP g.result f.result (appList (sym (.symbol g.name)) (x.map .evar))) }

/-- Cons-Coh: `inj{B,C}(inj{A,B}(x)) = inj{A,C}(x)` for a chain `A < B < C`
([AML-TR] §6, pp. 16–17: the triangle that coercions must satisfy). -/
def cohItem (A B C : String) : Item :=
  let x : EVar := ⟨1⟩
  let inj := fun (s t : String) (φ : P) => appList (sym (.symbol "inj")) [sortP s, sortP t, φ]
  { label := s!"cons-coh Sort{A} < Sort{B} < Sort{C}", rule := "Cons-Coh", names := ["x"]
    pat := guarded [x ∈∈ inhOf (sortP A)] (inj B C (inj A B (.evar x)) ≡ inj A C (.evar x)) }

/-- The text's no-junk sentence of the sort N with the generators `gs`:
`\or{N}(\exists{N}(x̄, g(x̄)), …, \bottom{N}())`, every element of N is a generator applied to
elements of its argument sorts (an injection `inj{A,N}` applied to an element of A).
`noJunkDisjuncts` writes the disjuncts, the closing `\bottom` among them. -/
def noJunkAx (N : String) (gs : List Gen) : Kore.Axiom :=
  { sortVars := [], pattern := .or (srt N) (noJunkDisjuncts N [] gs), attributes := [] }

/-- Cons-NoJunk: the translation (T-axiom) of the text's sentence `noJunkAx`, `⟦disjuncts⟧ = ⊤_N`. -/
def noJunkItem (N : String) (gs : List Gen) : Item :=
  { trAxiom [] [] ⟨0, "kernel", noJunkAx N gs⟩ with label := s!"cons-nojunk Sort{N}", rule := "Cons-NoJunk" }

end Cons

/-- `s ∈ ⟦Sort⟧ → ∃y:s. dv"v" s = y`: the domain value `\dv{s}("v")` denotes one element.
NOT part of Γ_D (decision D1 keeps T-dv's arity-only reading for milestone 1); it is assumed only
where STATEMENTS.md asks for a model in which ground configurations denote single elements. -/
def dvFunItem (lit : String) : Item :=
  let s : EVar := ⟨1⟩
  let y : EVar := ⟨2⟩
  { label := s!"dv-fun \"{lit}\"", rule := "DV-Fun", names := ["s", "y"]
    pat := guarded [sortGuard s] (sExists y (.evar s) (sym (.dv lit) ⬝ .evar s ≡ .evar y)) }

def dvFunctional : Premises Sym := fun φ => ∃ lit : String, φ = (dvFunItem lit).pat

/-- The premises a list of items denotes, with aml-port's `definedness` at every variable
(as `Theory.premises`). -/
def itemsPremises (its : List Item) : Premises Sym :=
  fun φ => (∃ it ∈ its, it.pat = φ) ∨ ∃ x : EVar, φ = @definedness Sym _ x

/-- G-dv-arity for every literal string: `s ∈ ⟦Sort⟧ → dv"v" s ⊆ ⟦s⟧`, an infinite schema.
The encoding (`Theory.ofDefinition`) lists the instances for the literals occurring in D; ground
configurations may contain any literal (`\dv{SortInt{}}("5")`), and without its arity axiom such a
literal could denote elements outside its sort (review finding 1). Arity only: no functionality,
no distinctness (decision D1). -/
def dvArityAll : Premises Sym := fun φ => ∃ lit : String, φ = (dvArityItem lit).pat

open ML

/-- One rule's disjunct, `∃x̄:s̄. (L ∧ y ∈ R)`, for the rule axiom `\rewrites{C}(L, R)`, with the
rule's variables numbered from `offset + 1` (so that the disjuncts of different rules use disjoint
indices), and the names of those variables. -/
def closureDisjunct (aliases : List String) (offset : Nat) (y : EVar) (pat : Kore.Pattern) :
    List String × P :=
  let t0 := tableOf [] pat
  let table : VarTable := List.replicate offset (.sortVar "#pad") ++ t0
  let c : Ctx := ⟨table, aliases⟩
  let (L, R) := match pat with
    | .rewrites _ l r => (tr c l, tr c r)
    | _ => (⊥, ⊥)
  let free := (freeOf [] pat).eraseDups.filterMap fun
    | k@(.evar _ s) => some (k, s)
    | _ => none
  (t0.map VarKey.name,
   free.foldr (fun (k, s) φ => sExists (table.ev k) (trSort table s) φ) (L ⋀ (y ∈∈ R)))

open ML

/-- ⟦t⟧: the AML pattern of a ground term, by the translation (T-app, T-dv). It has no free
variable, so its interpretation does not depend on the valuation. -/
def den (t : Kore.Pattern) : P := tr ⟨[], []⟩ t

/-- ⟦t⟧ for a KORE pattern that binds variables: each variable at its own index (`tableOf`).
For a pattern without variables it is `den`. -/
def denB (t : Kore.Pattern) : P := tr ⟨tableOf [] t, []⟩ t

theorem denB_ground {t : Kore.Pattern} (h : tableOf [] t = []) : denB t = den t := by rw [denB, den, h]

/-- The valuation used to read closed patterns. -/
def val0 {M : Type} [Inhabited M] : Valuation M := ⟨fun _ => default, fun _ _ => False⟩

/-- `◦φ ≡ ¬•¬φ`, all-path next (OOPSLA 2023 p. 13): every successor matches φ.
`◦⊥` is `¬•⊤`: no successor. -/
def allNext (φ : P) : P := ∼(sNext (∼φ))

end KoreAML
