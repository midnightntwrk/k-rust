/-
  The statement definitions of the per-sentence tie between a KORE text `k` and a definition `d`:
  what "entailed at values" means (`AtValues`, `EntailsAtValues`), the agreement of the attributes
  the translation does not read (`attrsAgree`), the symbols a sentence applies (`symbolsOf`) and the
  items of the signature that are about a name the text does not declare (`surplusItem`).

  None of them unfolds `Parse.parse` or `Definition.emit`: each reads the two literals.
-/
import KcoreSpec.Faithful
import KcoreSpec.Definition

set_option autoImplicit false

namespace KCore

open ML Faithful

/-! ## Entailed at values -/

/-- The valuation `e` sends each free element variable of the axiom `a` to the element of a ground
value of the variable's sort: in the interpretation `I`, the variable's index in the axiom's table
holds an element that the pattern of some value `v` of that sort denotes. -/
def AtValues (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M)
    (a : Kore.Axiom) : Prop :=
  ∀ n s, KoreAML.VarKey.evar n s ∈ (KoreAML.freeOf [] a.pattern).eraseDups →
    ∃ (v : GroundTerm) (S : Srt), srtOf c S = s ∧ c.sortOf v = some S ∧
      (den c v).interpret I e (e.evalEvar ((KoreAML.tableOf a.sortVars a.pattern).ev (.evar n s)))

/-- `φ` holds in every model of `Γ c` at every valuation that sends the free element variables of
the axiom `ad` to values (`AtValues`). Weaker than `Γ c ⊧ φ`, which asks it at every valuation: the
graph of an interpreted symbol is stated at values, and a model may hold elements of a sort that
are no value's. -/
def EntailsAtValues (c : Semantics) (ad : KoreAML.AxiomDecl) (φ : KoreAML.P) : Prop :=
  ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c →
    ∀ e, AtValues c I e ad.ax → ∀ m, φ.interpret I e m

/-! ## The symbols a sentence applies -/

mutual
  /-- The names of the symbols a pattern applies, in order of occurrence, with repetitions (the
  injection `inj` among them; the sort arguments of an application are not listed). -/
  def symbolsOf : Kore.Pattern → List String
    | .app h _ ps | .leftAssoc h _ ps | .rightAssoc h _ ps => h.ident.name :: symbolsOfList ps
    | .var _ | .string _ | .top _ | .bottom _ | .dv _ _ => []
    | .not _ p | .next _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p | .ceil _ _ p
    | .floor _ _ p => symbolsOf p
    | .and _ ps | .or _ ps => symbolsOfList ps
    | .implies _ p q | .iff _ p q | .rewrites _ p q | .equals _ _ p q | .in _ _ p q =>
      symbolsOf p ++ symbolsOf q
    termination_by structural p => p
  def symbolsOfList : List Kore.Pattern → List String
    | [] => []
    | p :: ps => symbolsOf p ++ symbolsOfList ps
    termination_by structural ps => ps
end

/-! ## The signature's surplus -/

/-- A registry sort as a KORE sort, under the registry's name. -/
def regSrtK (s : Srt) : Kore.KSort := KoreAML.srt (regSortNames.getD s "")

/-- The item of the signature `it` is about a registry name the text `k` does not declare at that
shape: the sort constant of a registry sort that `k` declares with no sort parameter under no
declaration, or the arity of an interpreted hooked symbol (`hookSigs`) that `k` declares with no
sort parameter under no declaration. A name the text declares with sort parameters (`SortMInt{S}`,
`Lblite{S}`) is not declared at the shape the item states, so its item is surplus too. -/
def surplusItem (k : Kore.Definition) (it : KoreAML.Item) : Bool :=
  (List.range nRegSorts).any (fun s =>
    let n := "Sort" ++ regSortNames.getD s ""
    !(k.sortDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
      it.pat == (KoreAML.sortConstantItem ⟨n, [], false⟩).pat) ||
  hookSigs.any (fun h =>
    let n := regSymNames.getD h.name ""
    !(k.symbolDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
      it.pat == (KoreAML.arityItem ⟨n, [], h.args.map regSrtK, regSrtK h.result, false, []⟩).pat)

/-! ## Attribute agreement

The translation of a sentence reads no attribute. What a definition takes from attributes is
compared with the text here: which symbols are constructors, functions and hooked symbols and with
which hook, which symbols build a collection sort, and the priorities of rules and equations. -/

namespace AttrsAgree

/-- The argument of the attribute `a`, where it is one string (`hook{}("MAP.concat")`). -/
def strArg (as : List Kore.AppPattern) (a : String) : Option String :=
  (as.find? (·.head.ident.name == a)).bind fun p => match p.args with
    | [.string s] => some s
    | _ => none

/-- The argument of the attribute `a`, where it is one symbol applied to nothing
(`unit{}(Lbl'Stop'Map{}())`). -/
def symArg (as : List Kore.AppPattern) (a : String) : Option String :=
  (as.find? (·.head.ident.name == a)).bind fun p => match p.args with
    | [.app h _ []] => some h.ident.name
    | _ => none

def has (as : List Kore.AppPattern) (a : String) : Bool := as.any (·.head.ident.name == a)

/-- A symbol declaration: its name and attributes. -/
def symDecls (k : Kore.Definition) : List (String × List Kore.AppPattern) :=
  k.modules.flatMap fun m => m.sentences.filterMap fun
    | .symbol s => some (s.symbol.ident.ident.name, s.attributes)
    | .hookedSymbol s => some (s.symbol.ident.ident.name, s.attributes)
    | _ => none

/-- A sort declaration: its name (with `Sort`) and attributes. -/
def sortDecls (k : Kore.Definition) : List (String × List Kore.AppPattern) :=
  k.modules.flatMap fun m => m.sentences.filterMap fun
    | .sort s => some (s.sort.ident.name, s.attributes)
    | .hookedSort s => some (s.sort.ident.name, s.attributes)
    | _ => none

/-- The priority an axiom's attributes state: 200 for `owise`, n for `priority{}("n")`, 50
otherwise. -/
def prioOf (as : List Kore.AppPattern) : Nat :=
  if has as "owise" then 200 else match (strArg as "priority").bind String.toNat? with
    | some n => n
    | none => 50

/-- The symbol at the head of an equation's left side: `\implies{R}(prem, \equals{s, R}(f(…), _))`
or `\equals{s, R}(f(…), _)`. -/
def eqnHead : Kore.Pattern → Option String
  | .implies _ _ (.equals _ _ (.app h _ _) _) => some h.ident.name
  | .equals _ _ (.app h _ _) _ => some h.ident.name
  | _ => none

def isRewrite : Kore.Pattern → Bool
  | .rewrites _ _ _ => true
  | _ => false

/-- `constructor{}` is on exactly the symbols the semantics has as constructors. -/
def ctors (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all fun (n, as) => has as "constructor" == c.ctorSigs.any (c.symName ·.name == n)

/-- A function of the semantics is declared `function{}` without a hook, and a symbol declared so
that the theory has as a constructor, function, parameter or overloading symbol is a function of
the semantics. Two kinds of symbol declared so are not compared: one the theory does not have (its
sentences have no direction), and one the registry interprets (`hookSigs`: a library function such
as `freshInt`, which the text defines by an equation and the theory states by its graph). -/
def fns (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all fun (n, as) =>
    let fn := has as "function" && !has as "hook"
    let isFn := c.allFns.any (c.symName ·.label == n)
    let own := (c.ctorSigs ++ c.params.map (·.sig) ++ c.ovlSigs).any (c.symName ·.name == n)
    (!isFn || fn) && (!(fn && own) || isFn)

/-- A symbol declared with `hook{}("h")` that the theory has is an interpreted hooked symbol whose
registry hook is `h`'s (`regHookOf`), or a parameter symbol whose `impl` is `h`'s registry hook;
and every parameter symbol is declared with a hook. -/
def hooks (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all (fun (n, as) =>
    match strArg as "hook" with
    | some h =>
      (hookSigs.all fun g => c.symName g.name != n || regHookOf h == some g.name) &&
      (c.params.all fun p => c.symName p.sig.name != n || p.impl == regHookOf h)
    | none => c.params.all fun p => c.symName p.sig.name != n)

/-- A sort declared with `unit`, `element` and `concat` is a collection sort of the semantics with
those three symbols, and each of the semantics' own collection sorts is declared so. -/
def colls (k : Kore.Definition) (c : Semantics) : Bool :=
  let declared := (sortDecls k).filterMap fun (n, as) =>
    match symArg as "unit", symArg as "element", symArg as "concat" with
    | some u, some e, some cc => some (n, u, e, cc)
    | _, _, _ => none
  let own := fun (cs : CollSig) =>
    ("Sort" ++ c.sortName cs.sort, c.symName cs.unit, c.symName cs.elem, c.symName cs.concat)
  declared.all (fun x => c.allColls.any fun cs => own cs == x) &&
    c.colls.all fun cs => declared.contains (own cs)

/-- The priorities of the text's rewrite axioms, in text order, are the rules'; and for each
function of the semantics, the priorities of the text's equations with the function at the head of
their left side, less the `simplification` ones, are its clauses' priorities, as lists up to order
(the order of a function's clauses carries no meaning). -/
def prios (k : Kore.Definition) (c : Semantics) : Bool :=
  let axs := k.axiomDecls.map (·.ax)
  ((axs.filter (isRewrite ·.pattern)).map (prioOf ·.attributes) == c.rules.map (·.prio)) &&
  c.allFns.all fun f =>
    let n := c.symName f.label
    ((axs.filter fun a => eqnHead a.pattern == some n && !has a.attributes "simplification").map
        (prioOf ·.attributes)).isPerm (f.clauses.map (·.prio))

end AttrsAgree

/-- **The attributes agree**: what the definition `d` holds that the text `k` states by attribute
only is what the attributes say (`AttrsAgree.ctors`, `fns`, `hooks`, `colls`, `prios`). -/
def attrsAgree (k : Kore.Definition) (d : Definition) : Bool :=
  AttrsAgree.ctors k d.sem && AttrsAgree.fns k d.sem && AttrsAgree.hooks k d.sem &&
    AttrsAgree.colls k d.sem && AttrsAgree.prios k d.sem

end KCore
