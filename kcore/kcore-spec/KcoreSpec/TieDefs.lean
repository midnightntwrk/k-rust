/-
  The statement definitions of the per-sentence tie between a KORE text `k` and a definition `d`:
  what "entailed at values" means (`AtValues`, `EntailsAtValues`, and for a sentence with free set
  variables `SetVarsAtValues`, `EntailsAtSetValues`, `SetVarsAtMostOne`), the agreement of the attributes
  the translation does not read (`attrsAgree`), the symbols a sentence applies (`symbolsOf`) and the
  items of the signature that are about a name the text does not declare (`surplusItem`), and the
  classes of an account with their directions (`tieClasses`).

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

/-- The valuation `e` sends each free set variable of the axiom `a` into the values of the
variable's sort: every element of the set is one that the pattern of some ground value of that
sort denotes. -/
def SetVarsAtValues (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M)
    (a : Kore.Axiom) : Prop :=
  ∀ n s, KoreAML.VarKey.svar n s ∈ (KoreAML.freeOf [] a.pattern).eraseDups →
    ∀ m, e.evalSvar ((KoreAML.tableOf a.sortVars a.pattern).sv (.svar n s)) m →
      ∃ (v : GroundTerm) (S : Srt), srtOf c S = s ∧ c.sortOf v = some S ∧ (den c v).interpret I e m

/-- `EntailsAtValues` for an axiom with free set variables: `φ` holds in every model of `Γ c` at
every valuation that sends the free element variables of the axiom `ad` to values (`AtValues`) and
each of its free set variables to a set of elements of values (`SetVarsAtValues`). A model may hold
elements of a sort that are no value's, and a set variable may hold them as an element variable
may. -/
def EntailsAtSetValues (c : Semantics) (ad : KoreAML.AxiomDecl) (φ : KoreAML.P) : Prop :=
  ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c →
    ∀ e, AtValues c I e ad.ax → SetVarsAtValues c I e ad.ax → ∀ m, φ.interpret I e m

/-- Each free set variable of the axiom `a` holds at most one element under the valuation `e`. -/
def SetVarsAtMostOne {M : Type} (e : Valuation M) (a : Kore.Axiom) : Prop :=
  ∀ n s, KoreAML.VarKey.svar n s ∈ (KoreAML.freeOf [] a.pattern).eraseDups →
    ∀ m m', e.evalSvar ((KoreAML.tableOf a.sortVars a.pattern).sv (.svar n s)) m →
      e.evalSvar ((KoreAML.tableOf a.sortVars a.pattern).sv (.svar n s)) m' → m = m'

/-- What is entailed at values is entailed at set values: the second asks it at fewer valuations. -/
theorem entailsAtSetValues_of {c : Semantics} {ad : KoreAML.AxiomDecl} {φ : KoreAML.P}
    (h : EntailsAtValues c ad φ) : EntailsAtSetValues c ad φ :=
  fun M inst I hI e hav _ m => h M inst I hI e hav m

/-- For an axiom without a free set variable the two are the same statement: `SetVarsAtValues`
holds of every valuation. -/
theorem entailsAtValues_of_noSetVar {c : Semantics} {ad : KoreAML.AxiomDecl} {φ : KoreAML.P}
    (hno : ∀ n s, KoreAML.VarKey.svar n s ∉ (KoreAML.freeOf [] ad.ax.pattern).eraseDups)
    (h : EntailsAtSetValues c ad φ) : EntailsAtValues c ad φ :=
  fun M inst I hI e hav m => h M inst I hI e hav (fun n s hn => absurd hn (hno n s)) m

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

/-- The number a non-empty string of decimal digits writes. Read off the string's characters, so
that the kernel reduces it at a literal (it does not reduce `String.toNat?`). -/
def digitsNat (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun a ch => a * 10 + (ch.toNat - 48)) 0)

/-- The priority an axiom's attributes state: 200 for `owise`, n for `priority{}("n")`, 50
otherwise. -/
def prioOf (as : List Kore.AppPattern) : Nat :=
  if has as "owise" then 200 else match (strArg as "priority").bind digitsNat with
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

/-- A law sentence: an equation without premise between terms, marked `assoc`, `comm`, `unit` or
`idem`, that states no priority (no `owise`, no `priority`). It states a law of the symbol at its
head, and is no equation of it. -/
def isLaw (a : Kore.Axiom) : Bool :=
  (has a.attributes "assoc" || has a.attributes "comm" || has a.attributes "unit" || has a.attributes "idem") &&
    !has a.attributes "owise" && !has a.attributes "priority" &&
  match a.pattern with
  | .equals _ _ (.app _ _ _) _ => true
  | _ => false

/-- The text's equations of the symbol `n`: the axioms with `n` at the head of their left side
that are no law sentence (`isLaw`). -/
def eqnsOf (k : Kore.Definition) (n : String) : List Kore.Axiom :=
  (k.axiomDecls.map (·.ax)).filter fun a => eqnHead a.pattern == some n && !isLaw a

/-- A function of the semantics is declared `function{}` without a hook, and a symbol declared so
that the theory has as a constructor, function, parameter or overloading symbol is a function of
the semantics, or a function without equations: a symbol the theory has only as a parameter that
no registry hook interprets (`impl = none`) and that is no open generator (`raw = false`), of
which the text states no equation (`eqnsOf`; a law sentence is no equation). Such a parameter's
value is the interpretation's, as is the value of a function where no clause applies, which with
no clause is everywhere. Two kinds of symbol declared so are not compared here: one the theory does
not have (its sentences have no direction), and one the registry interprets (`hookSigs`), which
`hooks` admits only where the registry holds it under no hook name (a library function such as
`freshInt`, which the text defines by an equation and the theory states by its graph; the equation
is a library sentence of the tie, entailed at values). -/
def fns (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all fun (n, as) =>
    let fn := has as "function" && !has as "hook"
    let isFn := c.allFns.any (c.symName ·.label == n)
    let own := (c.ctorSigs ++ c.params.map (·.sig) ++ c.ovlSigs).any (c.symName ·.name == n)
    let par := !(c.ctorSigs ++ c.ovlSigs).any (c.symName ·.name == n) &&
      (c.params.all fun p => c.symName p.sig.name != n || (p.impl.isNone && !p.raw)) && (eqnsOf k n).isEmpty
    (!isFn || fn) && (!(fn && own) || isFn || par)

/-- The interpreted hooked symbol `g` is one the registry holds under no hook name
(`regHookNames`): a function of the library's text with equations and no `hook` attribute. -/
def libFn (g : CtorSig) : Bool := !regHookNames.any (·.1 == g.name)

/-- A symbol declared with `hook{}("h")` that the theory has is an interpreted hooked symbol whose
registry hook is `h`'s (`regHookOf`), or a parameter symbol whose `impl` is `h`'s registry hook.
A symbol declared without a hook is an interpreted hooked symbol only where the registry holds it
under no hook name (`libFn`) and the text declares it `function{}`; it is a parameter symbol only
where no registry hook interprets the parameter (`impl = none`), the text states no equation of it
(`eqnsOf`), and it is an open generator (`raw`) exactly where the text does not declare it
`function{}`: an open generator is a parameter declared without hook and without function, and a
parameter declared `function{}` without hook is a function without equations. -/
def hooks (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all (fun (n, as) =>
    match strArg as "hook" with
    | some h =>
      (hookSigs.all fun g => c.symName g.name != n || regHookOf h == some g.name) &&
      (c.params.all fun p => c.symName p.sig.name != n || p.impl == regHookOf h)
    | none =>
      (hookSigs.all fun g => c.symName g.name != n || (libFn g && has as "function")) &&
      c.params.all fun p => c.symName p.sig.name != n ||
        (p.impl.isNone && (p.raw != has as "function") && (eqnsOf k n).isEmpty))

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

/-- The id an axiom's attributes state (`UNIQUE'Unds'ID{}("…")`). -/
def uidOf (as : List Kore.AppPattern) : Option String := strArg as "UNIQUE'Unds'ID"

/-- The priority of the text's rewrite axiom whose id is `u`. -/
def rewritePrioOf (k : Kore.Definition) (u : String) : Option Nat :=
  ((k.axiomDecls.map (·.ax)).find? fun a => isRewrite a.pattern && uidOf a.attributes == some u).map
    (prioOf ·.attributes)

/-- Each rule's priority is the priority of the text's rewrite axiom it is read from, the axiom
whose id the rule's presentation holds (`RulePres.info`; the rules a reading makes of one axiom,
`orSplit`'s, each hold that axiom's id), and every rewrite axiom of the text is read as some rule.
For each function of the semantics, the priorities of the text's equations of the function
(`eqnsOf`: with the function at the head of their left side, and no law sentence, which states a
law and no priority), less the `simplification` ones, are its clauses' priorities, as lists up to
order. The semantics need not hold a function's clauses in text order, so which equation has
which priority is not compared here. It is decided where a tie pairs each clause's item with its
sentence: for an `owise` equation by the pattern, which states the exclusion; for two equations of
one function with distinct `priority{}` numbers, where the text states the attribute only, by the
priorities of the paired sentences in the items' order, which a tie of such a text states. -/
def prios (k : Kore.Definition) (d : Definition) : Bool :=
  let c := d.sem
  let axs := k.axiomDecls.map (·.ax)
  d.pres.rules.length == c.rules.length &&
  ((c.rules.zip d.pres.rules).all fun (r, rp) => rewritePrioOf k rp.info.uid == some r.prio) &&
  ((axs.filter (isRewrite ·.pattern)).all fun a => d.pres.rules.any fun rp => uidOf a.attributes == some rp.info.uid) &&
  c.allFns.all fun f =>
    (((eqnsOf k (c.symName f.label)).filter (!has ·.attributes "simplification")).map
        (prioOf ·.attributes)).isPerm (f.clauses.map (·.prio))

end AttrsAgree

/-- **The attributes agree**: what the definition `d` holds that the text `k` states by attribute
only is what the attributes say (`AttrsAgree.ctors`, `fns`, `hooks`, `colls`, `prios`). -/
def attrsAgree (k : Kore.Definition) (d : Definition) : Bool :=
  AttrsAgree.ctors k d.sem && AttrsAgree.fns k d.sem && AttrsAgree.hooks k d.sem &&
    AttrsAgree.colls k d.sem && AttrsAgree.prios k d

/-! ## The classes of a tie and their directions -/

/-- What a tie shows of a sentence `s` of a class, for every interpretation of the hooks. -/
inductive TieDir where
  /-- An item of `Γ` is the translation of `s`, as written or with its variables renamed: `Γ` entails
  `s`, and the item is a consequence of `s`. -/
  | equal
  /-- `Γ ⊧ tr s`. -/
  | entailed
  /-- `tr s` entails the item `Γ` holds for `s`, which adds a premise to it. -/
  | weaker
  /-- `tr s` holds in every model of `Γ` at the valuations that send its variables to values
  (`EntailsAtValues`). -/
  | atValues
  /-- `Γ` does not hold `s`: it is owed as a hypothesis (`FnHyp` for a function's `functional`
  sentence, `FnLaws` for a law, `OpenTotal` for an open generator's `functional` sentence, and for
  a parameter lemma the sentence itself at the member, `Γ (c.withHooks H) ⊧ tr s`). -/
  | hypothesis
  /-- `Γ` with `s` has no model. -/
  | refuted
  /-- `s` applies a symbol `Γ` does not have: no statement relates them. -/
  | none
  deriving DecidableEq, Repr

/-- **The classes of a tie's account, each with its direction.** A text's account lists its
sentences under these names, in this order.
- function equation: an equation of a function of the semantics, `owise` or without priority;
- rewrite rule: `Γ`'s item has the premise that the right side with the `ensures` is defined;
- priority equation: an equation with `priority{}` that is not `owise`, whose item adds the
  negations of the clauses of a smaller priority;
- constructor functional, subsort, injectivity, distinctness, no junk: the constructor sentences;
- function functional: the `functional` sentence of a function of the semantics;
- hooked functional: the `functional` sentence of a symbol the registry interprets;
- collection law: associativity and the units of a collection's concatenation;
- library: an equation or a lemma of the builtin library over symbols `Γ` has;
- set idempotence: `_Set_(K, K) = K`, against which `Γ` states the concatenation of two sets with
  a common member undefined;
- set-variable lemma: a library lemma over set variables that `Γ` refutes at a valuation sending
  each free set variable to a set of values (`SetVarsAtValues`);
- function law: a law sentence (`AttrsAgree.isLaw`) whose head is a function or a parameter that is
  no open generator: the sentence of a law of the definition (`Definition.laws`), owed as `FnLaws`;
- open generator law: the `assoc` or `idem` sentence of an open generator, of which `Γ`'s law item
  is the translation;
- open generator functional: the `functional` sentence of an open generator, owed as `OpenTotal`;
- parameter lemma: a sentence the reader leaves out of `Γ` (a lemma) that applies a parameter
  symbol no registry hook interprets (`impl = none`), whose value the interpretation gives: owed as
  a hypothesis on `H`, the sentence itself at the member (`Γ (c.withHooks H) ⊧ tr s`);
- user lemma: a sentence of the user's text that the reader leaves out of `Γ` as a lemma
  (`InertReason.simplification`) and that applies no parameter symbol without `impl`, proved
  `Γ (c.withHooks H) ⊧ tr s` for every `H`;
- user lemma at values: the same, where the sentence holds at the valuations sending its variables
  to values (`EntailsAtValues`), because it rests on an interpreted symbol's graph;
- no direction: a sentence that applies a symbol `Γ` does not have. -/
def tieClasses : List (String × TieDir) :=
  [("function equation", .equal), ("rewrite rule", .weaker), ("priority equation", .weaker),
   ("constructor functional", .entailed), ("subsort", .entailed), ("injectivity", .entailed),
   ("distinctness", .entailed), ("no junk", .entailed), ("function functional", .hypothesis),
   ("hooked functional", .atValues), ("collection law", .atValues), ("library", .atValues),
   ("set idempotence", .refuted), ("set-variable lemma", .refuted), ("function law", .hypothesis),
   ("open generator law", .equal), ("open generator functional", .hypothesis),
   ("parameter lemma", .hypothesis), ("user lemma", .entailed), ("user lemma at values", .atValues),
   ("no direction", .none)]

/-! ## The no-direction class is closed -/

/-- Where the members of `l` in `p` are exactly those not in `q`, every member outside `p` is in
`q`: from an account's statement that the no-direction class holds exactly the sentences that
apply a symbol the theory lacks, every sentence outside it applies the theory's symbols only. -/
theorem tieAbsent_of_account {α : Type} (l : List α) (p q : α → Bool)
    (h : l.all (fun a => p a != q a) = true) : (l.filter (fun a => !p a)).all q = true := by
  refine List.all_eq_true.mpr fun a ha => ?_
  have hm : a ∈ l := (List.mem_filter.mp ha).1
  have hp : (!p a) = true := (List.mem_filter.mp ha).2
  have hpq : (p a != q a) = true := List.all_eq_true.mp h a hm
  cases hpa : p a with
  | true => rw [hpa] at hp; exact absurd hp (by decide)
  | false =>
    rw [hpa] at hpq
    cases hqa : q a with
    | true => rfl
    | false => rw [hqa] at hpq; exact absurd hpq (by decide)

end KCore
