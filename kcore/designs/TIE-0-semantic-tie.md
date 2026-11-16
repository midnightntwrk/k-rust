# TIE-0: the semantic tie (C14), its directions per sentence class, the converse, R-15, FD-C, and the spike

Nodes TIE-design and FD-C of `DONE-0-definition-of-done.md` section 2.1.
Lean tree read: `kcore-spec` at `1e306534` (`jj file show`), fixture `f2-examples/ens.kompile.kore`.
Nothing here was elaborated or run: every Lean block is marked **to run**.
"Shown" means shown by reading the quoted definition or text; "suspected" means argued, not checked.

## 0. Result in one paragraph

C14 layer 2 is statable on the literal `d` without `Parse.parse`, `emit` or `wf` (R-15 confirmed, section 4).
The single direction "Γ entails `tr s`" does not hold as written for every class the plan lists under it: `Γ` states hooked symbols by their graphs on ground values only, and its models may hold elements of Int, Bool and the token sorts that are no value's (`FaithfulColl.lean` header, quoted in F1), so a quantified sentence about a hooked symbol (a collection law, a `functional` axiom of a hook, a library lemma) is entailed at values only.
The table of section 1.3 therefore has four directions, not three: entailed as written (E), entailed at values (Ev), weaker with a guard (W), and Γ-only families (M).
The converse over `fnItems` and `ruleItems` is statable and is the cheap direction: each item is equal to, or a weakening of, the translation of one text sentence (section 2).
FD-C: no collection law is entailed as written, for any of the three sorts; each of the nine stated ones is entailed at values (suspected); idempotence is refuted (section 5).
Spike estimate: 900 to 1300 hand-written lines for every class except the 92 library equations and lemmas (rows 17 and 18), for which three samples are measured (section 6).

## 1. C14's statements on the literal `d`

### 1.1 Vocabulary fixed here

`k` is the generated `Kore.Definition` literal of the text, `d` the generated `KCore.Definition` literal, `c H := d.sem.withHooks H`.

Reading TR-1. `tr s` is the item `Theory.ofDefinition k` holds for `s`: `trAxiom k.symbolDecls k.aliasNames ad`, `ad` the member of `k.axiomDecls` for `s` (`Translate.lean:309`, `:441-458`).
Reason: this is the translation of the text as written, with the text's own declarations and aliases, and no value the reader produced occurs in it.
Reverse when: kernel evaluation through `k.symbolDecls` is too slow in the spike; then `trAxiom [] []` with a lemma that the two agree on an axiom whose top is a connective and which applies no alias (section 3).

Reading TR-2. "Entailed" has two strengths.
E: `Γ (c H) ⊧ (tr s).pat`.
Ev: in every model of `Γ (c H)`, at every valuation that sends each free element variable of `s` to the element of a ground value of its sort, `(tr s).pat` holds.
Reason: F1. Ev is what a theory that states graphs on values can give, and it is still a statement over all models of Γ and all H.
Reverse when: `Γ` gains an axiom family that excludes non-value elements from the hooked sorts (a cone change to `ΓDomains`); every Ev row then becomes E.

### 1.2 Statements (to run)

```lean
-- TO RUN. Fixture shape: a package with literals `Ens.kore : Kore.Definition`, `Ens.defn : KCore.Definition`.
namespace Ens.Tie
open KCore KCore.Faithful KoreAML ML

abbrev k := Ens.kore
abbrev d := Ens.defn
abbrev c (H : HookParams) : Semantics := d.sem.withHooks H

/-- The axioms of the user module, numbered as `axiomDecls` numbers them (1-based, text order). -/
def userAxioms : List AxiomDecl := k.axiomDecls.filter (·.module == "ENS")
/-- `tr s`. -/
def trS (ad : AxiomDecl) : Item := trAxiom k.symbolDecls k.aliasNames ad
theorem trS_is_text : (Theory.ofDefinition k).axioms = k.axiomDecls.map trS := rfl

-- Layer 1.
theorem tied : Tied k
-- where `wf d` fails on a conjunct `coreOK` does not ask (C14 part 1):
-- theorem tied' : Parse.parse k = .ok d ∧ Reordered d.emit k

-- Layer 2, one theorem per sentence, `ad` a literal member of `userAxioms`.
-- E
theorem s_entailed (H : HookParams) : Γ (c H) ⊧ (trS ad).pat

-- Ev, with a guard `G` on the values (True for a plain Ev row).
def AtValues (c : Semantics) {M : Type} (I : Interpretation Sym M) (e : Valuation M) (a : Kore.Axiom) : Prop :=
  ∀ n s, VarKey.evar n s ∈ (freeOf [] a.pattern).eraseDups →
    ∃ (v : GroundTerm) (S : Srt), srtOf c S = s ∧ c.sortOf v = some S ∧
      (den c v).interpret I e (e.evalEvar ((tableOf a.sortVars a.pattern).ev (.evar n s)))
def EntailsAtValues (c : Semantics) (ad : AxiomDecl) (φ : P) : Prop :=
  ∀ (M : Type) (_ : Inhabited M) (I : Interpretation Sym M), I ⊧ᴵP Γ c →
    ∀ e, AtValues c I e ad.ax → ∀ m, φ.interpret I e m
theorem s_entailed_at_values (H : HookParams) : EntailsAtValues (c H) ad (trS ad).pat

-- W: the item Γ holds for `s` is a consequence of `s` (W1), and Γ entails `s` at the values
-- outside the note's guard (W2: `AtValues` with the guard conjoined; for a rule, the right side
-- with its `ensures` is defined and no rule of a smaller priority applies).
theorem s_weaker (H : HookParams) :
    ∀ it, (ruleItems (c H))[j]? = some it → itemsPremises [trS ad] ⊧ it.pat

-- Non-vacuity (C14 closure (a)): at every H with FnDet and FnSolves,
theorem consistent (H : HookParams) (hd : FnDet (c H)) (hs : FnSolves (c H)) : Consistent (c H)
```

`AtValues` and `EntailsAtValues` are two new definitions; they are statements, belong beside `Consistent`, and are pinned with the C14 statements (C5 part 1).

### 1.3 The class-to-direction table

Counts are of `ens.kompile.kore`, user module `ENS` (lines 65 to 2743): 263 axioms, 127 symbol and 14 sort declarations.
Tops of the 263 axioms: `\implies` 146, `\exists` 94, `\or` 11, `\equals` 10, `\not` 1, `\rewrites` 1 (counted by script).

| # | Class (reader's class) | ens | Direction | Γ's part | Reason |
|---|---|---|---|---|---|
| 1 | rewrite rule (`read`) | 1 | W1 and W2 | `ΓRules` | `prioRuleK` (`Faithful.lean:535`) adds `¬ ⋁ competitors` and `⌈rhs ∧ ens⌉` to the text's left side; the right side is the text's. Γ's item is a weakening of the sentence, and Γ does not entail the sentence where the right side is empty or a smaller priority applies |
| 2 | function equation, no `ensures`, no clause of a smaller priority (`read`) | 0 | E and converse, by equality of patterns | `ΓFns` | `clauseEquation` (`:475`) and `clauseAx` (`Emit.lean:201`) build the same `equationAx (premise …)`; they differ in variable names and attributes, neither of which `trAxiom`'s `pat` keeps (section 2.1) |
| 3 | function equation with `ensures` (`readAs ensuresAsRequires` at `1e306534`) | 1 | at `1e306534`: W1 only, E and Ev fail at an H whose rest is a value where the clause fails (the defect); after lane CE expected as row 2 | `ΓFns`, `ΓFallback` | text `prem → f = r ∧ ⌈C⌉`, Γ `⌈C⌉ ∧ prem → f = r`: the text entails Γ's; Γ with `ΓFallback` states H's value where the text states ⊥ |
| 4 | `[owise]` equation (`read`) | 14 | E and converse; by equality where the binders' keys collide alike, else by an α-lemma (F6) | `ΓFns` | `competingEquation` (`:482`) and `clauseAx`'s `writtenOwise` branch have one shape |
| 5 | `priority(n)` equation, not `owise` | 0 | W1 only | `ΓFns` | `prioEquation` negates the smaller priorities for every clause; `clauseAx` writes the negation for `writtenOwise` only. A reading without a `ReadingNote` (C6 lists it) |
| 6 | generated equations: `isX` 15, cell initialisers and counter 4 | 19 | as row 2 | `ΓFns` (`allFns`) | functions of the semantics with clauses |
| 7 | generated `project:X` equations | 14 | corrected (TIE-1 D3): row 2's direction where a read sentence applies the projection (a function with the text's equation; where the text holds the selector-domain axiom, the clause of F-CE finding 8), none otherwise (principled limit, listed) | `ΓFns`, or none | `InertReason.projectionDomain` is removed (lane FX, b242cb79) |
| 8 | `functional` of a constructor (`read`) | 8 | E | `ΓCons`, `Cons.funItem` | same statement; the text's equality is sorted at `R`, `funItem`'s is not |
| 9 | `functional` of a hooked symbol (`read`) | 47 (corrected, TIE-1 D3: 7 of the 54 apply a hooked symbol Γ lacks and have no direction under `absent_closed`) | Ev | `ΓDomains` graph | the graph speaks of values; E fails (F1) |
| 10 | `functional` of a function (`isX`, initialisers, `freshInt`) | 17 | Ev under totality at values; not from Γ alone | none | "`Γ` holds no totality axiom, so a function's `[total]` attribute is not read" (`Consistent`'s doc). Read into `FnHyp`, not into Γ (F4) |
| 11 | `subsort` (`read`) | 15 | E | `ΓCons`, `funItem` of the `.inj` generator | `∃Val. Val = inj{A,B}(From)` is the injection's functionality |
| 12 | no confusion, same constructor (`inert injectivity`) | 6 | E | `Cons.injItem` with `funItem` | `c(x) ∧ c(y) ⊆ c(x ∧ y)` follows from injectivity and functionality |
| 13 | no confusion, different constructors (`inert distinctCtors`) | 1 | E for a pair not `distGuarded`; for a guarded pair the sentence is `unread overloadConfusion` and W1 | `Cons.distItem`, `distUncItem` | |
| 14 | no junk `\or` (`inert noJunk`; KItem's is `read`) | 11 | E | `Cons.noJunkItem` (constructor sorts); a logical truth for Int, Bool, KConfigVar (`\or(\top, \bottom)`) | Γ's least fixed point entails the text's disjunction; Γ says more (family, section 2.2) |
| 15 | collection law `assoc`, `unit` (`inert collectionLaw`) | 9 | Ev (section 5) | `ΓDomains` graph of the concatenation | E fails (F2) |
| 16 | `idem` (`unread setIdempotence`) | 1 | its own class, "refuted, recorded" (TIE-1 D5): `idem_refuted`, the guarded sentence at values, G7; builtin prose over attribute | `ΓDomains` | `ModelSetIdemWitness.not_model_idem` is this statement on a witness semantics |
| 17 | library equation, not `simplification` (builtin source, `read`) | 28 | Ev, one hook argument per sentence | `ΓDomains` graph (`freshInt` is in `hookSigs`) | the library's rule is not in Γ; its hook is |
| 18 | library `simplification` (builtin source), and one without source (`inert simplification`) | 64 | Ev, one hook argument per sentence | `ΓDomains` | a lemma about hooked symbols with variables |
| 19 | sort and symbol declarations (`read`) | 141 | G-sort and G-arity: E by equality for a declaration without sort parameters; G-nonempty and G-sorts: not entailed, stated limit (F5) | `ΓSig` | `sigItems`: "No sort is said to be inhabited (G-nonempty)" |
| 20 | `import`, `claim` | | none: `axiomDecls` holds axioms only, there is no `tr s` | | not statements of the theory |
| 21 | `readAs reflectionAsOwn`, `streamRule` | 0 | as the class the sentence is read as (rows 1, 19, 9 for a parameter) | | not in this fixture; not examined |

Rows 12 to 14 and 8, 11 need no H: the items do not read `c.hooks`.
A sentence of row 9, 10, 15, 17 or 18 is stated for every H because its graph is the first disjunct of `ΓDomains`, which reads `hook`, not `c.hooks`; none of the collection concatenations is a key of `silentTable` (shown, `silentTable`'s list), so `ΓFallback` states nothing at them.

## 2. The converse

### 2.1 `fnItems` and `ruleItems`: statable, and the cheap direction

Observation that carries it (shown): `trAxiom`'s `pat` depends on a variable's name only through its index in `tableOf`, the position of its first occurrence (`VarTable.index`, `Translate.lean:31`; `tableOf`, `:96`), and reads no attribute (`:317` filters them into `label` only).
Two axioms that differ by a renaming of variables that is injective on (name, sort) keys have the same `pat`.
So where Γ's sentence is the text's up to names, the two patterns are equal and the kernel checks it by evaluation (`rfl`); `ModelSetIdemWitness.lean:114-117` already evaluates `freeOf … |>.eraseDups` and `sortOf` on a text-shaped axiom by `decide +kernel`.

Form (to run):

```lean
-- TO RUN. `origin j` is the index in `userAxioms` of the sentence the j-th item comes from.
theorem fns_from_text (H : HookParams) :
    ∀ j it, (fnItems (c H))[j]? = some it →
      ∃ ad, userAxioms[originF j]? = some ad ∧ itemsPremises [trS ad] ⊧ it.pat
theorem rules_from_text (H : HookParams) :
    ∀ j it, (ruleItems (c H))[j]? = some it →
      ∃ ad, userAxioms[originR j]? = some ad ∧ itemsPremises [trS ad] ⊧ it.pat
```

Expected on every class: rows 2, 4, 6 by equality of `pat`; rows 1, 3, 5 by a weakening lemma (the premise of the item is the sentence's premise with conjuncts added).
No family is needed for these two parts: nothing in `fnItems` or `ruleItems` is more than a text sentence states. What Γ adds is all in the other five parts and in `Γstep`.
`fnItems (c H) = fnItems d.sem` and the same for `ruleItems`: neither reads `hooks` (the tree has this pattern as `kernel_rfl …_withHooks` lemmas).

### 2.2 The seven parts and their families

Statable in one theorem whose proof is a case split on `Γ`'s union (`Faithful.lean:561`), so that an eighth part breaks it (to run):

```lean
-- TO RUN.
inductive Family
  | dvArityAll                       -- ΓSig: dv arity at every literal, not only the text's
  | consNoJunk | injInjective | injDistinct | distLowerBound | distUncovered   -- ΓCons beyond the text
  | hookGraph | paramGraph | valueIsElement | valuesDistinct | collNoJunk      -- ΓDomains, its five disjuncts
  | collAxiom                        -- ΓColls
  | silentValue | restValue          -- ΓFallback, its two disjuncts
def Family.holds (c : Semantics) : Family → Premises Sym   -- each the disjunct or item list it names

theorem gamma_origin (H : HookParams) : ∀ φ, Γ (c H) φ →
    (∃ ad ∈ userAxioms, itemsPremises [trS ad] ⊧ φ) ∨          -- from a sentence
    (∃ it ∈ (Theory.ofDefinition k).signature, it.pat = φ) ∨    -- from a declaration
    (∃ ad ∈ k.axiomDecls, ad.module = "INJ" ∧ itemsPremises [trS ad] ⊧ φ) ∨   -- cohItem, from the prelude's inj axiom
    (∃ f : Family, f.holds (c H) φ) ∨ (∃ x : EVar, φ = definedness x)
```

| Part | Defined as | From the text | Families (rows of the pinned table) |
|---|---|---|---|
| `ΓSig` | `sigItems` list, and `dvArityAll` | G-def, G-sort, G-arity, ceil items, next arity: items of `Theory.ofDefinition k`'s signature | `dvArityAll`; `registrySignature` (TIE-1 D4: the registry's sorts and interpreted hooked symbols whether or not the text declares them, admitted per text by `sig_origin` and KItem's no-junk equality) |
| `ΓCons` | `consItemsK` list | `funItem` (rows 8, 11), `injItem` and `distItem` of constructors (12, 13), `cohItem` (module INJ's axiom), `ovlEqItem` (overload axioms) `noJunkItem` as a least fixed point until node NJ, then the text's sentence (no family) and `kNoJunk` for K, which has no sentence (TIE-1 D7); injectivity and distinctness of injections; `distLbItem`; `distUncItem` |
| `ΓDomains` | five disjuncts (`:204`) | none | one per disjunct; `paramGraph` reads H |
| `ΓColls` | `collAxioms` per kind (`:447`) | none ("KCore's own", `UnreadReason.setIdempotence`'s doc) | `collAxiom`: 4 map, 4 set, 5 list axioms |
| `ΓFns` | `itemsPremises (fnItems c)` | all (2.1) | none |
| `ΓRules` | `itemsPremises (ruleItems c)` | all (2.1) | none |
| `ΓFallback` | two disjuncts (`:230`) | none | `silentValue`, `restValue`; both read H; C6's `undetermined` statements are their guards |

For the three parts defined by predicates the family is the disjunct, so their case of `gamma_origin` is `Iff.rfl`-sized; the content is that the enumeration is forced by the definition.
`Γstep` is not part of `Γ`; it is a family of its own in the table (the closure), with no sentence.

Limit of the converse: it bounds `fnItems` and `ruleItems` by the text and names everything else; it does not say a family is true of K. Each family row needs its C6 guard or its trusted-base entry (hook graphs: the builtin prose, trusted base (4)).

## 3. What `trAxiom` needs of the declarations, and what it does not translate

Needs (shown, `Translate.lean:309-322`):
1. `decls`, only in `sortOf decls a.pattern`, only when the axiom's top is an application (`.app`, `.leftAssoc`, `.rightAssoc`); an undeclared head gives `untranslated "sort of the axiom"`. In ens no axiom of the user module has an application at its top (counts of 1.3), so no declaration is read.
2. `aliases`, at an alias application, which becomes `untranslated "alias …"`. The text declares aliases in module K (lines 59 to 61); the user module applies none (to check per text: one Bool over the user axioms).
Nothing else: `tr` does not check that an applied symbol or sort is declared, its arity, or the sorts of its arguments.
The tree has `tr_aliases` and `trAxiom_pat` (`Kore/ReorderTheory.lean`) for permuted declarations and alias lists that agree; a lemma for dropping both, under conditions 1 and 2, is not there (about 100 lines, or none if every equality is checked by evaluation with the text's lists).

Not translated; each is a stated limit (L) or a reader-trusted point (T):
- L1. Attributes, on every sentence (D-attributes): `tr s` is the same with and without `owise`, `priority`, `simplification`, `label`, `non-executable`, and on declarations `function`, `functional`, `total`, `constructor`, `injective`, `anywhere`, `hook`, `unit`/`element`/`concat`, `token`, `hasDomainValues`, `macro`, `symbol-overload`.
- T1. A rewrite rule's `priority` or `owise`: KORE states it by attribute only, so the competitors `prioRuleK` negates come from the reader's reading of the attribute. Layer 2 does not check it; the W2 guard names it. Reader-trusted, with C8's reader mutant as the only check.
- T2. `hook{}` on a symbol and `unit`/`element`/`concat` on a hooked sort: which interpretation and which symbols build a collection. Reader-trusted (`paramsOK`, `collOK` are conditions of `wf`, layer 1), and the builtin prose for the meaning.
- T3. `function` without equations, `constructor` without the generated axioms (a hooked sort has no no-junk axiom): the kind of a symbol is read from the attribute.
- L2. `\dv`: arity only (T-dv, `dvArityItem`); the text's theory does not say a literal denotes one element or that two differ. Γ's `valueIsElement` and `valuesDistinct` are families.
- L3. G-nonempty and G-sorts are in `Theory.ofDefinition k` and not in Γ (F5).
- L4. Sort-parametric declarations and axioms (`ite{S}`, `inj{S1,S2}`, `\exists … f{S}(…)`): translated with a guard over every sort; Γ states the instances at the definition's sorts. Entailed at instances only (`InertReason.parametricFunctional`).
- L5. Claims, imports, alias definitions, module structure: no translation.
- L6. `\rewrites` is translated as an implication into `•`; that a configuration steps only by a rule is no sentence (`Γstep`).

## 4. R-15: confirmed

Every statement of sections 1.2 and 2 mentions `k`, `d`, `Γ`, `Semantics.withHooks`, `trAxiom`, `Kore.Definition.symbolDecls`/`aliasNames`/`axiomDecls`, `itemsPremises`, `fnItems`, `ruleItems`, `⊧`.
None mentions `Parse.parse`, `Definition.emit` or `wf`. Layer 2 relates `d` to `k` directly; it does not even need `parse k = .ok d`. Only `Tied` (layer 1) unfolds the reader, and it is re-proved per text.
So the roots for C14 are `Γ` and `Translate.lean`'s translation, both already the theory layer, plus `AtValues`/`EntailsAtValues` if TR-2 stands.

The reversal criterion ("a library theorem obtained cheaply") does not fire:
- over `parse` (`∀ k d, parse k = .ok d → …`): needs an inversion of a 2409-line reader for which the tree has no lemma. Not cheap.
- over `emit` (`∀ d, wf d → every axiom of d.emit's user module holds in its direction`), which with `Tied` and `sameModels_of_reordered` (`Kore/ReorderTheory.lean`, present) would give layer 2 for every tied text at once: statable, and it would add `emit` to the roots, not `parse`. Its cost is one lemma per block of `userBlocks`, including the library's text (rows 17, 18): not cheap, estimated above 3000 lines. If it is ever wanted, the lanes to move before R2 are those that touch `Emit.lean`, not the reader's.

Per-text re-proof is therefore the form. A soundness-checked Bool (`tieCheck c a = true → Γ c ⊧ (trAxiom [] [] ⟨0, "kernel", a⟩).pat`, over a `Semantics` and an axiom, reading neither `parse` nor `emit`) is a proof device the spike may introduce to batch a class; it is not a root.

## 5. FD-C: does Γ entail the collection laws read as inert

What the text states (ens, lines 201 to 211 of the user module): associativity, right unit and left unit for `_List_`, `_Map_`, `_Set_` (nine axioms, `inert collectionLaw`), and idempotence for `_Set_` (`unread setIdempotence`). It states no `[comm]` axiom (F9).

Verdict as written (direction E): **not entailed, for every law and every sort**. Suspected: the left unit of Map by the sketch below, the other eight by the same reason without a worked model; no Lean lemma at `1e306534` states a collection law as a consequence of Γ (searched declaration names for `assoc`, `comm`, `unit`, `idem` over `KcoreSpec/`: only `ModelSetIdemWitness`).
Reason: `ΓDomains` gives the concatenation's graph on values; `ΓColls`' axioms each have a definedness premise or are a negation, so none makes a concatenation non-empty; and a model of Γ may hold a collection that is no value's.
Counter-model sketch for the left unit of Map: the intended model with one more element ω of Int, the constructor sorts closed freely over it, every hook and parameter empty on non-value arguments, except `elem(inj(ω), b₀) = {e}` for one new element e of Map and `concat(e, unit) = {e}`. `collNoJunk` holds (e is `concat(elem(inj ω, b₀), unit)`), the four map axioms hold (the only overlap involving e is `concat(e, unit)` with itself, decomposed with `y = unit`), and `concat(unit, e) = ∅ ≠ e`. This sketch refutes the left unit only. For the right unit and for associativity the same freedom is there (nothing in Γ makes `concat` non-empty on a non-value), but `collNoJunk` forces `e ∈ concat(elem(…), x)`, so their counter-models need more new elements and were not worked out. Settled by: the model in Lean (the first paragraph of `FaithfulColl.lean` describes its base), or by the orchestrator accepting Ev.

Verdict at values (direction Ev), per law and sort; each is suspected, and needs the hook's algebra, which no lemma states in entailment form:

| Law | Map | Set | List |
|---|---|---|---|
| associativity | holds: both sides are the union when the three key sets are pairwise apart and ⊥ otherwise. From `ΓDomains` disjunct 1 at `mapConcat` (as `FaithfulColl.concat_val` reads it), `union_spec`, `union_exists`, `entries_canon` (`MapLaws.lean`) | holds, same argument with `concatS` (`ModelColls.concatS_iff`, `concatS_of`) | holds: concatenation is total and associative |
| right unit, left unit | holds: `union a [] = a`, `union [] a = a` for a canonical `a` | holds: `concatS` with the empty set | holds |
| commutativity | not stated by the text; would hold | not stated; would hold | false, not stated |
| idempotence | not stated | **refuted**: at `K = SetItem(a)`, `hook setConcat [s, s] = some none` and it is not silent, so Γ entails `_Set_(K, K) = ⊥`. `ModelSetIdemWitness.not_model_idem` proves it for one semantics; "every semantics has the library's `Set`" (its header) | not stated |

Reading FD-1 (decided). `collectionLaw` is tied in direction Ev; no `ΓColls` change is required for C14 under TR-2.
Reason: the same limit holds for every quantified sentence about a hooked symbol (rows 9, 17, 18), so changing `ΓColls` would move nine sentences and leave more than a hundred; and `InertReason.collectionLaw`'s own words ("a law KCore's collection values satisfy by their representation") claim the law of values.
Reverse when: the orchestrator requires direction E for this class. The `ΓColls` change is then: `collAxioms` gains, per collection `k`, the text's own three axioms built from `k`'s symbols (`\equals{S,R}(concat(concat(K1,K2),K3), concat(K1,concat(K2,K3)))`, `\equals{S,R}(concat(K,unit),K)`, `\equals{S,R}(concat(unit,K),K)`), each as `trAxiom [] []` of that sentence so that E is membership and equality of patterns; no idempotence, no commutativity. It asserts nothing the text does not state. It adds to `Model.ModelColls` nine facts about the value model (the table's left three rows), about 350 lines, and changes no headline statement: more premises keep `sound_at` and `complete_at`, and `consistent_of` needs the nine facts.
What each reading makes provable: with the change, `Γ ⊧` the law at any elements, so a map pattern read at non-value elements can be reassociated inside a proof; without it, only at values. Nothing in `sound_hyp` or `complete_hyp` needs the former today (they hold at `1e306534` without it).

## 6. TIE-spike on `ens.kompile.kore`: cost, risks, and what decides TIE-decision

### 6.1 Cost

| Piece | Rows | Lines (hand) | Note |
|---|---|---|---|
| `AtValues`, `EntailsAtValues`, cut lemma (`(∀φ, Γ φ → T ⊧ φ) → Γ ⊧ ψ → T ⊧ ψ`) | all | 60 | |
| pattern equality by evaluation, membership in `ΓFns` (`f ∈ allFns → cl ∈ f.clauses → ΓFns c (item of prioEquation c f cl)`) | 2, 4, 6, 19 | 60 | 33 or 34 equations and 141 declarations close by `rfl` each |
| rule weakening: `guards ⇒ (sRewrites C (L ∧ q) R ≡ ⊤) ⊧ guards ⇒ (sRewrites C (L ∧ q ∧ X) R ≡ ⊤)` | 1, 3, 5 | 80 | uses `FaithfulTr.lean`'s `interp_*` |
| `funItem` to the sorted `functional`/`subsort` sentence | 8, 11 | 90 | `interp_sEquals`, `interp_sExists` |
| `injItem`, `distItem` to the no-confusion sentences | 12, 13 | 130 | |
| `noJunkItem` to the `\or` sentence; `\or(\top, \bottom)` | 14 | 150 | one unfolding of the fixed point; binders reuse `X0` across disjuncts |
| hooked `functional` at values | 9 | 100 if the tree has a lemma that a `functional` hook is defined at well-sorted values (`Totals.lean`, `ParamsTotal.lean` not read), else 54 lemmas, 300 to 800 | risk 2 |
| function `functional` at values | 10 | 80 | through `eval_den` and totality of `isX` |
| collection laws at values | 15 | 400 | map 150, set 120, list 40, glue 90 (`concat_val` exists for Map only) |
| idempotence refuted on `d` | 16 | 60 | `ModelSetIdemWitness` is the template |
| library equations | 17, 18 | 3 samples, 150 | the full 92 is one proof per library sentence, shared by every text: 1400 to 3600 lines, not in the spike |
| per-text statements | all | generated, about 8 lines a sentence, 2000 for ens | by a native generator; the kernel is the check |

Total hand-written: 900 to 1300 lines without the library equations, of which about 700 are lemmas every later fixture reuses.
The spike runs after lane CE; row 3 is then expected to be row 2. Before CE it is a negative control: the E statement for the `half` equation must fail to prove, and its refutation at the plan's `H7` is the check that the tie sees the defect.

### 6.2 Risky steps

1. Binder names (F6). `canonClausePres` gives an exclusion the equation's own names ("it may reuse the names of the equation it occurs in"), so in Γ's sentence an exclusion's variable and an outer variable of the same position and sort are one key; in the text they are two keys when the names differ. The patterns are then not equal although they mean the same, and since the negation comes first in the premise, the outer variables' indices shift too. The 14 `owise` sentences of ens are `isX` predicates (outer sort K, bound sort X), where no key collides on either side, so equality is expected. A user `owise` or a rule with competitors over one sort needs a lemma that `tr` does not depend on the table up to a renaming of keys (mutual over the seven functions of `tr`, 300 to 500 lines). The spike measures it on `f2-examples/ens-owise.kompile.kore` (one sentence) and reports whether `rfl` holds.
2. Totality of hooks at values, if no table lemma exists.
3. Kernel time of evaluating `fnItems d.sem` and `trAxiom` on literals with string names. Precedent in the tree: `decide +kernel` on `c.sortName`, `eraseDups`, `sortOf` (`ModelSetIdemWitness.lean:104-117`). Mitigation: reach an item through its function and clause, not through the list's index.
4. Row 7 (projections): the spike must say what `d.sem` holds for `project:X` in ens before any statement is written for the 14 sentences.
5. Form (a) of C7 on this fixture (F3): the text's rule, its `half` equation and the hook graph of `>=Int` together have no model, because `run(-4)` is a value and the rule gives it a successor in the empty set. A derivation "from the `tr s`" that takes both sentences and `ΓDomains` as premises proves anything. Form (a) must take the sentences at the instance (the rule at `N = 4`), or carry, per derivation, a model of its premises.

### 6.3 What result leads TIE-decision where

Form (a) of C7, given section 2: with `text_entails_gamma` (the converse plus the families) and the cut lemma, any `Γ (c H) ⊧ ψ` the package proves is also a consequence of the text's sentences and the named families. So form (a) costs the converse, not a new derivation per expectation, provided risk 5 is handled.

- **Form (a) throughout**: the spike closes rows 1 to 16 and 19 in their directions within about 1500 hand-written lines; `fns_from_text`, `rules_from_text` and `gamma_origin` are proved for ens; the per-text file checks within the memory cap in minutes; risk 1 is closed by `rfl` on `ens-owise` or by the table lemma; and the three library samples close with no new definition, so rows 17 and 18 are a known, shared, finite cost (92 sentences, proved once). Row 7 has a stated direction.
- **By class**: rows 1 to 6, 8, 11 to 14, 19 and the converse close (the equality and constructor classes), and one of these holds: rows 17 and 18 cost more than about 40 lines a sentence in the samples; risk 1 needs the table lemma and it is not written before R2; row 9 needs per-hook proofs. Then form (a) for the closed classes; the hooked classes (9, 10, 15, 17, 18) are form (b), and `[goal].statement` names for them the builtin prose as the trusted base, which trusted base (4) already is, and the reader for T1 to T3.
- **Not at all**: pattern equality fails for rows 2 and 6 for a reason other than names (the reader's `d` does not print the text's equation back under `trAxiom`), or the converse fails for an item with no family, and the fix is not local to a cone definition; or kernel evaluation of the per-sentence statements does not fit the cap. Then R-14's reversal fires as the plan says.

A fourth result needs no decision but a report: any sentence for which the stated direction is refuted on ens after CE is a cone or reader defect, fixed in the spike (the plan's row).

## 7. Findings

Kinds: 5 limits of the plan's statement (F1, F3, F4, F5, F7), 2 verdicts (F2, F9), 2 proof risks (F6, F8), 1 feasibility evidence (F10).

| # | Place | Claim | Evidence | Sure | Settles it |
|---|---|---|---|---|---|
| F1 | `Faithful.lean:204` `ΓDomains`; C14 part 2 "entailed" | Γ does not entail a quantified sentence about a hooked symbol; it entails its instances at values | `FaithfulColl.lean` header: "the sorts below KItem without generators (Int, Bool, the token sorts) may hold elements that are no value's"; `ΓDomains`' disjuncts quantify over `GroundTerm` only | shown that no part of Γ excludes such elements; that a full model with one exists is suspected | the ω model in Lean, or accepting TR-2 |
| F2 | `Faithful.lean:457` `ΓColls`; `InertReason.collectionLaw` | no collection law is entailed as written; assoc and both units are entailed at values for Map, Set, List; idempotence is refuted | section 5 | suspected (E fails; Ev holds); shown (idem, by `not_model_idem`'s argument) | section 5's model; nine value lemmas |
| F3 | `f2-examples/ens.k`; C7 form (a) | the translated text of ens with the hook graph of `>=Int` and the constructors' functionality has no model | rule `run(N) => done(half(N))` with `half(-4) = ⊥` from the equation's `∧ ⌈N >=Int 0 = true⌉`; `prioRuleK`'s doc states the same of any rule with an empty right side | shown by the argument | a Lean proof on ens of `¬ ∃ I, I ⊧ᴵP (itemsPremises [tr rule, tr eq] ∪ ΓSig ∪ ΓCons ∪ ΓDomains)` |
| F4 | `Consistent`'s doc; `Emit.lean` `functionalAx` | the text's `functional` axiom of a function is in no part of Γ; it is a hypothesis (`FnHyp`), so the class is neither E nor W | "`Γ` holds no totality axiom, so a function's `[total]` attribute is not read" | shown | a table row and a `ReadingNote` for it (C6), or a `ΓFns` item |
| F5 | `sigItems`' doc; `Theory.ofDefinition` | G-nonempty and G-sorts are in the text's theory and not in Γ | "No sort is said to be inhabited (G-nonempty)"; `ModelJunkWitness.lean` header | shown | stated limit L3 in `[goal]`; for a sort with a value, non-emptiness is entailed |
| F6 | `canonClausePres` (`Faithful.lean:57`) | pattern equality between Γ's `owise` equation and the text's is not guaranteed | "an exclusion binds its variables, so it may reuse the names of the equation it occurs in"; `VarKey` is (name, sort) | shown that keys can differ; whether any corpus text does is not measured | `rfl` on `ens-owise`; else the table lemma |
| F7 | `InertReason.projectionDomain`; row 7 | for a symbol read as a parameter that the text defines by an equation, "for every H" cannot hold in direction E or Ev | its doc: "its theorems hold for every interpretation, so for the one this axiom and the projection's equation define" | suspected (what `d.sem` holds for `project:X` not read) | the spike's first step (risk 4); the direction is then "for every H that satisfies the sentence at values", a C6 guard |
| F8 | `prioEquation` (`Faithful.lean:495`) against `clauseAx` (`Emit.lean:201`) | for a `priority(n)` equation that is not `owise`, Γ negates the smaller priorities and the text does not; direction W1 only | the two definitions | shown | row 5; it is one of C6's four un-noted readings |
| F9 | ens text, lines 201 to 211 | K 7.1.337 writes no `[comm]` axiom for `_Map_` or `_Set_` in this text; `isCollectionLaw` accepts one | `grep 'comm{}'` on the user module: 0 | shown for ens; other texts not read | a corpus count |
| F10 | `ModelSetIdemWitness.lean:90-121` | the tree already proves a statement of C14's shape about a text-form axiom through `trAxiom [] []`, `trAxiom_at` and kernel decisions | `idemItem`, `idem_vars`, `idem_sort`, `not_model_idem` | shown | none needed |

## 8. Not read

`Hooks.lean`, `Builtins.lean` and `BuiltinData.lean` (what `union`, `concatS` and the library's text are; taken from the headers of `MapLaws.lean`, `ModelColls.lean`, `FaithfulColl.lean`); every proof; `Emit.lean` outside lines 84 to 262; `Parse.lean` outside the three reason lists and `classify`; `Totals.lean`, `ParamsTotal.lean`, the `Model*` files beyond headers and declaration lines; lane CE's changes (the working copy was not read); any text but `ens.kompile.kore`; the findings files, the ticket file, `core-manifest.toml`, `core-cone.txt`.
Resting on it: every "suspected" above; the line estimates of section 6.1; whether the 28 library equations of row 17 are all hook-interpreted (`freshInt` is; the others were not checked one by one).
