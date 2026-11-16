# FA-0: a true statement of soundness and completeness

Delivers ticket FA-0 of `TICKETS-2026-11-11.toml` (findings F3, F4).
Unlike KN-0 and SY-0, nothing here is compiled yet: §3's definitions are specified, not written in Lean.
FA-1's first step is to write them and stop if one does not typecheck as specified.

## 1. What is wrong with the present statement

`ΓD c p` (Statements.lean:207) is the translation of the text `emit c p` prints, filtered, plus generated parts.
A read of how it is assembled (2026-11-11, file references in §6) confirms F3 and adds to it.

| # | defect | status |
|---|---|---|
| 1 | Soundness entails over Γ_D without the function-closure axioms, so a partial function under a priority or an `[owise]` is unconstrained where `Eval` says undefined | counter-model in AUDIT F3; argued |
| 2 | At `HookParams.none`, a used library symbol that is declared total and has no hook (`_-Map_`, `updateMap`, `_<=Map_`) gets "⊥ on every ground argument" from `ΓDom` and "defined everywhere" from `libBlocks`' functional axiom. Γ_D has no model, so `StdModelOK` is false and the other conjuncts hold vacuously | confirmed by reading both definitions |
| 3 | `_Map_` and `_Set_` have no functional axiom, and their graph on canonical arguments is `den v ≡ den v`. Nothing makes a two-entry map one element. Distinctness omits `List`; no-junk exists for `Map` and `Set` only, not for `c.colls` | confirmed |
| 4 | Nothing relates `Eval`, `EvalTerm` or `PatVal` to `Pattern.interpret`. `StepSound.lean` is about the executable step only | confirmed |
| 5 | Γ_D holds axioms about symbols that are not in `Semantics` (`initXCell`, `project:X`, `getGeneratedCounterCell`, `#unboxKConfigValue`, `append`) and reads `Presentation` for cell initial values and the import list | confirmed |
| 6 | `ΓDom` states the `ite` graphs about `Lblite` without its sort argument, a symbol the text never applies | reported by the read, not checked |
| 7 | `owiseClauseAx` passes `req = none`, so an `[owise]` clause over patterns loses its `requires` in the text | reported, not checked |
| 8 | A cell-collection sort's no-junk axiom has the injection from its element cell as only generator, which excludes maps of two entries | reported, not checked; no example has `colls` |

Defects 6 to 8 go away with the definition of §3 and need no separate fix; 7 is also a tie bug and goes to the reader lane.

## 2. The shape of the corrected statement

Two statements replace one.

**(A) Faithfulness of the kernel**, about a theory defined from `Semantics` alone:

```lean
def Γ (c : Semantics) : Premises KoreAML.Sym          -- §3; reads c.hooks, never a Presentation

theorem step_sound    : Hyp c → ∀ x y, Step c x y → Γ c ⊧ (den c x.val ⇒ sNext (den c y.val))
theorem step_complete : Hyp c → StepIs c ref → ∀ x, (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ allNext (disjList ((ref x.val).map (den c))))
theorem has_model     : Hyp c → ∃ M _ I, I ⊧ᴵP (Γ c ∪ Γstep c)
```

It is stated for every `c`, so in particular for `d.sem.withHooks H` at every `H`.
`Hyp c` is what the proof reads: `c.okAll`, `srReady`, and `Obligations` (termination, totality, `Coherent` after KN-2).
`Γstep` is the step-closure axiom, as today's `Γclosure` without the function part.

**(B) Agreement with the text**, optional and separate, the tie's counterpart:
every model of the kept axioms of `emit c p`, in which the uninterpreted parameters are partial functions on values, is a model of `Γ (c.withHooks H)` for the `H` it determines, on the symbols of `Semantics`.
`HookModel` belongs here and only here: it says `H` is defined where a parameter is declared total.
Statement (A) does not need it, because Γ holds the graph of whatever `H` is, and any graph is consistent.

Why two.
(A) is the property every theorem proved over `Step` rests on, and it must not depend on a printer.
(B) is evidence that the kernel's theory is the one kompile wrote; it is as strong as the tie and can stay unproved without weakening (A).

## 3. Γ from `Semantics`

Each part names the builder that exists and what changes.
Variable names are canonical (`numbered "V"`), since a name only fixes an index.
`trAxiom` is called with empty declarations and aliases: it reads them only for an application at the top of an axiom and for alias applications, and Γ has neither.

1. **Signature**: definedness; per sort, G-sort and G-nonempty; per symbol of `ctorSigs`, `allFns`, `params` and `hookSigs`, G-arity; the ceil and next items; `dvArityAll`. As `Theory.ofDefinition` gives, computed from `Semantics`' lists instead of declarations.
2. **Constructors**: `consItems c`, unchanged. After KN-3 it no longer reads cells.
3. **Domains** (`ΓDom`, changed):
   - the graph of every interpreted hook and of every parameter under `c.hooks`, as today, with `ite` applied to its sort argument as `Term.kore` writes it;
   - **values are elements**: for every ground `v` with `c.sortOf v = some s`, `∃y:s. den c v ≡ y`. For constructor terms this follows from Cons-Fun; it is the missing axiom for collections and replaces `dvFunctional` as a separate assumption;
   - **distinctness** for every pair of distinct values of one sort among Int, Bool, the token and byte sorts, and every sort of `c.allColls`;
   - **no junk per collection sort**: for each `k ∈ c.allColls`, `⟦k.sort⟧ ⊆ μX. unit ∨ concat(elem(⟦k.key⟧[, ⟦k.val⟧]), X)` with `k`'s symbols and sorts. A cell-collection sort is not a constructor sort and gets no Cons item.
4. **Functions**, for each `f ∈ c.allFns` (so the sort predicates are functions like any other):
   - per clause, `premise ∧ ¬⋁_{cl' : prio cl' < prio cl} applies cl' → f(X̄) = rhs`, with `premise` and `exclusion` as Emit builds them. Before KN-2 the competitors are: none for an ordinary clause, every other clause for the `[owise]` one, with its `requires`;
   - **the closure axiom** `fnClosurePattern`, moved here from `Γclosure`.
5. **Rules**: `prioRulePattern`, unchanged, with canonical names.

Not in Γ: the builtin modules' text (a hook's equations follow from its graph), INJ composition, cell initialisers and projections, anything read from `Presentation`.

Why closure is in Γ and not an extra assumption.
`Step` lets a rule fire when a competitor's `requires` is undefined, and `Eval` reads "no clause applies" as undefined.
Without closure the theory does not say so, and the soundness of every priority and every `[owise]` over a partial function fails (defect 1).
So closure is part of what K's function equations mean here: the least-defined reading. It is stated once, in Γ, where a reader of the theorem sees it.

## 4. The counter-models, spelled out

1. **Closure.** `f(1) => true`; r1 `a => b requires f(0) [priority(10)]`; r2 `a => c`. `Step` has a → c. Take the standard model and set `f(0) = true`: every axiom of the old Γ_D holds (f's equation only speaks at 1), r2's premise `¬ applies r1` is false, so `den a ⇒ •den c` fails. With §3.4's closure, `y ∈ f(0)` implies a clause premise at 0, which is false, so `f(0) = ⊥`.
2. **Total uninterpreted parameter.** Defect 2 above; instance `K0 = K1 = .Map` of `_-Map_`'s functional axiom against its graph `_-Map_(.Map, .Map) ≡ ⊥`.
3. **Maps.** Take the standard model and add a second element `m'` to `⟦Map⟧`, with `_Map_(k1 |-> v1, k2 |-> v2) = {m, m'}`. Assoc and unit hold, no-junk holds (both are in the μ), the graph is a tautology; `den` of the two-entry map is not one element, so `ModelsStandard`'s first conjunct fails.

## 5. Proof plan, first stage (FA-1)

Stage 1: no priorities, no `[owise]`, every function total (`Total c f` for all `f`), no collections in rules or values.
Under these the proof uses the axioms positively only, and builds no model.

Fix `I ⊧ᴵP Γ c`. Write `⟦v⟧` for `(den c v).interpret I val0`.
For a well-sorted σ and a variable list, `ρ_σ` maps variable i to the element of `⟦σ i⟧` (L1 gives it).

- **T. Translation lemmas** (about `tr`, not about K): the interpretation of `\and`, `\equals`, `\in`, `\top`, `\implies`, `\exists` and of `trAxiom`'s guards in a model of definedness and the ceil items. `disjList_interpret` (ReorderTheory.lean:207) is the one that exists. These are the bulk of the work and are reused by every later stage.
- **L1. Values are elements.** `c.sortOf v = some s → ∃ a, ⟦v⟧ = {a} ∧ a ∈ ⟦s⟧`. By §3.3's schema directly; the sort membership by G-arity and `dvArityAll`, induction on `v`.
- **L2. Patterns.** `PatVal c σ p v → (tr (Term.kore c vs p)).interpret I ρ_σ = ⟦v⟧`, for `var`, `dv`, `ctor`, `inj`, `as`. Induction on `PatVal`; application in matching logic is pointwise, so singletons compose.
- **L3. Evaluation**, mutual: `EvalTerm c σ t r → interpret (Term.kore t) ρ_σ = (⟦v⟧ if r = some v, ∅ if none)`, and `Eval c f vs (some v) → interpret f(den v̄s) = ⟦v⟧`.
  - `hook`: the graph axiom at the arguments' values; an undefined argument gives ∅ because application is strict.
  - `call`, `Eval.clause`: the clause's equation at `ρ_σ`. Its premise is `X_j ∈ p_j` (L2) and `req = true` (L3 on the `requires`). The equations of ordinary clauses carry no negated competitor, so the clauses before it are not read.
  - `Eval.undef` and `Eval.owise` do not occur in stage 1.
- **L4. Step.** `Step.rule` with no smaller priority: the rule's axiom at `ρ_σ`, with L2 for the left-hand side, L3 for `requires` and the right-hand side.

Later stages, each adding what its feature reads:
- **owise and priorities over total functions**: negated premises. Needs that a match of a standard element has standard parts (Cons-Inj, no-junk of the constructor sorts), to turn `Fails` into the falsity of `applies`.
- **partial functions**: the closure axiom, for `Eval.undef` and for `Fails` by an undefined `requires`.
- **collections**: §3.3's three per-collection items.
- **completeness and `has_model`**: the term model; the step-closure axiom.

## 6. Where the facts were read

Statements.lean:104-120, 207-217; Emit.lean:59-80, 145-206, 369-454; Kore/Translate.lean:125-201, 286-322, 441-458; Kore/Build.lean:57-155; Kore/Gamma.lean:92-142; Kore/Signature.lean:31-138; Builtins/BuiltinData totals; prelude/builtin.kore:193-202, 262-270, 361-371, 1101-1111, 1230-1243, 1881-1891.

## 7. Corrections made while proving (2026-11-11)

§3 and §5 above are the plan as first written. `KcoreSpec/Faithful.lean` on the theory lane is the definition; where the two differ, the Lean file is right.
Each correction below came from a proof step that failed or a counter-model, not from a comparison with kompile's text.

Γ is `ΓSig ∪ ΓCons ∪ ΓDomains ∪ ΓColls ∪ ΓFns ∪ ΓRules`.

| change to Γ | why |
|---|---|
| Collection sorts get no constructor items (§3.2 said `consItems` unchanged, §3.3 said a collection sort is not a constructor sort) | the two contradicted each other; a two-entry map is not a constructor term |
| `distinctSorts` includes KConfigVar | its values are literals and soundness compares them |
| New part `ΓColls`: per map collection, unit-split, entry-not-unit, entry-atomic, decomposition; per list collection, the same four with atomicity from the front and from the back | without them a model may add junk to a collection sort (an Int that is a map), and a rule matching a collection pattern is unsound there. §3.3's no-junk μ item alone does not exclude it |
| A rule's axiom has the premise `⌈rhs⌉` | `Step.rule` fires only where the right-hand side evaluates. Without the premise a rule whose right-hand side is undefined forces `lhs → •⊥`, and Γ has no model |
| G-nonempty is removed from `ΓSig` | it forced an element in a sort the definition gives no value (Float with no literal), which no-junk then contradicts. No soundness step needed it at a sort that may be empty |

Hypotheses, in place of the single `Hyp c` of §2:

- `HypSound c`, all decidable, is what `step_sound` reads: `okAll`, `srReady`, names numbered, and well-formedness facts about hooks, patterns and collections. It has no termination, totality or agreement condition.
- `Hyp c` adds termination, totality, `ClausesAgree` and `MatchIndependent`. Only model existence reads it.
- `HypModel c` adds what makes distinct things distinct in the model: symbol names apart, literals apart, sort ids in range, every sort of a symbol or collection numbered, collection symbols apart from constructors, ite-named symbols apart by sort, hooks and parameters apart from constructors.

Each `HypModel` condition beyond `Hyp` and `HypSound` is a well-formedness fact about the `Semantics`, and belongs in `okAll` or `wf` once the lanes are merged.
`HypModel` also has: no constructor signature listed twice, and no function named like a constructor, hook or parameter.
Five counter-models are on file as regression cores (undefined right-hand side, junk Float, same name twice, a constructor listed twice, a function named like a library constructor); the other conditions are argued and not yet witnessed.

Proof state:

- `step_sound (h : HypSound c)` is proved for every `c`, with no stage restriction; §5's stages were the route, not the result.
- `has_model (h : HypModel c)` is proved: `Γ c ∪ Γstep c` has a model, the value model, with no other condition. First-match `Eval` satisfies the unordered equations because of `ClausesAgree`.
- `step_complete` and statement (B) are not started.
- `KcoreSpec/Sound.lean` states `Sound d` (Γ ∪ Γstep has a model, and every step is entailed) and proves `sound : wf d = true → Obligations d → Sound d`. `wf` checks `faithOK`, the decidable facts of `HypSound` and `HypModel`. The older statement over Γ_D is removed; `complete` is the one `sorry`.
- `complete : wf d = true → Obligations d → Complete d ref` is proved (`KcoreSpec/FaithfulComplete.lean`); the library has no `sorry`. Every variable of a rule occurs in its left-hand side, so matching a value forces each variable onto a value, and Γ needs no no-junk axiom for literal sorts. Statement (B), agreement with kompile's text, is not started.
