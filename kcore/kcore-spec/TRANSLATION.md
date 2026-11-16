# The translation of a KORE definition into applicative matching logic

State: M1.2 output for review, 2026-11-05. Nothing here is decided until Sebastien reviews it.
Code: `KcoreSpec/Signature.lean` (signature, sorted notations), `KcoreSpec/Translate.lean` (the translation and Γ_D); the rule ids below appear in both.
The subject's Γ_D is in [GAMMA_D.txt](GAMMA_D.txt); [SAMPLE.md](SAMPLE.md) puts 15 axioms beside their KORE.

Status of a rule: SOURCE (transcribed from the cited definition), CHOICE (not dictated by a source; alternatives listed), GAP (not translated).
Counts: 36 SOURCE, 10 CHOICE, 1 GAP (table at the end).

## Sources

| Key | Document | Where |
|---|---|---|
| [Thesis] | X. Chen, *Matching mu-Logic*, PhD thesis, UIUC 2023 (`Matching mu-Logic (Chen PhD Thesis 2023).pdf`) | printed page p is PDF page p+7. ML syntax Def. 2.45 and notations (2.95)–(2.97), p. 31; definedness Def. 2.49 (2.98)–(2.103) and Prop. 2.3, pp. 33–34; (Function) (2.104), p. 34; MmL Def. 4.1 (4.3)–(4.6), p. 72, free set variables of axioms universally quantified, p. 73; §7.2 (7.7)–(7.19), p. 163; Prop. 7.2, pp. 164–165; §7.3.1 (7.25), p. 165; §7.3.2 (7.28)–(7.30), p. 166 |
| [AML-TR] | X. Chen, G. Roşu, *Applicative Matching Logic: Semantics of K*, TR 2020 | page numbers as printed (= PDF). Def. 6 (definedness, ≠), p. 8; §4.2 (Sort, ⟦_⟧, Nonempty Domain, sorted quantifiers), p. 11; Def. 11 (ws), p. 12; §7 (parametric sorts, (Sorts), Parametric Nil), p. 18; §8 (•, its arity, (Semantics)), p. 19; App. G.2 (MmL2AML, (Arity), ¬_s, ψ^VALID, Prop. 26), pp. 34–35 |
| [FoSSaCS] | X. Chen, H. Cheval, D. Lucanu, G. Roşu, *𝕂 Definitions as Matching Logic Theories, Formally*, FoSSaCS 2026 | LNCS page p is PDF page p−197. Notations as conservative extensions, p. 204; theory of sorts (`inh`, `Sort`, `Sort ∈ ⊤_Sort`), p. 204; rewriting (`•`, rules `ϕ → •ϕ′`), p. 206; §4.1 item 2 (`syntax N :↔ ∃y:Sort. N = y`), p. 208; §4.2 constructors and (No-Junk), p. 210 |
| [kore-syntax] | `haskell-backend/docs/kore-syntax.md` (the KORE grammar) | "Patterns" (`\left-assoc`), "Attributes", "Definition, modules" (scope), "Validity" |
| [kore-implicits] | `haskell-backend/docs/kore-implicits.md` | the sorts of KORE's connectives |

[kore-syntax] and [kore-implicits] define KORE's syntax and sorting; they are cited only for what the KORE text means as text.
Two backend documents are cited as evidence only, never as the reason for a rule: `haskell-backend/docs/injections/injections.tex` and `haskell-backend/docs/2019-04-23-Applicative-Kore.md` (its FullKore-to-AppKore section is marked "DO NOT REVIEW").

## Shape of Γ_D

[Thesis] §7.2 translates a matching μ-logic (MmL) theory Γ into the AML theory `Γ^AML ∪ AML(Γ)`, and Prop. 7.2 states that this preserves and reflects semantic consequence.
Γ_D has that shape (`Theory` in `Translate.lean`):

- `Γ^AML` (`ΓD.signature`, 141 axioms for the subject): the encoding's axioms, the G-rules below.
- `AML(Γ)` (`ΓD.axioms`, 202 axioms): one translated axiom per KORE axiom, in text order (T-axiom).
- `ΓD.premises` is aml-port's `Premises`; it also contains aml-port's `definedness` at every variable, so that aml-port's `HasDefinedness` instance holds.

KORE's connectives other than MmL's primitives are read as the MmL notations the thesis defines, and those notations are then translated by AML2.
No simplification is applied: `\top{S}()` becomes the AML image of `∃x:S. x:S`, not `⟦S⟧`, although the two are equal in every model of Γ^AML ([Thesis] Prop. 2.2 with (7.22)).
The cost is size (154,838 AML pattern nodes for the subject's 2,374 KORE nodes); a simplified encoding with a proof of equivalence belongs to the searched layer.
The printer shows the notations back (SAMPLE.md, "How to read").

## Sorts and sort parameters

The thesis's §7.2 handles a fixed set of sorts and no sort variables.
The subject has sort variables in 177 axioms (`axiom{R}` 175, `axiom{S1,S2,S3,R}` 1, `axiom{R,Q0}` 1), sort-parametric symbols (`inj{From,To}`, three `MInt` list operations with `{SortWidth}`), and a parametric hooked sort (`SortMInt{SortS0}`), whose instances `SortMInt{SortMInt{…}}` make the set of ground sorts infinite.
So sort parameters cannot be expanded into finitely many instances, and the translation takes the route of [Thesis] §7.3.2: sorts are elements, and sort variables range over `⟦Sort⟧`.

**S-param — CHOICE.**
A sort variable `α` of an axiom or declaration becomes the AML element variable `α`, guarded by `α ∈ ⟦Sort⟧` in the axiom's well-sortedness conjunction (T-axiom) or in front of the generated axiom (G-rules).
Basis: [Thesis] §7.3.2, p. 166, (7.28)–(7.30) ("similar to the (Function) axioms … but here s is a variable ranging over Sort"); [AML-TR] §7, p. 18; [FoSSaCS] p. 207, Ax.1–Ax.5 (`∀s1,s2:Sort`).
No source states it for KORE's `axiom{α…}` sentences.
Alternative: schematic instantiation, one AML axiom per ground instance, as KORE's sort parameters are usually read; it is infinite here (`SortMInt`), and with G-sorts it has the same models restricted to the generated sorts.
The `R` of `axiom{R}` is not special: it is the sort of the outer predicate, and since every sort in `⟦Sort⟧` is nonempty (G-sorts, G-nonempty), the instances of a predicate axiom at different `R` are equivalent (inference from [Thesis] Prop. 2.3 items 2–4).

**S-args — CHOICE.**
A sort-parametric symbol takes its sort arguments as leading applied arguments: `inj{SortNat{}, SortVal{}}(φ)` becomes `inj SortNat SortVal φ`; `\ceil{S,R}` and `\dv{S}` likewise (T-ceil, T-dv).
Basis: [AML-TR] §7, p. 18, (Parametric Nil) `∀s:Sort. ∃l:List s. nil s = l`.
Alternative: one overloaded symbol without sort arguments, as [AML-TR] §7's first version of `nil` and [Thesis] (7.28)–(7.30); it identifies instances that KORE keeps distinct (`inj{Nat,Val}` and `inj{Nat,KItem}` would be the same symbol), which adds constraints.

**S-sortof — CHOICE.**
"`s` is a sort" is `s ∈ ⟦Sort⟧` ([FoSSaCS] p. 204; [AML-TR] §7 writes `∀s:Sort` and `⟦Sort⟧`), not `s ∈ Sort` ([AML-TR] §4.2 (Sort), p. 11, where the symbol `Sort` itself is matched by the sorts).
`Sort ∈ ⟦Sort⟧` ([FoSSaCS] p. 204, "in particular") is not added: KORE has no sort of sorts, and with it every sort-parametric axiom would also constrain `Sort` (and G-sorts would have to list it).

**T-sort — SOURCE.**
A sort `C{s₁,…,sₖ}` becomes the symbol `C` applied to the translated arguments; a sort variable becomes its element variable (S-param).
[Thesis] §7.2, p. 163 ("for every sort s we introduce it as a (constant) symbol"); §7.3.2, p. 166 (a parametric sort as a function `List : Sort → Sort`).

## The encoding's axioms (Γ^AML)

| Rule | Axiom (as printed in GAMMA_D.txt) | Status, source |
|---|---|---|
| G-def | `∀x. ⌈x⌉` | SOURCE: [Thesis] (7.7), p. 163, written as aml-port's `definedness` (its universal closure; same models) |
| G-sort | `∃y:Sort. C = y` per declared sort; `α ∈ ⟦Sort⟧ → ∃y:Sort. C α = y` for a parametric one | SOURCE: [FoSSaCS] §4.1 item 2, p. 208; [AML-TR] §4.2 (Sort) and "functional constant", p. 11; for the parametric case [Thesis] (7.28)'s form, `C : Sort → Sort` |
| G-nonempty | `¬(⟦C⟧ = ⊥)`, guarded for a parametric sort | SOURCE: [Thesis] (7.8) `⊤_s ≠ ∅`; `≠` as [AML-TR] Def. 6, p. 8 |
| G-sorts | `⟦Sort⟧ = μS. SortK ∨ SortKItem ∨ … ∨ SortMInt S ∨ …` (one disjunct per declared sort, `S` for each parameter) | CHOICE: [AML-TR] §7 (Sorts), p. 18, `⟦Sort⟧ = µS. Nat ∨ Int ∨ List S`, applied to KORE's sorts. It makes S-param's quantified axioms say exactly what their ground instances say. It is the only μ in Γ_D. Alternative: omit it, so that sort variables also range over sorts no declaration names. |
| G-arity | `σ ᾱ ⟦s₁⟧ … ⟦sₙ⟧ ⊆ ⟦s⟧` per `symbol` and `hooked-symbol`, guarded by `ᾱ ∈ ⟦Sort⟧` | SOURCE: [Thesis] (7.9); [AML-TR] App. G.2 (Arity), p. 34 |
| G-ceil-arity | `s ∈ ⟦Sort⟧ ∧ s' ∈ ⟦Sort⟧ → ⌈⟦s⟧⌉[s,s'] ⊆ ⟦s'⟧` | SOURCE: (7.9) for the symbols `⌈_⌉^{s'}_s` of [Thesis] (2.98), which are MmL symbols of Σ^MmL |
| G-ceil-def | `s ∈ ⟦Sort⟧ ∧ s' ∈ ⟦Sort⟧ ∧ x ∈ ⟦s⟧ → ⌈x⌉[s,s'] = ⟦s'⟧` | SOURCE: [Thesis] (2.99) `⌈x:s⌉^{s'}_s`, translated by (7.10) |
| G-next-arity | `•⟦S⟧ ⊆ ⟦S⟧` for each sort `S` of a `\rewrites` or `\next` (here `SortGeneratedTopCell`) | SOURCE: [AML-TR] §8, p. 19 (`• ⟦Cfg⟧ ⊆ ⟦Cfg⟧`); equivalent in AML to [FoSSaCS] p. 206's `ϕ′ ⊆ ⊤_s → •ϕ′ ⊆ ⊤_s`. [FoSSaCS]'s `•ϕ′ = ∃y:s. •y ∧ y ∈ ϕ′` is not added: it is valid in every AML model, application being pointwise. |
| G-dv-arity | `s ∈ ⟦Sort⟧ → dv"v" s ⊆ ⟦s⟧` per literal `v` occurring in a `\dv` | CHOICE: see T-dv |

## Patterns (AML2 and KORE's other connectives)

Each rule gives `AML2(KORE pattern)`; `s'` denotes the translation of the KORE sort `s` (T-sort).
Rules marked with an equation number transcribe [Thesis] §7.2, p. 163; rules marked (2.9x)–(2.10x) or (4.6) first read the KORE connective as the MmL notation of that number, then apply AML2.

| Rule | KORE | AML | Status, source |
|---|---|---|---|
| T-axiom | `axiom{ᾱ} φ` with `φ` of sort `s` | `ws → (AML2(φ) = ⟦s'⟧)`, `ws` the conjunction of `α ∈ ⟦Sort⟧` for the declared sort variables, then `x ∈ ⟦s_x⟧` for free element variables and `X ⊆ ⟦s_X⟧` for free set variables, in order of first occurrence; `⊤` when empty | SOURCE: [Thesis] (7.10)–(7.11); [AML-TR] Def. 11, p. 12 (free variables), App. G.2, p. 35 (`ψ^VALID`, set variables with `⊆`). The thesis's (7.11) ranges over all variables of `EV^MmL`; its proof (p. 165) and [AML-TR] use the free ones. The sort-variable guards are S-param. The sort of `φ` is read off its outermost construct ([kore-implicits]). |
| T-evar | `x:s` | the variable `xˢ` | SOURCE: (7.12). A `(name, sort)` pair is one variable; each axiom numbers its pairs from 1 (index 0 is reserved, T-top). |
| T-svar | `@X:s` | `Xˢ` | SOURCE: (7.13) |
| T-app | `σ{s₁…sₖ}(φ₁…φₙ)` | `σ s₁' … sₖ' AML2(φ₁) … AML2(φₙ)` | SOURCE: (7.14), with S-args. `inj` is translated like any symbol; no axiom is added for it. |
| T-and | `\and{s}(φ, ψ)` | `AML2(φ) ∧ AML2(ψ)` | SOURCE: (7.15) |
| T-nary | `\and{s}`, `\or{s}` with n ≠ 2 operands | right-nested; one operand is itself; none is `⊤_s` (`\and`) or `⊥_s` (`\or`) | CHOICE: the grammar allows n operands ([kore-syntax] `<patterns>`) without fixing a reading; any nesting has the same meaning (∩ and ∪ are associative). In the subject, every `\and` is binary; `\or` has 3 operands 4 times and 17 once. No decision needed. |
| T-not | `\not{s}(φ)` | `¬[s'] φ' ≡ ¬φ' ∧ ⟦s'⟧` | SOURCE: (7.16); [AML-TR] App. G.2 (sorted negation) |
| T-exists | `\exists{s}(x:t, φ)` | `∃xᵗ. (xᵗ ∈ ⟦t'⟧) ∧ AML2(φ)` | SOURCE: (7.17), which prints `⊤_s`; the guard must use the bound variable's sort `t`, as [AML-TR] App. G.2 (`∃x:s′.ϕ ≡ ∃x:s′.ϕ^MmL2AML`) and §4.2 (`∃x:s.ϕ ≡ ∃x. x ∈ ⟦s⟧ ∧ ϕ`) write it |
| T-mu | `\mu{}(@X:s, φ)` | `μXˢ. AML2(φ)` | SOURCE: (7.18). Unused by the subject. |
| T-or | `\or{s}(φ, ψ)` | `¬[s'](¬[s'] φ' ∧ ¬[s'] ψ')`, printed `φ' ∨[s'] ψ'` | SOURCE: (2.95) `φ₁ ∨ φ₂ ≡ ¬(¬φ₁ ∧ ¬φ₂)` |
| T-implies | `\implies{s}(φ, ψ)` | `(¬[s'] φ') ∨[s'] ψ'`, printed `φ' →[s'] ψ'` | SOURCE: (2.96) `φ₁ → φ₂ ≡ ¬φ₁ ∨ φ₂` |
| T-iff | `\iff{s}(φ, ψ)` | `(φ' →[s'] ψ') ∧ (ψ' →[s'] φ')` | SOURCE: (2.96). Unused. |
| T-forall | `\forall{s}(x:t, φ)` | `¬[s'] ∃xᵗ. (xᵗ ∈ ⟦t'⟧) ∧ ¬[s'] φ'` | SOURCE: (2.95) `∀x:s.φ ≡ ¬∃x:s.¬φ`. Unused. |
| T-top | `\top{s}()` | `∃x₀. (x₀ ∈ ⟦s'⟧) ∧ x₀`, printed `⊤[s']` | SOURCE: (2.96) `⊤_s ≡ ∃x:s. x:s`, then (7.17). The bound variable is index 0 for every sort (α-equivalent to the thesis's `xˢ`). |
| T-bottom | `\bottom{s}()` | `¬[s'] ⊤[s']`, printed `⊥[s']` | SOURCE: (2.97) `⊥_s ≡ ¬⊤_s` |
| T-nu | `\nu{}(@X:s, φ)` | `¬[s'] μXˢ. ¬[s'] φ'[¬[s'] Xˢ / Xˢ]` | SOURCE: (4.6) `νX.φ ≡ ¬µX.¬φ[¬X/X]`. Unused. |
| T-ceil | `\ceil{s,r}(φ)` | `ceil s' r' φ'`, printed `⌈φ'⌉[s',r']` | SOURCE: [Thesis] Def. 2.49 (2.98) (the MmL symbol `⌈_⌉^r_s`) and (7.14), with S-args. It is not AML's own `⌈_⌉` (G-def): the two agree on patterns contained in `⟦s'⟧` (inference from G-ceil-arity, G-ceil-def and propagation), and the thesis keeps both in Σ^AML. |
| T-floor | `\floor{s,r}(φ)` | `¬[r'] ⌈¬[s'] φ'⌉[s',r']` | SOURCE: (2.100). Unused. |
| T-equals | `\equals{s,r}(φ, ψ)` | `⌊φ' ↔[s'] ψ'⌋[s',r']`, printed `φ' =[s',r'] ψ'` | SOURCE: (2.101) |
| T-in | `\in{s,r}(x:s, ψ)` | `⌈x ∧ ψ'⌉[s',r']`, printed `x ∈[s',r'] ψ'` | SOURCE: (2.102), stated for a variable `x`; all 80 `\in` of the subject have one (`Checks.lean`) |
| T-in-nonvar | `\in{s,r}(φ, ψ)`, `φ` not a variable | `⌈φ' ∧ ψ'⌉[s',r']` | CHOICE: (2.102) defines membership of a variable only. Unused. |
| T-next | `\next{s}(φ)` | `• AML2(φ)` | SOURCE: [FoSSaCS] p. 206; [AML-TR] §8. `•` is one unsorted symbol, as both write it (its sorts come from G-next-arity). Unused (only inside T-rewrites). |
| T-rewrites | `\rewrites{s}(φ, ψ)` | `φ' →[s'] •ψ'` | SOURCE: [FoSSaCS] p. 206 ("A rewrite rule … is a pattern of the form ϕ → •ϕ′"); [AML-TR] §8 (Semantics) `ϕ_lhs → •ϕ_rhs`. See the note below. |
| T-dv | `\dv{s}("v")` | `dv"v" s'` | CHOICE: no paper gives domain values a meaning. `\dv{s}("v")` is read as a nullary sort-parametric symbol `dv"v"{s}() : s`, with only its arity (G-dv-arity). Alternatives, cumulative: (Function) `∃y. dv"v" s = y`; distinctness of distinct literals of one sort; a fixed interpretation per hooked sort (the full theory of a standard model, `Q-domain-theories`). |
| T-string | a string literal `"v"` as a pattern | the constant `"v"` | CHOICE: KORE's `#String` sort has no counterpart in the papers. Unused (the subject's literals occur only in `\dv` and attributes). |
| T-assoc | `\left-assoc{}(σ{s̄}(φ₁,…,φₙ))`, `\right-assoc{}(…)` | `σ(…σ(φ₁,φ₂)…,φₙ)`, `σ(φ₁,σ(φ₂,…))`, then T-app | SOURCE: [kore-syntax] "Patterns". For n < 2 (not covered there): `σ s̄` for none, `φ₁` for one. Unused. |
| T-alias | an application of an `alias` | the marker `‹UNTRANSLATED alias …›` | GAP: expanding an alias needs capture-avoiding substitution of the arguments into the alias body, which M1.2 does not implement. The subject declares three aliases (module K) and applies none; `Checks.lean` verifies that no marker occurs in Γ_D. |

Note on T-rewrites.
kompile emits each rule as `\rewrites{S}(\and{S}(lhs, req), \and{S}(rhs, ens))`, here with `req` and `ens` both `\top{S}()`; the translation is therefore `lhs ∧ ⊤[S] →[S] •(rhs ∧ ⊤[S])`, which is group A's `lhs ∧ req → •∃ȳ.(rhs ∧ ens)` with no `ȳ`.
The translation adds no `∃ȳ` of its own: it is compositional, so right-hand-side existentials enter only when the KORE writes `\exists`; neither rule of the subject has a right-hand variable absent from its left-hand side.
The sorted `→[S]` agrees with the papers' unsorted `→`: under the guard, `lhs'` and `•rhs'` lie in `⟦S⟧` ([AML-TR] Prop. 26 and G-next-arity), so the axiom holds exactly when `lhs' ⊆ •rhs'`, which is [FoSSaCS] p. 206's Remark 2 reading (inference).

## Sentences

| Rule | KORE sentence | Contribution to Γ_D | Status, source |
|---|---|---|---|
| D-scope | modules, `import` | the union of all modules' sentences | SOURCE: [kore-syntax] "Definition, modules": a declaration is in scope in the modules that (transitively) import it. Here PEANO imports K, which imports KSEQ (importing BASIC-K) and INJ, so the union is the theory of the main module. |
| D-sort | `sort`, `hooked-sort` | G-sort, G-nonempty, a G-sorts disjunct | SOURCE (G-rules). A hooked sort gets nothing more: the loose reading of `Q-domain-theories` that milestone 1 fixes (README "Scope" item 3). |
| D-symbol | `symbol`, `hooked-symbol` | G-arity | SOURCE: (7.9). Hooked symbols likewise get only their arity. |
| D-attributes | attributes of any sentence | nothing | SOURCE: [kore-syntax] "Attributes": "Attributes are hints to the backend … All semantic information contained in attributes should correspond to axioms declared explicitly." [FoSSaCS] §4.2 gives K-level attributes axioms; at the KORE level kompile has already emitted those it emits (next section). |
| D-alias | `alias … where …` | nothing | SOURCE: an alias is a notation, and a notation is a conservative extension ([FoSSaCS] p. 204). Its applications: T-alias. |
| D-axiom | `axiom{ᾱ} φ [attrs]` | T-axiom, whatever the attributes (`simplification`, `owise`, `concrete`, …) | SOURCE: [Thesis] (7.19) `AML(Γ) = {AML(ψ) | ψ ∈ Γ}` |
| D-claim | `claim` | nothing | CHOICE: claims are proof obligations, not axioms. The subject has none. |

## What kompile emitted for the declared attributes

Read from the subject (`Checks.lean` and the attribute scan recorded here); none of these axioms comes from the translation.

- `functional` / `total`: one `[functional]` axiom `∃Val:s. Val = σ(K0,…)` for each such symbol (55), except `kseq`, `dotk` (module KSEQ) and `append`.
- `subsort`: one `[subsort]` axiom, functionality of `inj{A,B}` on `⟦A⟧`, per declared subsort (18). No inclusion `⟦A⟧ ⊆ ⟦B⟧` ([Thesis] (7.25)) and no injectivity of `inj`.
- `constructor`: 23 `[constructor]` axioms: injectivity `c x̄ ∧ c ȳ → c (x̄ ∧ ȳ)` for 8 constructors with arguments (`#KConfigValue`, `s`, `run`, `done`, `<k>`, `<generatedCounter>`, `<generatedTop>`, `<generatedTop>-fragment`); distinctness for 2 pairs (`z`/`s`, `run`/`done`); one μ-free no-junk disjunction for each of 13 sorts.
- Not emitted although an attribute declares it: anything for `kseq` and `dotk` (constructor, functional, injective), so no no-junk for `SortK`; `append`'s functionality; the injectivity of the hooked `SetItem` and `_|->_` (`injective`); distinctness of `noKCell` from `inj{SortKCell{}, SortKCellOpt{}}(_)`, of `noGeneratedCounterCell` from its `inj`, and among the 16 generators of `SortKItem` (`#KConfigValue` and 15 injections).
  [kore-syntax] asks that attribute semantics correspond to explicit axioms, so these are omissions in kompile's output, not facts the translation should add.

## CHOICEs needing Sebastien's decision

1. S-param: sort variables as element variables guarded by `∈ ⟦Sort⟧`, rather than schematic instances (infinite here).
2. S-args: sort arguments applied explicitly (`inj SortNat SortVal x`), rather than overloaded symbols.
3. S-sortof: sorts are `∈ ⟦Sort⟧`; `Sort ∈ ⟦Sort⟧` omitted.
4. G-sorts: add `⟦Sort⟧ = μS. ⋁ declared sorts`, so sort quantification ranges over KORE's sorts only.
5. T-dv / G-dv-arity: `\dv{s}("v")` has only its arity; no functionality, no distinctness (`"true"` and `"false"` may coincide in a model of Γ_D).

T-nary, T-in-nonvar, T-string, D-claim are choices with no effect on the subject.

## Gaps in the sources

- No source translates KORE's sort-parametric sentences (`axiom{R}`, `symbol inj{From,To}`); [Thesis] §7.2 has a fixed sort set, and §7.3.2 and [AML-TR] §7 show quantified sort variables only by example.
- Prop. 7.2 covers neither S-param, S-args, G-sorts nor the encoding of `•` and `\dv`; a Lean proof of Prop. 7.2 would have to be extended to parametric sorts before it justifies this Γ_D. Its μ case is a sketch (group B), but Γ_D's only μ is G-sorts.
- (7.17) prints `⊤_s` where the bound variable's sort `⊤_{s′}` is meant; (7.11) quantifies over all variables where the free ones are meant.
- Domain values and tokens, string literals, hooks' domain theories: absent from all four papers.
- Membership `φ ∈ ψ` with a non-variable `φ`, and KORE's n-ary `\and`/`\or`: not defined (harmless here).
- Distinctness of sort names: stated by no source; not added (two sort names may denote the same sort in a model).
- Alias expansion: the papers treat notations as meta-level definitions; KORE's `alias` bodies would need a substitution operation in the translation (T-alias).

## Findings about kompile's theory under the translation

None of these comes from the translation; each holds equally of the KORE read schematically.

F1. Axiom 3 (module INJ, `[simplification]`), `inj{S2,S3}(inj{S1,S2}(T:S1)) = inj{S1,S3}(T)` for all sorts `S1, S2, S3`, is false in the intended model.
Take `S1 = SortState`, `S2 = SortNat`, `S3 = SortKItem`, `T = run(z)`.
The left side lies in `inj{Nat,KItem}(⟦Nat⟧)` (G-arity for `inj{State,Nat}`, application pointwise); the right side is one element of `inj{State,KItem}(⟦State⟧)` (axiom 74, `[subsort]`).
So every model of Γ_D puts each injected `State` among the injected `Nat`s in `⟦KItem⟧` and, symmetrically, makes the images of all 15 injections into `KItem` coincide; a model whose `KItem` keeps the injected sorts apart (the term algebra M1.4 intends) does not satisfy Γ_D.
`injections.tex` raises the same concern for instances outside the subsort order and calls the unrestricted axioms "aggressive" (evidence only).
Options: restrict the axiom's sort variables to subsort chains (a CHOICE departing from the KORE text), leave `[simplification]` axioms out of Γ_D and prove them as lemmas (group A's proposal), or accept models with merged injections.

F2. Axiom 202 (`[simplification]`), `⌈K0 |-> K1 Rest⌉ = (K0 in_keys Rest = false) ∧ ⌈K1⌉` with set variables `@VarK0`, `@VarK1`, `@VarRest`, is false for finite maps.
Free set variables of an axiom range over all subsets of their sort ([Thesis] p. 73).
With `@VarK0 = {a, b}`, `a` a key of `Rest` and `b` not, and `@VarK1 = {v}`: the left side is `⟦Q0⟧`, since `b |-> v Rest` is defined; the right side is empty, since `in_keys({a,b}, Rest) = {true, false} ≠ {false}`.
So no model of Γ_D interprets `SortMap` as finite maps with pointwise application.
A degenerate choice appears to satisfy axiom 202 and the other Map axioms kompile emits (a one-element `⟦SortMap⟧`, every map operation constant, `_in_keys(_)_` constantly `false`; inference, for M1.4 to confirm).
For the milestone's open point about the hooked axioms, this means: not satisfiable by the intended choice for `Map`; possibly by a degenerate one.

F3. The no-junk axioms have no μ.
Axiom 107 is `⟦SortNat⟧ = z ∪ s(⟦SortNat⟧)` (a fixpoint equation), satisfied by non-standard carriers such as ℕ plus a copy of ℤ; [FoSSaCS] p. 210 and [AML-TR] App. F use `⟦Nat⟧ = μD. z ∨ s D`.
The no-junk axioms of the hooked `SortBool`, `SortInt` and `SortKConfigVar` (97, 102, 105) are `⊤[s] ∨[s] ⊥[s] = ⟦s⟧`, valid in every model.
`SortK`, `SortList`, `SortMap`, `SortSet` and `SortMInt` have none.
So "every model of Γ_D" includes non-standard ones; statement (3) of `Q-statement-package` (`done(z)` is stuck) will need the closure extension and may need μ no-junk as well.

F4. The attribute omissions listed above (`kseq`, `dotk`, `append`, `SetItem`, `_|->_`, missing distinctness).
In particular `kseq` is not functional in Γ_D, so a configuration's `<k>` contents may denote the empty set in some model.

F5. Domain values are unconstrained (T-dv): no axiom of Γ_D states `dv[SortBool]("true") ≠ dv[SortBool]("false")` or that a literal denotes one element; whether another axiom forces either is not checked here.

F6. The 18 `[simplification]` axioms (axiom 3, axiom 202, and 16 `selector-inverse` axioms) are axioms of Γ_D, as D-axiom requires; F1 and F2 show that two of them are false in the intended model, which supports group A's inference that simplification lemmas should be theorems checked against Γ_D, not axioms of it.

## Not in this step

The closure extension (M1.3), any model or soundness statement (M1.3, M1.4), and hooks' domain theories.

## Rule count

| Status | Rules |
|---|---|
| SOURCE (36) | T-sort; G-def, G-sort, G-nonempty, G-arity, G-ceil-arity, G-ceil-def, G-next-arity; T-axiom, T-evar, T-svar, T-app, T-and, T-not, T-exists, T-mu, T-or, T-implies, T-iff, T-forall, T-top, T-bottom, T-nu, T-ceil, T-floor, T-equals, T-in, T-next, T-rewrites, T-assoc; D-scope, D-sort, D-symbol, D-attributes, D-alias, D-axiom |
| CHOICE (10) | S-param, S-args, S-sortof, G-sorts, G-dv-arity, T-dv, T-nary, T-in-nonvar, T-string, D-claim |
| GAP (1) | T-alias |
