/-
  The AML signature generated from a KORE definition, and the sorted notations
  through which KORE's connectives enter applicative matching logic (AML).

  Every definition here cites the source it transcribes; TRANSLATION.md lists the rules
  with the same rule ids (T-…, S-…, A-…).
  Sources:
  - [Thesis] X. Chen, "Matching mu-Logic", PhD thesis, UIUC 2023:
    §2.13 (printed pp. 29–34), Definition 4.1 (p. 72), §7.2 (pp. 163–165), §7.3.2 (p. 166).
  - [AML-TR] X. Chen, G. Roşu, "Applicative Matching Logic: Semantics of K", TR 2020:
    §4.2 (p. 11), §7 (p. 18), §8 (p. 19), Appendix G.2 (pp. 34–35).
  - [FoSSaCS] X. Chen, H. Cheval, D. Lucanu, G. Roşu, "𝕂 Definitions as Matching Logic
    Theories, Formally", FoSSaCS 2026: §2.3 (pp. 204–206), §4.1 (pp. 208–209).
-/
import MatchingLogic
import KoreParser

set_option autoImplicit false

namespace KoreAML

open ML

/-- The AML signature Σ^AML generated from a KORE definition.

[Thesis] §7.2, p. 163: `Σ^AML = {⌈_⌉, ⊤_} ∪ S^MmL ∪ Σ^MmL`; the constructors below are
that set, extended as TRANSLATION.md records:
`sortSort` (the sort of sorts, [FoSSaCS] §2.3, [AML-TR] §4.2), `ceil` (the MmL definedness
symbols of [Thesis] Def. 2.49, which belong to Σ^MmL), `next` (one-path next, [FoSSaCS] p. 206,
[AML-TR] §8), and the CHOICE constructors `dv`, `str`, `untranslated`. -/
inductive Sym where
  /-- `⌈_⌉`, the AML definedness symbol ([Thesis] (7.7)). -/
  | defined
  /-- `⊤_`, the inhabitant symbol ([Thesis] §7.2); printed `⟦s⟧` as in [AML-TR] §4.2. -/
  | inh
  /-- `Sort`, whose inhabitants are the sorts ([FoSSaCS] §2.3; [Thesis] §7.3.2). -/
  | sortSort
  /-- A KORE sort constructor (`sort` or `hooked-sort`), applied to its sort arguments. -/
  | sort (name : String)
  /-- A KORE symbol (`symbol` or `hooked-symbol`, `inj` included), applied to its sort
  arguments and then to its arguments. -/
  | symbol (name : String)
  /-- The family `⌈_⌉^{s'}_s` of [Thesis] Def. 2.49, applied as `ceil s s' φ`. -/
  | ceil
  /-- `•`, one-path next. -/
  | next
  /-- CHOICE (TRANSLATION.md T-dv): the domain value `\dv{s}("lit")`, applied as `dv_lit s`. -/
  | dv (lit : String)
  /-- CHOICE (TRANSLATION.md T-string): a string-literal pattern; unused by the subject. -/
  | str (lit : String)
  /-- A marker for a construct the translation does not cover (alias applications,
  sorts that cannot be computed); the checks require that none occurs. -/
  | untranslated (what : String)
  deriving DecidableEq, Repr, Inhabited

instance : HasDefined Sym := ⟨Sym.defined⟩

/-- AML patterns over the generated signature. -/
abbrev P := Pattern Sym

def sym (σ : Sym) : P := .symbol σ

/-- `⟦s⟧`, i.e. `⊤_ s`: the inhabitants of sort `s` ([Thesis] §7.2; [AML-TR] §4.2). -/
def inhOf (s : P) : P := sym .inh ⬝ s

/-- `⟦Sort⟧`, the inhabitants of the sort of sorts. -/
def sortsDomain : P := inhOf (sym .sortSort)

/-- Application of a head to a list of arguments, left-nested: `σ φ₁ … φₙ` ([Thesis] (7.14)). -/
def appList (head : P) : List P → P
  | [] => head
  | φ :: φs => appList (head ⬝ φ) φs

/-- Right-nested conjunction, `⊤` when empty: the "well-sorted" conjunction of [Thesis] (7.11). -/
def conjList : List P → P
  | [] => ⊤
  | [φ] => φ
  | φ :: φs => φ ⋀ conjList φs

/-- Right-nested AML disjunction, `⊥` when empty. -/
def disjList : List P → P
  | [] => ⊥
  | [φ] => φ
  | φ :: φs => φ ⋁ disjList φs

/-! ## Sorted connectives

Each is the AML image, under [Thesis] AML2 (7.12)–(7.18), of an MmL primitive or of an MmL
notation ([Thesis] (2.95)–(2.97), (2.100)–(2.103), (4.6)).
The sort arguments `s`, `s'` are AML patterns (sort terms, possibly with sort variables). -/

/-- (7.16): `AML2(¬φ_s) = ¬_s AML2(φ) ≡ ¬AML2(φ) ∧ ⊤_s` (sorted negation). -/
def sNot (s φ : P) : P := (∼φ) ⋀ inhOf s

/-- (7.15): `AML2(φ ∧ φ') = AML2(φ) ∧ AML2(φ')`. -/
def sAnd (φ ψ : P) : P := φ ⋀ ψ

/-- (2.95): `φ₁ ∨ φ₂ ≡ ¬(¬φ₁ ∧ ¬φ₂)`, translated by (7.15), (7.16). -/
def sOr (s φ ψ : P) : P := sNot s (sAnd (sNot s φ) (sNot s ψ))

/-- (2.96): `φ₁ → φ₂ ≡ ¬φ₁ ∨ φ₂`. -/
def sImp (s φ ψ : P) : P := sOr s (sNot s φ) ψ

/-- (2.96): `φ₁ ↔ φ₂ ≡ (φ₁ → φ₂) ∧ (φ₂ → φ₁)`. -/
def sIff (s φ ψ : P) : P := sAnd (sImp s φ ψ) (sImp s ψ φ)

/-- (7.17), with the bound variable's own sort `s'` as [AML-TR] App. G.2 (p. 34) writes it
(the thesis prints `⊤_s`, a typo: see TRANSLATION.md T-exists):
`AML2(∃x:s'. φ) = ∃x. (x ∈ ⊤_{s'}) ∧ AML2(φ)`. -/
def sExists (x : EVar) (s' φ : P) : P := ∃∃ x ((x ∈∈ inhOf s') ⋀ φ)

/-- (2.95): `∀x:s'. φ ≡ ¬∃x:s'. ¬φ`, at the sort `s` of `φ`. -/
def sForall (s : P) (x : EVar) (s' φ : P) : P := sNot s (sExists x s' (sNot s φ))

/-- The element variable bound by `⊤_s ≡ ∃x:s. x:s`.
Index 0 is reserved for it; KORE variables get indices from 1 (see `VarTable`). -/
def topVar : EVar := ⟨0⟩

/-- (2.96): `⊤_s ≡ ∃x:s. x:s`, translated by (7.17), (7.12). -/
def sTop (s : P) : P := sExists topVar s (.evar topVar)

/-- (2.97): `⊥_s ≡ ¬⊤_s`. -/
def sBot (s : P) : P := sNot s (sTop s)

/-- Def. 2.49 (2.98) with (7.14): `AML2(⌈φ⌉^{s'}_s) = ceil s s' AML2(φ)`. -/
def sCeil (s s' φ : P) : P := sym .ceil ⬝ s ⬝ s' ⬝ φ

/-- (2.100): `⌊φ⌋^{s'}_s ≡ ¬⌈¬φ⌉^{s'}_s` (outer negation at `s'`, inner at `s`). -/
def sFloor (s s' φ : P) : P := sNot s' (sCeil s s' (sNot s φ))

/-- (2.101): `φ₁ =^{s'}_s φ₂ ≡ ⌊φ₁ ↔ φ₂⌋^{s'}_s`. -/
def sEquals (s s' φ ψ : P) : P := sFloor s s' (sIff s φ ψ)

/-- (2.102): `x ∈^{s'}_s φ ≡ ⌈x ∧ φ⌉^{s'}_s` (applied to any left operand: TRANSLATION.md T-in). -/
def sIn (s s' φ ψ : P) : P := sCeil s s' (sAnd φ ψ)

/-- `•φ`: one-path next, unsorted as [FoSSaCS] p. 206 and [AML-TR] §8 write it. -/
def sNext (φ : P) : P := sym .next ⬝ φ

/-- `φ → •ψ` at sort `s`: a rewrite rule ([FoSSaCS] p. 206; [AML-TR] §8 (Semantics)). -/
def sRewrites (s φ ψ : P) : P := sImp s φ (sNext ψ)

/-- (4.6): `νX. φ ≡ ¬µX. ¬φ[¬X/X]`, at the sort `s` of `X`, translated by (7.16), (7.18). -/
def sNu (s : P) (X : SVar) (φ : P) : P :=
  sNot s (.mu X (sNot s (φ.substSvar X (sNot s (.svar X)))))

/-! ## Notation for the generated (Γ^AML) axioms -/

/-- `ws ⇒ φ` where `ws` is the conjunction of guards; just `φ` when there is no guard.
Used for the generated axioms (G-rules); translated KORE axioms use (7.10) literally. -/
def guarded : List P → P → P
  | [], φ => φ
  | guards, φ => conjList guards ⇒ φ

/-- The guard of a sort variable `α`: `α ∈ ⟦Sort⟧` (TRANSLATION.md S-param). -/
def sortGuard (α : EVar) : P := α ∈∈ sortsDomain

/-- `φ ≠ ψ`, i.e. `¬(φ = ψ)` ([AML-TR] §2.3; used by [Thesis] (7.8) as `⊤_s ≠ ∅`). -/
def notEqual (φ ψ : P) : P := ∼(φ ≡ ψ)

end KoreAML
