/-
  KCore, outside the cone: a rule axiom whose `requires` the text writes as a pattern at Bool
  equated with `true` where Γ's item writes a Bool term (`predicateAtBool`, `andAtBool`), in the
  direction from Γ to the text at values (`EntailsAtValues`).

  - `ruleItem_of_empty`: the item of `\rewrites{C}(L, r)` holds at a valuation where `L` holds
    nothing.
  - `boolTwo`: in a model of the signature and the domains, Bool is one sort, and the values
    `false` and `true` denote two elements of it.
  - `eqTrue_empty`: `\equals{SortBool{}, s}(p, \dv{SortBool{}}("true"))` holds nothing where `p`
    holds the same of every two elements of Bool: it would have to hold `true` and not `false`.
  - `ceil_const`: `\ceil{S, SortBool{}}(p)`, where `p`'s elements are in the sort `S`, holds all of
    Bool or none of it.
  - `substAt ρ p`: the pattern `p` with each element variable `x` for which `ρ x` is a pattern
    replaced by it, under applications only. `substAt_iff`: where each such `ρ x` denotes exactly
    the element the valuation gives `x`, the two patterns denote the same elements.
  - `boolLits_of_text`: the Bool literals from five sentences a text of module INT-KORE writes
    (`eqIntTrueLeftAx`, `neqIntFalseLeftAx`, `eqIntFalseRightAx`, and the functional sentences of
    `_==Int_` and `_=/=Int_`, `fnlBoolAx`), with definedness, the sort constants Int and Bool,
    `⌈_⌉`'s definition, an element of Int and the arity of the two literals: `false` and `true`
    each denote one element of Bool, and the two are apart. A sentence equates its sides at a sort
    among that sort's elements only; that a literal holds nothing outside Bool is its arity item.
    `boolLits_of_text_sig` takes the signature items from `ΓSig`; `eqTrue_empty_lits` and
    `ensFalse_empty_lits` are `eqTrue_empty` and `TieRhs.ensFalse_empty` from that conclusion.
  - `boolLits_of_bool_text_sig`: for a text without those sentences, each literal one element of
    Bool from four other sentences (the equation `isK(K) = true` and `isK`'s functional
    sentence, the equation `notBool(true) = false` and `notBool_`'s functional sentence) with an
    element of K. That the two elements differ is not derived there.
  - `boolTrue_of_text_sig`, `boolFalse_of_text_sig`: one literal alone, from its two sentences
    (eq-int-true-left with `_==Int_`'s functional sentence; neq-int-false-left with `_=/=Int_`'s).
-/
import KcoreSpec.TieRuleLhs

set_option autoImplicit false

namespace KCore

namespace TieReqBool

open ML Faithful KoreAML

mutual
  /-- `p` with each element variable `x` for which `ρ x` is a pattern replaced by it, under
  applications; a pattern of another form is unchanged. -/
  def substAt (ρ : Kore.EVar → Option Kore.Pattern) : Kore.Pattern → Kore.Pattern
    | .var (.evar x) => (ρ x).getD (.var (.evar x))
    | .app h ss ps => .app h ss (substAtList ρ ps)
    | p => p
    termination_by structural p => p
  def substAtList (ρ : Kore.EVar → Option Kore.Pattern) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => substAt ρ p :: substAtList ρ ps
    termination_by structural ps => ps
end

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A rule axiom holds where its left side holds nothing.** -/
theorem ruleItem_of_empty (hD : DefOK I) {t : VarTable} {free : List VarKey} {C : Kore.KSort}
    {L r : Kore.Pattern} {e : Valuation M} (h : ∀ a, ¬ (tr ⟨t, []⟩ L).interpret I e a) (m : M) :
    (TieRuleLhs.itemAt t free C L r).interpret I e m := by
  unfold TieRuleLhs.itemAt
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  have hT : tr ⟨t, []⟩ (.rewrites C L r) = sRewrites (trSort t C) (tr ⟨t, []⟩ L) (tr ⟨t, []⟩ r) := by rw [tr]
  rw [hT]
  unfold sRewrites
  rw [interp_sImp]
  exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, fun hl => absurd hl (h a)⟩⟩

section subst
variable {t : VarTable} {e : Valuation M} {ρ : Kore.EVar → Option Kore.Pattern}

set_option linter.unusedSectionVars false in
mutual
  /-- **A substitution of patterns denoting the variables' elements keeps what a pattern
  denotes.** -/
  theorem substAt_iff
      (hρ : ∀ x q, ρ x = some q → ∀ m, (tr ⟨t, []⟩ q).interpret I e m ↔ m = e.evalEvar (t.ev (evarKey x))) :
      ∀ (p : Kore.Pattern) (m : M), (tr ⟨t, []⟩ (substAt ρ p)).interpret I e m ↔ (tr ⟨t, []⟩ p).interpret I e m
    | .var (.evar x), m => by
      rw [substAt]
      cases hx : ρ x with
      | none => exact Iff.rfl
      | some q =>
        rw [Option.getD_some, hρ x q hx m, tr, interp_evar]
    | .app h ss ps, m => by
      rw [substAt, tr, tr]
      split
      · exact Iff.rfl
      · exact substAtList_iff hρ ps _ _ (fun _ => Iff.rfl) m
    | .var (.svar _), _ => by rw [substAt] <;> simp
    | .string _, _ => by rw [substAt] <;> simp
    | .top _, _ => by rw [substAt] <;> simp
    | .bottom _, _ => by rw [substAt] <;> simp
    | .not _ _, _ => by rw [substAt] <;> simp
    | .and _ _, _ => by rw [substAt] <;> simp
    | .or _ _, _ => by rw [substAt] <;> simp
    | .implies _ _ _, _ => by rw [substAt] <;> simp
    | .iff _ _ _, _ => by rw [substAt] <;> simp
    | .exist _ _ _, _ => by rw [substAt] <;> simp
    | .forall _ _ _, _ => by rw [substAt] <;> simp
    | .mu _ _, _ => by rw [substAt] <;> simp
    | .nu _ _, _ => by rw [substAt] <;> simp
    | .ceil _ _ _, _ => by rw [substAt] <;> simp
    | .floor _ _ _, _ => by rw [substAt] <;> simp
    | .equals _ _ _ _, _ => by rw [substAt] <;> simp
    | .in _ _ _ _, _ => by rw [substAt] <;> simp
    | .next _ _, _ => by rw [substAt] <;> simp
    | .rewrites _ _ _, _ => by rw [substAt] <;> simp
    | .dv _ _, _ => by rw [substAt] <;> simp
    | .leftAssoc _ _ _, _ => by rw [substAt] <;> simp
    | .rightAssoc _ _ _, _ => by rw [substAt] <;> simp
  termination_by structural p => p
  theorem substAtList_iff
      (hρ : ∀ x q, ρ x = some q → ∀ m, (tr ⟨t, []⟩ q).interpret I e m ↔ m = e.evalEvar (t.ev (evarKey x))) :
      ∀ (ps : List Kore.Pattern) (acc acc' : P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (trArgs ⟨t, []⟩ acc (substAtList ρ ps)).interpret I e m ↔ (trArgs ⟨t, []⟩ acc' ps).interpret I e m
    | [], acc, acc', hacc, m => by
      rw [substAtList, trArgs_nil, trArgs_nil]; exact hacc m
    | p :: ps, acc, acc', hacc, m => by
      rw [substAtList, trArgs_cons, trArgs_cons]
      exact substAtList_iff hρ ps _ _ (interp_app_congr hacc (substAt_iff hρ p)) m
  termination_by structural ps => ps
end

end subst

/-- **Bool is one sort with two elements `false` and `true`**, in a model of the signature and the
domains of a semantics `c`. -/
theorem boolTwo [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c) (hDom : I ⊧ᴵP ΓDomains c)
    (hsf : c.sortOf (KCore.bool false) = some Srt.bool) (hst : c.sortOf (KCore.bool true) = some Srt.bool)
    (hdf : den c (KCore.bool false) = sym (.dv "false") ⬝ sym (.sort "SortBool"))
    (hdt : den c (KCore.bool true) = sym (.dv "true") ⬝ sym (.sort "SortBool")) (t : VarTable) (e : Valuation M) :
    ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB := by rw [trSort_srt]; exact hσB1
  obtain ⟨aF, haf, hif⟩ := TieRhs.den_single_dom hD hDom hsf e
  obtain ⟨aT, hat, hit⟩ := TieRhs.den_single_dom hD hDom hst e
  have htr : ∀ (n : String), tr ⟨t, []⟩ (.dv (srt "Bool") n) = sym (.dv n) ⬝ sym (.sort "SortBool") := by
    intro n; rw [tr, trSort_srt]; rfl
  rw [sortName_bool] at hif hit
  refine ⟨σB, aF, aT, hSB, hσB2, fun m => ?_, fun m => ?_, fun hfa => ?_,
    (interp_inhOf_of (S := sortP "Bool") hσB1).mp hif, (interp_inhOf_of (S := sortP "Bool") hσB1).mp hit⟩
  · rw [htr, ← hdf]; exact haf m
  · rw [htr, ← hdt]; exact hat m
  · have hne := hDom _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.bool false, KCore.bool true, Srt.bool,
      List.contains_iff_mem.mpr bool_distinct, hsf, hst,
      fun h => by have := GroundTerm.cmp_eq _ _ h; simp [KCore.bool] at this, rfl⟩)))) e aF
    rw [interpret_neg, interpret_conj] at hne
    exact hne ⟨(haf aF).mpr rfl, (hat aF).mpr hfa⟩

/-- **`p = true` at Bool holds nothing where `p` holds the same of every two elements of Bool**:
at `true` it must hold, at `false` it must not. -/
theorem eqTrue_empty [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c) (hDom : I ⊧ᴵP ΓDomains c)
    (hsf : c.sortOf (KCore.bool false) = some Srt.bool) (hst : c.sortOf (KCore.bool true) = some Srt.bool)
    (hdf : den c (KCore.bool false) = sym (.dv "false") ⬝ sym (.sort "SortBool"))
    (hdt : den c (KCore.bool true) = sym (.dv "true") ⬝ sym (.sort "SortBool"))
    {t : VarTable} {s : Kore.KSort} {σ : M} {e : Valuation M}
    (hs : ∀ a, (trSort t s).interpret I e a ↔ a = σ) (hσ : IsSort I σ) {p : Kore.Pattern}
    (hp : ∀ σB, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) → IsSort I σB → ∀ x y, Inh I σB x → Inh I σB y →
      ((tr ⟨t, []⟩ p).interpret I e x ↔ (tr ⟨t, []⟩ p).interpret I e y)) (b : M) :
    ¬ (tr ⟨t, []⟩ (.equals (srt "Bool") s p (.dv (srt "Bool") "true"))).interpret I e b := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σB, aF, aT, hSB, hσB, haf, hat, hne, hif, hit⟩ := boolTwo hD hSig hDom hsf hst hdf hdt t e
  have hT : tr ⟨t, []⟩ (.equals (srt "Bool") s p (.dv (srt "Bool") "true")) =
      sEquals (trSort t (srt "Bool")) (trSort t s) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ (.dv (srt "Bool") "true")) := by rw [tr]
  rw [hT, interp_sEquals hD hc hSB hs hσB hσ]
  rintro ⟨-, h⟩
  have h1 := (h aT hit).mpr ((hat aT).mpr rfl)
  have h2 := (hp σB hSB hσB aF aT hif hit).mpr h1
  exact hne ((hat aF).mp ((h aF hif).mp h2))

/-- **`\ceil{S, SortBool{}}(p)` is all of Bool or none of it**, where `p`'s elements are in `S`. -/
theorem ceil_const [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable} {S : Kore.KSort} {σS σB : M}
    {e : Valuation M} (hS : ∀ a, (trSort t S).interpret I e a ↔ a = σS) (hσS : IsSort I σS)
    (hSB : ∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) (hσB : IsSort I σB) {p : Kore.Pattern}
    (hp : ∀ a, (tr ⟨t, []⟩ p).interpret I e a → Inh I σS a) (x y : M) (hx : Inh I σB x) (hy : Inh I σB y) :
    (tr ⟨t, []⟩ (.ceil S (srt "Bool") p)).interpret I e x ↔ (tr ⟨t, []⟩ (.ceil S (srt "Bool") p)).interpret I e y := by
  have hT : tr ⟨t, []⟩ (.ceil S (srt "Bool") p) = sCeil (trSort t S) (trSort t (srt "Bool")) (tr ⟨t, []⟩ p) := by rw [tr]
  rw [hT, interp_sCeil hD hc hS hSB hσS hσB hp, interp_sCeil hD hc hS hSB hσS hσB hp]
  exact ⟨fun h => ⟨h.1, hy⟩, fun h => ⟨h.1, hx⟩⟩

end

/-! ## The Bool literals from the text's sentences of INT-KORE -/

/-- The sort variable `Q0` of a simplification sentence. -/
def Q0v : Kore.SortVar := ⟨⟨⟨"Q0"⟩⟩⟩
def Q0 : Kore.KSort := .var Q0v
def eqIntName : String := "Lbl'UndsEqlsEqls'Int'Unds'"
def neqIntName : String := "Lbl'UndsEqlsSlshEqls'Int'Unds'"

/-- The functional sentence of a symbol `f` from two Ints to Bool:
`axiom{R} \exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val, f(K0:SortInt{}, K1:SortInt{})))`. -/
def fnlBoolAx (f : String) : Kore.Axiom :=
  ⟨[Rv], .exist R (evar "Val" (srt "Bool"))
    (.equals (srt "Bool") R (ev "Val" (srt "Bool")) (ap f [ev "K0" (srt "Int"), ev "K1" (srt "Int")])), []⟩

/-- A sentence `axiom{R, Q0} \implies{R}(\top{R}(), \equals{Q0, R}(l, \and{Q0}(r, \top{Q0}())))`. -/
def simpAx (l r : Kore.Pattern) : Kore.Axiom :=
  ⟨[Rv, Q0v], .implies R (.top R) (.equals Q0 R l (.and Q0 [r, .top Q0])), []⟩

/-- `\equals{SortInt{}, Q0}(K1, K2)`. -/
def k12Eq : Kore.Pattern := .equals (srt "Int") Q0 (ev "VarK1" (srt "Int")) (ev "VarK2" (srt "Int"))
def k12App (f : String) : Kore.Pattern := ap f [ev "VarK1" (srt "Int"), ev "VarK2" (srt "Int")]

/-- INT-KORE.eq-int-true-left: `{K1 ==Int K2 #Equals true} => {K1 #Equals K2}`. -/
def eqIntTrueLeftAx : Kore.Axiom :=
  simpAx (.equals (srt "Bool") Q0 (k12App eqIntName) (.dv (srt "Bool") "true")) k12Eq
/-- INT-KORE.neq-int-false-left: `{K1 =/=Int K2 #Equals false} => {K1 #Equals K2}`. -/
def neqIntFalseLeftAx : Kore.Axiom :=
  simpAx (.equals (srt "Bool") Q0 (k12App neqIntName) (.dv (srt "Bool") "false")) k12Eq
/-- INT-KORE.eq-int-false-rigth: `{false #Equals K1 ==Int K2} => #Not({K1 #Equals K2})`. -/
def eqIntFalseRightAx : Kore.Axiom :=
  simpAx (.equals (srt "Bool") Q0 (.dv (srt "Bool") "false") (k12App eqIntName)) (.not Q0 k12Eq)

/-- The translation of a sentence, whatever its place in a text: the pattern of `trAxiom` reads
neither the index nor the module, and the sort of these sentences is read without the symbol
declarations. -/
def sentPat (a : Kore.Axiom) : P := (trAxiom [] [] ⟨0, "", a⟩).pat

def intP : P := sym (.sort "SortInt")
def boolP : P := sym (.sort "SortBool")
/-- `f(x, y)` at the variables 3 and 4, the two Int variables of each of the five sentences. -/
def app34 (f : String) : P := sym (.symbol f) ⬝ .evar ⟨3⟩ ⬝ .evar ⟨4⟩
def litP (n : String) : P := sym (.dv n) ⬝ boolP
def g34 : List P := [(⟨3⟩ : EVar) ∈∈ inhOf intP, (⟨4⟩ : EVar) ∈∈ inhOf intP]

theorem fnlBool_shape (f : String) : sentPat (fnlBoolAx f) =
    (conjList (sortGuard ⟨1⟩ :: g34) ⇒
      (sExists ⟨2⟩ boolP (sEquals boolP (.evar ⟨1⟩) (.evar ⟨2⟩) (app34 f)) ≡ inhOf (.evar ⟨1⟩))) := by
  rfl

theorem simp_shape_tt : sentPat eqIntTrueLeftAx =
    (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (app34 eqIntName) (litP "true"))
        (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)))) ≡ inhOf (.evar ⟨1⟩))) := by
  decide +kernel

theorem simp_shape_nf : sentPat neqIntFalseLeftAx =
    (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (app34 neqIntName) (litP "false"))
        (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)))) ≡ inhOf (.evar ⟨1⟩))) := by
  decide +kernel

theorem simp_shape_ff : sentPat eqIntFalseRightAx =
    (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (litP "false") (app34 eqIntName))
        (sAnd (sNot (.evar ⟨2⟩) (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩))) (sTop (.evar ⟨2⟩)))) ≡
        inhOf (.evar ⟨1⟩))) := by
  decide +kernel

section lits
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The valuation that gives the variables 1 and 2 (the sort variables) `σ` and every other
variable `n`. -/
def valAt (σ n : M) : Valuation M := ⟨fun x => match x with | ⟨1⟩ => σ | ⟨2⟩ => σ | _ => n, fun _ _ => False⟩

/-- An element of `f(n, n)`. -/
def AppAt (I : Interpretation KoreAML.Sym M) (f : String) (n b : M) : Prop :=
  ∃ s x, I.evalSymb (.symbol f) s ∧ I.evalApp s n x ∧ I.evalApp x n b

theorem interp_app34 {f : String} {e : Valuation M} {n : M} (h3 : e.evalEvar ⟨3⟩ = n) (h4 : e.evalEvar ⟨4⟩ = n)
    (b : M) : (app34 f).interpret I e b ↔ AppAt I f n b := by
  unfold app34 AppAt
  simp only [interp_app, interp_sym, interp_evar]
  constructor
  · rintro ⟨x, y, ⟨s, z, hs, rfl, hx⟩, rfl, hb⟩
    exact ⟨s, x, hs, h3 ▸ hx, h4 ▸ hb⟩
  · rintro ⟨s, x, hs, hx, hb⟩
    exact ⟨x, _, ⟨s, _, hs, rfl, h3 ▸ hx⟩, rfl, h4 ▸ hb⟩

variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI σB n : M}
  (hI : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI : IsSort I σI)
  (hB : ∀ a, I.evalSymb (.sort "SortBool") a ↔ a = σB) (hσB : IsSort I σB) (hn : Inh I σI n)
include hD hI hσI hn

theorem g34_at (e : Valuation M) (h3 : e.evalEvar ⟨3⟩ = n) (h4 : e.evalEvar ⟨4⟩ = n) (m : M) :
    ∀ w ∈ g34, w.interpret I e m := by
  intro w hw
  simp only [g34, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [interp_member hD, interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a), h3]; exact hn
  · rw [interp_member hD, interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a), h4]; exact hn

omit hI hn in
theorem sortGuard_at (e : Valuation M) {x : EVar} (hx : e.evalEvar x = σI) (m : M) :
    (sortGuard x).interpret I e m := by
  unfold sortGuard; rw [interp_member hD, interp_sortsDomain, hx]; exact hσI

include hc hB hσB

/-- **A functional sentence at `(n, n)`**: among Bool's elements, `f(n, n)` holds exactly one. -/
theorem fnl_one {f : String} (h : I ⊧ᴵ sentPat (fnlBoolAx f)) :
    ∃ y, Inh I σB y ∧ ∀ b, Inh I σB b → (AppAt I f n b ↔ b = y) := by
  have h1 := h (valAt σI n) n
  rw [fnlBool_shape, interpret_impl] at h1
  have h2 := h1 (interp_conjList fun w hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact sortGuard_at hD hσI _ rfl n
    · exact g34_at hD hI hσI hn _ rfl rfl n w hw)
  rw [interp_equal hD] at h2
  have h3 := (h2 n).mpr ((interp_inhOf_of (σ := σI) (fun a => Iff.rfl)).mpr hn)
  rw [interp_sExists] at h3
  obtain ⟨y, hy1, hy2⟩ := h3
  rw [interp_member hD, interp_inhOf_of (S := boolP) (σ := σB) (fun a => hB a)] at hy1
  simp only [Function.update_same] at hy1
  rw [interp_sEquals hD hc (S := boolP) (σ := σB) (σ' := σI) (fun a => hB a) (fun a => Iff.rfl) hσB hσI] at hy2
  refine ⟨y, hy1, fun b hb => ?_⟩
  have h4 := hy2.2 b hb
  rw [interp_app34 (n := n) rfl rfl, interp_evar] at h4
  simp only [Function.update_same] at h4
  exact h4.symm

/-- **A simplification sentence at `(n, n)`**, the sort variables at Int: its two sides hold the
same of `n`. -/
theorem simp_at {L Rr : P}
    (h : I ⊧ᴵ (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩) L Rr) ≡ inhOf (.evar ⟨1⟩)))) :
    L.interpret I (valAt σI n) n ↔ Rr.interpret I (valAt σI n) n := by
  have h1 := h (valAt σI n) n
  rw [interpret_impl] at h1
  have h2 := h1 (interp_conjList fun w hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact sortGuard_at hD hσI _ rfl n
    rcases List.mem_cons.mp hw with rfl | hw
    · exact sortGuard_at hD hσI _ rfl n
    · exact g34_at hD hI hσI hn _ rfl rfl n w hw)
  rw [interp_equal hD] at h2
  have hin : (inhOf (.evar ⟨1⟩) : P).interpret I (valAt σI n) n :=
    (interp_inhOf_of (σ := σI) (fun a => Iff.rfl)).mpr hn
  have h3 := (h2 n).mpr hin
  rw [interp_sImp] at h3
  have h4 := h3.2 ((interp_sTop hD rfl n).mpr hin)
  rw [interp_sEquals hD hc (σ := σI) (σ' := σI) (fun a => Iff.rfl) (fun a => Iff.rfl) hσI hσI] at h4
  exact h4.2 n hn

/-- `\equals{SortBool{}, Q0}(x, y)` at `n`, Q0 at Int: `x` and `y` hold the same of Bool's
elements. -/
theorem boolEq_at {x y : P} : (sEquals boolP (.evar ⟨2⟩) x y).interpret I (valAt σI n) n ↔
    ∀ b, Inh I σB b → (x.interpret I (valAt σI n) b ↔ y.interpret I (valAt σI n) b) := by
  rw [interp_sEquals hD hc (S := boolP) (σ := σB) (σ' := σI) (fun a => hB a) (fun a => Iff.rfl) hσB hσI]
  exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

/-- `\and{Q0}(\equals{SortInt{}, Q0}(K1, K2), \top{Q0}())` holds of `n` at `(n, n)`. -/
theorem k12_at : (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)).interpret I (valAt σI n) n := by
  rw [interp_sEquals hD hc (S := intP) (σ := σI) (σ' := σI) (fun a => hI a) (fun a => Iff.rfl) hσI hσI]
  exact ⟨hn, fun _ _ => Iff.rfl⟩

omit hI hσI hn hc in
/-- A literal of Bool holds elements of Bool only (its arity item). -/
theorem lit_in_bool {lit : String} (hd : I ⊧ᴵ (dvArityItem lit).pat) (e : Valuation M) (m : M)
    (h : (litP lit).interpret I e m) : Inh I σB m := by
  have h1 := hd ⟨fun _ => σB, e.evalSvar⟩ default
  unfold dvArityItem at h1
  dsimp only at h1
  unfold guarded at h1
  have h2 := h1 (by
    unfold conjList sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσB)
  rw [interp_included hD] at h2
  have h3 := h2 m (by
    unfold litP boolP at h
    rw [interp_app] at h ⊢
    obtain ⟨a, b, ha, hb, hab⟩ := h
    exact ⟨a, σB, ha, rfl, (hB b).mp hb ▸ hab⟩)
  exact (interp_inhOf_of (σ := σB) (fun a => Iff.rfl)).mp h3

/-- **One literal from its two sentences.** Where `f(n, n)` and the literal `lit` hold the same of
Bool's elements (a simplification sentence `{f(K1, K2) #Equals lit} => {K1 #Equals K2}` at
`(n, n)`) and `f` has its functional sentence, the literal denotes one element, an element of
Bool. -/
theorem lit_one_core {f lit : String} (hd : I ⊧ᴵ (dvArityItem lit).pat)
    (h : I ⊧ᴵ (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (app34 f) (litP lit))
        (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)))) ≡ inhOf (.evar ⟨1⟩))))
    (hf : I ⊧ᴵ sentPat (fnlBoolAx f)) (e : Valuation M) :
    ∃ a, (∀ m, (litP lit).interpret I e m ↔ m = a) ∧ Inh I σB a := by
  obtain ⟨v, hv, hv1⟩ := fnl_one hD hc hI hσI hB hσB hn hf
  have hk : (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)) : P).interpret I (valAt σI n) n :=
    interp_sAnd.mpr ⟨k12_at hD hc hI hσI hB hσB hn,
      (interp_sTop hD rfl n).mpr ((interp_inhOf_of (σ := σI) (fun a => Iff.rfl)).mpr hn)⟩
  have e1 := (boolEq_at hD hc hI hσI hB hσB hn).mp ((simp_at hD hc hI hσI hB hσB hn h).mpr hk)
  have hcl : ∀ m, (litP lit).interpret I e m ↔ (litP lit).interpret I (valAt σI n) m :=
    fun m => ((Closed.sym _).app (Closed.sym _)).interp _ _ m
  refine ⟨v, fun m => ?_, hv⟩
  rw [hcl]
  constructor
  · intro hm
    have hmB := lit_in_bool hD hB hσB hd _ m hm
    exact (hv1 m hmB).mp ((interp_app34 rfl rfl m).mp ((e1 m hmB).mpr hm))
  · rintro rfl
    exact (e1 m hv).mp ((interp_app34 rfl rfl m).mpr ((hv1 m hv).mpr rfl))

/-- **The Bool literals from the text's sentences.** In an interpretation with definedness,
`⌈_⌉`'s definition, the sort constants Int and Bool, an element `n` of Int and the arity of the
literals `true` and `false`, that satisfies eq-int-true-left, neq-int-false-left,
eq-int-false-rigth and the functional sentences of `_==Int_` and `_=/=Int_`: `false` and `true`
each denote one element of Bool, and the two elements differ. `n ==Int n` is one element of Bool
among Bool's and agrees there with `true`; `n =/=Int n` likewise with `false`; and `false` does
not agree with `n ==Int n` on Bool. -/
theorem boolLits_core (hdT : I ⊧ᴵ (dvArityItem "true").pat) (hdF : I ⊧ᴵ (dvArityItem "false").pat)
    (h1 : I ⊧ᴵ sentPat eqIntTrueLeftAx) (h2 : I ⊧ᴵ sentPat neqIntFalseLeftAx)
    (h3 : I ⊧ᴵ sentPat eqIntFalseRightAx)
    (hf1 : I ⊧ᴵ sentPat (fnlBoolAx eqIntName)) (hf2 : I ⊧ᴵ sentPat (fnlBoolAx neqIntName)) (e : Valuation M) :
    ∃ aF aT, (∀ m, (litP "false").interpret I e m ↔ m = aF) ∧ (∀ m, (litP "true").interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  have hcl : ∀ (lit : String) m, (litP lit).interpret I e m ↔ (litP lit).interpret I (valAt σI n) m :=
    fun lit m => ((Closed.sym _).app (Closed.sym _)).interp _ _ m
  obtain ⟨v, hv, hv1⟩ := fnl_one hD hc hI hσI hB hσB hn hf1
  obtain ⟨w, hw, hw1⟩ := fnl_one hD hc hI hσI hB hσB hn hf2
  rw [simp_shape_tt] at h1
  rw [simp_shape_nf] at h2
  rw [simp_shape_ff] at h3
  have hk : (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)) : P).interpret I (valAt σI n) n :=
    interp_sAnd.mpr ⟨k12_at hD hc hI hσI hB hσB hn,
      (interp_sTop hD rfl n).mpr ((interp_inhOf_of (σ := σI) (fun a => Iff.rfl)).mpr hn)⟩
  have e1 := (boolEq_at hD hc hI hσI hB hσB hn).mp ((simp_at hD hc hI hσI hB hσB hn h1).mpr hk)
  have e2 := (boolEq_at hD hc hI hσI hB hσB hn).mp ((simp_at hD hc hI hσI hB hσB hn h2).mpr hk)
  have e3 : ¬ ∀ b, Inh I σB b → ((litP "false").interpret I (valAt σI n) b ↔ (app34 eqIntName).interpret I (valAt σI n) b) :=
    fun hall => by
      have := (simp_at hD hc hI hσI hB hσB hn h3).mp ((boolEq_at hD hc hI hσI hB hσB hn).mpr hall)
      rw [interp_sAnd, interp_sNot] at this
      exact this.1.1 (k12_at hD hc hI hσI hB hσB hn)
  have hT : ∀ m, (litP "true").interpret I e m ↔ m = v := fun m => by
    rw [hcl]
    constructor
    · intro hm
      have hmB := lit_in_bool hD hB hσB hdT _ m hm
      exact (hv1 m hmB).mp ((interp_app34 rfl rfl m).mp ((e1 m hmB).mpr hm))
    · rintro rfl
      exact (e1 m hv).mp ((interp_app34 rfl rfl m).mpr ((hv1 m hv).mpr rfl))
  have hF : ∀ m, (litP "false").interpret I e m ↔ m = w := fun m => by
    rw [hcl]
    constructor
    · intro hm
      have hmB := lit_in_bool hD hB hσB hdF _ m hm
      exact (hw1 m hmB).mp ((interp_app34 rfl rfl m).mp ((e2 m hmB).mpr hm))
    · rintro rfl
      exact (e2 m hw).mp ((interp_app34 rfl rfl m).mpr ((hw1 m hw).mpr rfl))
  refine ⟨w, v, hF, hT, fun hwv => e3 fun b hb => ?_, hw, hv⟩
  rw [← hcl, hF, interp_app34 (n := n) rfl rfl, hv1 b hb, hwv]

end lits

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **The Bool literals from the text's sentences**, the signature items as sentences: the sort
constants Int and Bool, `⌈_⌉`'s definition, Int's G-nonempty item, and the arity of the two
literals. The conclusion is `boolTwo`'s. -/
theorem boolLits_of_text [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {bi bb bn : Bool}
    (hsI : I ⊧ᴵ (sortConstantItem ⟨"SortInt", [], bi⟩).pat) (hsB : I ⊧ᴵ (sortConstantItem ⟨"SortBool", [], bb⟩).pat)
    (hne : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], bn⟩).pat)
    (hdT : I ⊧ᴵ (dvArityItem "true").pat) (hdF : I ⊧ᴵ (dvArityItem "false").pat)
    (h1 : I ⊧ᴵ sentPat eqIntTrueLeftAx) (h2 : I ⊧ᴵ sentPat neqIntFalseLeftAx)
    (h3 : I ⊧ᴵ sentPat eqIntFalseRightAx)
    (hf1 : I ⊧ᴵ sentPat (fnlBoolAx eqIntName)) (hf2 : I ⊧ᴵ sentPat (fnlBoolAx neqIntName))
    (t : VarTable) (e : Valuation M) :
    ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  obtain ⟨σI, hI, hσI⟩ := sortConst_of hD hsI
  obtain ⟨σB, hB, hσB⟩ := sortConst_of hD hsB
  obtain ⟨n, hn⟩ := nonempty_of hD hne (e := e)
  have hn' : Inh I σI n := (interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a)).mp hn
  obtain ⟨aF, aT, hF, hT, hne', hiF, hiT⟩ := boolLits_core hD hc hI hσI hB hσB hn' hdT hdF h1 h2 h3 hf1 hf2 e
  have htr : ∀ (lit : String), tr ⟨t, []⟩ (.dv (srt "Bool") lit) = litP lit := by
    intro lit; rw [tr, trSort_srt]; rfl
  refine ⟨σB, aF, aT, fun a => by rw [trSort_srt]; exact hB a, hσB, fun m => ?_, fun m => ?_, hne', hiF, hiT⟩
  · rw [htr]; exact hF m
  · rw [htr]; exact hT m

/-- `boolLits_of_text` with the signature items from `ΓSig c`, for a semantics whose sort `sI`
is named Int. -/
theorem boolLits_of_text_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c)
    {sI : Srt} (hsI : sI < nRegSorts + c.sortNames.length) (hnI : c.sortName sI = "Int") {bn : Bool}
    (hne : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], bn⟩).pat)
    (h1 : I ⊧ᴵ sentPat eqIntTrueLeftAx) (h2 : I ⊧ᴵ sentPat neqIntFalseLeftAx)
    (h3 : I ⊧ᴵ sentPat eqIntFalseRightAx)
    (hf1 : I ⊧ᴵ sentPat (fnlBoolAx eqIntName)) (hf2 : I ⊧ᴵ sentPat (fnlBoolAx neqIntName))
    (t : VarTable) (e : Valuation M) :
    ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σI, hI, hσI⟩ := TieRhs.sortSing_sig hD hSig hsI
  rw [hnI] at hI
  have hI : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI := hI
  obtain ⟨σB, hB, hσB⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := c))
  rw [sortName_bool] at hB
  obtain ⟨n, hn⟩ := nonempty_of hD hne (e := e)
  have hn' : Inh I σI n := (interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a)).mp hn
  obtain ⟨aF, aT, hF, hT, hne', hiF, hiT⟩ := boolLits_core hD hc hI hσI hB hσB hn'
    (hSig _ (Or.inr ⟨"true", rfl⟩)) (hSig _ (Or.inr ⟨"false", rfl⟩)) h1 h2 h3 hf1 hf2 e
  have htr : ∀ (lit : String), tr ⟨t, []⟩ (.dv (srt "Bool") lit) = litP lit := by
    intro lit; rw [tr, trSort_srt]; rfl
  refine ⟨σB, aF, aT, fun a => by rw [trSort_srt]; exact hB a, hσB, fun m => ?_, fun m => ?_, hne', hiF, hiT⟩
  · rw [htr]; exact hF m
  · rw [htr]; exact hT m


/-- One literal from its two sentences, the signature items from `ΓSig c`. -/
theorem boolLit_of_text_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c)
    {sI : Srt} (hsI : sI < nRegSorts + c.sortNames.length) (hnI : c.sortName sI = "Int") {bn : Bool}
    (hne : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], bn⟩).pat) {f lit : String}
    (h : I ⊧ᴵ (conjList (sortGuard ⟨1⟩ :: sortGuard ⟨2⟩ :: g34) ⇒
      (sImp (.evar ⟨1⟩) (sTop (.evar ⟨1⟩)) (sEquals (.evar ⟨2⟩) (.evar ⟨1⟩)
        (sEquals boolP (.evar ⟨2⟩) (app34 f) (litP lit))
        (sAnd (sEquals intP (.evar ⟨2⟩) (.evar ⟨3⟩) (.evar ⟨4⟩)) (sTop (.evar ⟨2⟩)))) ≡ inhOf (.evar ⟨1⟩))))
    (hf : I ⊧ᴵ sentPat (fnlBoolAx f)) (t : VarTable) (e : Valuation M) :
    ∃ σB a, (∀ x, (trSort t (srt "Bool")).interpret I e x ↔ x = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") lit)).interpret I e m ↔ m = a) ∧ Inh I σB a := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σI, hI, hσI⟩ := TieRhs.sortSing_sig hD hSig hsI
  rw [hnI] at hI
  have hI : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI := hI
  obtain ⟨σB, hB, hσB⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := c))
  rw [sortName_bool] at hB
  obtain ⟨n, hn⟩ := nonempty_of hD hne (e := e)
  have hn' : Inh I σI n := (interp_inhOf_of (S := intP) (σ := σI) (fun a => hI a)).mp hn
  obtain ⟨a, ha, hia⟩ := lit_one_core hD hc hI hσI hB hσB hn' (hSig _ (Or.inr ⟨lit, rfl⟩)) h hf e
  refine ⟨σB, a, fun x => by rw [trSort_srt]; exact hB x, hσB, fun m => ?_, hia⟩
  have htr : tr ⟨t, []⟩ (.dv (srt "Bool") lit) = litP lit := by rw [tr, trSort_srt]; rfl
  rw [htr]; exact ha m

/-- **`true` is one element of Bool**, from eq-int-true-left, the functional sentence of `_==Int_`,
an element of Int and the signature. -/
theorem boolTrue_of_text_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c)
    {sI : Srt} (hsI : sI < nRegSorts + c.sortNames.length) (hnI : c.sortName sI = "Int") {bn : Bool}
    (hne : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], bn⟩).pat)
    (h1 : I ⊧ᴵ sentPat eqIntTrueLeftAx) (hf1 : I ⊧ᴵ sentPat (fnlBoolAx eqIntName)) (t : VarTable) (e : Valuation M) :
    ∃ σB aT, (∀ x, (trSort t (srt "Bool")).interpret I e x ↔ x = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧ Inh I σB aT :=
  boolLit_of_text_sig hD hSig hsI hnI hne (simp_shape_tt ▸ h1) hf1 t e

/-- **`false` is one element of Bool**, from neq-int-false-left, the functional sentence of
`_=/=Int_`, an element of Int and the signature. -/
theorem boolFalse_of_text_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c)
    {sI : Srt} (hsI : sI < nRegSorts + c.sortNames.length) (hnI : c.sortName sI = "Int") {bn : Bool}
    (hne : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], bn⟩).pat)
    (h2 : I ⊧ᴵ sentPat neqIntFalseLeftAx) (hf2 : I ⊧ᴵ sentPat (fnlBoolAx neqIntName)) (t : VarTable) (e : Valuation M) :
    ∃ σB aF, (∀ x, (trSort t (srt "Bool")).interpret I e x ↔ x = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧ Inh I σB aF :=
  boolLit_of_text_sig hD hSig hsI hnI hne (simp_shape_nf ▸ h2) hf2 t e

/-- `eqTrue_empty` from the literals' facts (the conclusion of `boolTwo`, of `boolLits_of_text`). -/
theorem eqTrue_empty_lits [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {t : VarTable} {s : Kore.KSort} {σ : M} {e : Valuation M}
    (hL : ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT)
    (hs : ∀ a, (trSort t s).interpret I e a ↔ a = σ) (hσ : IsSort I σ) {p : Kore.Pattern}
    (hp : ∀ σB, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) → IsSort I σB → ∀ x y, Inh I σB x → Inh I σB y →
      ((tr ⟨t, []⟩ p).interpret I e x ↔ (tr ⟨t, []⟩ p).interpret I e y)) (b : M) :
    ¬ (tr ⟨t, []⟩ (.equals (srt "Bool") s p (.dv (srt "Bool") "true"))).interpret I e b := by
  obtain ⟨σB, aF, aT, hSB, hσB, haf, hat, hne, hif, hit⟩ := hL
  have hT : tr ⟨t, []⟩ (.equals (srt "Bool") s p (.dv (srt "Bool") "true")) =
      sEquals (trSort t (srt "Bool")) (trSort t s) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ (.dv (srt "Bool") "true")) := by rw [tr]
  rw [hT, interp_sEquals hD hc hSB hs hσB hσ]
  rintro ⟨-, h⟩
  have h1 := (h aT hit).mpr ((hat aT).mpr rfl)
  have h2 := (hp σB hSB hσB aF aT hif hit).mpr h1
  exact hne ((hat aF).mp ((h aF hif).mp h2))

/-- `TieRhs.ensFalse_empty` from the literals' facts: `false = true` at Bool holds nothing. -/
theorem ensFalse_empty_lits [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {t : VarTable} {s : Kore.KSort} {σ : M} {e : Valuation M}
    (hL : ∃ σB aF aT, (∀ a, (trSort t (srt "Bool")).interpret I e a ↔ a = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "false")).interpret I e m ↔ m = aF) ∧
      (∀ m, (tr ⟨t, []⟩ (.dv (srt "Bool") "true")).interpret I e m ↔ m = aT) ∧
      aF ≠ aT ∧ Inh I σB aF ∧ Inh I σB aT)
    (hs : ∀ a, (trSort t s).interpret I e a ↔ a = σ) (hσ : IsSort I σ) (b : M) :
    ¬ (tr ⟨t, []⟩ (TieRhs.ensFalse s)).interpret I e b := by
  obtain ⟨σB, aF, aT, hSB, hσB, haf, hat, hne, hif, hit⟩ := hL
  have hT : tr ⟨t, []⟩ (TieRhs.ensFalse s) =
      sEquals (trSort t (srt "Bool")) (trSort t s) (tr ⟨t, []⟩ (.dv (srt "Bool") "false"))
        (tr ⟨t, []⟩ (.dv (srt "Bool") "true")) := by unfold TieRhs.ensFalse; rw [tr]
  rw [hT, interp_sEquals hD hc hSB hs hσB hσ]
  rintro ⟨-, h⟩
  exact hne ((hat aF).mp ((h aF hif).mp ((haf aF).mpr rfl)))

end

/-! ## The Bool literals from two function equations -/

/-- The functional sentence of a symbol `f` from the sort `s` to Bool:
`axiom{R} \exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val, f(K0:s)))`. -/
def fnl1Ax (f s : String) : Kore.Axiom :=
  ⟨[Rv], .exist R (evar "Val" (srt "Bool"))
    (.equals (srt "Bool") R (ev "Val" (srt "Bool")) (ap f [ev "K0" (srt s)])), []⟩

/-- The equation `f(X0) = lit` at Bool, for `X0` of the sort `s` in `p`:
`axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{s, R}(X0:s, p), \top{R}())),
\equals{SortBool{}, R}(f(X0:s), \and{SortBool{}}(\dv{SortBool{}}(lit), \top{SortBool{}}())))`. -/
def litEqnAx (f s : String) (p : Kore.Pattern) (lit : String) : Kore.Axiom :=
  ⟨[Rv], .implies R (.and R [.top R, .and R [.in (srt s) R (ev "X0" (srt s)) p, .top R]])
    (.equals (srt "Bool") R (ap f [ev "X0" (srt s)])
      (.and (srt "Bool") [.dv (srt "Bool") lit, .top (srt "Bool")])), []⟩

/-- `rule isK(K) => true`. -/
def isKTrueAx : Kore.Axiom := litEqnAx "LblisK" "K" (ev "VarK" (srt "K")) "true"
/-- `rule notBool true => false`. -/
def notTrueFalseAx : Kore.Axiom := litEqnAx "LblnotBool'Unds'" "Bool" (.dv (srt "Bool") "true") "false"

def kP : P := sym (.sort "SortK")

/-- The form of a translated `litEqnAx`, over its guards `ws`, the argument's sort `SA` and `p`. -/
def litEqnP (ws : List P) (SA pP : P) (f lit : String) : P :=
  conjList ws ⇒
    (sImp (.evar ⟨1⟩) (sAnd (sTop (.evar ⟨1⟩)) (sAnd (sIn SA (.evar ⟨1⟩) (.evar ⟨2⟩) pP) (sTop (.evar ⟨1⟩))))
      (sEquals boolP (.evar ⟨1⟩) (sym (.symbol f) ⬝ .evar ⟨2⟩) (sAnd (litP lit) (sTop boolP))) ≡ inhOf (.evar ⟨1⟩))

/-- The form of a translated `fnl1Ax`, over the argument's sort `SA`. -/
def fnl1P (SA : P) (f : String) : P :=
  conjList [sortGuard ⟨1⟩, (⟨3⟩ : EVar) ∈∈ inhOf SA] ⇒
    (sExists ⟨2⟩ boolP (sEquals boolP (.evar ⟨1⟩) (.evar ⟨2⟩) (sym (.symbol f) ⬝ .evar ⟨3⟩)) ≡ inhOf (.evar ⟨1⟩))

theorem fnl1_shape_isK : sentPat (fnl1Ax "LblisK" "K") = fnl1P kP "LblisK" := by decide +kernel
theorem fnl1_shape_not : sentPat (fnl1Ax "LblnotBool'Unds'" "Bool") = fnl1P boolP "LblnotBool'Unds'" := by
  decide +kernel
theorem isKTrue_shape : sentPat isKTrueAx =
    litEqnP [sortGuard ⟨1⟩, (⟨2⟩ : EVar) ∈∈ inhOf kP, (⟨3⟩ : EVar) ∈∈ inhOf kP] kP (.evar ⟨3⟩) "LblisK" "true" := by
  decide +kernel
theorem notTrueFalse_shape : sentPat notTrueFalseAx =
    litEqnP [sortGuard ⟨1⟩, (⟨2⟩ : EVar) ∈∈ inhOf boolP] boolP (litP "true") "LblnotBool'Unds'" "false" := by
  decide +kernel

section lits1
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The valuation that gives the variable 1 (the sort variable) `σ` and every other variable `a`. -/
def valAt1 (σ a : M) : Valuation M := ⟨fun x => match x with | ⟨1⟩ => σ | _ => a, fun _ _ => False⟩

/-- An element of `f(a)`. -/
def App1 (I : Interpretation KoreAML.Sym M) (f : String) (a b : M) : Prop :=
  ∃ s, I.evalSymb (.symbol f) s ∧ I.evalApp s a b

theorem interp_app1 {f : String} {e : Valuation M} {x : EVar} {a : M} (hx : e.evalEvar x = a) (b : M) :
    (sym (.symbol f) ⬝ .evar x : P).interpret I e b ↔ App1 I f a b := by
  unfold App1
  simp only [interp_app, interp_sym, interp_evar]
  constructor
  · rintro ⟨s, z, hs, rfl, hb⟩
    exact ⟨s, hs, hx ▸ hb⟩
  · rintro ⟨s, hs, hb⟩
    exact ⟨s, _, hs, rfl, hx ▸ hb⟩

variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σR σB r : M}
  (hB : ∀ a, I.evalSymb (.sort "SortBool") a ↔ a = σB) (hσB : IsSort I σB)
  (hσR : IsSort I σR) (hr : Inh I σR r)
include hD hc hB hσB hσR hr

/-- **A functional sentence at an element `a` of the argument's sort**, the sort variable at a sort
with an element: among Bool's elements, `f(a)` holds exactly one. -/
theorem fnl1_one {f : String} {SA : P} {σA a : M} (hSA : ∀ (e : Valuation M) x, SA.interpret I e x ↔ x = σA)
    (ha : Inh I σA a) (h : I ⊧ᴵ fnl1P SA f) :
    ∃ y, Inh I σB y ∧ ∀ b, Inh I σB b → (App1 I f a b ↔ b = y) := by
  have h1 := h (valAt1 σR a) r
  unfold fnl1P at h1
  rw [interpret_impl] at h1
  have h2 := h1 (interp_conjList fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · unfold sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσR
    · rw [interp_member hD, interp_inhOf_of (S := SA) (σ := σA) (hSA _)]; exact ha)
  rw [interp_equal hD] at h2
  have h3 := (h2 r).mpr ((interp_inhOf_of (σ := σR) (fun a => Iff.rfl)).mpr hr)
  rw [interp_sExists] at h3
  obtain ⟨y, hy1, hy2⟩ := h3
  rw [interp_member hD, interp_inhOf_of (S := boolP) (σ := σB) (fun a => hB a)] at hy1
  simp only [Function.update_same] at hy1
  rw [interp_sEquals hD hc (S := boolP) (σ := σB) (σ' := σR) (fun a => hB a) (fun a => Iff.rfl) hσB hσR] at hy2
  refine ⟨y, hy1, fun b hb => ?_⟩
  have h4 := hy2.2 b hb
  rw [interp_app1 (a := a) rfl, interp_evar] at h4
  simp only [Function.update_same] at h4
  exact h4.symm

/-- **An equation `f(X0) = lit` at an element `a` of `p`**, of the argument's sort: among Bool's
elements, `f(a)` and the literal hold the same. -/
theorem litEqn_at {f lit : String} {ws : List P} {SA pP : P} {σA a : M}
    (hSA : ∀ (e : Valuation M) x, SA.interpret I e x ↔ x = σA) (hσA : IsSort I σA) (ha : Inh I σA a)
    (hws : ∀ w ∈ ws, w.interpret I (valAt1 σR a) r) (hp : pP.interpret I (valAt1 σR a) a)
    (h : I ⊧ᴵ litEqnP ws SA pP f lit) :
    ∀ b, Inh I σB b → (App1 I f a b ↔ (litP lit).interpret I (valAt1 σR a) b) := by
  have h1 := h (valAt1 σR a) r
  unfold litEqnP at h1
  rw [interpret_impl] at h1
  have h2 := h1 (interp_conjList hws)
  rw [interp_equal hD] at h2
  have hin : (inhOf (.evar ⟨1⟩) : P).interpret I (valAt1 σR a) r :=
    (interp_inhOf_of (σ := σR) (fun a => Iff.rfl)).mpr hr
  have htop : (sTop (.evar ⟨1⟩) : P).interpret I (valAt1 σR a) r := (interp_sTop hD rfl r).mpr hin
  have h3 := (h2 r).mpr hin
  rw [interp_sImp] at h3
  have h4 := h3.2 (interp_sAnd.mpr ⟨htop, interp_sAnd.mpr ⟨
    (interp_sIn hD hc (S := SA) (σ := σA) (σ' := σR) (hSA _) (fun a => Iff.rfl) hσA hσR
      (fun x hx => by rw [interp_evar] at hx; rw [hx]; exact ha) r).mpr ⟨⟨a, rfl, hp⟩, hr⟩, htop⟩⟩)
  rw [interp_sEquals hD hc (S := boolP) (σ := σB) (σ' := σR) (fun a => hB a) (fun a => Iff.rfl) hσB hσR] at h4
  intro b hb
  have h5 := h4.2 b hb
  rw [interp_app1 (a := a) rfl, interp_sAnd, interp_sTop hD rfl,
    interp_inhOf_of (S := boolP) (σ := σB) (fun a => hB a)] at h5
  exact ⟨fun h => (h5.mp h).1, fun h => h5.mpr ⟨h, hb⟩⟩

end lits1

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **Each Bool literal is one element of Bool, from two function equations of the text.** In an
interpretation with definedness, `⌈_⌉`'s definition, the sort constants K and Bool, an element `k`
of K and the arity of the two literals, that satisfies `rule isK(K) => true`,
`rule notBool true => false` and the functional sentences of `isK` and `notBool_`: `isK(k)` is one
element of Bool among Bool's and agrees there with `true`; `notBool` of that element likewise with
`false`. That the two elements differ is not concluded. -/
theorem boolLits_bool_core [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σK σB k : M}
    (hK : ∀ a, I.evalSymb (.sort "SortK") a ↔ a = σK) (hσK : IsSort I σK)
    (hB : ∀ a, I.evalSymb (.sort "SortBool") a ↔ a = σB) (hσB : IsSort I σB) (hk : Inh I σK k)
    (hdT : I ⊧ᴵ (dvArityItem "true").pat) (hdF : I ⊧ᴵ (dvArityItem "false").pat)
    (h1 : I ⊧ᴵ sentPat isKTrueAx) (hf1 : I ⊧ᴵ sentPat (fnl1Ax "LblisK" "K"))
    (h2 : I ⊧ᴵ sentPat notTrueFalseAx) (hf2 : I ⊧ᴵ sentPat (fnl1Ax "LblnotBool'Unds'" "Bool")) (e : Valuation M) :
    ∃ aF aT, (∀ m, (litP "false").interpret I e m ↔ m = aF) ∧ (∀ m, (litP "true").interpret I e m ↔ m = aT) ∧
      Inh I σB aF ∧ Inh I σB aT := by
  have hcl : ∀ (lit : String) (e' : Valuation M) m, (litP lit).interpret I e m ↔ (litP lit).interpret I e' m :=
    fun lit e' m => ((Closed.sym _).app (Closed.sym _)).interp _ _ m
  rw [isKTrue_shape] at h1
  rw [fnl1_shape_isK] at hf1
  rw [notTrueFalse_shape] at h2
  rw [fnl1_shape_not] at hf2
  have hKP : ∀ (e : Valuation M) x, kP.interpret I e x ↔ x = σK := fun _ x => hK x
  have hBP : ∀ (e : Valuation M) x, boolP.interpret I e x ↔ x = σB := fun _ x => hB x
  have hsg : ∀ (a m : M), (sortGuard ⟨1⟩ : P).interpret I (valAt1 σK a) m := fun a m => by
    unfold sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσK
  obtain ⟨v, hv, hv1⟩ := fnl1_one hD hc hB hσB hσK hk hKP hk hf1
  have e1 := litEqn_at hD hc hB hσB hσK hk hKP hσK hk (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hsg k k
      · rw [interp_member hD, interp_inhOf_of (S := kP) (σ := σK) (hKP _)]; exact hk
      · rw [interp_member hD, interp_inhOf_of (S := kP) (σ := σK) (hKP _)]; exact hk)
    (show (Pattern.evar ⟨3⟩ : P).interpret I (valAt1 σK k) k from rfl) h1
  have hT : ∀ m, (litP "true").interpret I e m ↔ m = v := fun m => by
    rw [hcl "true" (valAt1 σK k)]
    constructor
    · intro hm
      have hmB := lit_in_bool hD hB hσB hdT _ m hm
      exact (hv1 m hmB).mp ((e1 m hmB).mpr hm)
    · rintro rfl
      exact (e1 m hv).mp ((hv1 m hv).mpr rfl)
  obtain ⟨w, hw, hw1⟩ := fnl1_one hD hc hB hσB hσK hk hBP hv hf2
  have e2 := litEqn_at hD hc hB hσB hσK hk hBP hσB hv (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hsg v k
      · rw [interp_member hD, interp_inhOf_of (S := boolP) (σ := σB) (hBP _)]; exact hv)
    ((hcl "true" (valAt1 σK v) v).mp ((hT v).mpr rfl)) h2
  refine ⟨w, v, fun m => ?_, hT, hw, hv⟩
  rw [hcl "false" (valAt1 σK v)]
  constructor
  · intro hm
    have hmB := lit_in_bool hD hB hσB hdF _ m hm
    exact (hw1 m hmB).mp ((e2 m hmB).mpr hm)
  · rintro rfl
    exact (e2 m hw).mp ((hw1 m hw).mpr rfl)

/-- `boolLits_bool_core` with the signature items from `ΓSig c`, for a semantics whose sort `sK` is
named K, and K's G-nonempty item: each of `false` and `true` denotes one element, an element of
Bool. -/
theorem boolLits_of_bool_text_sig [Inhabited M] (hD : DefOK I) {c : Semantics} [OvlOK c] (hSig : I ⊧ᴵP ΓSig c)
    {sK : Srt} (hsK : sK < nRegSorts + c.sortNames.length) (hnK : c.sortName sK = "K") {bn : Bool}
    (hne : I ⊧ᴵ (nonemptyItem ⟨"SortK", [], bn⟩).pat)
    (h1 : I ⊧ᴵ sentPat isKTrueAx) (hf1 : I ⊧ᴵ sentPat (fnl1Ax "LblisK" "K"))
    (h2 : I ⊧ᴵ sentPat notTrueFalseAx) (hf2 : I ⊧ᴵ sentPat (fnl1Ax "LblnotBool'Unds'" "Bool")) (e : Valuation M) :
    ∃ aF aT, (∀ m, (litP "false").interpret I e m ↔ m = aF) ∧ (∀ m, (litP "true").interpret I e m ↔ m = aT) ∧
      (inhOf boolP).interpret I e aF ∧ (inhOf boolP).interpret I e aT := by
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σK, hK, hσK⟩ := TieRhs.sortSing_sig hD hSig hsK
  rw [hnK] at hK
  have hK : ∀ a, I.evalSymb (.sort "SortK") a ↔ a = σK := hK
  obtain ⟨σB, hB, hσB⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := c))
  rw [sortName_bool] at hB
  have hB : ∀ a, I.evalSymb (.sort "SortBool") a ↔ a = σB := hB
  obtain ⟨k, hk⟩ := nonempty_of hD hne (e := e)
  have hk' : Inh I σK k := (interp_inhOf_of (S := kP) (σ := σK) (fun a => hK a)).mp hk
  obtain ⟨aF, aT, hF, hT, hiF, hiT⟩ := boolLits_bool_core hD hc hK hσK hB hσB hk'
    (hSig _ (Or.inr ⟨"true", rfl⟩)) (hSig _ (Or.inr ⟨"false", rfl⟩)) h1 hf1 h2 hf2 e
  exact ⟨aF, aT, hF, hT, (interp_inhOf_of (S := boolP) (σ := σB) (fun a => hB a)).mpr hiF,
    (interp_inhOf_of (S := boolP) (σ := σB) (fun a => hB a)).mpr hiT⟩

end

end TieReqBool

end KCore
