/-
  KCore, outside the cone: a function equation one of whose argument patterns Γ's item writes
  through the cut of an application (`Parse.ovlCutList`), against the equation as the text writes
  it. For a tie file. The analogue, for an equation, of `TieRuleCut` (a rule's left side).

  The text's premise holds a membership `x ∈ K[φ]`, x the variable of an argument of the function
  and `K[φ]` that argument's pattern, φ an application under the applications K. Γ's premise holds
  `x ∈ K[V]` in its place, V a variable of the clause that the text does not write, and the
  membership `V ∈ φ` as a last conjunct:

      text   T[x ∈ K[φ]]             → f(…) = r
      Γ      T[x ∈ K[V]] ∧ V ∈ φ     → f(…) = r

  T a tree of binary conjunctions (`AndFrame`). The right side and the other conjuncts are the
  same patterns, and do not hold V.

  - `partsOf dirs path a`: the parts of Γ's axiom `a` read so, the membership at `dirs` in the
    conjunctions of the premise's first operand and V at `path` in its pattern (`Parts`).
    `Parts.gammaPat` is `a`'s pattern (`partsOf_eq`), `Parts.textPat` the text's form, and
    `textItemOf a P` the item of the text's form at `a`'s variable table. A tie file compares it
    with the sentence's translation up to the names of the variables (`TieAlpha.acEqB`).
  - `gamma_sub`: at one valuation, every element of Γ's premise is one of the text's, in every
    interpretation: `V ∈ φ` holds somewhere only where φ holds V's element, an application context
    is monotone and so is a membership in its right operand.
    `argCut_from_text`: so the text's form gives Γ's item in every model of definedness
    (`subOK`: the variables of the text's form are variables of `a`).
  - `text_split`: at a valuation where the guards of the text's variables hold, an element of the
    text's premise is one of Γ's premise at V an element b of φ at which `K[b]` holds x's element
    (`KoreAML.cut_sem`), where b is in V's sort. `item_more`: Γ's item, with V a variable more,
    then gives the text's form at that valuation, V being free in nothing else (`freshOK`).
    `argCut_entailed`: so Γ's item gives the text's form in a model of definedness that reads
    `⌈_⌉`, where the sorts of x and V denote sorts and every such b is in V's sort (`hφs`).
    `argCut_entailed_top`: `hφs` holds of itself where the cut is the whole argument pattern
    (`topOK`: K is the hole and V is of x's sort), b being x's element.
    `argCut_iff`, `argCut_iff_top`: the two directions together.

  One cut, in an equation's own premise: an equation with two cut applications, or one read under
  the negation of the clauses of a smaller priority, is not of this form.
-/
import KcoreSpec.TieRuleCut
import KcoreSpec.TieCutEq

set_option autoImplicit false

namespace KCore

namespace TieEqArgCut

open ML Faithful KoreAML
open TieCutEq (itemAt freeG freeT trAxiom_implies tr_in tr_evar tr_implies noAlias_vars)
open TieRuleCut (sidesFreshB notFree_cut sidesFresh_noRead)

/-! ## The premise's conjunctions -/

/-- A pattern under binary conjunctions, outermost first: each conjunction's sort, whether the
pattern is its first operand, and its other operand. -/
abbrev AndFrame := List (Kore.KSort × Bool × Kore.Pattern)

def AndFrame.fill : AndFrame → Kore.Pattern → Kore.Pattern
  | [], b => b
  | (R, true, s) :: F, b => .and R [AndFrame.fill F b, s]
  | (R, false, s) :: F, b => .and R [s, AndFrame.fill F b]

/-- The operand at `dirs` (each 0 or 1, from the top) of a tree of binary conjunctions, and the
conjunctions around it. -/
def splitAnd : List Nat → Kore.Pattern → Option (AndFrame × Kore.Pattern)
  | [], p => some ([], p)
  | 0 :: ds, .and R [p, s] => (splitAnd ds p).map fun x => ((R, true, s) :: x.1, x.2)
  | 1 :: ds, .and R [s, p] => (splitAnd ds p).map fun x => ((R, false, s) :: x.1, x.2)
  | _ :: _, _ => none

theorem splitAnd_eq : ∀ (ds : List Nat) (p : Kore.Pattern) {F : AndFrame} {b : Kore.Pattern},
    splitAnd ds p = some (F, b) → p = AndFrame.fill F b
  | [], p, F, b, h => by
    simp only [splitAnd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | d :: ds, p, F, b, h => by
    unfold splitAnd at h
    split at h
    · next hh => cases hh
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨F', b'⟩, hq, rfl, rfl⟩ := h
      rw [AndFrame.fill, ← splitAnd_eq _ _ hq]
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨F', b'⟩, hq, rfl, rfl⟩ := h
      rw [AndFrame.fill, ← splitAnd_eq _ _ hq]
    · cases h

/-! ## The parts of Γ's equation -/

/-- The parts of Γ's equation
`\implies{Ri}(\and{R}(F[\in{Sx, Rm}(x, K[V])], \in{S, Rm}(V, φ)), eq)`. -/
structure Parts where
  Ri : Kore.KSort
  eq : Kore.Pattern
  R : Kore.KSort
  F : AndFrame
  Sx : Kore.KSort
  Rm : Kore.KSort
  x : Kore.EVar
  K : KoreCutCtx
  S : Kore.KSort
  V : Kore.EVar
  φ : Kore.Pattern

/-- Γ's premise: the membership of the argument with the variable, and the variable's membership
in the application. -/
def Parts.gammaPrem (P : Parts) : Kore.Pattern :=
  .and P.R [P.F.fill (.in P.Sx P.Rm (.var (.evar P.x)) (P.K.fill (.var (.evar P.V)))),
    .in P.S P.Rm (.var (.evar P.V)) P.φ]

/-- **The premise as the text writes it**: the membership of the argument with the application. -/
def Parts.textPrem (P : Parts) : Kore.Pattern :=
  P.F.fill (.in P.Sx P.Rm (.var (.evar P.x)) (P.K.fill P.φ))

def Parts.gammaPat (P : Parts) : Kore.Pattern := .implies P.Ri P.gammaPrem P.eq

/-- Γ's equation with the premise as the text writes it. -/
def Parts.textPat (P : Parts) : Kore.Pattern := .implies P.Ri P.textPrem P.eq

/-- The parts of the premise `\and{R}(A, \in{S, Rm}(V, φ))` whose operand at `dirs` in A is
`\in{Sx, Rm}(x, q)` with V at `path` in q, no head of the applications around V an alias. -/
def premParts (dirs path : List Nat) (Ri : Kore.KSort) (eq : Kore.Pattern) : Kore.Pattern → Option Parts
  | .and R [A, .in S Rm (.var (.evar V)) φ] =>
    match splitAnd dirs A with
    | some (F, .in Sx Rm' (.var (.evar x)) q) =>
      match TieRuleLhs.cutAt path q with
      | some (K, _) =>
        if Rm' = Rm ∧ q = K.fill (.var (.evar V)) ∧ K.noAlias ⟨[], []⟩ = true then
          some ⟨Ri, eq, R, F, Sx, Rm, x, K, S, V, φ⟩
        else none
      | none => none
    | _ => none
  | _ => none

/-- The parts of Γ's equation `a` read through the cut of the application at `path` in the
pattern of the argument whose membership is at `dirs`. -/
def partsOf (dirs path : List Nat) (a : Kore.Axiom) : Option Parts :=
  match a.pattern with
  | .implies Ri prem eq => premParts dirs path Ri eq prem
  | _ => none

theorem premParts_eq {dirs path : List Nat} {Ri : Kore.KSort} {eq p : Kore.Pattern} {P : Parts}
    (h : premParts dirs path Ri eq p = some P) :
    p = P.gammaPrem ∧ P.Ri = Ri ∧ P.eq = eq ∧ P.K.noAlias ⟨[], []⟩ = true := by
  unfold premParts at h
  split at h
  · split at h
    · next F Sx Rm' x q hs =>
      split at h
      · split at h
        · next hc =>
          obtain ⟨rfl, rfl, hK⟩ := hc
          cases h
          refine ⟨?_, rfl, rfl, hK⟩
          rw [splitAnd_eq _ _ hs]; rfl
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Γ's axiom is its parts' pattern**, and no head of the applications around the variable is an
alias. -/
theorem partsOf_eq {dirs path : List Nat} {a : Kore.Axiom} {P : Parts} (h : partsOf dirs path a = some P) :
    a.pattern = P.gammaPat ∧ P.K.noAlias ⟨[], []⟩ = true := by
  unfold partsOf at h
  split at h
  · next Ri prem eq hp =>
    obtain ⟨rfl, rfl, rfl, hK⟩ := premParts_eq h
    exact ⟨hp, hK⟩
  · cases h

/-- **The item of the text's form of Γ's equation `a`**, at `a`'s variable table, with the guards
of the form's own free variables in the order of their occurrence in it. -/
def textItemOf (a : Kore.Axiom) (P : Parts) : KoreAML.P :=
  itemAt (tableOf a.sortVars a.pattern) (freeT a P.textPat) P.Ri P.textPat

/-- The free variables of the text's form are free variables of `a`. -/
def subOK (a : Kore.Axiom) (P : Parts) : Bool :=
  (freeT a P.textPat).all (freeG a).contains

/-- What the converse reads of the parts, decided at `a`'s table. The free variables of `a` are
those of the text's form and V. The sort of the memberships is a sort variable of the text's form,
x a variable of it of the sort `Sx`, and V is of the sort `S`. V's index is not that of the sort
variable nor x's, and V is free in nothing but its occurrence and its membership: the patterns
beside the path to it, φ, the other conjuncts, the equation, the equation's sort and the guards of
the text's variables. -/
def freshOK (a : Kore.Axiom) (P : Parts) : Bool :=
  let t := tableOf a.sortVars a.pattern
  let v := t.ev (evarKey P.V)
  let fT := freeT a P.textPat
  (freeG a).all (fun k => fT.contains k || k == evarKey P.V) &&
  (match P.Rm with
    | .var α => fT.contains (sortVarKey α) && decide (t.ev (sortVarKey α) ≠ v)
    | _ => false) &&
  fT.contains (evarKey P.x) && decide (t.ev (evarKey P.x) ≠ v) &&
  decide (P.x.sort = P.Sx) && decide (P.V.sort = P.S) &&
  sidesFreshB ⟨t, []⟩ v P.K && !(tr ⟨t, []⟩ P.φ).isFreeEvar v &&
  P.F.all (fun s => !(tr ⟨t, []⟩ s.2.2).isFreeEvar v) &&
  !(tr ⟨t, []⟩ P.eq).isFreeEvar v && !(inhOf (trSort t P.Ri)).isFreeEvar v &&
  fT.all (fun k => !(guardOf t k).isFreeEvar v)

/-- The cut is the whole argument pattern, and the variable is of the argument's sort. -/
def topOK (P : Parts) : Bool :=
  (match P.K with
    | .hole => true
    | _ => false) && decide (P.S = P.Sx)

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- An element of a pattern under conjunctions is an element of the pattern and of each other
operand. -/
theorem fill_elem {t : VarTable} {e : Valuation M} {b : Kore.Pattern} (a : M) :
    ∀ (F : AndFrame), (tr ⟨t, []⟩ (AndFrame.fill F b)).interpret I e a ↔
      (tr ⟨t, []⟩ b).interpret I e a ∧ ∀ s ∈ F, (tr ⟨t, []⟩ s.2.2).interpret I e a
  | [] => by simp [AndFrame.fill]
  | (R, true, s) :: F => by
    rw [AndFrame.fill, tr_and2, interp_sAnd, fill_elem a F]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  | (R, false, s) :: F => by
    rw [AndFrame.fill, tr_and2, interp_sAnd, fill_elem a F]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

/-- A membership is monotone in its right operand, in every interpretation. -/
theorem sIn_mono {e : Valuation M} {S S' χ ψ ψ' : KoreAML.P}
    (h : ∀ b, ψ.interpret I e b → ψ'.interpret I e b) (m : M)
    (hm : (sIn S S' χ ψ).interpret I e m) : (sIn S S' χ ψ').interpret I e m := by
  unfold sIn sCeil at hm ⊢
  obtain ⟨f, b, hf, hb, happ⟩ := interp_app.mp hm
  obtain ⟨h1, h2⟩ := interp_sAnd.mp hb
  exact interp_app.mpr ⟨f, b, hf, interp_sAnd.mpr ⟨h1, h b h2⟩, happ⟩

/-- **Γ's premise is inside the text's**, at one valuation, in every interpretation. -/
theorem gamma_sub {t : VarTable} {P : Parts} (hK : P.K.noAlias ⟨t, []⟩ = true) (e : Valuation M) :
    TieCutEq.Sub I t e P.gammaPrem P.textPrem := by
  intro a ha
  unfold Parts.gammaPrem at ha
  rw [tr_and2, interp_sAnd, fill_elem, tr_in, tr_in, tr_evar] at ha
  obtain ⟨⟨hx, hsib⟩, hin⟩ := ha
  have hφ := TieCutEq.sIn_evar_elem hin
  have hsub : ∀ a', (tr ⟨t, []⟩ (.var (.evar P.V))).interpret I e a' → (tr ⟨t, []⟩ P.φ).interpret I e a' := by
    intro a' ha'
    rw [tr_evar, interp_evar] at ha'
    rw [ha']; exact hφ
  unfold Parts.textPrem
  rw [fill_elem, tr_in]
  exact ⟨sIn_mono (fun b => TieRuleLhs.tr_fill_mono _ P.K hK hsub b) a hx, hsib⟩

/-- **Sentence to item**: a model of definedness of the text's form of the equation is a model of
Γ's item. -/
theorem argCut_from_text (hD : DefOK I) {dirs path : List Nat} {a : Kore.Axiom} {P : Parts}
    (hP : partsOf dirs path a = some P) (hok : subOK a P = true) (h : I ⊧ᴵ textItemOf a P) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  obtain ⟨hp, hK⟩ := partsOf_eq hP
  have hsub : ∀ k ∈ freeT a P.textPat, k ∈ freeG a := by
    simpa only [subOK, List.all_eq_true, List.contains_iff_mem] using hok
  intro e m
  rw [trAxiom_implies a hp]
  unfold textItemOf at h
  generalize tableOf a.sortVars a.pattern = T at h ⊢
  rw [hp]
  exact TieCutEq.item_of_sub hD hsub h e m fun _ => gamma_sub ((noAlias_vars T [] [] P.K).trans hK) e

/-- **Γ's item with a variable more gives the text's form.** The item of `\implies{R}(prem', eq)`
with the guards of `fG` holds in `I`; v is free neither in the sort nor in `eq`; at the valuation
`e`, where the guards of `fT` hold, every element of `prem` is one of `prem'` at some value of v
at which the guards of `fG` hold. Then the item of `\implies{R}(prem, eq)` with the guards of `fT`
holds at `e`. -/
theorem item_more (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {R : Kore.KSort}
    {prem prem' eq : Kore.Pattern} {v : EVar} (h : I ⊧ᴵ itemAt t fG R (.implies R prem' eq))
    (hR : (inhOf (trSort t R)).isFreeEvar v = false) (heq : (tr ⟨t, []⟩ eq).isFreeEvar v = false)
    (e : Valuation M) (m : M)
    (hL : (∀ k ∈ fT, (guardOf t k).interpret I e m) → ∀ a, (tr ⟨t, []⟩ prem).interpret I e a →
      ∃ b, (∀ k ∈ fG, (guardOf t k).interpret I ⟨Function.update e.evalEvar v b, e.evalSvar⟩ m) ∧
        (tr ⟨t, []⟩ prem').interpret I ⟨Function.update e.evalEvar v b, e.evalSvar⟩ a) :
    (itemAt t fT R (.implies R prem eq)).interpret I e m := by
  unfold itemAt
  rw [interpret_impl]
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ fT, (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  rw [interp_equal hD]
  intro a
  rw [tr_implies, interp_sImp]
  refine ⟨fun hf => hf.1, fun hs => ⟨hs, fun hl => ?_⟩⟩
  obtain ⟨b, hgb, hlb⟩ := hL hg' a hl
  have h1 := h ⟨Function.update e.evalEvar v b, e.evalSvar⟩ m
  unfold itemAt at h1
  rw [interpret_impl] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun ψ hψ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hψ
    exact hgb k hk)
  rw [interp_equal hD] at h2
  have h3 := h2 a
  rw [tr_implies, interp_sImp] at h3
  exact (notFree_cut heq e b a).mp ((h3.mpr ((notFree_cut hR e b a).mpr hs)).2 hlb)

/-- **An element of the text's premise is one of Γ's, at an element of φ.** At the valuation `e`:
the sort of the memberships and the sorts of x and V denote sorts, x's element is in its sort, V's
index is neither the sort variable's nor x's, and V is free in nothing but its occurrence and its
membership; every element b of φ at which `K[b]` holds x's element is in V's sort (`hφs`). Then an
element of the text's premise is, at some such b as V's value, an element of Γ's premise. -/
theorem text_split [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {t : VarTable} {P : Parts}
    (hK : P.K.noAlias ⟨t, []⟩ = true) {α : Kore.SortVar} (hRm : P.Rm = .var α)
    (hαv : t.ev (sortVarKey α) ≠ t.ev (evarKey P.V)) (hxv : t.ev (evarKey P.x) ≠ t.ev (evarKey P.V))
    (hKv : sidesFreshB ⟨t, []⟩ (t.ev (evarKey P.V)) P.K = true)
    (hφv : (tr ⟨t, []⟩ P.φ).isFreeEvar (t.ev (evarKey P.V)) = false)
    (hFv : ∀ s ∈ P.F, (tr ⟨t, []⟩ s.2.2).isFreeEvar (t.ev (evarKey P.V)) = false)
    {σ σx : M} (hS : ∀ (e : Valuation M) a, (trSort t P.S).interpret I e a ↔ a = σ)
    (hSx : ∀ (e : Valuation M) a, (trSort t P.Sx).interpret I e a ↔ a = σx)
    (hσ : IsSort I σ) (hσx : IsSort I σx) (e : Valuation M)
    (hρ : IsSort I (e.evalEvar (t.ev (sortVarKey α))))
    (hx : Inh I σx (e.evalEvar (t.ev (evarKey P.x))))
    (hφs : ∀ b, (tr ⟨t, []⟩ P.φ).interpret I e b →
      (tr ⟨t, []⟩ (P.K.fill (.var (.evar P.V)))).interpret I
        ⟨Function.update e.evalEvar (t.ev (evarKey P.V)) b, e.evalSvar⟩ (e.evalEvar (t.ev (evarKey P.x))) →
      Inh I σ b)
    (a : M) (h : (tr ⟨t, []⟩ P.textPrem).interpret I e a) :
    ∃ b, Inh I σ b ∧
      (tr ⟨t, []⟩ P.gammaPrem).interpret I ⟨Function.update e.evalEvar (t.ev (evarKey P.V)) b, e.evalSvar⟩ a := by
  have hR : ∀ (e' : Valuation M) a', (trSort t P.Rm).interpret I e' a' ↔ a' = e'.evalEvar (t.ev (sortVarKey α)) :=
    fun e' a' => by rw [hRm, trSort]; exact interp_evar
  unfold Parts.textPrem at h
  rw [fill_elem, tr_in, tr_evar] at h
  obtain ⟨hin, hsib⟩ := h
  obtain ⟨hKφ, haρ⟩ := (mem_iff_cut hD hc (hSx e) (hR e) hσx hρ _ hx _ a).mp hin
  rw [tr_cutCtx _ _ P.K hK] at hKφ
  obtain ⟨b, hb, hKb⟩ := (cut_sem (t.ev (evarKey P.V)) (tr ⟨t, []⟩ P.φ) (P.K.toCut ⟨t, []⟩)
    (KoreCutCtx.toCut_fresh P.K (sidesFresh_noRead P.K hKv)) e _).mp hKφ
  have hKb' : (tr ⟨t, []⟩ (P.K.fill (.var (.evar P.V)))).interpret I
      ⟨Function.update e.evalEvar (t.ev (evarKey P.V)) b, e.evalSvar⟩ (e.evalEvar (t.ev (evarKey P.x))) := by
    rw [tr_cutCtx _ _ P.K hK, tr_evar]; exact hKb
  have hbσ := hφs b hb hKb'
  refine ⟨b, hbσ, ?_⟩
  generalize he' : (⟨Function.update e.evalEvar (t.ev (evarKey P.V)) b, e.evalSvar⟩ : Valuation M) = e' at hKb' ⊢
  have hV : e'.evalEvar (t.ev (evarKey P.V)) = b := by rw [← he']; simp
  have hα' : e'.evalEvar (t.ev (sortVarKey α)) = e.evalEvar (t.ev (sortVarKey α)) := by
    rw [← he']; exact Function.update_noteq hαv _ _
  have hx' : e'.evalEvar (t.ev (evarKey P.x)) = e.evalEvar (t.ev (evarKey P.x)) := by
    rw [← he']; exact Function.update_noteq hxv _ _
  have hρ' : IsSort I (e'.evalEvar (t.ev (sortVarKey α))) := hα' ▸ hρ
  have haρ' : Inh I (e'.evalEvar (t.ev (sortVarKey α))) a := hα' ▸ haρ
  unfold Parts.gammaPrem
  rw [tr_and2, interp_sAnd, fill_elem, tr_in, tr_in, tr_evar, tr_evar]
  refine ⟨⟨?_, fun s hs => ?_⟩, ?_⟩
  · exact (mem_iff_cut hD hc (hSx e') (hR e') hσx hρ' _ (hx' ▸ hx) _ a).mpr ⟨hx' ▸ hKb', haρ'⟩
  · rw [← he']; exact (notFree_cut (hFv s hs) e b a).mpr (hsib s hs)
  · refine (mem_iff_cut hD hc (hS e') (hR e') hσ hρ' _ (hV ▸ hbσ) _ a).mpr ⟨?_, haρ'⟩
    rw [hV, ← he']; exact (notFree_cut hφv e b b).mpr hb

/-- **Item to sentence**: a model of definedness that reads `⌈_⌉` of Γ's item is a model of the
text's form of the equation, where the sorts of x and V denote sorts and, at every valuation where
the guards of the text's variables hold, every element b of φ at which `K[b]` holds x's element is
in V's sort (`hφs`). -/
theorem argCut_entailed [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {dirs path : List Nat}
    {a : Kore.Axiom} {P : Parts} (hP : partsOf dirs path a = some P) (hok : freshOK a P = true)
    {σ σx : M}
    (hS : ∀ (e : Valuation M) m, (trSort (tableOf a.sortVars a.pattern) P.S).interpret I e m ↔ m = σ)
    (hSx : ∀ (e : Valuation M) m, (trSort (tableOf a.sortVars a.pattern) P.Sx).interpret I e m ↔ m = σx)
    (hσ : IsSort I σ) (hσx : IsSort I σx)
    (hφs : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ freeT a P.textPat, (guardOf (tableOf a.sortVars a.pattern) k).interpret I e m) →
      ∀ b, (tr ⟨tableOf a.sortVars a.pattern, []⟩ P.φ).interpret I e b →
        (tr ⟨tableOf a.sortVars a.pattern, []⟩ (P.K.fill (.var (.evar P.V)))).interpret I
          ⟨Function.update e.evalEvar ((tableOf a.sortVars a.pattern).ev (evarKey P.V)) b, e.evalSvar⟩
          (e.evalEvar ((tableOf a.sortVars a.pattern).ev (evarKey P.x))) →
        Inh I σ b)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) : I ⊧ᴵ textItemOf a P := by
  obtain ⟨hp, hK⟩ := partsOf_eq hP
  rw [trAxiom_implies a hp] at h
  unfold textItemOf
  unfold freshOK at hok
  generalize tableOf a.sortVars a.pattern = T at h hok hS hSx hφs ⊢
  have hK' : P.K.noAlias ⟨T, []⟩ = true := (noAlias_vars T [] [] P.K).trans hK
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem, Bool.or_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfG, hRm⟩, hxT⟩, hxv⟩, hxs⟩, hVs⟩, hKv⟩, hφv⟩, hFv⟩, heqv⟩, hRiv⟩, hgv⟩ := hok
  obtain ⟨α, hRmα, hαT, hαv⟩ : ∃ α, P.Rm = .var α ∧ sortVarKey α ∈ freeT a P.textPat ∧
      T.ev (sortVarKey α) ≠ T.ev (evarKey P.V) := by
    cases hRm' : P.Rm with
    | var α =>
      rw [hRm'] at hRm
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hRm
      exact ⟨α, rfl, hRm.1, hRm.2⟩
    | ctor _ _ => rw [hRm'] at hRm; cases hRm
  intro e m
  rw [hp] at h
  refine item_more (R := P.Ri) (prem := P.textPrem) (prem' := P.gammaPrem) (eq := P.eq) hD h hRiv heqv e m
    fun hg a' ha' => ?_
  have hρ : IsSort I (e.evalEvar (T.ev (sortVarKey α))) := by
    have h3 := hg _ hαT
    unfold sortVarKey guardOf sortGuard at h3
    rw [interp_member hD, interp_sortsDomain] at h3
    exact h3
  have hx : Inh I σx (e.evalEvar (T.ev (evarKey P.x))) := by
    have h3 := (TieRuleLhs.guard_evarKey hD).mp (hg _ hxT)
    rw [hxs] at h3
    exact (interp_inhOf_of (hSx e)).mp h3
  obtain ⟨b, hbσ, hlb⟩ := text_split hD hc hK' hRmα hαv hxv hKv hφv hFv hS hSx hσ hσx e hρ hx
    (hφs e m hg) a' ha'
  refine ⟨b, fun k hk => ?_, hlb⟩
  rcases hfG k hk with hk' | hk'
  · exact (notFree_cut (hgv k hk') e b m).mpr (hg k hk')
  · rw [hk', TieRuleLhs.guard_evarKey hD, hVs, interp_inhOf_of (hS _)]
    show Inh I σ (Function.update e.evalEvar _ b _)
    rw [Function.update_same]; exact hbσ

/-- **Item to sentence, the cut being the whole argument pattern**: `argCut_entailed` without its
last premise. The element of φ taken as V's value is x's, which x's guard puts in the sort. -/
theorem argCut_entailed_top [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {dirs path : List Nat}
    {a : Kore.Axiom} {P : Parts} (hP : partsOf dirs path a = some P) (hok : freshOK a P = true)
    (htop : topOK P = true) {σ : M}
    (hS : ∀ (e : Valuation M) m, (trSort (tableOf a.sortVars a.pattern) P.S).interpret I e m ↔ m = σ)
    (hσ : IsSort I σ) (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) : I ⊧ᴵ textItemOf a P := by
  unfold topOK at htop
  rw [Bool.and_eq_true, decide_eq_true_eq] at htop
  obtain ⟨hKh, hSS⟩ := htop
  have hSx : ∀ (e : Valuation M) m, (trSort (tableOf a.sortVars a.pattern) P.Sx).interpret I e m ↔ m = σ := by
    rw [← hSS]; exact hS
  have hxT : evarKey P.x ∈ freeT a P.textPat ∧ P.x.sort = P.Sx := by
    have hok' := hok
    unfold freshOK at hok'
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok'
    exact ⟨hok'.1.1.1.1.1.1.1.1.1.2, hok'.1.1.1.1.1.1.1.2⟩
  refine argCut_entailed hD hc hP hok hS hSx hσ hσ (fun e m hg b _ hKb => ?_) h
  have hK : P.K = .hole := by
    cases hk : P.K with
    | hole => rfl
    | app _ _ _ _ _ => rw [hk] at hKh; cases hKh
  rw [hK, KoreCutCtx.fill, tr_evar, interp_evar] at hKb
  have h3 := (TieRuleLhs.guard_evarKey hD).mp (hg _ hxT.1)
  rw [hxT.2] at h3
  have h4 := (interp_inhOf_of (hSx e)).mp h3
  rw [hKb] at h4
  simpa using h4

/-- **The text's form of the equation and Γ's item hold in the same models** of definedness that
read `⌈_⌉`, under the premises of `argCut_entailed`. -/
theorem argCut_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {dirs path : List Nat}
    {a : Kore.Axiom} {P : Parts} (hP : partsOf dirs path a = some P) (hsub : subOK a P = true)
    (hok : freshOK a P = true) {σ σx : M}
    (hS : ∀ (e : Valuation M) m, (trSort (tableOf a.sortVars a.pattern) P.S).interpret I e m ↔ m = σ)
    (hSx : ∀ (e : Valuation M) m, (trSort (tableOf a.sortVars a.pattern) P.Sx).interpret I e m ↔ m = σx)
    (hσ : IsSort I σ) (hσx : IsSort I σx)
    (hφs : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ freeT a P.textPat, (guardOf (tableOf a.sortVars a.pattern) k).interpret I e m) →
      ∀ b, (tr ⟨tableOf a.sortVars a.pattern, []⟩ P.φ).interpret I e b →
        (tr ⟨tableOf a.sortVars a.pattern, []⟩ (P.K.fill (.var (.evar P.V)))).interpret I
          ⟨Function.update e.evalEvar ((tableOf a.sortVars a.pattern).ev (evarKey P.V)) b, e.evalSvar⟩
          (e.evalEvar ((tableOf a.sortVars a.pattern).ev (evarKey P.x))) →
        Inh I σ b) :
    (I ⊧ᴵ textItemOf a P) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) :=
  ⟨argCut_from_text hD hP hsub, argCut_entailed hD hc hP hok hS hSx hσ hσx hφs⟩

/-- **The same, the cut being the whole argument pattern.** -/
theorem argCut_iff_top [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {dirs path : List Nat}
    {a : Kore.Axiom} {P : Parts} (hP : partsOf dirs path a = some P) (hsub : subOK a P = true)
    (hok : freshOK a P = true) (htop : topOK P = true) {σ : M}
    (hS : ∀ (e : Valuation M) m, (trSort (tableOf a.sortVars a.pattern) P.S).interpret I e m ↔ m = σ)
    (hσ : IsSort I σ) :
    (I ⊧ᴵ textItemOf a P) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) :=
  ⟨argCut_from_text hD hP hsub, argCut_entailed_top hD hc hP hok htop hS hσ⟩

end

end TieEqArgCut

end KCore
