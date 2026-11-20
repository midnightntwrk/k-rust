/-
  The lemmas of KcoreSpec/TieEX.lean and KcoreSpec/TieEXReadB.lean that give Γ's items of an
  equation `prem → F = (∃B:Bool. body) ∧ ens` from the sentence, in a model of the signature with
  one fact of the values named.

  `ex_clause_of_text`, `ex_last_of_text` and `exFacts_of_exB` take `HoldsShape.NodeFacts` whole and
  `Faithful.TermsInSort`. Of the model their proofs read the three facts of `TieFRSig.SigFacts`
  (definedness, the item of `⌈_⌉`, each numbered sort one sort) and one more: that each literal of
  Bool, `true` and `false`, denotes one element, an element of Bool (`TieEX.bool_lit`, from
  `NodeFacts.val`). `ΓSig` does not give it: the arity item of a literal puts its elements in
  Bool and says neither that there is one nor that there is at most one. The readings are not
  expected without it (argued, no interpretation is given in Lean): `ExFacts.hbody` compares the
  body at B sent to an element of the literal with the alternative of the instance, in which the
  literal stands for B; where the literal denotes two elements the two differ. So the fact stays
  a premise, named (`LitFacts.lit`); `NodeFacts` gives
  it (`litFacts_of_node`). That two values are apart is not read here.

  `TermsInSort` is replaced by `TieFRSig.TermsInSortNI`, with the decisions that the body's terms
  and the last alternative's term hold no injection.
-/
import KcoreSpec.TieFRSig
import KcoreSpec.TieEXReadB

set_option autoImplicit false

namespace KCore

namespace TieEXSig

open ML KoreAML Faithful KoreAML.TieFR
open KCore.TieFRRead KCore.TermRT KCore.TieEX KCore.TieFRTightB KCore.TieEXReadB KCore.TieFRSig

/-- The facts of a model the lemmas take: those of the signature, and that each literal of Bool is
one element of Bool. -/
structure LitFacts (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop where
  sig : SigFacts c I
  lit : ∀ (b : Bool) (e : Valuation M),
    ∃ y, (∀ m, (den c (bool b)).interpret I e m ↔ m = y) ∧ (inhOf boolP).interpret I e y

/-- `NodeFacts` holds them. -/
theorem litFacts_of_node {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
    (F : HoldsShape.NodeFacts c I) : LitFacts c I := ⟨sigFacts_of_node F, fun b e => bool_lit F b e⟩

/-- Each literal of Bool is one element of Bool. -/
theorem bool_lit_lit {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M} (F : LitFacts c I)
    (b : Bool) (e : Valuation M) :
    ∃ y, (∀ m, (den c (bool b)).interpret I e m ↔ m = y) ∧ (inhOf boolP).interpret I e y := F.lit b e

/-! ## The lemmas of KcoreSpec/TieEX.lean that give the items from the sentence, with `LitFacts` -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

variable {c : Semantics} (F : LitFacts c I)
include F

/-- Bool's elements at any valuation are those at another: `inhOf boolP` is closed. -/
theorem inBool_iff_lit (e e' : Valuation M) (y : M) :
    (inhOf boolP).interpret I e y ↔ (inhOf boolP).interpret I e' y := by
  obtain ⟨β, -, hβd⟩ := boolDen_of_sig F.sig
  rw [interp_inhOf_of (hβd e), interp_inhOf_of (hβd e')]

/-- **`∃B:Bool. φ` at a literal**: where φ holds at m with B sent to the element of a literal, the
existential holds at m. -/
theorem exists_of_lit_lit {x : EVar} {φ : KoreAML.P} {e : Valuation M} {m : M} {b : Bool} {y : M}
    (hb : (den c (bool b)).interpret I e y) (hφ : φ.interpret I (updX e x y) m) :
    (sExists x boolP φ).interpret I e m := by
  rw [interp_sExists]
  refine ⟨y, ?_, hφ⟩
  rw [interp_member F.sig.defOK]
  obtain ⟨y', hy', hin⟩ := bool_lit_lit F b e
  show (inhOf boolP).interpret I (updX e x y) (Function.update e.evalEvar x y x)
  rw [Function.update_same, (hy' y).mp hb]
  exact (inBool_iff_lit F e _ y').mp hin

end

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics}
  (F : LitFacts c I) {tbl : VarTable} {vs : List KoreAML.Var}
include F

omit [Inhabited M] in
/-- A disjunction of conditions, at an element of the sort variable's sort, holds where one does. -/
theorem condKore_disjC_lit {e : Valuation M} {m : M} (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m) :
    ∀ ps : List Cond, (tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.disjC ps))).interpret I e m ↔
      ∃ p ∈ ps, (tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m
  | [] => by
    rw [Parse.disjC, Cond.kore, tr_bottom_iff F.sig.defOK]
    simp
  | [p] => by
    rw [Parse.disjC]
    simp
  | p :: q :: qs => by
    show (tr ⟨tbl, []⟩ (Cond.kore c vs R (.or p (Parse.disjC (q :: qs))))).interpret I e m ↔ _
    rw [Cond.kore, tr_or]
    simp only [trOrList]
    rw [interp_sOr, TieFRRead.trSort_R, interp_inhOf_of (fun _ => interp_evar), condKore_disjC_lit hm (q :: qs)]
    constructor
    · rintro ⟨-, h | ⟨p', hp', h⟩⟩
      · exact ⟨p, List.mem_cons_self .., h⟩
      · exact ⟨p', List.mem_cons_of_mem _ hp', h⟩
    · rintro ⟨p', hp', h⟩
      refine ⟨hm, ?_⟩
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact Or.inl h
      · exact Or.inr ⟨p', hp', h⟩

/-- An alternative's predicate, at an element of the sort variable's sort: its term is defined and
each of its conditions holds. -/
theorem preOfC_iff_lit {e : Valuation M} {m : M} {s : Srt} {σ : M} {x : Term × List Cond}
    {CG : Cond → Valuation M → Prop}
    (hσ : ∀ a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv)))) (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m)
    (hφ : ∀ b, (altPC c tbl vs x).interpret I e b → Inh I σ b)
    (hcond : ∀ p ∈ x.2, ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e)) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (preOfC s x))).interpret I e m ↔
      (∃ b, (altPC c tbl vs x).interpret I e b) ∧ altGC CG x e := by
  unfold preOfC
  rw [condKore_conjC_sig F.sig hm]
  simp only [List.mem_cons, forall_eq_or_imp]
  rw [condKore_ceil_sig F.sig hσ hσS hr hm hφ]
  refine and_congr Iff.rfl ⟨fun h p hp => (hcond p hp).mp (h p hp), fun h p hp => (hcond p hp).mpr (h p hp)⟩

/-- **The premise of an alternative's clause**: the sentence's premise holds, the alternative is
defined and its predicates hold. -/
theorem clauseQC_iff_lit {s : Srt} {ws : List KoreAML.P} {σ : M} {prem : KoreAML.P} {CG : Cond → Valuation M → Prop}
    {x : Term × List Cond} (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    {e : Valuation M} {m : M} (hat : At I ws (tbl.ev (sortVarKey Rv)) e m)
    (hφ : ∀ a, (altPC c tbl vs x).interpret I e a → Inh I σ a)
    (hcond : ∀ p ∈ x.2, ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e)) :
    (clauseQC c tbl vs s prem x).interpret I e m ↔
      prem.interpret I e m ∧ (∃ b, (altPC c tbl vs x).interpret I e b) ∧ altGC CG x e := by
  unfold clauseQC
  rw [interp_sAnd, preOfC_iff_lit F (hσ e) hσS (isSort_of_at F.sig.defOK hr hat) hat.2 hφ hcond]

/-- **The premise of the last clause**: the sentence's premise holds, and at no element y of Bool
is an alternative of the body, read with the binder sent to y, defined where its predicates hold.
The binder's variable is not the sort variable (`hxr`); the alternatives of the body lie in σ and
their conditions read as `CGB` at each element of Bool (`hinB`, `hcondB`). -/
theorem lastBQC_iff_lit {s : Srt} {ws : List KoreAML.P} {σ : M} {prem : KoreAML.P} {CGB : Cond → Valuation M → Prop}
    {bs : List (Term × List Cond)} (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hxr : tbl.ev (evarKey (binderB c vs).kore) ≠ tbl.ev (sortVarKey Rv))
    {e : Valuation M} {m : M} (hat : At I ws (tbl.ev (sortVarKey Rv)) e m)
    (hinB : ∀ y, (inhOf boolP).interpret I e y → ∀ x ∈ bs, ∀ a,
      (altPC c tbl (vs ++ [binderB c vs]) x).interpret I (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) a →
        Inh I σ a)
    (hcondB : ∀ y, (inhOf boolP).interpret I e y → ∀ x ∈ bs, ∀ p ∈ x.2,
      ((tr ⟨tbl, []⟩ (Cond.kore c (vs ++ [binderB c vs]) R p)).interpret I
          (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) m ↔
        CGB p (updX e (tbl.ev (evarKey (binderB c vs).kore)) y))) :
    (lastBQC c tbl vs s prem bs).interpret I e m ↔
      prem.interpret I e m ∧ ∀ y, (inhOf boolP).interpret I e y → ∀ x ∈ bs,
        ¬ ((∃ b, (altPC c tbl (vs ++ [binderB c vs]) x).interpret I
              (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) b) ∧
           altGC CGB x (updX e (tbl.ev (evarKey (binderB c vs).kore)) y)) := by
  unfold lastBQC preBC
  rw [interp_sAnd, condKore_not, tr_condEx, interp_sExists]
  refine and_congr Iff.rfl ?_
  have hrS := isSort_of_at F.sig.defOK hr hat
  -- at the valuation with the binder sent to y, the sort variable holds what it holds at e
  have hrU : ∀ y, (updX e (tbl.ev (evarKey (binderB c vs).kore)) y).evalEvar (tbl.ev (sortVarKey Rv)) =
      e.evalEvar (tbl.ev (sortVarKey Rv)) := fun y => Function.update_noteq (Ne.symm hxr) _ _
  have hdisj : ∀ y, (inhOf boolP).interpret I e y →
      ((tr ⟨tbl, []⟩ (Cond.kore c (vs ++ [binderB c vs]) R (Parse.disjC (bs.map (preOfC s))))).interpret I
          (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) m ↔
        ∃ x ∈ bs, (∃ b, (altPC c tbl (vs ++ [binderB c vs]) x).interpret I
            (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) b) ∧
          altGC CGB x (updX e (tbl.ev (evarKey (binderB c vs).kore)) y)) := by
    intro y hy
    rw [condKore_disjC_lit F (by rw [hrU]; exact hat.2)]
    have hx : ∀ x ∈ bs, ((tr ⟨tbl, []⟩ (Cond.kore c (vs ++ [binderB c vs]) R (preOfC s x))).interpret I
        (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) m ↔
          (∃ b, (altPC c tbl (vs ++ [binderB c vs]) x).interpret I
            (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) b) ∧
          altGC CGB x (updX e (tbl.ev (evarKey (binderB c vs).kore)) y)) := fun x hx =>
      preOfC_iff_lit F (hσ _) hσS (by rw [hrU]; exact hrS) (by rw [hrU]; exact hat.2)
        (hinB y hy x hx) (hcondB y hy x hx)
    constructor
    · rintro ⟨p, hp, h⟩
      obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hp
      exact ⟨x, hxm, (hx x hxm).mp h⟩
    · rintro ⟨x, hxm, h⟩
      exact ⟨_, List.mem_map.mpr ⟨x, hxm, rfl⟩, (hx x hxm).mpr h⟩
  have hmem : ∀ y, (tbl.ev (evarKey (binderB c vs).kore) ∈∈ inhOf boolP : KoreAML.P).interpret I
      (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) m ↔ (inhOf boolP).interpret I e y := by
    intro y
    rw [interp_member F.sig.defOK]
    show (inhOf boolP).interpret I _ (Function.update e.evalEvar _ y _) ↔ _
    rw [Function.update_same]
    exact inBool_iff_lit F _ e y
  constructor
  · rintro ⟨hno, -⟩ y hy x hx hxd
    exact hno ⟨y, (hmem y).mpr hy, (hdisj y hy).mpr ⟨x, hx, hxd⟩⟩
  · intro h
    refine ⟨?_, hat.2⟩
    rintro ⟨y, hy, hd⟩
    have hy' := (hmem y).mp hy
    obtain ⟨x, hx, hxd⟩ := (hdisj y hy').mp hd
    exact h y hy' x hx hxd

omit [Inhabited M] in
/-- **An alternative of an instance lies inside the right side** `(∃B:Bool. body) ∧ ens`, with no
`boolClosed`: the element of a literal is in Bool. -/
theorem rhs_of_alt_lit {ws : List KoreAML.P} {r xB : EVar} {σ : M} {body ensT : KoreAML.P}
    {α : Type} {xsOf : Bool → List α} {A : α → KoreAML.P} {G : α → Valuation M → Prop}
    (hbody : ∀ e m, At I ws r e m → ∀ (b : Bool) (y : M), (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔ ∃ x ∈ xsOf b, (A x).interpret I e a ∧ G x e))
    {e : Valuation M} {m : M} (hat : At I ws r e m) {x : α} (hx : x ∈ xsOf true ++ xsOf false)
    {a : M} (ha : Inh I σ a) (hxa : (A x).interpret I e a) (hgx : G x e) :
    (sAnd (sExists xB boolP body) ensT).interpret I e a := by
  have hgo : ∀ b, x ∈ xsOf b → (sAnd (sExists xB boolP body) ensT).interpret I e a := by
    intro b hxb
    obtain ⟨y, hy, -⟩ := bool_lit_lit F b e
    have := (hbody e m hat b y ((hy y).mpr rfl) a ha).mpr ⟨x, hxb, hxa, hgx⟩
    rw [interp_sAnd]
    exact ⟨exists_of_lit_lit F ((hy y).mpr rfl) this.1, this.2⟩
  rcases List.mem_append.mp hx with h | h
  · exact hgo true h
  · exact hgo false h

/-! ## The tie -/

/-- **The sentence and f's functional sentence give the equation of each alternative**
`prem ∧ preOfC s x → F = aₓ ∧ ⊤_S`, with no `boolClosed`. -/
theorem ex_clause_of_text_lit {s : Srt} {xsOf : Bool → List (Term × List Cond)}
    {ws : List KoreAML.P} {σ : M} {prem body ensT S Fp : KoreAML.P} {xB : EVar} {CG : Cond → Valuation M → Prop}
    (hS : SortAt I S σ) (hG : GuardsPred I ws)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ)
    (hin : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ a,
      (altPC c tbl vs x).interpret I e a → Inh I σ a)
    (hcond : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ p ∈ x.2,
      ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e))
    (hbody : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ (b : Bool) (y : M),
      (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
        ∃ x ∈ xsOf b, (altPC c tbl vs x).interpret I e a ∧ altGC CG x e))
    (hT : I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) prem S Fp (sAnd (sExists xB boolP body) ensT))
    (hone : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m →
      ∃ y, Inh I σ y ∧ ∀ a, Inh I σ a → (Fp.interpret I e a ↔ a = y))
    {x : Term × List Cond} (hx : x ∈ xsOf true ++ xsOf false) :
    I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) (clauseQC c tbl vs s prem x) S Fp
      (sAnd (altPC c tbl vs x) (sTop S)) := by
  refine eqnPat_of F.sig.defOK F.sig.ceilDef hS.den hS.isSort hr hG fun e m hat hq a ha => ?_
  obtain ⟨hp, ⟨b, hb⟩, hgx⟩ :=
    (clauseQC_iff_lit F hr hσ hS.isSort hat (hin e m hat x hx) (hcond e m hat x hx)).mp hq
  have hT' := eqnPat_at F.sig.defOK F.sig.ceilDef hS.den hS.isSort hr hT hat hp
  obtain ⟨y, -, hy⟩ := hone e m hat
  have hbσ := hin e m hat x hx b hb
  have hby := (hy b hbσ).mp ((hT' b hbσ).mpr (rhs_of_alt_lit F hbody hat hx hbσ hb hgx))
  rw [andTop_on F.sig.defOK hS ha]
  constructor
  · intro hFa
    rw [(hy a ha).mp hFa, ← hby]; exact hb
  · intro hxa
    exact (hT' a ha).mpr (rhs_of_alt_lit F hbody hat hx ha hxa hgx)

/-- **The sentence and f's functional sentence give the last equation** `prem ∧ preBC s bs → F = BN`,
whatever `BN` is, with no `boolClosed`: where the premise holds, the body, at B := any element of
Bool, holds no element of σ (`hbodyB`: on σ it holds the alternatives `bs` read at the binder), so
the sentence leaves F no element of S, and the functional sentence gives it one. -/
theorem ex_last_of_text_lit {s : Srt} {bs : List (Term × List Cond)}
    {ws : List KoreAML.P} {σ : M} {prem body ensT S Fp : KoreAML.P} {xB : EVar} {CGB : Cond → Valuation M → Prop}
    (hS : SortAt I S σ) (hG : GuardsPred I ws)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ)
    (hxr : tbl.ev (evarKey (binderB c vs).kore) ≠ tbl.ev (sortVarKey Rv))
    (hinB : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ y, (inhOf boolP).interpret I e y → ∀ x ∈ bs, ∀ a,
      (altPC c tbl (vs ++ [binderB c vs]) x).interpret I (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) a →
        Inh I σ a)
    (hcondB : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ y, (inhOf boolP).interpret I e y → ∀ x ∈ bs,
      ∀ p ∈ x.2, ((tr ⟨tbl, []⟩ (Cond.kore c (vs ++ [binderB c vs]) R p)).interpret I
          (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) m ↔
        CGB p (updX e (tbl.ev (evarKey (binderB c vs).kore)) y)))
    (hbodyB : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ y, (inhOf boolP).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
        ∃ x ∈ bs, (altPC c tbl (vs ++ [binderB c vs]) x).interpret I
            (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) a ∧
          altGC CGB x (updX e (tbl.ev (evarKey (binderB c vs).kore)) y)))
    (hT : I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) prem S Fp (sAnd (sExists xB boolP body) ensT))
    (hone : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m →
      ∃ y, Inh I σ y ∧ ∀ a, Inh I σ a → (Fp.interpret I e a ↔ a = y))
    (BN : KoreAML.P) :
    I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) (lastBQC c tbl vs s prem bs) S Fp BN := by
  refine eqnPat_of F.sig.defOK F.sig.ceilDef hS.den hS.isSort hr hG fun e m hat hq a ha => ?_
  obtain ⟨hp, hno⟩ := (lastBQC_iff_lit F hr hσ hS.isSort hxr hat (hinB e m hat) (hcondB e m hat)).mp hq
  have hT' := eqnPat_at F.sig.defOK F.sig.ceilDef hS.den hS.isSort hr hT hat hp
  obtain ⟨y, hyσ, hy⟩ := hone e m hat
  have hrhs := (hT' y hyσ).mp ((hy y hyσ).mpr rfl)
  rw [interp_sAnd, interp_sExists] at hrhs
  obtain ⟨⟨z, hzB, hzb⟩, hens⟩ := hrhs
  have hz : (inhOf boolP).interpret I e z := by
    rw [interp_member F.sig.defOK] at hzB
    change (inhOf boolP).interpret I _ (Function.update e.evalEvar xB z xB) at hzB
    rw [Function.update_same] at hzB
    exact (inBool_iff_lit F _ e z).mp hzB
  obtain ⟨x, hx, hxa, hxg⟩ := (hbodyB e m hat z hz y hyσ).mp ⟨hzb, hens⟩
  exact (hno z hz x hx ⟨⟨y, hxa⟩, hxg⟩).elim

end

/-! ## The readings from the decision (KcoreSpec/TieEXReadB.lean), with `LitFacts` and `TermsInSortNI` -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}


/-- What the body gives at a valuation of the guards with B sent to an element y of Bool: the
body's elements are j's term's where each of j's conditions holds on all of R; each of j's
conditions holds at an element of R exactly where it holds on all of R; and j's term lies in σ. -/
theorem binder_core_lit {N : Parse.Names} {c : Semantics} (F : LitFacts c I) (hTS : TermsInSortNI c I)
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var} {Bv : Var} {s : Srt} {bodyK : Kore.Pattern}
    {j : Term × List Cond} {ws : List P} {σ : M}
    (hNI : tightNIB N (vsF ++ [Bv]) bodyK = true) (hnj : injFree j.1 = true)
    (hvars : Parse.varSorts N vsF = .ok vars) (hg : TieFRVars.guardsHold ws tblT vsF = true)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ)
    (hTab : tablesB c tbl tblT vars vsF Bv = true) (hBody : bodyB N c tbl tblT vars vsF Bv s bodyK j = true)
    {e : Valuation M} {m : M} (hat : At I ws (tbl.ev (sortVarKey Rv)) e m) {y : M}
    (hy : (inhOf boolP).interpret I e y) :
    (∀ a, (tr ⟨tblT, []⟩ bodyK).interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) a ↔
      (altPC c tbl (vsBof c vars) j).interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) a ∧
        ∀ z ∈ TieEXReadB.condPats c tbl (vsBof c vars) j.2, ∀ m', Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m' →
          z.interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) m') ∧
    (∀ z ∈ TieEXReadB.condPats c tbl (vsBof c vars) j.2, ∀ m', Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m' →
      (z.interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) m' ↔
        ∀ m'', Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m'' →
          z.interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) m'')) ∧
    ∀ a, (altPC c tbl (vsBof c vars) j).interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) a → Inh I σ a := by
  have hD := F.sig.defOK
  have hc := F.sig.ceilDef
  simp only [tablesB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hTab
  obtain ⟨⟨⟨⟨⟨⟨-, hxr⟩, hrT⟩, hA⟩, hAB⟩, hidx⟩, hlast⟩ := hTab
  simp only [bodyB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hBody
  obtain ⟨⟨⟨⟨⟨hTight, hNum⟩, hTerm⟩, hConds⟩, hty⟩, hs⟩ := hBody
  -- the valuation with B sent to y puts the variables and the binder in their sorts
  have hre : (updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tbl.ev (sortVarKey Rv)) =
      e.evalEvar (tbl.ev (sortVarKey Rv)) := Function.update_noteq (Ne.symm hxr) _ _
  have hV : ∀ i < (vars ++ [Srt.bool]).length, InS I (c.sortName ((vars ++ [Srt.bool]).getD i 0))
      ((updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tbl.ev (canonKey c (vars ++ [Srt.bool]) i))) := by
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · obtain ⟨h1, h2⟩ := hidx i hlt
      have h0 := TieFRVars.inS_of_guards hD hso hvars hA hg hat.1 (i := i)
        (by rw [← (TieFRVars.varSorts_spec hvars).1]; exact hlt)
      have hg' : (vars ++ [Srt.bool]).getD i 0 = vars.getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [h1, hg']
      show InS I _ (Function.update e.evalEvar _ y _)
      rw [Function.update_noteq h2]
      exact h0
    · have hg' : (vars ++ [Srt.bool]).getD vars.length 0 = Srt.bool := by simp [List.getD_eq_getElem?_getD]
      rw [hlast, hg']
      show InS I _ (Function.update e.evalEvar _ y _)
      rw [Function.update_same]
      have hy' := hy
      rw [← sortP_bool c] at hy'
      exact (inS_iff e).mp hy'
  have hT := tightSem_of_tightB_sig F.sig hTS hsy hso hAB hV hTight hNI
  have hrS : IsSort I ((updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tblT.ev (sortVarKey Rv))) := by
    rw [hrT, hre]; exact isSort_of_at hD hr hat
  have hpred : ∀ q ∈ bodyEqs bodyK, ∀ m', (tr ⟨tblT, []⟩ (.equals q.1 R q.2.1 q.2.2)).interpret I
      (updX e (tblT.ev (evarKey Bv.kore)) y) m' ↔
      Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m' ∧ EqH I tblT (updX e (tblT.ev (evarKey Bv.kore)) y) q := by
    intro q hq m'
    rw [eqPat_pred hD hc (sortDen_of_sortNumB_sig F.sig (hNum q hq) _) hrS m', hrT, hre]
  refine ⟨fun a => ?_, fun z hz m' hm' => ?_, fun a ha => ?_⟩
  · rw [bodySplit_sem hD hc hT (fun q hq => sortDen_of_sortNumB_sig F.sig (hNum q hq) _) a, hTerm, hConds]
    refine and_congr_right fun _ => ⟨fun h z hz m' hm' => ?_, fun h q hq => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      exact (hpred q hq m').mpr ⟨hm', h q hq⟩
    · exact ((hpred q hq m).mp (h _ (List.mem_map.mpr ⟨q, hq, rfl⟩) m hat.2)).2
  · rw [hConds] at hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    constructor
    · intro h m'' hm''
      exact (hpred q hq m'').mpr ⟨hm'', ((hpred q hq m').mp h).2⟩
    · intro h
      exact h m' hm'
  · have hvsB : vsBof c vars = canonVars c (vars ++ [Srt.bool]) := Model.canonVars_snocStdI c vars Srt.bool
    unfold altPC at ha
    rw [hvsB] at ha
    have h := hTS hnj hty hs (fun i hi => hV i (varOccs_lt j.1 hty i hi)) a ha
    rw [← inS_iff e] at h
    have hsp : KoreAML.Cons.sortP (c.sortName s) = trSort tbl (srtOf c s) := by
      rw [srtOf, Faithful.trSort_srt]; rfl
    rw [hsp, interp_inhOf_of (hσ e)] at h
    exact h

/-- **The readings from the decision.** -/
theorem exFacts_of_exB_lit {N : Parse.Names} {c : Semantics} (F : LitFacts c I) (hTS : TermsInSortNI c I)
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var} {Bv : Var} {s : Srt} {bodyK en : Kore.Pattern}
    {xT xF j : Term × List Cond} {al : List String} {ws : List P} {σ : M}
    (hNI : tightNIB N (vsF ++ [Bv]) bodyK = true) (hnj : injFree j.1 = true)
    (hvars : Parse.varSorts N vsF = .ok vars) (hg : TieFRVars.guardsHold ws tblT vsF = true)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hal : aliasFreeFR al bodyK = true) (hal' : aliasFreeFR al en = true)
    (h : exReadB N c tbl tblT vars vsF Bv s bodyK en xT xF j = true) :
    ExFacts I c tbl (canonVars c vars) ws σ (xsOfB xT xF) [j] (tr ⟨tblT, al⟩ bodyK) (tr ⟨tblT, al⟩ en)
      (tblT.ev (evarKey Bv.kore)) (CGof I c tbl (canonVars c vars)) (CGof I c tbl (vsBof c vars)) := by
  rw [tr_aliasFree tblT al _ hal, tr_aliasFree tblT al _ hal']
  have hD := F.sig.defOK
  have hc := F.sig.ceilDef
  simp only [exReadB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hTab, hBody⟩, hEns⟩, hIT⟩, hIF⟩ := h
  have core := fun {e : Valuation M} {m : M} (hat : At I ws (tbl.ev (sortVarKey Rv)) e m) {y : M}
      (hy : (inhOf boolP).interpret I e y) =>
    binder_core_lit F hTS hsy hso (s := s) (bodyK := bodyK) (j := j) hNI hnj hvars hg hr hσ hTab hBody hat hy
  have hTab' := hTab
  simp only [tablesB, Bool.and_eq_true, decide_eq_true_eq] at hTab'
  obtain ⟨⟨⟨⟨⟨⟨hxBG, hxr⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hTab'
  simp only [ensB, Bool.and_eq_true, decide_eq_true_eq] at hEns
  obtain ⟨hE1, hE2⟩ := hEns
  have hre : ∀ (e : Valuation M) y, (updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tbl.ev (sortVarKey Rv)) =
      e.evalEvar (tbl.ev (sortVarKey Rv)) := fun e y => Function.update_noteq (Ne.symm hxr) _ _
  -- the `ensures` part holds all of σ
  have hens : ∀ (e : Valuation M) a, Inh I σ a → (tr ⟨tblT, []⟩ en).interpret I e a := by
    intro e a ha
    rw [ens_reading hD hc (boolDen_of_sig F.sig) hE1 (fun e a => by rw [hE2]; exact hσ e a) hσS e a ha]
    intro b hb; cases hb
  -- the instances: each is j with its literal put for the binder's variable
  have hI : ∀ b, instB c tbl tblT vars Bv j b (bif b then xT else xF) = true := by
    intro b; cases b
    · exact hIF
    · exact hIT
  have hlit : ∀ (e : Valuation M) (b : Bool) (y : M), (den c (bool b)).interpret I e y →
      (inhOf boolP).interpret I e y ∧ ∀ (φ : P) (e' : Valuation M) (m : M),
        (φ.substEvar (tblT.ev (evarKey Bv.kore)) (den c (bool b))).interpret I e' m ↔
          φ.interpret I (updX e' (tblT.ev (evarKey Bv.kore)) y) m := by
    intro e b y hy
    obtain ⟨y0, hy0, hin0⟩ := bool_lit_lit F b e
    have hyy : y = y0 := (hy0 y).mp hy
    have hcl : Closed (den c (bool b)) := by
      rw [den_bool]; exact (Closed.sym _).app (Closed.sym _)
    exact ⟨hyy ▸ hin0, interp_substEvar_one fun e'' m => by rw [hcl.interp e'' e m, hy0 m, hyy]⟩
  have hmemX : ∀ x ∈ xsOfB xT xF true ++ xsOfB xT xF false, ∃ b, x = bif b then xT else xF := by
    intro x hx
    simp only [xsOfB, Bool.cond_true, Bool.cond_false, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e m hat x hx a ha
    obtain ⟨b, rfl⟩ := hmemX x hx
    obtain ⟨y, hy, -⟩ := bool_lit_lit F b e
    obtain ⟨hyB, sub⟩ := hlit e b y ((hy y).mpr rfl)
    have hi := hI b
    simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hi
    rw [← hi.1, sub] at ha
    exact (core hat hyB).2.2 a ha
  · intro e m hat x hx p hp
    obtain ⟨b, rfl⟩ := hmemX x hx
    obtain ⟨y, hy, -⟩ := bool_lit_lit F b e
    obtain ⟨hyB, sub⟩ := hlit e b y ((hy y).mpr rfl)
    have hi := hI b
    simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hi
    have hz' : tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) R p) ∈
        TieEXReadB.condPats c tbl (canonVars c vars) (bif b then xT else xF).2 := List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [← hi.2] at hz'
    obtain ⟨z, hz, hzz⟩ := List.mem_map.mp hz'
    unfold CGof
    rw [← hzz]
    simp only [sub]
    exact (core hat hyB).2.1 z hz m hat.2
  · intro e m hat b y hy a ha
    obtain ⟨hyB, sub⟩ := hlit e b y hy
    have hi := hI b
    simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hi
    rw [(core hat hyB).1 a]
    simp only [xsOfB, List.mem_singleton, exists_eq_left, altGC, CGof]
    rw [← hi.1, sub]
    refine ⟨fun ⟨⟨hA, hC⟩, _⟩ => ⟨hA, fun p hp m' hm' => ?_⟩, fun ⟨hA, hC⟩ => ⟨⟨hA, fun z hz m' hm' => ?_⟩, hens e a ha⟩⟩
    · have hz' : tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) R p) ∈
          TieEXReadB.condPats c tbl (canonVars c vars) (bif b then xT else xF).2 := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [← hi.2] at hz'
      obtain ⟨z, hz, hzz⟩ := List.mem_map.mp hz'
      rw [← hzz, sub]
      exact hC z hz m' hm'
    · have hz' : z.substEvar (tblT.ev (evarKey Bv.kore)) (den c (bool b)) ∈
          TieEXReadB.condPats c tbl (canonVars c vars) (bif b then xT else xF).2 := by
        rw [← hi.2]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
      obtain ⟨p, hp, hpz⟩ := List.mem_map.mp hz'
      have := hC p hp m' hm'
      rw [hpz, sub] at this
      exact this
  · rw [hxBG]; exact hxr
  · intro e m hat y hy x hx a ha
    rw [hxBG] at ha
    rw [List.mem_singleton] at hx
    subst hx
    exact (core hat hy).2.2 a ha
  · intro e m hat y hy x hx p hp
    rw [hxBG]
    rw [List.mem_singleton] at hx
    subst hx
    unfold CGof
    rw [hre]
    exact (core hat hy).2.1 _ (List.mem_map.mpr ⟨p, hp, rfl⟩) m hat.2
  · intro e m hat y hy a ha
    rw [hxBG, (core hat hy).1 a]
    have hre' : ∀ (e : Valuation M) y, Function.update e.evalEvar (tblT.ev (evarKey Bv.kore)) y
        (tbl.ev (sortVarKey Rv)) = e.evalEvar (tbl.ev (sortVarKey Rv)) := hre
    simp only [List.mem_singleton, exists_eq_left, altGC, CGof, hre']
    refine ⟨fun ⟨⟨hA, hC⟩, _⟩ => ⟨hA, fun p hp m' hm' => hC _ (List.mem_map.mpr ⟨p, hp, rfl⟩) m' hm'⟩,
      fun ⟨hA, hC⟩ => ⟨⟨hA, fun z hz m' hm' => ?_⟩, hens e a ha⟩⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact hC p hp m' hm'

end

end TieEXSig

end KCore
