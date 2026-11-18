/-
  An equation whose right side is `\exists` over one Bool variable, of a function with its
  `functional` sentence, against the n+1 equations of its split (`Parse.frClauses` over the
  alternatives of the two instances, as `Parse.exRead` writes them), on the translated axioms.

  The sentence is `prem → F = (∃B:Bool. body) ∧ ens`. Where every element of Bool is `true` or
  `false` (`boolClosed`), and each of them is one element of Bool (`NodeFacts.val`), the binder
  ranges over those two elements, so the right side holds on S the elements of the two instances
  `body[B := true] ∧ ens` and `body[B := false] ∧ ens` (`exists_bool_iff`). Where each instance holds
  exactly the elements of its alternatives at which their predicates hold, the right side holds
  those of all the alternatives (`rhs_ex`): the reading `TieFR.Readings.rhs` asks. The rest of
  `TieFR.Readings` is read from the clauses' premises as for an `\or`, with predicates any
  conditions (`readings_of_rhsC`: `TieFRRead.readings_of_rhs` reads only conditions that a Bool term
  be `true`).

  - `ex_clause_of_text`: the sentence, f's functional sentence and `boolClosed` give each
    alternative's equation.
  - `ex_none_of_text`: the same give the last equation.
  - `ex_text_of_split`: the n+1 equations and `boolClosed` give the sentence, the last clause's
    right side `a₁ ∧ ⌈false = true⌉` holding nothing because `false` and `true` are two elements of
    Bool (`TieFRRead.noneEmpty_of_apart`, from `NodeFacts.apart`), a fact of `Γ` about Bool's
    domain values, not one of the sentence or of f.

  What each instance means at the valuation (`hbody`: the body at B := the element of a literal,
  against the alternatives `exRead` reads from the body with the literal put for B), and what each
  condition of an alternative means (`hcond`), are hypotheses: they are the reading of the patterns
  the split writes, as in `TieFR`.
-/
import KcoreSpec.TieFRRead

set_option autoImplicit false

namespace KCore

namespace TieEX

open ML Faithful KoreAML KoreAML.TieFR TieFRRead

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- e with the element variable x sent to a. -/
abbrev updX (e : Valuation M) (x : EVar) (a : M) : Valuation M :=
  ⟨Function.update e.evalEvar x a, e.evalSvar⟩

/-- The sort of `boolClosed` is `SortBool{}`. -/
theorem sortP_bool (c : Semantics) : sortP (c.sortName Srt.bool) = boolP := by
  rw [sortName_bool]; rfl

variable {c : Semantics} (F : HoldsShape.NodeFacts c I)
include F

/-- **`boolClosed` read**: every element of Bool is the element of `true` or of `false`. -/
theorem bool_cases (hcl : I ⊧ᴵ boolClosed c) {e : Valuation M} {y : M}
    (hy : (inhOf boolP).interpret I e y) : ∃ b : Bool, (den c (bool b)).interpret I e y := by
  have hb := hcl e y
  unfold boolClosed at hb
  rw [interp_included F.defOK, sortP_bool] at hb
  have hy' := hb y hy
  by_cases h1 : (den c (.dv Srt.bool (.bool true))).interpret I e y
  · exact ⟨true, h1⟩
  · simp only [Pattern.interpret] at hy'
    exact ⟨false, hy' h1⟩

/-- Each literal of Bool is one element of Bool. -/
theorem bool_lit (b : Bool) (e : Valuation M) :
    ∃ y, (∀ m, (den c (bool b)).interpret I e m ↔ m = y) ∧ (inhOf boolP).interpret I e y := by
  obtain ⟨y, hy, hin⟩ := F.val (rmS_sortOf_bool c b) [] e
  rw [srtOf, sortName_bool, trSort_srt] at hin
  exact ⟨y, hy, hin⟩

/-- **`∃B:Bool. φ` is its two instances**: with `boolClosed`, it holds at m exactly where φ holds at
m with B sent to the element of `true` or of `false`. -/
theorem exists_bool_iff (hcl : I ⊧ᴵ boolClosed c) {x : EVar} {φ : KoreAML.P} {e : Valuation M} {m : M} :
    (sExists x boolP φ).interpret I e m ↔
      ∃ (b : Bool) (y : M), (den c (bool b)).interpret I e y ∧ φ.interpret I (updX e x y) m := by
  obtain ⟨β, hβ, hβd⟩ := boolDen_of F
  have hinh : ∀ (e' : Valuation M) a, (inhOf boolP).interpret I e' a ↔ Inh I β a :=
    fun e' a => interp_inhOf_of (hβd e')
  rw [interp_sExists]
  constructor
  · rintro ⟨y, hy, hφ⟩
    rw [interp_member F.defOK] at hy
    have hy' : (inhOf boolP).interpret I e y := by
      rw [hinh]; rw [hinh] at hy; simpa using hy
    obtain ⟨b, hb⟩ := bool_cases F hcl hy'
    exact ⟨b, y, hb, hφ⟩
  · rintro ⟨b, y, hb, hφ⟩
    refine ⟨y, ?_, hφ⟩
    rw [interp_member F.defOK, hinh]
    obtain ⟨y', hy', hin⟩ := bool_lit F b e
    rw [(hy' y).mp hb]
    rw [hinh] at hin
    simpa using hin

/-- **The right side `(∃B:Bool. body) ∧ ens` holds the alternatives of the two instances**: where,
for each literal b, `body` at B := b's element with `ens` holds on S exactly the alternatives
`xsOf b` at which their predicates hold, the right side holds those of `xsOf true ++ xsOf false`. -/
theorem rhs_ex (hcl : I ⊧ᴵ boolClosed c) {ws : List KoreAML.P} {r xB : EVar} {σ : M} {body ensT : KoreAML.P}
    {α : Type} {xsOf : Bool → List α} {A : α → KoreAML.P} {G : α → Valuation M → Prop}
    (hbody : ∀ e m, At I ws r e m → ∀ (b : Bool) (y : M), (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔ ∃ x ∈ xsOf b, (A x).interpret I e a ∧ G x e)) :
    ∀ e m, At I ws r e m → ∀ a, Inh I σ a →
      ((sAnd (sExists xB boolP body) ensT).interpret I e a ↔
        ∃ x ∈ xsOf true ++ xsOf false, (A x).interpret I e a ∧ G x e) := by
  intro e m hat a ha
  rw [interp_sAnd, exists_bool_iff F hcl]
  constructor
  · rintro ⟨⟨b, y, hb, hφ⟩, hens⟩
    obtain ⟨x, hx, hxa⟩ := (hbody e m hat b y hb a ha).mp ⟨hφ, hens⟩
    refine ⟨x, ?_, hxa⟩
    cases b
    · exact List.mem_append_right _ hx
    · exact List.mem_append_left _ hx
  · rintro ⟨x, hx, hxa⟩
    have hgo : ∀ b, x ∈ xsOf b → (∃ (b : Bool) (y : M), (den c (bool b)).interpret I e y ∧
        body.interpret I (updX e xB y) a) ∧ ensT.interpret I e a := by
      intro b hxb
      obtain ⟨y, hy, -⟩ := bool_lit F b e
      have := (hbody e m hat b y ((hy y).mpr rfl) a ha).mpr ⟨x, hxb, hxa⟩
      exact ⟨⟨b, y, (hy y).mpr rfl, this.1⟩, this.2⟩
    rcases List.mem_append.mp hx with h | h
    · exact hgo true h
    · exact hgo false h

end

/-! ## The clauses of alternatives with any conditions -/

/-- The predicate of an alternative's clause: `⌈a⌉ ∧ ⋀ⱼ pⱼ`. -/
def preOfC (s : Srt) (x : Term × List Cond) : Cond := Parse.conjC (Cond.ceil s x.1 :: x.2)

/-- The predicate of the last clause: no alternative's predicate holds. -/
def preNC (s : Srt) (xs : List (Term × List Cond)) : Cond := Parse.conjC ((xs.map (preOfC s)).map Cond.not)

/-- **The clauses of `frClauses`**: one per alternative, its term as the right side and `preOfC` as
its predicate, and the last, with the first alternative's term, the `ensures` false and `preNC`. -/
theorem frClauses_eqC (s : Srt) (vars : List Srt) (pats : List Term) (req : Option Term) (prio : Nat)
    (aside : Bool) (xs : List (Term × List Cond)) :
    Parse.frClauses s vars pats req prio aside xs =
      xs.map (fun x => ({ vars, pats, req, rhs := x.1, ens := none, prio, aside, pre := preOfC s x } : Clause)) ++
        [{ vars, pats, req, rhs := (xs.headD (Parse.boolT false, [])).1, ens := some (Parse.boolT false), prio, aside,
           pre := preNC s xs }] := by
  unfold Parse.frClauses preNC
  dsimp only
  rw [map_zip_map_self]
  rfl

/-- The right side of an alternative's clause. -/
def altPC (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (x : Term × List Cond) : KoreAML.P :=
  tr ⟨tbl, []⟩ (Term.kore c vs x.1)

/-- The predicates of an alternative: each of its conditions holds, as `CG` reads it. -/
def altGC {M : Type} (CG : Cond → Valuation M → Prop) (x : Term × List Cond) (e : Valuation M) : Prop :=
  ∀ p ∈ x.2, CG p e

/-- The premise of an alternative's clause, `prem ∧ preOfC s x` (`withPre`). -/
def clauseQC (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (s : Srt) (prem : KoreAML.P)
    (x : Term × List Cond) : KoreAML.P :=
  sAnd prem (tr ⟨tbl, []⟩ (Cond.kore c vs R (preOfC s x)))

/-- The premise of the last clause, `prem ∧ preNC s xs` (`withPre`). -/
def lastQC (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (s : Srt) (prem : KoreAML.P)
    (xs : List (Term × List Cond)) : KoreAML.P :=
  sAnd prem (tr ⟨tbl, []⟩ (Cond.kore c vs R (preNC s xs)))

theorem preOfC_isTop (s : Srt) (x : Term × List Cond) : (preOfC s x).isTop = false := by
  unfold preOfC; cases x.2 <;> rfl

theorem preNC_isTop (s : Srt) {xs : List (Term × List Cond)} (h : xs ≠ []) : (preNC s xs).isTop = false := by
  unfold preNC
  rcases xs with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact (h rfl).elim
  · rfl
  · rfl

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics}
  (F : HoldsShape.NodeFacts c I) {tbl : VarTable} {vs : List KoreAML.Var}
include F

/-- An alternative's predicate, at an element of the sort variable's sort: its term is defined and
each of its conditions holds. -/
theorem preOfC_iff {e : Valuation M} {m : M} {s : Srt} {σ : M} {x : Term × List Cond}
    {CG : Cond → Valuation M → Prop}
    (hσ : ∀ a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv)))) (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m)
    (hφ : ∀ b, (altPC c tbl vs x).interpret I e b → Inh I σ b)
    (hcond : ∀ p ∈ x.2, ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e)) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (preOfC s x))).interpret I e m ↔
      (∃ b, (altPC c tbl vs x).interpret I e b) ∧ altGC CG x e := by
  unfold preOfC
  rw [condKore_conjC F hm]
  simp only [List.mem_cons, forall_eq_or_imp]
  rw [condKore_ceil F hσ hσS hr hm hφ]
  refine and_congr Iff.rfl ⟨fun h p hp => (hcond p hp).mp (h p hp), fun h p hp => (hcond p hp).mpr (h p hp)⟩

/-- **The readings of the clauses `frClauses` writes**, for alternatives with any conditions
(`TieFR.Readings`): each clause's premise (`clauseQC`, `lastQC`) reads from `NodeFacts` and the
conditions' reading `hcond`; that each alternative lies in the result sort σ is `hin`; the
reading of the sentence's right side is `hrhs`. -/
theorem readings_of_rhsC {s : Srt} {xs : List (Term × List Cond)}
    {ws : List KoreAML.P} {σ : M} {prem rhsT : KoreAML.P} {CG : Cond → Valuation M → Prop}
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xs, ∀ a,
      (altPC c tbl vs x).interpret I e a → Inh I σ a)
    (hcond : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xs, ∀ p ∈ x.2,
      ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e))
    (hrhs : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ a, Inh I σ a →
      (rhsT.interpret I e a ↔ ∃ x ∈ xs, (altPC c tbl vs x).interpret I e a ∧ altGC CG x e)) :
    Readings I ws (tbl.ev (sortVarKey Rv)) σ prem rhsT xs (altPC c tbl vs) (altGC CG)
      (clauseQC c tbl vs s prem) (lastQC c tbl vs s prem xs) where
  inSort := hin
  clause e m hat x hx := by
    have hrS := isSort_of_at F.defOK hr hat
    unfold clauseQC
    rw [interp_sAnd, preOfC_iff F (hσ e) hσS hrS hat.2 (hin e m hat x hx) (hcond e m hat x hx)]
  none e m hat := by
    have hrS := isSort_of_at F.defOK hr hat
    unfold lastQC preNC
    rw [interp_sAnd, condKore_conjC F hat.2]
    refine and_congr Iff.rfl ?_
    simp only [List.forall_mem_map]
    refine forall_congr' fun x => forall_congr' fun hx => ?_
    rw [condKore_not, preOfC_iff F (hσ e) hσS hrS hat.2 (hin e m hat x hx) (hcond e m hat x hx)]
    exact ⟨fun h => h.1, fun h => ⟨h, hat.2⟩⟩
  rhs := hrhs

/-! ## The tie -/

/-- **The readings of the split of `prem → F = (∃B:Bool. body) ∧ ens`**: the alternatives are those
of the instance at `true`, then those at `false` (`exRead`'s order); with `boolClosed`, the right
side's reading is `rhs_ex`'s, the rest `readings_of_rhsC`'s. -/
theorem readings_ex (hcl : I ⊧ᴵ boolClosed c) {s : Srt} {xsOf : Bool → List (Term × List Cond)}
    {ws : List KoreAML.P} {σ : M} {prem body ensT : KoreAML.P} {xB : EVar} {CG : Cond → Valuation M → Prop}
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ a,
      (altPC c tbl vs x).interpret I e a → Inh I σ a)
    (hcond : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ p ∈ x.2,
      ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e))
    (hbody : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ (b : Bool) (y : M),
      (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
        ∃ x ∈ xsOf b, (altPC c tbl vs x).interpret I e a ∧ altGC CG x e)) :
    Readings I ws (tbl.ev (sortVarKey Rv)) σ prem (sAnd (sExists xB boolP body) ensT)
      (xsOf true ++ xsOf false) (altPC c tbl vs) (altGC CG)
      (clauseQC c tbl vs s prem) (lastQC c tbl vs s prem (xsOf true ++ xsOf false)) :=
  readings_of_rhsC F hr hσ hσS hin hcond (rhs_ex F hcl hbody)

/-- **The sentence, f's functional sentence and `boolClosed` give the equation of each
alternative** `prem ∧ preOfC s x → F = aₓ ∧ ⊤_S`. -/
theorem ex_clause_of_text (hcl : I ⊧ᴵ boolClosed c) {s : Srt} {xsOf : Bool → List (Term × List Cond)}
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
      (sAnd (altPC c tbl vs x) (sTop S)) :=
  clause_of_text F.defOK F.ceilDef hS hr hG
    (readings_ex F hcl hr hσ hS.isSort hin hcond hbody) hT hone hx

/-- **The sentence, f's functional sentence and `boolClosed` give the last equation**
`prem ∧ preNC s xs → F = BN`, whatever `BN` is. -/
theorem ex_none_of_text (hcl : I ⊧ᴵ boolClosed c) {s : Srt} {xsOf : Bool → List (Term × List Cond)}
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
    (BN : KoreAML.P) :
    I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) (lastQC c tbl vs s prem (xsOf true ++ xsOf false)) S Fp BN :=
  none_of_text F.defOK F.ceilDef hS hr hG
    (readings_ex F hcl hr hσ hS.isSort hin hcond hbody) hT hone BN

/-- **The n+1 equations and `boolClosed` give the sentence**, with no functional sentence: the last
clause's right side `A₁ ∧ ⌈false = true⌉` holds nothing (`noneEmpty_of_apart`). -/
theorem ex_text_of_split (hcl : I ⊧ᴵ boolClosed c) {s : Srt} {xsOf : Bool → List (Term × List Cond)}
    {ws : List KoreAML.P} {σ : M} {prem body ensT S Fp A₁ : KoreAML.P} {xB : EVar} {CG : Cond → Valuation M → Prop}
    {SR : Kore.KSort}
    (hS : SortAt I S σ) (hG : GuardsPred I ws)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ)
    (hSR : ∀ (e : Valuation M) a, (trSort tbl SR).interpret I e a ↔ a = σ)
    (hin : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ a,
      (altPC c tbl vs x).interpret I e a → Inh I σ a)
    (hcond : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ p ∈ x.2,
      ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e))
    (hbody : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ (b : Bool) (y : M),
      (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
        ∃ x ∈ xsOf b, (altPC c tbl vs x).interpret I e a ∧ altGC CG x e))
    (hk : ∀ x ∈ xsOf true ++ xsOf false,
      I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) (clauseQC c tbl vs s prem x) S Fp (sAnd (altPC c tbl vs x) (sTop S)))
    (hn : I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) (lastQC c tbl vs s prem (xsOf true ++ xsOf false)) S Fp
      (sAnd A₁ (tr ⟨tbl, []⟩ (reqPat SR (some (Term.kore c vs (Parse.boolT false))))))) :
    I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) prem S Fp (sAnd (sExists xB boolP body) ensT) :=
  text_of_split F.defOK F.ceilDef hS hr hG
    (readings_ex F hcl hr hσ hS.isSort hin hcond hbody) hk hn
    (noneEmpty_of_apart F hSR hS.isSort)

end

end TieEX

end KCore
