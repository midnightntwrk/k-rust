/-
  An equation whose right side is `\exists` over one Bool variable, of a function with its
  `functional` sentence, against the n+1 equations of its split (`Parse.exClauses`, as
  `Parse.exRead` writes them), on the translated axioms.

  The sentence is `prem → F = (∃B:Bool. body) ∧ ens`. Its right side holds, on S, the elements of
  `body ∧ ens` at B := y for the elements y of Bool. The split has one clause per alternative x of
  the two instances `body[B := true] ∧ ens`, `body[B := false] ∧ ens`, with the premise
  `prem ∧ ⌈aₓ⌉ ∧ Gₓ` (`clauseQC`) and the right side aₓ; and a last clause with the premise
  `prem ∧ ¬∃B:Bool. ⋁ⱼ (⌈bⱼ⌉ ∧ Qⱼ)` (`lastBQC`), over the alternatives `(bⱼ, Qⱼ)` of `body ∧ ens`
  with B a variable (B the variable `binderB` at the index after the clause's variables).

  - `ex_clause_of_text`: the sentence and f's functional sentence give each alternative's equation.
    The element of a literal is in Bool, so an alternative of an instance that is defined where its
    predicates hold lies inside the right side (`rhs_of_alt`); the functional sentence makes F one
    element of S, which is therefore that alternative's element. No `boolClosed`.
  - `ex_last_of_text`: the sentence and f's functional sentence give the last equation, whatever
    its right side. Where its premise holds, no element of Bool gives the body an alternative that
    is defined where its predicates hold, so the right side is empty; the functional sentence gives
    F an element of S, which the sentence puts in the right side. No `boolClosed`.
  - `ex_text_of_split`: the n+1 equations and `boolClosed` give the sentence, with no functional
    sentence. Where every element of Bool is `true` or `false` (`boolClosed`), and each of them is
    one element of Bool (`NodeFacts.val`), the binder ranges over those two elements, so the right
    side holds the alternatives of the two instances (`rhs_ex`), and the last clause's premise holds
    exactly where no alternative of an instance is defined with its predicates (`readings_exB`).
    The last clause's right side `a₁ ∧ ⌈false = true⌉` holds nothing because `false` and `true` are
    two elements of Bool (`TieFRRead.noneEmpty_of_apart`, from `NodeFacts.apart`), a fact of `Γ`
    about Bool's domain values, not one of the sentence or of f. Without `boolClosed` the sentence
    does not follow: the right side also holds the body's elements at an element of Bool that is
    no literal's, which no clause speaks of.

  The theory of a definition read so holds `boolClosed` (`Γcl`): the last clause's predicate has a
  binder, so the definition reads a confined sort. Where another equation of f of a larger
  priority stands beside the EX equation, its item excludes the premises of all n+1 clauses; their
  disjunction is `⊤` only where Bool is closed, so that item is derived from the text with `Γcl`,
  not from the sentences alone.

  What each instance means at the valuation (`hbody`: the body at B := the element of a literal,
  against the alternatives read from the body with the literal put for B), what the body means at
  B := any element of Bool (`hbodyB`, against the alternatives with B a variable, read at the
  clause's binder), and what each condition of an alternative means (`hcond`, `hcondB`), are
  hypotheses: they are the reading of the patterns the split writes, as in `TieFR`.
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

/-- Bool's elements at any valuation are those at another: `inhOf boolP` is closed. -/
theorem inBool_iff (e e' : Valuation M) (y : M) :
    (inhOf boolP).interpret I e y ↔ (inhOf boolP).interpret I e' y := by
  obtain ⟨β, -, hβd⟩ := boolDen_of F
  rw [interp_inhOf_of (hβd e), interp_inhOf_of (hβd e')]

/-- **`∃B:Bool. φ` at a literal**: where φ holds at m with B sent to the element of a literal, the
existential holds at m. -/
theorem exists_of_lit {x : EVar} {φ : KoreAML.P} {e : Valuation M} {m : M} {b : Bool} {y : M}
    (hb : (den c (bool b)).interpret I e y) (hφ : φ.interpret I (updX e x y) m) :
    (sExists x boolP φ).interpret I e m := by
  rw [interp_sExists]
  refine ⟨y, ?_, hφ⟩
  rw [interp_member F.defOK]
  obtain ⟨y', hy', hin⟩ := bool_lit F b e
  show (inhOf boolP).interpret I (updX e x y) (Function.update e.evalEvar x y x)
  rw [Function.update_same, (hy' y).mp hb]
  exact (inBool_iff F e _ y').mp hin

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
    exact (interp_sExists).mp (exists_of_lit F hb hφ)

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

/-! ## The clauses of `exClauses` -/

/-- The predicate of an alternative's clause: `⌈a⌉ ∧ ⋀ⱼ pⱼ`. -/
def preOfC (s : Srt) (x : Term × List Cond) : Cond := Parse.conjC (Cond.ceil s x.1 :: x.2)

/-- The variable the last clause's predicate binds: `V<n>` of Bool, n the number of the clause's
variables (`Cond.kore`'s binder of `.ex`). -/
def binderB (c : Semantics) (vs : List KoreAML.Var) : KoreAML.Var := Cond.binder c vs.length Srt.bool

/-- The predicate of the last clause: no element of Bool gives an alternative of the body that is
defined where its predicates hold, `¬∃B:Bool. ⋁ⱼ (⌈bⱼ⌉ ∧ Qⱼ)`. -/
def preBC (s : Srt) (bs : List (Term × List Cond)) : Cond :=
  .not (.ex Srt.bool (Parse.disjC (bs.map (preOfC s))))

/-- **The clauses of `exClauses`**: one per alternative, its term as the right side and `preOfC` as
its predicate, and the last, with the first alternative's term, the `ensures` false and `preBC`. -/
theorem exClauses_eqC (s : Srt) (vars : List Srt) (pats : List Term) (req : Option Term) (prio : Nat)
    (aside : Bool) (xs bs : List (Term × List Cond)) :
    Parse.exClauses s vars pats req prio aside xs bs =
      xs.map (fun x => ({ vars, pats, req, rhs := x.1, ens := none, prio, aside, pre := preOfC s x } : Clause)) ++
        [{ vars, pats, req, rhs := (xs.headD (Parse.boolT false, [])).1, ens := some (Parse.boolT false), prio, aside,
           pre := preBC s bs }] := by
  unfold Parse.exClauses preBC
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

/-- The premise of the last clause, `prem ∧ preBC s bs` (`withPre`). -/
def lastBQC (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (s : Srt) (prem : KoreAML.P)
    (bs : List (Term × List Cond)) : KoreAML.P :=
  sAnd prem (tr ⟨tbl, []⟩ (Cond.kore c vs R (preBC s bs)))

theorem preOfC_isTop (s : Srt) (x : Term × List Cond) : (preOfC s x).isTop = false := by
  unfold preOfC; cases x.2 <;> rfl

theorem preBC_isTop (s : Srt) (bs : List (Term × List Cond)) : (preBC s bs).isTop = false := rfl

/-- `Cond.kore` of `∃B:Bool. φ`: the existential over the table's variable of the binder, at Bool,
of φ read with the binder after the clause's variables. -/
theorem tr_condEx (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (φ : Cond) :
    tr ⟨tbl, []⟩ (Cond.kore c vs R (.ex Srt.bool φ)) =
      sExists (tbl.ev (evarKey (binderB c vs).kore)) boolP
        (tr ⟨tbl, []⟩ (Cond.kore c (vs ++ [binderB c vs]) R φ)) := by
  show sExists _ (trSort tbl (KoreAML.srt (c.sortName Srt.bool))) _ = _
  rw [Faithful.sortName_bool, Faithful.trSort_srt]
  rfl

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics}
  (F : HoldsShape.NodeFacts c I) {tbl : VarTable} {vs : List KoreAML.Var}
include F

omit [Inhabited M] in
/-- A disjunction of conditions, at an element of the sort variable's sort, holds where one does. -/
theorem condKore_disjC {e : Valuation M} {m : M} (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m) :
    ∀ ps : List Cond, (tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.disjC ps))).interpret I e m ↔
      ∃ p ∈ ps, (tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m
  | [] => by
    rw [Parse.disjC, Cond.kore, tr_bottom_iff F.defOK]
    simp
  | [p] => by
    rw [Parse.disjC]
    simp
  | p :: q :: qs => by
    show (tr ⟨tbl, []⟩ (Cond.kore c vs R (.or p (Parse.disjC (q :: qs))))).interpret I e m ↔ _
    rw [Cond.kore, tr_or]
    simp only [trOrList]
    rw [interp_sOr, TieFRRead.trSort_R, interp_inhOf_of (fun _ => interp_evar), condKore_disjC hm (q :: qs)]
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

/-- **The premise of an alternative's clause**: the sentence's premise holds, the alternative is
defined and its predicates hold. -/
theorem clauseQC_iff {s : Srt} {ws : List KoreAML.P} {σ : M} {prem : KoreAML.P} {CG : Cond → Valuation M → Prop}
    {x : Term × List Cond} (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    {e : Valuation M} {m : M} (hat : At I ws (tbl.ev (sortVarKey Rv)) e m)
    (hφ : ∀ a, (altPC c tbl vs x).interpret I e a → Inh I σ a)
    (hcond : ∀ p ∈ x.2, ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e)) :
    (clauseQC c tbl vs s prem x).interpret I e m ↔
      prem.interpret I e m ∧ (∃ b, (altPC c tbl vs x).interpret I e b) ∧ altGC CG x e := by
  unfold clauseQC
  rw [interp_sAnd, preOfC_iff F (hσ e) hσS (isSort_of_at F.defOK hr hat) hat.2 hφ hcond]

/-- **The premise of the last clause**: the sentence's premise holds, and at no element y of Bool
is an alternative of the body, read with the binder sent to y, defined where its predicates hold.
The binder's variable is not the sort variable (`hxr`); the alternatives of the body lie in σ and
their conditions read as `CGB` at each element of Bool (`hinB`, `hcondB`). -/
theorem lastBQC_iff {s : Srt} {ws : List KoreAML.P} {σ : M} {prem : KoreAML.P} {CGB : Cond → Valuation M → Prop}
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
  have hrS := isSort_of_at F.defOK hr hat
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
    rw [condKore_disjC F (by rw [hrU]; exact hat.2)]
    have hx : ∀ x ∈ bs, ((tr ⟨tbl, []⟩ (Cond.kore c (vs ++ [binderB c vs]) R (preOfC s x))).interpret I
        (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) m ↔
          (∃ b, (altPC c tbl (vs ++ [binderB c vs]) x).interpret I
            (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) b) ∧
          altGC CGB x (updX e (tbl.ev (evarKey (binderB c vs).kore)) y)) := fun x hx =>
      preOfC_iff F (hσ _) hσS (by rw [hrU]; exact hrS) (by rw [hrU]; exact hat.2)
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
    rw [interp_member F.defOK]
    show (inhOf boolP).interpret I _ (Function.update e.evalEvar _ y _) ↔ _
    rw [Function.update_same]
    exact inBool_iff F _ e y
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
theorem rhs_of_alt {ws : List KoreAML.P} {r xB : EVar} {σ : M} {body ensT : KoreAML.P}
    {α : Type} {xsOf : Bool → List α} {A : α → KoreAML.P} {G : α → Valuation M → Prop}
    (hbody : ∀ e m, At I ws r e m → ∀ (b : Bool) (y : M), (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔ ∃ x ∈ xsOf b, (A x).interpret I e a ∧ G x e))
    {e : Valuation M} {m : M} (hat : At I ws r e m) {x : α} (hx : x ∈ xsOf true ++ xsOf false)
    {a : M} (ha : Inh I σ a) (hxa : (A x).interpret I e a) (hgx : G x e) :
    (sAnd (sExists xB boolP body) ensT).interpret I e a := by
  have hgo : ∀ b, x ∈ xsOf b → (sAnd (sExists xB boolP body) ensT).interpret I e a := by
    intro b hxb
    obtain ⟨y, hy, -⟩ := bool_lit F b e
    have := (hbody e m hat b y ((hy y).mpr rfl) a ha).mpr ⟨x, hxb, hxa, hgx⟩
    rw [interp_sAnd]
    exact ⟨exists_of_lit F ((hy y).mpr rfl) this.1, this.2⟩
  rcases List.mem_append.mp hx with h | h
  · exact hgo true h
  · exact hgo false h

/-! ## The tie -/

/-- **The sentence and f's functional sentence give the equation of each alternative**
`prem ∧ preOfC s x → F = aₓ ∧ ⊤_S`, with no `boolClosed`. -/
theorem ex_clause_of_text {s : Srt} {xsOf : Bool → List (Term × List Cond)}
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
  refine eqnPat_of F.defOK F.ceilDef hS.den hS.isSort hr hG fun e m hat hq a ha => ?_
  obtain ⟨hp, ⟨b, hb⟩, hgx⟩ :=
    (clauseQC_iff F hr hσ hS.isSort hat (hin e m hat x hx) (hcond e m hat x hx)).mp hq
  have hT' := eqnPat_at F.defOK F.ceilDef hS.den hS.isSort hr hT hat hp
  obtain ⟨y, -, hy⟩ := hone e m hat
  have hbσ := hin e m hat x hx b hb
  have hby := (hy b hbσ).mp ((hT' b hbσ).mpr (rhs_of_alt F hbody hat hx hbσ hb hgx))
  rw [andTop_on F.defOK hS ha]
  constructor
  · intro hFa
    rw [(hy a ha).mp hFa, ← hby]; exact hb
  · intro hxa
    exact (hT' a ha).mpr (rhs_of_alt F hbody hat hx ha hxa hgx)

/-- **The sentence and f's functional sentence give the last equation** `prem ∧ preBC s bs → F = BN`,
whatever `BN` is, with no `boolClosed`: where the premise holds, the body, at B := any element of
Bool, holds no element of σ (`hbodyB`: on σ it holds the alternatives `bs` read at the binder), so
the sentence leaves F no element of S, and the functional sentence gives it one. -/
theorem ex_last_of_text {s : Srt} {bs : List (Term × List Cond)}
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
  refine eqnPat_of F.defOK F.ceilDef hS.den hS.isSort hr hG fun e m hat hq a ha => ?_
  obtain ⟨hp, hno⟩ := (lastBQC_iff F hr hσ hS.isSort hxr hat (hinB e m hat) (hcondB e m hat)).mp hq
  have hT' := eqnPat_at F.defOK F.ceilDef hS.den hS.isSort hr hT hat hp
  obtain ⟨y, hyσ, hy⟩ := hone e m hat
  have hrhs := (hT' y hyσ).mp ((hy y hyσ).mpr rfl)
  rw [interp_sAnd, interp_sExists] at hrhs
  obtain ⟨⟨z, hzB, hzb⟩, hens⟩ := hrhs
  have hz : (inhOf boolP).interpret I e z := by
    rw [interp_member F.defOK] at hzB
    change (inhOf boolP).interpret I _ (Function.update e.evalEvar xB z xB) at hzB
    rw [Function.update_same] at hzB
    exact (inBool_iff F _ e z).mp hzB
  obtain ⟨x, hx, hxa, hxg⟩ := (hbodyB e m hat z hz y hyσ).mp ⟨hzb, hens⟩
  exact (hno z hz x hx ⟨⟨y, hxa⟩, hxg⟩).elim

/-- **The readings of the split of `prem → F = (∃B:Bool. body) ∧ ens`** (`TieFR.Readings`), with
`boolClosed`: the alternatives are those of the instance at `true`, then those at `false`
(`exRead`'s order); the right side holds them (`rhs_ex`); the last clause's premise holds where none
is defined with its predicates, since every element of Bool is a literal's. -/
theorem readings_exB (hcl : I ⊧ᴵ boolClosed c) {s : Srt} {xsOf : Bool → List (Term × List Cond)}
    {bs : List (Term × List Cond)}
    {ws : List KoreAML.P} {σ : M} {prem body ensT : KoreAML.P} {xB : EVar}
    {CG CGB : Cond → Valuation M → Prop}
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ a,
      (altPC c tbl vs x).interpret I e a → Inh I σ a)
    (hcond : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ p ∈ x.2,
      ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e))
    (hbody : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ (b : Bool) (y : M),
      (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
      (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
        ∃ x ∈ xsOf b, (altPC c tbl vs x).interpret I e a ∧ altGC CG x e))
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
          altGC CGB x (updX e (tbl.ev (evarKey (binderB c vs).kore)) y))) :
    Readings I ws (tbl.ev (sortVarKey Rv)) σ prem (sAnd (sExists xB boolP body) ensT)
      (xsOf true ++ xsOf false) (altPC c tbl vs) (altGC CG)
      (clauseQC c tbl vs s prem) (lastBQC c tbl vs s prem bs) where
  inSort := hin
  clause e m hat x hx := clauseQC_iff F hr hσ hσS hat (hin e m hat x hx) (hcond e m hat x hx)
  none e m hat := by
    rw [lastBQC_iff F hr hσ hσS hxr hat (hinB e m hat) (hcondB e m hat)]
    refine and_congr Iff.rfl ⟨fun h x hx hxd => ?_, fun h y hy j hj hjd => ?_⟩
    · -- an alternative of an instance defined with its predicates gives the body an element at a literal
      obtain ⟨⟨b, hb⟩, hgx⟩ := hxd
      have hbσ := hin e m hat x hx b hb
      have hgo : ∀ b', x ∈ xsOf b' → False := by
        intro b' hxb
        obtain ⟨y, hy, hyB⟩ := bool_lit F b' e
        have hbd := (hbody e m hat b' y ((hy y).mpr rfl) b hbσ).mpr ⟨x, hxb, hb, hgx⟩
        obtain ⟨j, hj, hja, hjg⟩ := (hbodyB e m hat y hyB b hbσ).mp hbd
        exact h y hyB j hj ⟨⟨b, hja⟩, hjg⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hgo true hx
      · exact hgo false hx
    · -- an alternative of the body at an element of Bool, a literal's by `boolClosed`
      obtain ⟨⟨b, hb⟩, hjg⟩ := hjd
      have hbσ := hinB e m hat y hy j hj b hb
      have hbd := (hbodyB e m hat y hy b hbσ).mpr ⟨j, hj, hb, hjg⟩
      obtain ⟨b', hb'⟩ := bool_cases F hcl hy
      obtain ⟨x, hx, hxa, hxg⟩ := (hbody e m hat b' y hb' b hbσ).mp hbd
      have hxm : x ∈ xsOf true ++ xsOf false := by
        cases b'
        · exact List.mem_append_right _ hx
        · exact List.mem_append_left _ hx
      exact h x hxm ⟨⟨b, hxa⟩, hxg⟩
  rhs := rhs_ex F hcl hbody

/-- **The n+1 equations and `boolClosed` give the sentence**, with no functional sentence: the last
clause's right side `A₁ ∧ ⌈false = true⌉` holds nothing (`noneEmpty_of_apart`). -/
theorem ex_text_of_split (hcl : I ⊧ᴵ boolClosed c) {s : Srt} {xsOf : Bool → List (Term × List Cond)}
    {bs : List (Term × List Cond)}
    {ws : List KoreAML.P} {σ : M} {prem body ensT S Fp A₁ : KoreAML.P} {xB : EVar}
    {CG CGB : Cond → Valuation M → Prop} {SR : Kore.KSort}
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
    (hk : ∀ x ∈ xsOf true ++ xsOf false,
      I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) (clauseQC c tbl vs s prem x) S Fp (sAnd (altPC c tbl vs x) (sTop S)))
    (hn : I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) (lastBQC c tbl vs s prem bs) S Fp
      (sAnd A₁ (tr ⟨tbl, []⟩ (reqPat SR (some (Term.kore c vs (Parse.boolT false))))))) :
    I ⊧ᴵ eqnPat ws (tbl.ev (sortVarKey Rv)) prem S Fp (sAnd (sExists xB boolP body) ensT) :=
  text_of_split F.defOK F.ceilDef hS hr hG
    (readings_exB F hcl hr hσ hS.isSort hin hcond hbody hxr hinB hcondB hbodyB) hk hn
    (noneEmpty_of_apart F hSR hS.isSort)

end

end TieEX

end KCore
