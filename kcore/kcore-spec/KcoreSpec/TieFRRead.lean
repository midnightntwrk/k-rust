/-
  The readings `TieFR.Readings` asks of an equation with `\or` on its right side, for the clauses
  `Parse.frClauses` writes and the right side `Parse.frRead` reads, in every interpretation with
  the facts of a model of `Γ` it names.

  ## The right side: what the reader's normalisation keeps (`rhs_sem`)

  `frRead` reads the right side p as `hoist (dropEmptyAlts p) = (r, cs, false)`, the alternatives
  `orAlts r`, each read through `hoist`, an empty one left out (`keptAlts`). Each step keeps the
  elements of p, where p is `Tight`:
  - `dropEmptyAlts` leaves out the alternatives `vacuous` accepts, which hold nothing
    (`InertEv.vacuous_none`); an `\or` left with one alternative is that alternative.
  - `hoist` lifts the conjuncts `\equals{Bool,s}(B, true)` out of conjunctions and applications,
    and reads `t ∨ ⊥` as t: a conjunct that holds where B is `true` holds all of the conjunction's
    sort s there and nothing elsewhere, and an application with an empty argument is empty.
  - `orAlts` distributes `\or` over applications and conjunctions: application is pointwise, so it
    distributes over a union in each argument, and so does intersection.
  Each step drops a restriction to a sort: `\or{s}` holds only elements of s (`sOr`), and so does
  the conjunct `\equals{Bool,s}(B, true)`. That the operands of each `\or{s}` and `\and{s}` lie in
  s (`InSortK`), and that the conjunct's sort is the conjunction's (`sortIs`, the sorting rule of
  KORE), is `Tight`. The second part the reader checks: `frRead` reads only a right side that is
  `rhsSorted` (`frRead_rhsSorted`), which gives `sortIs` at every such connective
  (`tight_of_rhsSorted`). The first part, `TightSem`, is a fact of the model at the valuation, which
  a model of `Γ` has of the terms of a well-sorted text. With both the reader's alternatives, each with
  its lifted conditions and the top's, hold exactly the elements of p (`rhs_sem`). The lemmas read
  the translation with no alias (`⟨tbl, []⟩`), as `InertEv.vacuous_none` does.

  ## The clauses (`readings_of_fr`)

  Over the variables `vs` of the clauses, the alternatives `xs` (a term and the Bool terms that
  must be `true`) give the clauses `frClauses s vars pats req prio aside (frAltsOf xs)`. Clause k
  has the predicate `preOf s x = ⌈aₖ⌉ ∧ ⋀ⱼ Bⱼ = true`, the last `⋀ₖ ¬preOf s xₖ`. Where its premise
  `prem ∧ pre` (`withPre`) holds at an element of the sort variable's sort, `⌈aₖ⌉` reads as aₖ
  defined (`interp_sCeil`), `Bⱼ = true` as Bⱼ agreeing with `true` on Bool (`EqTrue`), from the
  facts of `NodeFacts` (definedness, the definedness symbols, every numbered sort a sort). These
  readings hold at every valuation of the guards, not only at one that sends the variables to
  values, so they are read from the patterns' meaning and not from `HoldsAt`. That the
  alternatives lie in the result sort follows from `TermsInSort` (`inSort_of_terms`). The
  right side's reading is `rhs_of_reader`: the text's right side holds what the reader's
  alternatives hold, where each of `xs` translates as the kept alternative it is read from.
  `readings_of_fr` takes the equation `frRead` read, the sorts of its right side from the reader
  and `TightSem` of it; `readings_of_rhs` takes the right side's reading itself.

  ## The last clause (`noneEmpty_of_apart`)

  The last clause's right side is `a₁ ∧ (false = true)`; it holds nothing, because `false` and
  `true` are two values of Bool that denote two elements (`NodeFacts.val`, `NodeFacts.apart`).
-/
import KcoreSpec.TieFR
import KcoreSpec.InertEv
import KcoreSpec.ReadFns
import KcoreSpec.HoldsNode
import KcoreSpec.CondCross

set_option autoImplicit false

namespace KCore

namespace TieFRRead

open ML Faithful KoreAML

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-! ## Conditions that a Bool term is `true` -/

/-- Bool's sort, `SortBool{}`. -/
def boolP : KoreAML.P := sym (.sort "SortBool")

/-- `\dv{SortBool{}}("true")`. -/
def trueP : KoreAML.P := sym (.dv "true") ⬝ boolP

/-- The pattern φ agrees with `true` on Bool at e. -/
def EqTrue (I : Interpretation KoreAML.Sym M) (e : Valuation M) (φ : KoreAML.P) : Prop :=
  ∀ y, (inhOf boolP).interpret I e y → (φ.interpret I e y ↔ trueP.interpret I e y)

/-- The Bool term of a condition `hoist` lifts that it be `true`. -/
def scTrue : Parse.SideCond → Option Kore.Pattern
  | .isTrue b => some b
  | .same .. => none

/-- Every condition is one that a Bool term be `true`. -/
def AllTrue (cs : List Parse.SideCond) : Prop := ∀ c ∈ cs, (scTrue c).isSome = true

/-- Each Bool term of the conditions agrees with `true` on Bool at e. -/
def HoldsSC (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) (cs : List Parse.SideCond) :
    Prop :=
  ∀ b ∈ cs.filterMap scTrue, EqTrue I e (tr ⟨tbl, []⟩ b)

theorem holdsSC_nil {tbl : VarTable} {e : Valuation M} : HoldsSC I tbl e [] := by
  intro b hb; simp at hb

theorem holdsSC_append {tbl : VarTable} {e : Valuation M} {cs cs' : List Parse.SideCond} :
    HoldsSC I tbl e (cs ++ cs') ↔ HoldsSC I tbl e cs ∧ HoldsSC I tbl e cs' := by
  unfold HoldsSC
  simp only [List.filterMap_append, List.mem_append]
  exact ⟨fun h => ⟨fun b hb => h b (Or.inl hb), fun b hb => h b (Or.inr hb)⟩,
    fun h b hb => hb.elim (h.1 b) (h.2 b)⟩

theorem holdsSC_one {tbl : VarTable} {e : Valuation M} {b : Kore.Pattern} :
    HoldsSC I tbl e [.isTrue b] ↔ EqTrue I e (tr ⟨tbl, []⟩ b) := by
  unfold HoldsSC; simp [scTrue]

theorem allTrue_append {cs cs' : List Parse.SideCond} : AllTrue (cs ++ cs') ↔ AllTrue cs ∧ AllTrue cs' := by
  unfold AllTrue; simp only [List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-! ## Sorts -/

/-- The elements of q lie in the sort s. -/
def InSortK (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) (s : Kore.KSort)
    (q : Kore.Pattern) : Prop :=
  ∀ a, (tr ⟨tbl, []⟩ q).interpret I e a → (inhOf (trSort tbl s)).interpret I e a

/-- The sort s denotes one sort at e. -/
def SortDen (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) (s : Kore.KSort) : Prop :=
  ∃ τ, IsSort I τ ∧ ∀ a, (trSort tbl s).interpret I e a ↔ a = τ

mutual
  /-- The pattern is of the sort s where it states its sort (`\or`, `\and`, `\equals`), and so are
  the operands of its `\or`s and `\and`s: the sorting rule of KORE at those connectives. -/
  def sortIs (s : Kore.KSort) : Kore.Pattern → Bool
    | .or s' ps => decide (s' = s) && sortIsList s ps
    | .and s' ps => decide (s' = s) && sortIsList s ps
    | .equals _ s' _ _ => decide (s' = s)
    | _ => true
    termination_by structural p => p
  def sortIsList (s : Kore.KSort) : List Kore.Pattern → Bool
    | [] => true
    | p :: ps => sortIs s p && sortIsList s ps
    termination_by structural ps => ps
end

theorem sortIsList_iff {s : Kore.KSort} : ∀ {ps : List Kore.Pattern},
    sortIsList s ps = true ↔ ∀ p ∈ ps, sortIs s p = true
  | [] => by simp [sortIsList]
  | p :: ps => by simp [sortIsList, sortIsList_iff (ps := ps)]

mutual
  /-- The operands of each `\or{s}` and `\and{s}` under applications, conjunctions and
  disjunctions are of the sort s (`sortIs`) and hold elements of s only (`InSortK`), and the sort
  of each `\and` denotes a sort. -/
  def Tight (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) : Kore.Pattern → Prop
    | .app _ _ ps => TightList I tbl e ps
    | .and s ps => SortDen I tbl e s ∧ (∀ q ∈ ps, sortIs s q = true ∧ InSortK I tbl e s q) ∧ TightList I tbl e ps
    | .or s ps => (∀ q ∈ ps, sortIs s q = true ∧ InSortK I tbl e s q) ∧ TightList I tbl e ps
    | _ => True
    termination_by structural p => p
  def TightList (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) : List Kore.Pattern → Prop
    | [] => True
    | p :: ps => Tight I tbl e p ∧ TightList I tbl e ps
    termination_by structural ps => ps
end

theorem tightList_iff {tbl : VarTable} {e : Valuation M} : ∀ {ps : List Kore.Pattern},
    TightList I tbl e ps ↔ ∀ p ∈ ps, Tight I tbl e p
  | [] => by simp [TightList]
  | p :: ps => by simp [TightList, tightList_iff (ps := ps)]

/-! ## The sorts the reader checks (`Parse.rhsSorted`) -/

theorem rhsOpSort_eq_sortIs (s : Kore.KSort) (p : Kore.Pattern) : Parse.rhsOpSort s p = sortIs s p := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => Parse.rhsOpSortList s ps = sortIsList s ps) with
  | or s' ps ih => rw [Parse.rhsOpSort, sortIs, ih]
  | and s' ps ih => rw [Parse.rhsOpSort, sortIs, ih]
  | nil => rw [Parse.rhsOpSortList, sortIsList]
  | cons q qs ih1 ih2 => rw [Parse.rhsOpSortList, sortIsList, ih1, ih2]
  | _ => simp [Parse.rhsOpSort, sortIs]

theorem rhsOpSortList_iff_sortIs {s : Kore.KSort} : ∀ {ps : List Kore.Pattern},
    Parse.rhsOpSortList s ps = true ↔ ∀ p ∈ ps, sortIs s p = true
  | [] => by simp [Parse.rhsOpSortList]
  | p :: ps => by
    simp [Parse.rhsOpSortList, rhsOpSort_eq_sortIs, rhsOpSortList_iff_sortIs (ps := ps)]

theorem rhsSortedList_iff : ∀ {ps : List Kore.Pattern},
    Parse.rhsSortedList ps = true ↔ ∀ p ∈ ps, Parse.rhsSorted p = true
  | [] => by simp [Parse.rhsSortedList]
  | p :: ps => by simp [Parse.rhsSortedList, rhsSortedList_iff (ps := ps)]

mutual
  /-- `Tight` without its sorting part: the operands of each `\or{s}` and `\and{s}` under
  applications, conjunctions and disjunctions hold elements of s only (`InSortK`), and the sort of
  each `\and` denotes a sort. What `Tight` adds, that those operands are of the sort s
  (`sortIs`), the reader checks (`tight_of_rhsSorted`). -/
  def TightSem (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) : Kore.Pattern → Prop
    | .app _ _ ps => TightSemList I tbl e ps
    | .and s ps => SortDen I tbl e s ∧ (∀ q ∈ ps, InSortK I tbl e s q) ∧ TightSemList I tbl e ps
    | .or s ps => (∀ q ∈ ps, InSortK I tbl e s q) ∧ TightSemList I tbl e ps
    | _ => True
    termination_by structural p => p
  def TightSemList (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) : List Kore.Pattern → Prop
    | [] => True
    | p :: ps => TightSem I tbl e p ∧ TightSemList I tbl e ps
    termination_by structural ps => ps
end

theorem tightSemList_iff {tbl : VarTable} {e : Valuation M} : ∀ {ps : List Kore.Pattern},
    TightSemList I tbl e ps ↔ ∀ p ∈ ps, TightSem I tbl e p
  | [] => by simp [TightSemList]
  | p :: ps => by simp [TightSemList, tightSemList_iff (ps := ps)]

/-- **A right side the reader accepts is `Tight` where its operands lie in their sorts.**
`rhsSorted p` gives, at each `\and{s}(ps)` and `\or{s}(ps)` under applications, conjunctions and
disjunctions, `sortIs s q` for every q in ps (`rhsOpSort` has `sortIs`'s clauses,
`rhsOpSort_eq_sortIs`); with `TightSem` that is `Tight`. -/
theorem tight_of_rhsSorted {tbl : VarTable} {e : Valuation M} (p : Kore.Pattern) :
    Parse.rhsSorted p = true → TightSem I tbl e p → Tight I tbl e p := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ p ∈ ps, Parse.rhsSorted p = true → TightSem I tbl e p → Tight I tbl e p) with
  | app h ss ps ih =>
    intro hS hT
    rw [Parse.rhsSorted, rhsSortedList_iff] at hS
    rw [TightSem, tightSemList_iff] at hT
    rw [Tight, tightList_iff]
    exact fun q hq => ih q hq (hS q hq) (hT q hq)
  | and s ps ih =>
    intro hS hT
    rw [Parse.rhsSorted, Bool.and_eq_true, rhsOpSortList_iff_sortIs, rhsSortedList_iff] at hS
    rw [TightSem, tightSemList_iff] at hT
    rw [Tight, tightList_iff]
    exact ⟨hT.1, fun q hq => ⟨hS.1 q hq, hT.2.1 q hq⟩, fun q hq => ih q hq (hS.2 q hq) (hT.2.2 q hq)⟩
  | or s ps ih =>
    intro hS hT
    rw [Parse.rhsSorted, Bool.and_eq_true, rhsOpSortList_iff_sortIs, rhsSortedList_iff] at hS
    rw [TightSem, tightSemList_iff] at hT
    rw [Tight, tightList_iff]
    exact ⟨fun q hq => ⟨hS.1 q hq, hT.1 q hq⟩, fun q hq => ih q hq (hS.2 q hq) (hT.2 q hq)⟩
  | nil => rename_i hq _ _; cases hq
  | cons q qs ih1 ih2 =>
    rename_i x hx hs ht
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih1 hs ht
    · exact ih2 x hx hs ht
  | _ => intro _ _; simp [Tight]

/-! ## The translation of the connectives -/

theorem tr_app (tbl : VarTable) (h : Kore.SymbolIdent) (ss : List Kore.KSort) (ps : List Kore.Pattern) :
    tr ⟨tbl, []⟩ (.app h ss ps) = trArgs ⟨tbl, []⟩ (trSortApp tbl (sym (.symbol h.ident.name)) ss) ps := by
  rw [tr]; simp

/-- An application of `acc` to the arguments `ps`, as sets. -/
theorem trArgs_iff {tbl : VarTable} {e : Valuation M} : ∀ (ps : List Kore.Pattern) (acc : KoreAML.P) (m : M),
    (trArgs ⟨tbl, []⟩ acc ps).interpret I e m ↔
      ∃ a, acc.interpret I e a ∧ ∃ bs, All2 (fun p b => (tr ⟨tbl, []⟩ p).interpret I e b) ps bs ∧ AppE I a bs m
  | [], acc, m => by
    rw [trArgs_nil]
    constructor
    · intro hm; exact ⟨m, hm, [], .nil, rfl⟩
    · rintro ⟨a, ha, bs, hbs, hm⟩
      cases hbs; subst hm; exact ha
  | p :: ps, acc, m => by
    rw [trArgs_cons, trArgs_iff ps _ m]
    constructor
    · rintro ⟨a', ha', bs, hbs, hm⟩
      obtain ⟨a, b, ha, hb, happ⟩ := interp_app.mp ha'
      exact ⟨a, ha, b :: bs, .cons hb hbs, a', happ, hm⟩
    · rintro ⟨a, ha, bs, hbs, hm⟩
      cases hbs with
      | cons hb hbs =>
        obtain ⟨a', happ, hm⟩ := hm
        exact ⟨a', interp_app.mpr ⟨a, _, ha, hb, happ⟩, _, hbs, hm⟩

/-- Arguments that hold the same elements give the same application. -/
theorem trArgs_congr {tbl : VarTable} {e : Valuation M} {ps ps' : List Kore.Pattern}
    (h : All2 (fun p p' => ∀ b, (tr ⟨tbl, []⟩ p).interpret I e b ↔ (tr ⟨tbl, []⟩ p').interpret I e b) ps ps')
    (acc : KoreAML.P) (m : M) :
    (trArgs ⟨tbl, []⟩ acc ps).interpret I e m ↔ (trArgs ⟨tbl, []⟩ acc ps').interpret I e m := by
  have key : ∀ (bs : List M), All2 (fun p b => (tr ⟨tbl, []⟩ p).interpret I e b) ps bs ↔
      All2 (fun p b => (tr ⟨tbl, []⟩ p).interpret I e b) ps' bs := by
    clear acc m
    induction h with
    | nil => intro bs; exact Iff.rfl
    | cons hp _ ih =>
      intro bs
      constructor
      · intro hb; cases hb with | cons h1 h2 => exact .cons ((hp _).mp h1) ((ih _).mp h2)
      · intro hb; cases hb with | cons h1 h2 => exact .cons ((hp _).mpr h1) ((ih _).mpr h2)
  rw [trArgs_iff, trArgs_iff]
  simp only [key]

/-- An application whose head holds the elements of `acc'` where Q holds, and none where it does
not, holds the application of `acc'` where Q holds, and nothing where it does not. -/
theorem trArgs_and {tbl : VarTable} {e : Valuation M} {acc acc' : KoreAML.P} {Q : Prop}
    (h : ∀ a, acc.interpret I e a ↔ acc'.interpret I e a ∧ Q) (ps : List Kore.Pattern) (m : M) :
    (trArgs ⟨tbl, []⟩ acc ps).interpret I e m ↔ (trArgs ⟨tbl, []⟩ acc' ps).interpret I e m ∧ Q := by
  rw [trArgs_iff, trArgs_iff]
  simp only [h]
  constructor
  · rintro ⟨a, ⟨ha, hq⟩, rest⟩; exact ⟨⟨a, ha, rest⟩, hq⟩
  · rintro ⟨⟨a, ha, rest⟩, hq⟩; exact ⟨a, ⟨ha, hq⟩, rest⟩

/-- A disjunction of operands in its sort holds the elements of its operands. -/
theorem trOrList_iff (hD : DefOK I) {tbl : VarTable} {e : Valuation M} {s : Kore.KSort} :
    ∀ {ps : List Kore.Pattern}, (∀ q ∈ ps, InSortK I tbl e s q) → ∀ m,
      (trOrList ⟨tbl, []⟩ (trSort tbl s) ps).interpret I e m ↔ ∃ q ∈ ps, (tr ⟨tbl, []⟩ q).interpret I e m
  | [], _, m => by
    rw [trOrList]
    simp only [List.not_mem_nil, false_and, exists_false, iff_false]
    exact InertEv.sBot_none hD (InertEv.trSort_topFresh tbl s) e m
  | [q], _, m => by rw [trOrList]; simp
  | q :: q' :: qs, hin, m => by
    rw [trOrList]
    rw [interp_sOr, trOrList_iff hD (ps := q' :: qs) (fun x hx => hin x (List.mem_cons_of_mem _ hx)) m]
    constructor
    · rintro ⟨-, h | ⟨x, hx, h⟩⟩
      · exact ⟨q, List.mem_cons_self .., h⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
    · rintro ⟨x, hx, h⟩
      refine ⟨hin x hx m h, ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, h⟩

/-- A conjunction of at least one operand holds the elements all of them hold. -/
theorem trAndList_iff {ctx : Ctx} {s : KoreAML.P} {e : Valuation M} :
    ∀ {ps : List Kore.Pattern}, ps ≠ [] → ∀ m,
      (trAndList ctx s ps).interpret I e m ↔ ∀ q ∈ ps, (tr ctx q).interpret I e m
  | [], h, _ => (h rfl).elim
  | [q], _, m => by rw [trAndList]; simp
  | q :: q' :: qs, _, m => by
    rw [trAndList]
    rw [interp_sAnd, trAndList_iff (ps := q' :: qs) (List.cons_ne_nil _ _) m]
    simp


/-! ## Lists of operands -/

theorem all2_map {α β : Type} {R : β → α → Prop} {f : α → β} :
    ∀ {ps : List α}, (∀ p ∈ ps, R (f p) p) → All2 R (ps.map f) ps
  | [], _ => .nil
  | p :: ps, h => .cons (h p (List.mem_cons_self ..)) (all2_map fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem all2_mem {α β : Type} {R : α → β → Prop} : ∀ {ps : List α} {qs : List β}, All2 R ps qs →
    ∀ x ∈ qs, ∃ p ∈ ps, R p x
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons h hs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self .., h⟩
    · obtain ⟨p, hp, hr⟩ := all2_mem hs x hx
      exact ⟨p, List.mem_cons_of_mem _ hp, hr⟩

/-- Operands that hold the same elements give the same conjunction. -/
theorem trAndList_congr {ctx : Ctx} {s : KoreAML.P} {e : Valuation M} {ps ps' : List Kore.Pattern}
    (h : All2 (fun p p' => ∀ b, (tr ctx p).interpret I e b ↔ (tr ctx p').interpret I e b) ps ps') (m : M) :
    (trAndList ctx s ps).interpret I e m ↔ (trAndList ctx s ps').interpret I e m := by
  induction h with
  | nil => exact Iff.rfl
  | cons hp hs ih =>
    rename_i p p' qs qs'
    cases hs with
    | nil => rw [trAndList, trAndList]; exact hp m
    | cons _ _ =>
      rw [trAndList, trAndList]
      rw [interp_sAnd, interp_sAnd, hp m, ih]

theorem dropList_eq : ∀ ps, Parse.dropEmptyAltsList ps = ps.map Parse.dropEmptyAlts
  | [] => by rw [Parse.dropEmptyAltsList]; rfl
  | p :: ps => by rw [Parse.dropEmptyAltsList, dropList_eq ps]; rfl

theorem orAltsList_nil : Parse.orAltsList [] = [[]] := by rw [Parse.orAltsList]

theorem mem_orAltsList_cons {p : Kore.Pattern} {ps : List Kore.Pattern} {qs : List Kore.Pattern} :
    qs ∈ Parse.orAltsList (p :: ps) ↔ ∃ q ∈ Parse.orAlts p, ∃ qs' ∈ Parse.orAltsList ps, qs = q :: qs' := by
  rw [Parse.orAltsList]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨q, hq, qs', hqs', rfl⟩; exact ⟨q, hq, qs', hqs', rfl⟩
  · rintro ⟨q, hq, qs', hqs', rfl⟩; exact ⟨q, hq, qs', hqs', rfl⟩

/-- A choice of an alternative of each operand. -/
theorem all2_of_mem_orAltsList : ∀ {ps qs : List Kore.Pattern}, qs ∈ Parse.orAltsList ps →
    All2 (fun p q => q ∈ Parse.orAlts p) ps qs
  | [], qs, h => by rw [orAltsList_nil] at h; rw [List.mem_singleton.mp h]; exact .nil
  | p :: ps, qs, h => by
    obtain ⟨q, hq, qs', hqs', rfl⟩ := mem_orAltsList_cons.mp h
    exact .cons hq (all2_of_mem_orAltsList hqs')

theorem mem_orAltsOr {q : Kore.Pattern} : ∀ {ps : List Kore.Pattern},
    q ∈ Parse.orAltsOr ps ↔ ∃ p ∈ ps, q ∈ Parse.orAlts p
  | [] => by rw [Parse.orAltsOr]; simp
  | p :: ps => by
    rw [Parse.orAltsOr, List.mem_append, mem_orAltsOr (ps := ps)]
    simp

/-- Each operand holds where one of its alternatives does: all do where a choice of alternatives
does. -/
theorem forall_orAlts {X : Kore.Pattern → Prop} : ∀ {ps : List Kore.Pattern},
    (∀ p ∈ ps, X p ↔ ∃ q ∈ Parse.orAlts p, X q) →
    ((∀ p ∈ ps, X p) ↔ ∃ qs ∈ Parse.orAltsList ps, ∀ q ∈ qs, X q)
  | [], _ => by rw [orAltsList_nil]; simp
  | p :: ps, h => by
    have ih := forall_orAlts (ps := ps) (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.mem_cons, forall_eq_or_imp, mem_orAltsList_cons]
    rw [ih, h p (List.mem_cons_self ..)]
    constructor
    · rintro ⟨⟨q, hq, hx⟩, qs', hqs', hall⟩
      exact ⟨q :: qs', ⟨q, hq, qs', hqs', rfl⟩, by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hx, hall⟩⟩
    · rintro ⟨_, ⟨q, hq, qs', hqs', rfl⟩, hall⟩
      simp only [List.mem_cons, forall_eq_or_imp] at hall
      exact ⟨⟨q, hq, hall.1⟩, qs', hqs', hall.2⟩

/-- The same, pairing each operand with an element. -/
theorem all2_orAlts {X : Kore.Pattern → M → Prop} : ∀ {ps : List Kore.Pattern},
    (∀ p ∈ ps, ∀ b, X p b ↔ ∃ q ∈ Parse.orAlts p, X q b) → ∀ bs,
    (All2 X ps bs ↔ ∃ qs ∈ Parse.orAltsList ps, All2 X qs bs)
  | [], _, bs => by
    rw [orAltsList_nil]
    simp only [List.mem_singleton, exists_eq_left]
  | p :: ps, h, bs => by
    have ih := all2_orAlts (ps := ps) (fun q hq => h q (List.mem_cons_of_mem _ hq))
    constructor
    · intro hb
      cases hb with
      | cons h1 h2 =>
        obtain ⟨q, hq, hx⟩ := (h p (List.mem_cons_self ..) _).mp h1
        obtain ⟨qs', hqs', h2'⟩ := (ih _).mp h2
        exact ⟨q :: qs', mem_orAltsList_cons.mpr ⟨q, hq, qs', hqs', rfl⟩, .cons hx h2'⟩
    · rintro ⟨qs, hqs, hb⟩
      obtain ⟨q, hq, qs', hqs', rfl⟩ := mem_orAltsList_cons.mp hqs
      cases hb with
      | cons h1 h2 =>
        exact .cons ((h p (List.mem_cons_self ..) _).mpr ⟨q, hq, h1⟩) ((ih _).mpr ⟨qs', hqs', h2⟩)

theorem length_of_mem_orAltsList : ∀ {ps qs : List Kore.Pattern}, qs ∈ Parse.orAltsList ps → qs.length = ps.length :=
  fun h => (all2_of_mem_orAltsList h).length.symm

/-! ## Sorts kept by the normalisation -/

theorem sortIs_drop (s : Kore.KSort) (p : Kore.Pattern) :
    sortIs s p = true → sortIs s (Parse.dropEmptyAlts p) = true := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, sortIs s q = true → sortIs s (Parse.dropEmptyAlts q) = true) with
  | and s' ps ih =>
    intro h
    rw [Parse.dropEmptyAlts, dropList_eq]
    simp only [sortIs, Bool.and_eq_true, decide_eq_true_eq, sortIsList_iff, List.mem_map] at h ⊢
    exact ⟨h.1, by rintro _ ⟨q, hq, rfl⟩; exact ih q hq (h.2 q hq)⟩
  | or s' ps ih =>
    intro h
    simp only [sortIs, Bool.and_eq_true, decide_eq_true_eq, sortIsList_iff] at h
    rw [Parse.dropEmptyAlts, dropList_eq]
    have hsub : ∀ q ∈ (ps.map Parse.dropEmptyAlts).filter (fun x => !Parse.vacuous x), sortIs s q = true := by
      intro q hq
      obtain ⟨hq, -⟩ := List.mem_filter.mp hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      exact ih q0 hq0 (h.2 q0 hq0)
    generalize (ps.map Parse.dropEmptyAlts).filter (fun x => !Parse.vacuous x) = F at hsub ⊢
    rcases F with _ | ⟨p, _ | ⟨p2, rest⟩⟩
    · rfl
    · exact hsub p (List.mem_singleton_self _)
    · simp only [sortIs, Bool.and_eq_true, decide_eq_true_eq, sortIsList_iff]
      exact ⟨h.1, hsub⟩
  | nil => rename_i hq _; cases hq
  | cons q qs ih1 ih2 =>
    rename_i x hx hs
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih1 hs
    · exact ih2 x hx hs
  | _ => intro h; exact h

theorem sortIs_orAlts (s : Kore.KSort) (p : Kore.Pattern) :
    sortIs s p = true → ∀ q ∈ Parse.orAlts p, sortIs s q = true := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ p ∈ ps, sortIs s p = true → ∀ q ∈ Parse.orAlts p, sortIs s q = true) with
  | app _ _ _ _ =>
    intro _ q hq
    rw [Parse.orAlts] at hq
    obtain ⟨qs, -, rfl⟩ := List.mem_map.mp hq
    rfl
  | and s' ps ih =>
    intro h q hq
    simp only [sortIs, Bool.and_eq_true, decide_eq_true_eq, sortIsList_iff] at h
    rw [Parse.orAlts] at hq
    obtain ⟨qs, hqs, rfl⟩ := List.mem_map.mp hq
    simp only [sortIs, Bool.and_eq_true, decide_eq_true_eq, sortIsList_iff]
    refine ⟨h.1, fun x hx => ?_⟩
    obtain ⟨p0, hp0, hx0⟩ := all2_mem (all2_of_mem_orAltsList hqs) x hx
    exact ih p0 hp0 (h.2 p0 hp0) x hx0
  | or s' ps ih =>
    intro h q hq
    simp only [sortIs, Bool.and_eq_true, decide_eq_true_eq, sortIsList_iff] at h
    rw [Parse.orAlts, mem_orAltsOr] at hq
    obtain ⟨p0, hp0, hq⟩ := hq
    exact ih p0 hp0 (h.2 p0 hp0) q hq
  | nil => rename_i hq _ _ _; cases hq
  | cons q qs ih1 ih2 =>
    rename_i x hx hs y hy
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih1 hs y hy
    · exact ih2 x hx hs y hy
  | _ => intro h q hq; rw [List.mem_singleton.mp hq]; exact h

/-! ## Leaving out the empty alternatives -/

section
variable (hD : DefOK I) {tbl : VarTable} {e : Valuation M}
include hD

theorem tr_bottom_iff (s : Kore.KSort) (a : M) : (tr ⟨tbl, []⟩ (.bottom s)).interpret I e a ↔ False := by
  rw [tr]; exact iff_false_intro (InertEv.sBot_none hD (InertEv.trSort_topFresh tbl s) e a)

omit hD in
theorem tr_or (s : Kore.KSort) (ps : List Kore.Pattern) :
    tr ⟨tbl, []⟩ (.or s ps) = trOrList ⟨tbl, []⟩ (trSort tbl s) ps := by rw [tr]

omit hD in
theorem tr_and (s : Kore.KSort) (ps : List Kore.Pattern) :
    tr ⟨tbl, []⟩ (.and s ps) = trAndList ⟨tbl, []⟩ (trSort tbl s) ps := by rw [tr]

/-- **`dropEmptyAlts` keeps the elements of a `Tight` pattern**, and its result is `Tight`. -/
theorem drop_sem (p : Kore.Pattern) : Tight I tbl e p →
    Tight I tbl e (Parse.dropEmptyAlts p) ∧
      ∀ a, (tr ⟨tbl, []⟩ (Parse.dropEmptyAlts p)).interpret I e a ↔ (tr ⟨tbl, []⟩ p).interpret I e a := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ p ∈ ps, Tight I tbl e p → Tight I tbl e (Parse.dropEmptyAlts p) ∧
      ∀ a, (tr ⟨tbl, []⟩ (Parse.dropEmptyAlts p)).interpret I e a ↔ (tr ⟨tbl, []⟩ p).interpret I e a) with
  | app h ss ps ih =>
    intro hT
    simp only [Tight, tightList_iff] at hT
    rw [Parse.dropEmptyAlts, dropList_eq]
    refine ⟨?_, fun a => ?_⟩
    · simp only [Tight, tightList_iff, List.mem_map]
      rintro _ ⟨q, hq, rfl⟩; exact (ih q hq (hT q hq)).1
    · rw [tr_app, tr_app]
      exact trArgs_congr (all2_map fun q hq => (ih q hq (hT q hq)).2) _ a
  | and s' ps ih =>
    intro hT
    simp only [Tight, tightList_iff] at hT
    obtain ⟨hden, hin, hT⟩ := hT
    rw [Parse.dropEmptyAlts, dropList_eq]
    refine ⟨?_, fun a => ?_⟩
    · simp only [Tight, tightList_iff, List.mem_map]
      refine ⟨hden, ?_, ?_⟩
      · rintro _ ⟨q, hq, rfl⟩
        exact ⟨sortIs_drop s' q (hin q hq).1, fun b hb => (hin q hq).2 b (((ih q hq (hT q hq)).2 b).mp hb)⟩
      · rintro _ ⟨q, hq, rfl⟩; exact (ih q hq (hT q hq)).1
    · rw [tr_and, tr_and]
      exact trAndList_congr (all2_map fun q hq => (ih q hq (hT q hq)).2) a
  | or s' ps ih =>
    intro hT
    simp only [Tight, tightList_iff] at hT
    obtain ⟨hin, hT⟩ := hT
    rw [Parse.dropEmptyAlts, dropList_eq]
    have hF : ∀ q ∈ (ps.map Parse.dropEmptyAlts).filter (fun x => !Parse.vacuous x),
        sortIs s' q = true ∧ InSortK I tbl e s' q ∧ Tight I tbl e q := by
      intro q hq
      obtain ⟨hq, -⟩ := List.mem_filter.mp hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      exact ⟨sortIs_drop s' q0 (hin q0 hq0).1,
        fun b hb => (hin q0 hq0).2 b (((ih q0 hq0 (hT q0 hq0)).2 b).mp hb), (ih q0 hq0 (hT q0 hq0)).1⟩
    have hE : ∀ a, (∃ q ∈ (ps.map Parse.dropEmptyAlts).filter (fun x => !Parse.vacuous x),
        (tr ⟨tbl, []⟩ q).interpret I e a) ↔ (tr ⟨tbl, []⟩ (.or s' ps)).interpret I e a := by
      intro a
      rw [tr_or, trOrList_iff hD (fun q hq => (hin q hq).2)]
      constructor
      · rintro ⟨q, hq, ha⟩
        obtain ⟨hq, -⟩ := List.mem_filter.mp hq
        obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
        exact ⟨q0, hq0, ((ih q0 hq0 (hT q0 hq0)).2 a).mp ha⟩
      · rintro ⟨q0, hq0, ha⟩
        have ha' := ((ih q0 hq0 (hT q0 hq0)).2 a).mpr ha
        refine ⟨Parse.dropEmptyAlts q0, List.mem_filter.mpr ⟨List.mem_map_of_mem hq0, ?_⟩, ha'⟩
        cases hv : Parse.vacuous (Parse.dropEmptyAlts q0)
        · rfl
        · exact (InertEv.vacuous_none hD tbl _ hv e a ha').elim
    generalize (ps.map Parse.dropEmptyAlts).filter (fun x => !Parse.vacuous x) = F at hF hE ⊢
    rcases F with _ | ⟨q, _ | ⟨q2, rest⟩⟩
    · refine ⟨trivial, fun a => ?_⟩
      rw [← hE a]
      simp only [List.not_mem_nil, false_and, exists_false, iff_false]
      rw [tr]
      exact InertEv.sBot_none hD (InertEv.trSort_topFresh tbl s') e a
    · refine ⟨(hF q (List.mem_singleton_self _)).2.2, fun a => ?_⟩
      rw [← hE a]
      simp
    · refine ⟨?_, fun a => ?_⟩
      · simp only [Tight, tightList_iff]
        exact ⟨fun x hx => ⟨(hF x hx).1, (hF x hx).2.1⟩, fun x hx => (hF x hx).2.2⟩
      · rw [← hE a, tr_or, trOrList_iff hD (fun x hx => (hF x hx).2.1)]
  | nil => rename_i hq _; cases hq
  | cons q qs ih1 ih2 =>
    rename_i x hx hs
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih1 hs
    · exact ih2 x hx hs
  | _ => intro hT; exact ⟨hT, fun _ => Iff.rfl⟩

/-! ## Distributing `\or` -/

/-- **`orAlts` keeps the elements of a `Tight` pattern**: they are those of its alternatives, each
of which is `Tight`. -/
theorem orAlts_sem (p : Kore.Pattern) : Tight I tbl e p →
    (∀ a, (tr ⟨tbl, []⟩ p).interpret I e a ↔ ∃ q ∈ Parse.orAlts p, (tr ⟨tbl, []⟩ q).interpret I e a) ∧
      ∀ q ∈ Parse.orAlts p, Tight I tbl e q := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ p ∈ ps, Tight I tbl e p →
      (∀ a, (tr ⟨tbl, []⟩ p).interpret I e a ↔ ∃ q ∈ Parse.orAlts p, (tr ⟨tbl, []⟩ q).interpret I e a) ∧
      ∀ q ∈ Parse.orAlts p, Tight I tbl e q) with
  | app h ss ps ih =>
    intro hT
    simp only [Tight, tightList_iff] at hT
    rw [Parse.orAlts]
    refine ⟨fun a => ?_, ?_⟩
    · rw [tr_app, trArgs_iff]
      simp only [List.mem_map]
      constructor
      · rintro ⟨a0, ha0, bs, hbs, happ⟩
        obtain ⟨qs, hqs, hbs'⟩ := (all2_orAlts (fun q hq => (ih q hq (hT q hq)).1) bs).mp hbs
        exact ⟨_, ⟨qs, hqs, rfl⟩, by rw [tr_app, trArgs_iff]; exact ⟨a0, ha0, bs, hbs', happ⟩⟩
      · rintro ⟨_, ⟨qs, hqs, rfl⟩, hq⟩
        rw [tr_app, trArgs_iff] at hq
        obtain ⟨a0, ha0, bs, hbs, happ⟩ := hq
        exact ⟨a0, ha0, bs, (all2_orAlts (fun q hq => (ih q hq (hT q hq)).1) bs).mpr ⟨qs, hqs, hbs⟩, happ⟩
    · simp only [List.mem_map]
      rintro _ ⟨qs, hqs, rfl⟩
      simp only [Tight, tightList_iff]
      intro x hx
      obtain ⟨p0, hp0, hx0⟩ := all2_mem (all2_of_mem_orAltsList hqs) x hx
      exact (ih p0 hp0 (hT p0 hp0)).2 x hx0
  | and s' ps ih =>
    intro hT
    have hT0 := hT
    simp only [Tight, tightList_iff] at hT
    obtain ⟨hden, hin, hT⟩ := hT
    rw [Parse.orAlts]
    rcases ps with _ | ⟨p0, ps0⟩
    · rw [orAltsList_nil]
      refine ⟨fun a => by simp, fun q hq => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
      subst hq
      exact hT0
    · have hsem : ∀ q ∈ p0 :: ps0, ∀ a, (tr ⟨tbl, []⟩ q).interpret I e a ↔
          ∃ x ∈ Parse.orAlts q, (tr ⟨tbl, []⟩ x).interpret I e a := fun q hq => (ih q hq (hT q hq)).1
      refine ⟨fun a => ?_, ?_⟩
      · rw [tr_and, trAndList_iff (List.cons_ne_nil _ _),
          forall_orAlts (X := fun q => (tr ⟨tbl, []⟩ q).interpret I e a) (fun q hq => hsem q hq a)]
        simp only [List.mem_map]
        constructor
        · rintro ⟨qs, hqs, hall⟩
          refine ⟨_, ⟨qs, hqs, rfl⟩, ?_⟩
          rw [tr_and, trAndList_iff (by
            intro h0; have := length_of_mem_orAltsList hqs; rw [h0] at this; cases this)]
          exact hall
        · rintro ⟨_, ⟨qs, hqs, rfl⟩, hq⟩
          rw [tr_and, trAndList_iff (by
            intro h0; have := length_of_mem_orAltsList hqs; rw [h0] at this; cases this)] at hq
          exact ⟨qs, hqs, hq⟩
      · simp only [List.mem_map]
        rintro _ ⟨qs, hqs, rfl⟩
        simp only [Tight, tightList_iff]
        have key : ∀ x ∈ qs, sortIs s' x = true ∧ InSortK I tbl e s' x ∧ Tight I tbl e x := by
          intro x hx
          obtain ⟨y0, hy0, hpq⟩ := all2_mem (all2_of_mem_orAltsList hqs) x hx
          exact ⟨sortIs_orAlts s' y0 (hin y0 hy0).1 _ hpq,
            fun b hb => (hin y0 hy0).2 b ((hsem y0 hy0 b).mpr ⟨_, hpq, hb⟩),
            (ih y0 hy0 (hT y0 hy0)).2 _ hpq⟩
        exact ⟨hden, fun x hx => ⟨(key x hx).1, (key x hx).2.1⟩, fun x hx => (key x hx).2.2⟩
  | or s' ps ih =>
    intro hT
    simp only [Tight, tightList_iff] at hT
    obtain ⟨hin, hT⟩ := hT
    rw [Parse.orAlts]
    refine ⟨fun a => ?_, fun q hq => ?_⟩
    · rw [tr_or, trOrList_iff hD (fun q hq => (hin q hq).2)]
      constructor
      · rintro ⟨q0, hq0, ha⟩
        obtain ⟨x, hx, hxa⟩ := ((ih q0 hq0 (hT q0 hq0)).1 a).mp ha
        exact ⟨x, mem_orAltsOr.mpr ⟨q0, hq0, hx⟩, hxa⟩
      · rintro ⟨x, hx, hxa⟩
        obtain ⟨q0, hq0, hx⟩ := mem_orAltsOr.mp hx
        exact ⟨q0, hq0, ((ih q0 hq0 (hT q0 hq0)).1 a).mpr ⟨x, hx, hxa⟩⟩
    · obtain ⟨q0, hq0, hx⟩ := mem_orAltsOr.mp hq
      exact (ih q0 hq0 (hT q0 hq0)).2 q hx
  | nil => rename_i hq _; cases hq
  | cons q qs ih1 ih2 =>
    rename_i x hx hs
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih1 hs
    · exact ih2 x hx hs
  | _ =>
    intro hT
    refine ⟨fun a => ?_, fun q hq => ?_⟩
    · exact ⟨fun h => ⟨_, List.mem_singleton_self _, h⟩, fun ⟨q, hq, h⟩ => by rw [List.mem_singleton.mp hq] at h; exact h⟩
    · rw [List.mem_singleton.mp hq]; exact hT

end


/-! ## Lifting the conditions -/

theorem dropPrefix_sortBool {n : String} (h : KoreAML.Parse.dropPrefix? "Sort" n = some "Bool") : n = "SortBool" := by
  unfold KoreAML.Parse.dropPrefix? at h
  simp only at h
  split at h
  · rename_i h1
    have h2 : n.toList.drop 4 = "Bool".toList := by
      have := congrArg String.toList (Option.some.inj h)
      simpa using this
    have h1' : n.toList.take 4 = "Sort".toList := by simpa using h1
    have : n.toList = "SortBool".toList := by
      rw [← List.take_append_drop 4 n.toList, h1', h2]; rfl
    exact String.toList_inj.mp this
  · cases h

/-- A sort named `Bool` translates as `SortBool{}`. -/
theorem trSort_bool {tbl : VarTable} {bs : Kore.KSort} (h : KoreAML.Parse.sortName? bs = some "Bool") :
    trSort tbl bs = boolP := by
  cases bs with
  | var a => simp [KoreAML.Parse.sortName?] at h
  | ctor C args =>
    cases args with
    | nil =>
      have hn := dropPrefix_sortBool (by simpa [KoreAML.Parse.sortName?] using h)
      rw [trSort, trSortApp, hn]; rfl
    | cons _ _ => simp [KoreAML.Parse.sortName?] at h

/-- The conjuncts `hoist` lifts: `\equals{Bool,s}(b, \dv{Bool}("true"))`. -/
theorem isTrueOf_spec {u b : Kore.Pattern} (h : Parse.isTrueOf? u = some b) :
    ∃ bs s' bs', u = .equals bs s' b (.dv bs' "true") ∧ KoreAML.Parse.sortName? bs = some "Bool" ∧
      KoreAML.Parse.sortName? bs' = some "Bool" := by
  unfold Parse.isTrueOf? at h
  split at h
  next bs s' b0 bs' =>
    by_cases hc : (KoreAML.Parse.sortName? bs == some "Bool" && KoreAML.Parse.sortName? bs' == some "Bool") = true
    · simp only [hc, ↓reduceIte] at h
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨bs, s', bs', rfl, hc.1, hc.2⟩
    · simp only [hc] at h; cases h
  next => cases h

/-- Bool denotes one sort. -/
def BoolDen (I : Interpretation KoreAML.Sym M) : Prop :=
  ∃ β, IsSort I β ∧ ∀ (e : Valuation M) a, boolP.interpret I e a ↔ a = β

section
variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hB : BoolDen I) {tbl : VarTable} {e : Valuation M}
include hD hc hB

/-- **A lifted conjunct** `\equals{Bool,s}(b, true)` holds all of s where b agrees with `true` on
Bool, and nothing elsewhere. -/
theorem tr_isTrue_iff {bs s' bs' : Kore.KSort} {b : Kore.Pattern} (h1 : KoreAML.Parse.sortName? bs = some "Bool")
    (h2 : KoreAML.Parse.sortName? bs' = some "Bool") (hs : SortDen I tbl e s') (a : M) :
    (tr ⟨tbl, []⟩ (.equals bs s' b (.dv bs' "true"))).interpret I e a ↔
      (inhOf (trSort tbl s')).interpret I e a ∧ EqTrue I e (tr ⟨tbl, []⟩ b) := by
  obtain ⟨β, hβ, hβd⟩ := hB
  obtain ⟨τ, hτ, hτd⟩ := hs
  have hT : tr ⟨tbl, []⟩ (.equals bs s' b (.dv bs' "true")) = sEquals boolP (trSort tbl s') (tr ⟨tbl, []⟩ b) trueP := by
    rw [tr, trSort_bool h1]
    congr 1
    rw [tr, trSort_bool h2]; rfl
  rw [hT, interp_sEquals hD hc (hβd e) hτd hβ hτ, interp_inhOf_of hτd]
  unfold EqTrue
  simp only [interp_inhOf_of (hβd e)]

end

/-- What `hoist` keeps of p: where p is `Tight` and every lifted condition is that a Bool term be
`true`, the side is `Tight` and holds, with the conditions, the elements of p. -/
def HoistOK (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M) (p : Kore.Pattern) : Prop :=
  ∀ r cs emp, Tight I tbl e p → Parse.hoist p = (r, cs, emp) → AllTrue cs →
    Tight I tbl e r ∧ ∀ a, (tr ⟨tbl, []⟩ p).interpret I e a ↔ (tr ⟨tbl, []⟩ r).interpret I e a ∧ HoldsSC I tbl e cs

theorem hoistList_ok {tbl : VarTable} {e : Valuation M} : ∀ {ps : List Kore.Pattern}, (∀ p ∈ ps, HoistOK I tbl e p) →
    ∀ {ps' cs emp}, TightList I tbl e ps → Parse.hoistList ps = (ps', cs, emp) → AllTrue cs →
      TightList I tbl e ps' ∧ ∀ acc a, (trArgs ⟨tbl, []⟩ acc ps).interpret I e a ↔
        (trArgs ⟨tbl, []⟩ acc ps').interpret I e a ∧ HoldsSC I tbl e cs
  | [], _, ps', cs, emp, _, hh, _ => by
    rw [Parse.hoistList] at hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    exact ⟨trivial, fun acc a => by simp [holdsSC_nil]⟩
  | p :: ps, hok, ps', cs, emp, hT, hh, hall => by
    rw [Parse.hoistList] at hh
    dsimp only at hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    rw [allTrue_append] at hall
    simp only [TightList] at hT
    obtain ⟨o1T, o1⟩ := hok p (List.mem_cons_self ..) _ _ _ hT.1 rfl hall.1
    obtain ⟨o2T, o2⟩ := hoistList_ok (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hT.2 rfl hall.2
    refine ⟨⟨o1T, o2T⟩, fun acc a => ?_⟩
    rw [trArgs_cons, trArgs_cons, o2, holdsSC_append]
    have hacc : ∀ x, (acc ⬝ tr ⟨tbl, []⟩ p).interpret I e x ↔
        (acc ⬝ tr ⟨tbl, []⟩ (Parse.hoist p).1).interpret I e x ∧ HoldsSC I tbl e (Parse.hoist p).2.1 := by
      intro x
      simp only [interp_app, o1]
      constructor
      · rintro ⟨a0, b, ha0, ⟨hb, hq⟩, happ⟩; exact ⟨⟨a0, b, ha0, hb, happ⟩, hq⟩
      · rintro ⟨⟨a0, b, ha0, hb, happ⟩, hq⟩; exact ⟨a0, b, ha0, ⟨hb, hq⟩, happ⟩
    rw [trArgs_and hacc]
    exact and_assoc

theorem trivOK {tbl : VarTable} {e : Valuation M} {p r : Kore.Pattern} {cs : List Parse.SideCond} {emp : Bool}
    (hT : Tight I tbl e p) (hh : (p, [], false) = (r, cs, emp)) :
    Tight I tbl e r ∧ ∀ a, (tr ⟨tbl, []⟩ p).interpret I e a ↔ (tr ⟨tbl, []⟩ r).interpret I e a ∧ HoldsSC I tbl e cs := by
  simp only [Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl, rfl⟩ := hh
  exact ⟨hT, fun a => by simp [holdsSC_nil]⟩

section
variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hB : BoolDen I) {tbl : VarTable} {e : Valuation M}
include hD hc hB

/-- **`hoist` keeps the elements of a `Tight` pattern** (`HoistOK`). -/
theorem hoist_ok (p : Kore.Pattern) : HoistOK I tbl e p := by
  induction p using Kore.Pattern.rec (motive_2 := fun ps => ∀ p ∈ ps, HoistOK I tbl e p) with
  | bottom s =>
    intro r cs emp hT hh _
    rw [Parse.hoist.eq_def] at hh
    dsimp only at hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    exact ⟨trivial, fun a => by simp [holdsSC_nil]⟩
  | app h ss ps ih =>
    intro r cs emp hT hh hall
    rw [Parse.hoist.eq_def] at hh
    dsimp only at hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    simp only [Tight] at hT
    obtain ⟨oT, o⟩ := hoistList_ok ih hT rfl hall
    exact ⟨oT, fun a => by rw [tr_app, tr_app]; exact o _ a⟩
  | or s' ps ih =>
    intro r cs emp hT hh hall
    rcases ps with _ | ⟨t, _ | ⟨u, _ | ⟨v, rest⟩⟩⟩
    · exact trivOK hT hh
    · exact trivOK hT hh
    · have hT0 := hT
      simp only [Tight, tightList_iff] at hT
      obtain ⟨hin, hT⟩ := hT
      rw [Parse.hoist.eq_def] at hh
      dsimp only at hh
      split at hh
      · obtain ⟨oT, o⟩ := ih _ (List.mem_cons_self ..) r cs emp (hT _ (List.mem_cons_self ..)) hh hall
        refine ⟨oT, fun a => ?_⟩
        rw [tr_or, trOrList_iff hD (fun q hq => (hin q hq).2), ← o a]
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
          tr_bottom_iff hD]
      · obtain ⟨oT, o⟩ := ih _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) r cs emp
          (hT _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hh hall
        refine ⟨oT, fun a => ?_⟩
        rw [tr_or, trOrList_iff hD (fun q hq => (hin q hq).2), ← o a]
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
          tr_bottom_iff hD, false_or]
      · exact trivOK hT0 hh
    · exact trivOK hT hh
  | and s' ps ih =>
    intro r cs emp hT hh hall
    rcases ps with _ | ⟨t, _ | ⟨u, _ | ⟨v, rest⟩⟩⟩
    · exact trivOK hT hh
    · exact trivOK hT hh
    · simp only [Tight, tightList_iff] at hT
      obtain ⟨hden, hin, hT⟩ := hT
      rw [Parse.hoist.eq_def] at hh
      dsimp only at hh
      split at hh
      · rename_i heq
        simp only [Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl, rfl⟩ := hh
        rw [allTrue_append] at hall
        obtain ⟨bs, s'', bs', rfl, h1, h2⟩ := isTrueOf_spec heq
        have hs : s'' = s' := by
          have := (hin _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1
          simpa [sortIs] using this
        subst hs
        obtain ⟨oT, o⟩ := ih t (List.mem_cons_self ..) _ _ _ (hT t (List.mem_cons_self ..)) rfl hall.1
        refine ⟨oT, fun a => ?_⟩
        have hin' := (hin t (List.mem_cons_self ..)).2 a
        rw [o] at hin'
        rw [tr_and, trAndList, trAndList, interp_sAnd, tr_isTrue_iff hD hc hB h1 h2 hden, o, holdsSC_append,
          holdsSC_one]
        constructor
        · rintro ⟨⟨h1, h2⟩, -, h3⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, hin' ⟨h1, h2⟩, h3⟩
      · rename_i u0 _ _ _ b0 heq heq'
        simp only [Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl, rfl⟩ := hh
        rw [allTrue_append] at hall
        obtain ⟨bs, s'', bs', rfl, h1, h2⟩ := isTrueOf_spec heq
        have hs : s'' = s' := by
          have := (hin _ (List.mem_cons_self ..)).1
          simpa [sortIs] using this
        subst hs
        have hmu : u0 ∈ [Kore.Pattern.equals bs s'' b0 (.dv bs' "true"), u0] :=
          List.mem_cons_of_mem _ (List.mem_cons_self ..)
        obtain ⟨oT, o⟩ := ih u0 hmu _ _ _ (hT u0 hmu) rfl hall.1
        refine ⟨oT, fun a => ?_⟩
        have hin' := (hin u0 hmu).2 a
        rw [o] at hin'
        rw [tr_and, trAndList, trAndList, interp_sAnd, tr_isTrue_iff hD hc hB h1 h2 hden, o, holdsSC_append,
          holdsSC_one]
        constructor
        · rintro ⟨⟨-, h3⟩, h1, h2⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨hin' ⟨h1, h2⟩, h3⟩, h1, h2⟩
      · simp only [Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl, rfl⟩ := hh
        have := hall _ (List.mem_append_right _ (List.mem_singleton_self _))
        simp [scTrue] at this
    · exact trivOK hT hh
  | nil => exact absurd ‹_ ∈ ([] : List Kore.Pattern)› List.not_mem_nil
  | cons q qs ih1 ih2 =>
    rename_i x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih1
    · exact ih2 x hx
  | _ => intro r cs emp hT hh _; exact trivOK hT hh

end

/-- **What `hoist` finds empty holds nothing.** -/
theorem hoist_empty (hD : DefOK I) {tbl : VarTable} {e : Valuation M} (p : Kore.Pattern) :
    (Parse.hoist p).2.2 = true → ∀ a, ¬ (tr ⟨tbl, []⟩ p).interpret I e a := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ p ∈ ps, (Parse.hoist p).2.2 = true → ∀ a, ¬ (tr ⟨tbl, []⟩ p).interpret I e a) with
  | bottom s =>
    intro _ a; rw [tr]; exact InertEv.sBot_none hD (InertEv.trSort_topFresh tbl s) e a
  | app h ss ps ih =>
    intro hh a
    rw [Parse.hoist.eq_def] at hh
    dsimp only at hh
    rw [tr_app]
    revert hh
    generalize trSortApp tbl (sym (.symbol h.ident.name)) ss = acc
    clear h ss
    induction ps generalizing acc with
    | nil => intro hh; rw [Parse.hoistList] at hh; cases hh
    | cons q qs ihl =>
      intro hh
      rw [Parse.hoistList] at hh
      dsimp only at hh
      rw [trArgs_cons]
      rcases Bool.or_eq_true _ _ ▸ hh with hq | hq
      · exact Faithful.trArgs_empty (fun m hm => by
          obtain ⟨_, b, _, hb, _⟩ := interp_app.mp hm
          exact ih q (List.mem_cons_self ..) hq b hb) qs a
      · exact ihl (fun y hy => ih y (List.mem_cons_of_mem _ hy)) _ hq
  | or s' ps ih =>
    intro hh a
    rcases ps with _ | ⟨t, _ | ⟨u, _ | ⟨v, rest⟩⟩⟩
    · cases hh
    · cases hh
    · rw [Parse.hoist.eq_def] at hh
      dsimp only at hh
      split at hh
      · intro ha
        rw [tr_or] at ha
        rcases InertEv.trOrList_cons_of ha with h1 | h1
        · exact ih _ (List.mem_cons_self ..) hh a h1
        · rw [trOrList, tr] at h1
          exact InertEv.sBot_none hD (InertEv.trSort_topFresh tbl _) e a h1
      · intro ha
        rw [tr_or] at ha
        rcases InertEv.trOrList_cons_of ha with h1 | h1
        · rw [tr] at h1
          exact InertEv.sBot_none hD (InertEv.trSort_topFresh tbl _) e a h1
        · rw [trOrList] at h1
          exact ih _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hh a h1
      · cases hh
    · cases hh
  | and s' ps ih =>
    intro hh a
    rcases ps with _ | ⟨t, _ | ⟨u, _ | ⟨v, rest⟩⟩⟩
    · cases hh
    · cases hh
    · rw [Parse.hoist.eq_def] at hh
      dsimp only at hh
      rw [tr_and, trAndList, trAndList, interp_sAnd]
      split at hh
      · exact fun h => ih t (List.mem_cons_self ..) hh a h.1
      · exact fun h => ih _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hh a h.2
      · rcases Bool.or_eq_true _ _ ▸ hh with hq | hq
        · exact fun h => ih t (List.mem_cons_self ..) hq a h.1
        · exact fun h => ih _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hq a h.2
    · cases hh
  | nil => exact absurd ‹_ ∈ ([] : List Kore.Pattern)› List.not_mem_nil
  | cons q qs ih1 ih2 =>
    rename_i x hx hh a
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih1 hh a
    · exact ih2 x hx hh a
  | _ => intro hh; cases hh


/-! ## The right side as the reader reads it -/

/-- The alternatives `frRead` keeps of r (`altsOf`): those of `orAlts r` that `hoist` does not find
empty, each as `hoist` reads it, with the conditions it lifts. -/
def keptAlts (r : Kore.Pattern) : List (Kore.Pattern × List Parse.SideCond) :=
  (Parse.orAlts r).filterMap fun a =>
    if (Parse.hoist a).2.2 then none else some ((Parse.hoist a).1, (Parse.hoist a).2.1)

section
variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hB : BoolDen I) {tbl : VarTable} {e : Valuation M}
include hD hc hB

/-- **The reader's normalisation keeps the right side's elements.** Where p is `Tight`, `frRead`'s
reading `hoist (dropEmptyAlts p) = (r, cs, false)` of it, with conditions that Bool terms be
`true` only, holds the elements of p: p holds an element exactly where the conditions `cs` hold
and some kept alternative holds it with its own conditions. -/
theorem rhs_sem {p r : Kore.Pattern} {cs : List Parse.SideCond} (hT : Tight I tbl e p)
    (hh : Parse.hoist (Parse.dropEmptyAlts p) = (r, cs, false)) (hcs : AllTrue cs)
    (halt : ∀ a ∈ Parse.orAlts r, AllTrue (Parse.hoist a).2.1) (m : M) :
    (tr ⟨tbl, []⟩ p).interpret I e m ↔
      HoldsSC I tbl e cs ∧ ∃ k ∈ keptAlts r, (tr ⟨tbl, []⟩ k.1).interpret I e m ∧ HoldsSC I tbl e k.2 := by
  obtain ⟨dT, d⟩ := drop_sem hD p hT
  obtain ⟨hT', h⟩ := hoist_ok hD hc hB _ r cs false dT hh hcs
  obtain ⟨o, oT⟩ := orAlts_sem hD r hT'
  have key : (∃ q ∈ Parse.orAlts r, (tr ⟨tbl, []⟩ q).interpret I e m) ↔
      ∃ k ∈ keptAlts r, (tr ⟨tbl, []⟩ k.1).interpret I e m ∧ HoldsSC I tbl e k.2 := by
    unfold keptAlts
    constructor
    · rintro ⟨q, hq, hm⟩
      have hq' := (hoist_ok hD hc hB q _ _ _ (oT q hq) rfl (halt q hq)).2 m
      cases hemp : (Parse.hoist q).2.2
      · refine ⟨((Parse.hoist q).1, (Parse.hoist q).2.1), List.mem_filterMap.mpr ⟨q, hq, by simp [hemp]⟩, hq'.mp hm⟩
      · exact (hoist_empty hD q hemp m hm).elim
    · rintro ⟨k, hk, hm⟩
      obtain ⟨q, hq, hqk⟩ := List.mem_filterMap.mp hk
      cases hemp : (Parse.hoist q).2.2
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hqk
        subst hqk
        exact ⟨q, hq, ((hoist_ok hD hc hB q _ _ _ (oT q hq) rfl (halt q hq)).2 m).mpr hm⟩
      · simp [hemp] at hqk
  rw [← d m, h m, o m, key]
  exact and_comm

omit [Inhabited M] hc hB in
/-- `\top{S}()` holds all of S. -/
theorem tr_top_iff {S : Kore.KSort} {σ : M} (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ) (a : M) :
    (tr ⟨tbl, []⟩ (.top S)).interpret I e a ↔ Inh I σ a := by
  rw [tr, interp_sTop hD (InertEv.trSort_topFresh tbl S), interp_inhOf_of hS]

end

/-- Two lists paired by `All2` have an element of the one kind exactly where they have one of the
other, where paired elements are of one kind or of neither. -/
theorem exists_of_all2 {α β : Type} {P : α → Prop} {Q : β → Prop} : ∀ {ks : List α} {xs : List β},
    All2 (fun k x => P k ↔ Q x) ks xs → ((∃ k ∈ ks, P k) ↔ ∃ x ∈ xs, Q x)
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [h, exists_of_all2 hs]

section
variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hB : BoolDen I)
include hD hc hB

/-- **`Readings.rhs` from the reader.** The text's right side `p ∧ en` (`trAxiom_eqnPat`'s B) holds,
at an element of the result sort σ, the elements the alternatives `xs` hold where their
predicates hold, where: p is `Tight` at every valuation of the guards; `frRead` reads it as
`hoist (dropEmptyAlts p) = (r, cs, false)` with conditions that Bool terms be `true` only; the
`ensures` part en holds all of σ exactly where `Ens` does; and the alternatives `xs` are the kept
ones (`keptAlts`) in order, each holding what its kept alternative holds, its predicates holding
exactly where `Ens`, the top's conditions and its own do. -/
theorem rhs_of_reader {ws : List KoreAML.P} {r : EVar} {σ : M} {tblT : VarTable} {p en r0 : Kore.Pattern}
    {cs : List Parse.SideCond} {α : Type} {xs : List α} {A : α → KoreAML.P} {G : α → Valuation M → Prop}
    {Ens : Valuation M → Prop}
    (hT : ∀ e m, TieFR.At I ws r e m → Tight I tblT e p)
    (hh : Parse.hoist (Parse.dropEmptyAlts p) = (r0, cs, false)) (hcs : AllTrue cs)
    (halt : ∀ a ∈ Parse.orAlts r0, AllTrue (Parse.hoist a).2.1)
    (hen : ∀ e m, TieFR.At I ws r e m → ∀ a, Inh I σ a → ((tr ⟨tblT, []⟩ en).interpret I e a ↔ Ens e))
    (hbr : All2 (fun k x =>
      (∀ e m, TieFR.At I ws r e m → ∀ a, (A x).interpret I e a ↔ (tr ⟨tblT, []⟩ k.1).interpret I e a) ∧
      ∀ e m, TieFR.At I ws r e m → (G x e ↔ Ens e ∧ HoldsSC I tblT e cs ∧ HoldsSC I tblT e k.2)) (keptAlts r0) xs) :
    ∀ e m, TieFR.At I ws r e m → ∀ a, Inh I σ a →
      ((sAnd (tr ⟨tblT, []⟩ p) (tr ⟨tblT, []⟩ en)).interpret I e a ↔ ∃ x ∈ xs, (A x).interpret I e a ∧ G x e) := by
  intro e m hat a ha
  rw [interp_sAnd, rhs_sem hD hc hB (hT e m hat) hh hcs halt a, hen e m hat a ha]
  have hb : All2 (fun k x => ((tr ⟨tblT, []⟩ k.1).interpret I e a ∧ Ens e ∧ HoldsSC I tblT e cs ∧
      HoldsSC I tblT e k.2) ↔ ((A x).interpret I e a ∧ G x e)) (keptAlts r0) xs := by
    clear hT hh hcs halt hen
    generalize keptAlts r0 = ks at hbr ⊢
    induction hbr with
    | nil => exact .nil
    | cons h _ ih => exact .cons (by rw [h.1 e m hat a, h.2 e m hat]) ih
  rw [← exists_of_all2 hb]
  constructor
  · rintro ⟨⟨hcs', k, hk, h1, h2⟩, he⟩; exact ⟨k, hk, h1, he, hcs', h2⟩
  · rintro ⟨k, hk, h1, he, hcs', h2⟩; exact ⟨⟨hcs', k, hk, h1, h2⟩, he⟩

end

/-! ## The clauses `frClauses` writes -/

/-- The alternatives `frRead` gives `frClauses`: each term with its conditions that Bool terms be
`true`. -/
def frAltsOf (xs : List (Term × List Term)) : List (Term × List Cond) := xs.map fun x => (x.1, x.2.map Parse.isTrueC)

/-- The predicate of an alternative's clause: `⌈a⌉ ∧ ⋀ⱼ Bⱼ = true`. -/
def preOf (s : Srt) (x : Term × List Term) : Cond := Parse.conjC (Cond.ceil s x.1 :: x.2.map Parse.isTrueC)

/-- The predicate of the last clause: no alternative's predicate holds. -/
def preN (s : Srt) (xs : List (Term × List Term)) : Cond := Parse.conjC ((xs.map (preOf s)).map Cond.not)

theorem map_zip_map_self {α β γ : Type} (f : α × β → γ) (h : α → β) :
    ∀ ys : List α, (ys.zip (ys.map h)).map f = ys.map fun y => f (y, h y)
  | [] => rfl
  | y :: ys => by simp only [List.map_cons, List.zip_cons_cons, map_zip_map_self f h ys]

/-- **The clauses of `frClauses`**: one per alternative, its term as the right side and `preOf` as
its predicate, and the last, with the first alternative's term, the `ensures` false and `preN`. -/
theorem frClauses_eq (s : Srt) (vars : List Srt) (pats : List Term) (req : Option Term) (prio : Nat) (aside : Bool)
    (xs : List (Term × List Term)) :
    Parse.frClauses s vars pats req prio aside (frAltsOf xs) =
      xs.map (fun x => ({ vars, pats, req, rhs := x.1, ens := none, prio, aside, pre := preOf s x } : Clause)) ++
        [{ vars, pats, req, rhs := (xs.headD (Parse.boolT false, [])).1, ens := some (Parse.boolT false), prio, aside,
           pre := preN s xs }] := by
  unfold Parse.frClauses preN frAltsOf
  dsimp only
  rw [map_zip_map_self]
  simp only [List.map_map]
  cases xs <;> rfl

/-- The right side of an alternative's clause. -/
def altP (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (x : Term × List Term) : KoreAML.P :=
  tr ⟨tbl, []⟩ (Term.kore c vs x.1)

/-- The predicates of an alternative: each of its Bool terms agrees with `true`. -/
def altG (I : Interpretation KoreAML.Sym M) (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var)
    (x : Term × List Term) (e : Valuation M) : Prop :=
  ∀ b ∈ x.2, EqTrue I e (tr ⟨tbl, []⟩ (Term.kore c vs b))

/-- The premise of an alternative's clause, `prem ∧ preOf s x` (`withPre`). -/
def clauseQ (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (s : Srt) (prem : KoreAML.P)
    (x : Term × List Term) : KoreAML.P :=
  sAnd prem (tr ⟨tbl, []⟩ (Cond.kore c vs R (preOf s x)))

/-- The premise of the last clause, `prem ∧ preN s xs` (`withPre`). -/
def lastQ (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (s : Srt) (prem : KoreAML.P)
    (xs : List (Term × List Term)) : KoreAML.P :=
  sAnd prem (tr ⟨tbl, []⟩ (Cond.kore c vs R (preN s xs)))

/-- A clause's premise with a predicate other than `\top` translates as `prem ∧ pre`. -/
theorem tr_withPre {c : Semantics} {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern} {tbl : VarTable}
    (h : cl.pre.isTop = false) :
    tr ⟨tbl, []⟩ (withPre c vs cl prem) = sAnd (tr ⟨tbl, []⟩ prem) (tr ⟨tbl, []⟩ (Cond.kore c vs R cl.pre)) := by
  unfold withPre; rw [h]; exact Faithful.tr_and2 _ _ _

theorem preOf_isTop (s : Srt) (x : Term × List Term) : (preOf s x).isTop = false := by
  unfold preOf; cases x.2 <;> rfl

theorem preN_isTop (s : Srt) {xs : List (Term × List Term)} (h : xs ≠ []) : (preN s xs).isTop = false := by
  unfold preN
  rcases xs with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact (h rfl).elim
  · rfl
  · rfl

theorem tr_boolT (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (b : Bool) :
    tr ⟨tbl, []⟩ (Term.kore c vs (Parse.boolT b)) = sym (.dv (boolRepr b)) ⬝ boolP := by
  simp only [Parse.boolT, Term.kore, tr, srtOf, Faithful.sortName_bool, Faithful.trSort_srt, Lit.text, boolP]
  rfl

theorem den_bool (c : Semantics) (b : Bool) : den c (bool b) = sym (.dv (boolRepr b)) ⬝ boolP := by
  simp only [den, KoreAML.den, bool, GroundTerm.kore, tr, Faithful.sortName_bool, Faithful.trSort_srt, Lit.text, boolP]
  rfl

theorem trSort_R (tbl : VarTable) : trSort tbl R = .evar (tbl.ev (sortVarKey Rv)) := by
  rw [R, trSort]

section
variable [Inhabited M] {c : Semantics} (F : HoldsShape.NodeFacts c I) {tbl : VarTable} {vs : List KoreAML.Var}
  {e : Valuation M} {m : M}
include F

omit [Inhabited M] in
theorem boolDen_of : BoolDen I := by
  obtain ⟨β, hβ, hβd⟩ := F.sort (Faithful.bool_numbered (c := c))
  refine ⟨β, hβ, fun e a => ?_⟩
  have := hβd [] e a
  rwa [srtOf, Faithful.sortName_bool, Faithful.trSort_srt] at this

omit [Inhabited M] in
/-- A conjunction of conditions, at an element of the sort variable's sort, holds where each does. -/
theorem condKore_conjC (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m) : ∀ ps : List Cond,
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.conjC ps))).interpret I e m ↔
      ∀ p ∈ ps, (tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m
  | [] => by
    rw [Parse.conjC, Cond.kore, tr_top_iff F.defOK (by rw [trSort_R]; exact fun _ => interp_evar)]
    exact ⟨fun _ p hp => absurd hp List.not_mem_nil, fun _ => hm⟩
  | [p] => by
    rw [Parse.conjC]
    simp only [List.mem_singleton, forall_eq]
  | p :: q :: qs => by
    show (tr ⟨tbl, []⟩ (Cond.kore c vs R (.and p (Parse.conjC (q :: qs))))).interpret I e m ↔ _
    rw [Cond.kore, Faithful.tr_and2, interp_sAnd, condKore_conjC hm (q :: qs)]
    simp

/-- `⌈t⌉` at an element of the sort variable's sort: t is defined. -/
theorem condKore_ceil {s : Srt} {σ : M} {t : Term}
    (hσ : ∀ a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv)))) (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m)
    (hφ : ∀ b, (tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e b → Inh I σ b) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (.ceil s t))).interpret I e m ↔ ∃ b, (tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e b := by
  rw [Cond.kore, tr, trSort_R, interp_sCeil F.defOK F.ceilDef hσ (fun _ => interp_evar) hσS hr hφ m]
  exact ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩

/-- `b = true` at an element of the sort variable's sort: b agrees with `true` on Bool. -/
theorem condKore_isTrue {b : Term} (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv))))
    (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.isTrueC b))).interpret I e m ↔ EqTrue I e (tr ⟨tbl, []⟩ (Term.kore c vs b)) := by
  obtain ⟨β, hβ, hβd⟩ := boolDen_of F
  have hT : tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.isTrueC b)) =
      sEquals boolP (.evar (tbl.ev (sortVarKey Rv))) (tr ⟨tbl, []⟩ (Term.kore c vs b)) trueP := by
    rw [Parse.isTrueC, Cond.kore, tr, ← trSort_R, tr_boolT]
    simp only [srtOf, Faithful.sortName_bool, Faithful.trSort_srt]
    rfl
  rw [hT, interp_sEquals F.defOK F.ceilDef (hβd e) (fun _ => interp_evar) hβ hr]
  unfold EqTrue
  simp only [interp_inhOf_of (hβd e), hm, true_and]

omit [Inhabited M] F in
theorem condKore_not {p : Cond} :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (.not p))).interpret I e m ↔
      ¬ (tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ∧ Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m := by
  rw [Cond.kore, tr, interp_sNot, trSort_R, interp_inhOf_of (fun _ => interp_evar)]

/-- An alternative's predicate, at an element of the sort variable's sort: its term is defined and
its Bool terms agree with `true`. -/
theorem preOf_iff {s : Srt} {σ : M} {x : Term × List Term}
    (hσ : ∀ a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv)))) (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m)
    (hφ : ∀ b, (altP c tbl vs x).interpret I e b → Inh I σ b) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (preOf s x))).interpret I e m ↔
      (∃ b, (altP c tbl vs x).interpret I e b) ∧ altG I c tbl vs x e := by
  unfold preOf
  rw [condKore_conjC F hm]
  simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  rw [condKore_ceil F hσ hσS hr hm hφ]
  simp only [condKore_isTrue F hr hm]
  rfl

end

section
variable [Inhabited M] {c : Semantics} (F : HoldsShape.NodeFacts c I)
include F

/-- **The readings of the clauses `frClauses` writes** (`TieFR.Readings`). For the alternatives
`xs` over the variables `vs`, with the premise `prem` of the sentence: each clause's premise
(`clauseQ`, `lastQ`) reads from `NodeFacts`; that each alternative lies in the result sort σ is
`hin` (`inSort_of_terms` gives it from `TermsInSort`); the reading of the sentence's right side is
`hrhs` (`readings_of_fr` gives it from the reader). -/
theorem readings_of_rhs {tbl : VarTable} {vs : List KoreAML.Var} {s : Srt} {xs : List (Term × List Term)}
    {ws : List KoreAML.P} {σ : M} {prem rhsT : KoreAML.P}
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xs, ∀ a,
      (altP c tbl vs x).interpret I e a → Inh I σ a)
    (hrhs : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ a, Inh I σ a →
      (rhsT.interpret I e a ↔ ∃ x ∈ xs, (altP c tbl vs x).interpret I e a ∧ altG I c tbl vs x e)) :
    TieFR.Readings I ws (tbl.ev (sortVarKey Rv)) σ prem rhsT xs (altP c tbl vs) (altG I c tbl vs)
      (clauseQ c tbl vs s prem) (lastQ c tbl vs s prem xs) where
  inSort := hin
  clause e m hat x hx := by
    have hrS := TieFR.isSort_of_at F.defOK hr hat
    unfold clauseQ
    rw [interp_sAnd, preOf_iff F (hσ e) hσS hrS hat.2 (hin e m hat x hx)]
  none e m hat := by
    have hrS := TieFR.isSort_of_at F.defOK hr hat
    unfold lastQ preN
    rw [interp_sAnd, condKore_conjC F hat.2]
    refine and_congr Iff.rfl ?_
    simp only [List.forall_mem_map]
    refine forall_congr' fun x => forall_congr' fun hx => ?_
    rw [condKore_not, preOf_iff F (hσ e) hσS hrS hat.2 (hin e m hat x hx)]
    exact ⟨fun h => h.1, fun h => ⟨h, hat.2⟩⟩
  rhs := hrhs

/-- **The readings of the clauses `frClauses` writes, from the reader** (`TieFR.Readings`). The
equation `eq` is one `frRead` reads, its right side `eq.rhs` translated over the text's table
`tblT`, and its `ensures` part `en` holding where `Ens` does. The sorts of the right side's
connectives are the reader's: `frRead` reads only a right side that is `rhsSorted`
(`frRead_rhsSorted`), which with `TightSem` (its operands lie in their sorts) is `Tight`
(`tight_of_rhsSorted`). The reading of the right side is then `rhs_of_reader`'s, the rest
`readings_of_rhs`'s. -/
theorem readings_of_fr {N : Parse.Names} {eq : Parse.RawEqn} {y : Option (List Clause × List KoreAML.Var)}
    {tbl tblT : VarTable} {vs : List KoreAML.Var} {s : Srt} {xs : List (Term × List Term)}
    {ws : List KoreAML.P} {σ : M} {prem : KoreAML.P} {en r0 : Kore.Pattern} {cs : List Parse.SideCond}
    {Ens : Valuation M → Prop}
    (hrd : Parse.frRead N eq = .ok y)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xs, ∀ a,
      (altP c tbl vs x).interpret I e a → Inh I σ a)
    (hT : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → TightSem I tblT e eq.rhs)
    (hh : Parse.hoist (Parse.dropEmptyAlts eq.rhs) = (r0, cs, false)) (hcs : AllTrue cs)
    (halt : ∀ a ∈ Parse.orAlts r0, AllTrue (Parse.hoist a).2.1)
    (hen : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ a, Inh I σ a →
      ((tr ⟨tblT, []⟩ en).interpret I e a ↔ Ens e))
    (hbr : All2 (fun k x =>
      (∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ a,
        (altP c tbl vs x).interpret I e a ↔ (tr ⟨tblT, []⟩ k.1).interpret I e a) ∧
      ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m →
        (altG I c tbl vs x e ↔ Ens e ∧ HoldsSC I tblT e cs ∧ HoldsSC I tblT e k.2)) (keptAlts r0) xs) :
    TieFR.Readings I ws (tbl.ev (sortVarKey Rv)) σ prem
      (sAnd (tr ⟨tblT, []⟩ eq.rhs) (tr ⟨tblT, []⟩ en)) xs (altP c tbl vs) (altG I c tbl vs)
      (clauseQ c tbl vs s prem) (lastQ c tbl vs s prem xs) :=
  readings_of_rhs F hr hσ hσS hin
    (rhs_of_reader F.defOK F.ceilDef (boolDen_of F)
      (fun e m hat => tight_of_rhsSorted eq.rhs (Parse.frRead_rhsSorted hrd) (hT e m hat))
      hh hcs halt hen hbr)

omit F in
/-- **The alternatives lie in the result sort** where each is a term of it (`TermsInSort`) and the
guards put its variables in their sorts. -/
theorem inSort_of_terms (hTS : Faithful.TermsInSort c I) {tbl : VarTable} {vars : List Srt} {s : Srt}
    {xs : List (Term × List Term)} {ws : List KoreAML.P} {r : EVar} {σ : M}
    (hs : s < nRegSorts + c.sortNames.length)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ)
    (hty : ∀ x ∈ xs, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars x.1 = some s)
    (hvar : ∀ e m, TieFR.At I ws r e m → ∀ x ∈ xs, ∀ i ∈ varOccs x.1,
      Faithful.InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (Faithful.canonKey c vars i)))) :
    ∀ e m, TieFR.At I ws r e m → ∀ x ∈ xs, ∀ a, (altP c tbl (canonVars c vars) x).interpret I e a → Inh I σ a := by
  intro e m hat x hx a ha
  have h := hTS (hty x hx) hs (hvar e m hat x hx) a ha
  rw [← Faithful.inS_iff e] at h
  have : KoreAML.Cons.sortP (c.sortName s) = trSort tbl (srtOf c s) := by
    rw [srtOf, Faithful.trSort_srt]; rfl
  rw [this, interp_inhOf_of (hσ e)] at h
  exact h

/-! ## The last clause's right side holds nothing -/

/-- **`false = true` holds nothing** (`reqPat S (some false)`, the last clause's `ensures`): the
values `false` and `true` of Bool denote two elements (`NodeFacts.val`, `NodeFacts.apart`). -/
theorem ensFalse_none {tbl : VarTable} {vs : List KoreAML.Var} {S : Kore.KSort} {e : Valuation M} {σ' : M}
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ') (hσ' : IsSort I σ') (a : M) :
    ¬ (tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c vs (Parse.boolT false))))).interpret I e a := by
  obtain ⟨β, hβ, hβd⟩ := boolDen_of F
  have hT : tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c vs (Parse.boolT false)))) =
      sEquals boolP (trSort tbl S) (den c (bool false)) (den c (bool true)) := by
    rw [reqPat, tr, tr_boolT, den_bool, den_bool, Faithful.trSort_srt, tr, Faithful.trSort_srt]
    rfl
  rw [hT, interp_sEquals F.defOK F.ceilDef (hβd e) hS hβ hσ']
  rintro ⟨-, h⟩
  obtain ⟨aF, haF, hinF⟩ := F.val (rmS_sortOf_bool c false) tbl e
  rw [srtOf, Faithful.sortName_bool, Faithful.trSort_srt] at hinF
  have hiF : Inh I β aF := (interp_inhOf_of (hβd e)).mp hinF
  have hT' := (h aF hiF).mp ((haF aF).mpr rfl)
  have := F.apart (rmS_sortOf_bool c false) (rmS_sortOf_bool c true) e aF ((haF aF).mpr rfl) hT'
  simp [bool] at this

/-- **`NoneEmpty` for the last clause's right side** `a₁ ∧ (false = true)` (`noneEmpty_of_empty`). -/
theorem noneEmpty_of_apart {ws : List KoreAML.P} {r : EVar} {σ : M} {α : Type} {alts : List α}
    {A : α → KoreAML.P} {G : α → Valuation M → Prop} {tbl : VarTable} {vs : List KoreAML.Var} {S : Kore.KSort}
    {A₁ : KoreAML.P} (hS : ∀ (e : Valuation M) a, (trSort tbl S).interpret I e a ↔ a = σ) (hσ : IsSort I σ) :
    TieFR.NoneEmpty I ws r σ alts A G
      (sAnd A₁ (tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c vs (Parse.boolT false)))))) :=
  TieFR.noneEmpty_of_empty fun e _ _ a _ ha => ensFalse_none F (hS e) hσ a (interp_sAnd.mp ha).2

end

end

end TieFRRead

end KCore
