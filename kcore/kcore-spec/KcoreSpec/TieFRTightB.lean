/-
  `TightSem` of a right side from one decision on the text (`tightB`), for the readings of
  KcoreSpec/TieFRRead.lean (`readings_of_frT`'s `hT`).

  `tightSem_of_termOps` leaves, of the operands of the right side's `\or{s}`s and `\and{s}`s, those
  that are no `\or`, no `\and` and state no sort at their head. `tightB` decides of each of them
  that it is `rhsSorted` and that each of its alternatives (`Parse.orAlts`; the operand itself where
  it holds no `\or`) is read by `Parse.term` over the equation's variables `vsF` as a term whose
  pattern is its own (`rtPat`) and whose sort (`sortOfTerm`) is numbered and is the connective's;
  and of the sort of each `\and` that it is a numbered sort's.

  - `tightSem_of_tightB`: where `tightB` holds, the pattern is `TightSem` at every valuation that
    puts the variables of `vars` in their sorts, in a model with `NodeFacts` and `TermsInSort`.
    A term lies in its sort (`inSortK_of_read`); an operand whose alternatives are terms of s lies
    in s (`inSortK_of_alts`), being `Tight` where it is `TightSem` and `rhsSorted`; so `TightSem` of
    a pattern and that it lies in the sort of the connective it is an operand of are shown
    together, by induction on the pattern.
  - `tightSem_of_guardsB`: the same at the valuations of an equation's guards, which hold each
    variable read in its sort (`guardsHold`, `inS_of_guards`).
-/
import KcoreSpec.TieFRVars

set_option autoImplicit false

namespace KCore

namespace TieFRTightB

open ML KoreAML Faithful
open KCore.TieFRRead KCore.TermRT KCore.TieFRRT

/-- q is read over the variables `vsF`, none added, as a term whose pattern is q's and whose sort
over `vars` is numbered and is the sort S names. -/
def termInB (N : Parse.Names) (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var)
    (S : Kore.KSort) (q : Kore.Pattern) : Bool :=
  match Parse.term N vsF q with
  | .ok (t, vs') =>
    decide (vs'.map (fun v => (v.name, v.sort)) = vsF.map (fun v => (v.name, v.sort))) && rtPat N q &&
      match sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t with
      | some s => decide (s < nRegSorts + c.sortNames.length) &&
          decide (trSort tblT S = trSort tbl (srtOf c s))
      | none => false
  | .error _ => false

/-- An operand that is an `\or` or an `\and`, or states its sort at its head (`opStatedK`), or is
`rhsSorted` with each alternative a term of the connective's sort (`termInB`). -/
def leafInB (N : Parse.Names) (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var)
    (x : Kore.KSort × Kore.Pattern) : Bool :=
  !opLeaf x.2 || opStatedK x.2 ||
    (Parse.rhsSorted x.2 && (Parse.orAlts x.2).all (termInB N c tbl tblT vars vsF x.1))

/-- S names a numbered sort. -/
def sortNumB (c : Semantics) (tbl tblT : VarTable) (S : Kore.KSort) : Bool :=
  (List.range (nRegSorts + c.sortNames.length)).any fun s => decide (trSort tblT S = trSort tbl (srtOf c s))

/-- The decision of `TightSem`: p is `rhsSorted`, each operand of its connectives is `leafInB`, and
the sort of each of its `\and`s is numbered. -/
def tightB (N : Parse.Names) (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var)
    (p : Kore.Pattern) : Bool :=
  Parse.rhsSorted p && (connOps p).all (leafInB N c tbl tblT vars vsF) && (andSorts p).all (sortNumB c tbl tblT)

/-- Two lists of variables with the same names and sorts are one list. -/
theorem varKeys_inj : ∀ {l l' : List Var},
    l.map (fun v => (v.name, v.sort)) = l'.map (fun v => (v.name, v.sort)) → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases a; cases b
    simp only at h1 h2
    subst h1 h2
    rw [varKeys_inj h3]

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- A numbered sort's name denotes one sort. -/
theorem sortDen_of_sortNumB {c : Semantics} (F : HoldsShape.NodeFacts c I) {tbl tblT : VarTable} {S : Kore.KSort}
    (h : sortNumB c tbl tblT S = true) (e : Valuation M) : SortDen I tblT e S := by
  obtain ⟨s, hs, hS⟩ := List.any_eq_true.mp h
  obtain ⟨τ, hτ, hd⟩ := F.sort (List.mem_range.mp hs)
  exact ⟨τ, hτ, fun a => by rw [of_decide_eq_true hS]; exact hd tbl e a⟩

/-- **A term of the sort S lies in S** (`termInB`), at a valuation that puts the variables of
`vars` in their sorts. -/
theorem inSortK_of_termInB {N : Parse.Names} {c : Semantics} (hTS : TermsInSort c I)
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames) {tbl tblT : VarTable} {vars : List Srt}
    {vsF : List Var} (hA : alignOK c tbl tblT vars vsF = true) {e : Valuation M}
    (hV : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    {S : Kore.KSort} {q : Kore.Pattern} (h : termInB N c tbl tblT vars vsF S q = true) :
    InSortK I tblT e S q := by
  unfold termInB at h
  split at h
  · rename_i t vs' hrd
    split at h
    · rename_i s hty
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hvs, hrt⟩, hs, hS⟩ := h
      have hvs' : vs' = vsF := varKeys_inj hvs
      exact inSortK_of_read hsy hso hTS hA hrd hrt (hvs' ▸ List.prefix_refl _) hs hty hS
        (fun i hi => hV i (varOccs_lt t hty i hi))
    · simp at h
  · cases h

/-- **`TightSem` from the decision**, at a valuation that puts the variables of `vars` in their
sorts. -/
theorem tightSem_of_tightB {N : Parse.Names} {c : Semantics} (F : HoldsShape.NodeFacts c I)
    (hTS : TermsInSort c I) (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var} (hA : alignOK c tbl tblT vars vsF = true)
    {e : Valuation M}
    (hV : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    {p : Kore.Pattern} (h : tightB N c tbl tblT vars vsF p = true) : TightSem I tblT e p := by
  have hD := F.defOK
  unfold tightB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hS, hL⟩, hA'⟩ := h
  -- an operand that is no `\or` and no `\and` lies in its connective's sort where it is `TightSem`
  have hleaf : ∀ (s : Kore.KSort) (q : Kore.Pattern), (s, q) ∈ connOps p → opLeaf q = true →
      TightSem I tblT e q → InSortK I tblT e s q := by
    intro s q hx hlf hT
    have hl := hL (s, q) hx
    unfold leafInB at hl
    simp only [hlf, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at hl
    rcases hl with hk | ⟨hrs, halts⟩
    · exact inSortK_of_stated hD q ((connOps_sub p (s, q) hx).2 hS) hk
    · exact inSortK_of_alts hD (tight_of_rhsSorted q hrs hT)
        (fun q' hq' => inSortK_of_termInB hTS hsy hso hA hV (halts q' hq'))
  suffices key : ∀ q, connOps q ⊆ connOps p → andSorts q ⊆ andSorts p →
      TightSem I tblT e q ∧ ∀ s, (s, q) ∈ connOps p → InSortK I tblT e s q from
    (key p (fun _ h => h) (fun _ h => h)).1
  intro q
  induction q using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, connOps q ⊆ connOps p → andSorts q ⊆ andSorts p →
      TightSem I tblT e q ∧ ∀ s, (s, q) ∈ connOps p → InSortK I tblT e s q) with
  | app hd ss ps ih =>
    intro h1 h2
    have hT : TightSem I tblT e (.app hd ss ps) := by
      rw [TightSem, tightSemList_iff]
      intro q hq
      refine (ih q hq (fun y hy => h1 ?_) (fun y hy => h2 ?_)).1
      · rw [connOps, mem_connOpsList]; exact ⟨q, hq, hy⟩
      · rw [andSorts, mem_andSortsList]; exact ⟨q, hq, hy⟩
    exact ⟨hT, fun s hx => hleaf s _ hx rfl hT⟩
  | and s' ps ih =>
    intro h1 h2
    have hops : ∀ q ∈ ps, TightSem I tblT e q ∧ InSortK I tblT e s' q := by
      intro q hq
      have hq1 : (s', q) ∈ connOps (.and s' ps) := by
        rw [connOps, List.mem_append]; exact .inl (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have := ih q hq (fun y hy => h1 (by rw [connOps, List.mem_append, mem_connOpsList]; exact .inr ⟨q, hq, hy⟩))
        (fun y hy => h2 (by rw [andSorts, List.mem_cons, mem_andSortsList]; exact .inr ⟨q, hq, hy⟩))
      exact ⟨this.1, this.2 s' (h1 hq1)⟩
    refine ⟨?_, fun s hx => ?_⟩
    · rw [TightSem, tightSemList_iff]
      exact ⟨sortDen_of_sortNumB F (hA' s' (h2 (by rw [andSorts]; exact List.mem_cons_self ..))) e,
        fun q hq => (hops q hq).2, fun q hq => (hops q hq).1⟩
    · have hs := (connOps_sub p (s, .and s' ps) hx).2 hS
      rw [sortIs, Bool.and_eq_true, decide_eq_true_iff] at hs
      obtain ⟨rfl, -⟩ := hs
      exact inSortK_conn hD (.inr rfl) fun q hq => (hops q hq).2
  | or s' ps ih =>
    intro h1 h2
    have hops : ∀ q ∈ ps, TightSem I tblT e q ∧ InSortK I tblT e s' q := by
      intro q hq
      have hq1 : (s', q) ∈ connOps (.or s' ps) := by
        rw [connOps, List.mem_append]; exact .inl (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have := ih q hq (fun y hy => h1 (by rw [connOps, List.mem_append, mem_connOpsList]; exact .inr ⟨q, hq, hy⟩))
        (fun y hy => h2 (by rw [andSorts, mem_andSortsList]; exact ⟨q, hq, hy⟩))
      exact ⟨this.1, this.2 s' (h1 hq1)⟩
    refine ⟨?_, fun s hx => ?_⟩
    · rw [TightSem, tightSemList_iff]
      exact ⟨fun q hq => (hops q hq).2, fun q hq => (hops q hq).1⟩
    · have hs := (connOps_sub p (s, .or s' ps) hx).2 hS
      rw [sortIs, Bool.and_eq_true, decide_eq_true_iff] at hs
      obtain ⟨rfl, -⟩ := hs
      exact inSortK_conn hD (.inl rfl) fun q hq => (hops q hq).2
  | nil => exact absurd ‹_ ∈ ([] : List Kore.Pattern)› List.not_mem_nil
  | cons q qs ih1 ih2 =>
    rename_i q' hq' h1 h2
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact ih1 h1 h2
    · exact ih2 q' hq' h1 h2
  | _ =>
    intro _ _
    refine ⟨by simp [TightSem], fun s hx => hleaf s _ hx rfl (by simp [TightSem])⟩

/-- **`TightSem` at the valuations of the guards** (`readings_of_frT`'s `hT`): the guards hold
each variable read in its sort (`guardsHold`). -/
theorem tightSem_of_guardsB {N : Parse.Names} {c : Semantics} (F : HoldsShape.NodeFacts c I)
    (hTS : TermsInSort c I) (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
    (hvars : Parse.varSorts N vsF = .ok vars) (hA : alignOK c tbl tblT vars vsF = true)
    {ws : List P} {r : EVar} (hg : TieFRVars.guardsHold ws tblT vsF = true)
    {p : Kore.Pattern} (h : tightB N c tbl tblT vars vsF p = true) :
    ∀ e m, TieFR.At I ws r e m → TightSem I tblT e p :=
  fun _ _ hat => tightSem_of_tightB F hTS hsy hso hA
    (fun _ hi => TieFRVars.inS_of_guards F.defOK hso hvars hA hg hat.1
      (by rw [← (TieFRVars.varSorts_spec hvars).1]; exact hi)) h

end

end TieFRTightB

end KCore
