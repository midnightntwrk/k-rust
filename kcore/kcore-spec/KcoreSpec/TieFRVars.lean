/-
  The variables of the clauses `Parse.frRead` reads, from the reader and from the definition's
  well-sortedness: what the readings of KcoreSpec/TieFRRead.lean (`readings_of_frT`,
  `inSort_of_terms`, `inSortK_of_term`) and `Γ`'s items (`TieFRGamma.gamma_shapeFG`) take of them.

  - **The numbering of `Parse.term`** (`numT_all`, `numTs_all`): a variable numbered while a term
    is read, that is one the list held before, or one the term holds. So the variables the
    patterns of an equation's head number (`svinPats`) are those the patterns hold
    (`svinPats_occ`).
  - **What `frRead` reads of the variables** (`frRead_occInv`): every variable of an alternative,
    of its own conditions, of the lifted conditions and of the `ensures` is one the patterns
    number (`boundByArgs`), and there are two alternatives or more. With the numbering, every
    variable of an alternative of the clauses `frClauses` writes occurs in the patterns
    (`occ_of_frRead`): `gamma_shapeFG`'s `hxs` and `hocc`.
  - **The sorts, from the definition**: `frRead` runs no sort check of the terms it reads. The
    definition's clause check (`clauseSorted`, which `sortedOK`, part of `coreOK`, asks of every
    clause of every function) states that each clause's right side, here an alternative, has the
    function's result sort, and that its patterns have the argument sorts, so that there are as
    many as the function has arguments (`sorted_of_frClauses`): `inSort_of_terms`'s `hty` and
    `gamma_shapeFG`'s `hlen`. A term operand of a connective that is not an alternative (an
    argument of an application under which an `\or` is distributed) is no clause's right side,
    and its sort stays a premise of `inSortK_of_term`.
  - **The variables in their sorts** (`inS_of_guards`): where the guards hold, and they hold the
    membership of each variable read in its sort over the text's table (`guardsHold`, a decision
    of the text), each variable of the table `tbl` aligned with the text's (`alignOK`) lies in
    the sort `varSorts` numbers for it. With the sort of a term (`hty`) its variables are among
    those read (`varOccs_lt`), which gives `inSort_of_terms`'s and `inSortK_of_term`'s `hvar`
    (`hvar_of_sorted`, `inSort_of_read`, `inSortK_of_readG`).
-/
import KcoreSpec.TieFRTermRT
import KcoreSpec.TieFRGamma

set_option autoImplicit false

namespace KCore

namespace TieFRVars

open ML KoreAML Faithful
open KCore.TieFRRead KCore.TermRT KCore.TieFRRT

/-! ## The numbering of `Parse.term` -/

/-- `varIndex` numbers a variable the list held, or the one it appends. -/
theorem varIndex_num {vs vs' : List Var} {x : Kore.EVar} {i : Nat} (h : Parse.varIndex vs x = .ok (i, vs')) :
    ∀ j < vs'.length, j < vs.length ∨ j = i := by
  unfold Parse.varIndex at h
  obtain ⟨n, -, h⟩ := bind_ok h
  obtain ⟨s, -, h⟩ := bind_ok h
  split at h
  · split at h
    · cases h
      exact fun j hj => .inl hj
    · cases h
  · cases h
    intro j hj
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact .inl h
    · exact .inr h

/-- What `numT_all` states of a pattern: a variable numbered while it is read was numbered before,
or the term read holds it. -/
def NumT (N : Parse.Names) (p : Kore.Pattern) : Prop :=
  ∀ (vs : List Var) (t : Term) (vs' : List Var), Parse.term N vs p = .ok (t, vs') →
    ∀ j < vs'.length, j < vs.length ∨ j ∈ varOccs t

/-- What `numTs_all` states of a list of patterns. -/
def NumTs (N : Parse.Names) (ps : List Kore.Pattern) : Prop :=
  ∀ (vs : List Var) (ts : List Term) (vs' : List Var), Parse.terms N vs ps = .ok (ts, vs') →
    ∀ j < vs'.length, j < vs.length ∨ j ∈ varOccsList ts

theorem numTs_nil (N : Parse.Names) : NumTs N [] := by
  intro vs ts vs' hrd
  rw [Parse.terms] at hrd
  cases hrd
  exact fun j hj => .inl hj

theorem numTs_cons {N : Parse.Names} {p : Kore.Pattern} {ps : List Kore.Pattern} (ih1 : NumT N p)
    (ih2 : NumTs N ps) : NumTs N (p :: ps) := by
  intro vs ts vs' hrd j hj
  rw [Parse.terms] at hrd
  obtain ⟨⟨t, vs1⟩, h1, hrd⟩ := bind_ok hrd
  obtain ⟨⟨ts1, vs2⟩, h2, hrd⟩ := bind_ok hrd
  cases hrd
  rw [varOccsList]
  rcases ih2 vs1 ts1 vs' h2 j hj with h | h
  · rcases ih1 vs t vs1 h1 j h with h | h
    · exact .inl h
    · exact .inr (List.mem_append_left _ h)
  · exact .inr (List.mem_append_right _ h)

/-- **The numbering of `Parse.term`**: a variable numbered while a pattern is read was numbered
before, or the term read holds it. -/
theorem numT_all (N : Parse.Names) (p : Kore.Pattern) : NumT N p := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => (∀ p ∈ ps, NumT N p) ∧ NumTs N ps) with
  | var v =>
    intro vs t vs' hrd
    cases v with
    | evar x =>
      rw [Parse.term.eq_def] at hrd; simp only at hrd
      obtain ⟨⟨i, vs1⟩, h1, hrd⟩ := bind_ok hrd
      cases hrd
      intro j hj
      rcases varIndex_num h1 j hj with h | rfl
      · exact .inl h
      · exact .inr (by rw [varOccs]; exact List.mem_singleton_self _)
    | svar X => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
  | app h ss ps ih =>
    intro vs t vs' hrd
    rw [Parse.term.eq_def] at hrd; simp only at hrd
    by_cases hinj : (h.ident.name == "inj") = true
    · rw [ifP hinj] at hrd
      obtain ⟨A, B, p, rfl, rfl⟩ : ∃ A B p, ss = [A, B] ∧ ps = [p] := by
        split at hrd
        · exact ⟨_, _, _, rfl, rfl⟩
        · cases hrd
      simp only at hrd
      obtain ⟨a, -, hrd⟩ := bind_ok hrd
      obtain ⟨b, -, hrd⟩ := bind_ok hrd
      by_cases hcc : N.cellPairs.contains (a, b) = true
      · rw [ifP hcc] at hrd; cases hrd
      rw [ifN hcc] at hrd
      obtain ⟨⟨t1, vs1⟩, h1, hrd⟩ := bind_ok hrd
      obtain ⟨sa, -, hrd⟩ := bind_ok hrd
      obtain ⟨sb, -, hrd⟩ := bind_ok hrd
      cases hrd
      rw [varOccs]
      exact ih.1 p (List.mem_singleton_self _) _ _ _ h1
    · rw [ifN hinj] at hrd
      by_cases hem : ss.isEmpty = true
      · rw [ifP hem] at hrd
        obtain ⟨⟨ts, vs1⟩, h1, hrd⟩ := bind_ok hrd
        obtain ⟨f, -, hrd⟩ := bind_ok hrd
        cases hrd
        rw [varOccs]
        exact ih.2 _ _ _ h1
      · rw [ifN hem] at hrd
        by_cases hal : Parse.preludeAliases.contains h.ident.name = true
        · rw [ifP hal] at hrd; cases hrd
        · rw [ifN hal] at hrd
          by_cases hite : (h.ident.name == "Lblite" && ss.length == 1) = true
          · rw [ifP hite] at hrd
            obtain ⟨S, rfl⟩ : ∃ S, ss = [S] := by
              split at hrd
              · exact ⟨_, rfl⟩
              · cases hrd
            simp only at hrd
            obtain ⟨⟨ts, vs1⟩, h1, hrd⟩ := bind_ok hrd
            obtain ⟨X, -, hrd⟩ := bind_ok hrd
            obtain ⟨f, -, hrd⟩ := bind_ok hrd
            cases hrd
            rw [varOccs]
            exact ih.2 _ _ _ h1
          · rw [ifN hite] at hrd
            split at hrd
            · obtain ⟨⟨ts, vs1⟩, h1, hrd⟩ := bind_ok hrd
              cases hrd
              rw [varOccs]
              exact ih.2 _ _ _ h1
            · cases hrd
  | and s ps ih =>
    intro vs t vs' hrd
    cases ps with
    | nil => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
    | cons p ps1 =>
      cases ps1 with
      | nil => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
      | cons q ps2 =>
        cases ps2 with
        | cons _ _ => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
        | nil =>
          cases q with
          | var v =>
            cases v with
            | evar x =>
              rw [Parse.term.eq_def] at hrd; simp only at hrd
              obtain ⟨⟨t1, vs1⟩, h1, hrd⟩ := bind_ok hrd
              obtain ⟨⟨i, vs2⟩, h2, hrd⟩ := bind_ok hrd
              cases hrd
              intro j hj
              rw [varOccs]
              rcases varIndex_num h2 j hj with h | rfl
              · rcases ih.1 p (List.mem_cons_self ..) vs t1 vs1 h1 j h with h | h
                · exact .inl h
                · exact .inr (List.mem_append_left _ h)
              · exact .inr (List.mem_append_right _ (List.mem_singleton_self _))
            | svar X => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
          | _ => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
  | dv s text =>
    intro vs t vs' hrd
    rw [Parse.term.eq_def] at hrd; simp only at hrd
    obtain ⟨s', -, hrd⟩ := bind_ok hrd
    obtain ⟨l, -, hrd⟩ := bind_ok hrd
    cases hrd
    exact fun j hj => .inl hj
  | nil => exact ⟨fun p hp => absurd hp List.not_mem_nil, numTs_nil N⟩
  | cons p ps ih1 ih2 =>
    refine ⟨fun q hq => ?_, numTs_cons ih1 ih2.2⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ih1
    · exact ih2.1 q hq
  | _ =>
    intro vs t vs' hrd
    rw [Parse.term.eq_def] at hrd
    simp only at hrd
    first | cases hrd | (split at hrd <;> first | cases hrd | (split at hrd <;> cases hrd))

/-- **The numbering of `Parse.terms`**. -/
theorem numTs_all (N : Parse.Names) : ∀ ps : List Kore.Pattern, NumTs N ps
  | [] => numTs_nil N
  | p :: ps => numTs_cons (numT_all N p) (numTs_all N ps)

/-- **The variables an equation's head numbers in its patterns are those the patterns hold.** -/
theorem svinPats_occ {N : Parse.Names} {e : Parse.RawEqn} {pats : List Term} {vs : List Var}
    (h : Parse.svinPats N e = .ok (pats, vs)) : ∀ j < vs.length, j ∈ varOccsList pats := by
  unfold Parse.svinPats at h
  split at h
  · cases h
  · intro j hj
    exact (numTs_all N _ _ _ _ h j hj).resolve_left (Nat.not_lt_zero _)
  · obtain ⟨s, -, h⟩ := bind_ok h
    obtain ⟨⟨ts, vs1⟩, h1, h⟩ := bind_ok h
    cases h
    intro j hj
    rw [varOccsList, varOccsList, varOccs, varOccs]
    rcases numTs_all N _ _ _ _ h1 j hj with h | h
    · simp only [List.length_cons, List.length_nil] at h
      rcases j with _ | _ | j
      · simp
      · simp
      · omega
    · exact List.mem_append_right _ (List.mem_append_right _ h)

/-! ## What `frRead` reads of the variables -/

/-- **The patterns `eqnHead` reads** are `svinPats`', and the number of variables they hold is the
count it gives. -/
theorem eqnHead_pats {N : Parse.Names} {e : Parse.RawEqn} {pats : List Term} {req ens : Option Term}
    {vs0 : List Var} {np : Nat} (h : Parse.eqnHead N e = .ok (pats, req, ens, vs0, np)) :
    ∃ vsP, Parse.svinPats N e = .ok (pats, vsP) ∧ np = vsP.length := by
  unfold Parse.eqnHead at h
  obtain ⟨⟨pats', vs⟩, hs, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, hp, h⟩ := bind_ok h
    cases hp
    dsimp only at h
    split at h
    · obtain ⟨_, hp, h⟩ := bind_ok h
      cases hp
      cases h
      exact ⟨vs, hs, rfl⟩
    · obtain ⟨⟨t, vs3⟩, -, h⟩ := bind_ok h
      dsimp only at h
      obtain ⟨_, hp, h⟩ := bind_ok h
      cases hp
      cases h
      exact ⟨vs, hs, rfl⟩
  · obtain ⟨⟨t0, vsr⟩, -, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, hp, h⟩ := bind_ok h
    cases hp
    dsimp only at h
    split at h
    · obtain ⟨_, hp, h⟩ := bind_ok h
      cases hp
      cases h
      exact ⟨vs, hs, rfl⟩
    · obtain ⟨⟨t, vs3⟩, -, h⟩ := bind_ok h
      dsimp only at h
      obtain ⟨_, hp, h⟩ := bind_ok h
      cases hp
      cases h
      exact ⟨vs, hs, rfl⟩

/-- `boundByArgs` accepts variables the arguments number only. -/
theorem boundByArgs_ok {vs : List Var} {np : Nat} {conn : String} {used : List Nat}
    (h : Parse.boundByArgs vs np conn used = .ok ()) : ∀ i ∈ used, i < np := by
  unfold Parse.boundByArgs at h
  split at h
  · cases h
  · rename_i hf
    intro i hi
    have := List.find?_eq_none.mp hf i hi
    simpa using this

/-- **What `frRead` reads of the variables** (`frRead N eq = .ok (some z)`): `frRead_inv`'s head,
lifted conditions and alternatives, with two alternatives or more, and every variable of an
alternative, of its own conditions, of the lifted conditions and of the `ensures` among the
`np` the head's patterns number. -/
theorem frRead_occInv {N : Parse.Names} {eq : Parse.RawEqn} {z : List Clause × List Var}
    (h : Parse.frRead N eq = .ok (some z)) :
    ∃ pats req ens vs0 np ts vs1 alts s vars,
      Parse.eqnHead N eq = .ok (pats, req, ens, vs0, np) ∧
      Parse.altsOf N vs1 (Parse.orAlts (frSide eq.rhs)) = .ok (alts, z.2) ∧
      ¬ alts.length < 2 ∧
      (∀ i ∈ alts.flatMap (fun a => varOccs a.1 ++ a.2.flatMap (varOccsCond z.2.length)) ++
        (ens.toList ++ ts).flatMap varOccs, i < np) ∧
      z.1 = Parse.frClauses s vars pats req (Parse.eqnPrio eq).2 (Parse.nonExec eq)
        (alts.map fun a => (a.1, (ens.toList ++ ts).map Parse.isTrueC ++ a.2)) := by
  unfold Parse.frRead at h
  obtain ⟨_, -, h⟩ := bind_ok_FR h
  unfold frSide
  rcases hx : Parse.hoist (Parse.dropEmptyAlts eq.rhs) with ⟨r, conds, emp⟩
  rw [hx] at h
  dsimp only at h ⊢
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨⟨pats, req, ens, vs, np⟩, hhead, h⟩ := bind_ok_FR h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨_, h', -⟩ := bind_ok_FR h; cases h'
    · split at h
      · obtain ⟨⟨cs, vs1⟩, -, h⟩ := bind_ok_FR h
        dsimp only at h
        obtain ⟨⟨alts, vs2⟩, hal, h⟩ := bind_ok_FR h
        dsimp only at h
        split at h
        · cases h
        · rename_i hlt
          obtain ⟨_, hb, h⟩ := bind_ok_FR h
          obtain ⟨s, -, h⟩ := bind_ok_FR h
          obtain ⟨vars, -, h⟩ := bind_ok_FR h
          cases h
          exact ⟨pats, req, ens, vs, np, cs, vs1, alts, s, vars, hhead, hal, hlt, boundByArgs_ok hb, rfl⟩
      · first | cases h | (obtain ⟨_, h', -⟩ := bind_ok_FR h; cases h')
  · first | cases h | (obtain ⟨_, h', -⟩ := bind_ok_FR h; cases h')

/-- The clauses of `frClauses` give the patterns back. -/
theorem frClauses_pats {s s' : Srt} {vars vars' : List Srt} {pats pats' : List Term} {req req' : Option Term}
    {prio prio' : Nat} {aside aside' : Bool} {alts alts' : List (Term × List Cond)}
    (h : Parse.frClauses s vars pats req prio aside alts = Parse.frClauses s' vars' pats' req' prio' aside' alts') :
    pats = pats' := by
  have := congrArg (fun l => l.getLast?.map Clause.pats) h
  simpa [Parse.frClauses] using this

theorem varOccsList_eq_flatMap : ∀ ts : List Term, varOccsList ts = ts.flatMap varOccs
  | [] => by rw [varOccsList]; rfl
  | t :: ts => by rw [varOccsList, List.flatMap_cons, varOccsList_eq_flatMap ts]

theorem varOccsCond_isTrue (n : Nat) (b : Term) : varOccsCond n (Parse.isTrueC b) = varOccs b := by
  simp [Parse.isTrueC, Parse.boolT, varOccsCond, varOccs]

/-- **Every variable of an alternative of the clauses `frRead` reads occurs in their patterns**,
and there is an alternative: `gamma_shapeFG`'s `hxs` and `hocc`, for the clauses given as
`frClauses … (frAltsOf xs)`. The reader numbers the variables of the head's patterns first
(`svinPats_occ`), and accepts an alternative, its conditions, the lifted conditions and the
`ensures` only over those (`frRead_occInv`). -/
theorem occ_of_frRead {N : Parse.Names} {eq : Parse.RawEqn} {z : List Clause × List Var}
    (hrd : Parse.frRead N eq = .ok (some z)) {s : Srt} {vars : List Srt} {pats : List Term}
    {req : Option Term} {prio : Nat} {aside : Bool} {xs : List (Term × List Term)}
    (hz : z.1 = Parse.frClauses s vars pats req prio aside (frAltsOf xs)) :
    xs ≠ [] ∧ ∀ x ∈ xs, ∀ i ∈ varOccsList (x.1 :: x.2), i ∈ varOccsList pats := by
  obtain ⟨pats0, req0, ens, vs0, np, ts, vs1, alts, s0, vars0, hhead, hal, h2, hb, hz0⟩ := frRead_occInv hrd
  obtain ⟨-, ys, rfl, -⟩ := altsOf_inv (c := semOf N) (tbl := []) (tblT := []) (vars := []) (vsF := [])
    rfl rfl rfl hal
  have hz1 : z.1 = Parse.frClauses s0 vars0 pats0 req0 (Parse.eqnPrio eq).2 (Parse.nonExec eq)
      (frAltsOf (ys.map fun y => (y.1, (ens.toList ++ ts) ++ y.2))) := by
    rw [hz0]
    congr 1
    simp [frAltsOf, List.map_map, Function.comp_def]
  rw [hz1] at hz
  have hxs := (frClauses_inj hz).1
  have hp := frClauses_pats hz
  subst hxs hp
  obtain ⟨vsP, hsv, rfl⟩ := eqnHead_pats hhead
  refine ⟨fun he => h2 ?_, fun x hx i hi => svinPats_occ hsv i (hb i ?_)⟩
  · rw [List.map_eq_nil_iff] at he
    subst he
    simp
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simp only [varOccsList_eq_flatMap, List.flatMap_cons, List.flatMap_append, List.mem_append] at hi
    simp only [List.mem_append, List.mem_flatMap, List.mem_map]
    rcases hi with hi | (hi | hi) | hi
    · exact .inl ⟨_, ⟨y, hy, rfl⟩, .inl hi⟩
    · obtain ⟨b, hb', hi⟩ := List.mem_flatMap.mp hi
      exact .inr ⟨b, .inl hb', hi⟩
    · obtain ⟨b, hb', hi⟩ := List.mem_flatMap.mp hi
      exact .inr ⟨b, .inr hb', hi⟩
    · obtain ⟨b, hb', hi⟩ := List.mem_flatMap.mp hi
      exact .inl ⟨_, ⟨y, hy, rfl⟩, .inr ⟨_, List.mem_map.mpr ⟨b, hb', rfl⟩, by rw [varOccsCond_isTrue]; exact hi⟩⟩

/-! ## The sorts, from the definition's well-sortedness -/

/-- The clause check of every clause of a function of a definition `sortedOK` accepts. -/
theorem clauseSorted_of_sortedOK {c : Semantics} (h : c.sortedOK = true) {f : Fn} (hf : f ∈ c.fns) :
    ∀ cl ∈ f.clauses, c.clauseSorted f (c.fns.map Fn.sig) cl = true := by
  have hs := Semantics.sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  exact hs.1.2 f hf

/-- **The sorts of the clauses `frClauses` writes**, where the clause check holds of them: each
alternative has the function's result sort (the clause's right side), and there is a pattern for
each argument (the clause's patterns have the argument sorts). -/
theorem sorted_of_frClauses {c : Semantics} {f : Fn} {s : Srt} {vars : List Srt} {pats : List Term}
    {req : Option Term} {prio : Nat} {aside : Bool} {xs : List (Term × List Term)}
    (hcs : ∀ cl ∈ Parse.frClauses s vars pats req prio aside (frAltsOf xs),
      c.clauseSorted f (c.fns.map Fn.sig) cl = true) :
    (∀ x ∈ xs, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars x.1 = some f.result) ∧
      pats.length = f.args.length := by
  rw [frClauses_eq] at hcs
  refine ⟨fun x hx => ?_, ?_⟩
  · have h := hcs _ (List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1.2
  · have h := hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at h
    exact sortsOfTerms_length h.1.1.1.1.1.1

/-- **`gamma_shapeFG`'s premises, from the reader and the clause check**: an alternative at least,
a pattern for each argument, and every variable of an alternative in the patterns. -/
theorem gammaPrem_of_frRead {c : Semantics} {f : Fn} {N : Parse.Names} {eq : Parse.RawEqn}
    {z : List Clause × List Var} (hrd : Parse.frRead N eq = .ok (some z)) {s : Srt} {vars : List Srt}
    {pats : List Term} {req : Option Term} {prio : Nat} {aside : Bool} {xs : List (Term × List Term)}
    (hz : z.1 = Parse.frClauses s vars pats req prio aside (frAltsOf xs))
    (hcs : ∀ cl ∈ z.1, c.clauseSorted f (c.fns.map Fn.sig) cl = true) :
    xs ≠ [] ∧ pats.length = f.args.length ∧
      ∀ x ∈ xs, ∀ i ∈ varOccsList (x.1 :: x.2), i ∈ varOccsList pats :=
  have ho := occ_of_frRead hrd hz
  ⟨ho.1, (sorted_of_frClauses (by rw [← hz]; exact hcs)).2, ho.2⟩

/-! ## The variables in their sorts -/

/-- The variables `varSorts` numbers the sorts of: as many sorts as variables, each the one
numbered for its variable's sort. -/
theorem varSorts_spec {N : Parse.Names} : ∀ {vsF : List Var} {vars : List Srt},
    Parse.varSorts N vsF = .ok vars →
    vars.length = vsF.length ∧ ∀ i < vsF.length, N.srtE (vsF.getD i default).sort = .ok (vars.getD i 0)
  | [], vars, h => by
    unfold Parse.varSorts at h
    rw [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | v :: vs, vars, h => by
    unfold Parse.varSorts at h
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    obtain ⟨hl, hi⟩ := varSorts_spec (N := N) (vsF := vs) hbs
    refine ⟨by simp [hl], fun i hi' => ?_⟩
    cases i with
    | zero => simpa using hb
    | succ i => simpa using hi i (by simpa using hi')

/-- The guards hold the membership of every variable read in its sort, over the text's table. -/
def guardsHold (ws : List P) (tblT : VarTable) (vsF : List Var) : Bool :=
  vsF.all fun v => decide (guardOf tblT (evarKey v.kore) ∈ ws)

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A variable read lies in its sort where the guards hold**: the guards hold its membership in
its sort over the text's table (`guardsHold`), the table `tbl` holds it where the text's does
(`alignOK`), and `varSorts` numbers its sort. -/
theorem inS_of_guards (hD : DefOK I) {N : Parse.Names} {c : Semantics} (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
    (hvars : Parse.varSorts N vsF = .ok vars) (hA : alignOK c tbl tblT vars vsF = true)
    {ws : List P} (hg : guardsHold ws tblT vsF = true) {e : Valuation M} {m : M}
    (hw : ∀ w ∈ ws, w.interpret I e m) {i : Nat} (hi : i < vsF.length) :
    InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))) := by
  have hv : vsF.getD i default ∈ vsF := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have h := hw _ (of_decide_eq_true (List.all_eq_true.mp hg _ hv))
  have hk : guardOf tblT (evarKey (vsF.getD i default).kore) =
      (tblT.ev (evarKey (vsF.getD i default).kore) ∈∈
        inhOf (KoreAML.Cons.sortP (vsF.getD i default).sort)) := by
    simp only [evarKey, Var.kore, guardOf]
    rfl
  rw [hk, interp_member hD] at h
  rw [alignOK_spec hA hi, sortName_of_srt hso (srtE_ok ((varSorts_spec hvars).2 i hi))]
  exact (Faithful.inS_iff e).mp h

/-- **The variables of a term of a sort lie in their sorts where the guards hold** (`hvar`): a
term with a sort over `vars` holds only variables `varSorts` numbers (`varOccs_lt`). -/
theorem hvar_of_sorted (hD : DefOK I) {N : Parse.Names} {c : Semantics} (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
    (hvars : Parse.varSorts N vsF = .ok vars) (hA : alignOK c tbl tblT vars vsF = true)
    {ws : List P} (hg : guardsHold ws tblT vsF = true) {e : Valuation M} {m : M}
    (hw : ∀ w ∈ ws, w.interpret I e m) {x : TermCtx} {t : Term} {s : Srt}
    (hty : sortOfTerm x vars t = some s) :
    ∀ i ∈ varOccs t, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))) :=
  fun i hi => inS_of_guards hD hso hvars hA hg hw
    (by rw [← (varSorts_spec hvars).1]; exact varOccs_lt t hty i hi)

/-- **The alternatives lie in the function's result sort** (`inSort_of_terms`'s conclusion, the
`hin` of `readings_of_frT`), from `TermsInSort`, the clause check of the clauses `frClauses`
writes (`hty`) and the guards (`hvar`). -/
theorem inSort_of_read {N : Parse.Names} {c : Semantics} (hD : DefOK I) (hTS : Faithful.TermsInSort c I)
    (hso : N.sorts = c.sortNames) {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
    (hvars : Parse.varSorts N vsF = .ok vars) (hA : alignOK c tbl tblT vars vsF = true)
    {ws : List P} {r : EVar} (hg : guardsHold ws tblT vsF = true)
    {f : Fn} {s : Srt} {pats : List Term} {req : Option Term} {prio : Nat} {aside : Bool}
    {xs : List (Term × List Term)}
    (hcs : ∀ cl ∈ Parse.frClauses s vars pats req prio aside (frAltsOf xs),
      c.clauseSorted f (c.fns.map Fn.sig) cl = true)
    (hs : f.result < nRegSorts + c.sortNames.length) {σ : M}
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c f.result)).interpret I e a ↔ a = σ) :
    ∀ e m, TieFR.At I ws r e m → ∀ x ∈ xs, ∀ a, (altP c tbl (canonVars c vars) x).interpret I e a → Inh I σ a :=
  inSort_of_terms hTS hs hσ (sorted_of_frClauses hcs).1
    (fun _ _ hat x hx => hvar_of_sorted hD hso hvars hA hg hat.1 ((sorted_of_frClauses hcs).1 x hx))

/-- **An operand read as a term of the sort s lies in s** (`inSortK_of_read`), the variables of the
term in their sorts from the guards (`hvar_of_sorted`). -/
theorem inSortK_of_readG {N : Parse.Names} {c : Semantics} (hD : DefOK I) (hTS : Faithful.TermsInSort c I)
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames) {tbl tblT : VarTable} {vars : List Srt}
    {vsF : List Var} (hvars : Parse.varSorts N vsF = .ok vars) (hA : alignOK c tbl tblT vars vsF = true)
    {ws : List P} (hg : guardsHold ws tblT vsF = true) {e : Valuation M} {m : M}
    (hw : ∀ w ∈ ws, w.interpret I e m) {vs vs' : List Var} {s : Srt} {t : Term} {S : Kore.KSort}
    {q : Kore.Pattern} (hrd : Parse.term N vs q = .ok (t, vs')) (hrt : rtPat N q = true) (hp : vs' <+: vsF)
    (hs : s < nRegSorts + c.sortNames.length) (hty : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (hS : trSort tblT S = trSort tbl (srtOf c s)) :
    InSortK I tblT e S q :=
  inSortK_of_read hsy hso hTS hA hrd hrt hp hs hty hS (hvar_of_sorted hD hso hvars hA hg hw hty)

end

end TieFRVars

end KCore
