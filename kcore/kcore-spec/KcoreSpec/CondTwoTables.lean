/-
  KCore. A condition's predicate under two tables.

  `Cond.kore c vs S p` is read through a variable table (`KoreAML.tr ⟨tbl, []⟩`). Two readings,
  through tables tbl and tbl' at valuations e and e', denote one set where the two valuations give
  each free variable of p one element through the two tables, and the keys of the pattern's
  variables, its binders included, are in both tables (`tr_condKore_twoT`). The sorts a condition
  names are constants, so they denote alike under every table and valuation; the connectives and
  `\ceil`, `\equals`, `\in` read the sets their operands denote (`eqv_sNot_twoT`, …); a binder is
  given one element under both readings, and its key, in both tables, is apart from the free
  variables' keys. The terms are read by `tr_kore_congr`.
-/
import KcoreSpec.HoldsFacts

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

section
variable {M : Type} {I : Interpretation KoreAML.Sym M} {e e' : Valuation M}

/-- A sort named by `srtOf` is the same constant under every table. -/
theorem trSort_srtOf_twoT (c : Semantics) (tbl : VarTable) (s : Srt) :
    KoreAML.trSort tbl (srtOf c s) = KoreAML.sym (.sort ("Sort" ++ c.sortName s)) := by
  unfold srtOf; exact trSort_srt _

theorem closed_inhOf_twoT {s : KoreAML.P} (hs : KoreAML.Closed s) : KoreAML.Closed (KoreAML.inhOf s) :=
  (KoreAML.Closed.sym _).app hs

theorem eqv_sNot_twoT {s φ φ' : KoreAML.P} (hs : KoreAML.Closed s)
    (h : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) :
    ∀ m, (KoreAML.sNot s φ).interpret I e m ↔ (KoreAML.sNot s φ').interpret I e' m := fun m => by
  rw [KoreAML.interp_sNot, KoreAML.interp_sNot, h m, (closed_inhOf_twoT hs).interp e e' m]

theorem eqv_sAnd_twoT {φ φ' ψ ψ' : KoreAML.P}
    (h1 : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (h2 : ∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) :
    ∀ m, (KoreAML.sAnd φ ψ).interpret I e m ↔ (KoreAML.sAnd φ' ψ').interpret I e' m := fun m => by
  rw [KoreAML.interp_sAnd, KoreAML.interp_sAnd, h1 m, h2 m]

theorem eqv_sOr_twoT {s φ φ' ψ ψ' : KoreAML.P} (hs : KoreAML.Closed s)
    (h1 : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (h2 : ∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) :
    ∀ m, (KoreAML.sOr s φ ψ).interpret I e m ↔ (KoreAML.sOr s φ' ψ').interpret I e' m := fun m => by
  rw [KoreAML.interp_sOr, KoreAML.interp_sOr, h1 m, h2 m, (closed_inhOf_twoT hs).interp e e' m]

theorem eqv_sImp_twoT {s φ φ' ψ ψ' : KoreAML.P} (hs : KoreAML.Closed s)
    (h1 : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (h2 : ∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) :
    ∀ m, (KoreAML.sImp s φ ψ).interpret I e m ↔ (KoreAML.sImp s φ' ψ').interpret I e' m := fun m => by
  rw [KoreAML.interp_sImp, KoreAML.interp_sImp, h1 m, h2 m, (closed_inhOf_twoT hs).interp e e' m]

theorem eqv_sIff_twoT {s φ φ' ψ ψ' : KoreAML.P} (hs : KoreAML.Closed s)
    (h1 : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (h2 : ∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) :
    ∀ m, (KoreAML.sIff s φ ψ).interpret I e m ↔ (KoreAML.sIff s φ' ψ').interpret I e' m := fun m => by
  rw [KoreAML.interp_sIff, KoreAML.interp_sIff, h1 m, h2 m, (closed_inhOf_twoT hs).interp e e' m]

theorem eqv_sCeil_twoT {s s' φ φ' : KoreAML.P} (hs : KoreAML.Closed s) (hs' : KoreAML.Closed s')
    (h : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) :
    ∀ m, (KoreAML.sCeil s s' φ).interpret I e m ↔ (KoreAML.sCeil s s' φ').interpret I e' m := by
  unfold KoreAML.sCeil
  exact KoreAML.interp_app_congr (KoreAML.interp_app_congr (KoreAML.interp_app_congr
    ((KoreAML.Closed.sym _).interp e e') (hs.interp e e')) (hs'.interp e e')) h

theorem eqv_sEquals_twoT {s s' φ φ' ψ ψ' : KoreAML.P} (hs : KoreAML.Closed s) (hs' : KoreAML.Closed s')
    (h1 : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (h2 : ∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) :
    ∀ m, (KoreAML.sEquals s s' φ ψ).interpret I e m ↔ (KoreAML.sEquals s s' φ' ψ').interpret I e' m := by
  unfold KoreAML.sEquals KoreAML.sFloor
  exact eqv_sNot_twoT hs' (eqv_sCeil_twoT hs hs' (eqv_sNot_twoT hs (eqv_sIff_twoT hs h1 h2)))

theorem eqv_sIn_twoT {s s' φ φ' ψ ψ' : KoreAML.P} (hs : KoreAML.Closed s) (hs' : KoreAML.Closed s')
    (h1 : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (h2 : ∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m) :
    ∀ m, (KoreAML.sIn s s' φ ψ).interpret I e m ↔ (KoreAML.sIn s s' φ' ψ').interpret I e' m := by
  unfold KoreAML.sIn
  exact eqv_sCeil_twoT hs hs' (eqv_sAnd_twoT h1 h2)

/-- A sorted binder, read through two tables: where the bodies denote one set whenever the binders
are given one element of the sort, the two `\exists` denote one set. -/
theorem eqv_sExists_twoT (hD : KoreAML.DefOK I) {x x' : EVar} {s φ φ' : KoreAML.P} (hs : KoreAML.Closed s)
    (h : ∀ a, (KoreAML.inhOf s).interpret I e a → ∀ m,
      φ.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m ↔
        φ'.interpret I ⟨Function.update e'.evalEvar x' a, e'.evalSvar⟩ m) :
    ∀ m, (KoreAML.sExists x s φ).interpret I e m ↔ (KoreAML.sExists x' s φ').interpret I e' m := fun m => by
  rw [KoreAML.interp_sExists, KoreAML.interp_sExists]
  simp only [KoreAML.interp_member hD, Function.update_same]
  constructor
  · rintro ⟨a, ha, hb⟩
    have ha0 := ((closed_inhOf_twoT hs).interp _ e a).mp ha
    exact ⟨a, ((closed_inhOf_twoT hs).interp e _ a).mp ha0, (h a ha0 m).mp hb⟩
  · rintro ⟨a, ha, hb⟩
    have ha0 := ((closed_inhOf_twoT hs).interp _ e a).mp ha
    exact ⟨a, ((closed_inhOf_twoT hs).interp e _ a).mp ha0, (h a ha0 m).mpr hb⟩

end

section
variable {c : Semantics}

/-- The free variables of a well-sorted condition are in scope. -/
theorem varOccsCond_lt_twoT : ∀ (p : Cond) {vars : List Srt}, c.condOK vars p = true →
    ∀ i ∈ varOccsCond vars.length p, i < vars.length
  | .top, _, _, i, hi => by simp [varOccsCond] at hi
  | .bot, _, _, i, hi => by simp [varOccsCond] at hi
  | .not p, vars, hok, i, hi => by
    rw [Semantics.condOK] at hok; rw [varOccsCond] at hi
    exact varOccsCond_lt_twoT p hok i hi
  | .and p q, vars, hok, i, hi | .or p q, vars, hok, i, hi | .implies p q, vars, hok, i, hi => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok; rw [varOccsCond, List.mem_append] at hi
    rcases hi with hi | hi
    · exact varOccsCond_lt_twoT p hok.1 i hi
    · exact varOccsCond_lt_twoT q hok.2 i hi
  | .ceil s t, vars, hok, i, hi => by
    rw [Semantics.condOK, beq_iff_eq] at hok; rw [varOccsCond] at hi
    exact varOccs_lt t hok i hi
  | .equals s t u, vars, hok, i, hi | .mem s t u, vars, hok, i, hi => by
    rw [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond, List.mem_append] at hi
    rcases hi with hi | hi
    · exact varOccs_lt t hok.1 i hi
    · exact varOccs_lt u hok.2 i hi
  | .exMatch ys s p t body, vars, hok, i, hi => by
    rw [Semantics.condOK, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [varOccsCond, List.mem_append] at hi
    rcases hi with hi | hi
    · exact varOccs_lt t hok.1.2 i hi
    · have h2 := (List.mem_filter.mp hi).2; simpa using h2
  | .ex s body, vars, hok, i, hi | .all s body, vars, hok, i, hi => by
    rw [varOccsCond] at hi
    have h2 := (List.mem_filter.mp hi).2; simpa using h2

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- Under one more binder, given one element under both readings: the body's two readings denote one
set, where the binder's key is in both tables and the outer free variables agree. -/
theorem binderBody_twoT {vars : List Srt} {s S : Srt} {body : Cond} {tbl tbl' : VarTable} {e e' : Valuation M}
    (hok : c.condOK (vars ++ [s]) body = true)
    (hK : canonKey c (vars ++ [s]) vars.length ∈ tbl ∧ canonKey c (vars ++ [s]) vars.length ∈ tbl')
    (hf : ∀ i ∈ varOccsCond (vars.length + 1) body, i < vars.length → canonKey c vars i ∈ tbl ∧
      canonKey c vars i ∈ tbl' ∧ e.evalEvar (tbl.ev (canonKey c vars i)) = e'.evalEvar (tbl'.ev (canonKey c vars i)))
    (ih : ∀ {e₁ e₁' : Valuation M}, (∀ i ∈ varOccsCond (vars ++ [s]).length body, canonKey c (vars ++ [s]) i ∈ tbl ∧
      canonKey c (vars ++ [s]) i ∈ tbl' ∧
      e₁.evalEvar (tbl.ev (canonKey c (vars ++ [s]) i)) = e₁'.evalEvar (tbl'.ev (canonKey c (vars ++ [s]) i))) →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I e₁ m ↔
        (KoreAML.tr ⟨tbl', []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I e₁' m)
    (a : M) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev (canonKey c (vars ++ [s]) vars.length)) a, e.evalSvar⟩ m ↔
      (KoreAML.tr ⟨tbl', []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e'.evalEvar (tbl'.ev (canonKey c (vars ++ [s]) vars.length)) a, e'.evalSvar⟩ m := by
  apply ih
  intro i hi
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hlt := varOccsCond_lt_twoT body hok i hi
  rw [hlen] at hlt hi
  by_cases hin : i < vars.length
  · obtain ⟨h1, h2, h3⟩ := hf i hi hin
    have hk' := Model.canonKey_appendStdI (c := c) (ys := [s]) hin
    rw [hk']
    refine ⟨h1, h2, ?_⟩
    show Function.update e.evalEvar _ a _ = Function.update e'.evalEvar _ a _
    rw [Function.update_noteq, Function.update_noteq]
    · exact h3
    · intro he
      have := canonKey_inj (c := c) (vars := vars ++ [s]) (i := i) (j := vars.length) (by simp; omega) (by simp)
        (hk'.trans (ev_inj h2 hK.2 he))
      omega
    · intro he
      have := canonKey_inj (c := c) (vars := vars ++ [s]) (i := i) (j := vars.length) (by simp; omega) (by simp)
        (hk'.trans (ev_inj h1 hK.1 he))
      omega
  · have hi' : i = vars.length := by omega
    subst hi'
    refine ⟨hK.1, hK.2, ?_⟩
    show Function.update e.evalEvar _ a _ = Function.update e'.evalEvar _ a _
    rw [Function.update_same, Function.update_same]

omit [Inhabited M] in
/-- `existsAll` read through two tables: where the valuations agree at the keys `Ks`, every key of
`Ks` and of the binders is in both tables, and the bodies denote one set wherever the valuations agree
at `Ks` and the binders, the two readings denote one set. -/
theorem existsAll_twoT (hD : KoreAML.DefOK I) {S : Kore.KSort} {body : Kore.Pattern} {tbl tbl' : VarTable} :
    ∀ (bs : List Kore.EVar) (Ks : List KoreAML.VarKey) {e e' : Valuation M},
    (∀ b ∈ bs, KoreAML.evarKey b ∈ tbl ∧ KoreAML.evarKey b ∈ tbl') → (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (∀ k ∈ Ks, k ∈ tbl ∧ k ∈ tbl') → (∀ k ∈ Ks, e.evalEvar (tbl.ev k) = e'.evalEvar (tbl'.ev k)) →
    (∀ e₁ e₁' : Valuation M, (∀ k ∈ Ks ++ bs.map KoreAML.evarKey, e₁.evalEvar (tbl.ev k) = e₁'.evalEvar (tbl'.ev k)) →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ body).interpret I e₁ m ↔ (KoreAML.tr ⟨tbl', []⟩ body).interpret I e₁' m) →
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)).interpret I e m ↔
      (KoreAML.tr ⟨tbl', []⟩ (KoreAML.existsAll S bs body)).interpret I e' m
  | [], Ks, e, e', _, _, _, hag, hb => hb e e' (by simpa using hag)
  | b :: bs, Ks, e, e', hbin, hsrt, hKs, hag, hb => by
    intro m
    show (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret I e m ↔
      (KoreAML.tr ⟨tbl', []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret I e' m
    obtain ⟨n, hn⟩ := hsrt b (List.mem_cons_self ..)
    have hkb := hbin b (List.mem_cons_self ..)
    rw [KoreAML.tr, KoreAML.tr, hn, trSort_srt, trSort_srt]
    refine eqv_sExists_twoT hD (KoreAML.Closed.sym _) (fun a _ => ?_) m
    refine existsAll_twoT hD bs (Ks ++ [KoreAML.evarKey b]) (fun b' hb' => hbin b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => hsrt b' (List.mem_cons_of_mem _ hb')) (fun k hk => ?_) (fun k hk => ?_)
      (fun e₁ e₁' h => hb e₁ e₁' fun k hk => h k ?_)
    · rcases List.mem_append.mp hk with hk | hk
      · exact hKs k hk
      · rw [List.mem_singleton.mp hk]; exact hkb
    · show Function.update e.evalEvar _ a _ = Function.update e'.evalEvar _ a _
      by_cases hk' : k = KoreAML.evarKey b
      · rw [hk', Function.update_same, Function.update_same]
      · have hkK : k ∈ Ks := by
          rcases List.mem_append.mp hk with hk | hk
          · exact hk
          · exact absurd (List.mem_singleton.mp hk) hk'
        rw [Function.update_noteq (fun he => hk' (ev_inj (hKs k hkK).1 hkb.1 he)),
          Function.update_noteq (fun he => hk' (ev_inj (hKs k hkK).2 hkb.2 he))]
        exact hag k hkK
    · simp only [List.map_cons, List.mem_append, List.mem_cons] at hk ⊢
      rcases hk with hk | hk | hk
      · exact Or.inl (Or.inl hk)
      · exact Or.inl (Or.inr (Or.inl hk))
      · exact Or.inr hk

omit [Inhabited M] in
/-- **A condition's predicate under two tables.** Where the keys of the pattern's variables are in
both tables and the two valuations give each free variable of p one element through the two
tables, the two readings denote one set. -/
theorem tr_condKore_twoT (hD : KoreAML.DefOK I) : ∀ (p : Cond) {vars : List Srt} {tbl tbl' : VarTable}
    {e e' : Valuation M} {S : Srt}, c.condOK vars p = true →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl ∧ k ∈ tbl') →
    (∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧ canonKey c vars i ∈ tbl' ∧
      e.evalEvar (tbl.ev (canonKey c vars i)) = e'.evalEvar (tbl'.ev (canonKey c vars i))) →
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e m ↔
      (KoreAML.tr ⟨tbl', []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e' m
  | .top, vars, tbl, tbl', e, e', S, _, _, _ => fun m => by
    rw [Cond.kore, KoreAML.tr, KoreAML.tr, KoreAML.interp_sTop hD Model.srtOf_free_stdI,
      KoreAML.interp_sTop hD Model.srtOf_free_stdI, trSort_srtOf_twoT, trSort_srtOf_twoT]
    exact (closed_inhOf_twoT (KoreAML.Closed.sym _)).interp e e' m
  | .bot, vars, tbl, tbl', e, e', S, _, _, _ => fun m => by
    rw [Cond.kore, KoreAML.tr, KoreAML.tr]
    unfold KoreAML.sBot
    rw [KoreAML.interp_sNot, KoreAML.interp_sNot, KoreAML.interp_sTop hD Model.srtOf_free_stdI,
      KoreAML.interp_sTop hD Model.srtOf_free_stdI, trSort_srtOf_twoT, trSort_srtOf_twoT,
      (closed_inhOf_twoT (KoreAML.Closed.sym _)).interp e e' m]
  | .not p, vars, tbl, tbl', e, e', S, hok, hk, hf => by
    rw [Semantics.condOK] at hok
    have ih := tr_condKore_twoT hD p (S := S) hok (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)) (fun i hi => hf i (by rw [varOccsCond]; exact hi))
    rw [Cond.kore, KoreAML.tr, KoreAML.tr, trSort_srtOf_twoT, trSort_srtOf_twoT]
    exact eqv_sNot_twoT (KoreAML.Closed.sym _) ih
  | .and p q, vars, tbl, tbl', e, e', S, hok, hk, hf => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := tr_condKore_twoT hD p (S := S) hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_left _ hk0)))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi))
    have ihq := tr_condKore_twoT hD q (S := S) hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0))))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi))
    rw [Cond.kore, tr_and2, tr_and2]
    exact eqv_sAnd_twoT ihp ihq
  | .or p q, vars, tbl, tbl', e, e', S, hok, hk, hf => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := tr_condKore_twoT hD p (S := S) hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_left _ hk0)))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi))
    have ihq := tr_condKore_twoT hD q (S := S) hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0))))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi))
    rw [Cond.kore, Model.tr_or2Stdi, Model.tr_or2Stdi]
    simp only [trSort_srtOf_twoT]
    exact eqv_sOr_twoT (KoreAML.Closed.sym _) ihp ihq
  | .implies p q, vars, tbl, tbl', e, e', S, hok, hk, hf => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := tr_condKore_twoT hD p (S := S) hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk0)))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi))
    have ihq := tr_condKore_twoT hD q (S := S) hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi))
    rw [Cond.kore, KoreAML.tr, KoreAML.tr, trSort_srtOf_twoT, trSort_srtOf_twoT]
    exact eqv_sImp_twoT (KoreAML.Closed.sym _) ihp ihq
  | .ceil s t, vars, tbl, tbl', e, e', S, _, _, hf => by
    rw [Cond.kore, KoreAML.tr, KoreAML.tr]
    simp only [trSort_srtOf_twoT]
    exact eqv_sCeil_twoT (KoreAML.Closed.sym _) (KoreAML.Closed.sym _)
      (tr_kore_congr t fun i hi => (hf i (by rw [varOccsCond]; exact hi)).2.2)
  | .equals s t u, vars, tbl, tbl', e, e', S, _, _, hf => by
    rw [Cond.kore, KoreAML.tr, KoreAML.tr]
    simp only [trSort_srtOf_twoT]
    exact eqv_sEquals_twoT (KoreAML.Closed.sym _) (KoreAML.Closed.sym _)
      (tr_kore_congr t fun i hi => (hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi)).2.2)
      (tr_kore_congr u fun i hi => (hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi)).2.2)
  | .mem s t u, vars, tbl, tbl', e, e', S, _, _, hf => by
    rw [Cond.kore, KoreAML.tr, KoreAML.tr]
    simp only [trSort_srtOf_twoT]
    exact eqv_sIn_twoT (KoreAML.Closed.sym _) (KoreAML.Closed.sym _)
      (tr_kore_congr t fun i hi => (hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi)).2.2)
      (tr_kore_congr u fun i hi => (hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi)).2.2)
  | .exMatch ys s p t body, vars, tbl, tbl', e, e', S, hok, hk, hf => by
    rw [Semantics.condOK, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    obtain ⟨⟨hpS, -⟩, hbody⟩ := hok
    let bs := ((List.range ys.length).zip ys).map fun (j, y) => Cond.binder c ((canonVars c vars).length + j) y
    have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.exMatch ys s p t body) =
        KoreAML.existsAll (srtOf c S) (bs.map KoreAML.Var.kore) (.and (srtOf c S)
          [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
           Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body]) := by
      rw [← Model.canonVars_appendStdI c vars ys]; rfl
    rw [hkore] at hk ⊢
    have hlen : (vars ++ ys).length = vars.length + ys.length := by simp
    have hbl : bs.length = ys.length := by simp [bs]
    have hbkey : ∀ i, vars.length ≤ i → i < vars.length + ys.length →
        canonKey c (vars ++ ys) i ∈ (bs.map KoreAML.Var.kore).map KoreAML.evarKey := by
      intro i h1 h2
      unfold canonKey
      rw [← Model.canonVars_appendStdI c vars ys,
        Model.getD_appendR_stdI _ _ _ (by rw [canonVars_length]; exact h1)]
      show KoreAML.evarKey ((bs.getD (i - (canonVars c vars).length) default).kore) ∈ _
      rw [canonVars_length]
      have hlt : i - vars.length < bs.length := by rw [hbl]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.mem_map_of_mem (List.mem_map_of_mem (List.getElem_mem hlt))
    have hbin : ∀ b ∈ bs.map KoreAML.Var.kore, KoreAML.evarKey b ∈ tbl ∧ KoreAML.evarKey b ∈ tbl' :=
      fun b hb => hk _ (varsOf_existsAll_binder _ hb)
    have hbin' : ∀ k ∈ (bs.map KoreAML.Var.kore).map KoreAML.evarKey, k ∈ tbl ∧ k ∈ tbl' := fun k hk0 => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk0; exact hbin b hb
    have hsrt : ∀ b ∈ bs.map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      obtain ⟨⟨j, y⟩, -, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, rfl⟩
    let Ks := (varOccsCond vars.length (.exMatch ys s p t body)).map (canonKey c vars)
    have hKs : ∀ k ∈ Ks, k ∈ tbl ∧ k ∈ tbl' := fun k hk0 => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk0; exact ⟨(hf i hi).1, (hf i hi).2.1⟩
    have hKe : ∀ k ∈ Ks, e.evalEvar (tbl.ev k) = e'.evalEvar (tbl'.ev k) := fun k hk0 => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk0; exact (hf i hi).2.2
    have hinK : ∀ i, i ∈ varOccsCond vars.length (.exMatch ys s p t body) → canonKey c vars i ∈ Ks :=
      fun i hi => List.mem_map_of_mem hi
    refine existsAll_twoT hD _ Ks hbin hsrt hKs hKe fun e₁ e₁' hag => ?_
    rw [tr_and2, tr_and2]
    refine eqv_sAnd_twoT ?_ ?_
    · rw [KoreAML.tr, KoreAML.tr]
      simp only [trSort_srtOf_twoT]
      refine eqv_sIn_twoT (KoreAML.Closed.sym _) (KoreAML.Closed.sym _)
        (tr_kore_congr t fun i hi => hag _ (List.mem_append_left _ (hinK i (by
          rw [varOccsCond]; exact List.mem_append_left _ hi))))
        (tr_kore_congr p fun i hi => ?_)
      have hlt := varOccs_lt p hpS i hi
      rw [hlen] at hlt
      show e₁.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)) = e₁'.evalEvar (tbl'.ev (canonKey c (vars ++ ys) i))
      by_cases hin : i < vars.length
      · rw [Model.canonKey_appendStdI hin]
        exact hag _ (List.mem_append_left _ (hinK i (by
          rw [varOccsCond]
          exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append_left _ hi, by simpa using hin⟩))))
      · exact hag _ (List.mem_append_right _ (hbkey i (by omega) hlt))
    · refine tr_condKore_twoT hD body (S := S) hbody (fun k hk0 => hk k (HoldsShape.varsOf_existsAll_bodyHF
        (Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk0) _)) fun i hi => ?_
      have hlt := varOccsCond_lt_twoT body hbody i hi
      rw [hlen] at hlt hi
      by_cases hin : i < vars.length
      · rw [Model.canonKey_appendStdI hin]
        have hiO : i ∈ varOccsCond vars.length (.exMatch ys s p t body) := by
          rw [varOccsCond]
          exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append_right _ hi, by simpa using hin⟩)
        exact ⟨(hf i hiO).1, (hf i hiO).2.1, hag _ (List.mem_append_left _ (hinK i hiO))⟩
      · have hb := hbkey i (by omega) hlt
        exact ⟨(hbin' _ hb).1, (hbin' _ hb).2, hag _ (List.mem_append_right _ hb)⟩
  | .ex s body, vars, tbl, tbl', e, e', S, hok, hk, hf => by
    rw [Semantics.condOK] at hok
    have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.ex s body) =
        .exist (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
          (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
      rw [← Model.canonVars_snocStdI c vars s]; rfl
    rw [hkore] at hk
    have hkb := Model.binder_keyStdI (c := c) vars s
    have hK := hk (canonKey c (vars ++ [s]) vars.length) (by rw [KoreAML.varsOf, hkb]; simp)
    have hbs : (Cond.binder c (canonVars c vars).length s).kore.sort = srtOf c s := rfl
    rw [hkore, KoreAML.tr, KoreAML.tr, hbs, hkb, trSort_srtOf_twoT, trSort_srtOf_twoT]
    exact eqv_sExists_twoT hD (KoreAML.Closed.sym _) fun a _ => binderBody_twoT hok hK
      (fun i hi hl => hf i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hl⟩))
      (fun h1 => tr_condKore_twoT hD body (S := S) hok
        (fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)) h1) a
  | .all s body, vars, tbl, tbl', e, e', S, hok, hk, hf => by
    rw [Semantics.condOK] at hok
    have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.all s body) =
        .forall (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
          (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
      rw [← Model.canonVars_snocStdI c vars s]; rfl
    rw [hkore] at hk
    have hkb := Model.binder_keyStdI (c := c) vars s
    have hK := hk (canonKey c (vars ++ [s]) vars.length) (by rw [KoreAML.varsOf, hkb]; simp)
    have hbs : (Cond.binder c (canonVars c vars).length s).kore.sort = srtOf c s := rfl
    rw [hkore, KoreAML.tr, KoreAML.tr, hbs, hkb]
    simp only [trSort_srtOf_twoT]
    unfold KoreAML.sForall
    exact eqv_sNot_twoT (KoreAML.Closed.sym _) (eqv_sExists_twoT hD (KoreAML.Closed.sym _) fun a _ =>
      eqv_sNot_twoT (KoreAML.Closed.sym _) (binderBody_twoT hok hK
        (fun i hi hl => hf i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hl⟩))
        (fun h1 => tr_condKore_twoT hD body (S := S) hok
          (fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)) h1) a))

end

end Faithful

end KCore
