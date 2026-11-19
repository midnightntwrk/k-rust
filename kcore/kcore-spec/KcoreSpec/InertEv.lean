/-
  KCore, checked layer: three classes of sentences the reader leaves inert (`Parse.InertReason`),
  each entailed by `Γ c` for every semantics meeting `coreOK`.

  - `vacuousLeft_entailed`: a rewrite axiom whose left side `Parse.vacuous` accepts. Its left side's
    translation holds of no element (`vacuous_none`), so the axiom holds in every interpretation
    with definedness: `Γ c` entails it, at every valuation.
  - `listLaw_ev`: the associativity and the two unit sentences of `_List_`, entailed at values
    (`EntailsAtValues`), from the graph `ΓDomains` states of `_List_` and `.List`
    (`LawEqn.entailed`: a sentence `\equals{s, R}(lhs, rhs)` whose sides have the same value).
  - `iteFun_entailed`: the `functional` sentence of a parameter symbol `ite{S}` implemented by the
    registry's `kIte`, entailed at values, from the graph `ΓDomains` states of the parameter. The
    text states the sentence once over a sort variable; no valuation sends a variable of that sort
    to a value, so the statement is of each instance the definition has.
-/
import KcoreSpec.LibEvInt
import KcoreSpec.ExistsHoist
import KcoreSpec.Parse

set_option autoImplicit false

namespace KCore

namespace InertEv

open ML Faithful

/-! ## A rewrite axiom whose left side is empty -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

mutual
  /-- The translation of a sort holds no free occurrence of the variable `⊤_s` binds. -/
  theorem trSort_topFresh (t : KoreAML.VarTable) : ∀ (s : Kore.KSort),
      (KoreAML.trSort t s).isFreeEvar KoreAML.topVar = false
    | .var α => by
      rw [KoreAML.trSort]
      simp [Pattern.isFreeEvar, KoreAML.topVar, KoreAML.VarTable.ev, KoreAML.VarTable.index]
    | .ctor C args => by
      rw [KoreAML.trSort]; exact trSortApp_topFresh t args _ rfl
  theorem trSortApp_topFresh (t : KoreAML.VarTable) : ∀ (ss : List Kore.KSort) (acc : KoreAML.P),
      acc.isFreeEvar KoreAML.topVar = false → (KoreAML.trSortApp t acc ss).isFreeEvar KoreAML.topVar = false
    | [], acc, h => by rw [KoreAML.trSortApp]; exact h
    | s :: ss, acc, h => by
      rw [KoreAML.trSortApp]
      exact trSortApp_topFresh t ss _ (by simp [Pattern.isFreeEvar, h, trSort_topFresh t s])
end

/-- `⊥_s` holds of no element. -/
theorem sBot_none (hD : KoreAML.DefOK I) {s : KoreAML.P} (hs : s.isFreeEvar KoreAML.topVar = false)
    (e : Valuation M) (m : M) : ¬ (KoreAML.sBot s).interpret I e m := by
  unfold KoreAML.sBot
  rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD hs]
  exact fun h => h.1 h.2

theorem trAndList_cons_of {ctx : KoreAML.Ctx} {s : KoreAML.P} {p : Kore.Pattern} {ps : List Kore.Pattern}
    {e : Valuation M} {m : M} (h : (KoreAML.trAndList ctx s (p :: ps)).interpret I e m) :
    (KoreAML.tr ctx p).interpret I e m ∧ (ps = [] ∨ (KoreAML.trAndList ctx s ps).interpret I e m) := by
  cases ps with
  | nil => rw [KoreAML.trAndList] at h; exact ⟨h, Or.inl rfl⟩
  | cons q qs =>
    rw [KoreAML.trAndList, KoreAML.interp_sAnd] at h
    exact ⟨h.1, Or.inr h.2⟩

theorem trOrList_cons_of {ctx : KoreAML.Ctx} {s : KoreAML.P} {p : Kore.Pattern} {ps : List Kore.Pattern}
    {e : Valuation M} {m : M} (h : (KoreAML.trOrList ctx s (p :: ps)).interpret I e m) :
    (KoreAML.tr ctx p).interpret I e m ∨ (KoreAML.trOrList ctx s ps).interpret I e m := by
  cases ps with
  | nil => rw [KoreAML.trOrList] at h; exact Or.inl h
  | cons q qs =>
    rw [KoreAML.trOrList, KoreAML.interp_sOr] at h
    exact h.2

mutual
  /-- **A left side `Parse.vacuous` accepts is empty**: its translation holds of no element, in
  every interpretation with definedness and at every valuation. -/
  theorem vacuous_none (hD : KoreAML.DefOK I) (t : KoreAML.VarTable) : ∀ (p : Kore.Pattern),
      Parse.vacuous p = true → ∀ (e : Valuation M) (m : M), ¬ (KoreAML.tr ⟨t, []⟩ p).interpret I e m
    | .bottom s, _, e, m => by
      rw [KoreAML.tr]; exact sBot_none hD (trSort_topFresh t s) e m
    | .app h ss ps, hv, e, m => by
      rw [Parse.vacuous] at hv
      rw [KoreAML.tr]
      simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
      exact anyVacuous_none hD t ps hv _ e m
    | .and s ps, hv, e, m => by
      rw [Parse.vacuous] at hv
      rw [KoreAML.tr]
      exact anyVacuous_and_none hD t ps hv _ e m
    | .exist _ x p, hv, e, m => by
      rw [Parse.vacuous] at hv
      rw [KoreAML.tr, KoreAML.interp_sExists]
      rintro ⟨a, -, h⟩
      exact vacuous_none hD t p hv _ m h
    | .or s ps, hv, e, m => by
      rw [Parse.vacuous] at hv
      rw [KoreAML.tr]
      exact allVacuous_none hD t ps hv _ (trSort_topFresh t s) e m
    | .var _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .string _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .top _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .not _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .implies _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .iff _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .forall _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .mu _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .nu _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .ceil _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .floor _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .equals _ _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .in _ _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .next _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .rewrites _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .dv _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .leftAssoc _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
    | .rightAssoc _ _ _, hv, _, _ => by simp [Parse.vacuous] at hv
  termination_by structural p => p
  /-- An application one of whose arguments is empty is empty. -/
  theorem anyVacuous_none (hD : KoreAML.DefOK I) (t : KoreAML.VarTable) : ∀ (ps : List Kore.Pattern),
      Parse.anyVacuous ps = true → ∀ (acc : KoreAML.P) (e : Valuation M) (m : M),
        ¬ (KoreAML.trArgs ⟨t, []⟩ acc ps).interpret I e m
    | [], hv, _, _, _ => by simp [Parse.anyVacuous] at hv
    | p :: ps, hv, acc, e, m => by
      rw [Parse.anyVacuous, Bool.or_eq_true] at hv
      rw [KoreAML.trArgs_cons]
      rcases hv with hv | hv
      · exact trArgs_empty (fun m' hm' => by
          obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
          exact vacuous_none hD t p hv e b hb) ps m
      · exact anyVacuous_none hD t ps hv _ e m
  termination_by structural ps => ps
  /-- A conjunction one of whose operands is empty is empty. -/
  theorem anyVacuous_and_none (hD : KoreAML.DefOK I) (t : KoreAML.VarTable) : ∀ (ps : List Kore.Pattern),
      Parse.anyVacuous ps = true → ∀ (s : KoreAML.P) (e : Valuation M) (m : M),
        ¬ (KoreAML.trAndList ⟨t, []⟩ s ps).interpret I e m
    | [], hv, _, _, _ => by simp [Parse.anyVacuous] at hv
    | p :: ps, hv, s, e, m => by
      rw [Parse.anyVacuous, Bool.or_eq_true] at hv
      intro h
      obtain ⟨h1, h2⟩ := trAndList_cons_of h
      rcases hv with hv | hv
      · exact vacuous_none hD t p hv e m h1
      · rcases h2 with rfl | h2
        · simp [Parse.anyVacuous] at hv
        · exact anyVacuous_and_none hD t ps hv s e m h2
  termination_by structural ps => ps
  /-- A disjunction all of whose operands are empty is empty. -/
  theorem allVacuous_none (hD : KoreAML.DefOK I) (t : KoreAML.VarTable) : ∀ (ps : List Kore.Pattern),
      Parse.allVacuous ps = true → ∀ (s : KoreAML.P), s.isFreeEvar KoreAML.topVar = false →
        ∀ (e : Valuation M) (m : M), ¬ (KoreAML.trOrList ⟨t, []⟩ s ps).interpret I e m
    | [], _, s, hs, e, m => by rw [KoreAML.trOrList]; exact sBot_none hD hs e m
    | p :: ps, hv, s, hs, e, m => by
      rw [Parse.allVacuous, Bool.and_eq_true] at hv
      intro h
      rcases trOrList_cons_of h with h1 | h2
      · exact vacuous_none hD t p hv.1 e m h1
      · exact allVacuous_none hD t ps hv.2 s hs e m h2
  termination_by structural ps => ps
end

end

/-- **A rewrite axiom with an empty left side is entailed** (`InertReason.vacuousLeft`): where the
left side of `\rewrites{s}(\and{s'}(l, q), r)` is one `Parse.vacuous` accepts (the condition of
`classifyAxiom`), the translation of the axiom, with any declarations and no alias, holds in every
model of `Γ c`. The proof reads definedness alone: no hook, no rule, no function. -/
theorem vacuousLeft_entailed (c : Semantics) {a : Kore.Axiom}
    (hv : (match a.pattern with
      | .rewrites _ (.and _ [l, _]) _ => Parse.vacuous l
      | _ => false) = true)
    (decls : List KoreAML.SymbolDecl) (i : Nat) (mod : String) :
    Γ c ⊧ (KoreAML.trAxiom decls [] ⟨i, mod, a⟩).pat := by
  intro M _ I hI e m
  have hD := defOK hI
  split at hv
  · rename_i s s' l q r hp
    unfold KoreAML.trAxiom
    dsimp only
    rw [interpret_impl]
    intro _
    rw [hp]
    simp only [KoreAML.sortOf]
    rw [KoreAML.interp_equal hD]
    intro b
    rw [KoreAML.tr]
    unfold KoreAML.sRewrites
    rw [KoreAML.interp_sImp]
    refine ⟨fun h => h.1, fun hb => ⟨hb, fun hl => ?_⟩⟩
    rw [KoreAML.tr] at hl
    exact absurd (trAndList_cons_of hl).1 (vacuous_none hD _ l hv e b)
  · cases hv

/-! ## The laws of `_List_`, at values -/

/-- Two keys of a table, one of them in it, have different indices. -/
theorem ev_ne_of_mem {t : KoreAML.VarTable} {k k' : KoreAML.VarKey} (hk : k ∈ t) (hne : k ≠ k') :
    t.ev k ≠ t.ev k' := by
  have key : ∀ (l : List KoreAML.VarKey), k ∈ l → l.idxOf k = l.idxOf k' → False := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons a l ih =>
      intro hm he
      simp only [List.idxOf_cons] at he
      by_cases h1 : a = k
      · subst h1
        have h2 : (a == k') = false := by simpa using hne
        simp [h2] at he
      · have h1' : (a == k) = false := by simpa using h1
        by_cases h2 : a = k'
        · subst h2; simp [h1'] at he
        · have h2' : (a == k') = false := by simpa using h2
          simp only [h1', h2', Bool.false_eq_true, ↓reduceIte, Nat.add_right_cancel_iff] at he
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact h1 rfl
          · exact ih hm' he
  intro h
  have h' : t.idxOf k = t.idxOf k' := by
    simpa [KoreAML.VarTable.ev, KoreAML.VarTable.index] using h
  exact key t hk h'

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The values of an axiom's variables.** At a valuation that sends the free element variables
of the axiom to values (`AtValues`), a substitution gives each of the listed variables, free in the
axiom, a value of its sort whose element is the valuation's. -/
theorem atValues_subst (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {e : Valuation M} {a : Kore.Axiom}
    (hat : AtValues c I e a) (vars : LibEv.Vars)
    (hvR : ∀ p ∈ vars, p.2 < nRegSorts + c.sortNames.length)
    (hfv : ∀ i, i < vars.length → LibEv.vkey c vars i ∈ KoreAML.freeOf [] a.pattern) :
    ∃ σ : Subst, (∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) ∧
      ∀ i v, i < vars.length → σ.lookup i = some v →
        elemOf c I v = e.evalEvar ((KoreAML.tableOf a.sortVars a.pattern).ev (LibEv.vkey c vars i)) := by
  haveI : OvlOK c := ovlOK_of_core h
  obtain ⟨-, hfa, -, -, -⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -, -, -, hn, -, hsn, -, -, -, -⟩ := faithCoreOK_parts hfa
  unfold AtValues at hat
  generalize KoreAML.tableOf a.sortVars a.pattern = t at hat ⊢
  have hval : ∀ i, i < vars.length → ∃ v, c.sortOf v = some (vars.getD i ("", 0)).2 ∧
      elemOf c I v = e.evalEvar (t.ev (LibEv.vkey c vars i)) := by
    intro i hi
    obtain ⟨v, S, hS, hv, hden⟩ := hat _ _ (List.mem_eraseDups.mpr (hfv i hi))
    have hp2 : (vars.getD i ("", 0)).2 < nRegSorts + c.sortNames.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hvR _ (List.getElem_mem hi)
    have hSe : S = (vars.getD i ("", 0)).2 :=
      sort_eq_of_name hn (sortOf_numbered_ofCl hg hsn (Semantics.coreOK_ovls h) hv) hp2 (srt_inj hS)
    subst hSe
    exact ⟨v, hv, (((elemOf_spec hI hv e).1 _).mp hden).symm⟩
  let σ : Subst := (List.range vars.length).map fun i =>
    (i, pick c I (vars.getD i ("", 0)).2 (e.evalEvar (t.ev (LibEv.vkey c vars i))))
  have hlk : ∀ i, σ.lookup i = if i < vars.length then
      some (pick c I (vars.getD i ("", 0)).2 (e.evalEvar (t.ev (LibEv.vkey c vars i)))) else none := by
    intro i
    show ((List.range vars.length).map _).lookup i = _
    rw [List.range_eq_range', lookup_range']
    simp
  refine ⟨σ, fun i p hp' => ?_, fun i v hi hv => ?_⟩
  · have hi : i < vars.length := (List.getElem?_eq_some_iff.mp hp').1
    have hgd' : vars.getD i ("", 0) = p := by rw [List.getD_eq_getElem?_getD, hp']; rfl
    refine ⟨pick c I (vars.getD i ("", 0)).2 (e.evalEvar (t.ev (LibEv.vkey c vars i))), ?_, ?_⟩
    · rw [hlk]; simp only [hi, ite_true]
    · rw [← hgd']
      exact (pick_spec (hval i hi)).1
  · rw [hlk] at hv
    simp only [hi, ite_true] at hv
    cases hv
    exact (pick_spec (hval i hi)).2

end

/-- A law of a collection's concatenation as kompile writes it, `\equals{s, R}(lhs, rhs)`, its sides
terms over variables and interpreted hooked symbols. -/
structure LawEqn where
  vars : LibEv.Vars
  s : Srt
  lhs : Term
  rhs : Term

/-- The law's pattern, over the registry's names. -/
def LawEqn.patR (E : LawEqn) : Kore.Pattern :=
  .equals (regSrtK E.s) KoreAML.R (LibEv.koreR E.vars E.lhs) (LibEv.koreR E.vars E.rhs)

/-- The law is over the registry's symbols and sorts, and each of its variables is free in its
pattern. -/
def LawEqn.regular (E : LawEqn) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  LibEv.reg E.lhs && LibEv.reg E.rhs &&
  E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

/-- **A law whose two sides have the same value is entailed at values.** For a semantics meeting
`coreOK` and a regular law whose sides are terms of its sort with the same value, or both none, at
every substitution of values of the variables' sorts: the translation of an axiom declaration with
the law's pattern over the one sort variable `R` holds in every model of `Γ c` at every valuation
that sends the axiom's free element variables to values. -/
theorem LawEqn.entailed {c : Semantics} (h : c.coreOK = true) (E : LawEqn) (hr : E.regular = true)
    (htl : LibEv.srt? c E.vars E.lhs = some E.s) (htr : LibEv.srt? c E.vars E.rhs = some E.s)
    (hE : ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
      LibEv.val c σ E.lhs = LibEv.val c σ E.rhs)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [LawEqn.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨⟨hsR, hvR⟩, hrl⟩, hrr⟩, hf⟩ := hr
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  have hpc : ad.ax.pattern = .equals (srtOf c E.s) KoreAML.R (LibEv.kore c E.vars E.lhs)
      (LibEv.kore c E.vars E.rhs) := by
    rw [hp, LibEv.kore_reg c hvR _ hrl, LibEv.kore_reg c hvR _ hrr, LibEv.srtOf_reg c hsR]; rfl
  have hfv : ∀ i, i < E.vars.length → LibEv.vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern := by
    intro i hi
    have hmem : E.vars.getD i ("", 0) ∈ E.vars := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    have := hf _ hmem
    rw [hp]
    unfold LibEv.vkey
    rw [LibEv.srtOf_reg c (hvR _ hmem)]
    exact List.mem_of_elem_eq_true this
  obtain ⟨σ, hσ, hel⟩ := atValues_subst h hI hat E.vars (fun p hp' => hnum (hvR p hp')) hfv
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hag : ∀ i v, i < E.vars.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (LibEv.vkey c E.vars i)) ↔ (den c v).interpret I e m := by
    intro i v hi hv m'
    obtain ⟨w, hw, hws⟩ := hσ i _ (List.getElem?_eq_getElem hi)
    rw [hv] at hw; cases hw
    rw [(elemOf_spec hI hws e).1 m', hel i v hi hv]
  have hDV := fun (u : Term) (s : Srt) (hu : LibEv.srt? c E.vars u = some s) =>
    LibEv.den_val (tbl := t) (e := e) h hI hσ hag u hu
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [hpc]
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
  refine ⟨fun h' => (KoreAML.interp_inhOf_of hRv).mpr h'.1,
    fun ha => ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b _ => ?_⟩⟩
  rw [(hDV E.lhs _ htl).1 b, hE σ hσ, ← (hDV E.rhs _ htr).1 b]

/-- `_List_` applied to two terms. -/
def listCat (a b : Term) : Term := .app listConcat [a, b]

/-- Associativity of `_List_`: `(K1 K2) K3 = K1 (K2 K3)`. -/
def listAssoc : LawEqn :=
  ⟨[("K1", Srt.list), ("K2", Srt.list), ("K3", Srt.list)], Srt.list,
    listCat (listCat (.var 0) (.var 1)) (.var 2), listCat (.var 0) (listCat (.var 1) (.var 2))⟩

/-- The right unit of `_List_`: `K .List = K`. -/
def listUnitRight : LawEqn :=
  ⟨[("K", Srt.list)], Srt.list, listCat (.var 0) (.app listUnit []), .var 0⟩

/-- The left unit of `_List_`: `.List K = K`. -/
def listUnitLeft : LawEqn :=
  ⟨[("K", Srt.list)], Srt.list, listCat (.app listUnit []) (.var 0), .var 0⟩

section
variable {c : Semantics}

theorem hv_listConcat (a b : List GroundTerm) :
    c.hv listConcat [.list Srt.list a, .list Srt.list b] = some (.list Srt.list (a ++ b)) :=
  hv_of_value (List'.hook_concat _ _ a b)
theorem hv_listUnit : c.hv listUnit [] = some (.list Srt.list []) := hv_of_value List'.hook_unit

/-- A substitution of values of the variables' sorts gives a List variable a list. -/
theorem list_at (hs : c.shapesOK = true) {vars : LibEv.Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
    (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.list)) :
    ∃ es, σ.lookup i = some (.list Srt.list es) := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨es, rfl⟩ := shape_list hs hsv
  exact ⟨es, hv⟩

end

/-- **The laws of `_List_` are entailed at values** (`InertReason.collectionLaw`): for a semantics
meeting `coreOK` whose List values are lists (`shapesOK`), an axiom declaration whose pattern is the
associativity, the right unit or the left unit of `_List_` holds in every model of `Γ c` at every
valuation that sends its variables to values. `_List_` is total on lists and has no silent point:
the value of each side is `hook`'s, whatever the interpretation. -/
theorem listLaw_ev {c : Semantics} (hcore : c.coreOK = true) (hs : c.shapesOK = true)
    {E : LawEqn} (hE : E = listAssoc ∨ E = listUnitRight ∨ E = listUnitLeft) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  rcases hE with rfl | rfl | rfl
  · refine LawEqn.entailed hcore listAssoc (by decide) (by rfl) (by rfl) (fun σ hσ => ?_) ad hp hsv
    obtain ⟨a, ha⟩ := list_at hs hσ 0 (n := "K1") rfl
    obtain ⟨b, hb⟩ := list_at hs hσ 1 (n := "K2") rfl
    obtain ⟨d, hd⟩ := list_at hs hσ 2 (n := "K3") rfl
    simp only [listAssoc, listCat, LibEv.val, LibEv.valList, allSome, ha, hb, hd, Option.bind_some,
      Option.map_some, hv_listConcat, List.append_assoc]
  · refine LawEqn.entailed hcore listUnitRight (by decide) (by rfl) (by rfl) (fun σ hσ => ?_) ad hp hsv
    obtain ⟨a, ha⟩ := list_at hs hσ 0 (n := "K") rfl
    simp only [listUnitRight, listCat, LibEv.val, LibEv.valList, allSome, ha, Option.bind_some,
      Option.map_some, hv_listConcat, hv_listUnit, List.append_nil]
  · refine LawEqn.entailed hcore listUnitLeft (by decide) (by rfl) (by rfl) (fun σ hσ => ?_) ad hp hsv
    obtain ⟨a, ha⟩ := list_at hs hσ 0 (n := "K") rfl
    simp only [listUnitLeft, listCat, LibEv.val, LibEv.valList, allSome, ha, Option.bind_some,
      Option.map_some, hv_listConcat, hv_listUnit, List.nil_append]

/-! ## `ite` at a sort is total, at values -/

/-- The variables of `ite`'s `functional` sentence at the sort S. -/
def iteVars (S : Srt) : LibEv.Vars := [("K0", Srt.bool), ("K1", S), ("K2", S)]

/-- `\exists{R}(Val:S, \equals{S, R}(Val:S, f(K0:Bool, K1:S, K2:S)))`, the application written as
the translation of a term writes it (`symApp`: `Lblite{SortX}(…)` for a symbol named `ite{X}`): the
`functional` sentence of `ite{S}` at the sort S. -/
def iteFunPat (c : Semantics) (f : Sym) (S : Srt) : Kore.Pattern :=
  .exist KoreAML.R (KoreAML.evar "Val" (srtOf c S))
    (.equals (srtOf c S) KoreAML.R (.var (.evar (KoreAML.evar "Val" (srtOf c S))))
      (symApp c f (LibEv.koreList c (iteVars S) [.var 0, .var 1, .var 2])))

theorem freeOf_symApp (c : Semantics) (f : Sym) (ps : List Kore.Pattern) (b : List KoreAML.VarKey) :
    KoreAML.freeOf b (symApp c f ps) = KoreAML.freeOfList b ps := by
  obtain ⟨h, xs, -, hw⟩ := symApp_head c f
  rw [hw, KoreAML.freeOf]

theorem mem_varsOf_symApp (c : Semantics) (f : Sym) {ps : List Kore.Pattern} {k : KoreAML.VarKey}
    (h : k ∈ KoreAML.varsOfList ps) : k ∈ KoreAML.varsOf (symApp c f ps) := by
  obtain ⟨hd, xs, -, hw⟩ := symApp_head c f
  rw [hw, KoreAML.varsOf]; exact List.mem_append_right _ h

/-- **`ite` at a sort is total at values** (`InertReason.parametricFunctional`, at an instance):
for a semantics meeting `coreOK` whose Bool values are literals (`shapesOK`) and a parameter symbol
`f : Bool × S × S → S` implemented by the registry's `kIte`, an axiom declaration whose pattern is
the `functional` sentence of `f` holds in every model of `Γ c` at every valuation that sends its
variables to values: at values b, x, y the application denotes the one element of x or of y, by the
graph `ΓDomains` states of the parameter. -/
theorem iteFun_entailed {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) {k : ParamSig}
    (hk : c.lookupParam k.sig.name = some k) (himpl : k.impl = some kIte) {S : Srt}
    (hargs : k.sig.args = [Srt.bool, S, S]) (hres : k.sig.result = S)
    (hS : S < nRegSorts + c.sortNames.length) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = iteFunPat c k.sig.name S) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hvars : ∀ p ∈ iteVars S, p.2 < nRegSorts + c.sortNames.length := by
    intro p hp'
    simp only [iteVars, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    · exact hS
    · exact hS
  have hkeyL : ∀ i, i < (iteVars S).length → LibEv.vkey c (iteVars S) i ∈
      KoreAML.varsOfList (LibEv.koreList c (iteVars S) [.var 0, .var 1, .var 2]) ∧
      LibEv.vkey c (iteVars S) i ∈ KoreAML.freeOfList [KoreAML.evarKey (KoreAML.evar "Val" (srtOf c S))]
        (LibEv.koreList c (iteVars S) [.var 0, .var 1, .var 2]) ∧
      LibEv.vkey c (iteVars S) i ≠ KoreAML.evarKey (KoreAML.evar "Val" (srtOf c S)) := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by simp only [iteVars, List.length_cons, List.length_nil] at hi; omega
    have hkl : LibEv.koreList c (iteVars S) [.var 0, .var 1, .var 2] =
        [.var (.evar (KoreAML.evar "K0" (srtOf c Srt.bool))), .var (.evar (KoreAML.evar "K1" (srtOf c S))),
         .var (.evar (KoreAML.evar "K2" (srtOf c S)))] := by
      simp only [LibEv.koreList, LibEv.kore]; rfl
    have hno : ∀ k : KoreAML.VarKey, k ≠ .evar "Val" (srtOf c S) →
        ([KoreAML.evarKey (KoreAML.evar "Val" (srtOf c S))].contains k) = false := by
      intro k hk
      show ([KoreAML.VarKey.evar "Val" (srtOf c S)].contains k) = false
      simp [hk]
    have hne : ∀ (n : String) (s : Kore.KSort), n ≠ "Val" →
        KoreAML.VarKey.evar n s ≠ .evar "Val" (srtOf c S) := fun n s hn he => by
      injection he with h1 _; exact hn h1
    rw [hkl]
    rcases hi' with rfl | rfl | rfl
    · have hk : LibEv.vkey c (iteVars S) 0 = .evar "K0" (srtOf c Srt.bool) := rfl
      rw [hk]
      refine ⟨?_, ?_, hne _ _ (by decide)⟩
      · simp only [KoreAML.varsOfList, KoreAML.varsOf, List.mem_append]
        exact Or.inl (Or.inr (List.mem_singleton.mpr rfl))
      · simp only [KoreAML.freeOfList, KoreAML.freeOf, List.mem_append]
        refine Or.inl ?_
        rw [show KoreAML.evarKey (KoreAML.evar "K0" (srtOf c Srt.bool)) = .evar "K0" (srtOf c Srt.bool) from rfl,
          hno _ (hne _ _ (by decide))]
        exact List.mem_singleton.mpr rfl
    · have hk : LibEv.vkey c (iteVars S) 1 = .evar "K1" (srtOf c S) := rfl
      rw [hk]
      refine ⟨?_, ?_, hne _ _ (by decide)⟩
      · simp only [KoreAML.varsOfList, KoreAML.varsOf, List.mem_append]
        exact Or.inr (Or.inl (Or.inr (List.mem_singleton.mpr rfl)))
      · simp only [KoreAML.freeOfList, KoreAML.freeOf, List.mem_append]
        refine Or.inr (Or.inl ?_)
        rw [show KoreAML.evarKey (KoreAML.evar "K1" (srtOf c S)) = .evar "K1" (srtOf c S) from rfl,
          hno _ (hne _ _ (by decide))]
        exact List.mem_singleton.mpr rfl
    · have hk : LibEv.vkey c (iteVars S) 2 = .evar "K2" (srtOf c S) := rfl
      rw [hk]
      refine ⟨?_, ?_, hne _ _ (by decide)⟩
      · simp only [KoreAML.varsOfList, KoreAML.varsOf, List.mem_append]
        exact Or.inr (Or.inr (Or.inl (Or.inr (List.mem_singleton.mpr rfl))))
      · simp only [KoreAML.freeOfList, KoreAML.freeOf, List.mem_append]
        refine Or.inr (Or.inr (Or.inl ?_))
        rw [show KoreAML.evarKey (KoreAML.evar "K2" (srtOf c S)) = .evar "K2" (srtOf c S) from rfl,
          hno _ (hne _ _ (by decide))]
        exact List.mem_singleton.mpr rfl
  have hfv : ∀ i, i < (iteVars S).length → LibEv.vkey c (iteVars S) i ∈ KoreAML.freeOf [] ad.ax.pattern := by
    intro i hi
    rw [hp]
    unfold iteFunPat
    rw [KoreAML.freeOf, KoreAML.freeOf, freeOf_symApp]
    exact List.mem_append_right _ (hkeyL i hi).2.1
  obtain ⟨σ, hσ, hel⟩ := atValues_subst h hI hat (iteVars S) hvars hfv
  obtain ⟨v0, h0, hs0⟩ := hσ 0 _ rfl
  obtain ⟨b, rfl⟩ := shape_bool hs hs0
  obtain ⟨vx, h1, hs1⟩ := hσ 1 _ rfl
  obtain ⟨vy, h2, hs2⟩ := hσ 2 _ rfl
  have hvS : c.sortOf (if b then vx else vy) = some S := by cases b <;> simpa
  have hpv : c.paramVal k.sig.name [bool b, vx, vy] = some (if b then vx else vy) :=
    paramVal_ite hk himpl b (by rw [hres]; exact hvS)
  have hsorts : c.sortsOf [bool b, vx, vy] = some k.sig.args := by
    rw [hargs]
    exact sortsOf_cons.mpr ⟨_, _, hs0, sortsOf_cons.mpr ⟨_, _, hs1, sortsOf_cons.mpr ⟨_, _, hs2, sortsOf_nil, rfl⟩,
      rfl⟩, rfl⟩
  have hax := sat_dom hI (Or.inr (Or.inl ⟨k, [bool b, vx, vy], lookupParam_mem hk, hsorts, rfl⟩))
  simp only [hpv] at hax
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel ⊢
  rw [interpret_impl]
  intro hgd
  have hmemR : KoreAML.VarKey.sortVar "R" ∈ t := by
    rw [← htb]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl))
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hmemK : ∀ i, i < (iteVars S).length → LibEv.vkey c (iteVars S) i ∈ t := by
    intro i hi
    rw [← htb, hp]
    unfold KoreAML.tableOf iteFunPat
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    rw [KoreAML.varsOf, KoreAML.varsOf]
    exact List.mem_append_right _ (List.mem_append_right _ (mem_varsOf_symApp c _ (hkeyL i hi).1))
  generalize hxv : t.ev (KoreAML.evarKey (KoreAML.evar "Val" (srtOf c S))) = xv
  have hneK : ∀ i, i < (iteVars S).length → t.ev (LibEv.vkey c (iteVars S) i) ≠ xv := fun i hi => by
    rw [← hxv]; exact ev_ne_of_mem (hmemK i hi) (hkeyL i hi).2.2
  have hneR : t.ev (.sortVar "R") ≠ xv := by
    rw [← hxv]; exact ev_ne_of_mem hmemR (by simp [KoreAML.evarKey])
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI hS
  have hRv : ∀ b', (KoreAML.trSort t KoreAML.R).interpret I e b' ↔ b' = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b' => by rw [trSort_R, KoreAML.interp_evar]
  have hRv' : ∀ a0 b', (KoreAML.trSort t KoreAML.R).interpret I (KoreAML.updE e xv a0) b' ↔
      b' = e.evalEvar (t.ev (.sortVar "R")) := fun a0 b' => by
    rw [trSort_R, KoreAML.interp_evar]
    show b' = Function.update e.evalEvar xv a0 (t.ev (.sortVar "R")) ↔ _
    rw [Function.update_noteq hneR]
  rw [hp]
  unfold iteFunPat
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, hxv, KoreAML.interp_sExists_elem hD]
  constructor
  · rintro ⟨a0, -, heq⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t _) (hRv' a0) hτsort hR] at heq
    exact (KoreAML.interp_inhOf_of hRv).mpr heq.1
  · intro ha
    refine ⟨elemOf c I (if b then vx else vy), ?_, ?_⟩
    · have := (elemOf_spec hI hvS (KoreAML.updE e xv (elemOf c I (if b then vx else vy)))).2
      show (KoreAML.inhOf (KoreAML.trSort t (srtOf c S))).interpret _ _ _
      rwa [trSort_srtOf_twoT]
    · rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t _) (hRv' _) hτsort hR]
      refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b' _ => ?_⟩
      rw [KoreAML.tr, hxv, KoreAML.interp_evar]
      show b' = Function.update e.evalEvar xv _ xv ↔ _
      rw [Function.update_same, tr_symApp]
      have hag' : ∀ i w, i < (iteVars S).length → σ.lookup i = some w →
          ∀ m', m' = (KoreAML.updE e xv (elemOf c I (if b then vx else vy))).evalEvar
            (t.ev (LibEv.vkey c (iteVars S) i)) ↔
            (den c w).interpret I (KoreAML.updE e xv (elemOf c I (if b then vx else vy))) m' := by
        intro i w hi hw m'
        obtain ⟨w', hw', hws⟩ := hσ i _ (List.getElem?_eq_getElem hi)
        rw [hw] at hw'; cases hw'
        rw [(elemOf_spec hI hws _).1 m', hel i w hi hw]
        show m' = Function.update e.evalEvar xv _ (t.ev (LibEv.vkey c (iteVars S) i)) ↔ _
        rw [Function.update_noteq (hneK i hi)]
      have hdv := LibEv.den_vals (tbl := t) (e := KoreAML.updE e xv (elemOf c I (if b then vx else vy)))
        h hI hσ hag' [.var 0, .var 1, .var 2] (ss := [Srt.bool, S, S]) rfl
      have hall : allSome (LibEv.valList c σ [.var 0, .var 1, .var 2]) = some [bool b, vx, vy] := by
        simp [LibEv.valList, LibEv.val, allSome, h0, h1, h2]
      rw [(hdv.1 _ hall).2 (symHead c k.sig.name) (symHead c k.sig.name) (fun _ => Iff.rfl) b']
      have hgr := (KoreAML.interp_equal hD).mp
        (hax (KoreAML.updE e xv (elemOf c I (if b then vx else vy))) default) b'
      unfold KoreAML.den at hgr
      rw [tr_symApp] at hgr
      rw [hgr, (elemOf_spec hI hvS _).1]

end InertEv

end KCore
