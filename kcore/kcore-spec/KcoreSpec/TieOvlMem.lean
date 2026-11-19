/-
  KCore, outside the cone: a function equation whose argument Γ's item binds by a membership,
  against the equation as the text writes it, with the argument pattern under the function. For a
  tie file.

  The reading of a `symbol-overload` axiom of a function gives the clause the argument pattern of
  the axiom, and Γ's item of a clause states it with a variable at the argument:
    Γ:     `\implies{R}(\and{R}(\top{R}(), \and{R}(\in{S, R}(x, p), \top{R}())),
                        \equals{S', R}(f(x), \and{S'}(r, \top{S'}())))`
    text:  `\equals{S', R}(f(p), r)`
  - `parts`: the parts `(R, S, x, p, S', f, ss, r)` of an equation of Γ of that form, one argument
    bound by one membership and no other premise.
  - `textItem a`: the item of Γ's equation `a` as the text writes it, at `a`'s variable table, with
    the guards of its own free variables (x is not among them). A tie file compares it with the
    sentence's translation up to the names of the variables (`TieAlpha.acEqB`).
  - `ArgOne I a`: where the guards of the text's form hold, the argument pattern p denotes exactly
    one element, of the sort S. What each direction reads of it (argued here, no lemma states the
    converse): item to sentence reads that p holds an element of S, since where p is empty Γ's item
    states nothing and the text states that r is empty in S'; sentence to item reads that p holds
    at most one element, since where p holds two the text states r of the union of f at both and
    Γ's item of f at each.
  - `ovlMem_entailed` (item to sentence) and `ovlMem_from_text` (sentence to item), `ovlMem_iff`:
    in a model with the constructors' facts (`NodeFacts`) and `ArgOne`, for an equation `okB`
    accepts. The two right sides `r` and `r ∧ ⊤_S'` are compared inside S' only (`\equals{S', R}`),
    where they hold the same elements. Item to sentence reads the item at the valuation with p's
    element at x, which `okB` shows no other part of the item reads.
  - `argOne_inj`: `ArgOne` for the argument `inj{A, S}(v)`, v a variable of the sort A, from
    Cons-Fun of that injection (`KoreAML.Cons.funItem`), an item of Γ.

  Limit: one argument and one membership. An overload of several arguments has one membership for
  each; no lemma here states that form.
-/
import KcoreSpec.TieCutEq
import KcoreSpec.FaithfulNeg
import KcoreSpec.TieFRRead

set_option autoImplicit false

namespace KCore

namespace TieOvlMem

open ML Faithful KoreAML

/-- The parts `(R, S, x, p, S', f, ss, r)` of Γ's equation
`\implies{R}(\and{R}(\top{R}(), \and{R}(\in{S, R}(x, p), \top{R}())),
  \equals{S', R}(f{ss}(x), \and{S'}(r, \top{S'}())))`. -/
def parts : Kore.Pattern →
    Option (Kore.KSort × Kore.KSort × Kore.EVar × Kore.Pattern × Kore.KSort × Kore.SymbolIdent ×
      List Kore.KSort × Kore.Pattern)
  | .implies R (.and R₁ [.top R₂, .and R₃ [.in S R₄ (.var (.evar x)) p, .top R₅]])
      (.equals S' R₆ (.app f ss [.var (.evar y)]) (.and S₁ [r, .top S₂])) =>
    if R₁ = R ∧ R₂ = R ∧ R₃ = R ∧ R₄ = R ∧ R₅ = R ∧ R₆ = R ∧ y = x ∧ S₁ = S' ∧ S₂ = S' then
      some (R, S, x, p, S', f, ss, r)
    else none
  | _ => none

/-- The equation as the text writes it: `\equals{S', R}(f{ss}(p), r)`. -/
def textOf (R S' : Kore.KSort) (f : Kore.SymbolIdent) (ss : List Kore.KSort) (p r : Kore.Pattern) :
    Kore.Pattern :=
  .equals S' R (.app f ss [p]) r

/-- **The item of the text's form of Γ's equation `a`**, at `a`'s variable table, with the guards
of the form's own free variables. -/
def textItem (a : Kore.Axiom) : Option P :=
  (parts a.pattern).map fun x =>
    TieCutEq.itemAt (tableOf a.sortVars a.pattern)
      (TieCutEq.freeT a (textOf x.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.1 x.2.2.2.2.2.2.2))
      x.1 (textOf x.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.1 x.2.2.2.2.2.2.2)

/-- What the two directions read of Γ's equation `a`, decided. Its sort R is a sort variable among
the free variables of the text's form; S and S' are numbered sorts of the definition and S is the
sort of x; the free variables of the text's form are free in Γ's, and those of Γ's are x and those
of the text's form; x's index is free in no guard of the text's form, nor in p, r, the function
with its sort arguments or R; the variable of `\top` is free in neither R nor S'. -/
def okB (c : Semantics) (a : Kore.Axiom) : Bool :=
  match parts a.pattern with
  | some (R, S, x, p, S', f, ss, r) =>
    let t := tableOf a.sortVars a.pattern
    let xi := t.ev (evarKey x)
    let fT := TieCutEq.freeT a (textOf R S' f ss p r)
    (match R with
      | .var α => fT.contains (sortVarKey α)
      | _ => false) &&
    (List.range (nRegSorts + c.sortNames.length)).any (fun s => decide (S = srtOf c s)) &&
    (List.range (nRegSorts + c.sortNames.length)).any (fun s => decide (S' = srtOf c s)) &&
    decide (x.sort = S) &&
    fT.all (TieCutEq.freeG a).contains &&
    (TieCutEq.freeG a).all (fun k => decide (k = evarKey x) || fT.contains k) &&
    fT.all (fun k => !(guardOf t k).isFreeEvar xi) &&
    !(tr ⟨t, []⟩ p).isFreeEvar xi && !(tr ⟨t, []⟩ r).isFreeEvar xi &&
    !(trSortApp t (sym (.symbol f.ident.name)) ss).isFreeEvar xi &&
    !(trSort t R).isFreeEvar xi &&
    !(trSort t R).isFreeEvar topVar && !(trSort t S').isFreeEvar topVar
  | none => false

/-- **The argument pattern denotes one element of its sort** where the guards of the text's form
of Γ's equation `a` hold. -/
def ArgOne {M : Type} (I : Interpretation KoreAML.Sym M) (a : Kore.Axiom) : Prop :=
  ∀ R S x p S' f ss r, parts a.pattern = some (R, S, x, p, S', f, ss, r) →
    ∀ (e : Valuation M) (m : M),
      (∀ k ∈ TieCutEq.freeT a (textOf R S' f ss p r),
        (guardOf (tableOf a.sortVars a.pattern) k).interpret I e m) →
      ∃ b, (inhOf (trSort (tableOf a.sortVars a.pattern) S)).interpret I e b ∧
        ∀ y, (tr ⟨tableOf a.sortVars a.pattern, []⟩ p).interpret I e y ↔ y = b

/-- The argument of Γ's equation `a` is the injection into the sort named `N` of the variable `v`
of the sort named `A`, a free variable of the text's form, decided. -/
def injB (a : Kore.Axiom) (N A : String) (v : Kore.EVar) : Bool :=
  match parts a.pattern with
  | some (R, S, _, p, S', f, ss, r) =>
    let t := tableOf a.sortVars a.pattern
    decide (tr ⟨t, []⟩ p = Cons.genPat N (.inj A) [.evar (t.ev (evarKey v))]) &&
    decide (trSort t S = Cons.sortP N) && decide (trSort t v.sort = Cons.sortP A) &&
    (TieCutEq.freeT a (textOf R S' f ss p r)).contains (evarKey v)
  | none => false

theorem parts_eq {q : Kore.Pattern} {R S : Kore.KSort} {x : Kore.EVar} {p : Kore.Pattern} {S' : Kore.KSort}
    {f : Kore.SymbolIdent} {ss : List Kore.KSort} {r : Kore.Pattern}
    (h : parts q = some (R, S, x, p, S', f, ss, r)) :
    q = .implies R (.and R [.top R, .and R [.in S R (.var (.evar x)) p, .top R]])
      (.equals S' R (.app f ss [.var (.evar x)]) (.and S' [r, .top S'])) := by
  unfold parts at h
  split at h
  · split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
      rfl
    · cases h
  · cases h

theorem textItem_parts {a : Kore.Axiom} {g : P} (h : textItem a = some g) :
    ∃ R S x p S' f ss r, parts a.pattern = some (R, S, x, p, S', f, ss, r) ∧
      g = TieCutEq.itemAt (tableOf a.sortVars a.pattern) (TieCutEq.freeT a (textOf R S' f ss p r)) R
        (textOf R S' f ss p r) := by
  unfold textItem at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨R, S, x, p, S', f, ss, r⟩, hp, rfl⟩ := h
  exact ⟨R, S, x, p, S', f, ss, r, hp, rfl⟩

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- An application reads its two operands only through the sets they denote. -/
theorem app_congr {e e' : Valuation M} {φ φ' ψ ψ' : P}
    (h1 : ∀ u, φ.interpret I e u ↔ φ'.interpret I e' u) (h2 : ∀ v, ψ.interpret I e v ↔ ψ'.interpret I e' v)
    (m : M) : (φ ⬝ ψ).interpret I e m ↔ (φ' ⬝ ψ').interpret I e' m := by
  simp only [interp_app, h1, h2]

/-- The translation of a function applied to one argument. -/
theorem tr_app1 (t : VarTable) (f : Kore.SymbolIdent) (ss : List Kore.KSort) (q : Kore.Pattern) :
    tr ⟨t, []⟩ (.app f ss [q]) = trSortApp t (sym (.symbol f.ident.name)) ss ⬝ tr ⟨t, []⟩ q := by
  rw [TieFRRead.tr_app, trArgs_cons, trArgs_nil]

/-- A pattern in which x is not free is read alike with x at another element. -/
theorem notFree_upd {ψ : P} {x : EVar} (h : ψ.isFreeEvar x = false) (e : Valuation M) (b m : M) :
    ψ.interpret I (updE e x b) m ↔ ψ.interpret I e m :=
  only_free_var_relevant _ _ _ _ (fun y hy => by
    have : y ≠ x := by
      rintro rfl
      rw [h] at hy; cases hy
    simp [Function.update, this]) (fun _ _ => rfl) m

end

/-- What `okB` decides, as facts. -/
theorem okB_parts {c : Semantics} {a : Kore.Axiom} {R S : Kore.KSort} {x : Kore.EVar} {p : Kore.Pattern}
    {S' : Kore.KSort} {f : Kore.SymbolIdent} {ss : List Kore.KSort} {r : Kore.Pattern}
    (hp : parts a.pattern = some (R, S, x, p, S', f, ss, r)) (h : okB c a = true) :
    (∃ α, R = .var α ∧ sortVarKey α ∈ TieCutEq.freeT a (textOf R S' f ss p r)) ∧
    (∃ s, s < nRegSorts + c.sortNames.length ∧ S = srtOf c s) ∧
    (∃ s, s < nRegSorts + c.sortNames.length ∧ S' = srtOf c s) ∧
    x.sort = S ∧
    (∀ k ∈ TieCutEq.freeT a (textOf R S' f ss p r), k ∈ TieCutEq.freeG a) ∧
    (∀ k ∈ TieCutEq.freeG a, k = evarKey x ∨ k ∈ TieCutEq.freeT a (textOf R S' f ss p r)) ∧
    (∀ k ∈ TieCutEq.freeT a (textOf R S' f ss p r),
      (guardOf (tableOf a.sortVars a.pattern) k).isFreeEvar ((tableOf a.sortVars a.pattern).ev (evarKey x)) = false) ∧
    (tr ⟨tableOf a.sortVars a.pattern, []⟩ p).isFreeEvar ((tableOf a.sortVars a.pattern).ev (evarKey x)) = false ∧
    (tr ⟨tableOf a.sortVars a.pattern, []⟩ r).isFreeEvar ((tableOf a.sortVars a.pattern).ev (evarKey x)) = false ∧
    (trSortApp (tableOf a.sortVars a.pattern) (sym (.symbol f.ident.name)) ss).isFreeEvar
      ((tableOf a.sortVars a.pattern).ev (evarKey x)) = false ∧
    (trSort (tableOf a.sortVars a.pattern) R).isFreeEvar ((tableOf a.sortVars a.pattern).ev (evarKey x)) = false ∧
    (trSort (tableOf a.sortVars a.pattern) R).isFreeEvar topVar = false ∧
    (trSort (tableOf a.sortVars a.pattern) S').isFreeEvar topVar = false := by
  unfold okB at h
  rw [hp] at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hR, hS⟩, hS'⟩, hx⟩, hTG⟩, hGT⟩, hgd⟩, hfp⟩, hfr⟩, hff⟩, hfR⟩, htR⟩, htS'⟩ := h
  refine ⟨?_, hS, hS', hx, hTG, hGT, hgd, hfp, hfr, hff, hfR, htR, htS'⟩
  cases R with
  | var α => exact ⟨α, rfl, by simpa using hR⟩
  | ctor _ _ => simp at hR

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

open HoldsShape (NodeFacts) in
/-- **Item to sentence**: with the constructors' facts and the argument pattern one element of its
sort, a model of Γ's item is a model of the text's form of the equation. -/
theorem ovlMem_entailed [Inhabited M] {c : Semantics} (N : NodeFacts c I) {a : Kore.Axiom} {g : P}
    (hg : textItem a = some g) (hok : okB c a = true) (hone : ArgOne I a)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) : I ⊧ᴵ g := by
  obtain ⟨R, S, x, p, S', f, ss, r, hp, rfl⟩ := textItem_parts hg
  obtain ⟨⟨α, rfl, hα⟩, ⟨s, hs, rfl⟩, ⟨s', hs', rfl⟩, hxs, -, hGT, hgd, hfp, hfr, hff, hfR, htR, htS'⟩ :=
    okB_parts hp hok
  have hD := N.defOK
  have hc := N.ceilDef
  obtain ⟨σ, hσ, hS⟩ := N.sort hs
  obtain ⟨σ', hσ', hS'⟩ := N.sort hs'
  have hpat := parts_eq hp
  have hone' := hone _ _ _ _ _ _ _ _ hp
  rw [TieCutEq.trAxiom_implies a hpat] at h
  generalize tableOf a.sortVars a.pattern = T at h hone' hgd hfp hfr hff hfR htR htS' ⊢
  rw [hpat] at h
  intro e m
  unfold TieCutEq.itemAt
  rw [interpret_impl]
  intro hgs
  rw [TieUnion.interp_conjListAll] at hgs
  have hg' : ∀ k ∈ TieCutEq.freeT a (textOf (.var α) (srtOf c s') f ss p r), (guardOf T k).interpret I e m :=
    fun k hk => hgs _ (List.mem_map_of_mem hk)
  obtain ⟨b, hbS, hb⟩ := hone' e m hg'
  have hbσ : Inh I σ b := (interp_inhOf_of (hS T e)).mp hbS
  have hρ : IsSort I (e.evalEvar (T.ev (sortVarKey α))) := by
    have h3 := hg' _ hα
    unfold sortVarKey guardOf sortGuard at h3
    rw [interp_member hD, interp_sortsDomain] at h3
    exact h3
  have hR : ∀ e' : Valuation M, e'.evalEvar (T.ev (sortVarKey α)) = e.evalEvar (T.ev (sortVarKey α)) →
      ∀ a0, (trSort T (.var α)).interpret I e' a0 ↔ a0 = e.evalEvar (T.ev (sortVarKey α)) := fun e' he' a0 => by
    rw [trSort, ← he']; exact interp_evar
  -- the item at the valuation with p's element at x
  let e' : Valuation M := updE e (T.ev (evarKey x)) b
  have hxe' : e'.evalEvar (T.ev (evarKey x)) = b := Function.update_same _ _ _
  have hαe' : e'.evalEvar (T.ev (sortVarKey α)) = e.evalEvar (T.ev (sortVarKey α)) := by
    have h3 := notFree_upd (I := I) hfR e b (e.evalEvar (T.ev (sortVarKey α)))
    rw [trSort, interp_evar, interp_evar] at h3
    exact (h3.mpr rfl).symm
  have h1 := h e' m
  unfold TieCutEq.itemAt at h1
  rw [interpret_impl] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    rcases hGT k hk with rfl | hk
    · rw [TieRuleLhs.guard_evarKey hD, hxs, hxe']
      exact (interp_inhOf_of (hS T e')).mpr hbσ
    · exact (notFree_upd (hgd k hk) e b m).mpr (hg' k hk))
  rw [interp_equal hD] at h2 ⊢
  intro a0
  have h3 := h2 a0
  rw [TieCutEq.tr_implies, interp_sImp, interp_inhOf_of (hR e' hαe')] at h3
  unfold textOf
  rw [TieCutEq.tr_equals, interp_sEquals hD hc (hS' T e) (hR e rfl) hσ' hρ, interp_inhOf_of (hR e rfl)]
  refine ⟨fun hf => hf.1, fun ha0 => ⟨ha0, fun y hy => ?_⟩⟩
  have hprem : (tr ⟨T, []⟩ (.and (.var α) [.top (.var α),
      .and (.var α) [.in (srtOf c s) (.var α) (.var (.evar x)) p, .top (.var α)]])).interpret I e' a0 := by
    have htop : (tr ⟨T, []⟩ (.top (.var α))).interpret I e' a0 := by
      rw [TieCutEq.tr_top, interp_sTop hD htR, interp_inhOf_of (hR e' hαe')]; exact ha0
    rw [tr_and2, tr_and2, interp_sAnd, interp_sAnd, TieCutEq.tr_in, TieCutEq.tr_evar]
    refine ⟨htop, ?_, htop⟩
    rw [mem_iff_cut hD hc (hS T e') (hR e' hαe') hσ hρ _ (by rw [hxe']; exact hbσ), hxe']
    exact ⟨(notFree_upd hfp e b b).mpr ((hb b).mpr rfl), ha0⟩
  have h4 := (h3.mpr ha0).2 hprem
  rw [TieCutEq.tr_equals, interp_sEquals hD hc (hS' T e') (hR e' hαe') hσ' hρ] at h4
  have h5 := h4.2 y hy
  rw [tr_app1, tr_and2, interp_sAnd, TieCutEq.tr_top, interp_sTop hD htS', interp_inhOf_of (hS' T e'),
    TieCutEq.tr_evar] at h5
  rw [tr_app1]
  have h6 : (trSortApp T (sym (.symbol f.ident.name)) ss ⬝ tr ⟨T, []⟩ p).interpret I e y ↔
      (trSortApp T (sym (.symbol f.ident.name)) ss ⬝ .evar (T.ev (evarKey x))).interpret I e' y :=
    app_congr (fun u => (notFree_upd hff e b u).symm) (fun v => by
      rw [hb v, interp_evar, hxe']) y
  rw [h6, h5]
  exact ⟨fun hh => (notFree_upd hfr e b y).mp hh.1, fun hh => ⟨(notFree_upd hfr e b y).mpr hh, hy⟩⟩

open HoldsShape (NodeFacts) in
/-- **Sentence to item**: with the constructors' facts and the argument pattern one element of its
sort, a model of the text's form of the equation is a model of Γ's item. -/
theorem ovlMem_from_text [Inhabited M] {c : Semantics} (N : NodeFacts c I) {a : Kore.Axiom} {g : P}
    (hg : textItem a = some g) (hok : okB c a = true) (hone : ArgOne I a)
    (h : I ⊧ᴵ g) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  obtain ⟨R, S, x, p, S', f, ss, r, hp, rfl⟩ := textItem_parts hg
  obtain ⟨⟨α, rfl, hα⟩, ⟨s, hs, rfl⟩, ⟨s', hs', rfl⟩, hxs, hTG, -, -, -, -, -, -, htR, htS'⟩ :=
    okB_parts hp hok
  have hD := N.defOK
  have hc := N.ceilDef
  obtain ⟨σ, hσ, hS⟩ := N.sort hs
  obtain ⟨σ', hσ', hS'⟩ := N.sort hs'
  have hpat := parts_eq hp
  have hone' := hone _ _ _ _ _ _ _ _ hp
  rw [TieCutEq.trAxiom_implies a hpat]
  generalize tableOf a.sortVars a.pattern = T at h hone' htR htS' ⊢
  rw [hpat]
  intro e m
  have h1 := h e m
  unfold TieCutEq.itemAt at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hgs
  rw [TieUnion.interp_conjListAll] at hgs
  have hgG : ∀ k ∈ TieCutEq.freeG a, (guardOf T k).interpret I e m :=
    fun k hk => hgs _ (List.mem_map_of_mem hk)
  have hg' : ∀ k ∈ TieCutEq.freeT a (textOf (.var α) (srtOf c s') f ss p r), (guardOf T k).interpret I e m :=
    fun k hk => hgG k (hTG k hk)
  obtain ⟨b, -, hb⟩ := hone' e m hg'
  have hρ : IsSort I (e.evalEvar (T.ev (sortVarKey α))) := by
    have h3 := hg' _ hα
    unfold sortVarKey guardOf sortGuard at h3
    rw [interp_member hD, interp_sortsDomain] at h3
    exact h3
  have hR : ∀ a0, (trSort T (.var α)).interpret I e a0 ↔ a0 = e.evalEvar (T.ev (sortVarKey α)) := fun a0 => by
    rw [trSort]; exact interp_evar
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hg' k hk)
  rw [interp_equal hD] at h2 ⊢
  intro a0
  have h3 := h2 a0
  unfold textOf at h3
  rw [TieCutEq.tr_equals, interp_sEquals hD hc (hS' T e) hR hσ' hρ, interp_inhOf_of hR] at h3
  rw [TieCutEq.tr_implies, interp_sImp, interp_inhOf_of hR]
  refine ⟨fun hf => hf.1, fun ha0 => ⟨ha0, fun hprem => ?_⟩⟩
  rw [tr_and2, tr_and2, interp_sAnd, interp_sAnd, TieCutEq.tr_in, TieCutEq.tr_evar] at hprem
  have hx : e.evalEvar (T.ev (evarKey x)) = b := (hb _).mp (TieCutEq.sIn_evar_elem hprem.2.1)
  rw [TieCutEq.tr_equals, interp_sEquals hD hc (hS' T e) hR hσ' hρ]
  refine ⟨ha0, fun y hy => ?_⟩
  have h5 := (h3.mpr ha0).2 y hy
  rw [tr_app1] at h5
  rw [tr_app1, tr_and2, interp_sAnd, TieCutEq.tr_top, interp_sTop hD htS', interp_inhOf_of (hS' T e),
    TieCutEq.tr_evar]
  have h6 : (trSortApp T (sym (.symbol f.ident.name)) ss ⬝ .evar (T.ev (evarKey x))).interpret I e y ↔
      (trSortApp T (sym (.symbol f.ident.name)) ss ⬝ tr ⟨T, []⟩ p).interpret I e y :=
    app_congr (fun _ => Iff.rfl) (fun v => by rw [hb v, interp_evar, hx]) y
  rw [h6, h5]
  exact ⟨fun hh => ⟨hh, hy⟩, fun hh => hh.1⟩

open HoldsShape (NodeFacts) in
/-- **The text's form of the equation and Γ's item hold in the same models** with the
constructors' facts in which the argument pattern is one element of its sort. -/
theorem ovlMem_iff [Inhabited M] {c : Semantics} (N : NodeFacts c I) {a : Kore.Axiom} {g : P}
    (hg : textItem a = some g) (hok : okB c a = true) (hone : ArgOne I a) :
    (I ⊧ᴵ g) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) :=
  ⟨ovlMem_from_text N hg hok hone, ovlMem_entailed N hg hok hone⟩

/-- **The argument `inj{A, S}(v)` is one element of S** where v is an element of A: Cons-Fun of
the injection, an item of Γ. -/
theorem argOne_inj [Inhabited M] (hD : DefOK I) {a : Kore.Axiom} {N A : String} {v : Kore.EVar}
    (hf : I ⊧ᴵ (Cons.funItem N (.inj A)).pat) (hi : injB a N A v = true) : ArgOne I a := by
  intro R S x p S' f ss r hp e m hg
  unfold injB at hi
  rw [hp] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hi
  obtain ⟨⟨⟨hpe, hSN⟩, hvA⟩, hv⟩ := hi
  have hvg := (TieRuleLhs.guard_evarKey hD).mp (hg _ hv)
  rw [hvA, inS_iff] at hvg
  obtain ⟨y, hy, hyy⟩ := fun_at hD hf (xs := [e.evalEvar ((tableOf a.sortVars a.pattern).ev (evarKey v))]) rfl
    (fun i z s' hz hs' => by
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
        have hs'' : A = s' := by simpa [KoreAML.Gen.argSorts] using hs'
        rw [← hz, ← hs'']; exact hvg
      | succ i => simp at hz)
  refine ⟨y, by rw [hSN, inS_iff]; exact hy, fun z => ?_⟩
  rw [hpe]
  have h1 := interp_genPat_vars (I := I) N (.inj A) e [(tableOf a.sortVars a.pattern).ev (evarKey v)] z
  simp only [List.map_cons, List.map_nil] at h1
  rw [h1]
  exact hyy z

end

/-- `okB` reads the definition's sort names only. -/
theorem okB_withHooks (c : Semantics) (H : HookParams) (a : Kore.Axiom) : okB (c.withHooks H) a = okB c a := rfl

end TieOvlMem

end KCore
