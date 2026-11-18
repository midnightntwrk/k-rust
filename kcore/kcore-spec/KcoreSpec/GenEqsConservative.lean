/-
  The generated equations the account accepts without a function of the definition holding them
  (`Parse.consumedWith`'s arm for generated equations): what holds of them in `Γ`.

  - **Sort predicates (`predEqnOK`).** An equation of a sort predicate `isX` that `predEqnOK`
    accepts against a function `fn` is read (`Parse.clause?`, without an exclusion) as a clause of
    `fn` itself (`predEqnOK_clause`); for an `[owise]` equation, its exclusion's disjuncts pair one
    for one with the clauses of `fn` it negates (`Faithful.lowerClauses`), each read back as that
    clause. Where `fn` is one of `Semantics.sortPreds` (`predProjOK?`, `predProjOK_sortPred`), the
    clause's equation (`prioEquation`) is a premise of `Γ`'s function part (`sortPred_items`): the
    accepted equation is not omitted from `Γ`, it is the clause `Γ` states.
  - **Symbols outside `Γ`'s sentences (`freeB`).** For symbols `ks` of the semantics that are no
    interpreted hooked symbol's name, a decided check that no premise of `Γc c ∪ Γstep c` applies
    them (`free_of_decided`): no item of the theory's lists names one, the values and the symbols
    applied at values name none (the checks of `DetachedB`, at no sort and at `ks`), and no hook
    has the name of one. For the registry's projections `projectSym X` of a definition that reads
    none of them, this is the first half of the conservativity of their equations: the symbol may
    be reinterpreted in a model of `Γ` without changing what any premise of `Γ` denotes.

  The model half is GenEqsModel.lean: the value model with such a symbol's application replaced is
  a model of the theory in which the symbol's equations at values hold. Not here: the freeness of
  a name that the semantics does not number (a constructor argument's projection, an own sort's
  projection).
-/
import KcoreSpec.DetachedB
import KcoreSpec.Account

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

/-! ## Sort predicates' equations -/

theorem optBeq_eq {x y : Option Term}
    (h : (match x, y with
      | none, none => true
      | some t, some u => Term.beq t u
      | _, _ => false) = true) : x = y := by
  cases x <;> cases y <;> simp only at h
  · rfl
  · cases h
  · cases h
  · exact congrArg some (Det.Term.beq_sound h)

theorem isTop_eq {p : Cond} (h : p.isTop = true) : p = .top := by
  cases p <;> simp_all [Cond.isTop]

/-- `clauseSame` is equality. -/
theorem clauseSame_eq {a b : Clause} (h : Parse.clauseSame a b = true) : a = b := by
  obtain ⟨av, ap, aq, ar, ae, apr, aas, ax, apre, apost⟩ := a
  obtain ⟨bv, bp, bq, br, be, bpr, bas, bx, bpre, bpost⟩ := b
  simp only [Parse.clauseSame, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hp⟩, hq⟩, hr⟩, he⟩, hpr⟩, has⟩, hx⟩, hpa⟩, hpo⟩, hpb⟩, hpob⟩ := h
  have := Det.Term.beqList_sound hp
  have := Det.Term.beq_sound hr
  have := optBeq_eq hq
  have := optBeq_eq he
  have := isTop_eq hpa
  have := isTop_eq hpo
  have := isTop_eq hpb
  have := isTop_eq hpob
  subst_vars
  rfl

/-- An `Option`-valued `mapM` that pairs each element with what it finds keeps the elements. -/
theorem mapM_pair_snd {α β : Type} (g : α → Option β) :
    ∀ (xs : List α) (ys : List (β × α)), xs.mapM (fun x => (g x).map (·, x)) = some ys → ys.map (·.2) = xs
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hg : g x with
    | none => simp [hg] at h
    | some b =>
      cases hr : xs.mapM (fun x => (g x).map (·, x)) with
      | none => simp [hg, hr] at h
      | some zs =>
        simp [hg, hr] at h
        subst h
        simp [mapM_pair_snd g xs zs hr]

/-- **An equation `predEqnOK` accepts against `fn` is a clause of `fn`.** The plain reading of
the equation (`clause?` without an exclusion; it has no `requires`, `ensures` or selector-domain
form) is a clause `cl` of `fn`. Where the equation is an `[owise]` one with the exclusion's
disjuncts `ds`: there are equations `es` of the text, paired with the clauses of `fn` that `cl`
negates (`lowerClauses fn cl`, in order), one disjunct for each, and each equation read with the
disjunct `pairExcl` gives it is that clause. -/
theorem predEqnOK_clause {N : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {fn : Fn}
    {e : Parse.RawEqn} (h : Parse.predEqnOK N msrc eqs fn e = true) :
    ∃ cl cp, Parse.clause? N msrc e none = .ok (cl, cp) ∧ cl ∈ fn.clauses ∧
      ∀ ds, e.competitors = some ds → ∃ es : List (Parse.RawEqn × Clause),
        es.map (·.2) = lowerClauses fn cl ∧ ds.length = es.length ∧
        ∀ q ∈ (Parse.pairExcl (es.map (·.1)) ds).zip es,
          ∃ cp', Parse.clause? N msrc q.1.1 q.1.2 = .ok (q.2.2, cp') := by
  unfold Parse.predEqnOK at h
  simp only at h
  split at h
  · cases h
  · rename_i cl hplain
    split at hplain
    · cases hc : Parse.clause? N msrc e none with
      | error _ => rw [hc] at hplain; cases hplain
      | ok r =>
        rw [hc] at hplain
        obtain ⟨cl0, cp⟩ := r
        simp only [Except.toOption, Option.map_some, Option.some.injEq] at hplain
        subst hplain
        simp only [Bool.and_eq_true, List.any_eq_true] at h
        obtain ⟨⟨cl', hcl', hsame⟩, hcomp⟩ := h
        have := clauseSame_eq hsame
        subst this
        refine ⟨cl0, cp, rfl, hcl', fun ds hds => ?_⟩
        rw [hds] at hcomp
        simp only at hcomp
        split at hcomp
        · cases hcomp
        · rename_i es hes
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcomp
          refine ⟨es, mapM_pair_snd _ _ es hes, hcomp.1, fun q hq => ?_⟩
          have hq' := hcomp.2 q hq
          obtain ⟨⟨e', ex⟩, ⟨e'', lc⟩⟩ := q
          simp only at hq' ⊢
          cases hc' : Parse.clause? N msrc e' ex with
          | error _ => rw [hc'] at hq'; cases hq'
          | ok r' =>
            rw [hc'] at hq'
            obtain ⟨cl'', cp''⟩ := r'
            simp only at hq'
            rw [clauseSame_eq hq']
            exact ⟨cp'', rfl⟩
    · cases hplain

/-- **`predProjOK?` accepts a sort predicate's equation against its `sortPreds` function**: where
it is `some true` of an equation whose head is no projection, the head is a function of
`c.sortPreds` of that name and `predEqnOK` holds of it. -/
theorem predProjOK_sortPred {N : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics}
    {e : Parse.RawEqn} (h : Parse.predProjOK? N msrc eqs c e = some true)
    (hX : KoreAML.Parse.dropPrefix? "Lblproject'Coln'" e.fn = none) :
    ∃ fn ∈ c.sortPreds, c.symName fn.label = e.fn ∧ Parse.predEqnOK N msrc eqs fn e = true := by
  unfold Parse.predProjOK? at h
  rw [hX] at h
  simp only at h
  split at h
  · cases hf : c.sortPreds.find? (c.symName ·.label == e.fn) with
    | none => rw [hf] at h; cases h
    | some fn =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hp := List.find?_some hf
      simp only [beq_iff_eq] at hp
      exact ⟨fn, List.mem_of_find?_eq_some hf, hp, h⟩
  · cases h

/-- **A clause of a sort predicate states a premise of `Γ`**: each item of its equation
(`prioEquation`) is a premise of `ΓFns`. -/
theorem sortPred_items {c : Semantics} {fn : Fn} {cl : Clause} (hfn : fn ∈ c.sortPreds) (hcl : cl ∈ fn.clauses) :
    ∀ it ∈ kernelItems [prioEquation c fn cl], ΓFns c it.pat := by
  intro it hit
  refine Or.inl ⟨it, ?_, rfl⟩
  unfold fnItems
  refine List.mem_flatMap.mpr ⟨fn, List.mem_append_right _ hfn, ?_⟩
  unfold kernelItems at hit ⊢
  obtain ⟨s, hs, hs'⟩ := List.mem_filterMap.mp hit
  rw [List.mem_singleton] at hs
  subst hs
  exact List.mem_filterMap.mpr ⟨_, List.mem_map.mpr ⟨cl, hcl, rfl⟩, hs'⟩

/-- **An accepted sort predicate equation is a clause `Γ` states**: where `predProjOK?` accepts an
equation whose head is no projection, its plain reading is a clause of a function of `sortPreds`,
and that clause's equation is a premise of `Γ`. -/
theorem sortPredEqn_in_Γ {N : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics}
    {e : Parse.RawEqn} (h : Parse.predProjOK? N msrc eqs c e = some true)
    (hX : KoreAML.Parse.dropPrefix? "Lblproject'Coln'" e.fn = none) :
    ∃ fn ∈ c.sortPreds, c.symName fn.label = e.fn ∧ ∃ cl cp, Parse.clause? N msrc e none = .ok (cl, cp) ∧
      cl ∈ fn.clauses ∧ ∀ it ∈ kernelItems [prioEquation c fn cl], Γ c it.pat := by
  obtain ⟨fn, hfn, hname, hok⟩ := predProjOK_sortPred h hX
  obtain ⟨cl, cp, hc, hcl, -⟩ := predEqnOK_clause hok
  exact ⟨fn, hfn, hname, cl, cp, hc, hcl, fun it hit => Or.inl (Or.inl (Or.inr (sortPred_items hfn hcl it hit)))⟩

/-! ## Symbols no premise of `Γ` applies -/

open DetachedB in
/-- **No premise of the theory applies a symbol of `ks`** where `freeB` holds: `Γc c ∪ Γstep c`'s
premises name no symbol of `ks` (the proof of `detached_of_decided`'s third part, where with no
sort and no hook among the names no premise is the registry's own). -/
theorem free_of_decided (c : Semantics) (ks : List Sym) (h : c.coreOK = true) (hd : freeB c ks = true) :
    ∀ φ, (Γc c ∪ Γstep c) φ → ¬ ∃ σ ∈ psyms φ, names c [] ks σ := by
  simp only [freeB, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hL, hV⟩, hG⟩, hK⟩ := hd
  simp only [graphsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨hGh, hGp⟩, hGf⟩ := hG
  simp only [listsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hL
  obtain ⟨⟨⟨hLs, hLi⟩, hLc⟩, hLb⟩ := hL
  have hKk : ∀ k ∈ hookSigs, kOK c [] ks k.name = true := fun k hk => List.all_eq_true.mp hK k hk
  have hsOK : ∀ s, sOK c [] ks s = true := fun s => by simp [sOK, isName]
  intro φ hφ hname
  have hclean : ∀ {ψ : KoreAML.P}, ψ = φ → clean c [] ks ψ = true → False :=
    fun he hc => (clean_spec hc) (he ▸ hname)
  rcases hφ with hφ | hφ
  rotate_left
  · exact hclean hφ.symm (hLi _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  rcases hφ with hφ | hφ
  rotate_left
  · exact hclean hφ.2.2.symm hLb
  rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
  · -- the signature
    rcases hφ with (⟨it, hit, rfl⟩ | ⟨x, rfl⟩) | ⟨lit, rfl⟩
    · rcases hLs it hit with h' | h'
      · exact hclean rfl h'
      · simp only [regSig, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at h'
        rcases h' with ⟨s, hs, -⟩ | ⟨g, hg, hgk, -⟩
        · cases hs
        · have hn : isName c [] ks (.symbol (c.symName g.name)) = true :=
            List.any_eq_true.mpr ⟨g.name, List.contains_iff_mem.mp hgk, beq_self_eq_true _⟩
          have := hKk g hg
          simp [kOK, hn] at this
    · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
    · exact hclean rfl (by
        simp [KoreAML.dvArityItem, KoreAML.guarded, KoreAML.conjList, KoreAML.sortGuard, ML.member, ML.included,
          ML.total, Pattern.negation, Pattern.conjunction, Pattern.disjunction, KoreAML.sortsDomain,
          KoreAML.inhOf, KoreAML.sym, isName])
  · -- the constructors
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hit))))
    · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
  · -- the domains
    rcases hφ with ⟨k, vs, r, hk, hvs, hr, hsil, rfl⟩ | ⟨k, vs, hk, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ |
      ⟨v, w, s, hds, hv, hw, hne, rfl⟩ | ⟨k, hk, rfl⟩
    · rcases hGh k hk with h' | h'
      · rw [hKk k hk] at h'; cases h'
      · refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
        cases r with
        | none => rfl
        | some v =>
          exact clean_val hV v _ (hook_sorted (fun _ => rangeBelow_of_core h) (hookSigs_lookup k hk) hvs hr)
            (h'.2 _ (List.mem_cons_self ..))
    · have h' := hGp k hk
      refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
      cases hpv : c.paramVal k.sig.name vs with
      | none => rfl
      | some v =>
        obtain ⟨k', hk', hs'⟩ := c.paramVal_sorted hpv
        rw [c.lookupParam_eq] at hk'
        exact clean_val hV v _ hs' ((hGp k' (List.mem_of_find?_eq_some hk')).2 _ (List.mem_cons_self ..))
    · refine hclean rfl ?_
      rw [clean_sExists, clean_eq, clean_val hV v s hv (hsOK s)]
      simpa [sOK] using hsOK s
    · refine hclean rfl ?_
      rw [clean_neg, clean_and, clean_val hV v s hv (hsOK s), clean_val hV w s hw (hsOK s)]; rfl
    · have h' := hLc k hk
      have hb : ¬ (builtinColls.contains k = true ∧ ([] : List Srt).contains k.sort = true) := by simp
      simp only [hb, ↓reduceIte] at h'
      exact hclean rfl (Bool.and_eq_true_iff.mp h').1
  · -- the collections
    obtain ⟨k, hk, hmem⟩ := hφ
    have h' := hLc k hk
    have hb : ¬ (builtinColls.contains k = true ∧ ([] : List Srt).contains k.sort = true) := by simp
    simp only [hb, ↓reduceIte] at h'
    exact hclean rfl (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h').2 φ hmem)
  · -- the functions
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hit))))
    · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
  · -- the rules
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_right _ hit)))
    · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
  · -- the fallbacks
    rcases hφ with ⟨k, vs, hk, hvs, hr, hsil, rfl⟩ | ⟨fn, vs, hfn, hvs, -, rfl⟩
    · rcases hGh k hk with h' | h'
      · rw [hKk k hk] at h'; cases h'
      · refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
        cases hfb : c.fallback k.name vs with
        | none => rfl
        | some v =>
          exact clean_val hV v _ (c.fallback_sorted (hookSigs_lookup k hk) hfb) (h'.2 _ (List.mem_cons_self ..))
    · have h' := hGf fn hfn
      refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
      cases hfr : c.fnRest fn vs with
      | none => rfl
      | some v => exact clean_val hV v _ (Semantics.fnRest_sorted hfr) (h'.2 _ (List.mem_cons_self ..))

/-- **A symbol of `ks` occurs in no premise of the theory** where `freeB` holds. -/
theorem sym_free (c : Semantics) (ks : List Sym) (h : c.coreOK = true) (hd : freeB c ks = true)
    {k : Sym} (hk : k ∈ ks) : ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol (c.symName k) ∉ psyms φ :=
  fun φ hφ hm => free_of_decided c ks h hd φ hφ ⟨_, hm, .inr ⟨k, hk, rfl⟩⟩

end GenEqs

end KCore
