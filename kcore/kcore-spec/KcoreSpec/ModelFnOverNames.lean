/-
  KCore. Where the name of one function is held by its own items only.

  `avoidsOff_of_lists`: every premise of the theory that is not one of `f`'s own items (`FnOwn`)
  avoids the name `n` (`AvoidsOff`), from
  - `ListsOff`: each item of the theory's lists is one of `f`'s own or holds no symbol named `n`;
  - `valuesN`: the symbols values are built from are not named `n`;
  - the heads `symApp` writes for the hooks, the parameter symbols and the functions other than
    `f` are not `n`;
  - `listsOffB`, `listsOff_of_decided`: `ListsOff` as a check of the lists;
  - `f`'s clauses fail together at no argument list of its sorts, so the theory states no rest of
    `f` (`ΓFallback` has no item of `f`).
  The premises stated at every value are a symbol applied at values equal to a value or to `⊥`, a
  value in its sort, and two values apart; they hold no symbol named `n` by `cleanN_graph` and
  `cleanN_val`.
-/
import KcoreSpec.ModelFnOver

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **The lists of the theory hold the name `n` in `f`'s own items only**: each item of the
signature, the constructors, the functions, the rules and the step's closure is one of `f`'s own
(`FnOwn`) or holds no symbol named `n`; the collections' items and Bool's closure hold none. -/
def ListsOff (c : Semantics) (f : Sym) (n : String) : Prop :=
  (∀ it ∈ sigItems c ++ consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c],
    FnOwn c f it.pat ∨ GenEqs.NameFree.cleanN [n] it.pat = true) ∧
  (∀ k ∈ c.allColls, GenEqs.NameFree.cleanN [n] (collNoJunk c k) = true ∧
    ∀ φ ∈ collAxioms c k, GenEqs.NameFree.cleanN [n] φ = true) ∧
  GenEqs.NameFree.cleanN [n] (boolClosed c) = true

/-- The patterns of `f`'s own items, as a list. -/
def fnOwnPats (c : Semantics) (f : Sym) : List KoreAML.P :=
  (c.fns.filter fun fn => decide (fn.label = f)).flatMap (fun fn => (kernelItems (fnEquationsK c fn)).map (·.pat)) ++
  (c.allFns.filter fun fn => decide (fn.label = f)).map (fun fn => (symArityItem c fn.sig).pat)

/-- A pattern of the list is one of `f`'s own items. -/
theorem fnOwn_of_mem {f : Sym} {φ : KoreAML.P} (h : φ ∈ fnOwnPats c f) : FnOwn c f φ := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨fn, hfn, hφ⟩ := List.mem_flatMap.mp h
    obtain ⟨hfn, hl⟩ := List.mem_filter.mp hfn
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hφ
    exact .inl ⟨fn, hfn, of_decide_eq_true hl, it, hit, rfl⟩
  · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp h
    obtain ⟨hfn, hl⟩ := List.mem_filter.mp hfn
    exact .inr ⟨fn, hfn, of_decide_eq_true hl, rfl⟩

/-- `ListsOff`, decided: each item of the lists is one of `fnOwnPats` or holds no symbol named
`n`. -/
def listsOffB (c : Semantics) (f : Sym) (n : String) : Bool :=
  (sigItems c ++ consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).all
    (fun it => (fnOwnPats c f).any (fun ψ => decide (ψ = it.pat)) || GenEqs.NameFree.cleanN [n] it.pat) &&
  c.allColls.all (fun k => GenEqs.NameFree.cleanN [n] (collNoJunk c k) &&
    (collAxioms c k).all (GenEqs.NameFree.cleanN [n])) &&
  GenEqs.NameFree.cleanN [n] (boolClosed c)

/-- `ListsOff` where `listsOffB` holds. -/
theorem listsOff_of_decided {f : Sym} {n : String} (h : listsOffB c f n = true) : ListsOff c f n := by
  simp only [listsOffB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun it hit => ?_, fun k hk => h2 k hk, h3⟩
  rcases h1 it hit with ⟨ψ, hψ, he⟩ | hc
  · exact .inl (fnOwn_of_mem (he ▸ hψ))
  · exact .inr hc

open GenEqs.NameFree in
/-- **Every premise that is not one of `f`'s own items avoids the name `n`**, where the lists hold
`n` in `f`'s own items only (`ListsOff`), the symbols of values and the heads applied at values,
`f`'s aside, are not named `n`, and the clauses of `f` fail together at no argument list of its
sorts. -/
theorem avoidsOff_of_lists {f : Sym} {n : String} (hrb : RangeBelow c) (hL : ListsOff c f n)
    (hV : valuesN c [n] = true)
    (hGh : ∀ k ∈ hookSigs, appOKN c [n] k.name = true)
    (hGp : ∀ k ∈ c.params, appOKN c [n] k.sig.name = true)
    (hGf : ∀ g ∈ c.allFns, g.label ≠ f → appOKN c [n] g.label = true)
    (hnf : ∀ fn ∈ c.allFns, fn.label = f → ∀ vs, c.sortsOf vs = some fn.args →
      ¬ ∀ cl ∈ fn.clauses, Fails c vs cl) :
    AvoidsOff c f n := by
  obtain ⟨hLi, hLc, hLb⟩ := hL
  have hclean : ∀ {ψ : KoreAML.P}, cleanN [n] ψ = true → AvoidsFn n ψ :=
    fun hc => cleanN_spec hc (List.mem_singleton.mpr rfl)
  have hdef : ∀ x : EVar, cleanN [n] (@definedness KoreAML.Sym _ x) = true := fun x => by
    simp [definedness, Pattern.universal, Pattern.negation]
  intro φ hφ ho
  rcases hφ with hφ | hφ
  rotate_left
  · have he : φ = (stepClosureItem c).pat := hφ
    subst he
    exact hclean ((hLi _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))).resolve_left ho)
  rcases hφ with hφ | hφ
  rotate_left
  · have he : φ = boolClosed c := hφ.2.2
    subst he
    exact hclean hLb
  rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
  · -- the signature
    rcases hφ with (⟨it, hit, rfl⟩ | ⟨x, rfl⟩) | ⟨lit, rfl⟩
    · exact hclean ((hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hit))))).resolve_left ho)
    · exact hclean (hdef x)
    · exact hclean (by
        simp [KoreAML.dvArityItem, KoreAML.guarded, KoreAML.conjList, KoreAML.sortGuard, ML.member, ML.included,
          ML.total, Pattern.negation, Pattern.conjunction, Pattern.disjunction, KoreAML.sortsDomain,
          KoreAML.inhOf, KoreAML.sym, isNm])
  · -- the constructors
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean ((hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hit))))).resolve_left ho)
    · exact hclean (hdef x)
  · -- the domains
    rcases hφ with ⟨k, vs, r, hk, hvs, hr, hsil, rfl⟩ | ⟨k, vs, hk, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ |
      ⟨v, w, s, hds, hv, hw, hne, rfl⟩ | ⟨k, hk, rfl⟩
    · refine hclean (cleanN_graph hV (hGh k hk) hvs ?_)
      cases r with
      | none => rfl
      | some v =>
        exact cleanN_val hV v _ (hook_sorted (fun _ => hrb) (hookSigs_lookup k hk) hvs hr)
    · refine hclean (cleanN_graph hV (hGp k hk) hvs ?_)
      cases hpv : c.paramVal k.sig.name vs with
      | none => rfl
      | some v =>
        obtain ⟨k', -, hs'⟩ := c.paramVal_sorted hpv
        exact cleanN_val hV v _ hs'
    · refine hclean ?_
      rw [cleanN_sExists, cleanN_eq, cleanN_val hV v s hv]
      simp
    · refine hclean ?_
      rw [cleanN_neg, cleanN_and, cleanN_val hV v s hv, cleanN_val hV w s hw]; rfl
    · exact hclean (hLc k hk).1
  · -- the collections
    obtain ⟨k, hk, hmem⟩ := hφ
    exact hclean ((hLc k hk).2 φ hmem)
  · -- the functions
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean ((hLi it (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hit)))).resolve_left ho)
    · exact hclean (hdef x)
  · -- the rules
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean ((hLi it (List.mem_append_left _ (List.mem_append_right _ hit))).resolve_left ho)
    · exact hclean (hdef x)
  · -- the fallbacks
    rcases hφ with ⟨k, vs, hk, hvs, hr, hsil, rfl⟩ | ⟨fn, vs, hfn, hvs, hfail, rfl⟩
    · refine hclean (cleanN_graph hV (hGh k hk) hvs ?_)
      cases hfb : c.fallback k.name vs with
      | none => rfl
      | some v => exact cleanN_val hV v _ (c.fallback_sorted (hookSigs_lookup k hk) hfb)
    · by_cases he : fn.label = f
      · exact absurd hfail (hnf fn hfn he vs hvs)
      · refine hclean (cleanN_graph hV (hGf fn hfn he) hvs ?_)
        cases hfr : c.fnRest fn vs with
        | none => rfl
        | some v => exact cleanN_val hV v _ (Semantics.fnRest_sorted hfr)

end Model

end Faithful

end KCore
