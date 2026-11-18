/-
  What a model of the theory without the registry family (`Γown c D`, RegistryOwn.lean) says of
  the values of the sorts outside `D`: each denotes one element of its sort (`own_single`), and
  distinct values of one such sort denote distinct elements (`own_apart`).

  The proof reads definedness, the constructors' items (`consItemsK`), and, at the sorts outside
  `D`, that a value is one element and that distinct values of a sort of `distinctSorts` are
  distinct elements (`OwnVals`). It reads no graph of a hooked symbol. Every constructor sort is K,
  KItem or a sort below KItem. At KItem and below, two values are told apart by Map's distinctness
  (`map_apart_own`): their one-entry maps are distinct values of Map, which is never detached.
  At K, which is no open generator's sort, by K's generators (Cons-Inj, Cons-Dist), their arguments
  told apart in turn. The graph of `_==K_` gives the same where the theory keeps it
  (`values_apart_own`).

  `OwnVals` is given for the decided form of `Detached` (`ownVals_of_decided`, at
  `DetachedB.names`).
-/
import KcoreSpec.DetachedB
import KcoreSpec.ConsExtModel

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort Closed KGround)

/-- What the lemmas below read of a model `I`, at the sorts `O`: definedness; the constructors'
items; a value of a sort of `O` is one element of it; distinct values of a sort of `O` among
`distinctSorts` share no element; both sorts of a subsort pair and the argument sorts of a
constructor and of an overloading symbol are in `O`. -/
structure OwnVals (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (O : Srt → Prop) : Prop where
  defOK : DefOK I
  cons : ∀ it ∈ consItemsK c, I ⊧ᴵ it.pat
  single : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → O s →
    I ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName s)) (den c v ≡ .evar ⟨1⟩)
  apart : ∀ {v w : GroundTerm} {s : Srt}, (distinctSorts c).contains s = true → O s →
    c.sortOf v = some s → c.sortOf w = some s → GroundTerm.cmp v w ≠ .eq → I ⊧ᴵ ∼(den c v ⋀ den c w)
  sub : ∀ {a b : Srt}, (a, b) ∈ c.subsorts → O a ∧ O b
  sig : ∀ k ∈ c.ctorSigs ++ c.ovlSigs, ∀ s ∈ k.args, O s

open DetachedB in
/-- **A model of the theory without the names of `ss` and `ks`**, where the decided check holds,
gives `OwnVals` at the sorts without a name. -/
theorem ownVals_of_decided {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks)) :
    OwnVals c I (fun s => sOK c ss ks s = true) := by
  simp only [detachedB, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨-, hL⟩, hV⟩, -⟩ := hd
  simp only [listsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hL
  obtain ⟨⟨⟨-, hLi⟩, -⟩, -⟩ := hL
  have mem : ∀ {φ : KoreAML.P}, Γ c φ → clean c ss ks φ = true → I ⊧ᴵ φ := fun {φ} h hc =>
    hI φ ⟨Or.inl (Or.inl h), fun σ hσ hn => clean_spec hc ⟨σ, hσ, hn⟩⟩
  refine ⟨?_, ?_, ?_, ?_, fun h => valuesB_sub hV h, fun k hk =>
    (valuesB_sig hV (List.mem_append_left _ hk)).2⟩
  · exact KoreAML.defOK_of fun x =>
      mem (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))))))) rfl
  · intro it hit
    exact mem (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, hit, rfl⟩)))))))
      (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hit))))
  · intro v s hv hs
    refine mem (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, s, hv, rfl⟩)))))))) ?_
    rw [clean_sExists, clean_eq, clean_val hV v s hv hs]
    simpa [sOK] using hs
  · intro v w s hds hs hv hw hne
    refine mem (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨v, w, s, hds, hv, hw, hne, rfl⟩))))))))) ?_
    rw [clean_neg, clean_and, clean_val hV v s hv hs, clean_val hV w s hw hs]
    rfl

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {O : Srt → Prop}

/-- A value of a sort of `O` denotes one element, and that element is in the sort. -/
theorem den_single_own (hI : OwnVals c I O) {v : GroundTerm} {s : Srt} (h : c.sortOf v = some s) (hO : O s)
    (e : Valuation M) :
    ∃ a, (∀ m, (den c v).interpret I e m ↔ m = a) ∧ (KoreAML.inhOf (sortP (c.sortName s))).interpret I e a := by
  have hD := hI.defOK
  have hax := hI.single h hO e default
  rw [KoreAML.interp_sExists] at hax
  obtain ⟨a, h1, h2⟩ := hax
  rw [KoreAML.interp_member hD] at h1
  simp only [Function.update_same] at h1
  rw [KoreAML.interp_equal hD] at h2
  refine ⟨a, fun m => ?_, ?_⟩
  · rw [(den_closed c v).interp e ⟨Function.update e.evalEvar ⟨1⟩ a, e.evalSvar⟩ m, h2 m,
      KoreAML.interp_evar]
    simp only [Function.update_same]
  · exact (((Closed.sym _).app (Closed.sym _)).interp _ e a).mp h1

theorem elemOf_spec_own (hI : OwnVals c I O) {v : GroundTerm} {s : Srt} (h : c.sortOf v = some s) (hO : O s)
    (e : Valuation M) :
    (∀ m, (den c v).interpret I e m ↔ m = elemOf c I v) ∧
      (KoreAML.inhOf (sortP (c.sortName s))).interpret I e (elemOf c I v) := by
  obtain ⟨a, ha, has⟩ := den_single_own hI h hO ⟨fun _ => default, fun _ _ => False⟩
  have hs := Classical.epsilon_spec (p := fun a => ∀ m, (den c v).interpret I ⟨fun _ => default, fun _ _ => False⟩ m ↔ m = a) ⟨a, ha⟩
  have heq : elemOf c I v = a := ((ha _).mp ((hs _).mpr rfl))
  refine ⟨fun m => ?_, ?_⟩
  · rw [(den_closed c v).interp e ⟨fun _ => default, fun _ _ => False⟩ m, heq]; exact ha m
  · rw [heq]
    exact (((Closed.sym _).app (Closed.sym _)).interp _ e a).mpr
      ((((Closed.sym _).app (Closed.sym _)).interp _ _ a).mp has)

end

/-! ## Values as generator applications, in a model that satisfies `OwnVals` -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {O : Srt → Prop}
  (hI : OwnVals c I O) [OvlOK c]
include hI


/-- Coherence of injections, from its item: `inj{A,B}(inj{A',A}(x)) = inj{A',B}(x)` for an
element `x` of `A'`, along a chain `A' < A < B` of subsorts. -/
theorem coh_at_own {a' a b : Srt} (h1 : (a', a) ∈ c.subsorts) (h2 : (a, b) ∈ c.subsorts)
    {e : Valuation M} {X : KoreAML.P} {x : M} (hX : ∀ m, X.interpret I e m ↔ m = x)
    (hx : (KoreAML.inhOf (sortP (c.sortName a'))).interpret I e x) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b),
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a'), KoreAML.Cons.sortP (c.sortName a), X]]).interpret I e m ↔
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a'), KoreAML.Cons.sortP (c.sortName b), X]).interpret I e m := by
  have hD := hI.defOK
  have hax := hI.cons _ (coh_mem h1 h2)
  let e' : Valuation M := ⟨Function.update e.evalEvar ⟨1⟩ x, e.evalSvar⟩
  have h := hax e' default
  unfold KoreAML.Cons.cohItem at h
  dsimp only at h
  have hb := KoreAML.interp_guarded h (by
    intro w hw
    rw [mem_one hw, KoreAML.interp_member hD]
    simp only [e', Function.update_same]
    exact (((Closed.sym _).app (Closed.sym _)).interp _ _ x).mp hx)
  rw [KoreAML.interp_equal hD] at hb
  have hXe : ∀ m, X.interpret I e m ↔ (Pattern.evar ⟨1⟩ : KoreAML.P).interpret I e' m := fun m => by
    rw [hX, KoreAML.interp_evar]; simp [e']
  rw [injApp_congr (injApp_congr hXe) m, injApp_congr hXe m]
  exact hb m

theorem elems_all2_own (e : Valuation M) : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss →
    (∀ s ∈ ss, O s) → All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x) (ws.map (den c)) (ws.map (elemOf c I))
  | [], _, _, _ => .nil
  | w :: ws, ss, h, hO => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOf_cons.mp h
    exact .cons (elemOf_spec_own hI h1 (hO _ (List.mem_cons_self ..)) e).1
      (elems_all2_own e h2 fun s hs => hO s (List.mem_cons_of_mem _ hs))

theorem elems_sorts_own : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss → (∀ s ∈ ss, O s) →
    ∀ (i : Nat) x s, (ws.map (elemOf c I))[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x := by
  intro ws ss h hO i x s hx hs
  rw [List.getElem?_map] at hx hs
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨w', hw', hsw⟩ := sortsOf_get h hs'
  rw [hw] at hw'; cases hw'
  exact (inS_iff _).mp (elemOf_spec_own hI hsw (hO _ (List.mem_of_getElem? hs')) KoreAML.val0).2

theorem elems_length_own {ws : List GroundTerm} {ss : List Srt} (h : c.sortsOf ws = some ss) :
    (ws.map (elemOf c I)).length = (ss.map c.sortName).length := by
  rw [List.length_map, List.length_map]; exact sortsOf_length h

/-- The element of a constructor value is the one its constructor builds from its arguments'. -/
theorem den_ctor_gs_own {f : Sym} {ws : List GroundTerm} {k : CtorSig} (hk : lookupSig c.ctorSigs f = some k)
    (hws : c.sortsOf ws = some k.args) (hO : ∀ s ∈ k.args, O s) (e : Valuation M) (m : M) :
    (den c (.ctor f ws)).interpret I e m ↔ GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m := by
  rw [den_ctor, trArgs_appList, koreList_tr', interp_appList_sing _ _ _ (elems_all2_own hI e hws hO)]
  have hn := (lookupSig_spec hk).2
  unfold GS
  simp only [Gen.toK, toK, genHead, hn]
  rfl

/-- The element of a raw application of a symbol with the signature `k` is the one `k`'s generator
builds from its arguments'. -/
theorem den_sig_gs_own {f : Sym} {ws : List GroundTerm} {k : CtorSig} (hn : k.name = f)
    (hws : c.sortsOf ws = some k.args) (hO : ∀ s ∈ k.args, O s) (e : Valuation M) (m : M) :
    (den c (.ctor f ws)).interpret I e m ↔ GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m := by
  rw [den_ctor, trArgs_appList, koreList_tr', interp_appList_sing _ _ _ (elems_all2_own hI e hws hO)]
  unfold GS
  simp only [Gen.toK, toK, genHead, hn]
  rfl

/-- The element of an injection value is the one the injection builds from its argument's. -/
theorem den_inj_gs_own {a b : Srt} {w : GroundTerm} (hw : c.sortOf w = some a) (hO : O a) (e : Valuation M) (m : M) :
    (den c (.inj a b w)).interpret I e m ↔ GS I (c.sortName b) (.inj (c.sortName a)) [elemOf c I w] m := by
  rw [den_inj, interp_injApp]
  constructor
  · rintro ⟨x, hx, hm⟩; rw [(elemOf_spec_own hI hw hO e).1 x] at hx; subst hx; exact hm
  · intro hm; exact ⟨_, ((elemOf_spec_own hI hw hO e).1 _).mpr rfl, hm⟩

/-- Cons-Fun for a generator of a constructor sort, from its item. -/
theorem gen_fun_own {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hnf : c.fnOvl g = false) {xs : List M}
    (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x) :
    ∃ y, InS I (c.sortName N) y ∧ ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ m = y :=
  fun_at (hI.defOK) (hI.cons _ (funItem_mem hN hgm hnf)) (by rw [toK_argSorts]; exact hl)
    (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))

/-- Cons-Inj for a generator of a constructor sort with arguments, from its item. -/
theorem gen_inj_own {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g.argSorts ≠ []) (hnf : c.fnOvl g = false)
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g) ys m) : xs = ys :=
  inj_at (hI.defOK) (hI.cons _ (injItem_mem hN hgm hne hnf)) (by rw [toK_argSorts]; exact hl)
    (by rw [toK_argSorts]; exact hl')
    (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
    (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2)) heq

/-- Cons-Inj for a generator of a constructor sort with arguments, from its item, at arguments that
no overload covers in the model where the generator is a function-overloaded symbol (`UncE`). -/
theorem gen_injU_own {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g.argSorts ≠ [])
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hu : c.fnOvl g = true → UncE I ((ovlArgsOf c g).getD []) (Gen.toK c g).argSorts xs)
    (hu' : c.fnOvl g = true → UncE I ((ovlArgsOf c g).getD []) (Gen.toK c g).argSorts ys)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g) ys m) : xs = ys := by
  cases hf : c.fnOvl g with
  | false => exact gen_inj_own hI hN hgm hne hf hl hl' hxs hys heq
  | true =>
    exact injUnc_at (hI.defOK) (hI.cons _ (injUncItem_mem hN hgm hne hf))
      (by rw [toK_argSorts]; exact hl) (by rw [toK_argSorts]; exact hl')
      (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
      (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2)) (hu hf) (hu' hf) heq

/-- Cons-Dist for two generators of a constructor sort, not both injections, from its item:
they build no element in common from arguments of their sorts. -/
theorem gen_dist_own {N : Srt} (hN : N ∈ consSorts c) {g g' : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hgm' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g ≠ g') (hni : ∀ a b, g = .inj a → g' = .inj b → False)
    (hgd : c.distGuarded g g' = false) (hgd' : c.distGuarded g' g = false)
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g'.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g'.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g') ys m) : False := by
  rcases mem_pairs_of hne hgm hgm' with hp | hp
  · exact dist_at (hI.defOK) (hI.cons _ (distItem_mem hN hp hni hgd))
      (by rw [toK_argSorts]; exact hl) (by rw [toK_argSorts]; exact hl')
      (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
      (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2)) heq
  · exact dist_at (hI.defOK) (hI.cons _ (distItem_mem hN hp (fun a b h1 h2 => hni b a h2 h1) hgd'))
      (by rw [toK_argSorts]; exact hl') (by rw [toK_argSorts]; exact hl)
      (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2))
      (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2)) (fun m => (heq m).symm)

/-- Cons-Dist for two generators of a constructor sort, not both injections, from its item,
guarded or not: they build no element in common from arguments of their sorts that, for each
overloading generator among them, no overload covers in the model (`UncE`). -/
theorem gen_dist_own' {N : Srt} (hN : N ∈ consSorts c) {g g' : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hgm' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g ≠ g') (hni : ∀ a b, g = .inj a → g' = .inj b → False)
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g'.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g'.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hu : ∀ covs, ovlArgsOf c g = some covs → UncE I covs (Gen.toK c g).argSorts xs)
    (hu' : ∀ covs, ovlArgsOf c g' = some covs → UncE I covs (Gen.toK c g').argSorts ys)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g') ys m) : False := by
  cases hgd : c.distGuarded g g' with
  | false => exact gen_dist_own hI hN hgm hgm' hne hni hgd (by rw [distGuarded_symm]; exact hgd) hl hl' hxs hys heq
  | true =>
    have hgd' : c.distGuarded g' g = true := by rw [distGuarded_symm]; exact hgd
    have hl1 : xs.length = (Gen.toK c g).argSorts.length := by rw [toK_argSorts]; exact hl
    have hl2 : ys.length = (Gen.toK c g').argSorts.length := by rw [toK_argSorts]; exact hl'
    rcases mem_pairs_of hne hgm hgm' with hp | hp
    · have hsp := listVal_split xs ys _ _ hl1 hl2
      exact distUnc_at (hI.defOK) (hI.cons _ (distUncItem_mem hN hp hni hgd)) hl1 hl2
        (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun covs hc m => uncoveredP_of (hI.defOK) hsp.1
          (not_mem_xs (off := 0) (n := (Gen.toK c g).argSorts.length)
            (k := (Gen.toK c g).argSorts.length + (Gen.toK c g').argSorts.length + 1) (by omega)) (hu covs hc) m)
        (fun covs hc m => uncoveredP_of (hI.defOK) hsp.2
          (not_mem_xs (off := (Gen.toK c g).argSorts.length) (n := (Gen.toK c g').argSorts.length)
            (k := (Gen.toK c g).argSorts.length + (Gen.toK c g').argSorts.length + 1) (by omega))
          (hu' covs hc) m) heq
    · have hsp := listVal_split ys xs _ _ hl2 hl1
      exact distUnc_at (hI.defOK) (hI.cons _ (distUncItem_mem hN hp (fun a b h1 h2 => hni b a h2 h1) hgd')) hl2 hl1
        (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun covs hc m => uncoveredP_of (hI.defOK) hsp.1
          (not_mem_xs (off := 0) (n := (Gen.toK c g').argSorts.length)
            (k := (Gen.toK c g').argSorts.length + (Gen.toK c g).argSorts.length + 1) (by omega)) (hu' covs hc) m)
        (fun covs hc m => uncoveredP_of (hI.defOK) hsp.2
          (not_mem_xs (off := (Gen.toK c g').argSorts.length) (n := (Gen.toK c g).argSorts.length)
            (k := (Gen.toK c g').argSorts.length + (Gen.toK c g).argSorts.length + 1) (by omega))
          (hu covs hc) m)
        (fun m => (heq m).symm)

/-- Cons-Coh between generator sets: for `x` of `A'` and `y` the element `inj{A',A}(x)`,
`inj{A,B}(y)` and `inj{A',B}(x)` build the same elements. -/
theorem coh_gs_own {a' a b : Srt} (h1 : (a', a) ∈ c.subsorts) (h2 : (a, b) ∈ c.subsorts) {x y : M}
    (hx : InS I (c.sortName a') x) (hy : ∀ m, GS I (c.sortName a) (.inj (c.sortName a')) [x] m ↔ m = y) (m : M) :
    GS I (c.sortName b) (.inj (c.sortName a)) [y] m ↔ GS I (c.sortName b) (.inj (c.sortName a')) [x] m := by
  have hX : ∀ m, (Pattern.evar ⟨1⟩ : KoreAML.P).interpret I (listVal [x]) m ↔ m = x := fun m => by
    rw [KoreAML.interp_evar, listVal_at]; rfl
  have h := coh_at_own hI h1 h2 hX ((inS_iff _).mpr hx) m
  rw [interp_injApp, interp_injApp] at h
  simp only [interp_injApp, hX, exists_eq_left] at h
  constructor
  · intro hm; exact h.mp ⟨y, (hy y).mpr rfl, hm⟩
  · intro hm; obtain ⟨y', hy', hm'⟩ := h.mpr hm; rw [(hy y').mp hy'] at hm'; exact hm'


end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {O : Srt → Prop}
  (hI : OwnVals c I O) [OvlOK c]
variable (hg : genWf c = true)
include hI hg

theorem uncE_of_value_own (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {g : Sym} {o : OvlSig} {ws : List GroundTerm} (hlo : c.lookupOvl g = some o)
    (hws : c.sortsOf ws = some o.sig.args) (hu : c.uncovered g ws = true)
    (hback : ∀ u ∈ ws, ∀ (A B : Srt), (A, B) ∈ c.subsorts → c.sortOf u = some B → ∀ (y : M),
      InS I (c.sortName A) y → GS I (c.sortName B) (.inj (c.sortName A)) [y] (elemOf c I u) → c.lies A B u = true) :
    ∀ covs, ovlArgsOf c (.ctor o.sig) = some covs →
      UncE I covs (Gen.toK c (.ctor o.sig)).argSorts (ws.map (elemOf c I)) := by
  have H : OvlLaws.OvlHyp c := OvlOK.hyp inferInstance htr
  obtain ⟨hom, hn, hio, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts hlo
  intro covs hcov
  simp only [ovlArgsOf, hn, hio, ↓reduceIte, hlo, Option.map_some, Option.some.injEq] at hcov
  subst hcov
  intro as has
  obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp has
  obtain ⟨hlen, hle, -, -⟩ := OvlLaws.over_ovlF H.fnFacts hlo hkg
  have hwl : ws.length = o.sig.args.length := sortsOf_length hws
  have hnc : c.ovlCovers o.sig kg ws = false := by
    simp only [Semantics.uncovered, hlo, List.all_eq_true, Bool.not_eq_true'] at hu
    exact hu kg hkg
  have hall : ¬ ((kg.args.zip o.sig.args).zip ws).all (fun ((A, B), v) => c.lies A B v) = true := fun h => by
    rw [OvlLaws.covers_iff.mpr ⟨hlen, hwl, h⟩] at hnc; cases hnc
  rw [OvlLaws.zip3_all_iff] at hall
  obtain ⟨i, h1, h2, h3, hli⟩ : ∃ i, ∃ h1 : i < kg.args.length, ∃ h2 : i < o.sig.args.length,
      ∃ h3 : i < ws.length, c.lies kg.args[i] o.sig.args[i] ws[i] ≠ true :=
    Classical.byContradiction fun hc => hall fun i h1 h2 h3 =>
      Classical.byContradiction fun hl => hc ⟨i, h1, h2, h3, hl⟩
  have hAB : kg.args[i] ≠ o.sig.args[i] := fun h => hli (h ▸ OvlLaws.lies_self _ _)
  have hsub : (kg.args[i], o.sig.args[i]) ∈ c.subsorts :=
    OvlLaws.mem_of_le ((OvlLaws.zip2_all_iff.mp hle) i h1 h2) hAB
  obtain ⟨u, hu', hsu⟩ := sortsOf_get hws (List.getElem?_eq_getElem h2)
  rw [List.getElem?_eq_getElem h3] at hu'
  cases hu'
  refine ⟨i, c.sortName kg.args[i], c.sortName o.sig.args[i], elemOf c I ws[i], by simp [h1], by
    show (o.sig.args.map c.sortName)[i]? = _
    simp [h2], fun he => hAB ((inferInstance : OvlOK c).names o hom kg hkg _
      (List.mem_cons_of_mem _ (List.getElem_mem h1)) _ (List.mem_cons_of_mem _ (List.getElem_mem h2)) he),
    by simp [h3], ?_⟩
  rintro ⟨y, hy, hm⟩
  exact hli (hback _ (List.getElem_mem h3) _ _ hsub hsu y hy hm)

/-- **An injection's image at a value.** If the element of a value of sort `s` lies in what
`inj{a,s}` builds from an element `b` of `a`, the value is the injection of a value of `a` whose
element is `b` (normalised: an injection of an injection is the injection from the inner sort). -/
theorem inj_back_own (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) :
    ∀ (w : GroundTerm) {a s : Srt}, (a, s) ∈ c.subsorts → c.sortOf w = some s →
    ∀ {b : M}, InS I (c.sortName a) b → GS I (c.sortName s) (.inj (c.sortName a)) [b] (elemOf c I w) →
    ∃ w', c.sortOf w' = some a ∧ w = injNormal a s w' ∧ b = elemOf c I w'
  | .inj a0 s' w0, a, s, has, hsw, b, hb, hm => by
    have hN := (genWf_sub hg has).1
    obtain ⟨y, -, hy⟩ := gen_fun_own hI hN (gensF_inj has) rfl (xs := [b]) rfl (single_sorts hb)
    have hset : ∀ m, GS I (c.sortName s) (.inj (c.sortName a)) [b] m ↔ m = elemOf c I (.inj a0 s' w0) :=
      fun m => by rw [show (.inj (c.sortName a) : KoreAML.Gen) = Gen.toK c (.inj a) from rfl, hy, ((hy _).mp hm)]
    obtain ⟨has0, hni, hw0, rfl⟩ := sortOf_inj.mp hsw
    have hx0 : InS I (c.sortName a0) (elemOf c I w0) := (inS_iff _).mp (elemOf_spec_own hI hw0 (hI.sub has0).1 KoreAML.val0).2
    have hvset : ∀ m, GS I (c.sortName s) (.inj (c.sortName a0)) [elemOf c I w0] m ↔ m = elemOf c I (.inj a0 s w0) :=
      fun m => by rw [← den_inj_gs_own hI hw0 (hI.sub has0).1 KoreAML.val0 m]; exact (elemOf_spec_own hI hsw (hI.sub has).2 KoreAML.val0).1 m
    by_cases h0 : a0 = a
    · subst h0
      have := gen_inj_own hI hN (gensF_inj has) (by simp [Gen.argSorts]) rfl (xs := [b]) (ys := [elemOf c I w0]) rfl rfl
        (single_sorts hb) (single_sorts hx0) (fun m => by
          show GS I _ (.inj _) _ m ↔ GS I _ (.inj _) _ m
          rw [hset, hvset])
      exact ⟨w0, hw0, (injNormal_of_not hni).symm, by simpa using this⟩
    by_cases h1 : (a0, a) ∈ c.subsorts
    · have hw' : c.sortOf (.inj a0 a w0) = some a := sortOf_inj.mpr ⟨h1, hni, hw0, rfl⟩
      have hy1 : ∀ m, GS I (c.sortName a) (.inj (c.sortName a0)) [elemOf c I w0] m ↔ m = elemOf c I (.inj a0 a w0) :=
        fun m => by rw [← den_inj_gs_own hI hw0 (hI.sub has0).1 KoreAML.val0 m]; exact (elemOf_spec_own hI hw' (hI.sub has).1 KoreAML.val0).1 m
      have hc := coh_gs_own hI h1 has hx0 hy1
      have := gen_inj_own hI hN (gensF_inj has) (by simp [Gen.argSorts]) rfl (xs := [b]) (ys := [elemOf c I (.inj a0 a w0)]) rfl rfl
        (single_sorts hb) (single_sorts ((inS_iff _).mp (elemOf_spec_own hI hw' (hI.sub has).1 KoreAML.val0).2)) (fun m => by
          show GS I _ (.inj _) _ m ↔ GS I _ (.inj _) _ m
          rw [hset, hc, hvset])
      exact ⟨.inj a0 a w0, hw', rfl, by simpa using this⟩
    by_cases h2 : (a, a0) ∈ c.subsorts
    · exfalso
      have hN0 := (genWf_sub hg h2).1
      obtain ⟨y2, hy2s, hy2⟩ := gen_fun_own hI hN0 (gensF_inj h2) rfl (xs := [b]) rfl (single_sorts hb)
      have hc := coh_gs_own hI h2 has0 hb hy2
      have := gen_inj_own hI hN (gensF_inj has0) (by simp [Gen.argSorts]) rfl (xs := [y2]) (ys := [elemOf c I w0]) rfl rfl
        (single_sorts hy2s) (single_sorts hx0) (fun m => by
          show GS I _ (.inj _) _ m ↔ GS I _ (.inj _) _ m
          rw [hc, hset, hvset])
      have hy2w : y2 = elemOf c I w0 := by simpa using this
      obtain ⟨w'', -, hw'', -⟩ := inj_back_own htr w0 h2 hw0 hb (by
        show GS I _ (Gen.toK c (.inj a)) _ _
        rw [hy2, hy2w])
      have := injNormal_isInj a a0 w''
      rw [← hw''] at this; rw [hni] at this; cases this
    · exfalso
      have hle : (c.le a0 a || c.le a a0) = false := by
        simp only [Semantics.le, Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_iff_mem]
        exact ⟨⟨h0, by simpa using h1⟩, ⟨fun h => h0 h.symm, by simpa using h2⟩⟩
      have hle' : (c.le a a0 || c.le a0 a) = false := by rw [Bool.or_comm]; exact hle
      have hseq : ∀ m, GS I (c.sortName s) (.inj (c.sortName a0)) [elemOf c I w0] m ↔
          GS I (c.sortName s) (.inj (c.sortName a)) [b] m := fun m => by rw [hset, hvset]
      have hdist : ∀ (C : Srt) (z : M), (C, a0) ∈ c.subsorts → InS I (c.sortName C) z →
          (∀ m, GS I (c.sortName a0) (.inj (c.sortName C)) [z] m ↔ m = elemOf c I w0) → False := by
        intro C z hC hz hzs
        obtain ⟨w'', -, hw'', -⟩ := inj_back_own htr w0 hC hw0 hz (by rw [hzs])
        have := injNormal_isInj C a0 w''
        rw [← hw''] at this; rw [hni] at this; cases this
      rcases mem_pairs_of (fun h => h0 (by cases h; rfl)) (gensF_inj has0) (gensF_inj has) with hp | hp
      · rcases injPair_mem hN hp hle with ⟨-, hit⟩ | ⟨-, hit⟩
        · exact dist_at (hI.defOK) (hI.cons _ (hit)) (xs := [elemOf c I w0]) (ys := [b]) rfl rfl
            (single_sorts hx0) (single_sorts hb) hseq
        · obtain ⟨C, hC, z, hz, hz1, -⟩ := distLb_at (hI.defOK) (hI.cons _ (hit)) hx0 hb hseq
          obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
          exact hdist C' z (mem_lowerBounds hC').1 hz hz1
      · rcases injPair_mem hN hp hle' with ⟨-, hit⟩ | ⟨-, hit⟩
        · exact dist_at (hI.defOK) (hI.cons _ (hit)) (xs := [b]) (ys := [elemOf c I w0]) rfl rfl
            (single_sorts hb) (single_sorts hx0) (fun m => (hseq m).symm)
        · obtain ⟨C, hC, z, hz, -, hz2⟩ := distLb_at (hI.defOK) (hI.cons _ (hit)) hb hx0
            (fun m => (hseq m).symm)
          obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
          exact hdist C' z (mem_lowerBounds hC').2 hz hz2
  | .ctor g ws, a, s, has, hsw, b, hb, hm => by
    exfalso
    have hN := (genWf_sub hg has).1
    obtain ⟨y, -, hy⟩ := gen_fun_own hI hN (gensF_inj has) rfl (xs := [b]) rfl (single_sorts hb)
    have hset : ∀ m, GS I (c.sortName s) (Gen.toK c (.inj a)) [b] m ↔ m = elemOf c I (.ctor g ws) :=
      fun m => by rw [hy, ((hy _).mp hm)]
    rcases sortOf_ctor_cases hg hsw with ⟨kg, hkg, hws, hres⟩ | ⟨o, hlo, -, hws, hu, hres, -⟩ |
      ⟨kp, hko, -, -, -, -, hres, -⟩
    rotate_right
    · -- an open generator's sort has no subsort pair below it (`genWf`'s flat conjunct)
      obtain ⟨hpm, hpr, -, -⟩ := c.lookupOpen_spec hko
      exact genWf_flat_sub hg hpm hpr has hres
    rotate_left
    · obtain ⟨hom, hn, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
      have hOo : ∀ s ∈ o.sig.args, O s := hI.sig _ (List.mem_append_right _ (List.mem_map_of_mem hom))
      have hvset : ∀ m, GS I (c.sortName s) (Gen.toK c (.ctor o.sig)) (ws.map (elemOf c I)) m ↔
          m = elemOf c I (.ctor g ws) := fun m => by
        rw [hres, ← den_sig_gs_own hI hn hws hOo KoreAML.val0 m]; exact (elemOf_spec_own hI hsw (hI.sub has).2 KoreAML.val0).1 m
      exact gen_dist_own' hI hN (gensF_inj has) (by rw [hres]; exact gensF_of_ovl hg hom) (fun h => by cases h)
        (fun _ _ _ h => by cases h) rfl (elems_length_own hI hws) (single_sorts hb) (elems_sorts_own (ss := o.sig.args) hI hws hOo)
        (fun covs h => by simp [ovlArgsOf] at h)
        (uncE_of_value_own hI hg htr hlo hws hu fun u hu' A B hAB hsu y hy hmy => by
          have _hlt := List.sizeOf_lt_of_mem hu'
          obtain ⟨w', hw', rfl, -⟩ := inj_back_own htr u hAB hsu hy hmy
          exact lies_injNormal hw')
        (fun m => by rw [hset, hvset])
    obtain ⟨hkgm, -⟩ := lookupSig_spec hkg
    have hOk : ∀ s ∈ kg.args, O s := hI.sig _ (List.mem_append_left _ hkgm)
    have hvset : ∀ m, GS I (c.sortName kg.result) (Gen.toK c (.ctor kg)) (ws.map (elemOf c I)) m ↔
        m = elemOf c I (.ctor g ws) := fun m => by
      rw [← den_ctor_gs_own hI hkg hws hOk KoreAML.val0 m]; exact (elemOf_spec_own hI hsw (hI.sub has).2 KoreAML.val0).1 m
    rw [← hres] at hvset
    exact gen_dist_own hI hN (gensF_inj has) (by rw [hres]; exact gensF_ctor hg hkgm) (fun h => by cases h)
      (fun _ _ _ h => by cases h)
      (distGuarded_ctorSigs (fun _ h => by cases h) (fun _ h => by cases h; exact hkgm))
      (distGuarded_ctorSigs (fun _ h => by cases h; exact hkgm) (fun _ h => by cases h)) rfl (elems_length_own hI hws) (single_sorts hb)
      (elems_sorts_own (ss := kg.args) hI hws hOk) (fun m => by rw [hset, hvset])
  | .dv s' lit, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | .map s' es, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | .set s' es, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | .list s' es, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  termination_by w => w
  decreasing_by all_goals (simp_wf; omega)


/-- **A constructor's image at a value.** If the element of a value lies in what the constructor
`f` builds from elements of its argument sorts, the value is `f` applied to values whose elements
those are. -/
theorem ctor_back_own (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {k : CtorSig} (hk : lookupSig c.ctorSigs f = some k)
    (hno : ∀ p ∈ c.params, p.raw = true → p.sig.result ≠ k.result)
    {w : GroundTerm} (hsw : c.sortOf w = some k.result) (hOr : O k.result) {bs : List M}
    (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs (elemOf c I w)) :
    ∃ ws, w = .ctor f ws ∧ c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I) := by
  obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
  have hN := genWf_ctor hg hkm
  have hgk := gensF_ctor hg hkm
  obtain ⟨y, -, hy⟩ := gen_fun_own hI hN hgk (fnOvl_ctorSigs hkm) hbl hbs
  have hyw : y = elemOf c I w := ((hy _).mp hm).symm
  have hset : ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs m ↔ m = elemOf c I w := fun m => by
    rw [hy, hyw]
  have hwe := (elemOf_spec_own hI hsw hOr KoreAML.val0).1
  rcases consSort_shape hg hN hsw with ⟨g, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
  · rcases sortOf_ctor_cases hg hsw with ⟨kg, hkg, hws, hres⟩ | ⟨o, hlo, hio, hws, hu, hres, -⟩ |
      ⟨kp, hko, hgn, -, -, -, hres, -⟩
    rotate_right
    · -- the sort is no open generator's
      exfalso
      obtain ⟨hpm, hpr, -, -⟩ := c.lookupOpen_spec hko
      exact hno _ hpm hpr hres.symm
    rotate_left
    · exfalso
      obtain ⟨hom, hn, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
      have hOo : ∀ s ∈ o.sig.args, O s := hI.sig _ (List.mem_append_right _ (List.mem_map_of_mem hom))
      have hgf : g ≠ f := fun h => by
        have := (c.isOvl_parts hio).1
        rw [h] at this
        simp [Semantics.isCtor, hk] at this
      have hvset : ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor o.sig)) (ws.map (elemOf c I)) m ↔
          m = elemOf c I (.ctor g ws) := fun m => by
        rw [hres, ← den_sig_gs_own hI hn hws hOo KoreAML.val0 m]; exact hwe m
      exact gen_dist_own' hI hN hgk (by rw [hres]; exact gensF_of_ovl hg hom)
        (fun h => by cases h; exact hgf (hn.symm.trans hkn))
        (fun _ _ h _ => by cases h) hbl (elems_length_own hI hws) hbs (elems_sorts_own (ss := o.sig.args) hI hws hOo)
        (fun covs h => by simp [ovlArgsOf, isOvl_of_ctorSigs hkm] at h)
        (uncE_of_value_own hI hg htr hlo hws hu fun u hu' A B hAB hsu y hy hmy => by
          obtain ⟨w', hw', rfl, -⟩ := inj_back_own hI hg htr u hAB hsu hy hmy
          exact lies_injNormal hw')
        (fun m => by rw [hset, hvset])
    obtain ⟨hkgm, hkgn⟩ := lookupSig_spec hkg
    have hOk : ∀ s ∈ kg.args, O s := hI.sig _ (List.mem_append_left _ hkgm)
    have hvset : ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor kg)) (ws.map (elemOf c I)) m ↔
        m = elemOf c I (.ctor g ws) := fun m => by
      rw [hres, ← den_ctor_gs_own hI hkg hws hOk KoreAML.val0 m]; exact hwe m
    by_cases hgf : g = f
    · subst hgf
      rw [hk] at hkg; cases hkg
      refine ⟨ws, rfl, hws, ?_⟩
      by_cases hne : k.args = []
      · have h1 : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hbl, hne]; rfl)
        rw [hne] at hws
        rw [h1, sortsOf_nil_eq hws]; rfl
      · exact gen_inj_own hI hN hgk hne (fnOvl_ctorSigs hkm) hbl (elems_length_own hI hws) hbs (elems_sorts_own (ss := k.args) hI hws hOk)
          (fun m => by rw [hset, hvset])
    · exfalso
      have hgm' : Gen.ctor kg ∈ (c.gens k.result).filter (!c.isOpenGen ·) := by rw [hres]; exact gensF_ctor hg hkgm
      exact gen_dist_own hI hN hgk hgm' (fun h => by cases h; exact hgf (hkgn.symm.trans hkn))
        (fun _ _ h _ => by cases h)
        (distGuarded_ctorSigs (fun _ h => by cases h; exact hkm) (fun _ h => by cases h; exact hkgm))
        (distGuarded_ctorSigs (fun _ h => by cases h; exact hkgm) (fun _ h => by cases h; exact hkm)) hbl (elems_length_own hI hws) hbs
        (elems_sorts_own (ss := kg.args) hI hws hOk) (fun m => by rw [hset, hvset])
  · exfalso
    obtain ⟨hab, -, hw0, hb⟩ := sortOf_inj.mp hsw
    subst hb
    have hvset : ∀ m, GS I (c.sortName k.result) (.inj (c.sortName a)) [elemOf c I w0] m ↔
        m = elemOf c I (.inj a k.result w0) :=
      fun m => by rw [← den_inj_gs_own hI hw0 (hI.sub hab).1 KoreAML.val0 m]; exact hwe m
    exact gen_dist_own hI hN hgk (gensF_inj hab) (fun h => by cases h) (fun _ _ h _ => by cases h)
      (distGuarded_ctorSigs (fun _ h => by cases h; exact hkm) (fun _ h => by cases h))
      (distGuarded_ctorSigs (fun _ h => by cases h) (fun _ h => by cases h; exact hkm)) (ys := [elemOf c I w0])
      hbl rfl hbs (single_sorts ((inS_iff _).mp (elemOf_spec_own hI hw0 (hI.sub hab).1 KoreAML.val0).2))
      (fun m => by rw [hset]; exact (hvset m).symm)


end

/-! ## Values below KItem, told apart by Map -/

/-- A value of KItem or of a sort below KItem, as a value of KItem: itself, or its injection
into KItem. -/
def asKItemMp (s : Srt) (v : GroundTerm) : GroundTerm :=
  if s = Srt.kitem then v else injNormal s Srt.kitem v

theorem sortOf_asKItemMp {c : Semantics}
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {s : Srt} (hs : s = Srt.kitem ∨ s ∈ c.sortsBelowKItem) {v : GroundTerm} (hv : c.sortOf v = some s) :
    c.sortOf (asKItemMp s v) = some Srt.kitem := by
  unfold asKItemMp
  split
  · rename_i h; subst h; exact hv
  · rename_i hki; exact sortOf_injNormal htr (kitem_sub (hs.resolve_left hki)) hv

theorem asKItemMp_inj {c : Semantics} (hg : genWf c = true) [OvlOK c] {s : Srt} {v w : GroundTerm}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s) (h : asKItemMp s v = asKItemMp s w) : v = w := by
  unfold asKItemMp at h
  split at h
  · exact h
  · exact injNormal_inj hg hv hw h

/-- An open generator's result sort is not K: K's constructor `kseq` has arguments, and every
constructor of an open generator's sort has none. -/
theorem open_result_ne_k {c : Semantics} (hg : genWf c = true) {k : ParamSig} (hk : k ∈ c.params)
    (hr : k.raw = true) : k.sig.result ≠ Srt.k := by
  intro h
  have hm := (lookupSig_spec (lookup_kseq c)).1
  have := ((genWf_flat_parts hg hk hr).1 _ hm).2 h.symm
  cases this

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {O : Srt → Prop}
  (hI : OwnVals c I O) [OvlOK c]
include hI

/-- An injection of a value, normalised, builds the element the injection builds from the
value's element. -/
theorem den_injNormal_gs_own {s b : Srt} (hsb : (s, b) ∈ c.subsorts) {v : GroundTerm}
    (hv : c.sortOf v = some s) (e : Valuation M) (m : M) :
    (den c (injNormal s b v)).interpret I e m ↔ GS I (c.sortName b) (.inj (c.sortName s)) [elemOf c I v] m := by
  have hOs := (hI.sub hsb).1
  cases hvi : v.isInj
  · rw [injNormal_of_not hvi]; exact den_inj_gs_own hI hv hOs e m
  · cases v with
    | inj a0 s' v0 =>
      obtain ⟨has0, hni, hv0, rfl⟩ := sortOf_inj.mp hv
      have hOa := (hI.sub has0).1
      show (den c (.inj a0 b v0)).interpret I e m ↔ _
      rw [den_inj_gs_own hI hv0 hOa]
      have hx0 : InS I (c.sortName a0) (elemOf c I v0) := (inS_iff _).mp (elemOf_spec_own hI hv0 hOa KoreAML.val0).2
      exact (coh_gs_own hI has0 hsb hx0 (fun m => by
        rw [← den_inj_gs_own hI hv0 hOa KoreAML.val0 m]; exact (elemOf_spec_own hI hv hOs KoreAML.val0).1 m) m).symm
    | _ => cases hvi

/-- Two values of one sort with one element have `asKItemMp` forms that hold of the same
elements. -/
theorem den_asKItemMp_congr_own {s : Srt} (hs : s = Srt.kitem ∨ s ∈ c.sortsBelowKItem) (hO : O s)
    {v w : GroundTerm} (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (he : elemOf c I v = elemOf c I w) (e : Valuation M) (m : M) :
    (den c (asKItemMp s v)).interpret I e m ↔ (den c (asKItemMp s w)).interpret I e m := by
  unfold asKItemMp
  split
  · rw [(elemOf_spec_own hI hv hO e).1, (elemOf_spec_own hI hw hO e).1, he]
  · rename_i hki
    have hb := hs.resolve_left hki
    rw [den_injNormal_gs_own hI (kitem_sub hb) hv, den_injNormal_gs_own hI (kitem_sub hb) hw, he]

/-- **Distinct values of KItem or of a sort below KItem are distinct elements**, in a model with
Map among `O`: for two such values `v`, `w` with one element, the one-entry maps
`{v' ↦ v'}` and `{w' ↦ w'}` of their KItem forms are values of Map whose patterns hold of the same
elements (a one-entry map's pattern is Map's element symbol applied to its entry's), and Map's
distinctness makes them equal. -/
theorem map_apart_own (hg : genWf c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hOm : O Srt.map) {s : Srt} (hs : s = Srt.kitem ∨ s ∈ c.sortsBelowKItem) (hO : O s)
    {v w : GroundTerm} (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (he : elemOf c I v = elemOf c I w) : v = w := by
  refine Classical.byContradiction fun hne => ?_
  have hav := sortOf_asKItemMp htr hs hv
  have haw := sortOf_asKItemMp htr hs hw
  have hmv : c.sortOf (.map Srt.map [(asKItemMp s v, asKItemMp s v)]) = some Srt.map :=
    sortOf_libMap.mpr ⟨rfl, entriesOK_cons.mpr ⟨hav, hav, rfl⟩⟩
  have hmw : c.sortOf (.map Srt.map [(asKItemMp s w, asKItemMp s w)]) = some Srt.map :=
    sortOf_libMap.mpr ⟨rfl, entriesOK_cons.mpr ⟨haw, haw, rfl⟩⟩
  have hne' : GroundTerm.cmp (.map Srt.map [(asKItemMp s v, asKItemMp s v)])
      (.map Srt.map [(asKItemMp s w, asKItemMp s w)]) ≠ .eq := fun h => by
    have h1 := GroundTerm.cmp_eq _ _ h
    simp only [GroundTerm.map.injEq, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at h1
    exact hne (asKItemMp_inj hg hv hw h1.1)
  have hset := den_asKItemMp_congr_own hI hs hO hv hw he KoreAML.val0
  have hden : ∀ m, (den c (.map Srt.map [(asKItemMp s v, asKItemMp s v)])).interpret I KoreAML.val0 m ↔
      (den c (.map Srt.map [(asKItemMp s w, asKItemMp s w)])).interpret I KoreAML.val0 m := fun m => by
    rw [den_mapOne_eq, den_mapOne_eq]
    exact KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) hset) hset m
  have ht := elemOf_spec_own hI hmv hOm KoreAML.val0
  have hax := hI.apart (List.contains_iff_mem.mpr (coll_distinct (k := builtinColls[0]) rfl)) hOm hmv hmw hne'
    KoreAML.val0 (elemOf c I (.map Srt.map [(asKItemMp s v, asKItemMp s v)]))
  rw [interpret_neg, interpret_conj] at hax
  exact hax ⟨(ht.1 _).mpr rfl, (hden _).mp ((ht.1 _).mpr rfl)⟩

end

/-! ## Distinct values are distinct elements -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {O : Srt → Prop}

/-- A value is a constructor or an injection applied to values, or its sort is one of
`distinctSorts`. -/
theorem shape_or_distinct_own [OvlOK c] {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    (∃ f ts, v = .ctor f ts) ∨ (∃ a b t, v = .inj a b t) ∨ s ∈ distinctSorts c := by
  cases v with
  | ctor f ws => exact .inl ⟨f, ws, rfl⟩
  | inj a b w => exact .inr (.inl ⟨a, b, w, rfl⟩)
  | dv s' lit =>
    refine .inr (.inr ?_)
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hv
    by_cases hcar : c.lib.carriers.all (·.1 != s) = false
    · exact carrier_distinct (by rw [hcar]; exact Bool.false_ne_true)
    have hcs := Lib.carrier_of_not _ (by rw [Bool.not_eq_false] at hcar; exact hcar)
    cases lit with
    | int _ => simp only [dvOK, hcs] at hok; rw [beq_iff_eq.mp hok]; exact int_distinct
    | bool _ => simp only [dvOK, hcs] at hok; rw [beq_iff_eq.mp hok]; exact bool_distinct
    | float _ _ _ =>
      simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1]; exact float_distinct
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.and_eq_true] at hok
      rcases hok with ((h | h) | h) | ⟨h | h, -⟩
      · rw [h]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))
      · rw [h]; exact string_distinct
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
      · rw [h]; exact bytes_distinct
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  | map s' es =>
    obtain ⟨k, -, hk, -, -, -, -, rfl⟩ := sortOf_mapS_fwd hv
    exact .inr (.inr (coll_distinct hk))
  | set s' es =>
    obtain ⟨k, hk, -, -, -, rfl⟩ := sortOf_setS.mp hv
    exact .inr (.inr (coll_distinct hk))
  | list s' es =>
    obtain ⟨k, hk, -, -, rfl⟩ := sortOf_listS.mp hv
    exact .inr (.inr (coll_distinct hk))

/-- Two lists of values of the same sorts with the same elements are equal, where each value of
the first is the only value of its sort with its element. -/
theorem elems_eq_own : ∀ {ts ws : List GroundTerm} {ss : List Srt}, c.sortsOf ts = some ss →
    c.sortsOf ws = some ss → (∀ s ∈ ss, O s) → ts.map (elemOf c I) = ws.map (elemOf c I) →
    (∀ t ∈ ts, ∀ {w : GroundTerm} {s : Srt}, c.sortOf t = some s → c.sortOf w = some s → O s →
      elemOf c I t = elemOf c I w → t = w) → ts = ws
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | t :: ts, w :: ws, ss, h1, h2, hO, he, ih => by
    obtain ⟨s, ss', ht, hts, rfl⟩ := sortsOf_cons.mp h1
    obtain ⟨s2, ss2, hw, hws, hc⟩ := sortsOf_cons.mp h2
    cases hc
    simp only [List.map_cons, List.cons.injEq] at he
    rw [ih t (List.mem_cons_self ..) ht hw (hO _ (List.mem_cons_self ..)) he.1,
      elems_eq_own hts hws (fun s hs => hO s (List.mem_cons_of_mem _ hs)) he.2
        (fun t ht => ih t (List.mem_cons_of_mem _ ht))]

variable (hI : OwnVals c I O) [OvlOK c] (hg : genWf c = true)
include hI hg

omit hg [OvlOK c] in
/-- Distinct values of a sort of `O` among `distinctSorts` are distinct elements. -/
theorem apart_distinct_own {v w : GroundTerm} {s : Srt} (hd : s ∈ distinctSorts c) (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) (hO : O s) (he : elemOf c I v = elemOf c I w) : v = w := by
  refine Classical.byContradiction fun hne => ?_
  have := hI.apart (List.contains_iff_mem.mpr hd) hO hv hw (fun h => hne (GroundTerm.cmp_eq _ _ h)) KoreAML.val0
    (elemOf c I v)
  rw [interpret_neg, interpret_conj] at this
  exact this ⟨((elemOf_spec_own hI hv hO KoreAML.val0).1 _).mpr rfl, ((elemOf_spec_own hI hw hO KoreAML.val0).1 _).mpr he⟩

/-- **Distinct values of a sort of `O` are distinct elements**, with Map among `O`. At a sort of
`distinctSorts` by the distinctness of its values; at KItem and the sorts below it by Map's
(`map_apart_own`); at K, which is no open generator's sort, by its generators: a constructor's image holds the element of no other value (`ctor_back_own`),
an injection's image that of no value but the injection of a value (`inj_back_own`), and an
overloading symbol builds one element from one list of arguments and none that another
overloading symbol builds at arguments no overload covers. -/
theorem own_apart_at (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hOm : O Srt.map) :
    ∀ (v : GroundTerm) {w : GroundTerm} {s : Srt}, c.sortOf v = some s → c.sortOf w = some s → O s →
      elemOf c I v = elemOf c I w → v = w
  | .ctor f ts, w, s, hv, hw, hO, he => by
    by_cases hsK : s ≠ Srt.k
    · -- KItem and the sorts below it by Map, the others by their distinctness
      have hap := apartSort_of_sorted hg hv
      unfold apartSort at hap
      simp only [Bool.or_eq_true, beq_iff_eq] at hap
      rcases hap with ((hK | hKI) | hB) | hD'
      · exact absurd hK hsK
      · exact map_apart_own hI hg htr hOm (.inl hKI) hO hv hw he
      · exact map_apart_own hI hg htr hOm (.inr (List.contains_iff_mem.mp hB)) hO hv hw he
      · exact apart_distinct_own hI (List.contains_iff_mem.mp hD') hv hw hO he
    replace hsK : s = Srt.k := Classical.byContradiction hsK
    have hno : ∀ p ∈ c.params, p.raw = true → p.sig.result ≠ s := fun p hp hr h =>
      open_result_ne_k hg hp hr (h.trans hsK)
    have hsv := (elemOf_spec_own hI hv hO KoreAML.val0).1
    have hsw := (elemOf_spec_own hI hw hO KoreAML.val0).1
    have hN : s ∈ consSorts c := ctor_sort_cons hg hv
    rcases sortOf_ctor_cases hg hv with ⟨k, hk, hts, hres⟩ | ⟨o, hlo, hio, hts, hu, hres, -⟩ |
      ⟨kp, hko, -, -, -, -, hres, -⟩
    rotate_right
    · obtain ⟨hpm, hpr, -, -⟩ := c.lookupOpen_spec hko
      exact absurd hres.symm (hno _ hpm hpr)
    · -- a constructor's application
      subst hres
      obtain ⟨hkm, -⟩ := lookupSig_spec hk
      have hOk : ∀ s ∈ k.args, O s := hI.sig _ (List.mem_append_left _ hkm)
      have hm : GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ts.map (elemOf c I)) (elemOf c I w) := by
        rw [← he]; exact (den_ctor_gs_own hI hk hts hOk KoreAML.val0 _).mp ((hsv _).mpr rfl)
      obtain ⟨ws, rfl, hws, hel⟩ := ctor_back_own hI hg htr hk hno hw hO (elems_length_own hI hts)
        (elems_sorts_own (ss := k.args) hI hts hOk) hm
      rw [elems_eq_own hts hws hOk hel fun t ht => by
        have _hlt := List.sizeOf_lt_of_mem ht
        exact @fun _ _ h1 h2 h3 h4 => own_apart_at htr hOm t h1 h2 h3 h4]
    · -- a raw application of an overloading symbol
      obtain ⟨hom, hn, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
      have hOo : ∀ s ∈ o.sig.args, O s := hI.sig _ (List.mem_append_right _ (List.mem_map_of_mem hom))
      have hgo : Gen.ctor o.sig ∈ (c.gens s).filter (!c.isOpenGen ·) := by rw [hres]; exact gensF_of_ovl hg hom
      have hvset : ∀ m, GS I (c.sortName s) (Gen.toK c (.ctor o.sig)) (ts.map (elemOf c I)) m ↔
          m = elemOf c I (.ctor f ts) := fun m => by
        rw [hres, ← den_sig_gs_own hI hn hts hOo KoreAML.val0 m]; exact hsv m
      have hunc := uncE_of_value_own hI hg htr hlo hts hu fun u _ A B hAB hsu y hy hmy => by
        obtain ⟨w', hw', rfl, -⟩ := inj_back_own hI hg htr u hAB hsu hy hmy
        exact lies_injNormal hw'
      rcases consSort_shape hg hN hw with ⟨g, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
      · rcases sortOf_ctor_cases hg hw with ⟨kg, hkg, hws, hres'⟩ | ⟨o', hlo', -, hws, hu', hres', -⟩ |
          ⟨kp, hko, -, -, -, -, hres', -⟩
        rotate_right
        · obtain ⟨hpm, hpr, -, -⟩ := c.lookupOpen_spec hko
          exact absurd hres'.symm (hno _ hpm hpr)
        · -- the other is a constructor's application: so would this one be
          exfalso
          obtain ⟨hkgm, -⟩ := lookupSig_spec hkg
          have hOk : ∀ s ∈ kg.args, O s := hI.sig _ (List.mem_append_left _ hkgm)
          subst hres'
          have hm : GS I (c.sortName kg.result) (Gen.toK c (.ctor kg)) (ws.map (elemOf c I))
              (elemOf c I (.ctor f ts)) := by
            rw [he]; exact (den_ctor_gs_own hI hkg hws hOk KoreAML.val0 _).mp ((hsw _).mpr rfl)
          obtain ⟨ts', h', -, -⟩ := ctor_back_own hI hg htr hkg hno hv hO (elems_length_own hI hws)
            (elems_sorts_own (ss := kg.args) hI hws hOk) hm
          injection h' with hfg _
          subst hfg
          have := (c.isOvl_parts hio).1
          simp [Semantics.isCtor, hkg] at this
        · obtain ⟨hom', hn', -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo'
          have hOo' : ∀ s ∈ o'.sig.args, O s := hI.sig _ (List.mem_append_right _ (List.mem_map_of_mem hom'))
          have hwset : ∀ m, GS I (c.sortName s) (Gen.toK c (.ctor o'.sig)) (ws.map (elemOf c I)) m ↔
              m = elemOf c I (.ctor g ws) := fun m => by
            rw [hres', ← den_sig_gs_own hI hn' hws hOo' KoreAML.val0 m]; exact hsw m
          by_cases hfg : g = f
          · -- the same symbol: its arguments have the same elements
            subst hfg
            rw [hlo] at hlo'; cases hlo'
            by_cases hne : o.sig.args = []
            · rw [hne] at hts hws; rw [sortsOf_nil_eq hts, sortsOf_nil_eq hws]
            · have hunc' := uncE_of_value_own hI hg htr hlo hws hu' fun u _ A B hAB hsu y hy hmy => by
                obtain ⟨w', hw', rfl, -⟩ := inj_back_own hI hg htr u hAB hsu hy hmy
                exact lies_injNormal hw'
              have hel := gen_injU_own hI hN hgo hne (elems_length_own hI hts) (elems_length_own hI hws)
                (elems_sorts_own (ss := o.sig.args) hI hts hOo) (elems_sorts_own (ss := o.sig.args) hI hws hOo)
                (uncE_getD hunc) (uncE_getD hunc') (fun m => by rw [hvset, hwset, he])
              rw [elems_eq_own hts hws hOo hel fun t ht => by
                have _hlt := List.sizeOf_lt_of_mem ht
                exact @fun _ _ h1 h2 h3 h4 => own_apart_at htr hOm t h1 h2 h3 h4]
          · -- two overloading symbols, each at arguments no overload covers
            exfalso
            have hgo' : Gen.ctor o'.sig ∈ (c.gens s).filter (!c.isOpenGen ·) := by
              rw [hres']; exact gensF_of_ovl hg hom'
            have hunc' := uncE_of_value_own hI hg htr hlo' hws hu' fun u _ A B hAB hsu y hy hmy => by
              obtain ⟨w', hw', rfl, -⟩ := inj_back_own hI hg htr u hAB hsu hy hmy
              exact lies_injNormal hw'
            exact gen_dist_own' hI hN hgo hgo'
              (fun h => by injection h with h; exact hfg (by rw [← hn', ← h, hn]))
              (fun _ _ h _ => by cases h) (elems_length_own hI hts) (elems_length_own hI hws)
              (elems_sorts_own (ss := o.sig.args) hI hts hOo) (elems_sorts_own (ss := o'.sig.args) hI hws hOo')
              hunc hunc' (fun m => by rw [hvset, hwset, he])
      · -- the other is an injection: so would this one be
        exfalso
        obtain ⟨hab, -, hw0, hb⟩ := sortOf_inj.mp hw
        subst hb
        have hm : GS I (c.sortName s) (.inj (c.sortName a)) [elemOf c I w0] (elemOf c I (.ctor f ts)) := by
          rw [he]; exact (den_inj_gs_own hI hw0 (hI.sub hab).1 KoreAML.val0 _).mp ((hsw _).mpr rfl)
        obtain ⟨w', -, h', -⟩ := inj_back_own hI hg htr (.ctor f ts) hab hv
          ((inS_iff _).mp (elemOf_spec_own hI hw0 (hI.sub hab).1 KoreAML.val0).2) hm
        have := injNormal_isInj a s w'
        rw [← h'] at this
        exact absurd this (by simp [GroundTerm.isInj])
  | .inj a b t, w, s, hv, hw, hO, he => by
    have hsv := (elemOf_spec_own hI hv hO KoreAML.val0).1
    have hsw := (elemOf_spec_own hI hw hO KoreAML.val0).1
    obtain ⟨hab, hni, ht, hb⟩ := sortOf_inj.mp hv
    subst hb
    have hOa := (hI.sub hab).1
    have hm : GS I (c.sortName s) (.inj (c.sortName a)) [elemOf c I t] (elemOf c I w) := by
      rw [← he]; exact (den_inj_gs_own hI ht hOa KoreAML.val0 _).mp ((hsv _).mpr rfl)
    obtain ⟨w', hw', rfl, hel⟩ := inj_back_own hI hg htr w hab hw
      ((inS_iff _).mp (elemOf_spec_own hI ht hOa KoreAML.val0).2) hm
    have : t = w' := own_apart_at htr hOm t ht hw' hOa hel
    subst this
    rw [injNormal_of_not hni]
  | .dv _ _, w, s, hv, hw, hO, he => by
    rcases shape_or_distinct_own hv with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | h
    · cases h
    · cases h
    · exact apart_distinct_own hI h hv hw hO he
  | .map _ _, w, s, hv, hw, hO, he => by
    rcases shape_or_distinct_own hv with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | h
    · cases h
    · cases h
    · exact apart_distinct_own hI h hv hw hO he
  | .set _ _, w, s, hv, hw, hO, he => by
    rcases shape_or_distinct_own hv with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | h
    · cases h
    · cases h
    · exact apart_distinct_own hI h hv hw hO he
  | .list _ _, w, s, hv, hw, hO, he => by
    rcases shape_or_distinct_own hv with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | h
    · cases h
    · cases h
    · exact apart_distinct_own hI h hv hw hO he
  termination_by v => v
  decreasing_by all_goals (simp_wf; omega)

end

/-! ## Distinct values by the graph of `_==K_` -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {O : Srt → Prop}
  (hI : OwnVals c I O) [OvlOK c]
include hI

/-- Two values of one sort with one element have `wrapK` forms that hold of the same elements. -/
theorem den_wrapK_congr_own {s : Srt} (hs : BelowK c s) (hO : O s) {v w : GroundTerm}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (he : elemOf c I v = elemOf c I w) (e : Valuation M) (m : M) :
    (den c (wrapK s v)).interpret I e m ↔ (den c (wrapK s w)).interpret I e m := by
  have hvw : ∀ m, (den c v).interpret I e m ↔ (den c w).interpret I e m := fun m => by
    rw [(elemOf_spec_own hI hv hO e).1, (elemOf_spec_own hI hw hO e).1, he]
  unfold wrapK
  split
  · exact hvw m
  · rename_i hk
    rw [den_ctor, den_ctor]
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    refine KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => ?_)) (fun _ => Iff.rfl) m
    show (den c _).interpret I e m ↔ (den c _).interpret I e m
    split
    · exact hvw m
    · rename_i hki
      have hb : s ∈ c.sortsBelowKItem := by
        rcases hs with h | h | h
        · exact absurd h hk
        · exact absurd h hki
        · exact h
      rw [den_injNormal_gs_own hI (kitem_sub hb) hv, den_injNormal_gs_own hI (kitem_sub hb) hw, he]

/-- **Distinct values of a sort of `O` are distinct elements**, in a model that holds the graph of
`_==K_` at values of K (`hkeq`), with K and Bool among `O`: at K, KItem and a sort below KItem,
two values with one element have `wrapK` forms with one element, at which `_==K_` would be both
`true` and `false`; at a sort of `distinctSorts`, by the distinctness of its values. It asks
nothing of the parameters: a raw application of an open generator is a value like another. -/
theorem values_apart_own (hg : genWf c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hOb : O Srt.bool)
    (hkeq : ∀ {u u' : GroundTerm}, c.sortOf u = some Srt.k → c.sortOf u' = some Srt.k → ∀ m,
      (KoreAML.den (symApp c kEq (GroundTerm.koreList c [u, u']))).interpret I KoreAML.val0 m ↔
        (den c (bool (GroundTerm.cmp u u' == .eq))).interpret I KoreAML.val0 m)
    {s : Srt} (hO : O s) {v w : GroundTerm} (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (he : elemOf c I v = elemOf c I w) : v = w := by
  refine Classical.byContradiction fun hne => ?_
  have key : BelowK c s → False := by
    intro hs
    have hwv := sortOf_wrapK htr hs hv
    have hww := sortOf_wrapK htr hs hw
    have hne' : GroundTerm.cmp (wrapK s v) (wrapK s w) ≠ .eq := fun h =>
      hne (wrapK_inj hg hv hw (GroundTerm.cmp_eq _ _ h))
    have hset := den_wrapK_congr_own hI hs hO hv hw he KoreAML.val0
    have h3 : (GroundTerm.cmp (wrapK s v) (wrapK s w) == .eq) = false := by
      cases h : GroundTerm.cmp (wrapK s v) (wrapK s w) with
      | eq => exact absurd h hne'
      | lt => rfl
      | gt => rfl
    have hb : ∀ m, (den c (bool false)).interpret I KoreAML.val0 m ↔
        (den c (bool true)).interpret I KoreAML.val0 m := by
      intro m
      have h1 := hkeq hwv hww m
      have h2 := hkeq hwv hwv m
      rw [GroundTerm.cmp_refl] at h2
      have h2 : _ ↔ (den c (bool true)).interpret I KoreAML.val0 m := h2
      rw [h3] at h1
      rw [← h1, ← h2]
      exact eqK_congr hset m
    have ht := elemOf_spec_own hI (sortOf_bool (c := c) true) hOb KoreAML.val0
    have hax := hI.apart (List.contains_iff_mem.mpr bool_distinct) hOb (sortOf_bool (c := c) false)
      (sortOf_bool true) (fun h => by have := GroundTerm.cmp_eq _ _ h; cases this) KoreAML.val0
      (elemOf c I (bool true))
    rw [interpret_neg, interpret_conj] at hax
    exact hax ⟨(hb _).mpr ((ht.1 _).mpr rfl), (ht.1 _).mpr rfl⟩
  have hap := apartSort_of_sorted hg hv
  unfold apartSort at hap
  simp only [Bool.or_eq_true, beq_iff_eq] at hap
  rcases hap with ((hK | hKI) | hB) | hD'
  · exact key (Or.inl hK)
  · exact key (Or.inr (Or.inl hKI))
  · exact key (Or.inr (Or.inr (List.contains_iff_mem.mp hB)))
  · exact hne (apart_distinct_own hI (List.contains_iff_mem.mp hD') hv hw hO he)

end

/-! ## At the decided form of `Detached` -/

section
open DetachedB
variable {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
  {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
include hd hI

/-- **A value of a sort without a detached name denotes one element of its sort**, in a model of
the theory without the detached names. -/
theorem own_single {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) (hs : sOK c ss ks s = true)
    (e : Valuation M) :
    ∃ a, (∀ m, (den c v).interpret I e m ↔ m = a) ∧ (KoreAML.inhOf (sortP (c.sortName s))).interpret I e a :=
  den_single_own (ownVals_of_decided hd hI) hv hs e

omit hI in
/-- Where `_==K_` is none of the names, neither are K, Bool and its application's head. -/
theorem kEq_ok_own (hk : kOK c ss ks kEq = true) :
    appOK c ss ks kEq = true ∧ sOK c ss ks Srt.k = true ∧ sOK c ss ks Srt.bool = true := by
  simp only [detachedB, Bool.and_eq_true] at hd
  have hG := hd.2
  simp only [graphsB, Bool.and_eq_true, List.all_eq_true] at hG
  have hmem : (⟨kEq, [Srt.k, Srt.k], Srt.bool⟩ : CtorSig) ∈ hookSigs := by decide
  have := hG.1.1 _ hmem
  simp only [hk, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_cons, List.all_nil] at this
  exact ⟨this.1, this.2.2.1, this.2.1⟩

/-- **The graph of `_==K_` at two values of K**, in a model of the theory without the detached
names, where `_==K_` is none of them. -/
theorem eqK_den_own (hk : kOK c ss ks kEq = true) {u u' : GroundTerm} (hu : c.sortOf u = some Srt.k)
    (hu' : c.sortOf u' = some Srt.k) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c kEq (GroundTerm.koreList c [u, u']))).interpret I e m ↔
      (den c (bool (GroundTerm.cmp u u' == .eq))).interpret I e m := by
  obtain ⟨hf, hsk, hsb⟩ := kEq_ok_own hd hk
  have hV : valuesB c ss ks = true := by
    simp only [detachedB, Bool.and_eq_true] at hd
    exact hd.1.2
  have hmem : (⟨kEq, [Srt.k, Srt.k], Srt.bool⟩ : CtorSig) ∈ hookSigs := by decide
  have hvs : c.sortsOf [u, u'] = some [Srt.k, Srt.k] :=
    sortsOf_cons.mpr ⟨_, _, hu, sortsOf_cons.mpr ⟨_, _, hu', sortsOf_nil, rfl⟩, rfl⟩
  have hax := hI _ ⟨Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl
      ⟨_, [u, u'], some (bool (GroundTerm.cmp u u' == .eq)), hmem, hvs, rfl, (by intro h; cases h), rfl⟩))))))),
    fun σ hσ hn => clean_spec (clean_graph hV hf hvs (fun s hs => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hs; rw [hs]; exact hsk)
      (clean_val hV _ Srt.bool (sortOf_bool _) hsb)) ⟨σ, hσ, hn⟩⟩
  exact (KoreAML.interp_equal (ownVals_of_decided hd hI).defOK).mp (hax e default) m

omit hI in
/-- Map is none of the names: the library's map collection has axioms, so the decided check
keeps its sort. -/
theorem map_sOK_of_decided : sOK c ss ks Srt.map = true := by
  simp only [detachedB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hd
  rcases hd.1.1.1.2 builtinColls[0] (List.mem_cons_self ..) with h | h
  · exact h
  · exact absurd h (by simp [builtinColls, collAxioms, mapCollAxioms])

/-- **Distinct values of a sort without a detached name denote distinct elements**, in a model of
the theory without the detached names: two values of the sort whose patterns hold of the same
elements are equal. At KItem and the sorts below it by Map's distinctness (Map is never detached),
at the sorts of `distinctSorts` by theirs, and at K by its generators. -/
theorem own_apart (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {v w : GroundTerm} {s : Srt}
    (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) (hs : sOK c ss ks s = true) (e : Valuation M)
    (h : ∀ m, (den c v).interpret I e m ↔ (den c w).interpret I e m) : v = w := by
  have H := ownVals_of_decided hd hI
  have he : elemOf c I v = elemOf c I w :=
    ((elemOf_spec_own H hw hs e).1 _).mp ((h _).mp (((elemOf_spec_own H hv hs e).1 _).mpr rfl))
  exact own_apart_at H hg htr (map_sOK_of_decided hd) v hv hw hs he

omit hd hI in
theorem sOK_of_not_DSort {s : Srt} (hs : ¬ DSort c (DetachedB.names c ss ks) s) : sOK c ss ks s = true := by
  cases h : isName c ss ks (.sort ("Sort" ++ c.sortName s))
  · simp [sOK, h]
  · exact absurd (isName_iff.mp h) hs

/-- Every value has an element in the extension (`ElemOf`). -/
theorem elemOf_total {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    ∃ x, ElemOf c (DetachedB.names c ss ks) I v x := by
  by_cases hs : DSort c (DetachedB.names c ss ks) s
  · exact ⟨.inr (.val v), .inl ⟨s, hv, hs, rfl⟩⟩
  · obtain ⟨a, ha, -⟩ := own_single hd hI hv (sOK_of_not_DSort hs) KoreAML.val0
    exact ⟨.inl a, .inr ⟨s, a, hv, hs, rfl, ha⟩⟩

/-- Two values of one sort with the same element in the extension (`ElemOf`) are equal. -/
theorem elemOf_inj (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {v w : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) {x : Ext M} (h1 : ElemOf c (DetachedB.names c ss ks) I v x)
    (h2 : ElemOf c (DetachedB.names c ss ks) I w x) : v = w := by
  rcases h1 with ⟨s1, hv1, hs1, rfl⟩ | ⟨s1, m1, hv1, hs1, rfl, hm1⟩
  · rcases h2 with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h, _⟩
    · cases h; rfl
    · cases h
  · rcases h2 with ⟨_, _, _, h⟩ | ⟨s2, m2, _, _, h, hm2⟩
    · cases h
    · cases h
      rw [hv] at hv1; cases hv1
      exact own_apart hd hI hg htr hv hw (sOK_of_not_DSort hs1) KoreAML.val0
        (fun m => by rw [hm1, hm2])

end

end KCore.Cons
