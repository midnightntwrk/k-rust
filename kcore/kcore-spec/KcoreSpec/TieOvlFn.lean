/-
  KCore, outside the cone: the constructor sentences a text states of a function-overloaded symbol
  `f` (a generator with `Semantics.fnOvl`: an overloading symbol one of whose overloads is a
  function), against Γ's items at uncovered arguments, for any text and any interpretation.

  Γ holds, for such a generator, `KoreAML.Cons.funUncItem`, `injUncItem` and `distUncItem`: the
  functionality, injectivity and distinctness of `f` at the arguments no overload covers. The text
  states them at every argument. This module shows that the text's sentences give Γ's items, in
  every interpretation `I` that meets the hypotheses named below (no model of Γ is assumed):

  - The `functional` sentence `\exists{R}(Val:N, \equals{N, R}(Val:N, f(K̄)))` says, at elements x̄
    of f's argument sorts, that exactly one element of N is in `f(x̄)` (`tieOvlFnFun_at`): the
    sorted equality compares the two sides within N only. With f's arity (`TieOvlFnArity`:
    `f(x̄)` holds elements of N only) that is Cons-Fun, `funItem` (`tieOvlFnFun_funItem`), which
    entails `funUncItem` (`funUncItem_of_funItem`).
  - The same-constructor sentence `f(X̄) ∧ f(Ȳ) → f(X̄ ∧ Ȳ)` with Cons-Fun of f gives Cons-Inj,
    `injItem` (`tieOvlFnInj_at`): where `f(x̄)` and `f(ȳ)` are one element y, of N, the sentence
    puts y in `f(x̄ ∧ ȳ)`, an application that holds an element only where each `xᵢ ∧ yᵢ` does, so
    x̄ = ȳ. `injItem` entails `injUncItem`. Alone the sentence does not give the item: where
    `f(x̄)` and `f(ȳ)` are both empty they are equal and the sentence holds, whatever x̄ and ȳ.
  - A different-constructors sentence `¬(f(X̄) ∧ k(Ȳ))` with Cons-Fun of one of the two gives
    Cons-Dist, `distItem`, in both orders (`tieOvlFnDist_at`): the one element of N the first
    application holds is not in the second. `distItem` entails `distUncItem`
    (`tieOvlFn_distUncItem_of_distItem`). Alone it does not: two empty applications are equal.

  What is asked of the interpretation beside the sentences (`TieOvlFnBase`, `TieOvlFnArity`):
  definedness, the definition of ceiling, the sort constant of N denoting one sort, some sort with
  an inhabitant (the sentence is closed over a sort variable R and says nothing where every sort is
  empty), and the arity of the generator. None is one of Γ's constructor items; a model of Γ meets
  all of them. The first three are items of Γ's signature (`tieOvlFnBase_of_Γ_dotk`). Γ states no
  sort's nonemptiness, but the sort K has the value `.K` (a constructor of K with no arguments in
  every semantics), whose element Γ's domains put in K (`tieOvlFnInh_of_Γ`). The arity is the
  generator's G-arity item, which Γ holds for every symbol of `kernelSyms`, the overloading
  symbols among them (`tieOvlFnArity_of_Γ`, decided by `tieOvlFnArityB`). Outside the models of Γ
  neither is implied by the sentences: where every sort is empty the `functional` sentence holds
  and Cons-Fun fails at a nullary generator, and an application holding one element of N and one
  outside it satisfies the `functional` sentence, whose equality compares within N only.

  Conversely Cons-Fun, Cons-Inj and Cons-Dist give the sentences (`tieOvlFnFun_sent_of`,
  `tieOvlFnInj_sent_of`, `tieOvlFnDist_sent_of`), so the hypotheses of the weaker lemmas are met
  together wherever the generators are free constructors.

  `tieOvlFnFunB`, `tieOvlFnInjB`, `tieOvlFnDistB` decide on a text that an axiom is such a
  sentence of a function-overloaded generator, in the form the lemmas read, and that the matching
  item at uncovered arguments is among `consItemsK`; they do not depend on the hooks' parameters.
-/
import KcoreSpec.TieOvlEq

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace Faithful

/-! ## Patterns: guards, applications -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A guarded pattern holds where the pattern holds whenever its guards do. -/
theorem tieOvlFn_guarded_intro {e : Valuation M} {m : M} {ws : List KoreAML.P} {φ : KoreAML.P}
    (h : (∀ w ∈ ws, w.interpret I e m) → φ.interpret I e m) : (KoreAML.guarded ws φ).interpret I e m := by
  cases ws with
  | nil => exact h (fun _ hw => nomatch hw)
  | cons u us => intro hc; exact h (conjList_mem hc)

/-- An application that holds an element has a head that holds one. -/
theorem tieOvlFn_appList_head {e : Valuation M} : ∀ (φs : List KoreAML.P) (h : KoreAML.P) (m : M),
    (KoreAML.appList h φs).interpret I e m → ∃ a, h.interpret I e a
  | [], _, m, hm => ⟨m, hm⟩
  | ψ :: φs, h, m, hm => by
    have hm' : (KoreAML.appList (h ⬝ ψ) φs).interpret I e m := hm
    obtain ⟨a, ha⟩ := tieOvlFn_appList_head φs (h ⬝ ψ) m hm'
    rw [KoreAML.interp_app] at ha
    obtain ⟨a', _, ha', _, _⟩ := ha
    exact ⟨a', ha'⟩

/-- An application that holds an element has arguments each of which holds one. -/
theorem tieOvlFn_appList_args {e : Valuation M} : ∀ (φs : List KoreAML.P) (h : KoreAML.P) (m : M),
    (KoreAML.appList h φs).interpret I e m → ∀ φ ∈ φs, ∃ b, φ.interpret I e b
  | [], _, _, _, _, hφ => absurd hφ List.not_mem_nil
  | ψ :: φs, h, m, hm, φ, hφ => by
    have hm' : (KoreAML.appList (h ⬝ ψ) φs).interpret I e m := hm
    rcases List.mem_cons.mp hφ with hφ | hφ
    · obtain ⟨a, ha⟩ := tieOvlFn_appList_head φs (h ⬝ ψ) m hm'
      rw [KoreAML.interp_app] at ha
      obtain ⟨_, b, _, hb, _⟩ := ha
      exact ⟨b, hφ ▸ hb⟩
    · exact tieOvlFn_appList_args φs (h ⬝ ψ) m hm' φ hφ

/-- Variables whose conjunctions `x ∧ y` each hold an element hold the same elements. -/
theorem tieOvlFn_zipAnd_eq {e : Valuation M} : ∀ (ix iy : List EVar), ix.length = iy.length →
    (∀ φ ∈ (ix.zip iy).map (fun p => KoreAML.sAnd (.evar p.1) (.evar p.2)), ∃ b, φ.interpret I e b) →
    ix.map e.evalEvar = iy.map e.evalEvar
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: ix, y :: iy, hl, h => by
    obtain ⟨b, hb⟩ := h (KoreAML.sAnd (.evar x) (.evar y)) (by
      simp only [List.zip_cons_cons, List.map_cons]
      exact List.mem_cons_self ..)
    rw [KoreAML.interp_sAnd, KoreAML.interp_evar, KoreAML.interp_evar] at hb
    have ih := tieOvlFn_zipAnd_eq ix iy (by simpa using hl) (fun φ hφ => h φ (by
      simp only [List.zip_cons_cons, List.map_cons]
      exact List.mem_cons_of_mem _ hφ))
    rw [List.map_cons, List.map_cons, ih, ← hb.1, ← hb.2]

end

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-! ## Γ's constructor items from what they say at elements -/

/-- Variables whose membership guards hold take elements of their sorts. -/
theorem tieOvlFn_memGuards_inS (hD : KoreAML.DefOK I) {e : Valuation M} {m : M} :
    ∀ (vs : List EVar) (ss : List String), (∀ w ∈ KoreAML.Cons.memGuards vs ss, w.interpret I e m) →
      ∀ (i : Nat) v s, vs[i]? = some v → ss[i]? = some s → InS I s (e.evalEvar v)
  | [], _, _, _, _, _, hv, _ => by simp at hv
  | _ :: _, [], _, _, _, _, _, hs => by simp at hs
  | v0 :: vs, s0 :: ss, h, i, v, s, hv, hs => by
    have h0 : ∀ w ∈ (v0 ∈∈ KoreAML.inhOf (KoreAML.Cons.sortP s0) : KoreAML.P) :: KoreAML.Cons.memGuards vs ss,
        w.interpret I e m := fun w hw => h w hw
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hs
      subst hv; subst hs
      have h1 := h0 _ (List.mem_cons_self ..)
      rw [KoreAML.interp_member hD, inS_iff] at h1
      exact h1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hv hs
      exact tieOvlFn_memGuards_inS hD vs ss (fun w hw => h0 w (List.mem_cons_of_mem _ hw)) i v s hv hs

omit [Inhabited M] in
theorem tieOvlFn_map_get {e : Valuation M} {vs : List EVar} {P : Nat → M → Prop}
    (h : ∀ (i : Nat) v, vs[i]? = some v → P i (e.evalEvar v)) :
    ∀ (i : Nat) x, (vs.map e.evalEvar)[i]? = some x → P i x := by
  intro i x hx
  rw [List.getElem?_map] at hx
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
  exact h i v hv

/-- The elements variables take, where their membership guards hold, are of their sorts. -/
theorem tieOvlFn_guards_inS (hD : KoreAML.DefOK I) {e : Valuation M} {m : M} {vs : List EVar} {ss : List String}
    (h : ∀ w ∈ KoreAML.Cons.memGuards vs ss, w.interpret I e m) :
    ∀ (i : Nat) x s, (vs.map e.evalEvar)[i]? = some x → ss[i]? = some s → InS I s x := fun i x s hx hs =>
  tieOvlFn_map_get (P := fun i x => ∀ s, ss[i]? = some s → InS I s x)
    (fun i v hv s hs => tieOvlFn_memGuards_inS hD vs ss h i v s hv hs) i x hx s hs

/-- **Cons-Fun from its statement at elements**: the converse of `fun_at`. -/
theorem tieOvlFn_funItem_intro (hD : KoreAML.DefOK I) {N : String} {g : KoreAML.Gen}
    (h : ∀ xs : List M, xs.length = g.argSorts.length →
      (∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x) →
      ∃ y, InS I N y ∧ ∀ m, GS I N g xs m ↔ m = y) :
    I ⊧ᴵ (KoreAML.Cons.funItem N g).pat := by
  intro e m
  unfold KoreAML.Cons.funItem
  dsimp only
  refine tieOvlFn_guarded_intro fun hw => ?_
  obtain ⟨y, hy1, hy2⟩ := h ((KoreAML.Cons.xs 0 g.argSorts.length).map e.evalEvar)
    (by rw [List.length_map, xs_length]) (tieOvlFn_guards_inS hD hw)
  rw [KoreAML.interp_sExists]
  refine ⟨y, ?_, ?_⟩
  · rw [KoreAML.interp_member hD]
    simp only [Function.update_same]
    rw [inS_iff]
    exact hy1
  · rw [KoreAML.interp_equal hD]
    intro b
    rw [interp_genPat_vars, KoreAML.interp_evar]
    simp only [Function.update_same]
    rw [map_update_xs 0 _ _ _ _ (fun i hi he => by simp only [EVar.mk.injEq] at he; omega)]
    exact hy2 b

/-- **Cons-Inj from its statement at elements**: the converse of `inj_at`. -/
theorem tieOvlFn_injItem_intro (hD : KoreAML.DefOK I) {N : String} {g : KoreAML.Gen}
    (h : ∀ xs ys : List M, xs.length = g.argSorts.length → ys.length = g.argSorts.length →
      (∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x) →
      (∀ (i : Nat) x s, ys[i]? = some x → g.argSorts[i]? = some s → InS I s x) →
      (∀ m, GS I N g xs m ↔ GS I N g ys m) → xs = ys) :
    I ⊧ᴵ (KoreAML.Cons.injItem N g).pat := by
  intro e m
  unfold KoreAML.Cons.injItem
  dsimp only
  refine tieOvlFn_guarded_intro fun hw => ?_
  rw [interpret_impl]
  intro heq
  rw [KoreAML.interp_equal hD] at heq
  have hxy := h _ _ (by rw [List.length_map, xs_length]) (by rw [List.length_map, xs_length])
    (tieOvlFn_guards_inS hD fun w hw' => hw w (List.mem_append_left _ hw'))
    (tieOvlFn_guards_inS hD fun w hw' => hw w (List.mem_append_right _ hw'))
    (fun b => (interp_genPat_vars N g e _ b).symm.trans ((heq b).trans (interp_genPat_vars N g e _ b)))
  refine KoreAML.interp_conjList fun w hw' => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hw'
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hab
  rw [List.getElem?_zip_eq_some] at hi
  have h1 := congrArg (·[i]?) hxy
  simp only [List.getElem?_map, hi.1, hi.2, Option.map_some, Option.some.injEq] at h1
  show (Pattern.evar a ≡ Pattern.evar b : KoreAML.P).interpret I e m
  rw [KoreAML.interp_equal hD]
  intro b'
  rw [KoreAML.interp_evar, KoreAML.interp_evar, h1]

/-- **Cons-Dist from its statement at elements**: the converse of `dist_at`. -/
theorem tieOvlFn_distItem_intro (hD : KoreAML.DefOK I) {N : String} {g g' : KoreAML.Gen}
    (h : ∀ xs ys : List M, xs.length = g.argSorts.length → ys.length = g'.argSorts.length →
      (∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x) →
      (∀ (i : Nat) x s, ys[i]? = some x → g'.argSorts[i]? = some s → InS I s x) →
      ¬ ∀ m, GS I N g xs m ↔ GS I N g' ys m) :
    I ⊧ᴵ (KoreAML.Cons.distItem N g g').pat := by
  intro e m
  unfold KoreAML.Cons.distItem
  dsimp only
  refine tieOvlFn_guarded_intro fun hw => ?_
  rw [KoreAML.interp_notEqual hD]
  intro heq
  exact h _ _ (by rw [List.length_map, xs_length]) (by rw [List.length_map, xs_length])
    (tieOvlFn_guards_inS hD fun w hw' => hw w (List.mem_append_left _ hw'))
    (tieOvlFn_guards_inS hD fun w hw' => hw w (List.mem_append_right _ hw'))
    (fun b => (interp_genPat_vars N g e _ b).symm.trans ((heq b).trans (interp_genPat_vars N g' e _ b)))

omit [Inhabited M] in
/-- **Cons-Dist entails Cons-Dist at uncovered arguments**: the second is the first with the
guards `uncoveredP` of the overloading generators added. -/
theorem tieOvlFn_distUncItem_of_distItem {N : String} {g g' : KoreAML.Gen} (ug ug' : Option (List (List String)))
    (h : I ⊧ᴵ (KoreAML.Cons.distItem N g g').pat) : I ⊧ᴵ (KoreAML.Cons.distUncItem N g g' ug ug').pat := by
  unfold KoreAML.Cons.distUncItem
  unfold KoreAML.Cons.distItem at h
  exact guarded_append_unc (guarded_append_unc h)

/-! ## The sentences at elements -/

/-- Elements of the sorts `ss`, as `tieGuards_vals` reads them. -/
theorem tieOvlFn_all2 {e : Valuation M} : ∀ (ss : List String) (vals : List M), vals.length = ss.length →
    (∀ (i : Nat) x s, vals[i]? = some x → ss[i]? = some s → InS I s x) →
    All2 (fun s v => (KoreAML.inhOf (KoreAML.Cons.sortP s)).interpret I e v) ss vals
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | s :: ss, v :: vals, hl, h =>
    .cons ((inS_iff e).mpr (h 0 v s rfl rfl))
      (tieOvlFn_all2 ss vals (by simpa using hl)
        (fun i x s' hx hs => h (i + 1) x s' (by simpa using hx) (by simpa using hs)))

/-- **The `functional` sentence of a generator, at elements of its argument sorts**: exactly one
element of N is in the application. The sentence is `axiom{R} \exists{R}(Val:N, \equals{N, R}(Val:N,
g(K̄)))`, read at the valuation sending K̄ to the elements and R to a sort with an inhabitant; its
equality compares the two sides at elements of N. The hypotheses on the sentence are decided on
its text (`tieOvlFnFunShapeB`). -/
theorem tieOvlFnFun_at (hD : KoreAML.DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) {N : String} {g : KoreAML.Gen}
    {σN : M} (hσN1 : ∀ b, I.evalSymb (.sort ("Sort" ++ N)) b ↔ b = σN) (hσN2 : KoreAML.IsSort I σN)
    {σR x0 : M} (hσR : KoreAML.IsSort I σR) (hx0 : KoreAML.Inh I σR x0)
    {i : Nat} {mod : String} {a : Kore.Axiom} {val : Kore.EVar} {ks : List Kore.EVar} {body : Kore.Pattern}
    (hpat : a.pattern = .exist KoreAML.R val (.equals (KoreAML.srt N) KoreAML.R (.var (.evar val)) body))
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey)
    (hval : val.sort = KoreAML.srt N)
    (hks : ks.map (·.sort) = g.argSorts.map KoreAML.srt)
    (hbody : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ body =
      KoreAML.Cons.genPat N g
        ((ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hfresh : (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey val) ∉
      (KoreAML.tableOf a.sortVars a.pattern).ev (.sortVar "R") ::
        ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k))
    (hnd : ((KoreAML.tableOf a.sortVars a.pattern).ev (.sortVar "R") ::
        ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).Nodup)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat)
    {xs : List M} (hl : xs.length = g.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x) :
    ∃ v, KoreAML.Inh I σN v ∧ ∀ b, KoreAML.Inh I σN b → (GS I N g xs b ↔ b = v) := by
  have hat := KoreAML.trAxiom_at hD hsent
  dsimp only at hat
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hat hbody hfresh hnd
  rw [hfree] at hat
  have hlen : (t.ev (.sortVar "R") :: ks.map fun k => t.ev (KoreAML.evarKey k)).length = (σR :: xs).length := by
    have h1 := congrArg List.length hks
    simp only [List.length_map] at h1
    simp only [List.length_cons, List.length_map, h1, hl]
  have hv := tieZipVal_map (M := M) hnd hlen
  generalize tieZipVal (t.ev (.sortVar "R") :: ks.map fun k => t.ev (KoreAML.evarKey k)) (σR :: xs) = e at hv
  simp only [List.map_cons, List.cons.injEq] at hv
  obtain ⟨hvR, hvx⟩ := hv
  have hg : ∀ k ∈ KoreAML.VarKey.sortVar "R" :: ks.map KoreAML.evarKey, ∀ m,
      (KoreAML.guardOf t k).interpret I e m := by
    intro k hk m
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [KoreAML.interp_guard_sortVar hD, hvR]; exact hσR
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact tieGuards_vals hD hks hvx (tieOvlFn_all2 _ _ hl hxs) k' hk' m
  have h1 := hat e hg x0
  rw [hpat] at h1
  change (KoreAML.tr ⟨t, []⟩ (.exist KoreAML.R val (.equals (KoreAML.srt N) KoreAML.R (.var (.evar val)) body))).interpret I e x0 ↔
    (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e x0 at h1
  have hRv : ∀ (e' : Valuation M) b, (KoreAML.trSort t KoreAML.R).interpret I e' b ↔ b = e'.evalEvar (t.ev (.sortVar "R")) :=
    fun e' b => by rw [trSort_R, KoreAML.interp_evar]
  have hS : ∀ (e' : Valuation M) b, (KoreAML.trSort t (KoreAML.srt N)).interpret I e' b ↔ b = σN :=
    fun e' b => by rw [trSort_srt]; exact hσN1 b
  have hne : t.ev (.sortVar "R") ≠ t.ev (KoreAML.evarKey val) := fun h => hfresh (h ▸ List.mem_cons_self ..)
  have hupd : ∀ v : M, (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ : Valuation M).evalEvar
      (t.ev (.sortVar "R")) = e.evalEvar (t.ev (.sortVar "R")) := fun v => Function.update_noteq hne _ _
  have hmap : ∀ v : M, (ks.map fun k => t.ev (KoreAML.evarKey k)).map
      (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ : Valuation M).evalEvar =
      (ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar := fun v =>
    List.map_congr_left fun z hz => Function.update_noteq
      (fun (h : z = t.ev (KoreAML.evarKey val)) => hfresh (List.mem_cons_of_mem _ (h ▸ hz))) _ _
  have hlhs := h1.mpr ((KoreAML.interp_inhOf_of (hRv e)).mpr (by rw [hvR]; exact hx0))
  rw [KoreAML.tr, KoreAML.interp_sExists] at hlhs
  obtain ⟨v, hv1, hv2⟩ := hlhs
  rw [KoreAML.interp_member hD] at hv1
  simp only [Function.update_same] at hv1
  rw [hval] at hv1
  have hvN : KoreAML.Inh I σN v := (KoreAML.interp_inhOf_of (hS _)).mp hv1
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hS _) (hRv _) hσN2 (by rw [hupd, hvR]; exact hσR)] at hv2
  refine ⟨v, hvN, fun b hb => ?_⟩
  have h2 := hv2.2 b hb
  rw [hbody, tieGen_vars, hmap, hvx, KoreAML.tr, KoreAML.interp_evar] at h2
  simp only [Function.update_same] at h2
  exact h2.symm

/-- The valuation of a sentence with the free variables `xs ++ ys`, at elements of their sorts. -/
theorem tieOvlFn_val2 (hD : KoreAML.DefOK I) {t : KoreAML.VarTable} {xs ys : List Kore.EVar} {ss ss' : List String}
    (hxs : xs.map (·.sort) = ss.map KoreAML.srt) (hys : ys.map (·.sort) = ss'.map KoreAML.srt)
    (hnd : ((xs.map fun k => t.ev (KoreAML.evarKey k)) ++ (ys.map fun k => t.ev (KoreAML.evarKey k))).Nodup)
    {us vs : List M} (hl : us.length = ss.length) (hl' : vs.length = ss'.length)
    (hus : ∀ (i : Nat) x s, us[i]? = some x → ss[i]? = some s → InS I s x)
    (hvs : ∀ (i : Nat) x s, vs[i]? = some x → ss'[i]? = some s → InS I s x) :
    ∃ e : Valuation M, (xs.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar = us ∧
      (ys.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar = vs ∧
      ∀ k ∈ (xs ++ ys).map KoreAML.evarKey, ∀ m, (KoreAML.guardOf t k).interpret I e m := by
  have hlx : (xs.map fun k => t.ev (KoreAML.evarKey k)).length = us.length := by
    have h1 := congrArg List.length hxs
    simp only [List.length_map] at h1
    rw [List.length_map, h1, hl]
  have hly : (ys.map fun k => t.ev (KoreAML.evarKey k)).length = vs.length := by
    have h1 := congrArg List.length hys
    simp only [List.length_map] at h1
    rw [List.length_map, h1, hl']
  have hv := tieZipVal_map (M := M) (vals := us ++ vs) hnd
    (by rw [List.length_append, List.length_append, hlx, hly])
  generalize tieZipVal ((xs.map fun k => t.ev (KoreAML.evarKey k)) ++
    (ys.map fun k => t.ev (KoreAML.evarKey k))) (us ++ vs) = e at hv
  rw [List.map_append] at hv
  obtain ⟨hv1, hv2⟩ := List.append_inj hv (by rw [List.length_map, hlx])
  refine ⟨e, hv1, hv2, fun k hk m => ?_⟩
  rw [List.map_append, List.mem_append] at hk
  rcases hk with hk | hk
  · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact tieGuards_vals hD hxs hv1 (tieOvlFn_all2 _ _ hl hus) k' hk' m
  · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact tieGuards_vals hD hys hv2 (tieOvlFn_all2 _ _ hl' hvs) k' hk' m

/-- **The no-confusion sentence of one generator, with its Cons-Fun, at elements of its argument
sorts**: two argument lists at which the generator builds the same elements are equal. The
sentence is `\implies{N}(\and{N}(g(X̄), g(Ȳ)), g(X̄ ∧ Ȳ))`, read at the valuation sending X̄ and Ȳ
to the two lists: the one element both applications hold is in `g(X̄ ∧ Ȳ)`, so each `Xᵢ ∧ Yᵢ`
holds an element. The hypotheses on the sentence are decided on its text (`tieOvlFnInjShapeB`). -/
theorem tieOvlFnInj_at (hD : KoreAML.DefOK I) {N : String} {g : KoreAML.Gen}
    (hfun : I ⊧ᴵ (KoreAML.Cons.funItem N g).pat)
    {i : Nat} {mod : String} {a : Kore.Axiom} {xs ys : List Kore.EVar} {p1 p2 q : Kore.Pattern}
    (hpat : a.pattern = .implies (KoreAML.srt N) (.and (KoreAML.srt N) [p1, p2]) q)
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey)
    (hxs : xs.map (·.sort) = g.argSorts.map KoreAML.srt) (hys : ys.map (·.sort) = g.argSorts.map KoreAML.srt)
    (hp1 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p1 = KoreAML.Cons.genPat N g
      ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hp2 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p2 = KoreAML.Cons.genPat N g
      ((ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hq : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ q = KoreAML.Cons.genPat N g
      (((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).zip
        (ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k))).map
          fun p => KoreAML.sAnd (.evar p.1) (.evar p.2)))
    (hnd : ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)) ++
      (ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k))).Nodup)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat)
    {us vs : List M} (hl : us.length = g.argSorts.length) (hl' : vs.length = g.argSorts.length)
    (hus : ∀ (i : Nat) x s, us[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hvs : ∀ (i : Nat) x s, vs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (heq : ∀ m, GS I N g us m ↔ GS I N g vs m) : us = vs := by
  have hat := KoreAML.trAxiom_at hD hsent
  dsimp only at hat
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hat hp1 hp2 hq hnd
  rw [hfree] at hat
  obtain ⟨e, hv1, hv2, hg⟩ := tieOvlFn_val2 hD hxs hys hnd hl hl' hus hvs
  obtain ⟨y1, hy1N, hy1⟩ := fun_at hD hfun hl hus
  have h1 := hat e hg y1
  rw [hpat] at h1
  change (KoreAML.sImp (KoreAML.trSort t (KoreAML.srt N))
      (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2)) (KoreAML.tr ⟨t, []⟩ q)).interpret I e y1 ↔
    (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N))).interpret I e y1 at h1
  rw [KoreAML.interp_sImp, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars, hv1, hv2, trSort_srt] at h1
  have hq' := (h1.mpr ((inS_iff e).mpr hy1N)).2 ⟨(hy1 y1).mpr rfl, (heq y1).mp ((hy1 y1).mpr rfl)⟩
  rw [hq, genPat_eq] at hq'
  have hlen : (xs.map fun k => t.ev (KoreAML.evarKey k)).length = (ys.map fun k => t.ev (KoreAML.evarKey k)).length := by
    have h1 := congrArg List.length hxs
    have h2 := congrArg List.length hys
    simp only [List.length_map] at h1 h2
    rw [List.length_map, List.length_map, h1, h2]
  have hmap := tieOvlFn_zipAnd_eq _ _ hlen (tieOvlFn_appList_args _ _ _ hq')
  rw [hv1, hv2] at hmap
  exact hmap

/-- **A no-confusion sentence of two generators, with Cons-Fun of one of them, at elements of their
argument sorts**: the two applications do not hold the same elements. The sentence is
`\not{N}(\and{N}(g(X̄), g'(Ȳ)))`, read at the valuation sending X̄ and Ȳ to the two lists: the one
element of N one application holds is not in the other. The hypotheses on the sentence are decided
on its text (`tieOvlFnDistShapeB`). -/
theorem tieOvlFnDist_at (hD : KoreAML.DefOK I) {N : String} {g g' : KoreAML.Gen}
    (hfun : (I ⊧ᴵ (KoreAML.Cons.funItem N g).pat) ∨ (I ⊧ᴵ (KoreAML.Cons.funItem N g').pat))
    {i : Nat} {mod : String} {a : Kore.Axiom} {xs ys : List Kore.EVar} {p1 p2 : Kore.Pattern}
    (hpat : a.pattern = .not (KoreAML.srt N) (.and (KoreAML.srt N) [p1, p2]))
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey)
    (hxs : xs.map (·.sort) = g.argSorts.map KoreAML.srt) (hys : ys.map (·.sort) = g'.argSorts.map KoreAML.srt)
    (hp1 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p1 = KoreAML.Cons.genPat N g
      ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hp2 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p2 = KoreAML.Cons.genPat N g'
      ((ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hnd : ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)) ++
      (ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k))).Nodup)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat)
    {us vs : List M} (hl : us.length = g.argSorts.length) (hl' : vs.length = g'.argSorts.length)
    (hus : ∀ (i : Nat) x s, us[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hvs : ∀ (i : Nat) x s, vs[i]? = some x → g'.argSorts[i]? = some s → InS I s x) :
    ¬ ∀ m, GS I N g us m ↔ GS I N g' vs m := by
  have hat := KoreAML.trAxiom_at hD hsent
  dsimp only at hat
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hat hp1 hp2 hnd
  rw [hfree] at hat
  obtain ⟨e, hv1, hv2, hg⟩ := tieOvlFn_val2 hD hxs hys hnd hl hl' hus hvs
  intro heq
  have key : ∃ y, InS I N y ∧ GS I N g us y ∧ GS I N g' vs y := by
    rcases hfun with hfun | hfun
    · obtain ⟨y1, hy1N, hy1⟩ := fun_at hD hfun hl hus
      exact ⟨y1, hy1N, (hy1 y1).mpr rfl, (heq y1).mp ((hy1 y1).mpr rfl)⟩
    · obtain ⟨y1, hy1N, hy1⟩ := fun_at hD hfun hl' hvs
      exact ⟨y1, hy1N, (heq y1).mpr ((hy1 y1).mpr rfl), (hy1 y1).mpr rfl⟩
  obtain ⟨y1, hy1N, hyg, hyg'⟩ := key
  have h1 := hat e hg y1
  rw [hpat] at h1
  change (KoreAML.sNot (KoreAML.trSort t (KoreAML.srt N))
      (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2))).interpret I e y1 ↔
    (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N))).interpret I e y1 at h1
  rw [KoreAML.interp_sNot, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars, hv1, hv2, trSort_srt] at h1
  exact (h1.mpr ((inS_iff e).mpr hy1N)).1 ⟨hyg, hyg'⟩

/-! ## What the lemmas ask of an interpretation beside the sentences -/

/-- The part of the encoding the sentences of the sort named `N` are read under: definedness, the
definition of ceiling, the sort constant of `N` denoting one sort, and some sort with an inhabitant
(a `functional` sentence is closed over a sort variable, and says nothing where every sort is
empty). A model of Γ meets all four (`tieOvlFnBase_of_Γ_dotk`). -/
structure TieOvlFnBase (I : Interpretation KoreAML.Sym M) (N : String) : Prop where
  defOK : KoreAML.DefOK I
  ceil : I ⊧ᴵ KoreAML.ceilDefItem.pat
  sortN : ∃ σ, (∀ b, I.evalSymb (.sort ("Sort" ++ N)) b ↔ b = σ) ∧ KoreAML.IsSort I σ
  inh : ∃ σ x, KoreAML.IsSort I σ ∧ KoreAML.Inh I σ x

/-- The arity of the generator `g` of the sort named `N`: applied to elements of its argument
sorts it holds elements of `N` only. The `functional` sentence states nothing of the elements of
the application outside `N`; Cons-Fun does. -/
def TieOvlFnArity (I : Interpretation KoreAML.Sym M) (N : String) (g : KoreAML.Gen) : Prop :=
  ∀ xs : List M, xs.length = g.argSorts.length →
    (∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x) → ∀ m, GS I N g xs m → InS I N m

theorem tieOvlFnBase_of_Γ {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c) {N : Srt}
    (hN : N < nRegSorts + c.sortNames.length) (hinh : ∃ σ x, KoreAML.IsSort I σ ∧ KoreAML.Inh I σ x) :
    TieOvlFnBase I (c.sortName N) :=
  ⟨defOK hI, sat_sigItem hI (sig_ceilDef (c := c)), sortSing hI hN, hinh⟩

/-- A numbered sort's constant denotes one sort in a model of Γ (G-sort, an item of `sigItems`). -/
theorem tieOvlFn_sortSing {c : Semantics} (hI : I ⊧ᴵP Γ c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length) :
    ∃ σ, (∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName s)) a ↔ a = σ) ∧ KoreAML.IsSort I σ :=
  KoreAML.sortConst_of (defOK hI) (sat_sigItem hI (sig_sortConst hs))

/-- `.K` is a value of K in every semantics: `dotk`, with no arguments and the result K, is the
second of the fixed constructors that head `ctorSigs`. -/
theorem tieOvlFn_dotk_sortOf (c : Semantics) : c.sortOf (.ctor dotk []) = some Srt.k := by
  unfold Semantics.sortOf
  rw [lookupSig_eq]
  rfl

/-- **Some sort is inhabited in every model of Γ.** Γ states no sort's nonemptiness (`sigItems`
holds no G-nonempty item); the sort K is inhabited because it has a value: `ΓDomains` states that
the value `.K` denotes one element of K (`den_single`). -/
theorem tieOvlFnInh_of_Γ {c : Semantics} (hI : I ⊧ᴵP Γ c) :
    ∃ σ x, KoreAML.IsSort I σ ∧ KoreAML.Inh I σ x := by
  obtain ⟨σ, hσ1, hσ2⟩ := tieOvlFn_sortSing hI (s := Srt.k)
    (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _))
  obtain ⟨a, -, ha⟩ := den_single hI (tieOvlFn_dotk_sortOf c) KoreAML.val0
  exact ⟨σ, a, hσ2, (KoreAML.interp_inhOf_of (S := KoreAML.Cons.sortP (c.sortName Srt.k)) (fun b => hσ1 b)).mp ha⟩

/-- **A model of Γ meets `TieOvlFnBase`** at every numbered sort, with no assumption on the
interpretation: some sort is inhabited by `tieOvlFnInh_of_Γ`. -/
theorem tieOvlFnBase_of_Γ_dotk {c : Semantics} (hI : I ⊧ᴵP Γ c) {N : Srt}
    (hN : N < nRegSorts + c.sortNames.length) : TieOvlFnBase I (c.sortName N) :=
  ⟨defOK hI, sat_sigItem hI (sig_ceilDef (c := c)), tieOvlFn_sortSing hI hN, tieOvlFnInh_of_Γ hI⟩

/-- **G-arity gives the arity of a generator**: Γ holds `symArityItem c k` for every symbol of
`kernelSyms c` (`sig_arity`; the overloading symbols are among them, `c.ovlSigs`), and where the
symbol's name is no instance (`symApp` writes it at its name) the item says that the symbol applied
to elements of its argument sorts holds elements of its result sort only. -/
theorem tieOvlFnArity_of_Γ {c : Semantics} (hI : I ⊧ᴵP Γ c) {k : CtorSig} (hkm : k ∈ kernelSyms c)
    (hit0 : instDecode? (c.symName k.name) = none) :
    TieOvlFnArity I (c.sortName k.result) (Gen.toK c (.ctor k)) := by
  intro bs hbl hbs m hm
  have hD := defOK hI
  have hit := sat_sigItem hI (sig_arity (c := c) (k := k) hkm)
  rw [symArityItem_plain_irs (fun _ => symApp_noInst hit0)] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  apply hinc
  obtain ⟨a, ha, hm⟩ := hm
  rw [interp_appList]
  refine ⟨a, ha, bs, ?_, hm⟩
  clear ha hm hinc hit
  have : ∀ (ss : List Srt) (bs : List M), bs.length = (ss.map c.sortName).length →
      (∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x) →
      All2 (fun φ b => φ.interpret I KoreAML.val0 b)
        (ss.map fun s => KoreAML.inhOf (sortP (c.sortName s))) bs := by
    intro ss
    induction ss with
    | nil => intro bs hl _; cases bs with
      | nil => exact .nil
      | cons _ _ => simp at hl
    | cons s ss ih =>
      intro bs hl hb
      cases bs with
      | nil => simp at hl
      | cons b bs =>
        refine .cons ?_ (ih bs (by simpa using hl) (fun i x s' h1 h2 => hb (i + 1) x s' (by simpa using h1) (by simpa using h2)))
        exact hb 0 b (c.sortName s) rfl rfl
  exact this k.args bs hbl hbs

/-! ## The items give the sentences -/

/-- **Cons-Fun gives the `functional` sentence**, in every interpretation with `TieOvlFnBase`: the
converse of `tieOvlFnFun_funItem`, which needs the arity besides. -/
theorem tieOvlFnFun_sent_of_funItem {N : String} {g : KoreAML.Gen} (hB : TieOvlFnBase I N)
    (hitem : I ⊧ᴵ (KoreAML.Cons.funItem N g).pat)
    {i : Nat} {mod : String} {a : Kore.Axiom} {val : Kore.EVar} {ks : List Kore.EVar} {body : Kore.Pattern}
    (hpat : a.pattern = .exist KoreAML.R val (.equals (KoreAML.srt N) KoreAML.R (.var (.evar val)) body))
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey)
    (hval : val.sort = KoreAML.srt N)
    (hks : ks.map (·.sort) = g.argSorts.map KoreAML.srt)
    (hbody : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ body =
      KoreAML.Cons.genPat N g
        ((ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hfresh : (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey val) ∉
      (KoreAML.tableOf a.sortVars a.pattern).ev (.sortVar "R") ::
        ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)) :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  have hD := hB.defOK
  have hc := hB.ceil
  obtain ⟨σN, hσN1, hσN2⟩ := hB.sortN
  refine tieAxiom_intro hD fun e hg x => ?_
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hg hbody hfresh ⊢
  rw [hfree] at hg
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (hg _ (List.mem_cons_self ..) default)
  have hargs := tieArgs_inS hD (fun k hk m => hg k (List.mem_cons_of_mem _ hk) m)
    (ks := ks) (ss := g.argSorts) (fun k hk => List.mem_map.mpr ⟨k, hk, rfl⟩) hks
  have hl : ((ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar).length = g.argSorts.length := by
    have := congrArg List.length hks
    simpa using this
  obtain ⟨y, hyN, hy⟩ := fun_at hD hitem hl hargs
  rw [hpat]
  show (KoreAML.tr ⟨t, []⟩ (.exist KoreAML.R val (.equals (KoreAML.srt N) KoreAML.R (.var (.evar val)) body))).interpret I e x ↔
    (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e x
  have hRv : ∀ (e' : Valuation M) b, (KoreAML.trSort t KoreAML.R).interpret I e' b ↔ b = e'.evalEvar (t.ev (.sortVar "R")) :=
    fun e' b => by rw [trSort_R, KoreAML.interp_evar]
  have hS : ∀ (e' : Valuation M) b, (KoreAML.trSort t (KoreAML.srt N)).interpret I e' b ↔ b = σN :=
    fun e' b => by rw [trSort_srt]; exact hσN1 b
  rw [KoreAML.tr, KoreAML.interp_sExists, KoreAML.interp_inhOf_of (hRv e)]
  have hne : t.ev (.sortVar "R") ≠ t.ev (KoreAML.evarKey val) := fun h => hfresh (h ▸ List.mem_cons_self ..)
  have hupd : ∀ v : M, (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ : Valuation M).evalEvar
      (t.ev (.sortVar "R")) = e.evalEvar (t.ev (.sortVar "R")) := fun v => Function.update_noteq hne _ _
  have hmap : ∀ v : M, (ks.map fun k => t.ev (KoreAML.evarKey k)).map
      (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ : Valuation M).evalEvar =
      (ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar := fun v =>
    List.map_congr_left fun z hz => Function.update_noteq
      (fun (h : z = t.ev (KoreAML.evarKey val)) => hfresh (List.mem_cons_of_mem _ (h ▸ hz))) _ _
  have hbodyI : ∀ (v b : M), (KoreAML.tr ⟨t, []⟩ body).interpret I
      ⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ b ↔ b = y := fun v b => by
    rw [hbody, tieGen_vars, hmap]; exact hy b
  constructor
  · rintro ⟨v, -, h2⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hS _) (hRv _) hσN2 (by rw [hupd]; exact hR)] at h2
    rw [← hupd v]; exact h2.1
  · intro hx
    refine ⟨y, ?_, ?_⟩
    · rw [KoreAML.interp_member hD]
      simp only [Function.update_same]
      rw [hval, trSort_srt]
      exact (inS_iff _).mpr hyN
    · rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hS _) (hRv _) hσN2 (by rw [hupd]; exact hR)]
      refine ⟨by rw [hupd]; exact hx, fun b _ => ?_⟩
      rw [hbodyI, KoreAML.tr, KoreAML.interp_evar]
      simp only [Function.update_same]

/-! ## The sentences give the items -/

/-- **The `functional` sentence of a generator, with its arity, gives its Cons-Fun.** -/
theorem tieOvlFnFun_funItem {N : String} {g : KoreAML.Gen} (hB : TieOvlFnBase I N) (hA : TieOvlFnArity I N g)
    {i : Nat} {mod : String} {a : Kore.Axiom} {val : Kore.EVar} {ks : List Kore.EVar} {body : Kore.Pattern}
    (hpat : a.pattern = .exist KoreAML.R val (.equals (KoreAML.srt N) KoreAML.R (.var (.evar val)) body))
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey)
    (hval : val.sort = KoreAML.srt N)
    (hks : ks.map (·.sort) = g.argSorts.map KoreAML.srt)
    (hbody : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ body =
      KoreAML.Cons.genPat N g
        ((ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hfresh : (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey val) ∉
      (KoreAML.tableOf a.sortVars a.pattern).ev (.sortVar "R") ::
        ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k))
    (hnd : ((KoreAML.tableOf a.sortVars a.pattern).ev (.sortVar "R") ::
        ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).Nodup)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) :
    I ⊧ᴵ (KoreAML.Cons.funItem N g).pat := by
  obtain ⟨σN, hσN1, hσN2⟩ := hB.sortN
  obtain ⟨σR, x0, hσR, hx0⟩ := hB.inh
  have hN : ∀ b, InS I N b ↔ KoreAML.Inh I σN b := fun b =>
    KoreAML.interp_inhOf_of (S := KoreAML.Cons.sortP N) (e := KoreAML.val0) (fun a => hσN1 a)
  refine tieOvlFn_funItem_intro hB.defOK fun xs hl hxs => ?_
  obtain ⟨v, hv, h⟩ := tieOvlFnFun_at hB.defOK hB.ceil hσN1 hσN2 hσR hx0 hpat hfree hval hks hbody hfresh hnd
    hsent hl hxs
  refine ⟨v, (hN v).mpr hv, fun m => ⟨fun hm => (h m ((hN m).mp (hA xs hl hxs m hm))).mp hm, fun hm => ?_⟩⟩
  rw [hm]
  exact (h v hv).mpr rfl

end

/-! ## The sentences, decided on a text -/

/-- The axiom `a` is the `functional` sentence of the generator `g` of the sort N, in the form
`tieOvlFnFun_at` reads: the shape `tieFunB` asks, and the indices of the sentence's variables
apart. -/
def tieOvlFnFunShapeB (c : Semantics) (N : Srt) (g : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .exist r val (.equals s r' (.var (.evar val')) body) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let ks := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    decide (s = KoreAML.srt (c.sortName N)) && decide (r = KoreAML.R) && decide (r' = KoreAML.R) &&
    decide (val' = val) && decide (N < nRegSorts + c.sortNames.length) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey) &&
    decide (val.sort = KoreAML.srt (c.sortName N)) && decide (ks.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ body =
      KoreAML.Cons.genPat (c.sortName N) g ((ks.map fun k => t.ev (KoreAML.evarKey k)).map .evar)) &&
    decide (t.ev (KoreAML.evarKey val) ∉ t.ev (.sortVar "R") :: ks.map fun k => t.ev (KoreAML.evarKey k)) &&
    decide (t.ev (.sortVar "R") :: ks.map fun k => t.ev (KoreAML.evarKey k)).Nodup
  | _ => false

/-- The axiom `a` is the no-confusion sentence of the generator `g` of the sort N, in the form
`tieOvlFnInj_at` reads: the shape `tieInjB` asks, and the indices of the sentence's variables
apart. -/
def tieOvlFnInjShapeB (c : Semantics) (N : Srt) (g : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .implies s (.and s' [p1, p2]) q =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName N)) && decide (s' = KoreAML.srt (c.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c.sortName N) g (iy.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ q = KoreAML.Cons.genPat (c.sortName N) g
      ((ix.zip iy).map fun p => KoreAML.sAnd (.evar p.1) (.evar p.2))) &&
    decide (ix ++ iy).Nodup
  | _ => false

/-- The axiom `a` is the no-confusion sentence of the generators `g` and `g'` of the sort N, in the
form `tieOvlFnDist_at` reads: the shape `tieDistB` asks, and the indices of the sentence's
variables apart. -/
def tieOvlFnDistShapeB (c : Semantics) (N : Srt) (g g' : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .not s (.and s' [p1, p2]) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName N)) && decide (s' = KoreAML.srt (c.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g'.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c.sortName N) g' (iy.map .evar)) &&
    decide (ix ++ iy).Nodup
  | _ => false

/-- The axiom `a` is the `functional` sentence of the function-overloaded generator `g` of the sort
N, and Γ holds the generator's Cons-Fun at uncovered arguments. -/
def tieOvlFnFunAtB (c : Semantics) (N : Srt) (g : Gen) (a : Kore.Axiom) : Bool :=
  c.fnOvl g && tieOvlFnFunShapeB c N (Gen.toK c g) a &&
  (consItemsK c).any (fun it => decide (it.pat =
    (KoreAML.Cons.funUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD [])).pat))

/-- The axiom `a` is the no-confusion sentence of the function-overloaded generator `g` of the sort
N, and Γ holds the generator's Cons-Inj at uncovered arguments. -/
def tieOvlFnInjAtB (c : Semantics) (N : Srt) (g : Gen) (a : Kore.Axiom) : Bool :=
  c.fnOvl g && tieOvlFnInjShapeB c N (Gen.toK c g) a &&
  (consItemsK c).any (fun it => decide (it.pat =
    (KoreAML.Cons.injUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD [])).pat))

/-- The axiom `a` is the no-confusion sentence of the generators `g` and `g'` of the sort N, one of
them function-overloaded, and Γ holds their Cons-Dist at uncovered arguments in one of the two
orders. -/
def tieOvlFnDistAtB (c : Semantics) (N : Srt) (g g' : Gen) (a : Kore.Axiom) : Bool :=
  (c.fnOvl g || c.fnOvl g') && tieOvlFnDistShapeB c N (Gen.toK c g) (Gen.toK c g') a &&
  ((consItemsK c).any (fun it => decide (it.pat =
      (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsOf c g) (ovlArgsOf c g')).pat)) ||
    (consItemsK c).any (fun it => decide (it.pat =
      (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g') (Gen.toK c g) (ovlArgsOf c g') (ovlArgsOf c g)).pat)))

/-- **The axiom is the `functional` sentence of a function-overloaded generator** of a constructor
sort of the semantics, whose Cons-Fun at uncovered arguments Γ holds. -/
def tieOvlFnFunB (c : Semantics) (a : Kore.Axiom) : Bool :=
  (consSorts c).any fun N => (c.gens N).any fun g => tieOvlFnFunAtB c N g a

/-- **The axiom is the same-constructor no-confusion sentence of a function-overloaded generator**
of a constructor sort of the semantics, whose Cons-Inj at uncovered arguments Γ holds. -/
def tieOvlFnInjB (c : Semantics) (a : Kore.Axiom) : Bool :=
  (consSorts c).any fun N => (c.gens N).any fun g => tieOvlFnInjAtB c N g a

/-- **The axiom is a different-constructors no-confusion sentence naming a function-overloaded
generator** of a constructor sort of the semantics, whose Cons-Dist at uncovered arguments Γ
holds. -/
def tieOvlFnDistB (c : Semantics) (a : Kore.Axiom) : Bool :=
  (consSorts c).any fun N => (c.gens N).any fun g => (c.gens N).any fun g' => tieOvlFnDistAtB c N g g' a

/-- **Γ holds the generator's G-arity in the form `tieOvlFnArity_of_Γ` reads**: `g` is a symbol of
`kernelSyms c` of result N whose name is no instance. A function-overloaded generator is a symbol
(`Semantics.fnOvl` is false at an injection). -/
def tieOvlFnArityB (c : Semantics) (N : Srt) : Gen → Bool
  | .ctor k => decide (k ∈ kernelSyms c) && decide (k.result = N) && (instDecode? (c.symName k.name)).isNone
  | .inj _ => false

theorem tieOvlFnFunB_at {c : Semantics} {a : Kore.Axiom} (h : tieOvlFnFunB c a = true) :
    ∃ N g, tieOvlFnFunAtB c N g a = true := by
  simp only [tieOvlFnFunB, List.any_eq_true] at h
  obtain ⟨N, -, g, -, h⟩ := h
  exact ⟨N, g, h⟩

theorem tieOvlFnInjB_at {c : Semantics} {a : Kore.Axiom} (h : tieOvlFnInjB c a = true) :
    ∃ N g, tieOvlFnInjAtB c N g a = true := by
  simp only [tieOvlFnInjB, List.any_eq_true] at h
  obtain ⟨N, -, g, -, h⟩ := h
  exact ⟨N, g, h⟩

theorem tieOvlFnDistB_at {c : Semantics} {a : Kore.Axiom} (h : tieOvlFnDistB c a = true) :
    ∃ N g g', tieOvlFnDistAtB c N g g' a = true := by
  simp only [tieOvlFnDistB, List.any_eq_true] at h
  obtain ⟨N, -, g, -, g', -, h⟩ := h
  exact ⟨N, g, g', h⟩

/-! ## The item is among Γ's -/

theorem tieOvlFnFun_item {c : Semantics} {N : Srt} {g : Gen} {a : Kore.Axiom} (h : tieOvlFnFunAtB c N g a = true) :
    ∃ it ∈ consItemsK c, it.pat =
      (KoreAML.Cons.funUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD [])).pat := by
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at h
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp h.2
  exact ⟨it, hit, of_decide_eq_true he⟩

theorem tieOvlFnInj_item {c : Semantics} {N : Srt} {g : Gen} {a : Kore.Axiom} (h : tieOvlFnInjAtB c N g a = true) :
    ∃ it ∈ consItemsK c, it.pat =
      (KoreAML.Cons.injUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD [])).pat := by
  simp only [tieOvlFnInjAtB, Bool.and_eq_true] at h
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp h.2
  exact ⟨it, hit, of_decide_eq_true he⟩

theorem tieOvlFnDist_item {c : Semantics} {N : Srt} {g g' : Gen} {a : Kore.Axiom}
    (h : tieOvlFnDistAtB c N g g' a = true) :
    (∃ it ∈ consItemsK c, it.pat =
      (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsOf c g) (ovlArgsOf c g')).pat) ∨
    (∃ it ∈ consItemsK c, it.pat =
      (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g') (Gen.toK c g) (ovlArgsOf c g') (ovlArgsOf c g)).pat) := by
  simp only [tieOvlFnDistAtB, Bool.and_eq_true] at h
  rcases Bool.or_eq_true _ _ ▸ h.2 with h2 | h2
  · obtain ⟨it, hit, he⟩ := List.any_eq_true.mp h2
    exact .inl ⟨it, hit, of_decide_eq_true he⟩
  · obtain ⟨it, hit, he⟩ := List.any_eq_true.mp h2
    exact .inr ⟨it, hit, of_decide_eq_true he⟩

/-! ## The weaker direction: the text's sentences give Γ's items -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics}

/-- **A `functional` sentence in the form `tieOvlFnFunShapeB` decides, with the generator's arity,
gives the generator's Cons-Fun**, in every interpretation with `TieOvlFnBase`. -/
theorem tieOvlFnFun_funItem_of {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnFunShapeB c N g a = true) (hB : TieOvlFnBase I (c.sortName N))
    (hA : TieOvlFnArity I (c.sortName N) g) {i : Nat} {mod : String}
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) :
    I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat := by
  unfold tieOvlFnFunShapeB at h
  split at h
  · rename_i r val s r' val' body hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
    subst h1 h2 h3 h4
    exact tieOvlFnFun_funItem hB hA hp h6 h7 h8 h9 h10 h11 hsent
  · cases h

/-- **A same-constructor sentence in the form `tieOvlFnInjShapeB` decides, with the generator's
Cons-Fun, gives the generator's Cons-Inj**, in every interpretation with definedness. -/
theorem tieOvlFnInj_injItem_of {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnInjShapeB c N g a = true) (hD : KoreAML.DefOK I)
    (hfun : I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat) {i : Nat} {mod : String}
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) :
    I ⊧ᴵ (KoreAML.Cons.injItem (c.sortName N) g).pat := by
  unfold tieOvlFnInjShapeB at h
  split at h
  · rename_i s s' p1 p2 q hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    subst h1 h2
    exact tieOvlFn_injItem_intro hD fun us vs hl hl' hus hvs heq =>
      tieOvlFnInj_at hD hfun hp h3 h4 h5 h6 h7 h8 h9 hsent hl hl' hus hvs heq
  · cases h

/-- **A different-constructors sentence in the form `tieOvlFnDistShapeB` decides, with Cons-Fun of
one of the two generators, gives their Cons-Dist in both orders**, in every interpretation with
definedness. -/
theorem tieOvlFnDist_distItem_of {N : Srt} {g g' : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnDistShapeB c N g g' a = true) (hD : KoreAML.DefOK I)
    (hfun : (I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat) ∨ (I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g').pat))
    {i : Nat} {mod : String} (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) :
    (I ⊧ᴵ (KoreAML.Cons.distItem (c.sortName N) g g').pat) ∧ (I ⊧ᴵ (KoreAML.Cons.distItem (c.sortName N) g' g).pat) := by
  unfold tieOvlFnDistShapeB at h
  split at h
  · rename_i s s' p1 p2 hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    subst h1 h2
    have key := fun (us vs : List M) hl hl' hus hvs =>
      tieOvlFnDist_at (us := us) (vs := vs) hD hfun hp h3 h4 h5 h6 h7 h8 hsent hl hl' hus hvs
    exact ⟨tieOvlFn_distItem_intro hD key,
      tieOvlFn_distItem_intro hD fun vs us hl' hl hvs hus heq => key us vs hl hl' hus hvs fun m => (heq m).symm⟩
  · cases h

/-- **The `functional` sentence of a function-overloaded generator entails Γ's item**, Cons-Fun at
uncovered arguments, whatever overloads the item names: in every interpretation with `TieOvlFnBase`
and the generator's arity that satisfies the sentence. -/
theorem tieOvlFnFun_weaker {N : Srt} {g : Gen} {a : Kore.Axiom} (h : tieOvlFnFunAtB c N g a = true)
    (hB : TieOvlFnBase I (c.sortName N)) (hA : TieOvlFnArity I (c.sortName N) (Gen.toK c g))
    {i : Nat} {mod : String} (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) (covs : List (List String)) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem (c.sortName N) (Gen.toK c g) covs).pat := by
  simp only [tieOvlFnFunAtB, Bool.and_eq_true] at h
  exact funUncItem_of_funItem covs (tieOvlFnFun_funItem_of h.1.2 hB hA hsent)

/-- **The same-constructor sentence of a function-overloaded generator, with its `functional`
sentence, entails Γ's item**, Cons-Inj at uncovered arguments: in every interpretation with
`TieOvlFnBase` and the generator's arity that satisfies the two sentences. -/
theorem tieOvlFnInj_weaker {N : Srt} {g : Gen} {af a : Kore.Axiom} (hf : tieOvlFnFunAtB c N g af = true)
    (h : tieOvlFnInjAtB c N g a = true)
    (hB : TieOvlFnBase I (c.sortName N)) (hA : TieOvlFnArity I (c.sortName N) (Gen.toK c g))
    {j i : Nat} {modf mod : String} (hsf : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨j, modf, af⟩).pat)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) (covs : List (List String)) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem (c.sortName N) (Gen.toK c g) covs).pat := by
  simp only [tieOvlFnFunAtB, tieOvlFnInjAtB, Bool.and_eq_true] at hf h
  exact injUncItem_of_injItem covs
    (tieOvlFnInj_injItem_of h.1.2 hB.defOK (tieOvlFnFun_funItem_of hf.1.2 hB hA hsf) hsent)

/-- **A different-constructors sentence of two generators, with the `functional` sentence of one of
them, entails Γ's item**, Cons-Dist at uncovered arguments, in both orders and whatever overloads
the item names: in every interpretation with `TieOvlFnBase` and that generator's arity that
satisfies the two sentences. `gf` is the generator whose `functional` sentence `af` is. -/
theorem tieOvlFnDist_weaker {N : Srt} {g g' : Gen} {gf : KoreAML.Gen} {af a : Kore.Axiom}
    (hgf : gf = Gen.toK c g ∨ gf = Gen.toK c g')
    (hf : tieOvlFnFunShapeB c N gf af = true) (h : tieOvlFnDistAtB c N g g' a = true)
    (hB : TieOvlFnBase I (c.sortName N)) (hA : TieOvlFnArity I (c.sortName N) gf)
    {j i : Nat} {modf mod : String} (hsf : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨j, modf, af⟩).pat)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') ug ug').pat) ∧
    (I ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g') (Gen.toK c g) ug' ug).pat) := by
  simp only [tieOvlFnDistAtB, Bool.and_eq_true] at h
  have hfun := tieOvlFnFun_funItem_of hf hB hA hsf
  have hd := tieOvlFnDist_distItem_of h.1.2 hB.defOK
    (hgf.elim (fun e => .inl (e ▸ hfun)) fun e => .inr (e ▸ hfun)) hsent
  exact ⟨tieOvlFn_distUncItem_of_distItem ug ug' hd.1, tieOvlFn_distUncItem_of_distItem ug' ug hd.2⟩

/-- **The arity in a model of Γ**, from `tieOvlFnArityB`. -/
theorem tieOvlFnArity_of_ΓB (hI : I ⊧ᴵP Γ c) {N : Srt} {g : Gen} (h : tieOvlFnArityB c N g = true) :
    TieOvlFnArity I (c.sortName N) (Gen.toK c g) := by
  cases g with
  | inj _ => cases h
  | ctor k =>
    simp only [tieOvlFnArityB, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨hk, rfl⟩, hi⟩ := h
    exact tieOvlFnArity_of_Γ hI hk hi

/-- **A model of Γ that satisfies the `functional` sentence of a function-overloaded generator
satisfies Γ's Cons-Fun at uncovered arguments by the sentence**: `tieOvlFnFun_weaker` with its
hypotheses discharged by Γ (`tieOvlFnBase_of_Γ_dotk`, `tieOvlFnArity_of_ΓB`). -/
theorem tieOvlFnFun_weaker_Γ (hI : I ⊧ᴵP Γ c) {N : Srt} {g : Gen} {a : Kore.Axiom}
    (h : tieOvlFnFunAtB c N g a = true) (hN : N < nRegSorts + c.sortNames.length) (hA : tieOvlFnArityB c N g = true)
    {i : Nat} {mod : String} (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) (covs : List (List String)) :
    I ⊧ᴵ (KoreAML.Cons.funUncItem (c.sortName N) (Gen.toK c g) covs).pat :=
  tieOvlFnFun_weaker h (tieOvlFnBase_of_Γ_dotk hI hN) (tieOvlFnArity_of_ΓB hI hA) hsent covs

/-- Cons-Inj at uncovered arguments, in a model of Γ that satisfies the two sentences. -/
theorem tieOvlFnInj_weaker_Γ (hI : I ⊧ᴵP Γ c) {N : Srt} {g : Gen} {af a : Kore.Axiom}
    (hf : tieOvlFnFunAtB c N g af = true) (h : tieOvlFnInjAtB c N g a = true)
    (hN : N < nRegSorts + c.sortNames.length) (hA : tieOvlFnArityB c N g = true)
    {j i : Nat} {modf mod : String} (hsf : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨j, modf, af⟩).pat)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) (covs : List (List String)) :
    I ⊧ᴵ (KoreAML.Cons.injUncItem (c.sortName N) (Gen.toK c g) covs).pat :=
  tieOvlFnInj_weaker hf h (tieOvlFnBase_of_Γ_dotk hI hN) (tieOvlFnArity_of_ΓB hI hA) hsf hsent covs

/-- Cons-Dist at uncovered arguments, in both orders, in a model of Γ that satisfies the
different-constructors sentence and the `functional` sentence of `gf`, one of the two generators. -/
theorem tieOvlFnDist_weaker_Γ (hI : I ⊧ᴵP Γ c) {N : Srt} {g g' gf : Gen} {af a : Kore.Axiom}
    (hgf : gf = g ∨ gf = g') (hf : tieOvlFnFunShapeB c N (Gen.toK c gf) af = true)
    (h : tieOvlFnDistAtB c N g g' a = true)
    (hN : N < nRegSorts + c.sortNames.length) (hA : tieOvlFnArityB c N gf = true)
    {j i : Nat} {modf mod : String} (hsf : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨j, modf, af⟩).pat)
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') ug ug').pat) ∧
    (I ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g') (Gen.toK c g) ug' ug).pat) :=
  tieOvlFnDist_weaker (hgf.elim (fun e => .inl (congrArg _ e)) fun e => .inr (congrArg _ e)) hf h
    (tieOvlFnBase_of_Γ_dotk hI hN) (tieOvlFnArity_of_ΓB hI hA) hsf hsent ug ug'

/-- **Cons-Fun gives the `functional` sentence in the form `tieOvlFnFunShapeB` decides**, in every
interpretation with `TieOvlFnBase`. -/
theorem tieOvlFnFun_sent_of {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnFunShapeB c N g a = true) (hB : TieOvlFnBase I (c.sortName N))
    (hitem : I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat) {i : Nat} {mod : String} :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  unfold tieOvlFnFunShapeB at h
  split at h
  · rename_i r val s r' val' body hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, -⟩ := h
    subst h1 h2 h3 h4
    exact tieOvlFnFun_sent_of_funItem hB hitem hp h6 h7 h8 h9 h10
  · cases h

/-- **Under `TieOvlFnBase` and the arity, the `functional` sentence and Cons-Fun are equivalent.** -/
theorem tieOvlFnFun_sent_iff {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnFunShapeB c N g a = true) (hB : TieOvlFnBase I (c.sortName N))
    (hA : TieOvlFnArity I (c.sortName N) g) {i : Nat} {mod : String} :
    (I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) ↔ (I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat) :=
  ⟨tieOvlFnFun_funItem_of h hB hA, fun hf => tieOvlFnFun_sent_of h hB hf⟩

/-- **Cons-Fun and Cons-Inj give the same-constructor sentence in the form `tieOvlFnInjShapeB`
decides**, in every interpretation with definedness. -/
theorem tieOvlFnInj_sent_of {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnInjShapeB c N g a = true) (hD : KoreAML.DefOK I)
    (hfun : I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat)
    (hinj : I ⊧ᴵ (KoreAML.Cons.injItem (c.sortName N) g).pat) {i : Nat} {mod : String} :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  unfold tieOvlFnInjShapeB at h
  split at h
  · rename_i s s' p1 p2 q hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩ := h
    subst h1 h2
    exact tieInj_entailed hD hfun hinj hp h3 h4 h5 h6 h7 h8
  · cases h

/-- **Cons-Fun of both generators and Cons-Dist in one order give the different-constructors
sentence in the form `tieOvlFnDistShapeB` decides**, in every interpretation with definedness. -/
theorem tieOvlFnDist_sent_of {N : Srt} {g g' : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnDistShapeB c N g g' a = true) (hD : KoreAML.DefOK I)
    (hfun : I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat)
    (hfun' : I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g').pat)
    (hdist : (I ⊧ᴵ (KoreAML.Cons.distItem (c.sortName N) g g').pat) ∨
      (I ⊧ᴵ (KoreAML.Cons.distItem (c.sortName N) g' g).pat)) {i : Nat} {mod : String} :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  unfold tieOvlFnDistShapeB at h
  split at h
  · rename_i s s' p1 p2 hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩ := h
    subst h1 h2
    exact tieDist_entailed hD hfun hfun' hdist hp h3 h4 h5 h6 h7
  · cases h

end

end Faithful

/-! ## The predicates do not read the hooks' parameters -/

kernel_rfl Faithful.tieOvlFnFunAtB_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Srt) (g : Gen) (a : Kore.Axiom),
  Faithful.tieOvlFnFunAtB (c.withHooks H) N g a = Faithful.tieOvlFnFunAtB c N g a

kernel_rfl Faithful.tieOvlFnInjAtB_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Srt) (g : Gen) (a : Kore.Axiom),
  Faithful.tieOvlFnInjAtB (c.withHooks H) N g a = Faithful.tieOvlFnInjAtB c N g a

kernel_rfl Faithful.tieOvlFnDistAtB_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Srt) (g g' : Gen) (a : Kore.Axiom),
  Faithful.tieOvlFnDistAtB (c.withHooks H) N g g' a = Faithful.tieOvlFnDistAtB c N g g' a

kernel_rfl Faithful.tieOvlFnFunB_withHooks : ∀ (c : Semantics) (H : HookParams) (a : Kore.Axiom),
  Faithful.tieOvlFnFunB (c.withHooks H) a = Faithful.tieOvlFnFunB c a

kernel_rfl Faithful.tieOvlFnInjB_withHooks : ∀ (c : Semantics) (H : HookParams) (a : Kore.Axiom),
  Faithful.tieOvlFnInjB (c.withHooks H) a = Faithful.tieOvlFnInjB c a

kernel_rfl Faithful.tieOvlFnDistB_withHooks : ∀ (c : Semantics) (H : HookParams) (a : Kore.Axiom),
  Faithful.tieOvlFnDistB (c.withHooks H) a = Faithful.tieOvlFnDistB c a

kernel_rfl Faithful.tieOvlFnArityB_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Srt) (g : Gen),
  Faithful.tieOvlFnArityB (c.withHooks H) N g = Faithful.tieOvlFnArityB c N g

namespace Faithful

/-- **Γ holds the item at every interpretation of the hooks' parameters**: Cons-Fun at uncovered
arguments of the generator whose `functional` sentence `tieOvlFnFunAtB` accepts. -/
theorem tieOvlFnFun_item_withHooks {c : Semantics} {N : Srt} {g : Gen} {a : Kore.Axiom}
    (h : tieOvlFnFunAtB c N g a = true) (H : HookParams) :
    ∃ it ∈ consItemsK (c.withHooks H), it.pat = (KoreAML.Cons.funUncItem ((c.withHooks H).sortName N)
      (Gen.toK (c.withHooks H) g) ((ovlArgsOf (c.withHooks H) g).getD [])).pat :=
  tieOvlFnFun_item ((tieOvlFnFunAtB_withHooks c H N g a).trans h)

/-- Cons-Inj at uncovered arguments, at every interpretation of the hooks' parameters. -/
theorem tieOvlFnInj_item_withHooks {c : Semantics} {N : Srt} {g : Gen} {a : Kore.Axiom}
    (h : tieOvlFnInjAtB c N g a = true) (H : HookParams) :
    ∃ it ∈ consItemsK (c.withHooks H), it.pat = (KoreAML.Cons.injUncItem ((c.withHooks H).sortName N)
      (Gen.toK (c.withHooks H) g) ((ovlArgsOf (c.withHooks H) g).getD [])).pat :=
  tieOvlFnInj_item ((tieOvlFnInjAtB_withHooks c H N g a).trans h)

/-- Cons-Dist at uncovered arguments, in one of the two orders, at every interpretation of the
hooks' parameters. -/
theorem tieOvlFnDist_item_withHooks {c : Semantics} {N : Srt} {g g' : Gen} {a : Kore.Axiom}
    (h : tieOvlFnDistAtB c N g g' a = true) (H : HookParams) :
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (KoreAML.Cons.distUncItem ((c.withHooks H).sortName N)
      (Gen.toK (c.withHooks H) g) (Gen.toK (c.withHooks H) g') (ovlArgsOf (c.withHooks H) g)
      (ovlArgsOf (c.withHooks H) g')).pat) ∨
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (KoreAML.Cons.distUncItem ((c.withHooks H).sortName N)
      (Gen.toK (c.withHooks H) g') (Gen.toK (c.withHooks H) g) (ovlArgsOf (c.withHooks H) g')
      (ovlArgsOf (c.withHooks H) g)).pat) :=
  tieOvlFnDist_item ((tieOvlFnDistAtB_withHooks c H N g g' a).trans h)

end Faithful

end KCore
