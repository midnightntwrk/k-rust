/-
  Lemmas of the per-sentence tie, for any text: Γ's no-junk item of a sort entails the no-junk
  sentence over any list that holds its generators, so the text's sentence with its disjuncts in
  another order.
-/
import KcoreSpec.Confined

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace Faithful

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- A member of an `\or` holds the elements of the sort it holds. -/
theorem tieOr_intro {ctx : KoreAML.Ctx} {s : KoreAML.P} {e : Valuation M} {m : M} :
    ∀ {ps : List Kore.Pattern} {p : Kore.Pattern}, p ∈ ps → (KoreAML.inhOf s).interpret I e m →
      (KoreAML.tr ctx p).interpret I e m → (KoreAML.trOrList ctx s ps).interpret I e m
  | [], _, hp, _, _ => absurd hp List.not_mem_nil
  | [q], p, hp, _, h => by rw [List.mem_singleton.mp hp] at h; rw [KoreAML.trOrList]; exact h
  | q :: r :: ps, p, hp, hs, h => by
    rw [KoreAML.trOrList, KoreAML.interp_sOr]
    refine ⟨hs, ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl h
    · exact .inr (tieOr_intro hp hs h)

/-- The no-junk disjuncts end with `\bottom`. -/
theorem tieNoJunk_last (N : String) : ∀ (seen : List (String × List String)) (gs : List KoreAML.Gen),
    (KoreAML.noJunkDisjuncts N seen gs).getLast? = some (.bottom (KoreAML.srt N))
  | _, [] => rfl
  | seen, .ctor k :: gs => by
    simp only [KoreAML.noJunkDisjuncts]
    rw [List.getLast?_cons_of_ne_nil (Model.noJunkDisjuncts_ne_nil N _ gs)]
    exact tieNoJunk_last N _ gs
  | seen, .inj a :: gs => by
    simp only [KoreAML.noJunkDisjuncts]
    rw [List.getLast?_cons_of_ne_nil (Model.noJunkDisjuncts_ne_nil N _ gs)]
    exact tieNoJunk_last N _ gs

omit [Inhabited M] in
/-- An `\or` whose last operand is `\bottom{S}` holds elements of S only. -/
theorem tieOr_inh {ctx : KoreAML.Ctx} {S : Kore.KSort} {e : Valuation M} {m : M} :
    ∀ {ps : List Kore.Pattern}, ps.getLast? = some (.bottom S) →
      (KoreAML.trOrList ctx (KoreAML.trSort ctx.vars S) ps).interpret I e m →
      (KoreAML.inhOf (KoreAML.trSort ctx.vars S)).interpret I e m
  | [], h, _ => by cases h
  | [q], h, hm => by
    have hq : q = .bottom S := by simpa using h
    subst hq
    rw [KoreAML.trOrList, KoreAML.tr] at hm
    unfold KoreAML.sBot at hm
    rw [KoreAML.interp_sNot] at hm
    exact hm.2
  | q :: r :: ps, _, hm => by
    rw [KoreAML.trOrList, KoreAML.interp_sOr] at hm
    exact hm.1

/-- Under the binders of `existsAll`, upwards: where the body holds at every valuation that gives
the binders the elements `xs` of their sorts and agrees with `e` elsewhere, the quantified pattern
holds at `e`. -/
theorem tieExistsAll_intro (hD : KoreAML.DefOK I) {tbl : KoreAML.VarTable} {S : Kore.KSort} {body : Kore.Pattern} {m : M} :
    ∀ (bs : List Kore.EVar) (ss : List String) (xs : List M) (e : Valuation M),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    bs.map (·.sort) = ss.map KoreAML.srt → All2 (fun s x => InS I s x) ss xs →
    (∀ e' : Valuation M, e'.evalSvar = e.evalSvar →
      (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e'.evalEvar x = e.evalEvar x) →
      All2 (fun (b : Kore.EVar) x => e'.evalEvar (tbl.ev (KoreAML.evarKey b)) = x) bs xs →
      (KoreAML.tr ⟨tbl, []⟩ body).interpret I e' m) →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)).interpret I e m
  | [], [], _, e, _, _, hx, h => by
    cases hx
    exact h e rfl (fun _ _ => rfl) .nil
  | [], _ :: _, _, _, _, hs, _, _ => by simp at hs
  | _ :: _, [], _, _, _, hs, _, _ => by simp at hs
  | b :: bs, s :: ss, xs, e, hnd, hs, hx, h => by
    cases hx with
    | @cons _ x _ xs hx hxs =>
    simp only [List.map_cons, List.cons.injEq] at hs
    rw [List.map_cons, List.nodup_cons] at hnd
    show (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret I e m
    rw [KoreAML.tr, KoreAML.interp_sExists]
    refine ⟨x, ?_, ?_⟩
    · rw [KoreAML.interp_member hD]
      simp only [Function.update_same]
      rw [hs.1, trSort_srt]
      exact (inS_iff _).mpr hx
    · refine tieExistsAll_intro hD bs ss xs _ hnd.2 hs.2 hxs fun e' hsv hout hall => ?_
      refine h e' hsv (fun y hy => ?_) (.cons ?_ hall)
      · rw [hout y fun b' hb' => hy b' (List.mem_cons_of_mem _ hb')]
        exact Function.update_noteq (hy b (List.mem_cons_self ..)) _ _
      · rw [hout _ fun b' hb' heq => hnd.1 (List.mem_map.mpr ⟨b', hb', heq.symm⟩)]
        exact Function.update_same _ _ _

omit [Inhabited M] in
/-- Variables that hold the elements `xs` denote them. -/
theorem tieAll2_evars {tbl : KoreAML.VarTable} {e : Valuation M} : ∀ {bs : List Kore.EVar} {xs : List M},
    All2 (fun (b : Kore.EVar) x => e.evalEvar (tbl.ev (KoreAML.evarKey b)) = x) bs xs →
    All2 (fun (φ : KoreAML.P) x => φ.interpret I e x) (bs.map fun b => .evar (tbl.ev (KoreAML.evarKey b))) xs
  | _, _, .nil => .nil
  | _, _, .cons hb hs => .cons (by rw [KoreAML.interp_evar]; exact hb.symm) (tieAll2_evars hs)

/-- **The no-junk sentence over more generators is a consequence.** In a model of definedness, the
no-junk item of the sort N over the generators `gs` entails the one over any list `gs'` that holds
each generator of `gs`: every element of N is a generator of `gs` applied to elements of its
argument sorts, so a generator of `gs'`. For two lists with the same generators it gives the
sentence with its disjuncts in the other list's order. -/
theorem noJunkItem_of_subset (hD : KoreAML.DefOK I) {N : String} {gs gs' : List KoreAML.Gen}
    (hsub : ∀ g ∈ gs, g ∈ gs') (h : I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs).pat) :
    I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs').pat := by
  let X := Kore.Pattern.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs')
  let t := KoreAML.tableOf [] X
  have hfree : KoreAML.freeOf [] X = [] := by
    show KoreAML.freeOf [] (.or _ _) = []
    rw [KoreAML.freeOf]
    exact freeOfList_nil fun p hp => by
      rcases noJunkDisjuncts_cases N [] gs' p hp with rfl | ⟨g, -, bs, body, rfl, -, -, hb, -⟩
      · rw [KoreAML.freeOf]
      · exact nj_freeOf_existsAll bs [] fun B _ hB => hb B hB
  intro e m
  show (KoreAML.conjList ((([] : List KoreAML.VarKey) ++ KoreAML.freeOf [] X).eraseDups.map (KoreAML.guardOf t)) ⇒
    (KoreAML.tr ⟨t, []⟩ X ≡ KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N)))).interpret I e m
  rw [interpret_impl]
  intro _
  rw [KoreAML.interp_equal hD]
  intro a
  show (KoreAML.tr ⟨t, []⟩ (.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs'))).interpret I e a ↔ _
  rw [KoreAML.tr]
  constructor
  · exact tieOr_inh (ctx := ⟨t, []⟩) (tieNoJunk_last N [] gs')
  · intro ha
    have hx : InS I N a := by rw [trSort_srt] at ha; exact (inS_iff _).mp ha
    obtain ⟨g, hg, xs, hxs, a0, ha0, happ⟩ := noJunk_elim hD h hx
    obtain ⟨bs, body, hmem, hsorts, hnd, htr⟩ := Model.noJunkDisjuncts_gen N [] gs' g (hsub g hg)
    have hkt : ∀ b ∈ bs, KoreAML.evarKey b ∈ t := fun b hb => List.mem_eraseDups.mpr (List.mem_append_right _ (by
      show KoreAML.evarKey b ∈ KoreAML.varsOf (.or _ _)
      rw [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOfList hmem (Model.varsOf_existsAll' hb))))
    have hidx : (bs.map fun b => t.ev (KoreAML.evarKey b)).Nodup := by
      rw [show (bs.map fun b => t.ev (KoreAML.evarKey b)) = (bs.map KoreAML.evarKey).map t.ev by rw [List.map_map]; rfl]
      refine Model.nodup_map_of_injOn t.ev (fun k hk k' hk' he => ?_) hnd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hk'
      exact ev_inj (hkt b hb) (hkt b' hb') he
    refine tieOr_intro hmem ha (tieExistsAll_intro hD bs g.argSorts xs e hidx hsorts hxs fun e' _ _ hall => ?_)
    rw [htr t, genPat_eq, interp_appList]
    exact ⟨a0, (genHead_val0 N g e' a0).mpr ha0, xs, tieAll2_evars hall, happ⟩

end

end Faithful

end KCore
