/-
  KCore. Step soundness for the first stage: what every model of `Γ c` says of values (L1),
  patterns (L2), evaluation (L3) and a rule's step (L4).
-/
import KcoreSpec.Faithful
import KcoreSpec.FaithfulTr
import KcoreSpec.MatchComplete

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround)

/-! ## The KORE of a value is ground -/

theorem nil_consts : ∀ s ∈ ([] : List Kore.KSort), ∃ C, s = .ctor C [] := fun _ h => absurd h List.not_mem_nil

theorem mem_one {α : Type} {a x : α} (h : x ∈ [a]) : x = a := by
  rcases List.mem_cons.mp h with h | h
  · exact h
  · exact absurd h List.not_mem_nil

theorem mem_two {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (mem_one h)

mutual
  theorem kore_ground (c : Semantics) : ∀ v : GroundTerm, KGround (GroundTerm.kore c v)
    | .ctor f ts => by
      rw [GroundTerm.kore]
      exact .app nil_consts (koreList_ground c ts)
    | .inj a b t => by
      rw [GroundTerm.kore]
      unfold KoreAML.injP
      refine .app ?_ ?_
      · intro s hs
        rcases mem_two hs with rfl | rfl <;> exact ⟨_, rfl⟩
      · intro p hp
        rw [mem_one hp]
        exact kore_ground c t
    | .dv s lit => by
      rw [GroundTerm.kore]
      exact .dv
    | .map s es => by
      rw [GroundTerm.kore]
      exact koreEntries_ground c _ es
    | .set s es => by
      rw [GroundTerm.kore]
      exact koreElems_ground c _ es
    | .list s es => by
      rw [GroundTerm.kore]
      exact koreElems_ground c _ es
    termination_by structural v => v
  theorem koreList_ground (c : Semantics) : ∀ ts : List GroundTerm, ∀ p ∈ GroundTerm.koreList c ts, KGround p
    | [] => by
      rw [GroundTerm.koreList]
      exact fun _ h => absurd h List.not_mem_nil
    | t :: ts => by
      rw [GroundTerm.koreList]
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact kore_ground c t
      · exact koreList_ground c ts p hp
    termination_by structural ts => ts
  theorem koreEntries_ground (c : Semantics) (k : CollSig) :
      ∀ es : List (GroundTerm × GroundTerm), KGround (GroundTerm.koreEntries c k es)
    | [] => by
      rw [GroundTerm.koreEntries]
      unfold KoreAML.ap
      exact .app nil_consts (fun _ h => absurd h List.not_mem_nil)
    | [e] => by
      rw [GroundTerm.koreEntries]
      exact koreEntry_ground c k e
    | e :: e' :: es => by
      rw [GroundTerm.koreEntries.eq_3 c k e (e' :: es) (List.cons_ne_nil _ _)]
      unfold KoreAML.ap
      refine .app nil_consts ?_
      intro p hp
      rcases mem_two hp with rfl | rfl
      · exact koreEntry_ground c k e
      · exact koreEntries_ground c k (e' :: es)
    termination_by structural es => es
  theorem koreEntry_ground (c : Semantics) (k : CollSig) :
      ∀ e : GroundTerm × GroundTerm, KGround (GroundTerm.koreEntry c k e)
    | (x, v) => by
      rw [GroundTerm.koreEntry]
      unfold KoreAML.ap
      refine .app nil_consts ?_
      intro p hp
      rcases mem_two hp with rfl | rfl
      · exact kore_ground c x
      · exact kore_ground c v
    termination_by structural e => e
  theorem koreElems_ground (c : Semantics) (k : CollSig) :
      ∀ es : List GroundTerm, KGround (GroundTerm.koreElems c k es)
    | [] => by
      rw [GroundTerm.koreElems]
      unfold KoreAML.ap
      exact .app nil_consts (fun _ h => absurd h List.not_mem_nil)
    | [e] => by
      rw [GroundTerm.koreElems]
      unfold KoreAML.ap
      refine .app nil_consts ?_
      intro p hp
      rw [mem_one hp]
      exact kore_ground c e
    | e :: e' :: es => by
      rw [GroundTerm.koreElems.eq_3 c k e (e' :: es) (List.cons_ne_nil _ _)]
      unfold KoreAML.ap
      refine .app nil_consts ?_
      intro p hp
      rcases mem_two hp with rfl | rfl
      · refine .app nil_consts ?_
        intro q hq
        rw [mem_one hq]
        exact kore_ground c e
      · exact koreElems_ground c k (e' :: es)
    termination_by structural es => es
end

/-- The pattern of a value has no free variable. -/
theorem den_closed (c : Semantics) (v : GroundTerm) : Closed (den c v) :=
  (kore_ground c v).closed _

/-! ## Reading `Γ` in a model -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

theorem sat_sig (hI : I ⊧ᴵP Γ c) {φ : KoreAML.P} (h : ΓSig c φ) : I ⊧ᴵ φ :=
  hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
theorem sat_cons (hI : I ⊧ᴵP Γ c) {φ : KoreAML.P} (h : ΓCons c φ) : I ⊧ᴵ φ :=
  hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
theorem sat_dom (hI : I ⊧ᴵP Γ c) {φ : KoreAML.P} (h : ΓDomains c φ) : I ⊧ᴵ φ :=
  hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
theorem sat_colls (hI : I ⊧ᴵP Γ c) : I ⊧ᴵP ΓColls c :=
  fun φ h => hI φ (Or.inl (Or.inl (Or.inl (Or.inr h))))
theorem sat_fns (hI : I ⊧ᴵP Γ c) {φ : KoreAML.P} (h : ΓFns c φ) : I ⊧ᴵ φ :=
  hI φ (Or.inl (Or.inl (Or.inr h)))
theorem sat_rules (hI : I ⊧ᴵP Γ c) {φ : KoreAML.P} (h : ΓRules c φ) : I ⊧ᴵ φ :=
  hI φ (Or.inl (Or.inr h))
theorem sat_fb (hI : I ⊧ᴵP Γ c) {φ : KoreAML.P} (h : ΓFallback c φ) : I ⊧ᴵ φ :=
  hI φ (Or.inr h)

/-- An interpreted symbol's result (`hookRes`) at values of its argument sorts: its graph, from
`ΓDomains` off the silent points and from `ΓFallback` at them. -/
theorem sat_hookRes (hI : I ⊧ᴵP Γ c) {k : CtorSig} {vs : List GroundTerm} {r : Option GroundTerm}
    (hk : k ∈ hookSigs) (hvs : c.sortsOf vs = some k.args) (hr : c.hookRes k.name vs = some r) :
    I ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match (generalizing := false) r with
      | some v => den c v
      | none => ⊥)) := by
  rcases Semantics.hookRes_cases hr with ⟨hh, hs⟩ | ⟨hh, hs, rfl⟩
  · exact sat_dom hI (Or.inl ⟨k, vs, r, hk, hvs, hh, hs, rfl⟩)
  · exact sat_fb hI (Or.inl ⟨k, vs, hk, hvs, hh, hs, rfl⟩)

/-- A function's rest at values of its argument sorts where every clause fails: its graph, from
`ΓFallback`. -/
theorem sat_rest (hI : I ⊧ᴵP Γ c) {fn : Fn} {vs : List GroundTerm} (hfn : fn ∈ c.allFns)
    (hvs : c.sortsOf vs = some fn.args) (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) :
    I ⊧ᴵ (KoreAML.den (symApp c fn.label (GroundTerm.koreList c vs)) ≡ (match c.fnRest fn vs with
      | some v => den c v
      | none => ⊥)) :=
  sat_fb hI (Or.inr ⟨fn, vs, hfn, hvs, hnone, rfl⟩)

/-- A model of `Γ` interprets `⌈_⌉` as definedness. -/
theorem defOK (hI : I ⊧ᴵP Γ c) : DefOK I :=
  KoreAML.defOK_of fun x => sat_sig hI (Or.inl (Or.inr ⟨x, rfl⟩))

theorem sat_sigItem (hI : I ⊧ᴵP Γ c) {it : KoreAML.Item} (h : it ∈ sigItems c) : I ⊧ᴵ it.pat :=
  sat_sig hI (Or.inl (Or.inl ⟨it, h, rfl⟩))

/-! ## L1. Values are elements -/

/-- **L1.** In a model of `Γ`, a value of sort `s` denotes one element, and that element is in
the sort `s`. -/
theorem den_single [Inhabited M] (hI : I ⊧ᴵP Γ c) {v : GroundTerm} {s : Srt} (h : c.sortOf v = some s)
    (e : Valuation M) :
    ∃ a, (∀ m, (den c v).interpret I e m ↔ m = a) ∧ (KoreAML.inhOf (sortP (c.sortName s))).interpret I e a := by
  have hD := defOK hI
  have hax := sat_dom hI (Or.inr (Or.inr (Or.inl ⟨v, s, h, rfl⟩))) e default
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

end

/-! ## The first stage's restrictions and the names it reads -/

mutual
  /-- A pattern of constructors, injections, aliases, variables and domain values only: no map or
  collection pattern symbol. -/
  def plainPat (c : Semantics) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .app f ts => c.isCtor f && !patternHooks.contains f && plainPats c ts
    | .inj _ _ t => plainPat c t
    | .as t _ => plainPat c t
    termination_by structural t => t
  def plainPats (c : Semantics) : List Term → Bool
    | [] => true
    | t :: ts => plainPat c t && plainPats c ts
    termination_by structural ts => ts
end

/-- The valuation `e` gives each variable `i` of `vs` that σ binds the element its value denotes,
at the index the table `t` gives the variable's key. -/
def Agrees {M : Type} (c : Semantics) (I : Interpretation KoreAML.Sym M) (t : KoreAML.VarTable)
    (vs : List KoreAML.Var) (σ : Subst) (e : Valuation M) : Prop :=
  ∀ i v, i < vs.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (t.ev (KoreAML.evarKey (vs.getD i default).kore)) ↔ (den c v).interpret I e m

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

theorem sym_congr {e e' : Valuation M} (σ : KoreAML.Sym) (m : M) :
    (KoreAML.sym σ).interpret I e m ↔ (KoreAML.sym σ).interpret I e' m := Iff.rfl

/-- `inj{A,B}(φ)` depends only on the set `φ` denotes. -/
theorem injApp_congr {e e' : Valuation M} {A B : String} {φ φ' : KoreAML.P}
    (h : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ]).interpret I e m ↔
      (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ']).interpret I e' m := by
  simp only [KoreAML.appList]
  exact KoreAML.interp_app_congr (KoreAML.interp_app_congr (KoreAML.interp_app_congr
    (sym_congr (e := e) (e' := e') _) (sym_congr (e := e) (e' := e') _)) (sym_congr (e := e) (e' := e') _)) h m

theorem coh_mem {a' a b : Srt} (h1 : (a', a) ∈ c.subsorts) (h2 : (a, b) ∈ c.subsorts) :
    KoreAML.Cons.cohItem (c.sortName a') (c.sortName a) (c.sortName b) ∈ consItemsK c := by
  unfold consItemsK
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(a', a), h1, ?_⟩)))
  exact List.mem_map.mpr ⟨(a, b), List.mem_filter.mpr ⟨h2, beq_iff_eq.mpr rfl⟩, rfl⟩

/-- Coherence of injections in a model of `Γ`: `inj{A,B}(inj{A',A}(x)) = inj{A',B}(x)` for an
element `x` of `A'`, along a chain `A' < A < B` of subsorts. -/
theorem coh_at [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] {a' a b : Srt} (h1 : (a', a) ∈ c.subsorts) (h2 : (a, b) ∈ c.subsorts)
    {e : Valuation M} {X : KoreAML.P} {x : M} (hX : ∀ m, X.interpret I e m ↔ m = x)
    (hx : (KoreAML.inhOf (sortP (c.sortName a'))).interpret I e x) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b),
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a'), KoreAML.Cons.sortP (c.sortName a), X]]).interpret I e m ↔
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a'), KoreAML.Cons.sortP (c.sortName b), X]).interpret I e m := by
  have hD := defOK hI
  have hax := sat_cons hI (Or.inl ⟨_, coh_mem h1 h2, rfl⟩)
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

theorem injNormal_cases (a b : Srt) (w : GroundTerm) :
    (∃ a' a'' w', w = .inj a' a'' w' ∧ injNormal a b w = .inj a' b w') ∨ injNormal a b w = .inj a b w := by
  cases w with
  | inj a' a'' w' => exact Or.inl ⟨a', a'', w', rfl, rfl⟩
  | ctor _ _ => exact Or.inr rfl
  | dv _ _ => exact Or.inr rfl
  | map _ _ => exact Or.inr rfl
  | set _ _ => exact Or.inr rfl
  | list _ _ => exact Or.inr rfl

theorem den_inj (x y : Srt) (w : GroundTerm) :
    den c (.inj x y w) = KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName x), KoreAML.Cons.sortP (c.sortName y), den c w] := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, KoreAML.tr_injP]

theorem den_ctor (f : Sym) (ws : List GroundTerm) :
    den c (.ctor f ws) = KoreAML.trArgs ⟨[], []⟩ (KoreAML.sym (.symbol (c.symName f))) (GroundTerm.koreList c ws) := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, KoreAML.tr_app0]

theorem lookup_patCtxAll {f : Sym} {k k0 : CtorSig} (h0 : lookupSig c.ctorSigs f = some k0)
    (h : lookupSig c.patCtxAll.heads f = some k) : k = k0 := by
  have : lookupSig c.patCtxAll.heads f = some k0 := by
    simp only [Semantics.patCtxAll, Semantics.patCtx]
    exact lookupSig_append_some (lookupSig_append_some h0)
  rw [h] at this; exact Option.some.inj this

/-- Under `NamesPlain`, `symApp` writes a constructor at its name, at no sort. -/
theorem ctor_writes_irs (hnm : NamesPlain c) {f : Sym} {k0 : CtorSig} (h0 : lookupSig c.ctorSigs f = some k0) :
    ∀ ps, symApp c f ps = .app ⟨⟨c.symName f⟩⟩ [] ps := by
  rw [lookupSig_eq] at h0
  have hmem := List.mem_of_find?_eq_some h0
  have h1 := List.find?_some h0
  have hname : k0.name = f := beq_iff_eq.mp h1
  rw [← hname]; exact namesPlain_writes_irs hnm hmem

theorem tr_var {vs : List KoreAML.Var} {t : KoreAML.VarTable} {e : Valuation M} (i : Nat) (m : M) :
    (KoreAML.tr ⟨t, []⟩ (Term.kore c vs (.var i))).interpret I e m ↔
      m = e.evalEvar (t.ev (KoreAML.evarKey (vs.getD i default).kore)) := by
  rw [Term.kore]; unfold KoreAML.varAt; rw [KoreAML.tr]; exact Iff.rfl

variable [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnm : NamesPlain c)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  {σ : Subst} {vars : List Srt} {vs : List KoreAML.Var} {t : KoreAML.VarTable} {e : Valuation M}
  (hσ : c.WellSorted vars σ) (hvs : vs.length = vars.length) (hag : Agrees c I t vs σ e)
include hI hnm htr hσ hvs hag

mutual
  /-- **L2.** A plain, well-sorted pattern that denotes `v` under a well-sorted σ translates, at a
  valuation that agrees with σ, to the element `v` denotes; and `v` has the pattern's sort. -/
  theorem patVal_den : ∀ {p : Term} {v : GroundTerm} {s : Srt}, PatVal c σ p v → plainPat c p = true →
      sortOfTerm c.patCtxAll vars p = some s →
      c.sortOf v = some s ∧ ∀ m, (KoreAML.tr ⟨t, []⟩ (Term.kore c vs p)).interpret I e m ↔ (den c v).interpret I e m
    | _, _, s, .var (i := i) (v := v) hl, _, ht => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hi).1
      refine ⟨?_, fun m => ?_⟩
      · obtain ⟨w, hw, hsw⟩ := hσ i s hi
        rw [hl] at hw; cases hw; exact hsw
      · rw [tr_var]
        exact hag i v hlt hl m
    | _, _, s, .dv (s := s') (lit := lit), _, ht => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      refine ⟨sortOf_dv.mpr ⟨hok, rfl⟩, fun m => ?_⟩
      rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | _, _, s, .ctor (f := f) (ps := ps) (vs := ws) hk hs, hp, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hk
      have hkk := lookup_patCtxAll hk0 hk'
      subst hkk
      rw [plainPat] at hp
      simp only [Bool.and_eq_true] at hp
      have ih := patVals_den hs hp.2 hargs
      refine ⟨sortOf_ctor_intro ⟨k, hk0, ih.1, rfl⟩, fun m => ?_⟩
      rw [kore_app, ctor_writes_irs hnm hk0]
      rw [KoreAML.tr_app0, den_ctor]
      exact ih.2 _ _ (fun _ => Iff.rfl) m
    | _, _, s, .hook hp _ _, hpl, _ => by
      rw [plainPat] at hpl
      simp only [hp, Bool.not_true, Bool.and_false, Bool.false_and] at hpl
      cases hpl
    | _, _, s, .coll hc _ _ _, hpl, _ => by
      rw [plainPat, hc] at hpl
      simp only [Bool.false_and] at hpl
      cases hpl
    | _, _, s, .ovl hc _ _ _, hpl, _ => by
      rw [plainPat, hc] at hpl
      simp only [Bool.false_and] at hpl
      cases hpl
    | _, _, s, .inj (a := a) (b := b) (p := p) (w := w) h, hpl, ht => by
      obtain ⟨hab, ht', hsb⟩ := sortOfTerm_inj.mp ht
      rw [hsb]
      rw [plainPat] at hpl
      have ih := patVal_den h hpl ht'
      refine ⟨sortOf_injNormal htr hab ih.1, fun m => ?_⟩
      rw [Term.kore, KoreAML.tr_injP]
      rcases injNormal_cases a b w with ⟨a', a'', w', rfl, hn⟩ | hn
      · rw [hn]
        obtain ⟨h1, -, h3, rfl⟩ := sortOf_inj.mp ih.1
        obtain ⟨x, hx, hxs⟩ := den_single hI h3 e
        rw [injApp_congr ih.2 m, den_inj, den_inj]
        exact coh_at hI h1 hab hx hxs m
      · rw [hn, den_inj]
        exact injApp_congr ih.2 m
    | _, _, s, .as (p := p) (i := i) (v := v) h hi, hpl, ht => by
      obtain ⟨hvi, ht'⟩ := Exec.sortOfTerm_as ht
      rw [plainPat] at hpl
      have ih := patVal_den h hpl ht'
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hvi).1
      refine ⟨ih.1, fun m => ?_⟩
      rw [Term.kore, KoreAML.tr]
      simp only [KoreAML.trAndList]
      rw [KoreAML.interp_sAnd, ih.2 m]
      have hv := tr_var (c := c) (I := I) (vs := vs) (t := t) (e := e) i m
      rw [Term.kore] at hv
      rw [hv, hag i v hlt hi m, and_self]
  theorem patVals_den : ∀ {ps : List Term} {ws : List GroundTerm} {ss : List Srt}, PatVals c σ ps ws →
      plainPats c ps = true → sortsOfTerms c.patCtxAll vars ps = some ss →
      c.sortsOf ws = some ss ∧ ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (KoreAML.trArgs ⟨t, []⟩ acc (Term.koreList c vs ps)).interpret I e m ↔
          (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m
    | _, _, _, .nil, _, ht => by
      rw [sortsOfTerms_nil.mp ht]
      refine ⟨sortsOf_nil, fun acc acc' h m => ?_⟩
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact h m
    | _, _, _, .cons (p := p) (ps := ps) (v := w) (vs := ws) h hs, hp, ht => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [plainPats] at hp
      simp only [Bool.and_eq_true] at hp
      have ih1 := patVal_den h hp.1 h1
      have ih2 := patVals_den hs hp.2 h2
      refine ⟨sortsOf_cons.mpr ⟨s, ss', ih1.1, ih2.1, rfl⟩, fun acc acc' hacc m => ?_⟩
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
      exact ih2.2 _ _ (KoreAML.interp_app_congr hacc ih1.2) m
end

end

end Faithful

end KCore
