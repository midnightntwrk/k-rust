/-
  The extension of a model of the theory without the detached names (`extModel`,
  ConsExtModel.lean) satisfies the premises of the constructors (`ΓCons`) that name nothing of `D`
  (`sat_own_cons`), for names `D` that are sort constants and symbols of the definition and open
  generators whose symbol and result sort are outside `D` (their law sentences, associativity and
  idempotence, are transferred as written: `transfer_assoc`, `transfer_idem`); with
  `sat_own_sig` and `sat_own_colls` (ConsTransferSig.lean) every premise of `ΓSig`, `ΓCons` and
  `ΓColls` that names nothing of `D` (`sat_own_sig_cons`).

  Each item of the constructors is a guarded premise of the class `OwnSorted` (ConsTransfer.lean):
  its guards put the variables `x̄` in sort constants (`memGuards`, which is `memGs` of the pairs of
  `x̄` and their sorts, `memGuards_eq_cs`), and its body is built from equality, definedness and
  sorted quantifiers over a generator applied to the variables (`own_genPat_cs`). The items at
  uncovered arguments carry further guards, `uncoveredP`, which are predicates of the class; a
  premise `ws ++ us → φ` holds in an interpretation exactly when `ws → (us → φ)` does
  (`guarded_append_cs`), so those guards move into the body (`transferGU_cs`).

  The no-junk item is the translation of a closed sentence (`noJunk_free_cs`): its guard list is
  empty, and the translation of `\or{N}(∃x̄. g(x̄), …, \bottom{N}())` has no added element in the
  extension (`own_trNoJunk_cs`).
-/
import KcoreSpec.ConsTransferSig
import KcoreSpec.Confined

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort)

local notation "Own0" => OwnSorted (fun _ => False)

/-! ## Guards -/

theorem memGuards_eq_cs : ∀ (x : List EVar) (ss : List String),
    KoreAML.Cons.memGuards x ss = memGs (x.zip (ss.map KoreAML.Cons.sortP))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: x, s :: ss => by
    show (a ∈∈ KoreAML.inhOf (KoreAML.Cons.sortP s)) :: KoreAML.Cons.memGuards x ss =
      (a ∈∈ KoreAML.inhOf (KoreAML.Cons.sortP s)) :: memGs (x.zip (ss.map KoreAML.Cons.sortP))
    rw [memGuards_eq_cs x ss]

theorem memGuards_append_cs : ∀ {x : List EVar} {ss : List String} (y : List EVar) (ss' : List String),
    x.length = ss.length →
    KoreAML.Cons.memGuards x ss ++ KoreAML.Cons.memGuards y ss' = KoreAML.Cons.memGuards (x ++ y) (ss ++ ss')
  | x, ss, y, ss', h => by
    unfold KoreAML.Cons.memGuards
    rw [List.zip_append h, List.map_append]

theorem fst_zip_cs {x : List EVar} {ss : List String} (h : x.length ≤ ss.length) :
    (x.zip (ss.map KoreAML.Cons.sortP)).map (·.1) = x :=
  List.map_fst_zip (by rw [List.length_map]; exact h)

theorem sortGuards_cs (x : List EVar) (ss : List String) :
    ∀ p ∈ x.zip (ss.map KoreAML.Cons.sortP), Own0 [] [] .ex p.2 := fun p hp => by
  obtain ⟨s, -, hs⟩ := List.mem_map.mp (List.of_mem_zip hp).2
  rw [← hs]
  exact .sortC id

/-- A premise `ws ++ us → φ` holds exactly when `ws → (us → φ)` does. -/
theorem guarded_append_cs {N : Type} {J : Interpretation KoreAML.Sym N} {ws us : List KoreAML.P} {φ : KoreAML.P} :
    (J ⊧ᴵ KoreAML.guarded (ws ++ us) φ) ↔ (J ⊧ᴵ KoreAML.guarded ws (KoreAML.guarded us φ)) := by
  constructor
  · intro h e m
    rw [guarded_iff, guarded_iff]
    intro hw hu
    exact guarded_iff.mp (h e m) fun w hw' => (List.mem_append.mp hw').elim (hw w) (hu w)
  · intro h e m
    rw [guarded_iff]
    intro hw
    exact guarded_iff.mp (guarded_iff.mp (h e m) fun w h' => hw w (List.mem_append_left _ h'))
      fun w h' => hw w (List.mem_append_right _ h')

theorem psyms_guarded_mem_cs {ws : List KoreAML.P} {w φ : KoreAML.P} {σ : KoreAML.Sym} (hw : w ∈ ws)
    (hσ : σ ∈ psyms w) : σ ∈ psyms (KoreAML.guarded ws φ) := by
  have h2 := psyms_conjList_sg hw hσ
  cases ws with
  | nil => exact absurd hw List.not_mem_nil
  | cons w0 ws =>
    show σ ∈ psyms (KoreAML.conjList (w0 :: ws) ⇒ φ)
    simp [psyms, h2]

theorem psyms_member_cs {x : EVar} {s : KoreAML.P} {σ : KoreAML.Sym} (h : σ ∈ psyms s) :
    σ ∈ psyms (x ∈∈ KoreAML.inhOf s) := by
  simp [ML.member, psyms, KoreAML.inhOf, KoreAML.sym, Pattern.conjunction, Pattern.disjunction,
    Pattern.negation, h]

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- `transfer` for a premise whose guards are memberships in sorts of the class followed by
predicates of the class: the predicates move into the body. -/
theorem transferGU_cs (hDI : DefOK I) {gs : List (EVar × KoreAML.P)} {us : List KoreAML.P} {body : KoreAML.P}
    {k : OwnKind} (hs : ∀ p ∈ gs, Own0 [] [] .ex p.2) (hu : ∀ u ∈ us, Own0 (gs.map (·.1)) [] .pred u)
    (hb : Own0 (gs.map (·.1)) [] k body) (hk : k = .pred ∨ k = .co)
    (hn : ∀ σ ∈ psyms (KoreAML.guarded (memGs gs ++ us) body), ¬ D σ)
    (h : I ⊧ᴵ KoreAML.guarded (memGs gs ++ us) body) :
    extModel c D I ⊧ᴵ KoreAML.guarded (memGs gs ++ us) body := by
  have hn1 : ∀ w ∈ memGs gs ++ us, ∀ σ ∈ psyms w, ¬ D σ := fun w hw σ hσ => hn σ (psyms_guarded_mem_cs hw hσ)
  have hs' : ∀ p ∈ gs, OwnSorted D [] [] .ex p.2 := fun p hp => ownSorted_clean_sg (hs p hp) fun σ hσ =>
    hn1 _ (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)) σ (psyms_member_cs hσ)
  have hu' : ∀ u ∈ us, OwnSorted D (gs.map (·.1)) [] .pred u := fun u hu0 =>
    ownSorted_clean_sg (hu u hu0) (hn1 u (List.mem_append_right _ hu0))
  have hb' := ownSorted_clean_sg hb fun σ hσ => hn σ (psyms_guarded_body_sg hσ)
  rw [guarded_append_cs] at h ⊢
  exact transfer hD hDI hs' (.guarded hu' hk hb') hk h

/-- `transfer` for a premise guarded by `memGuards x̄ s̄` and then predicates of the class. -/
theorem transferMU_cs (hDI : DefOK I) {x : List EVar} {ss : List String} (hl : x.length ≤ ss.length)
    {us : List KoreAML.P} {body : KoreAML.P} {k : OwnKind}
    (hu : ∀ u ∈ us, Own0 x [] .pred u) (hb : Own0 x [] k body) (hk : k = .pred ∨ k = .co)
    (hn : ∀ σ ∈ psyms (KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ us) body), ¬ D σ)
    (h : I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ us) body) :
    extModel c D I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ us) body := by
  rw [memGuards_eq_cs] at hn h ⊢
  exact transferGU_cs hD hDI (sortGuards_cs x ss) (by rw [fst_zip_cs hl]; exact hu)
    (by rw [fst_zip_cs hl]; exact hb) hk hn h

/-- `transfer` for a premise guarded by `memGuards x̄ s̄`. -/
theorem transferM_cs (hDI : DefOK I) {x : List EVar} {ss : List String} (hl : x.length ≤ ss.length)
    {body : KoreAML.P} {k : OwnKind} (hb : Own0 x [] k body) (hk : k = .pred ∨ k = .co)
    (hn : ∀ σ ∈ psyms (KoreAML.guarded (KoreAML.Cons.memGuards x ss) body), ¬ D σ)
    (h : I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss) body) :
    extModel c D I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss) body := by
  rw [memGuards_eq_cs] at hn h ⊢
  exact transferG_sg hD hDI (sortGuards_cs x ss) (by rw [fst_zip_cs hl]; exact hb) hk hn h

end

/-! ## The bodies of the constructors' items are of the class -/

section
variable {V : List EVar} {W : List SVar}

theorem disjList_pred_cs : ∀ {ws : List KoreAML.P}, (∀ w ∈ ws, Own0 V W .pred w) →
    Own0 V W .pred (KoreAML.disjList ws)
  | [], _ => .botP
  | [w], h => h w (List.mem_cons_self ..)
  | w :: w' :: ws, h => .disj_pred (h w (List.mem_cons_self ..))
      (disjList_pred_cs (ws := w' :: ws) fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem own_evars_cs {x : List EVar} (hx : ∀ a ∈ x, a ∈ V) :
    ∀ a ∈ x.map (Pattern.evar : EVar → KoreAML.P), Own0 V W .old a := fun a ha => by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact (OwnSorted.evar (hx b hb)).toOld

/-- A generator applied to arguments of the class. -/
theorem own_genPat_cs (N : String) (g : KoreAML.Gen) {args : List KoreAML.P}
    (h : ∀ a ∈ args, Own0 V W .old a) : Own0 V W .ex (KoreAML.Cons.genPat N g args) := by
  cases g with
  | ctor k => exact .appList (.symC id) h
  | inj A =>
    refine .appList (.symC id) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> exact (OwnSorted.sortC id).toOld
    · exact h a ha

theorem own_inj_cs (A B : String) {φ : KoreAML.P} (h : Own0 V W .old φ) :
    Own0 V W .ex (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ]) :=
  .appList (.symC id) fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact (OwnSorted.sortC id).toOld
    · exact (OwnSorted.sortC id).toOld
    · exact h

theorem own_liftP_cs (A B : String) {φ : KoreAML.P} (h : Own0 V W .ex φ) :
    Own0 V W .ex (if (A == B) = true then φ else
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ]) := by
  split
  · exact h
  · exact own_inj_cs A B h.toOld

theorem sub_cons_cs {x : List EVar} {y : EVar} : ∀ a ∈ x, a ∈ y :: x := fun _ h => List.mem_cons_of_mem _ h

/-- `x ∈ A` for `x` of sort `B`, at the variable `z`: `∃z:A. x = inj{A,B}(z)`. -/
theorem own_liesP_cs (A B : String) {xi z : EVar} (hx : xi ∈ V) :
    Own0 V W .pred (KoreAML.Cons.liesP A B (.evar xi) z) :=
  .sEx (V' := []) (.sortC id) nil_sub (.inr (.inl rfl))
    (.equal_ex (.evar (List.mem_cons_of_mem _ hx)) (own_inj_cs A B (OwnSorted.evar (List.mem_cons_self ..)).toOld))

/-- The arguments are covered by no overload. -/
theorem own_uncovered_cs (bs : List String) (covs : List (List String)) {x : List EVar} (z : EVar)
    (hx : ∀ a ∈ x, a ∈ V) : Own0 V W .pred (KoreAML.Cons.uncoveredP bs covs x z) := by
  unfold KoreAML.Cons.uncoveredP
  refine OwnSorted.conjList_pred fun w hw => ?_
  obtain ⟨as, -, rfl⟩ := List.mem_map.mp hw
  refine disjList_pred_cs fun d hd => ?_
  obtain ⟨⟨⟨A, B⟩, xi⟩, hm, hd⟩ := List.mem_filterMap.mp hd
  have hxi : xi ∈ x := (List.of_mem_zip hm).2
  dsimp only at hd
  split at hd
  · cases hd
  · cases hd
    exact .neg_pred (own_liesP_cs A B (hx xi hxi))

/-- The guards at uncovered arguments of a generator that is an overloading symbol (`some`), none
for another (`none`). -/
theorem own_uncOpt_cs (ug : Option (List (List String))) (bs : List String) {x : List EVar} (z : EVar)
    (hx : ∀ a ∈ x, a ∈ V) : ∀ u ∈ (match ug with
      | some covs => [KoreAML.Cons.uncoveredP bs covs x z]
      | none => []), Own0 V W .pred u := by
  intro u hu
  cases ug with
  | none => exact absurd hu List.not_mem_nil
  | some covs =>
    rw [List.mem_singleton.mp hu]
    exact own_uncovered_cs bs covs z hx

end

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- `transfer` for a premise guarded by `memGuards x̄ s̄ ++ memGuards ȳ s̄'`. -/
theorem transferM2_cs (hDI : DefOK I) {x y : List EVar} {ss ss' : List String} (hl : x.length = ss.length)
    (hl' : y.length ≤ ss'.length) {body : KoreAML.P} {k : OwnKind} (hb : Own0 (x ++ y) [] k body)
    (hk : k = .pred ∨ k = .co)
    (hn : ∀ σ ∈ psyms (KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ KoreAML.Cons.memGuards y ss') body), ¬ D σ)
    (h : I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ KoreAML.Cons.memGuards y ss') body) :
    extModel c D I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ KoreAML.Cons.memGuards y ss') body := by
  rw [memGuards_append_cs y ss' hl] at hn h ⊢
  exact transferM_cs hD hDI (by rw [List.length_append, List.length_append, hl]; omega) hb hk hn h

/-- `transfer` for a premise guarded by `memGuards x̄ s̄ ++ memGuards ȳ s̄'` and then predicates of
the class. -/
theorem transferM2U_cs (hDI : DefOK I) {x y : List EVar} {ss ss' : List String} (hl : x.length = ss.length)
    (hl' : y.length ≤ ss'.length) {us : List KoreAML.P} {body : KoreAML.P} {k : OwnKind}
    (hu : ∀ u ∈ us, Own0 (x ++ y) [] .pred u) (hb : Own0 (x ++ y) [] k body) (hk : k = .pred ∨ k = .co)
    (hn : ∀ σ ∈ psyms (KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ KoreAML.Cons.memGuards y ss' ++ us) body), ¬ D σ)
    (h : I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ KoreAML.Cons.memGuards y ss' ++ us) body) :
    extModel c D I ⊧ᴵ KoreAML.guarded (KoreAML.Cons.memGuards x ss ++ KoreAML.Cons.memGuards y ss' ++ us) body := by
  rw [memGuards_append_cs y ss' hl] at hn h ⊢
  exact transferMU_cs hD hDI (by rw [List.length_append, List.length_append, hl]; omega) hu hb hk hn h

/-! ## Each item of the constructors -/

theorem sat_fun_cs (hDI : DefOK I) (N : String) (g : KoreAML.Gen)
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.funItem N g).pat, ¬ D σ) (h : I ⊧ᴵ (KoreAML.Cons.funItem N g).pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.funItem N g).pat :=
  transferM_cs hD hDI (x := KoreAML.Cons.xs 0 g.argSorts.length) (ss := g.argSorts) (Nat.le_of_eq (xs_length ..))
    (.sEx (V' := []) (.sortC id) nil_sub (.inr (.inl rfl))
      (.equal_ex (own_genPat_cs N g (own_evars_cs sub_cons_cs)) (.evar (List.mem_cons_self ..)))) (.inl rfl) hn h

theorem sat_funUnc_cs (hDI : DefOK I) (N : String) (g : KoreAML.Gen) (covs : List (List String))
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.funUncItem N g covs).pat, ¬ D σ)
    (h : I ⊧ᴵ (KoreAML.Cons.funUncItem N g covs).pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.funUncItem N g covs).pat :=
  transferMU_cs hD hDI (x := KoreAML.Cons.xs 0 g.argSorts.length) (ss := g.argSorts)
    (us := [KoreAML.Cons.uncoveredP g.argSorts covs (KoreAML.Cons.xs 0 g.argSorts.length) ⟨g.argSorts.length + 2⟩])
    (Nat.le_of_eq (xs_length ..))
    (fun u hu => by rw [List.mem_singleton.mp hu]; exact own_uncovered_cs _ _ _ fun _ h => h)
    (.sEx (V' := []) (.sortC id) nil_sub (.inr (.inl rfl))
      (.equal_ex (own_genPat_cs N g (own_evars_cs sub_cons_cs)) (.evar (List.mem_cons_self ..)))) (.inl rfl) hn h

omit hD in
theorem own_injBody_cs (N : String) (g : KoreAML.Gen) (x y : List EVar) :
    Own0 (x ++ y) [] .pred ((KoreAML.Cons.genPat N g (x.map .evar) ≡ KoreAML.Cons.genPat N g (y.map .evar)) ⇒
      KoreAML.conjList ((x.zip y).map fun (a, b) => .evar a ≡ .evar b)) :=
  .impPP (.equal_ex (own_genPat_cs N g (own_evars_cs fun _ h => List.mem_append_left _ h))
      (own_genPat_cs N g (own_evars_cs fun _ h => List.mem_append_right _ h)))
    (.conjList_pred fun w hw => by
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hw
      exact .equal_ex (.evar (List.mem_append_left _ (List.of_mem_zip hab).1))
        (.evar (List.mem_append_right _ (List.of_mem_zip hab).2)))

theorem sat_inj_cs (hDI : DefOK I) (N : String) (g : KoreAML.Gen)
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.injItem N g).pat, ¬ D σ) (h : I ⊧ᴵ (KoreAML.Cons.injItem N g).pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.injItem N g).pat :=
  transferM2_cs hD hDI (x := KoreAML.Cons.xs 0 g.argSorts.length) (y := KoreAML.Cons.xs g.argSorts.length g.argSorts.length)
    (ss := g.argSorts) (ss' := g.argSorts) (xs_length ..) (Nat.le_of_eq (xs_length ..))
    (own_injBody_cs N g _ _) (.inl rfl) hn h

theorem sat_injUnc_cs (hDI : DefOK I) (N : String) (g : KoreAML.Gen) (covs : List (List String))
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.injUncItem N g covs).pat, ¬ D σ)
    (h : I ⊧ᴵ (KoreAML.Cons.injUncItem N g covs).pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.injUncItem N g covs).pat :=
  transferM2U_cs hD hDI (x := KoreAML.Cons.xs 0 g.argSorts.length) (y := KoreAML.Cons.xs g.argSorts.length g.argSorts.length)
    (ss := g.argSorts) (ss' := g.argSorts)
    (us := [KoreAML.Cons.uncoveredP g.argSorts covs (KoreAML.Cons.xs 0 g.argSorts.length) ⟨2 * g.argSorts.length + 1⟩,
      KoreAML.Cons.uncoveredP g.argSorts covs (KoreAML.Cons.xs g.argSorts.length g.argSorts.length)
        ⟨2 * g.argSorts.length + 1⟩])
    (xs_length ..) (Nat.le_of_eq (xs_length ..))
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact own_uncovered_cs _ _ _ fun _ h => List.mem_append_left _ h
      · exact own_uncovered_cs _ _ _ fun _ h => List.mem_append_right _ h)
    (own_injBody_cs N g _ _) (.inl rfl) hn h

omit hD in
theorem own_distBody_cs (N : String) (g g' : KoreAML.Gen) (x y : List EVar) :
    Own0 (x ++ y) [] .pred (KoreAML.notEqual (KoreAML.Cons.genPat N g (x.map .evar))
      (KoreAML.Cons.genPat N g' (y.map .evar))) :=
  .notEqual_ex (own_genPat_cs N g (own_evars_cs fun _ h => List.mem_append_left _ h))
    (own_genPat_cs N g' (own_evars_cs fun _ h => List.mem_append_right _ h))

theorem sat_dist_cs (hDI : DefOK I) (N : String) (g g' : KoreAML.Gen)
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.distItem N g g').pat, ¬ D σ) (h : I ⊧ᴵ (KoreAML.Cons.distItem N g g').pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.distItem N g g').pat :=
  transferM2_cs hD hDI (x := KoreAML.Cons.xs 0 g.argSorts.length) (y := KoreAML.Cons.xs g.argSorts.length g'.argSorts.length)
    (ss := g.argSorts) (ss' := g'.argSorts) (xs_length ..) (Nat.le_of_eq (xs_length ..))
    (own_distBody_cs N g g' _ _) (.inl rfl) hn h

theorem sat_distUnc_cs (hDI : DefOK I) (N : String) (g g' : KoreAML.Gen) (ug ug' : Option (List (List String)))
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.distUncItem N g g' ug ug').pat, ¬ D σ)
    (h : I ⊧ᴵ (KoreAML.Cons.distUncItem N g g' ug ug').pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.distUncItem N g g' ug ug').pat := by
  unfold KoreAML.Cons.distUncItem at hn h ⊢
  dsimp only at hn h ⊢
  rw [List.append_assoc (KoreAML.Cons.memGuards _ _ ++ KoreAML.Cons.memGuards _ _)] at hn h ⊢
  refine transferM2U_cs hD hDI (xs_length ..) (Nat.le_of_eq (xs_length ..)) (fun u hu => ?_)
    (own_distBody_cs N g g' _ _) (.inl rfl) hn h
  rcases List.mem_append.mp hu with hu | hu
  · exact own_uncOpt_cs ug _ _ (fun _ h => List.mem_append_left _ h) u hu
  · exact own_uncOpt_cs ug' _ _ (fun _ h => List.mem_append_right _ h) u hu

theorem sat_distLb_cs (hDI : DefOK I) (N A B : String) (lbs : List String)
    (hn : ∀ σ ∈ psyms (distLbItem N A B lbs).pat, ¬ D σ) (h : I ⊧ᴵ (distLbItem N A B lbs).pat) :
    extModel c D I ⊧ᴵ (distLbItem N A B lbs).pat :=
  transferG_sg hD hDI (gs := [(⟨1⟩, KoreAML.Cons.sortP A), (⟨2⟩, KoreAML.Cons.sortP B)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact .sortC id)
    (k := .pred)
    (.impPP (.equal_ex (own_inj_cs A N (OwnSorted.evar (by simp)).toOld) (own_inj_cs B N (OwnSorted.evar (by simp)).toOld))
      (disjList_pred_cs fun w hw => by
        obtain ⟨C, -, rfl⟩ := List.mem_map.mp hw
        exact .sEx (V' := []) (.sortC id) nil_sub (.inr (.inl rfl)) (.conj_pred
          (.equal_ex (.evar (by simp)) (own_inj_cs C A (OwnSorted.evar (List.mem_cons_self ..)).toOld))
          (.equal_ex (.evar (by simp)) (own_inj_cs C B (OwnSorted.evar (List.mem_cons_self ..)).toOld)))))
    (.inl rfl) hn h

theorem sat_coh_cs (hDI : DefOK I) (A B C : String)
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.cohItem A B C).pat, ¬ D σ) (h : I ⊧ᴵ (KoreAML.Cons.cohItem A B C).pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.cohItem A B C).pat :=
  transferG_sg hD hDI (gs := [(⟨1⟩, KoreAML.Cons.sortP A)])
    (fun p hp => by rw [List.mem_singleton.mp hp]; exact .sortC id)
    (k := .pred)
    (.equal_ex (own_inj_cs B C (own_inj_cs A B (OwnSorted.evar (List.mem_cons_self ..)).toOld).toOld)
      (own_inj_cs A C (OwnSorted.evar (List.mem_cons_self ..)).toOld))
    (.inl rfl) hn h

theorem sat_ovlEq_cs (hDI : DefOK I) (f g : KoreAML.CtorSig)
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.ovlEqItem f g).pat, ¬ D σ) (h : I ⊧ᴵ (KoreAML.Cons.ovlEqItem f g).pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.ovlEqItem f g).pat :=
  transferM_cs hD hDI (x := KoreAML.Cons.xs 0 g.args.length) (ss := g.args) (Nat.le_of_eq (xs_length ..))
    (k := .pred)
    (.equal_ex (.appList (.symC id) fun a ha => by
        obtain ⟨⟨⟨A, B⟩, xi⟩, hm, rfl⟩ := List.mem_map.mp ha
        exact (own_liftP_cs A B (.evar (List.of_mem_zip hm).2)).toOld)
      (own_liftP_cs _ _ (.appList (.symC id) (own_evars_cs fun _ h => h))))
    (.inl rfl) hn h

end

/-! ## The no-junk item -/

theorem noJunk_pat_cs (N : String) (gs : List KoreAML.Gen) :
    (KoreAML.Cons.noJunkItem N gs).pat =
      let X := Kore.Pattern.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs)
      (KoreAML.conjList (((KoreAML.freeOf [] X).eraseDups).map (KoreAML.guardOf (KoreAML.tableOf [] X))) ⇒
        (KoreAML.tr ⟨KoreAML.tableOf [] X, []⟩ X ≡ KoreAML.inhOf (KoreAML.Cons.sortP N))) := rfl

/-- The text's no-junk sentence is closed. -/
theorem noJunk_free_cs (N : String) (gs : List KoreAML.Gen) :
    KoreAML.freeOf [] (Kore.Pattern.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs)) = [] := by
  rw [KoreAML.freeOf]
  exact freeOfList_nil fun p hp => by
    rcases noJunkDisjuncts_cases N [] gs p hp with rfl | ⟨g, -, bs, body, rfl, -, -, hb, -⟩
    · rw [KoreAML.freeOf]
    · exact nj_freeOf_existsAll bs [] fun B _ hB => hb B hB

section
variable {V : List EVar}

theorem own_sTop_cs (n : String) : Own0 V [] .ex (KoreAML.sTop (KoreAML.sym (.sort n))) :=
  .sEx (V' := []) (.sortC id) nil_sub (.inl rfl) (.evar (List.mem_cons_self ..))

theorem own_sBot_cs (n : String) : Own0 V [] .ex (KoreAML.sBot (KoreAML.sym (.sort n))) :=
  .sNot (.sortC id) (own_sTop_cs n).toOld

theorem own_trOrList_cs (ctx : KoreAML.Ctx) (n : String) : ∀ {ds : List Kore.Pattern},
    (∀ d ∈ ds, Own0 V [] .ex (KoreAML.tr ctx d)) →
    Own0 V [] .ex (KoreAML.trOrList ctx (KoreAML.sym (.sort n)) ds)
  | [], _ => by rw [KoreAML.trOrList]; exact own_sBot_cs n
  | [d], h => by rw [KoreAML.trOrList]; exact h d (List.mem_singleton_self _)
  | d :: d' :: ds, h => by
    rw [KoreAML.trOrList]
    exact .sOr (.sortC id) (h d (List.mem_cons_self ..)).toOld
      (own_trOrList_cs ctx n (ds := d' :: ds) fun q hq => h q (List.mem_cons_of_mem _ hq)).toOld

end

/-- Binders at sort constants around a body of the class. -/
theorem own_existsAll_cs (t : KoreAML.VarTable) (S : Kore.KSort) (body : Kore.Pattern) {k : OwnKind}
    (hk : k = .ex ∨ k = .pred ∨ k = .old) : ∀ (bs : List Kore.EVar) (V : List EVar),
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    Own0 ((bs.map fun b => t.ev (KoreAML.evarKey b)) ++ V) [] k (KoreAML.tr ⟨t, []⟩ body) →
    Own0 V [] k (KoreAML.tr ⟨t, []⟩ (KoreAML.existsAll S bs body))
  | [], _, _, h => h
  | b :: bs, V, hs, h => by
    show Own0 V [] k (KoreAML.tr ⟨t, []⟩ (.exist S b (KoreAML.existsAll S bs body)))
    rw [KoreAML.tr]
    dsimp only
    obtain ⟨n, hn⟩ := hs b (List.mem_cons_self ..)
    refine .sEx (V' := []) (by rw [hn, trSort_srt]; exact .sortC id) nil_sub hk
      (own_existsAll_cs t S body hk bs _ (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb')) (h.mono ?_ fun _ h => h))
    intro y hy
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hy ⊢
    rcases hy with rfl | hy | hy
    · exact .inr (.inl rfl)
    · exact .inl hy
    · exact .inr (.inr hy)

/-- The translation of the text's no-junk sentence has no added element in the extension. -/
theorem own_trNoJunk_cs (N : String) (gs : List KoreAML.Gen) (t : KoreAML.VarTable) :
    Own0 [] [] .ex (KoreAML.tr ⟨t, []⟩ (Kore.Pattern.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs))) := by
  rw [KoreAML.tr, trSort_srt]
  refine own_trOrList_cs _ _ fun d hd => ?_
  rcases noJunkDisjuncts_cases N [] gs d hd with rfl | ⟨g, -, bs, body, rfl, hsorts, -, -, htr⟩
  · rw [KoreAML.tr, trSort_srt]; exact own_sBot_cs _
  · refine own_existsAll_cs t _ body (.inl rfl) bs [] (fun b hb => ?_) ?_
    · have : b.sort ∈ g.argSorts.map KoreAML.srt := hsorts ▸ List.mem_map.mpr ⟨b, hb, rfl⟩
      obtain ⟨n, -, hn⟩ := List.mem_map.mp this
      exact ⟨n, hn.symm⟩
    · rw [htr t]
      exact own_genPat_cs _ g fun a ha => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact (OwnSorted.evar (List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩))).toOld

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

theorem sat_noJunk_cs (hDI : DefOK I) (N : String) (gs : List KoreAML.Gen)
    (hn : ∀ σ ∈ psyms (KoreAML.Cons.noJunkItem N gs).pat, ¬ D σ) (h : I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs).pat) :
    extModel c D I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs).pat := by
  have hb : Own0 [] [] .pred (KoreAML.Cons.noJunkItem N gs).pat := by
    rw [noJunk_pat_cs]
    dsimp only
    rw [noJunk_free_cs, List.eraseDups_nil, List.map_nil]
    exact .impPP .top_pred (.equal_ex (own_trNoJunk_cs N gs _) (.inhOf (.sortC id)))
  exact transfer0_sg hD hDI hb (.inl rfl) hn h

theorem sat_consItem_cs (hlaw : ∀ p ∈ c.params, p.raw = true →
      ¬ D (.sort ("Sort" ++ c.sortName p.sig.result)) ∧ ¬ D (.symbol (c.symName p.sig.name)) ∧
      ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName p.sig.result)) a ↔ a = σ)
    (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) (hDI : DefOK I) {it : KoreAML.Item}
    (hit : it ∈ consItemsK c) (hn : ∀ σ ∈ psyms it.pat, ¬ D σ) (h : I ⊧ᴵ it.pat) :
    extModel c D I ⊧ᴵ it.pat := by
  unfold consItemsK at hit
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter] at hit
  revert hn h
  rcases hit with ((⟨N, -, (((⟨g, -, rfl⟩ | ⟨g, -, rfl⟩) | ⟨⟨g, g'⟩, -, hit⟩) | hit)⟩ |
    ⟨ab, -, e, -, rfl⟩) | ⟨o, -, kg, -, rfl⟩) | hit
  · split <;> intro hn h
    · exact sat_funUnc_cs hD hDI _ _ _ hn h
    · exact sat_fun_cs hD hDI _ _ hn h
  · split <;> intro hn h
    · exact sat_injUnc_cs hD hDI _ _ _ hn h
    · exact sat_inj_cs hD hDI _ _ hn h
  · dsimp only at hit
    repeat' split at hit
    all_goals first
      | exact absurd hit List.not_mem_nil
      | (obtain rfl := List.mem_singleton.mp hit
         intro hn h
         first
           | with_reducible exact sat_dist_cs hD hDI _ _ _ hn h
           | with_reducible exact sat_distLb_cs hD hDI _ _ _ _ hn h
           | with_reducible exact sat_distUnc_cs hD hDI _ _ _ _ _ hn h)
  · split at hit
    · exact absurd hit List.not_mem_nil
    · obtain rfl := List.mem_singleton.mp hit
      exact sat_noJunk_cs hD hDI _ _
  · exact sat_coh_cs hD hDI _ _ _
  · exact sat_ovlEq_cs hD hDI _ _
  · simp only [lawItemsK, List.mem_flatMap] at hit
    obtain ⟨p, hp, hit⟩ := hit
    split at hit
    · rename_i hr
      obtain ⟨hns, hnf, hSs⟩ := hlaw p hp hr
      rcases List.mem_append.mp hit with hit | hit
      · split at hit
        · obtain rfl := List.mem_singleton.mp hit
          exact fun _ h => transfer_assoc hD hDI hc p hns hnf hSs h
        · exact absurd hit List.not_mem_nil
      · split at hit
        · obtain rfl := List.mem_singleton.mp hit
          exact fun _ h => transfer_idem hD hDI hc p hns hnf hSs h
        · exact absurd hit List.not_mem_nil
    · exact absurd hit List.not_mem_nil


/-- **The extension satisfies every premise of `ΓCons` that names nothing of `D`**, for a model of
`Γown c D`, names `D` that are sort constants and symbols of the definition, and open generators
whose symbol and result sort are outside `D`, the sort denoting one sort of the model (`hlaw`:
their law sentences are transferred as written). -/
theorem sat_own_cons (hlaw : ∀ p ∈ c.params, p.raw = true →
      ¬ D (.sort ("Sort" ++ c.sortName p.sig.result)) ∧ ¬ D (.symbol (c.symName p.sig.name)) ∧
      ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName p.sig.result)) a ↔ a = σ) (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P}
    (hφ : ΓCons c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr hφ))))))), hn⟩
  rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
  · exact sat_consItem_cs hD hlaw (hI _ (own_of_sig_sg
      (.inl (.inl ⟨KoreAML.ceilDefItem, by unfold sigItems; simp, rfl⟩))
      (clean_of_plain_sg hD (noPlain_of_sg (by decide))))) hDI hit hn hI'
  · exact sat_definedness_sg x

/-- **The extension satisfies every premise of `ΓSig`, `ΓCons` and `ΓColls` that names nothing of
`D`** (the definedness schema and `dvArityAll` among them), for a model of `Γown c D`, names `D`
that are sort constants and symbols of the definition, and open generators whose symbol and
result sort are outside `D`, the sort denoting one sort of the model. -/
theorem sat_own_sig_cons (hlaw : ∀ p ∈ c.params, p.raw = true →
      ¬ D (.sort ("Sort" ++ c.sortName p.sig.result)) ∧ ¬ D (.symbol (c.symName p.sig.name)) ∧
      ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName p.sig.result)) a ↔ a = σ) (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P}
    (hφ : ΓSig c φ ∨ ΓCons c φ ∨ ΓColls c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  rcases hφ with hφ | hφ | hφ
  · exact sat_own_sig hD hI hφ hn
  · exact sat_own_cons hD hlaw hI hφ hn
  · exact sat_own_colls hD hI hφ hn

end

end KCore.Cons
