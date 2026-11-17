/-
  The model half of the conservativity of the generated equations the account accepts without a
  function of the definition holding them: equations `f(w) = v` at values, of a symbol `f` that no
  premise of `Γ` applies (a sort's projection, a constructor argument's projection).

  - **An interpretation patched at some elements (`patch`).** `patch I P F` is `I` with the
    application of the elements of `P` replaced by `F`. Where they are spare for the symbols `S`
    (`Spare`: only a symbol of `S` holds of one, and application gives one, and the definedness
    element `d`, only from `d`), a pattern that names no symbol of `S` and whose applications are
    chains from a symbol (`rootedB`: the left side of an application is a symbol, or an
    application whose chain starts at a symbol other than definedness) denotes in `patch I P F`
    what it denotes in `I` (`patch_interpret`). Freeness of the symbols alone would not give it: a
    variable, a negation and `⌈_⌉` denote the patched elements too, so `x ⬝ y` would read the
    patch.
  - **Every premise of the theory is such a pattern (`rooted_of_decided`)**, decided on the
    theory's lists (`rootedListsB`) and shown for the premises stated at every value.
  - **The value model (`stdPatch`).** In the value model at any transition `T`, the heads of any
    names `N` are spare for those names' symbols (`spare_stdI`). So where no premise names one of
    `N`, the value model patched at those heads by any `F` is a model of the theory wherever the
    value model is (`stdPatch_model`), it denotes at every rooted pattern without a name of `N`
    what the value model denotes (`stdPatch_interpret`: the transition, the values and the sorts
    are unchanged, `stdPatch_step`), and for partial functions `G n` on values, a name `n` of `N`
    applied to a value `w` with `G n w = some v` is `v` (`stdPatch_eqn`: the equation `n(w) = v`
    holds). `model_with_eqns` puts these together under `coreOK` and `FnHyp`. The equations are
    stated at values, one instance for each value, not as the text's quantified sentence.
  - **The projections as such functions**: a sort's (`projFn`, through the item's normal form),
    KItem's (`itemFn`), K's (the identity, `some`), a constructor argument's (`argFn`).

  The statement is at the value models `stdI_T c T`, not at every model of `Γ`. Application is one
  relation of the interpretation, so a symbol is reinterpreted only by changing application at an
  element it denotes; an arbitrary model has no element that application and the other symbols
  leave alone, and adding one changes what every quantifier and negation of every premise ranges
  over. The value models are the models the statements over a semantics produce (`Consistent`,
  `ExactC`, `has_model_choice`); their entailments only gain premises.
-/
import KcoreSpec.GenEqsConservative
import KcoreSpec.ModelFunctional

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

/-! ## Application chains -/

/-- The symbol an application chain starts at. -/
def root : KoreAML.P → Option KoreAML.Sym
  | .symbol σ => some σ
  | .application a _ => root a
  | _ => none

/-- An application chain that starts at a symbol other than definedness. -/
def chainB (a : KoreAML.P) : Bool :=
  match root a with
  | some .defined => false
  | some _ => true
  | none => false

/-- What an application's left side may be: a symbol, or an application whose chain starts at a
symbol other than definedness. -/
def lhsB : KoreAML.P → Bool
  | .symbol _ => true
  | .application a _ => chainB a
  | _ => false

/-- Every application of the pattern has such a left side. -/
def rootedB : KoreAML.P → Bool
  | .application a b => lhsB a && rootedB a && rootedB b
  | .implication a b => rootedB a && rootedB b
  | .existential _ a => rootedB a
  | .mu _ a => rootedB a
  | _ => true

@[simp] theorem rootedB_app (a b : KoreAML.P) : rootedB (a ⬝ b) = (lhsB a && rootedB a && rootedB b) := rfl
@[simp] theorem rootedB_imp (a b : KoreAML.P) : rootedB (a ⇒ b) = (rootedB a && rootedB b) := rfl
@[simp] theorem rootedB_ex (x : EVar) (a : KoreAML.P) : rootedB (.existential x a) = rootedB a := rfl
@[simp] theorem rootedB_mu (X : SVar) (a : KoreAML.P) : rootedB (.mu X a) = rootedB a := rfl
@[simp] theorem rootedB_bot : rootedB (⊥ : KoreAML.P) = true := rfl
@[simp] theorem rootedB_evar (x : EVar) : rootedB (.evar x : KoreAML.P) = true := rfl
@[simp] theorem rootedB_svar (X : SVar) : rootedB (.svar X : KoreAML.P) = true := rfl
@[simp] theorem rootedB_symbol (σ : KoreAML.Sym) : rootedB (.symbol σ : KoreAML.P) = true := rfl
@[simp] theorem lhsB_symbol (σ : KoreAML.Sym) : lhsB (.symbol σ : KoreAML.P) = true := rfl
@[simp] theorem lhsB_app (a b : KoreAML.P) : lhsB (a ⬝ b) = chainB a := rfl
@[simp] theorem chainB_app (a b : KoreAML.P) : chainB (a ⬝ b) = chainB a := rfl
@[simp] theorem chainB_symbol (n : String) : chainB (.symbol (.symbol n) : KoreAML.P) = true := rfl
@[simp] theorem chainB_sort (n : String) : chainB (.symbol (.sort n) : KoreAML.P) = true := rfl
@[simp] theorem chainB_dv (l : String) : chainB (.symbol (.dv l) : KoreAML.P) = true := rfl
@[simp] theorem chainB_inh : chainB (.symbol .inh : KoreAML.P) = true := rfl
@[simp] theorem chainB_ceil : chainB (.symbol .ceil : KoreAML.P) = true := rfl
@[simp] theorem chainB_next : chainB (.symbol .next : KoreAML.P) = true := rfl

theorem lhsB_of_chain : ∀ {a : KoreAML.P}, chainB a = true → lhsB a = true
  | .symbol _, _ => rfl
  | .application _ _, h => h
  | .evar _, h => by cases h
  | .svar _, h => by cases h
  | .bottom, h => by cases h
  | .implication _ _, h => by cases h
  | .existential _ _, h => by cases h
  | .mu _ _, h => by cases h

/-! ## An interpretation patched at some elements -/

section Patch

variable {M : Type}

/-- `I` with the application of the elements of `P` replaced by `F`. -/
def patch (I : Interpretation KoreAML.Sym M) (P : M → Prop) (F : M → M → Set M) :
    Interpretation KoreAML.Sym M :=
  ⟨I.evalSymb, fun a b x => (P a ∧ F a b x) ∨ (¬ P a ∧ I.evalApp a b x)⟩

/-- The elements of `P` are spare for the symbols `S` in `I`, with `d` the definedness element: no
symbol but one of `S` holds of an element of `P`, none but definedness of `d`, and application
gives an element of `P`, or `d`, only from `d`. -/
structure Spare (I : Interpretation KoreAML.Sym M) (P : M → Prop) (S : KoreAML.Sym → Prop) (d : M) : Prop where
  sym_e : ∀ τ e, P e → I.evalSymb τ e → S τ
  sym_d : ∀ τ, I.evalSymb τ d → τ = .defined
  app_e : ∀ a b e, P e → I.evalApp a b e → a = d
  app_d : ∀ a b, I.evalApp a b d → a = d

variable {I : Interpretation KoreAML.Sym M} {P : M → Prop} {S : KoreAML.Sym → Prop} {d : M}

/-- A chain from a symbol other than definedness does not denote the definedness element. -/
theorem chain_not_d (hS : Spare I P S d) : ∀ (a : KoreAML.P), chainB a = true → ∀ ρ : Valuation M,
    ¬ a.interpret I ρ d
  | .symbol τ, h, _, hd => by
    have := hS.sym_d τ hd
    subst this
    cases h
  | .application a b, h, ρ, hd => by
    obtain ⟨a0, b0, ha, -, happ⟩ := interpret_app.mp hd
    rw [hS.app_d a0 b0 happ] at ha
    exact chain_not_d hS a h ρ ha
  | .evar _, h, _, _ => by cases h
  | .svar _, h, _, _ => by cases h
  | .bottom, h, _, _ => by cases h
  | .implication _ _, h, _, _ => by cases h
  | .existential _ _, h, _, _ => by cases h
  | .mu _ _, h, _, _ => by cases h

/-- An application's left side that names no symbol of `S` denotes no element of `P`. -/
theorem lhs_not_e (hS : Spare I P S d) : ∀ (a : KoreAML.P), lhsB a = true → (∀ τ ∈ psyms a, ¬ S τ) →
    ∀ (ρ : Valuation M) (e : M), P e → ¬ a.interpret I ρ e
  | .symbol τ, _, hσ, _, e, hP, he => hσ τ (List.mem_singleton.mpr rfl) (hS.sym_e τ e hP he)
  | .application a b, h, _, ρ, e, hP, he => by
    obtain ⟨a0, b0, ha, -, happ⟩ := interpret_app.mp he
    rw [hS.app_e a0 b0 e hP happ] at ha
    exact chain_not_d hS a h ρ ha
  | .evar _, h, _, _, _, _, _ => by cases h
  | .svar _, h, _, _, _, _, _ => by cases h
  | .bottom, h, _, _, _, _, _ => by cases h
  | .implication _ _, h, _, _, _, _, _ => by cases h
  | .existential _ _, h, _, _, _, _, _ => by cases h
  | .mu _ _, h, _, _, _, _, _ => by cases h

/-- **A rooted pattern that names no symbol of `S` denotes the same in the patched
interpretation.** -/
theorem patch_interpret (hS : Spare I P S d) (F : M → M → Set M) : ∀ (φ : KoreAML.P), rootedB φ = true →
    (∀ τ ∈ psyms φ, ¬ S τ) → ∀ ρ : Valuation M, φ.interpret (patch I P F) ρ = φ.interpret I ρ
  | .evar _, _, _, _ => rfl
  | .svar _, _, _, _ => rfl
  | .symbol _, _, _, _ => rfl
  | .bottom, _, _, _ => rfl
  | .implication a b, h, hσ, ρ => by
    simp only [rootedB, Bool.and_eq_true] at h
    simp only [psyms, List.mem_append] at hσ
    have iha := patch_interpret hS F a h.1 (fun τ hτ => hσ τ (.inl hτ)) ρ
    have ihb := patch_interpret hS F b h.2 (fun τ hτ => hσ τ (.inr hτ)) ρ
    show (fun m => a.interpret (patch I P F) ρ m → b.interpret (patch I P F) ρ m) = _
    rw [iha, ihb]
    rfl
  | .existential x a, h, hσ, ρ => by
    have ih := patch_interpret hS F a h hσ
    funext m
    simp only [Pattern.interpret, ih]
  | .mu X a, h, hσ, ρ => by
    have ih := patch_interpret hS F a h hσ
    funext m
    simp only [Pattern.interpret, ih]
  | .application a b, h, hσ, ρ => by
    simp only [rootedB, Bool.and_eq_true] at h
    simp only [psyms, List.mem_append] at hσ
    have hσa : ∀ τ ∈ psyms a, ¬ S τ := fun τ hτ => hσ τ (.inl hτ)
    have iha := patch_interpret hS F a h.1.2 hσa ρ
    have ihb := patch_interpret hS F b h.2 (fun τ hτ => hσ τ (.inr hτ)) ρ
    funext m
    apply propext
    rw [interpret_app, interpret_app, iha, ihb]
    constructor
    · rintro ⟨a0, b0, ha, hb, happ⟩
      rcases happ with ⟨hP, -⟩ | ⟨-, happ⟩
      · exact absurd ha (lhs_not_e hS a h.1.1 hσa ρ a0 hP)
      · exact ⟨a0, b0, ha, hb, happ⟩
    · rintro ⟨a0, b0, ha, hb, happ⟩
      exact ⟨a0, b0, ha, hb, .inr ⟨fun hP => lhs_not_e hS a h.1.1 hσa ρ a0 hP ha, happ⟩⟩

/-- A rooted pattern that names no symbol of `S` and holds in `I` holds in the patched
interpretation. -/
theorem patch_sat (hS : Spare I P S d) (F : M → M → Set M) {φ : KoreAML.P} (hr : rootedB φ = true)
    (hσ : ∀ τ ∈ psyms φ, ¬ S τ) (h : I ⊧ᴵ φ) : patch I P F ⊧ᴵ φ := by
  intro ρ m
  show φ.interpret (patch I P F) ρ m
  rw [patch_interpret hS F φ hr hσ ρ]
  exact h ρ m

end Patch

/-! ## The premises of the theory are rooted -/

theorem rooted_appList : ∀ (φs : List KoreAML.P) (h : KoreAML.P), chainB h = true → rootedB h = true →
    (∀ φ ∈ φs, rootedB φ = true) →
    chainB (KoreAML.appList h φs) = true ∧ rootedB (KoreAML.appList h φs) = true
  | [], _, hc, hr, _ => ⟨hc, hr⟩
  | φ :: φs, h, hc, hr, hφ => by
    rw [KoreAML.appList]
    refine rooted_appList φs (h ⬝ φ) hc ?_ (fun x hx => hφ x (List.mem_cons_of_mem _ hx))
    rw [rootedB_app, lhsB_of_chain hc, hr, hφ φ (List.mem_cons_self ..)]
    rfl

theorem rooted_eq (a b : KoreAML.P) : rootedB (a ≡ b) = (rootedB a && rootedB b) := by
  simp only [ML.equal, ML.total, Pattern.equivalence, Pattern.conjunction, Pattern.disjunction, Pattern.negation,
    rootedB_app, rootedB_imp, rootedB_symbol, rootedB_bot, lhsB_symbol]
  cases rootedB a <;> cases rootedB b <;> rfl

theorem rooted_neg (a : KoreAML.P) : rootedB (∼a) = rootedB a := by
  simp [Pattern.negation]

theorem rooted_and (a b : KoreAML.P) : rootedB (a ⋀ b) = (rootedB a && rootedB b) := by
  simp only [Pattern.conjunction, Pattern.disjunction, Pattern.negation, rootedB_imp, rootedB_bot]
  cases rootedB a <;> cases rootedB b <;> rfl

theorem rooted_sExists (x : EVar) (n : String) (a : KoreAML.P) :
    rootedB (KoreAML.sExists x (sortP n) a) = rootedB a := by
  simp only [KoreAML.sExists, rootedB_ex, rooted_and, ML.member, rootedB_app, rootedB_symbol, lhsB_symbol,
    rootedB_evar, KoreAML.inhOf, KoreAML.sym, sortP]
  simp

theorem rooted_ap (f : String) (ps : List Kore.Pattern) (h : ∀ p ∈ ps, rootedB (KoreAML.den p) = true) :
    rootedB (KoreAML.den (KoreAML.ap f ps)) = true := by
  unfold KoreAML.den
  rw [Model.tr_ap]
  exact (rooted_appList _ _ rfl rfl (fun φ hφ => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
    exact h p hp)).2

theorem rooted_symApp (c : Semantics) (f : Sym) (ps : List Kore.Pattern)
    (hps : ∀ p ∈ ps, rootedB (KoreAML.den p) = true) : rootedB (KoreAML.den (symApp c f ps)) = true := by
  unfold symApp
  cases hi : iteSort? (c.symName f) with
  | none => exact rooted_ap _ _ hps
  | some X =>
    show rootedB (KoreAML.tr ⟨[], []⟩ (.app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt X] ps)) = true
    rw [KoreAML.tr]
    simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte, KoreAML.trSortApp, KoreAML.srt,
      KoreAML.trSort_const, trArgs_appList]
    exact (rooted_appList _ _ rfl rfl (fun φ hφ => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
      exact hps p hp)).2

theorem rooted_elems (c : Semantics) (k : CollSig) : ∀ es : List GroundTerm,
    (∀ e ∈ es, rootedB (den c e) = true) → rootedB (KoreAML.den (GroundTerm.koreElems c k es)) = true
  | [], _ => by rw [GroundTerm.koreElems]; exact rooted_ap _ _ (fun _ h => nomatch h)
  | [e], h => by
    rw [GroundTerm.koreElems]
    exact rooted_ap _ _ (fun p hp => by rw [List.mem_singleton.mp hp]; exact h e (List.mem_cons_self ..))
  | e :: e' :: es, h => by
    rw [GroundTerm.koreElems]
    case x_1 => exact fun h => nomatch h
    refine rooted_ap _ _ (fun p hp => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact rooted_ap _ _ (fun p hp => by rw [List.mem_singleton.mp hp]; exact h e (List.mem_cons_self ..))
    · exact rooted_elems c k (e' :: es) fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem rooted_entry (c : Semantics) (k : CollSig) (e : GroundTerm × GroundTerm)
    (h : rootedB (den c e.1) = true ∧ rootedB (den c e.2) = true) :
    rootedB (KoreAML.den (GroundTerm.koreEntry c k e)) = true := by
  obtain ⟨x, v⟩ := e
  rw [GroundTerm.koreEntry]
  refine rooted_ap _ _ (fun p hp => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h.1
  · exact h.2

theorem rooted_entries (c : Semantics) (k : CollSig) : ∀ es : List (GroundTerm × GroundTerm),
    (∀ e ∈ es, rootedB (den c e.1) = true ∧ rootedB (den c e.2) = true) →
    rootedB (KoreAML.den (GroundTerm.koreEntries c k es)) = true
  | [], _ => by rw [GroundTerm.koreEntries]; exact rooted_ap _ _ (fun _ h => nomatch h)
  | [e], h => by
    rw [GroundTerm.koreEntries]
    exact rooted_entry c k e (h e (List.mem_cons_self ..))
  | e :: e' :: es, h => by
    rw [GroundTerm.koreEntries]
    case x_1 => exact fun h => nomatch h
    refine rooted_ap _ _ (fun p hp => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact rooted_entry c k e (h e (List.mem_cons_self ..))
    · exact rooted_entries c k (e' :: es) fun x hx => h x (List.mem_cons_of_mem _ hx)

mutual
/-- **A value's pattern is rooted.** -/
theorem rooted_val (c : Semantics) : ∀ v : GroundTerm, rootedB (den c v) = true
  | .ctor f ts => by
    rw [den_ctor, trArgs_appList, DetachedB.koreList_map]
    exact (rooted_appList _ _ rfl rfl (fun φ hφ => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      exact rooted_vals c ts t ht)).2
  | .inj a b t => by
    rw [den_inj]
    exact (rooted_appList _ _ rfl rfl (fun φ hφ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl | rfl
      · rfl
      · rfl
      · exact rooted_val c t)).2
  | .dv s lit => by
    unfold den KoreAML.den
    rw [GroundTerm.kore, KoreAML.tr_dv]
    rfl
  | .map s es => by
    unfold den
    rw [GroundTerm.kore]
    exact rooted_entries c _ es (rooted_ents c es)
  | .set s es => by
    unfold den
    rw [GroundTerm.kore]
    exact rooted_elems c _ es (rooted_vals c es)
  | .list s es => by
    unfold den
    rw [GroundTerm.kore]
    exact rooted_elems c _ es (rooted_vals c es)
  termination_by structural v => v
theorem rooted_vals (c : Semantics) : ∀ (vs : List GroundTerm), ∀ v ∈ vs, rootedB (den c v) = true
  | [], v, hv => nomatch hv
  | w :: ws, v, hv => by
    rcases List.mem_cons.mp hv with he | hv'
    · rw [he]; exact rooted_val c w
    · exact rooted_vals c ws v hv'
  termination_by structural vs => vs
theorem rooted_ents (c : Semantics) : ∀ (es : List (GroundTerm × GroundTerm)),
    ∀ e ∈ es, rootedB (den c e.1) = true ∧ rootedB (den c e.2) = true
  | [], e, he => nomatch he
  | e0 :: es, e, he => by
    rcases List.mem_cons.mp he with he0 | he'
    · rw [he0]; exact rooted_ent c e0
    · exact rooted_ents c es e he'
  termination_by structural es => es
theorem rooted_ent (c : Semantics) : ∀ (e : GroundTerm × GroundTerm),
    rootedB (den c e.1) = true ∧ rootedB (den c e.2) = true
  | (x, v) => ⟨rooted_val c x, rooted_val c v⟩
  termination_by structural e => e
end

/-- A graph's premise is rooted: a symbol applied at values, equal to a rooted pattern. -/
theorem rooted_graph (c : Semantics) (f : Sym) (vs : List GroundTerm) {ρ : KoreAML.P} (hρ : rootedB ρ = true) :
    rootedB (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ ρ) = true := by
  rw [rooted_eq, hρ, Bool.and_true]
  refine rooted_symApp c f _ (fun p hp => ?_)
  rw [DetachedB.koreList_map] at hp
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hp
  exact rooted_val c v

/-- The parts of the theory that are lists hold rooted patterns only. -/
def rootedListsB (c : Semantics) : Bool :=
  (sigItems c ++ consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).all (fun it => rootedB it.pat) &&
  c.allColls.all (fun k => rootedB (collNoJunk c k) && (collAxioms c k).all rootedB) &&
  rootedB (boolClosed c)

/-- **Every premise of the theory is rooted** where its lists are (`rootedListsB`): the premises
stated at every value are a symbol applied at values equal to a value or to `⊥`, a value in its
sort, and two values apart. -/
theorem rooted_of_decided (c : Semantics) (hd : rootedListsB c = true) :
    ∀ φ, (Γc c ∪ Γstep c) φ → rootedB φ = true := by
  simp only [rootedListsB, Bool.and_eq_true, List.all_eq_true] at hd
  obtain ⟨⟨hLi, hLc⟩, hLb⟩ := hd
  have hdef : ∀ x : EVar, rootedB (@definedness KoreAML.Sym _ x) = true := fun x => by
    simp [definedness, Pattern.universal, Pattern.negation]
  intro φ hφ
  rcases hφ with hφ | hφ
  rotate_left
  · rw [hφ]
    exact hLi _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  rcases hφ with hφ | hφ
  rotate_left
  · rw [hφ.2.2]
    exact hLb
  rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
  · -- the signature
    rcases hφ with (⟨it, hit, rfl⟩ | ⟨x, rfl⟩) | ⟨lit, rfl⟩
    · exact hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hit))))
    · exact hdef x
    · simp [KoreAML.dvArityItem, KoreAML.guarded, KoreAML.conjList, KoreAML.sortGuard, ML.member, ML.included,
        ML.total, Pattern.negation, Pattern.conjunction, Pattern.disjunction, KoreAML.sortsDomain,
        KoreAML.inhOf, KoreAML.sym]
  · -- the constructors
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hit))))
    · exact hdef x
  · -- the domains
    rcases hφ with ⟨k, vs, r, hk, hvs, hr, hsil, rfl⟩ | ⟨k, vs, hk, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ |
      ⟨v, w, s, hds, hv, hw, hne, rfl⟩ | ⟨k, hk, rfl⟩
    · refine rooted_graph c _ vs ?_
      cases r with
      | none => rfl
      | some v => exact rooted_val c v
    · refine rooted_graph c _ vs ?_
      cases hpv : c.paramVal k.sig.name vs with
      | none => rfl
      | some v => exact rooted_val c v
    · rw [rooted_sExists, rooted_eq, rooted_val]
      rfl
    · rw [rooted_neg, rooted_and, rooted_val, rooted_val]
      rfl
    · exact (hLc k hk).1
  · -- the collections
    obtain ⟨k, hk, hmem⟩ := hφ
    exact (hLc k hk).2 φ hmem
  · -- the functions
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hit)))
    · exact hdef x
  · -- the rules
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hLi it (List.mem_append_left _ (List.mem_append_right _ hit))
    · exact hdef x
  · -- the fallbacks
    rcases hφ with ⟨k, vs, hk, hvs, hr, hsil, rfl⟩ | ⟨fn, vs, hfn, hvs, -, rfl⟩
    · refine rooted_graph c _ vs ?_
      cases hfb : c.fallback k.name vs with
      | none => rfl
      | some v => exact rooted_val c v
    · refine rooted_graph c _ vs ?_
      cases hfr : c.fnRest fn vs with
      | none => rfl
      | some v => exact rooted_val c v

/-! ## The value model -/

open Faithful.Model

/-- The symbol whose element a head without arguments is. -/
def symOfHead : Head → KoreAML.Sym
  | .defined => .defined
  | .inh => .inh
  | .sortSort => .sortSort
  | .ceil => .ceil
  | .next => .next
  | .inj => .symbol "inj"
  | .dv l => .dv l
  | .sym n => .symbol n

theorem result_val {c : Semantics} {k : CtorSig} {vs : List GroundTerm} {x : Elem} (h : result c k vs x) :
    ∃ v, x = .val v := by
  simp only [result] at h
  split at h
  · exact ⟨_, h⟩
  · split at h
    · obtain ⟨v, rfl, -⟩ := h; exact ⟨v, rfl⟩
    · split at h
      · obtain ⟨v, rfl, -⟩ := h; exact ⟨v, rfl⟩
      · split at h
        · unfold ovlRes at h
          split at h
          · obtain ⟨o, v, -, rfl, -⟩ := h; exact ⟨_, rfl⟩
          · exact ⟨_, h⟩
        · obtain ⟨v, rfl, -⟩ := h; exact ⟨v, rfl⟩

/-- A symbol holds of a head without arguments only as that head's symbol. -/
theorem evalSymb_head {c : Semantics} {τ : KoreAML.Sym} {h : Head} (hx : evalSymb c τ (.app h [])) :
    τ = symOfHead h := by
  cases τ with
  | defined => have h' : Elem.app h [] = .app .defined [] := hx; cases h'; rfl
  | inh => have h' : Elem.app h [] = .app .inh [] := hx; cases h'; rfl
  | sortSort => have h' : Elem.app h [] = .app .sortSort [] := hx; cases h'; rfl
  | ceil => have h' : Elem.app h [] = .app .ceil [] := hx; cases h'; rfl
  | next => have h' : Elem.app h [] = .app .next [] := hx; cases h'; rfl
  | dv l => have h' : Elem.app h [] = .app (.dv l) [] := hx; cases h'; rfl
  | sort n => obtain ⟨s, -, hs⟩ := hx; cases hs
  | str _ => exact hx.elim
  | untranslated _ => exact hx.elim
  | symbol m =>
    by_cases hm : m = "inj"
    · subst hm
      have h' : Elem.app h [] = .app .inj [] := hx
      cases h'; rfl
    · rw [evalSymb_symbol hm] at hx
      generalize resolve c m [] = r at hx
      rcases r with _ | ⟨k, _ | i⟩
      · cases hx; rfl
      · have hx' := (ite_mem _ _ _).mp hx
        by_cases hk : k.args = []
        · simp only [hk, ↓reduceIte] at hx'
          obtain ⟨v, hv⟩ := result_val hx'
          cases hv
        · simp only [hk, ↓reduceIte] at hx'
          cases hx'; rfl
      · cases hx; rfl

theorem symAt_head {c : Semantics} {n : String} {args : List Elem} {h : Head}
    (hx : symAt c n args (.app h [])) : args = [] := by
  refine Classical.byContradiction fun ha => ?_
  unfold symAt at hx
  generalize resolve c n args = r at hx
  rcases r with _ | ⟨k, p⟩
  · have hx' := (ite_mem _ _ _).mp hx
    simp only [ha, ↓reduceIte] at hx'
    split at hx'
    · cases hx'
    · rename_i hneg
      exact cast (congrFun (symAt.match_3.eq_2 (fun _ _ => Set Elem) n args
        (fun _ => fun x => x = Elem.app (.sym n) args) (fun _ _ => fun _ => False) hneg) (Elem.app h [])) hx'
  · have hx' := (ite_mem _ _ _).mp hx
    by_cases hl : args.length < p + k.args.length
    · simp only [hl, ↓reduceIte] at hx'
      injection hx' with _ h2
      exact ha h2.symm
    · simp only [hl, ↓reduceIte] at hx'
      have hx2 := (ite_mem _ _ _).mp hx'
      by_cases hl2 : args.length = p + k.args.length
      · simp only [hl2, ↓reduceIte] at hx2
        generalize vals (List.drop p args) = o at hx2
        rcases o with _ | vs
        · exact hx2
        · obtain ⟨v, hv⟩ := result_val hx2
          cases hv
      · simp only [hl2, ↓reduceIte] at hx2

/-- Application gives a head without arguments only from the definedness element. -/
theorem evalApp_head {c : Semantics} {T : GroundTerm → GroundTerm → Prop} {a b : Elem} {h : Head}
    (hx : evalApp_T c T a b (.app h [])) : a = .app .defined [] := by
  rcases a with v | s | ⟨hd, args⟩
  · exact False.elim hx
  · exact False.elim hx
  · cases hd with
    | sym n =>
      have hx' : symAt c n (args ++ [b]) (.app h []) := hx
      exact absurd (symAt_head hx') (by simp)
    | defined =>
      rcases args with _ | ⟨_, _⟩
      · rfl
      · exact False.elim hx
    | sortSort => rcases args with _ | ⟨_, _⟩ <;> exact False.elim hx
    | next => rcases args with _ | ⟨_, _⟩ <;> exact False.elim hx
    | inh =>
      rcases args with _ | ⟨_, _⟩
      · rcases b with _ | _ | ⟨hb, bargs⟩
        · exact False.elim hx
        · exact False.elim hx
        · cases hb <;> rcases bargs with _ | ⟨_, _⟩ <;>
            first | exact False.elim hx | (obtain ⟨_, -, hs⟩ := hx; cases hs)
      · exact False.elim hx
    | dv l =>
      rcases args with _ | ⟨_, _⟩
      · rcases b with _ | _ | _
        · exact False.elim hx
        · obtain ⟨_, hs, -⟩ := hx
          cases hs
        · exact False.elim hx
      · exact False.elim hx
    | ceil =>
      rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩
      · cases hx
      · cases hx
      · rcases a2 with _ | _ | _ <;> exact False.elim hx
      · rcases a2 with _ | _ | _ <;> exact False.elim hx
    | inj =>
      rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩
      · cases hx
      · cases hx
      · rcases a1 with _ | _ | _ <;> rcases a2 with _ | _ | _ <;> rcases b with _ | _ | _ <;>
          first | exact False.elim hx | cases hx
      · rcases a1 with _ | _ | _ <;> rcases a2 with _ | _ | _ <;> rcases b with _ | _ | _ <;>
          exact False.elim hx

/-- The heads of the names `N`. -/
def headsOf (N : String → Prop) : Elem → Prop := fun x => ∃ n, N n ∧ x = .app (.sym n) []

/-- The symbols of the names `N`. -/
def namesOf (N : String → Prop) : KoreAML.Sym → Prop := fun τ => ∃ n, N n ∧ τ = .symbol n

/-- **The heads of any names are spare for those names' symbols** in the value model at any
transition. -/
theorem spare_stdI (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop) :
    Spare (stdI_T c T) (headsOf N) (namesOf N) (Elem.app .defined []) :=
  ⟨fun _ _ ⟨n, hn, he⟩ h => ⟨n, hn, by subst he; exact evalSymb_head h⟩, fun _ h => evalSymb_head h,
    fun _ _ _ ⟨_, _, he⟩ h => by subst he; exact evalApp_head h, fun _ _ h => evalApp_head h⟩

/-- The value model at `T` with the application of the heads of the names `N` replaced by `F`. -/
def stdPatch (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop)
    (F : Elem → Elem → Set Elem) : Interpretation KoreAML.Sym Elem :=
  patch (stdI_T c T) (headsOf N) F

/-- **A rooted pattern that names none of `N` denotes in the patched value model what it denotes in
the value model.** -/
theorem stdPatch_interpret (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop)
    (F : Elem → Elem → Set Elem) {φ : KoreAML.P} (hr : rootedB φ = true)
    (hn : ∀ n, N n → KoreAML.Sym.symbol n ∉ psyms φ) (ρ : Valuation Elem) :
    φ.interpret (stdPatch c T N F) ρ = φ.interpret (stdI_T c T) ρ :=
  patch_interpret (spare_stdI c T N) F φ hr (fun _ hτ ⟨n, hN, he⟩ => hn n hN (he ▸ hτ)) ρ

/-- **The patched value model is a model of the theory wherever the value model is**, for names
no premise names and any `F`. -/
theorem stdPatch_model (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop)
    (F : Elem → Elem → Set Elem) (hr : rootedListsB c = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ)
    (hI : stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c)) : stdPatch c T N F ⊧ᴵP (Γc c ∪ Γstep c) :=
  fun φ hφ => patch_sat (spare_stdI c T N) F (rooted_of_decided c hr φ hφ)
    (fun _ hτ ⟨n, hN, he⟩ => hfree n hN φ hφ (he ▸ hτ)) (hI φ hφ)

/-- A value of a sort names no symbol that no premise names: the theory states that the value is
an element of its sort. -/
theorem val_unnamed {c : Semantics} {n : String}
    (hfree : ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) {v : GroundTerm} {s : Srt}
    (hv : c.sortOf v = some s) : KoreAML.Sym.symbol n ∉ psyms (den c v) := by
  intro hm
  refine hfree _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
    (Or.inr (Or.inr (Or.inl ⟨v, s, hv, rfl⟩)))))))))) ?_
  simp only [KoreAML.sExists, ML.member, ML.equal, ML.total, Pattern.equivalence, Pattern.conjunction,
    Pattern.disjunction, Pattern.negation, psyms, List.mem_append]
  simp [hm]

/-- The symbol named `n` holds of its head only: the name is not `inj`'s, and it resolves to no
symbol without arguments. -/
def spareSymB (c : Semantics) (n : String) : Bool :=
  n != "inj" && match resolve c n [] with
    | some (k, 0) => !k.args.isEmpty
    | _ => true

theorem evalSymb_spare {c : Semantics} {n : String} (h : spareSymB c n = true) (x : Elem) :
    evalSymb c (.symbol n) x ↔ x = .app (.sym n) [] := by
  simp only [spareSymB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hn, hres⟩ := h
  rw [evalSymb_symbol hn]
  generalize resolve c n [] = r at hres
  rcases r with _ | ⟨k, _ | i⟩
  · exact Iff.rfl
  · refine (ite_mem _ _ x).trans ?_
    have hk : ¬ k.args = [] := by
      intro hk
      simp [hk] at hres
    simp only [hk, ↓reduceIte]
  · exact Iff.rfl

/-- **The symbol of a name of `N` applied to a pattern** in the patched value model: `F` of the
name's head at the elements the pattern denotes in the value model. -/
theorem stdPatch_app (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop)
    (F : Elem → Elem → Set Elem) {n : String} (hN : N n) (hsym : spareSymB c n = true) {ψ : KoreAML.P}
    (hr : rootedB ψ = true) (hn : ∀ n, N n → KoreAML.Sym.symbol n ∉ psyms ψ) (ρ : Valuation Elem) (m : Elem) :
    (symP n ⬝ ψ).interpret (stdPatch c T N F) ρ m ↔
      ∃ b, ψ.interpret (stdI_T c T) ρ b ∧ F (.app (.sym n) []) b m := by
  rw [interpret_app, stdPatch_interpret c T N F hr hn ρ]
  constructor
  · rintro ⟨a, b, ha, hb, happ⟩
    have ha' : a = Elem.app (.sym n) [] := (evalSymb_spare hsym a).mp ha
    subst ha'
    rcases happ with ⟨-, hF⟩ | ⟨hne, -⟩
    · exact ⟨b, hb, hF⟩
    · exact absurd ⟨n, hN, rfl⟩ hne
  · rintro ⟨b, hb, hF⟩
    exact ⟨_, b, (evalSymb_spare hsym _).mpr rfl, hb, .inl ⟨⟨n, hN, rfl⟩, hF⟩⟩

/-- Partial functions on values, one for each name, as the application of the names' heads:
`G n w` at the head of `n` and the value `w`. -/
def valApp (G : String → GroundTerm → Option GroundTerm) : Elem → Elem → Set Elem :=
  fun a b m => ∃ n w v, a = .app (.sym n) [] ∧ b = .val w ∧ G n w = some v ∧ m = .val v

/-- **The equation `n(w) = v` holds in the value model patched by `G`** where `G n w = some v`, for
a name `n` of `N` and values `w` and `v` of a sort: every value denotes its own element
(`DenGoalT`), so `n` applied to `w` denotes `G n`'s value at `w`. -/
theorem stdPatch_eqn (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop)
    (G : String → GroundTerm → Option GroundTerm) (hr : rootedListsB c = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ)
    (hI : stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c)) (hden : AtT.DenGoalT c T) {n : String} (hN : N n)
    (hsym : spareSymB c n = true) {w v : GroundTerm} {s s' : Srt}
    (hw : c.sortOf w = some s) (hv : c.sortOf v = some s') (hg : G n w = some v) :
    stdPatch c T N (valApp G) ⊧ᴵ (symP n ⬝ den c w ≡ den c v) := by
  have hM := stdPatch_model c T N (valApp G) hr hfree hI
  have hD : KoreAML.DefOK (stdPatch c T N (valApp G)) := defOK (fun φ hφ => hM φ (Or.inl (Or.inl hφ)))
  intro ρ m
  show (symP n ⬝ den c w ≡ den c v).interpret (stdPatch c T N (valApp G)) ρ m
  rw [KoreAML.interp_equal hD]
  intro a
  rw [stdPatch_app c T N _ hN hsym (rooted_val c w) (fun k hk => val_unnamed (hfree k hk) hw),
    stdPatch_interpret c T N _ (rooted_val c v) (fun k hk => val_unnamed (hfree k hk) hv)]
  constructor
  · rintro ⟨b, hb, n', w', v', hn', hbw, hg', rfl⟩
    cases hn'
    have hb' := (hden w s hw ρ b).mp hb
    rw [hb'] at hbw
    cases hbw
    rw [hg] at hg'
    cases hg'
    exact (hden v s' hv ρ _).mpr rfl
  · intro ha
    have ha' := (hden v s' hv ρ a).mp ha
    rw [ha']
    exact ⟨.val w, (hden w s hw ρ _).mpr rfl, n, w, v, rfl, rfl, hg, rfl⟩

/-- **The patched value model has the value model's steps**: at configurations `x` and `y`, the
sentence "`y` is no successor of `x`" holds in one where it holds in the other. -/
theorem stdPatch_step (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop)
    (F : Elem → Elem → Set Elem)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) (x y : Config c) :
    (stdPatch c T N F ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) ↔
      (stdI_T c T ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hr : rootedB (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)) = true := by
    simp [KoreAML.sNext, KoreAML.sym, Pattern.negation, rooted_val]
  have hn : ∀ n, N n → KoreAML.Sym.symbol n ∉ psyms (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)) := by
    intro n hN
    simp [KoreAML.sNext, KoreAML.sym, psyms, val_unnamed (hfree n hN) x.property,
      val_unnamed (hfree n hN) y.property]
  constructor
  · intro h ρ m
    have := h ρ m
    rwa [show (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)).interpret (stdPatch c T N F) ρ = _ from
      stdPatch_interpret c T N F hr hn ρ] at this
  · intro h ρ m
    show (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)).interpret (stdPatch c T N F) ρ m
    rw [stdPatch_interpret c T N F hr hn ρ]
    exact h ρ m

/-- **The theory with the equations of symbols it does not name has a model with the value
model's steps.** For a semantics that `coreOK` accepts under `FnHyp`, names `N` no premise names
(`hfree`) that resolve to no constant (`spareSymB`), and a partial function `G n` on values for
each: an interpretation that satisfies `Γc c` with the step's closure, in which `n(w) = v` holds
for every name `n` of `N` wherever `G n w = some v` at values of a sort, and whose steps at values
are the model's (`StepM`). -/
theorem model_with_eqns (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (N : String → Prop)
    (G : String → GroundTerm → Option GroundTerm) (hr : rootedListsB c = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ)
    (hsym : ∀ n, N n → spareSymB c n = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ n, N n → ∀ (w v : GroundTerm) (s s' : Srt), c.sortOf w = some s → c.sortOf v = some s' →
        G n w = some v → I ⊧ᴵ (symP n ⬝ den c w ≡ den c v)) ∧
      ∀ x y : Config c, StepM c x.val y.val ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hm := hypModel_of_fnHyp h hf
  have hrules := Semantics.ruleFactsHeld_of_core h
  have hiff : ∀ {x y : GroundTerm}, StepV c x y ↔ StepM c x y :=
    stepV_iff_stepM h (fnModel_of_fnHyp h hf).1 hf.1 (fun r hr => (hrules r hr).1)
  have hI : stdI_T c (StepM c) ⊧ᴵP (Γc c ∪ Γstep c) :=
    stdI_T_model_held c h hm (clausePreDecided_of_fnHyp h hf) hf.2.2.2.2.2 hrules (StepM c)
      (fun _ _ _ _ hT => hiff.mpr hT) (fun r σ _ _ hb _ => hiff.mp ⟨r, σ, hb⟩)
      (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, hiff.mp ⟨r, σ, hb⟩⟩)
  refine ⟨stdPatch c (StepM c) N (valApp G), stdPatch_model c _ N _ hr hfree hI,
    fun n hN w v s s' hw hv hg => stdPatch_eqn c _ N G hr hfree hI (AtT.denGoal hm) hN (hsym n hN) hw hv hg,
    fun x y => ?_⟩
  rw [stdPatch_step c _ N _ hfree x y]
  exact step_iff_stdI_T c hm (StepM c) x y

/-! ## The projections as partial functions on values -/

/-- A sort's projection on values. The item of a value `v` of `X` is `kseq(i, dotk)` with `i` the
value `v` as one of KItem (`injNormal`): `inj{X,KItem}(v)`, or for `v = inj{A,X}(u)` the same core
`inj{A,KItem}(u)`. -/
def projFn (c : Semantics) (X : Srt) : GroundTerm → Option GroundTerm
  | .ctor f [.inj a b u, .ctor f' []] =>
    if f = kseq ∧ f' = dotk ∧ b = Srt.kitem then
      if a = X then some u else if c.subsorts.contains (a, X) then some (.inj a X u) else none
    else none
  | _ => none

/-- `projFn c X` at the item of a value of `X` is that value, where `X` is no subsort of itself. -/
theorem projFn_item (c : Semantics) (X : Srt) (hX : (X, X) ∉ c.subsorts) {v : GroundTerm}
    (hv : c.sortOf v = some X) :
    projFn c X (.ctor kseq [injNormal X Srt.kitem v, .ctor dotk []]) = some v := by
  cases v with
  | inj a b t =>
    obtain ⟨hab, -, -, hb⟩ := sortOf_inj.mp hv
    subst hb
    have ha : a ≠ X := fun h => hX (h ▸ hab)
    simp [projFn, injNormal, ha, hab]
  | _ => simp [projFn, injNormal]

/-- KItem's projection on values: the item `i` at `kseq(i, dotk)`. -/
def itemFn : GroundTerm → Option GroundTerm
  | .ctor f [i, .ctor f' []] => if f = kseq ∧ f' = dotk then some i else none
  | _ => none

theorem itemFn_item (i : GroundTerm) : itemFn (.ctor kseq [i, .ctor dotk []]) = some i := by
  simp [itemFn]

/-- A constructor argument's projection on values: the `i`-th argument of a term of `f`. -/
def argFn (f : Sym) (i : Nat) : GroundTerm → Option GroundTerm
  | .ctor f' vs => if f' = f then vs[i]? else none
  | _ => none

theorem argFn_ctor (f : Sym) (i : Nat) (vs : List GroundTerm) : argFn f i (.ctor f vs) = vs[i]? := by
  simp [argFn]

end GenEqs

end KCore
