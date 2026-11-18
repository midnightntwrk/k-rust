/-
  A walk of the theory's lists: every item of `Γc c ∪ Γstep c` that a list holds is rooted, and the
  symbols it names are the semantics' own (`c.symName f`), `inj` or `Lblite`.

  - **Good patterns (`good ok`).** A pattern whose applications have a rooted left side (`rootedB`)
    and whose symbols `.symbol n` have names that `ok` accepts.
  - **The translation (`good_tr`).** The translation of a KORE pattern whose application heads `ok`
    accepts (`kok ok`) is good: `tr` writes an application as a chain from its head symbol applied
    to the sort arguments and the arguments, and every connective as a pattern of applications of
    `⌈_⌉`, `⟦_⟧`, `•` and `ceil` to its operands; `ν` substitutes a good pattern for a set variable,
    which keeps a pattern good (`good_subst`).
  - **The KORE the semantics writes (`kok_term`, ...).** Its terms, conditions, premises,
    equations and rules apply `c.symName f`, `inj` or `Lblite` only.
  - **The lists (`good_lists`).** Every item of the signature, the constructors, the functions, the
    rules, the step's closure, the collections and Bool's closure is good where `ok` accepts every
    `c.symName f`, `inj` and `Lblite` (`HeadsOK`).

  Consequences:
  - `rootedListsB_holds`: `rootedListsB c` for every `c` (at `ok` accepting every name), the
    premise `hr` of `model_with_eqns`.
  - `nameFreeB_of_unnumbered`: `nameFreeB c ns` for names that are no symbol's of the semantics,
    none of them `inj` or `Lblite`; with `nameFree_of_decided`, `premise_symbols`: every symbol a
    premise holds is named by a symbol of the semantics, or is `inj` or `Lblite`.
  - At the account's arm for generated equations (`genEqClassOK_cases`): a constructor argument's
    projection it accepts is free of the theory and resolves to no constant
    (`nameFree_of_argProj`, `argProj_free_of_genEqClassOK`), and `model_with_eqns_argProj` is
    `model_with_eqns_step` at such names with no decided premise.
-/
import KcoreSpec.GenEqsNames

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

namespace Walk

open KoreAML (P)

variable (ok : String → Bool)

/-- The symbol, where it is a symbol `.symbol n`, has a name `ok` accepts. -/
def symOK : KoreAML.Sym → Bool
  | .symbol n => ok n
  | _ => true

/-- Every application of the pattern has a rooted left side (`lhsB`), and every symbol `.symbol n`
it holds has a name `ok` accepts. -/
def good : P → Bool
  | .application a b => lhsB a && good a && good b
  | .implication a b => good a && good b
  | .existential _ a => good a
  | .mu _ a => good a
  | .symbol σ => symOK ok σ
  | _ => true

variable {ok}

@[simp] theorem good_app (a b : P) : good ok (a ⬝ b) = (lhsB a && good ok a && good ok b) := rfl
@[simp] theorem good_imp (a b : P) : good ok (a ⇒ b) = (good ok a && good ok b) := rfl
@[simp] theorem good_ex (x : EVar) (a : P) : good ok (.existential x a) = good ok a := rfl
@[simp] theorem good_mu (X : SVar) (a : P) : good ok (.mu X a) = good ok a := rfl
@[simp] theorem good_bot : good ok (⊥ : P) = true := rfl
@[simp] theorem good_evar (x : EVar) : good ok (.evar x : P) = true := rfl
@[simp] theorem good_svar (X : SVar) : good ok (.svar X : P) = true := rfl
@[simp] theorem good_symbol (σ : KoreAML.Sym) : good ok (.symbol σ : P) = symOK ok σ := rfl
@[simp] theorem symOK_symbol (n : String) : symOK ok (.symbol n) = ok n := rfl
@[simp] theorem symOK_defined : symOK ok (HasDefined.defined : KoreAML.Sym) = true := rfl
@[simp] theorem symOK_sort (n : String) : symOK ok (.sort n) = true := rfl
@[simp] theorem symOK_inh : symOK ok .inh = true := rfl
@[simp] theorem symOK_sortSort : symOK ok .sortSort = true := rfl
@[simp] theorem symOK_ceil : symOK ok .ceil = true := rfl
@[simp] theorem symOK_next : symOK ok .next = true := rfl
@[simp] theorem symOK_dv (l : String) : symOK ok (.dv l) = true := rfl
@[simp] theorem symOK_str (l : String) : symOK ok (.str l) = true := rfl
@[simp] theorem symOK_untranslated (l : String) : symOK ok (.untranslated l) = true := rfl
@[simp] theorem chainB_defined_app (a b : P) :
    chainB ((.symbol HasDefined.defined : P) ⬝ a ⬝ b) = false := rfl
@[simp] theorem chainB_untranslated (l : String) : chainB (.symbol (.untranslated l) : P) = true := rfl
@[simp] theorem chainB_str (l : String) : chainB (.symbol (.str l) : P) = true := rfl
@[simp] theorem chainB_sortSort : chainB (.symbol .sortSort : P) = true := rfl

/-- A good pattern is rooted. -/
theorem good_rooted : ∀ {φ : P}, good ok φ = true → rootedB φ = true
  | .application a b, h => by
    simp only [good_app, Bool.and_eq_true] at h
    simp only [rootedB_app, Bool.and_eq_true]
    exact ⟨⟨h.1.1, good_rooted h.1.2⟩, good_rooted h.2⟩
  | .implication a b, h => by
    simp only [good_imp, Bool.and_eq_true] at h
    simp only [rootedB_imp, Bool.and_eq_true]
    exact ⟨good_rooted h.1, good_rooted h.2⟩
  | .existential _ a, h => good_rooted (φ := a) h
  | .mu _ a, h => good_rooted (φ := a) h
  | .symbol _, _ => rfl
  | .evar _, _ => rfl
  | .svar _, _ => rfl
  | .bottom, _ => rfl

/-- A good pattern's symbols are accepted. -/
theorem good_syms : ∀ {φ : P}, good ok φ = true → ∀ σ ∈ psyms φ, symOK ok σ = true
  | .application a b, h, σ, hσ => by
    simp only [good_app, Bool.and_eq_true] at h
    rcases List.mem_append.mp hσ with hσ | hσ
    · exact good_syms h.1.2 σ hσ
    · exact good_syms h.2 σ hσ
  | .implication a b, h, σ, hσ => by
    simp only [good_imp, Bool.and_eq_true] at h
    rcases List.mem_append.mp hσ with hσ | hσ
    · exact good_syms h.1 σ hσ
    · exact good_syms h.2 σ hσ
  | .existential _ a, h, σ, hσ => good_syms (φ := a) h σ hσ
  | .mu _ a, h, σ, hσ => good_syms (φ := a) h σ hσ
  | .symbol τ, h, σ, hσ => by
    rw [List.mem_singleton.mp hσ]; exact h
  | .evar _, _, _, hσ => nomatch hσ
  | .svar _, _, _, hσ => nomatch hσ
  | .bottom, _, _, hσ => nomatch hσ

/-! ## The connectives -/

theorem good_neg (a : P) : good ok (∼a) = good ok a := by simp [Pattern.negation]

theorem good_or (a b : P) : good ok (a ⋁ b) = (good ok a && good ok b) := by
  simp [Pattern.disjunction, Pattern.negation]

theorem good_and (a b : P) : good ok (a ⋀ b) = (good ok a && good ok b) := by
  simp [Pattern.conjunction, Pattern.disjunction, Pattern.negation]

theorem good_ceil (a : P) : good ok ⌈a⌉ = good ok a := by simp

theorem good_total (a : P) : good ok (ML.total a) = good ok a := by
  simp [ML.total, Pattern.negation]

theorem good_eq (a b : P) : good ok (a ≡ b) = (good ok a && good ok b) := by
  simp only [ML.equal, ML.total, Pattern.equivalence, Pattern.conjunction, Pattern.disjunction,
    Pattern.negation, good_app, good_imp, good_symbol, good_bot, lhsB_symbol, symOK_defined]
  cases good ok a <;> cases good ok b <;> rfl

theorem good_member (x : EVar) (a : P) : good ok (x ∈∈ a) = good ok a := by
  simp [ML.member]

theorem good_included (a b : P) : good ok (a ⊆⊆ b) = (good ok a && good ok b) := by
  simp [ML.included, ML.total, Pattern.negation]

theorem good_forall (x : EVar) (a : P) : good ok (∀∀ x a) = good ok a := by
  simp [Pattern.universal, Pattern.negation]

theorem good_top : good ok (⊤ : P) = true := rfl

theorem good_inhOf (s : P) : good ok (KoreAML.inhOf s) = good ok s := by
  simp [KoreAML.inhOf, KoreAML.sym]

theorem good_sNot (s a : P) : good ok (KoreAML.sNot s a) = (good ok a && good ok s) := by
  simp only [KoreAML.sNot, good_and, good_neg, good_inhOf]

theorem good_sAnd (a b : P) : good ok (KoreAML.sAnd a b) = (good ok a && good ok b) := good_and a b

theorem good_sOr (s a b : P) : good ok (KoreAML.sOr s a b) = (good ok a && good ok b && good ok s) := by
  simp only [KoreAML.sOr, good_sNot, good_sAnd]
  cases good ok a <;> cases good ok b <;> cases good ok s <;> rfl

theorem good_sImp (s a b : P) : good ok (KoreAML.sImp s a b) = (good ok a && good ok b && good ok s) := by
  simp only [KoreAML.sImp, good_sOr, good_sNot]
  cases good ok a <;> cases good ok b <;> cases good ok s <;> rfl

theorem good_sIff (s a b : P) : good ok (KoreAML.sIff s a b) = (good ok a && good ok b && good ok s) := by
  simp only [KoreAML.sIff, good_sAnd, good_sImp]
  cases good ok a <;> cases good ok b <;> cases good ok s <;> rfl

theorem good_sExists (x : EVar) (s a : P) : good ok (KoreAML.sExists x s a) = (good ok s && good ok a) := by
  simp only [KoreAML.sExists, good_ex, good_and, good_member, good_inhOf]

theorem good_sForall (s : P) (x : EVar) (s' a : P) :
    good ok (KoreAML.sForall s x s' a) = (good ok s' && good ok a && good ok s) := by
  simp only [KoreAML.sForall, good_sNot, good_sExists]
  cases good ok a <;> cases good ok s <;> cases good ok s' <;> rfl

theorem good_sTop (s : P) : good ok (KoreAML.sTop s) = good ok s := by
  simp only [KoreAML.sTop, good_sExists, good_evar, Bool.and_true]

theorem good_sBot (s : P) : good ok (KoreAML.sBot s) = good ok s := by
  simp only [KoreAML.sBot, good_sNot, good_sTop, Bool.and_self]

theorem good_sCeil (s s' a : P) : good ok (KoreAML.sCeil s s' a) = (good ok s && good ok s' && good ok a) := by
  simp [KoreAML.sCeil, KoreAML.sym]

theorem good_sFloor (s s' a : P) : good ok (KoreAML.sFloor s s' a) = (good ok s && good ok s' && good ok a) := by
  simp only [KoreAML.sFloor, good_sNot, good_sCeil]
  cases good ok a <;> cases good ok s <;> cases good ok s' <;> rfl

theorem good_sEquals (s s' a b : P) :
    good ok (KoreAML.sEquals s s' a b) = (good ok s && good ok s' && good ok a && good ok b) := by
  simp only [KoreAML.sEquals, good_sFloor, good_sIff]
  cases good ok a <;> cases good ok b <;> cases good ok s <;> cases good ok s' <;> rfl

theorem good_sIn (s s' a b : P) :
    good ok (KoreAML.sIn s s' a b) = (good ok s && good ok s' && good ok a && good ok b) := by
  simp only [KoreAML.sIn, good_sCeil, good_sAnd]
  cases good ok a <;> cases good ok b <;> cases good ok s <;> cases good ok s' <;> rfl

theorem good_sNext (a : P) : good ok (KoreAML.sNext a) = good ok a := by
  simp [KoreAML.sNext, KoreAML.sym]

theorem good_sRewrites (s a b : P) :
    good ok (KoreAML.sRewrites s a b) = (good ok a && good ok b && good ok s) := by
  simp only [KoreAML.sRewrites, good_sImp, good_sNext]

/-! ## Substituting a set variable -/

theorem chainB_subst (X : SVar) (χ : P) : ∀ {a : P}, chainB a = true → chainB (a.substSvar X χ) = true
  | .symbol _, h => h
  | .application a _, h => by
    simp only [Pattern.substSvar, chainB_app] at h ⊢
    exact chainB_subst X χ h
  | .evar _, h => by cases h
  | .svar _, h => by cases h
  | .bottom, h => by cases h
  | .implication _ _, h => by cases h
  | .existential _ _, h => by cases h
  | .mu _ _, h => by cases h

theorem lhsB_subst (X : SVar) (χ : P) : ∀ {a : P}, lhsB a = true → lhsB (a.substSvar X χ) = true
  | .symbol _, h => h
  | .application a _, h => by
    simp only [Pattern.substSvar, lhsB_app] at h ⊢
    exact chainB_subst X χ h
  | .evar _, h => by cases h
  | .svar _, h => by cases h
  | .bottom, h => by cases h
  | .implication _ _, h => by cases h
  | .existential _ _, h => by cases h
  | .mu _ _, h => by cases h

/-- **Substituting a good pattern for a set variable keeps a pattern good**: the variable is never
an application's left side in a good pattern. -/
theorem good_subst (X : SVar) {χ : P} (hχ : good ok χ = true) : ∀ {φ : P}, good ok φ = true →
    good ok (φ.substSvar X χ) = true
  | .application a b, h => by
    simp only [good_app, Bool.and_eq_true] at h
    simp only [Pattern.substSvar, good_app, Bool.and_eq_true]
    exact ⟨⟨lhsB_subst X χ h.1.1, good_subst X hχ h.1.2⟩, good_subst X hχ h.2⟩
  | .implication a b, h => by
    simp only [good_imp, Bool.and_eq_true] at h
    simp only [Pattern.substSvar, good_imp, Bool.and_eq_true]
    exact ⟨good_subst X hχ h.1, good_subst X hχ h.2⟩
  | .existential _ a, h => by
    simp only [Pattern.substSvar, good_ex]
    exact good_subst X hχ (φ := a) h
  | .mu Y a, h => by
    simp only [Pattern.substSvar]
    split
    · exact h
    · exact good_subst X hχ (φ := a) h
  | .svar Y, _ => by
    simp only [Pattern.substSvar]
    split
    · exact hχ
    · rfl
  | .symbol _, h => h
  | .evar _, _ => rfl
  | .bottom, _ => rfl

theorem good_sNu (s : P) (X : SVar) (a : P) (hs : good ok s = true) (ha : good ok a = true) :
    good ok (KoreAML.sNu s X a) = true := by
  simp only [KoreAML.sNu, good_sNot, good_mu, hs, Bool.and_true]
  exact good_subst X (by simp only [good_sNot, good_svar, hs, Bool.and_self]) ha

/-! ## Lists of patterns -/

theorem good_appList : ∀ (φs : List P) (h : P), chainB h = true → good ok h = true →
    (∀ φ ∈ φs, good ok φ = true) →
    chainB (KoreAML.appList h φs) = true ∧ good ok (KoreAML.appList h φs) = true
  | [], _, hc, hg, _ => ⟨hc, hg⟩
  | φ :: φs, h, hc, hg, hφ => by
    rw [KoreAML.appList]
    refine good_appList φs (h ⬝ φ) hc ?_ (fun x hx => hφ x (List.mem_cons_of_mem _ hx))
    rw [good_app, lhsB_of_chain hc, hg, hφ φ (List.mem_cons_self ..)]
    rfl

theorem good_conjList : ∀ (φs : List P), (∀ φ ∈ φs, good ok φ = true) → good ok (KoreAML.conjList φs) = true
  | [], _ => rfl
  | [φ], h => h φ (List.mem_singleton_self _)
  | φ :: ψ :: φs, h => by
    rw [KoreAML.conjList]
    case x_1 => exact fun h => nomatch h
    rw [good_and, h φ (List.mem_cons_self ..),
      good_conjList (ψ :: φs) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem good_disjList : ∀ (φs : List P), (∀ φ ∈ φs, good ok φ = true) → good ok (KoreAML.disjList φs) = true
  | [], _ => rfl
  | [φ], h => h φ (List.mem_singleton_self _)
  | φ :: ψ :: φs, h => by
    rw [KoreAML.disjList]
    case x_1 => exact fun h => nomatch h
    rw [good_or, h φ (List.mem_cons_self ..),
      good_disjList (ψ :: φs) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem good_guarded (gs : List P) (φ : P) (hg : ∀ g ∈ gs, good ok g = true) (hφ : good ok φ = true) :
    good ok (KoreAML.guarded gs φ) = true := by
  unfold KoreAML.guarded
  split
  · exact hφ
  · rw [good_imp, good_conjList _ hg, hφ]; rfl

/-! ## The translation -/

open KoreAML in
mutual
theorem good_trSort (t : VarTable) : ∀ (s : Kore.KSort), good ok (trSort t s) = true
  | .var _ => rfl
  | .ctor _ args => (good_trSortApp t args _ rfl rfl).2
theorem good_trSortApp (t : VarTable) : ∀ (ss : List Kore.KSort) (acc : P), chainB acc = true →
    good ok acc = true → chainB (trSortApp t acc ss) = true ∧ good ok (trSortApp t acc ss) = true
  | [], _, h1, h2 => ⟨h1, h2⟩
  | s :: ss, acc, h1, h2 => by
    rw [trSortApp]
    refine good_trSortApp t ss _ (by rw [chainB_app]; exact h1) ?_
    rw [good_app, lhsB_of_chain h1, h2, good_trSort t s]; rfl
end

theorem chainB_sym (σ : KoreAML.Sym) (h : σ ≠ HasDefined.defined) : chainB (KoreAML.sym σ) = true := by
  unfold KoreAML.sym chainB root
  cases σ <;> first | rfl | exact absurd rfl h

mutual
/-- The application heads of a KORE pattern have names `ok` accepts. -/
def kok (ok : String → Bool) : Kore.Pattern → Bool
  | .var _ => true
  | .app h _ ps => ok h.ident.name && kokL ok ps
  | .string _ => true
  | .top _ => true
  | .bottom _ => true
  | .not _ p => kok ok p
  | .and _ ps => kokL ok ps
  | .or _ ps => kokL ok ps
  | .implies _ p q => kok ok p && kok ok q
  | .iff _ p q => kok ok p && kok ok q
  | .exist _ _ p => kok ok p
  | .forall _ _ p => kok ok p
  | .mu _ p => kok ok p
  | .nu _ p => kok ok p
  | .ceil _ _ p => kok ok p
  | .floor _ _ p => kok ok p
  | .equals _ _ p q => kok ok p && kok ok q
  | .in _ _ p q => kok ok p && kok ok q
  | .next _ p => kok ok p
  | .rewrites _ p q => kok ok p && kok ok q
  | .dv _ _ => true
  | .leftAssoc h _ ps => ok h.ident.name && kokL ok ps
  | .rightAssoc h _ ps => ok h.ident.name && kokL ok ps
  termination_by structural p => p
def kokL (ok : String → Bool) : List Kore.Pattern → Bool
  | [] => true
  | p :: ps => kok ok p && kokL ok ps
  termination_by structural ps => ps
end

theorem kokL_iff : ∀ (ps : List Kore.Pattern), kokL ok ps = true ↔ ∀ p ∈ ps, kok ok p = true
  | [] => by simp [kokL]
  | p :: ps => by simp [kokL, kokL_iff ps]

open KoreAML in
mutual
/-- **The translation of a KORE pattern whose heads `ok` accepts is good.** -/
theorem good_tr (ctx : Ctx) : ∀ (p : Kore.Pattern), kok ok p = true → good ok (tr ctx p) = true
  | .var (.evar _), _ => by rw [tr]; rfl
  | .var (.svar _), _ => by rw [tr]; rfl
  | .app h ss ps, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr]
    split
    · rfl
    · have hs := good_trSortApp (ok := ok) ctx.vars ss (sym (.symbol h.ident.name)) rfl
        (by simp [sym, hk.1])
      exact (good_trArgs ctx ps _ hs.1 hs.2 hk.2).2
  | .string _, _ => by rw [tr]; rfl
  | .top s, _ => by rw [tr, good_sTop, good_trSort]
  | .bottom s, _ => by rw [tr, good_sBot, good_trSort]
  | .not s p, hk => by
    rw [tr, good_sNot, good_trSort, good_tr ctx p hk]; rfl
  | .and s ps, hk => by rw [tr]; exact good_trAndList ctx ps _ (good_trSort _ s) hk
  | .or s ps, hk => by rw [tr]; exact good_trOrList ctx ps _ (good_trSort _ s) hk
  | .implies s p q, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr, good_sImp, good_trSort, good_tr ctx p hk.1, good_tr ctx q hk.2]; rfl
  | .iff s p q, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr, good_sIff, good_trSort, good_tr ctx p hk.1, good_tr ctx q hk.2]; rfl
  | .exist _ x p, hk => by
    rw [tr, good_sExists, good_trSort, good_tr ctx p hk]; rfl
  | .forall s x p, hk => by
    rw [tr, good_sForall, good_trSort, good_trSort, good_tr ctx p hk]; rfl
  | .mu X p, hk => by rw [tr, good_mu]; exact good_tr ctx p hk
  | .nu X p, hk => by rw [tr]; exact good_sNu _ _ _ (good_trSort _ _) (good_tr ctx p hk)
  | .ceil s s' p, hk => by
    rw [tr, good_sCeil, good_trSort, good_trSort, good_tr ctx p hk]; rfl
  | .floor s s' p, hk => by
    rw [tr, good_sFloor, good_trSort, good_trSort, good_tr ctx p hk]; rfl
  | .equals s s' p q, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr, good_sEquals, good_trSort, good_trSort, good_tr ctx p hk.1, good_tr ctx q hk.2]; rfl
  | .in s s' p q, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr, good_sIn, good_trSort, good_trSort, good_tr ctx p hk.1, good_tr ctx q hk.2]; rfl
  | .next _ p, hk => by rw [tr, good_sNext]; exact good_tr ctx p hk
  | .rewrites s p q, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr, good_sRewrites, good_trSort, good_tr ctx p hk.1, good_tr ctx q hk.2]; rfl
  | .dv s _, _ => by
    rw [tr, good_app, good_trSort]; rfl
  | .leftAssoc h ss ps, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr]
    have hs := good_trSortApp (ok := ok) ctx.vars ss (sym (.symbol h.ident.name)) rfl
      (by simp [sym, hk.1])
    exact good_trLeftAssoc ctx ps _ hs.1 hs.2 hk.2
  | .rightAssoc h ss ps, hk => by
    simp only [kok, Bool.and_eq_true] at hk
    rw [tr]
    have hs := good_trSortApp (ok := ok) ctx.vars ss (sym (.symbol h.ident.name)) rfl
      (by simp [sym, hk.1])
    exact good_trRightAssoc ctx ps _ hs.1 hs.2 hk.2
theorem good_trArgs (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (acc : P), chainB acc = true →
    good ok acc = true → kokL ok ps = true →
    chainB (trArgs ctx acc ps) = true ∧ good ok (trArgs ctx acc ps) = true
  | [], _, h1, h2, _ => ⟨h1, h2⟩
  | p :: ps, acc, h1, h2, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    rw [trArgs]
    refine good_trArgs ctx ps _ (by rw [chainB_app]; exact h1) ?_ hk.2
    rw [good_app, lhsB_of_chain h1, h2, good_tr ctx p hk.1]; rfl
theorem good_trAndList (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (s : P), good ok s = true →
    kokL ok ps = true → good ok (trAndList ctx s ps) = true
  | [], s, hs, _ => by rw [trAndList, good_sTop, hs]
  | [p], _, _, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    rw [trAndList]; exact good_tr ctx p hk.1
  | p :: q :: ps, s, hs, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    have ih := good_trAndList ctx (q :: ps) s hs (by simp only [kokL, Bool.and_eq_true]; exact hk.2)
    rw [trAndList]
    rw [good_sAnd, good_tr ctx p hk.1, ih]; rfl
theorem good_trOrList (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (s : P), good ok s = true →
    kokL ok ps = true → good ok (trOrList ctx s ps) = true
  | [], s, hs, _ => by rw [trOrList, good_sBot, hs]
  | [p], _, _, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    rw [trOrList]; exact good_tr ctx p hk.1
  | p :: q :: ps, s, hs, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    have ih := good_trOrList ctx (q :: ps) s hs (by simp only [kokL, Bool.and_eq_true]; exact hk.2)
    rw [trOrList]
    rw [good_sOr, good_tr ctx p hk.1, ih, hs]; rfl
theorem good_trLeftAssoc (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (head : P), chainB head = true →
    good ok head = true → kokL ok ps = true → good ok (trLeftAssoc ctx head ps) = true
  | [], _, _, h2, _ => by rw [trLeftAssoc]; exact h2
  | p :: ps, head, h1, h2, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    rw [trLeftAssoc]
    exact good_trLeftAssocRest ctx ps head _ h1 h2 (good_tr ctx p hk.1) hk.2
theorem good_trLeftAssocRest (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (head acc : P), chainB head = true →
    good ok head = true → good ok acc = true → kokL ok ps = true →
    good ok (trLeftAssocRest ctx head acc ps) = true
  | [], _, _, _, _, h3, _ => by rw [trLeftAssocRest]; exact h3
  | p :: ps, head, acc, h1, h2, h3, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    rw [trLeftAssocRest]
    refine good_trLeftAssocRest ctx ps head _ h1 h2 ?_ hk.2
    rw [good_app, good_app, lhsB_app, h1, lhsB_of_chain h1, h2, h3, good_tr ctx p hk.1]; rfl
theorem good_trRightAssoc (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (head : P), chainB head = true →
    good ok head = true → kokL ok ps = true → good ok (trRightAssoc ctx head ps) = true
  | [], _, _, h2, _ => by rw [trRightAssoc]; exact h2
  | [p], _, _, _, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    rw [trRightAssoc]; exact good_tr ctx p hk.1
  | p :: q :: ps, head, h1, h2, hk => by
    simp only [kokL, Bool.and_eq_true] at hk
    have ih := good_trRightAssoc ctx (q :: ps) head h1 h2 (by simp only [kokL, Bool.and_eq_true]; exact hk.2)
    rw [trRightAssoc]
    rw [good_app, good_app, lhsB_app, h1, lhsB_of_chain h1, h2, good_tr ctx p hk.1, ih]; rfl
end

/-! ## The KORE the semantics writes -/

/-- `ok` accepts the name of every symbol of the semantics, and `inj` and `Lblite`. -/
def HeadsOK (c : Semantics) (ok : String → Bool) : Prop :=
  (∀ f, ok (c.symName f) = true) ∧ ok "inj" = true ∧ ok "Lblite" = true

/-- A sentence that is an axiom has a pattern whose heads `ok` accepts. -/
def sok (ok : String → Bool) : Kore.Sentence → Bool
  | .axiom a => kok ok a.pattern
  | _ => true

theorem kokL_append (a b : List Kore.Pattern) : kokL ok (a ++ b) = (kokL ok a && kokL ok b) := by
  induction a with
  | nil => simp [kokL]
  | cons p ps ih => simp [kokL, ih, Bool.and_assoc]

theorem kokL_of (l : List Kore.Pattern) (h : ∀ p ∈ l, kok ok p = true) : kokL ok l = true :=
  (kokL_iff l).mpr h

theorem kokL_vars (xs : List Kore.EVar) : kokL ok (KoreAML.vars xs) = true :=
  kokL_of _ fun p hp => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
    rfl

theorem kok_foldr_exist {α : Type} (s : Kore.KSort) (g : α → Kore.EVar) (body : Kore.Pattern) :
    ∀ (l : List α), kok ok (l.foldr (fun v p => .exist s (g v) p) body) = kok ok body
  | [] => rfl
  | _ :: l => by rw [List.foldr_cons, kok]; exact kok_foldr_exist s g body l

theorem kok_existsAll (s : Kore.KSort) (bs : List Kore.EVar) (body : Kore.Pattern) :
    kok ok (KoreAML.existsAll s bs body) = kok ok body :=
  kok_foldr_exist s (fun b => b) body bs

theorem kok_anyOf : ∀ (l : List Kore.Pattern), (∀ p ∈ l, kok ok p = true) → kok ok (KoreAML.anyOf l) = true
  | [], _ => rfl
  | p :: l, h => by
    simp only [KoreAML.anyOf, kok, kokL, h p (List.mem_cons_self ..),
      kok_anyOf l (fun x hx => h x (List.mem_cons_of_mem _ hx)), Bool.and_self]

theorem kok_anyOfC (S : Kore.KSort) : ∀ (l : List Kore.Pattern), (∀ p ∈ l, kok ok p = true) →
    kok ok (anyOfC S l) = true
  | [], _ => rfl
  | p :: l, h => by
    simp only [anyOfC, kok, kokL, h p (List.mem_cons_self ..),
      kok_anyOfC S l (fun x hx => h x (List.mem_cons_of_mem _ hx)), Bool.and_self]

theorem kok_argsConj : ∀ (i : Nat) (l : List (String × Kore.Pattern)), (∀ x ∈ l, kok ok x.2 = true) →
    kok ok (KoreAML.argsConj i l) = true
  | _, [], _ => rfl
  | i, (s, p) :: rest, h => by
    simp only [KoreAML.argsConj, kok, kokL, KoreAML.ev, h (s, p) (List.mem_cons_self ..),
      kok_argsConj (i + 1) rest (fun x hx => h x (List.mem_cons_of_mem _ hx)), Bool.and_self]

section Sem

variable {c : Semantics}

mutual
theorem kok_term (H : HeadsOK c ok) (vs : List KoreAML.Var) : ∀ (t : Term), kok ok (Term.kore c vs t) = true
  | .var _ => by rw [Term.kore]; rfl
  | .app f ts => by
    rw [Term.kore]
    split
    · simp only [kok, H.2.2, kok_terms H vs ts, Bool.and_self]
    · simp only [kok, H.1 f, kok_terms H vs ts, Bool.and_self]
  | .inj a b t => by
    rw [Term.kore]
    simp only [KoreAML.injP, kok, kokL, H.2.1, kok_term H vs t, Bool.and_self]
  | .as t i => by
    rw [Term.kore]
    simp only [kok, kokL, kok_term H vs t, KoreAML.varAt, Bool.and_self]
  | .dv _ _ => by rw [Term.kore]; rfl
theorem kok_terms (H : HeadsOK c ok) (vs : List KoreAML.Var) : ∀ (ts : List Term),
    kokL ok (Term.koreList c vs ts) = true
  | [] => by rw [Term.koreList]; rfl
  | t :: ts => by rw [Term.koreList, kokL, kok_term H vs t, kok_terms H vs ts]; rfl
end

theorem kok_terms_mem (H : HeadsOK c ok) (vs : List KoreAML.Var) (ts : List Term) :
    ∀ p ∈ Term.koreList c vs ts, kok ok p = true :=
  (kokL_iff _).mp (kok_terms H vs ts)

theorem kok_reqPat (H : HeadsOK c ok) (S : Kore.KSort) (vs : List KoreAML.Var) (r : Option Term) :
    kok ok (reqPat S (r.map (Term.kore c vs))) = true := by
  cases r with
  | none => rfl
  | some t => simp only [Option.map_some, reqPat, kok, kok_term H vs t, Bool.and_true]

theorem kok_cond (H : HeadsOK c ok) (S : Kore.KSort) : ∀ (p : Cond) (vs : List KoreAML.Var),
    kok ok (Cond.kore c vs S p) = true
  | .top, _ => rfl
  | .bot, _ => rfl
  | .not p, vs => by rw [Cond.kore, kok]; exact kok_cond H S p vs
  | .and p q, vs => by
    simp only [Cond.kore, kok, kokL, kok_cond H S p vs, kok_cond H S q vs, Bool.and_self]
  | .or p q, vs => by
    simp only [Cond.kore, kok, kokL, kok_cond H S p vs, kok_cond H S q vs, Bool.and_self]
  | .implies p q, vs => by
    simp only [Cond.kore, kok, kok_cond H S p vs, kok_cond H S q vs, Bool.and_self]
  | .ceil _ t, vs => by simp only [Cond.kore, kok, kok_term H vs t]
  | .equals _ t u, vs => by simp only [Cond.kore, kok, kok_term H vs t, kok_term H vs u, Bool.and_self]
  | .mem _ t u, vs => by simp only [Cond.kore, kok, kok_term H vs t, kok_term H vs u, Bool.and_self]
  | .exMatch ys s p t body, vs => by
    simp only [Cond.kore, kok_existsAll, kok, kokL, kok_term H, kok_cond H S body, Bool.and_self]
  | .ex _ body, vs => by simp only [Cond.kore, kok]; exact kok_cond H S body _
  | .all _ body, vs => by simp only [Cond.kore, kok]; exact kok_cond H S body _

theorem kok_condConj (H : HeadsOK c ok) (vs : List KoreAML.Var) (S : Kore.KSort) (p : Cond) :
    kokL ok (Cond.conj c vs S p) = true := by
  unfold Cond.conj
  split
  · rfl
  · simp only [kokL, kok_cond H S p vs, Bool.and_self]

theorem kok_premise (H : HeadsOK c ok) (vs : List KoreAML.Var) (args : List String) (req : Option Term)
    (pats : List Term) : kok ok (premise args (req.map (Term.kore c vs)) (Term.koreList c vs pats)) = true := by
  simp only [premise, kok, kokL, kok_reqPat H, Bool.true_and, Bool.and_true]
  exact kok_argsConj 0 _ fun x hx => kok_terms_mem H vs pats x.2 (List.of_mem_zip hx).2

theorem kok_withPre (H : HeadsOK c ok) (vs : List KoreAML.Var) (cl : Clause) {prem : Kore.Pattern}
    (hp : kok ok prem = true) : kok ok (withPre c vs cl prem) = true := by
  unfold withPre
  split
  · exact hp
  · simp only [kok, kokL, hp, kok_cond H, Bool.and_self]

theorem kok_exclusion (H : HeadsOK c ok) (f : Fn) (cl : Clause) (cp : ClausePres) :
    kok ok (exclusion c f cl cp) = true := by
  unfold exclusion
  rw [kok_existsAll]
  exact kok_withPre H _ cl (kok_premise H _ _ _ _)

theorem kok_clauseRhs (H : HeadsOK c ok) (f : Fn) (cl : Clause) :
    kok ok (clauseRhs c f cl).1 = true ∧ kok ok (clauseRhs c f cl).2 = true := by
  unfold clauseRhs
  split
  · exact ⟨kok_term H _ _, kok_reqPat H _ _ _⟩
  · refine ⟨?_, rfl⟩
    rw [kok_foldr_exist]
    simp only [kok, kokL_append, kokL, kok_term H, kok_reqPat H, kok_condConj H, Bool.and_self]

theorem sok_eqnSentence (H : HeadsOK c ok) (f : Fn) {prem rhs ens : Kore.Pattern} (h1 : kok ok prem = true)
    (h2 : kok ok rhs = true) (h3 : kok ok ens = true) : sok ok (eqnSentence c f prem rhs ens) = true := by
  simp only [eqnSentence, KoreAML.equationAx, KoreAML.axiomR, sok, kok, kokL, KoreAML.ap, H.1 f.label,
    kokL_vars, h1, h2, h3, Bool.and_self]

theorem sok_prioEquation (H : HeadsOK c ok) (f : Fn) (cl : Clause) : sok ok (prioEquation c f cl) = true := by
  have hr := kok_clauseRhs H f cl
  unfold prioEquation clauseEquation competingEquation
  split
  · exact sok_eqnSentence H f (kok_withPre H _ cl (kok_premise H _ _ _ _)) hr.1 hr.2
  · refine sok_eqnSentence H f ?_ hr.1 hr.2
    simp only [kok, kokL, kok_withPre H _ cl (kok_premise H _ _ _ _), Bool.and_true]
    exact kok_anyOf _ fun p hp => by
      obtain ⟨cl', -, rfl⟩ := List.mem_map.mp hp
      exact kok_exclusion H f cl' _

theorem kok_applies (H : HeadsOK c ok) (r : Rule) (rp : RulePres) : kok ok (applies c r rp) = true := by
  unfold applies
  rw [kok_existsAll]
  simp only [kok, kokL_append, kokL, kok_term H, kok_reqPat H, kok_condConj H, Bool.and_self]

theorem kok_ruleRight (H : HeadsOK c ok) (r : Rule) : kok ok (ruleRight c r) = true := by
  unfold ruleRight
  rw [kok_foldr_exist]
  simp only [kok, kokL_append, kokL, kok_term H, kok_reqPat H, kok_condConj H, Bool.and_self]

theorem kok_prioRuleK (H : HeadsOK c ok) (r : Rule) : kok ok (prioRuleK c r) = true := by
  have hR := kok_ruleRight H r
  unfold prioRuleK
  dsimp only
  split
  · simp only [kok, kokL_append, kokL, kok_term H, kok_reqPat H, kok_condConj H, hR, Bool.and_self]
  · simp only [kok, kokL_append, kokL, kok_term H, kok_reqPat H, kok_condConj H, hR, Bool.and_self,
      Bool.and_true]
    exact kok_anyOfC _ _ fun p hp => by
      obtain ⟨r', -, rfl⟩ := List.mem_map.mp hp
      exact kok_applies H r' _

end Sem

/-! ## The items of the theory's lists -/

theorem good_sortP (n : String) : good ok (sortP n) = true := rfl
theorem good_consSortP (n : String) : good ok (KoreAML.Cons.sortP n) = true := rfl
theorem chainB_symP (n : String) : chainB (symP n) = true := rfl
theorem good_symP {n : String} (h : ok n = true) : good ok (symP n) = true := h

theorem good_guardOf (t : KoreAML.VarTable) (k : KoreAML.VarKey) : good ok (KoreAML.guardOf t k) = true := by
  cases k <;> simp only [KoreAML.guardOf, KoreAML.sortGuard, KoreAML.sortsDomain, good_member, good_inhOf,
    good_included, good_svar, good_trSort, Bool.and_self] <;> rfl

/-- **A translated axiom is good** where its pattern's heads are accepted. -/
theorem good_trAxiom (decls : List KoreAML.SymbolDecl) (aliases : List String) (ad : KoreAML.AxiomDecl)
    (h : kok ok ad.ax.pattern = true) : good ok (KoreAML.trAxiom decls aliases ad).pat = true := by
  simp only [KoreAML.trAxiom]
  rw [good_imp, good_conjList _ (fun g hg => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
    exact good_guardOf _ _), good_eq, good_tr _ _ h]
  split <;> simp [good_inhOf, good_trSort, KoreAML.sym]

theorem good_kernelItems (ss : List Kore.Sentence) (h : ∀ s ∈ ss, sok ok s = true) :
    ∀ it ∈ kernelItems ss, good ok it.pat = true := by
  intro it hit
  unfold kernelItems at hit
  obtain ⟨s, hs, hs'⟩ := List.mem_filterMap.mp hit
  have hk := h s hs
  cases s <;> simp only [Option.some.injEq, reduceCtorEq] at hs'
  subst hs'
  exact good_trAxiom _ _ _ hk

/-- A generator's head is accepted. -/
def genOK (ok : String → Bool) : KoreAML.Gen → Bool
  | .ctor k => ok k.name
  | .inj _ => ok "inj"

theorem good_genPat (N : String) (g : KoreAML.Gen) (hg : genOK ok g = true) (args : List P)
    (ha : ∀ a ∈ args, good ok a = true) : good ok (KoreAML.Cons.genPat N g args) = true := by
  cases g with
  | ctor k => exact (good_appList args (KoreAML.sym (.symbol k.name)) rfl hg ha).2
  | inj A =>
    refine (good_appList _ (KoreAML.sym (.symbol "inj")) rfl hg ?_).2
    intro a hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> rfl
    · exact ha a hm

theorem good_evars (xs : List EVar) : ∀ a ∈ xs.map (.evar : EVar → P), good ok a = true := by
  intro a ha
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
  rfl

theorem good_memGuards (xs : List EVar) (ss : List String) :
    ∀ g ∈ KoreAML.Cons.memGuards xs ss, good ok g = true := by
  intro g hg
  obtain ⟨⟨x, s⟩, -, rfl⟩ := List.mem_map.mp hg
  simp only [good_member, good_inhOf]; rfl

theorem good_liesP (hi : ok "inj" = true) (A B : String) (x : P) (hx : good ok x = true) (z : EVar) :
    good ok (KoreAML.Cons.liesP A B x z) = true := by
  simp only [KoreAML.Cons.liesP, good_sExists, good_eq, hx, good_consSortP, Bool.true_and]
  exact (good_appList _ (KoreAML.sym (.symbol "inj")) rfl hi (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> rfl)).2

theorem good_uncoveredP (hi : ok "inj" = true) (bs : List String) (covs : List (List String)) (x : List EVar)
    (z : EVar) : good ok (KoreAML.Cons.uncoveredP bs covs x z) = true := by
  refine good_conjList _ fun φ hφ => ?_
  obtain ⟨as, -, rfl⟩ := List.mem_map.mp hφ
  refine good_disjList _ fun ψ hψ => ?_
  obtain ⟨⟨⟨A, B⟩, xi⟩, -, he⟩ := List.mem_filterMap.mp hψ
  dsimp only at he
  split at he
  · cases he
  · cases he
    rw [good_neg]
    exact good_liesP hi A B _ rfl z

theorem kok_noJunk (N : String) : ∀ (seen : List (String × List String)) (gs : List KoreAML.Gen),
    (∀ g ∈ gs, genOK ok g = true) → ok "inj" = true → kokL ok (KoreAML.noJunkDisjuncts N seen gs) = true
  | _, [], _, _ => rfl
  | seen, .ctor k :: gs, h, hi => by
    rw [KoreAML.noJunkDisjuncts]
    split
    rename_i xs seen' _
    rw [kokL, kok_existsAll, kok_noJunk N seen' gs (fun g hg => h g (List.mem_cons_of_mem _ hg)) hi]
    simp only [kok, KoreAML.ap, kokL_vars, Bool.and_true]
    exact h _ (List.mem_cons_self ..)
  | seen, .inj a :: gs, h, hi => by
    rw [KoreAML.noJunkDisjuncts]
    split
    rename_i n seen' _
    rw [kokL, kok_noJunk N seen' gs (fun g hg => h g (List.mem_cons_of_mem _ hg)) hi]
    simp only [kok, KoreAML.injP, kokL, hi, Bool.and_self]

theorem good_injApp (hi : ok "inj" = true) {a b φ : P} (ha : good ok a = true) (hb : good ok b = true)
    (hφ : good ok φ = true) : good ok (KoreAML.appList (KoreAML.sym (.symbol "inj")) [a, b, φ]) = true :=
  (good_appList _ (KoreAML.sym (.symbol "inj")) rfl hi (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hφ)).2

section Items

variable {c : Semantics}

theorem genOK_toK (H : HeadsOK c ok) (g : Gen) : genOK ok (Gen.toK c g) = true := by
  cases g with
  | ctor k => exact H.1 k.name
  | inj _ => exact H.2.1

theorem good_symArityItem (H : HeadsOK c ok) (k : CtorSig) : good ok (symArityItem c k).pat = true := by
  unfold symArityItem
  split
  · simp only [KoreAML.arityItem, KoreAML.paramTable, List.map_nil, KoreAML.guarded, good_included,
      good_inhOf, good_trSort, Bool.and_true]
    refine (good_appList _ (KoreAML.sym (.symbol (c.symName k.name))) rfl (H.1 k.name) ?_).2
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
    rw [good_inhOf, good_trSort]
  · simp only [good_included, good_inhOf, good_sortP, Bool.and_true]
    refine (good_appList _ _ rfl (by simp only [good_app, KoreAML.sym, good_symbol, symOK_symbol, H.2.2]; rfl) ?_).2
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
    rfl

theorem good_sigItems (H : HeadsOK c ok) : ∀ it ∈ sigItems c, good ok it.pat = true := by
  intro it hit
  simp only [sigItems, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hit
  rcases hit with (((rfl | ⟨s, -, rfl⟩) | ⟨k, -, rfl⟩) | (rfl | rfl | rfl))
  · simp [KoreAML.definednessItem, definedness, good_forall]
  · simp only [KoreAML.sortConstantItem, sortDeclOf, List.map_nil, KoreAML.guarded, KoreAML.appList,
      good_sExists, good_eq]; rfl
  · exact good_symArityItem H k
  · rfl
  · rfl
  · simp only [KoreAML.nextArityItem]
    refine good_guarded _ _ (fun g hg => ?_) ?_
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hg
      rfl
    · rw [good_included, good_sNext, good_inhOf, good_trSort]; rfl

theorem good_genItem_parts (H : HeadsOK c ok) {N : String} (g : Gen) (xs : List EVar) :
    good ok (KoreAML.Cons.genPat N (Gen.toK c g) (xs.map .evar)) = true :=
  good_genPat _ _ (genOK_toK H g) _ (good_evars _)

theorem good_funItem (H : HeadsOK c ok) (N : String) (g : Gen) :
    good ok (KoreAML.Cons.funItem N (Gen.toK c g)).pat = true := by
  simp only [KoreAML.Cons.funItem]
  refine good_guarded _ _ (good_memGuards _ _) ?_
  rw [good_sExists, good_eq, good_genItem_parts H]; rfl

theorem good_funUncItem (H : HeadsOK c ok) (N : String) (g : Gen) (covs : List (List String)) :
    good ok (KoreAML.Cons.funUncItem N (Gen.toK c g) covs).pat = true := by
  simp only [KoreAML.Cons.funUncItem]
  refine good_guarded _ _ (fun x hx => ?_) ?_
  · rcases List.mem_append.mp hx with hx | hx
    · exact good_memGuards _ _ x hx
    · rw [List.mem_singleton.mp hx]; exact good_uncoveredP H.2.1 _ _ _ _
  · rw [good_sExists, good_eq, good_genItem_parts H]; rfl

theorem good_eqConj (xs ys : List EVar) :
    good ok (KoreAML.conjList ((xs.zip ys).map fun (a, b) => (.evar a ≡ .evar b : P))) = true :=
  good_conjList _ (fun φ hφ => by
    obtain ⟨⟨_, _⟩, -, rfl⟩ := List.mem_map.mp hφ
    rw [good_eq]; rfl)

theorem good_injItem (H : HeadsOK c ok) (N : String) (g : Gen) :
    good ok (KoreAML.Cons.injItem N (Gen.toK c g)).pat = true := by
  simp only [KoreAML.Cons.injItem]
  refine good_guarded _ _ (fun x hx => ?_) ?_
  · rcases List.mem_append.mp hx with hx | hx
    · exact good_memGuards _ _ x hx
    · exact good_memGuards _ _ x hx
  · rw [good_imp, good_eq, good_genItem_parts H, good_genItem_parts H, good_eqConj]; rfl

theorem good_injUncItem (H : HeadsOK c ok) (N : String) (g : Gen) (covs : List (List String)) :
    good ok (KoreAML.Cons.injUncItem N (Gen.toK c g) covs).pat = true := by
  simp only [KoreAML.Cons.injUncItem]
  refine good_guarded _ _ (fun x hx => ?_) ?_
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((hx | hx) | rfl | rfl)
    · exact good_memGuards _ _ x hx
    · exact good_memGuards _ _ x hx
    · exact good_uncoveredP H.2.1 _ _ _ _
    · exact good_uncoveredP H.2.1 _ _ _ _
  · rw [good_imp, good_eq, good_genItem_parts H, good_genItem_parts H, good_eqConj]; rfl

theorem good_distItem (H : HeadsOK c ok) (N : String) (g g' : Gen) :
    good ok (KoreAML.Cons.distItem N (Gen.toK c g) (Gen.toK c g')).pat = true := by
  simp only [KoreAML.Cons.distItem, KoreAML.notEqual]
  refine good_guarded _ _ (fun x hx => ?_) ?_
  · rcases List.mem_append.mp hx with hx | hx
    · exact good_memGuards _ _ x hx
    · exact good_memGuards _ _ x hx
  · rw [good_neg, good_eq, good_genItem_parts H, good_genItem_parts H]; rfl

theorem good_distUncItem (H : HeadsOK c ok) (N : String) (g g' : Gen) (ug ug' : Option (List (List String))) :
    good ok (KoreAML.Cons.distUncItem N (Gen.toK c g) (Gen.toK c g') ug ug').pat = true := by
  simp only [KoreAML.Cons.distUncItem, KoreAML.notEqual]
  refine good_guarded _ _ (fun x hx => ?_) ?_
  · simp only [List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact good_memGuards _ _ x hx
    · exact good_memGuards _ _ x hx
    · split at hx
      · rw [List.mem_singleton.mp hx]; exact good_uncoveredP H.2.1 _ _ _ _
      · cases hx
    · split at hx
      · rw [List.mem_singleton.mp hx]; exact good_uncoveredP H.2.1 _ _ _ _
      · cases hx
  · rw [good_neg, good_eq, good_genItem_parts H, good_genItem_parts H]; rfl

theorem good_distLbItem (hi : ok "inj" = true) (N A B : String) (lbs : List String) :
    good ok (distLbItem N A B lbs).pat = true := by
  simp only [distLbItem]
  refine good_guarded _ _ (fun x hx => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  · rw [good_imp, good_eq, good_injApp hi rfl rfl rfl, good_injApp hi rfl rfl rfl]
    rw [good_disjList _ (fun φ hφ => by
      obtain ⟨C, -, rfl⟩ := List.mem_map.mp hφ
      rw [good_sExists, good_and, good_eq, good_eq, good_injApp hi rfl rfl rfl, good_injApp hi rfl rfl rfl]; rfl)]
    rfl

theorem good_consItemsK (H : HeadsOK c ok) : ∀ it ∈ consItemsK c, good ok it.pat = true := by
  have hi := H.2.1
  intro it hit
  unfold consItemsK at hit
  simp only [List.mem_append, List.mem_flatMap, List.mem_map] at hit
  rcases hit with (((⟨N, -, hit⟩ | ⟨⟨a, b⟩, -, ⟨⟨_, e⟩, -, rfl⟩⟩) | ⟨o, -, ⟨kg, -, rfl⟩⟩) | hit)
  · rcases hit with ((⟨g, -, rfl⟩ | ⟨g, -, rfl⟩) | ⟨⟨g, g'⟩, -, hit⟩) | hit
    · split
      · exact good_funUncItem H _ _ _
      · exact good_funItem H _ _
    · split
      · exact good_injUncItem H _ _ _
      · exact good_injItem H _ _
    · cases g <;> cases g' <;> simp only at hit <;> split at hit <;> (try simp only [List.mem_singleton] at hit)
      · subst hit; exact good_distUncItem H _ _ _ _ _
      · subst hit; exact good_distItem H _ _ _
      · subst hit; exact good_distUncItem H _ _ _ _ _
      · subst hit; exact good_distItem H _ _ _
      · subst hit; exact good_distUncItem H _ _ _ _ _
      · subst hit; exact good_distItem H _ _ _
      · cases hit
      · split at hit <;> simp only [List.mem_singleton] at hit <;> subst hit
        · exact good_distItem H _ _ _
        · exact good_distLbItem hi _ _ _ _
    · split at hit
      · cases hit
      · rw [List.mem_singleton.mp hit]
        refine good_trAxiom [] [] ⟨0, "kernel", KoreAML.Cons.noJunkAx (c.sortName N) _⟩ ?_
        simp only [KoreAML.Cons.noJunkAx, kok]
        exact kok_noJunk _ _ _ (fun g hg' => by
          obtain ⟨g0, -, rfl⟩ := List.mem_map.mp hg'
          exact genOK_toK H g0) hi
  · simp only [KoreAML.Cons.cohItem]
    refine good_guarded _ _ (fun x hx => ?_) ?_
    · rw [List.mem_singleton.mp hx]; rfl
    · rw [good_eq, good_injApp hi rfl rfl (good_injApp hi rfl rfl rfl), good_injApp hi rfl rfl rfl]; rfl
  · simp only [KoreAML.Cons.ovlEqItem]
    have hlift : ∀ (A B : String) (φ : P), good ok φ = true →
        good ok (if (A == B) = true then φ else
          KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ]) = true := by
      intro A B φ hφ
      split
      · exact hφ
      · exact good_injApp hi rfl rfl hφ
    refine good_guarded _ _ (good_memGuards _ _) ?_
    rw [good_eq]
    simp only [Bool.and_eq_true]
    refine ⟨(good_appList _ (KoreAML.sym (.symbol (toK c o.sig).name)) rfl (H.1 _) ?_).2,
      hlift _ _ _ (good_appList _ (KoreAML.sym (.symbol (toK c kg).name)) rfl (H.1 _) (good_evars _)).2⟩
    intro φ hφ
    obtain ⟨⟨⟨A, B⟩, xi⟩, -, rfl⟩ := List.mem_map.mp hφ
    exact hlift _ _ _ rfl
  · unfold lawItemsK at hit
    obtain ⟨k, -, hit⟩ := List.mem_flatMap.mp hit
    have hap : ∀ (ps : List Kore.Pattern), kokL ok ps = true →
        kok ok (KoreAML.ap (c.symName k.sig.name) ps) = true := fun ps hps => by
      simp only [KoreAML.ap, kok, H.1, hps, Bool.and_self]
    split at hit
    · rcases List.mem_append.mp hit with hit | hit
      · split at hit
        · rw [List.mem_singleton.mp hit]
          refine good_trAxiom _ _ _ ?_
          simp only [assocAxK, kok, KoreAML.ev]
          simp only [hap, kokL, kok, Bool.and_true]
        · cases hit
      · split at hit
        · rw [List.mem_singleton.mp hit]
          refine good_trAxiom _ _ _ ?_
          simp only [idemAxK, kok, KoreAML.ev, Bool.and_true]
          simp only [hap, kokL, kok, Bool.and_true]
        · cases hit
    · cases hit

theorem good_fnItems (H : HeadsOK c ok) : ∀ it ∈ fnItems c, good ok it.pat = true := by
  intro it hit
  obtain ⟨f, -, hit⟩ := List.mem_flatMap.mp hit
  refine good_kernelItems _ (fun s hs => ?_) it hit
  obtain ⟨cl, -, rfl⟩ := List.mem_map.mp hs
  exact sok_prioEquation H f cl

theorem good_ruleItems (H : HeadsOK c ok) : ∀ it ∈ ruleItems c, good ok it.pat = true := by
  intro it hit
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hit
  exact good_trAxiom _ _ _ (kok_prioRuleK H r)

theorem good_foldr_sExists (table : KoreAML.VarTable) : ∀ (l : List (KoreAML.VarKey × Kore.KSort)) (body : P),
    good ok body = true →
    good ok (l.foldr (fun (k, s) φ => KoreAML.sExists (table.ev k) (KoreAML.trSort table s) φ) body) = true
  | [], _, h => h
  | (_, _) :: l, body, h => by
    rw [List.foldr_cons, good_sExists, good_trSort, good_foldr_sExists table l body h]; rfl

theorem good_closureDisjunct (aliases : List String) (offset : Nat) (y : EVar) (pat : Kore.Pattern)
    (h : kok ok pat = true) : good ok (KoreAML.closureDisjunct aliases offset y pat).2 = true := by
  unfold KoreAML.closureDisjunct
  dsimp only
  refine good_foldr_sExists _ _ _ ?_
  rw [good_and, good_member]
  split
  · simp only [kok, Bool.and_eq_true] at h
    dsimp only
    rw [good_tr _ _ h.1, good_tr _ _ h.2]; rfl
  · rfl

theorem foldl_inv_walk {α β : Type} (Pr : β → Prop) (F : β → α → β) (l : List α)
    (hF : ∀ b a, a ∈ l → Pr b → Pr (F b a)) : ∀ (init : β), Pr init → Pr (l.foldl F init) := by
  induction l with
  | nil => exact fun _ h => h
  | cons a l ih =>
    intro init h
    exact ih (fun b a' ha' hb => hF b a' (List.mem_cons_of_mem _ ha') hb) _ (hF init a (List.mem_cons_self ..) h)

theorem good_stepClosureItem (H : HeadsOK c ok) : good ok (stepClosureItem c).pat = true := by
  unfold stepClosureItem
  dsimp only
  rw [good_forall, good_included, good_sNext, good_evar, Bool.true_and]
  refine good_disjList _ (foldl_inv_walk (fun acc : List String × List P × Nat => ∀ φ ∈ acc.2.1, good ok φ = true)
    _ _ ?_ _ (fun _ h => nomatch h))
  intro b p hp hb
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
  intro ψ hψ
  rcases List.mem_append.mp hψ with hψ | hψ
  · exact hb ψ hψ
  · rw [List.mem_singleton.mp hψ]; exact good_closureDisjunct _ _ _ _ (kok_prioRuleK H r)

theorem good_collNoJunk (H : HeadsOK c ok) (k : CollSig) : good ok (collNoJunk c k) = true := by
  unfold collNoJunk
  dsimp only
  rw [good_included, good_inhOf, good_mu, good_or]
  simp only [good_sortP, Bool.true_and, good_symP (H.1 _)]
  refine (good_appList _ _ (chainB_symP _) (good_symP (H.1 _)) ?_).2
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · split <;>
    · refine (good_appList _ _ (chainB_symP _) (good_symP (H.1 _)) ?_).2
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      first | (obtain rfl | rfl := ha <;> rfl) | (subst ha; rfl)
  · rfl

theorem good_collApp (H : HeadsOK c ok) (f : Sym) (args : List P) (ha : ∀ a ∈ args, good ok a = true) :
    good ok (KoreAML.appList (symP (c.symName f)) args) = true :=
  (good_appList _ _ (chainB_symP _) (good_symP (H.1 _)) ha).2

theorem good_collAxioms (H : HeadsOK c ok) (k : CollSig) : ∀ φ ∈ collAxioms c k, good ok φ = true := by
  have hU : good ok (collU c k) = true := good_symP (H.1 _)
  have h2 : ∀ (f : Sym) (a b : P), good ok a = true → good ok b = true →
      good ok (KoreAML.appList (symP (c.symName f)) [a, b]) = true := fun f a b ha hb =>
    good_collApp H f _ (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb)
  have h1 : ∀ (f : Sym) (a : P), good ok a = true → good ok (KoreAML.appList (symP (c.symName f)) [a]) = true :=
    fun f a ha => good_collApp H f _ (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exact ha)
  have hC : ∀ a b : P, good ok a = true → good ok b = true → good ok (collC c k a b) = true := h2 _
  have hE : ∀ a b : P, good ok a = true → good ok b = true → good ok (collE c k a b) = true := h2 _
  have hI : ∀ a : P, good ok a = true → good ok (collI c k a) = true := h1 _
  have hg : ∀ (x : EVar) (s : Srt), good ok (x ∈∈ inSort c s) = true := fun x s => by rw [good_member]; rfl
  have hv : ∀ x : EVar, good ok (.evar x : P) = true := fun _ => rfl
  intro φ hφ
  unfold collAxioms at hφ
  split at hφ <;>
    simp only [mapCollAxioms, setCollAxioms, listCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
  all_goals
    rcases hφ with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [mapUnitSplitAx, mapElemNotUnitAx, mapElemAtomAx, mapDecompAx, setUnitSplitAx, setElemNotUnitAx,
      setElemAtomAx, setDecompAx, listUnitSplitAx, listElemNotUnitAx, listElemAtomAx, listElemAtomBackAx,
      listDecompAx]
    refine good_guarded _ _ (by
      intro g hg'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl | rfl <;> exact hg _ _) ?_
    simp only [good_imp, good_ceil, good_and, good_eq, good_neg, good_or, good_sExists, hU, hv,
      good_sortP, Bool.and_true, Bool.true_and, Bool.and_self]
    simp only [hC _ _ (hv _) (hv _), hE _ _ (hv _) (hv _), hI _ (hv _), Bool.and_true, Bool.true_and,
      Bool.and_self]
    try simp only [hC _ _ (hE _ _ (hv _) (hv _)) (hv _), hC _ _ (hI _ (hv _)) (hv _),
      hC _ _ (hv _) (hI _ (hv _)), Bool.and_self]

theorem good_boolClosed : good ok (boolClosed c) = true := by
  unfold boolClosed
  rw [good_included, good_or]
  simp only [den, KoreAML.den, GroundTerm.kore]
  rw [good_tr _ _ rfl, good_tr _ _ rfl]; rfl

/-- **Every item of the theory's lists is good** where `ok` accepts every name of the semantics,
`inj` and `Lblite`. -/
theorem good_lists (H : HeadsOK c ok) :
    (sigItems c ++ consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).all
      (fun it => good ok it.pat) = true ∧
    c.allColls.all (fun k => good ok (collNoJunk c k) && (collAxioms c k).all (good ok)) = true ∧
    good ok (boolClosed c) = true := by
  refine ⟨List.all_eq_true.mpr fun it hit => ?_, List.all_eq_true.mpr fun k _ => ?_, good_boolClosed⟩
  · simp only [List.mem_append, List.mem_singleton] at hit
    rcases hit with ((((hit | hit) | hit) | hit) | rfl)
    · exact good_sigItems H it hit
    · exact good_consItemsK H it hit
    · exact good_fnItems H it hit
    · exact good_ruleItems H it hit
    · exact good_stepClosureItem H
  · rw [good_collNoJunk H k, List.all_eq_true.mpr (good_collAxioms H k)]; rfl

end Items

end Walk

open Walk

/-- **Every premise of the theory's lists is rooted**, for every semantics: `rootedListsB`, the
premise `hr` of `model_with_eqns`, holds without a decision. -/
theorem rootedListsB_holds (c : Semantics) : rootedListsB c = true := by
  obtain ⟨h1, h2, h3⟩ := good_lists (ok := fun _ => true) (c := c) ⟨fun _ => rfl, rfl, rfl⟩
  simp only [rootedListsB, Bool.and_eq_true, List.all_eq_true] at h1 h2 ⊢
  refine ⟨⟨fun it hit => good_rooted (h1 it hit), fun k hk => ⟨good_rooted (h2 k hk).1, fun φ hφ =>
    good_rooted ((h2 k hk).2 φ hφ)⟩⟩, good_rooted h3⟩

/-- A good pattern at `ok` excluding the names `ns` holds none of them. -/
theorem cleanN_of_good {ns : List String} {φ : KoreAML.P} (h : good (fun n => !ns.contains n) φ = true) :
    NameFree.cleanN ns φ = true :=
  List.all_eq_true.mpr fun σ hσ =>
    (show (!NameFree.isNm ns σ) = symOK (fun n => !ns.contains n) σ by cases σ <;> rfl).trans (good_syms h σ hσ)

/-- **Names that are no symbol's of the semantics, and none of them `inj` or `Lblite`, are free
of the theory, decided** (`nameFreeB`): no symbol name of the semantics is one of them
(`symName_ne_of_unnumbered`), so every item of the lists is good at `ok` excluding them, and the
values and the symbols applied at values are named by the semantics' symbols, `inj` and
`Lblite` only. -/
theorem nameFreeB_of_unnumbered (c : Semantics) (ns : List String)
    (hn : ∀ n ∈ ns, (regSymNames ++ c.symNames).contains n = false ∧ n ≠ "" ∧ n ≠ "inj" ∧ n ≠ "Lblite") :
    nameFreeB c ns = true := by
  have hsym : ∀ f, (!ns.contains (c.symName f)) = true := fun f => by
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hm
    obtain ⟨h1, h2, -, -⟩ := hn _ (List.contains_iff_mem.mp hm)
    exact symName_ne_of_unnumbered c h1 h2 f rfl
  have hfix : ∀ m, m = "inj" ∨ m = "Lblite" → (!ns.contains m) = true := fun m hm => by
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hc
    obtain ⟨-, -, h3, h4⟩ := hn _ (List.contains_iff_mem.mp hc)
    rcases hm with rfl | rfl
    · exact h3 rfl
    · exact h4 rfl
  have H : Walk.HeadsOK c (fun n => !ns.contains n) := ⟨hsym, hfix _ (.inl rfl), hfix _ (.inr rfl)⟩
  obtain ⟨h1, h2, h3⟩ := good_lists H
  have hk : ∀ f, NameFree.kOKN c ns f = true := hsym
  have ha : ∀ f, NameFree.appOKN c ns f = true := fun f => by
    unfold NameFree.appOKN
    split
    · exact hfix _ (.inr rfl)
    · exact hk f
  simp only [nameFreeB, NameFree.listsN, NameFree.valuesN, NameFree.graphsN, Bool.and_eq_true,
    List.all_eq_true]
  simp only [Bool.and_eq_true, List.all_eq_true] at h1 h2
  refine ⟨⟨⟨⟨fun it hit => cleanN_of_good (h1 it hit), fun k hk' => ⟨cleanN_of_good (h2 k hk').1,
    fun φ hφ => cleanN_of_good ((h2 k hk').2 φ hφ)⟩⟩, cleanN_of_good h3⟩,
    ⟨⟨fun k _ => hk _, fun k _ => ⟨⟨hk _, hk _⟩, hk _⟩⟩, hfix _ (.inl rfl)⟩⟩,
    ⟨⟨fun k _ => ha _, fun k _ => ha _⟩, fun f _ => ha _⟩⟩

/-- **A constructor argument's projection that the account's arm accepts is free of the theory**:
a name with the prefix `Lblproject'Coln` that is no registry symbol's and none of the semantics'
own (the conditions `Account.genEqClassOK` checks of it) is held by no premise of `Γc c ∪ Γstep c`,
the premise `hfree` of `model_with_eqns`. -/
theorem nameFree_of_argProj (c : Semantics) (h : c.coreOK = true) {n : String}
    (hp : (KoreAML.Parse.dropPrefix? "Lblproject'Coln" n).isSome = true)
    (hr : regSymNames.contains n = false) (hs : c.symNames.contains n = false) :
    ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ :=
  nameFree_of_decided c [n] h (nameFreeB_of_unnumbered c [n] fun m hm => by
    rw [List.mem_singleton.mp hm]
    refine ⟨by rw [List.contains_append, hr, hs]; rfl, ?_, ?_, ?_⟩ <;>
      · rintro rfl; revert hp; decide) n (List.mem_singleton_self _)

/-- **The symbols the theory names.** Every symbol `.symbol n` that a premise of `Γc c ∪ Γstep c`
holds is named by a symbol of the semantics (a name of the registry or of `c.symNames`, or the
empty name of an unnumbered symbol), or is `inj` or `Lblite`. -/
theorem premise_symbols (c : Semantics) (h : c.coreOK = true) :
    ∀ φ, (Γc c ∪ Γstep c) φ → ∀ n, KoreAML.Sym.symbol n ∈ psyms φ →
      n ∈ regSymNames ++ c.symNames ∨ n = "" ∨ n = "inj" ∨ n = "Lblite" := by
  intro φ hφ n hn
  refine Classical.byContradiction fun hno => ?_
  simp only [not_or] at hno
  obtain ⟨h1, h2, h3, h4⟩ := hno
  have hfree := nameFree_of_decided c [n] h (nameFreeB_of_unnumbered c [n] fun m hm => by
    rw [List.mem_singleton.mp hm]
    exact ⟨by simpa using h1, h2, h3, h4⟩) n (List.mem_singleton_self _) φ hφ
  exact hfree hn

/-- **`model_with_eqns_step` at constructor arguments' projections the account's arm accepts**,
with no decided premise: rootedness holds of every semantics (`rootedListsB_holds`), freeness of
such names from the arm's conditions (`nameFree_of_argProj`), and they resolve to no constant
(`spareSymB_of_argProj`). -/
theorem model_with_eqns_argProj (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (N : String → Prop)
    (G : String → GroundTerm → Option GroundTerm)
    (hN : ∀ n, N n → (KoreAML.Parse.dropPrefix? "Lblproject'Coln" n).isSome = true ∧
      regSymNames.contains n = false ∧ c.symNames.contains n = false) :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ n, N n → ∀ (w v : GroundTerm) (s s' : Srt), c.sortOf w = some s → c.sortOf v = some s' →
        G n w = some v → I ⊧ᴵ (symP n ⬝ den c w ≡ den c v)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  model_with_eqns_step c h hf N G (rootedListsB_holds c)
    (fun n hn => let ⟨hp, hr, hs⟩ := hN n hn; nameFree_of_argProj c h hp hr hs)
    (fun n hn => let ⟨hp, hr, hs⟩ := hN n hn; spareSymB_of_argProj c hp hr hs)

/-- **The account's arm for generated equations, read**: an equation `genEqClassOK` accepts is one
`predProjOK?` accepts (a sort predicate's or a sort's projection's), or a constructor argument's
projection, whose name has the prefix `Lblproject'Coln` and is no registry symbol's and none of
the definition's own: the conditions `nameFree_of_argProj` and `spareSymB_of_argProj` read. -/
theorem genEqClassOK_cases {E : Parse.Env} {d : Definition} {eqs : List Parse.RawEqn} {e : Parse.RawEqn}
    (h : Parse.genEqClassOK E d eqs e = true) :
    Parse.predProjOK? E.N E.src eqs d.sem e = some true ∨
      ((KoreAML.Parse.dropPrefix? "Lblproject'Coln" e.fn).isSome = true ∧ regSymNames.contains e.fn = false ∧
        d.sem.symNames.contains e.fn = false) := by
  unfold Parse.genEqClassOK at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨h.1.1.1.1.1, h.1.1.2, h.1.2⟩

/-- **A constructor argument's projection whose equation the account's arm accepts outside
`predProjOK?` is free of the theory and resolves to no constant**: the premises `hfree` and `hsym`
of `model_with_eqns_step` at its name, from the arm's check alone. -/
theorem argProj_free_of_genEqClassOK {E : Parse.Env} {d : Definition} {eqs : List Parse.RawEqn}
    {e : Parse.RawEqn} (h : Parse.genEqClassOK E d eqs e = true)
    (hp : Parse.predProjOK? E.N E.src eqs d.sem e ≠ some true) (hc : d.sem.coreOK = true) :
    (∀ φ, (Γc d.sem ∪ Γstep d.sem) φ → KoreAML.Sym.symbol e.fn ∉ psyms φ) ∧ spareSymB d.sem e.fn = true := by
  rcases genEqClassOK_cases h with h' | ⟨h1, h2, h3⟩
  · exact absurd h' hp
  · exact ⟨nameFree_of_argProj d.sem hc h1 h2 h3, spareSymB_of_argProj d.sem h1 h2 h3⟩

end GenEqs

end KCore
