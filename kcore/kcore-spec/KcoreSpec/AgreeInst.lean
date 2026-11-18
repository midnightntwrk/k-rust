/-
  KCore, checked layer: two equations of one priority whose patterns are one an instance of the
  other agree when, read at that instance, their right-hand sides are one term or their `requires`
  exclude each other (`instAgree`, `instAgree_sound`, `fnExclusiveI`, `agreeObligationsI`).

  The instance is read position by position (`instOfList`): where the first clause's pattern has
  a variable x (or an alias `p #as x`) the second's has a term t made of variables, domain values,
  constructors and injections (`plainTerm`; an alias of the second clause stands for its variable),
  and elsewhere the two patterns have one head. Where both clauses apply at one argument list, the
  first's match gives x the value t has under the second's match (`instOfList_sound`). A term of
  the first clause whose variables are all read this way has, under the first match, exactly the
  results its instance (`substT`) has under the second (`substT_eval`, both directions: the
  instance's terms have one result each). So

  - the right-hand sides agree when the instance of the first is the second (`schedule`'s and
    `#parseMap`'s renamed copies);
  - the clauses never both apply when the instance of the first's `requires` and the second's
    `requires` exclude each other (`reqsExclusive`: `N >Int 0` against `notBool (N >Int 0)` with
    the variables renamed, `N <Int 0` against `N >Int 0` at `W : WS`), or when a literal of the
    instance is false by itself: `t ==K t` asserted false or `t =/=K t` true, t a ground value
    (`(V, BERLIN) requires notBool (V ==K Ghasaccesslist)` at the instance
    `(Ghasaccesslist, BERLIN)`).

  `fnExclusiveI` adds this to `fnExclusiveL`'s cases pair by pair; `agreeObligationsI` names the
  functions it does not confirm.
-/
import KcoreSpec.AgreeLists

set_option autoImplicit false

namespace KCore.Det

open KCore KCore.Exec GroundTerm

variable {c : Semantics}

/-! ## The instance -/

mutual
  /-- A term built from variables, domain values, constructors and injections: as a pattern it
  denotes the value it has as a term, and as a term it has one result. -/
  def _root_.KCore.Semantics.plainTerm (c : Semantics) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .app f ts => c.isCtor f && c.plainTermList ts
    | .inj _ _ t => c.plainTerm t
    | .as _ _ => false
    termination_by structural t => t
  def _root_.KCore.Semantics.plainTermList (c : Semantics) : List Term → Bool
    | [] => true
    | t :: ts => c.plainTerm t && c.plainTermList ts
    termination_by structural ts => ts
end

/-- The term a pattern of the second clause stands for: an alias's variable, or the pattern itself
when it is plain. -/
def _root_.KCore.Semantics.asTermOf (c : Semantics) : Term → Option Term
  | .as _ j => some (.var j)
  | q => if c.plainTerm q then some q else none

/-- Read x as t: consistent with an earlier reading of x (one term). -/
def bindInst (θ : List (Nat × Term)) (x : Nat) (t : Term) : Option (List (Nat × Term)) :=
  match θ.lookup x with
  | some t' => if Term.beq t t' then some θ else none
  | none => some ((x, t) :: θ)

mutual
  /-- The first pattern's variables read as terms of the second pattern, position by position;
  `none` where the heads differ or a variable of the first faces a pattern that is not plain. -/
  def _root_.KCore.Semantics.instOf (c : Semantics) (θ : List (Nat × Term)) : Term → Term → Option (List (Nat × Term))
    | .var x, q => (c.asTermOf q).bind (bindInst θ x)
    | .as p i, q => ((c.asTermOf q).bind (bindInst θ i)).bind fun θ' => c.instOf θ' p q
    | .dv s l, q => match peelAs q with
      | .dv s' l' => if s == s' && l == l' then some θ else none
      | _ => none
    | .app f ps, q => match peelAs q with
      | .app g qs => if f == g && c.isCtor f then c.instOfList θ ps qs else none
      | _ => none
    | .inj a b p, q => match peelAs q with
      | .inj a' b' q' => if a == a' && b == b' then c.instOf θ p q' else none
      | _ => none
    termination_by structural p => p
  def _root_.KCore.Semantics.instOfList (c : Semantics) (θ : List (Nat × Term)) : List Term → List Term → Option (List (Nat × Term))
    | [], [] => some θ
    | p :: ps, q :: qs => (c.instOf θ p q).bind fun θ' => c.instOfList θ' ps qs
    | _, _ => none
    termination_by structural ps => ps
end

mutual
  /-- The instance of a term: each variable read by θ replaced by its term. -/
  def substT (θ : List (Nat × Term)) : Term → Term
    | .var x => (θ.lookup x).getD (.var x)
    | .dv s l => .dv s l
    | .app f ts => .app f (substTList θ ts)
    | .inj a b t => .inj a b (substT θ t)
    | .as t i => .as (substT θ t) i
    termination_by structural t => t
  def substTList (θ : List (Nat × Term)) : List Term → List Term
    | [] => []
    | t :: ts => substT θ t :: substTList θ ts
    termination_by structural ts => ts
end

/-- Every variable of t is read by θ. -/
def boundBy (θ : List (Nat × Term)) (t : Term) : Bool := (varOccs t).all fun x => (θ.lookup x).isSome

/-- A term true wherever it has a value: `t ==K t` for a ground value t, or a disjunction one of
whose disjuncts is. -/
def _root_.KCore.Semantics.selfTrue (c : Semantics) : Term → Bool
  | .app f [t, u] => (f == kEq && Term.beq t u && c.groundValue t) || (f == boolOr && (c.selfTrue t || c.selfTrue u))
  | _ => false

/-- A literal false by itself: a term `selfTrue` accepts asserted false, or `t =/=K t` asserted
true, t a ground value. -/
def _root_.KCore.Semantics.litSelfFalse (c : Semantics) : Term × Bool → Bool
  | (A, false) => c.selfTrue A
  | (.app f [t, u], true) => f == kNe && Term.beq t u && c.groundValue t
  | _ => false

/-- `t ==K u` and `t =/=K u` asserted alike. -/
def complK : Term × Bool → Term × Bool → Bool
  | (.app f [t, u], b), (.app g [t', u'], b') =>
    b == b' && ((f == kEq && g == kNe) || (f == kNe && g == kEq)) && Term.beq t t' && Term.beq u u'
  | _, _ => false

/-- Two lists of literals that are not all asserted: a literal of the first false by itself, a
literal of each that are `==K` and `=/=K` of the same terms, or a negated conjunction against its
conjuncts (`negConjLits`, either way). -/
def _root_.KCore.Semantics.litsApartI (c : Semantics) (ls ls' : List (Term × Bool)) : Bool :=
  ls.any c.litSelfFalse || ls.any (fun l => ls'.any (complK l)) || negConjLits ls ls' || negConjLits ls' ls

/-- **Two clauses that agree at an instance**: the second's patterns are an instance of the
first's, and, read at it, the right-hand sides are one term, or the `requires` exclude each other,
or their literals are apart by `litsApartI`. -/
def _root_.KCore.Semantics.instAgree (c : Semantics) (heads : List CtorSig) (cl cl' : Clause) : Bool :=
  match c.instOfList [] cl.pats cl'.pats with
  | none => false
  | some θ =>
    (boundBy θ cl.rhs && Term.beq (substT θ cl.rhs) cl'.rhs && cl.ens.isNone && cl'.ens.isNone) ||
    (match cl.req with
     | some q => boundBy θ q &&
         (c.reqsExclusive heads cl'.vars (some (substT θ q)) cl'.req ||
          c.reqsExclusive heads cl'.vars cl'.req (some (substT θ q)) ||
          c.litsApartI (lits (substT θ q)) (reqLits cl'.req))
     | none => false)

/-! ## Soundness -/

/-- θ reads each of its variables as a plain term whose value under σ' is the variable's value
under σ. -/
def InstOK (c : Semantics) (σ σ' : Subst) (θ : List (Nat × Term)) : Prop :=
  ∀ p ∈ θ, c.plainTerm p.2 = true ∧ ∃ v, σ.lookup p.1 = some v ∧ EvalTerm c σ' p.2 (some v)

theorem lookup_mem_nat {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: l, a, b, h => by
    by_cases hx : a = x
    · subst hx; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · have : (a == x) = false := by simp [hx]
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem_nat h)

mutual
  /-- A plain term has one result. -/
  theorem plain_fun {σ : Subst} : ∀ {t : Term}, c.plainTerm t = true → Fun c σ t
    | .var _, _ => fun r r' h h' => by rw [EvalTerm.var_inv h, EvalTerm.var_inv h']
    | .dv _ _, _ => fun r r' h h' => by rw [EvalTerm.dv_inv h, EvalTerm.dv_inv h']
    | .as _ _, hp => by simp [Semantics.plainTerm] at hp
    | .inj a b t, hp => fun r r' h h' => by
      simp only [Semantics.plainTerm] at hp
      obtain ⟨r₀, h₀, rfl⟩ := EvalTerm.inj_inv h
      obtain ⟨r₀', h₀', rfl⟩ := EvalTerm.inj_inv h'
      rw [plain_fun hp _ _ h₀ h₀']
    | .app f ts, hp => fun r r' h h' => by
      simp only [Semantics.plainTerm, Bool.and_eq_true] at hp
      obtain ⟨rs, hts, rfl⟩ := EvalTerm.ctor_inv hp.1 h
      obtain ⟨rs', hts', rfl⟩ := EvalTerm.ctor_inv hp.1 h'
      rw [plainList_fun hp.2 hts hts']
    termination_by structural t => t
  theorem plainList_fun {σ : Subst} : ∀ {ts : List Term} {rs rs' : List (Option GroundTerm)},
      c.plainTermList ts = true → EvalTerms c σ ts rs → EvalTerms c σ ts rs' → rs = rs'
    | [], _, _, _, h, h' => by rw [EvalTerms.nil_inv h, EvalTerms.nil_inv h']
    | t :: ts, _, _, hp, h, h' => by
      simp only [Semantics.plainTermList, Bool.and_eq_true] at hp
      cases h with
      | cons h1 hs => cases h' with
        | cons h1' hs' => rw [plain_fun hp.1 _ _ h1 h1', plainList_fun hp.2 hs hs']
    termination_by structural ts => ts
end

mutual
  /-- A plain pattern denotes the value it has as a term. -/
  theorem plain_patVal_eval (hmc : MatchCtxO c) {σ : Subst} : ∀ {q : Term} {v : GroundTerm},
      c.plainTerm q = true → PatVal c σ q v → EvalTerm c σ q (some v)
    | .var _, _, _, h => by rw [← PatVal.var_inv h]; exact EvalTerm.var
    | .dv _ _, _, _, h => by rw [PatVal.dv_shape h]; exact EvalTerm.dv
    | .as _ _, _, hp, _ => by simp [Semantics.plainTerm] at hp
    | .inj a b q, _, hp, h => by
      simp only [Semantics.plainTerm] at hp
      obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv h
      exact EvalTerm.inj (plain_patVal_eval hmc hp hw)
    | .app f qs, _, hp, h => by
      simp only [Semantics.plainTerm, Bool.and_eq_true] at hp
      obtain ⟨vs, rfl, hvs⟩ := PatVal.ctor_shape hmc hp.1 h
      have := EvalTerm.ctor (c := c) (σ := σ) hp.1 (plainList_patVal_eval hmc hp.2 hvs)
      rwa [allSome_map_some] at this
    termination_by structural q => q
  theorem plainList_patVal_eval (hmc : MatchCtxO c) {σ : Subst} : ∀ {qs : List Term} {vs : List GroundTerm},
      c.plainTermList qs = true → PatVals c σ qs vs → EvalTerms c σ qs (vs.map some)
    | [], _, _, h => by cases h; exact EvalTerms.nil
    | q :: qs, _, hp, h => by
      simp only [Semantics.plainTermList, Bool.and_eq_true] at hp
      cases h with
      | cons h1 hs => exact EvalTerms.cons (plain_patVal_eval hmc hp.1 h1) (plainList_patVal_eval hmc hp.2 hs)
    termination_by structural qs => qs
end

theorem asTermOf_sound (hmc : MatchCtxO c) {σ' : Subst} {q t : Term} {v : GroundTerm}
    (ht : c.asTermOf q = some t) (h : PatVal c σ' q v) : c.plainTerm t = true ∧ EvalTerm c σ' t (some v) := by
  unfold Semantics.asTermOf at ht
  split at ht
  · rename_i j
    cases ht
    refine ⟨rfl, ?_⟩
    rw [← (PatVal.as_inv h).2]; exact EvalTerm.var
  · split at ht
    · rename_i hp; cases ht; exact ⟨hp, plain_patVal_eval hmc hp h⟩
    · cases ht

theorem bindInst_sound {σ σ' : Subst} {θ θ' : List (Nat × Term)} {x : Nat} {t : Term} {v : GroundTerm}
    (hb : bindInst θ x t = some θ') (hx : σ.lookup x = some v) (hp : c.plainTerm t = true)
    (he : EvalTerm c σ' t (some v)) (hθ : InstOK c σ σ' θ) : InstOK c σ σ' θ' := by
  unfold bindInst at hb
  split at hb
  · split at hb
    · cases hb; exact hθ
    · cases hb
  · cases hb
    intro p hp'
    rcases List.mem_cons.mp hp' with rfl | hm
    · exact ⟨hp, v, hx, he⟩
    · exact hθ p hm

mutual
  /-- **Where both patterns denote one value, the instance reads each variable of the first as a
  term whose value under the second match is the variable's value under the first.** -/
  theorem instOf_sound (hmc : MatchCtxO c) {vars vars' : List Srt} {σ σ' : Subst}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') :
      ∀ (p : Term) {q : Term} {θ θ' : List (Nat × Term)} {v : GroundTerm} {s s' : Srt},
      c.instOf θ p q = some θ' → PatVal c σ p v → PatVal c σ' q v →
      sortOfTerm c.patCtxAll vars p = some s → sortOfTerm c.patCtxAll vars' q = some s' →
      InstOK c σ σ' θ → InstOK c σ σ' θ'
    | .var x, q, θ, θ', v, s, s', hi, h, h', _, _, hθ => by
      simp only [Semantics.instOf, Option.bind_eq_some_iff] at hi
      obtain ⟨t, ht, hb⟩ := hi
      obtain ⟨hp, he⟩ := asTermOf_sound hmc ht h'
      exact bindInst_sound hb (PatVal.var_inv h) hp he hθ
    | .as p i, q, θ, θ', v, s, s', hi, h, h', hs, hs', hθ => by
      simp only [Semantics.instOf, Option.bind_eq_some_iff] at hi
      obtain ⟨θ₁, ⟨t, ht, hb⟩, hi⟩ := hi
      obtain ⟨hpv, hiv⟩ := PatVal.as_inv h
      obtain ⟨hp, he⟩ := asTermOf_sound hmc ht h'
      exact instOf_sound hmc hσ hσ' p hi hpv h' (sortOfTerm_as hs).2 hs' (bindInst_sound hb hiv hp he hθ)
    | .dv s₀ l, q, θ, θ', v, s, s', hi, _, _, _, _, hθ => by
      simp only [Semantics.instOf] at hi
      split at hi
      · split at hi
        · cases hi; exact hθ
        · cases hi
      · cases hi
    | .app f ps, q, θ, θ', v, s, s', hi, h, h', hs, hs', hθ => by
      simp only [Semantics.instOf] at hi
      obtain ⟨hsq, hq⟩ := peelAs_patVal hs' h'
      split at hi
      · rename_i g qs hpq
        split at hi
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, hct⟩ := hc
          rw [hpq] at hsq hq
          obtain ⟨vs, rfl, hvs⟩ := PatVal.ctor_shape hmc hct h
          obtain ⟨vs', he, hvs'⟩ := PatVal.ctor_shape hmc hct hq
          cases he
          obtain ⟨k, -, hk, -⟩ := sortOfTerm_app.mp hs
          obtain ⟨k', -, hk', -⟩ := sortOfTerm_app.mp hsq
          exact instOfList_sound hmc hσ hσ' ps hi hvs hvs' hk hk' hθ
        · cases hi
      · cases hi
    | .inj a b p, q, θ, θ', v, s, s', hi, h, h', hs, hs', hθ => by
      simp only [Semantics.instOf] at hi
      obtain ⟨hsq, hq⟩ := peelAs_patVal hs' h'
      split at hi
      · rename_i a' b' q' hpq
        split at hi
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          rw [hpq] at hsq hq
          obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv h
          obtain ⟨w', hw', he⟩ := PatVal.inj_inv hq
          obtain ⟨-, hps, -⟩ := sortOfTerm_inj.mp hs
          obtain ⟨-, hqs, -⟩ := sortOfTerm_inj.mp hsq
          have := injNormal_inj hmc (patVal_sortedAll hmc hσ hw hps) (patVal_sortedAll hmc hσ' hw' hqs) he
          subst this
          exact instOf_sound hmc hσ hσ' p hi hw hw' hps hqs hθ
        · cases hi
      · cases hi
    termination_by structural p => p
  theorem instOfList_sound (hmc : MatchCtxO c) {vars vars' : List Srt} {σ σ' : Subst}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') :
      ∀ (ps : List Term) {qs : List Term} {θ θ' : List (Nat × Term)} {vs : List GroundTerm} {ss ss' : List Srt},
      c.instOfList θ ps qs = some θ' → PatVals c σ ps vs → PatVals c σ' qs vs →
      sortsOfTerms c.patCtxAll vars ps = some ss → sortsOfTerms c.patCtxAll vars' qs = some ss' →
      InstOK c σ σ' θ → InstOK c σ σ' θ'
    | [], qs, θ, θ', vs, ss, ss', hi, _, _, _, _, hθ => by
      cases qs with
      | nil => simp only [Semantics.instOfList, Option.some.injEq] at hi; subst hi; exact hθ
      | cons _ _ => simp [Semantics.instOfList] at hi
    | p :: ps, qs, θ, θ', vs, ss, ss', hi, h, h', hs, hs', hθ => by
      cases qs with
      | nil => simp [Semantics.instOfList] at hi
      | cons q qs =>
        simp only [Semantics.instOfList, Option.bind_eq_some_iff] at hi
        obtain ⟨θ₁, hi₁, hi₂⟩ := hi
        obtain ⟨v, vs₁, rfl, h1, h2⟩ := PatVals.cons_inv' h
        obtain ⟨v', vs₁', he, h1', h2'⟩ := PatVals.cons_inv' h'
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨_, _, hs₁, hs₂, -⟩ := sortsOfTerms_cons.mp hs
        obtain ⟨_, _, hs₁', hs₂', -⟩ := sortsOfTerms_cons.mp hs'
        exact instOfList_sound hmc hσ hσ' ps hi₂ h2 h2' hs₂ hs₂'
          (instOf_sound hmc hσ hσ' p hi₁ h1 h1' hs₁ hs₁' hθ)
    termination_by structural ps => ps
end

/-- An application's result is read from its arguments' results only: arguments with the same
results give it the same result. -/
theorem EvalTerm.app_args {σ σ' : Subst} {f : Sym} {ts ts' : List Term} {r : Option GroundTerm}
    (ha : ∀ rs, EvalTerms c σ ts rs → EvalTerms c σ' ts' rs) (h : EvalTerm c σ (.app f ts) r) :
    EvalTerm c σ' (.app f ts') r := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | ctor hc hts => cases ht; exact EvalTerm.ctor hc (ha _ hts)
  | hook hc hhk hts hh hund => cases ht; exact EvalTerm.hook hc hhk (ha _ hts) hh hund
  | param hc hhk hp hts hr => cases ht; exact EvalTerm.param hc hhk hp (ha _ hts) hr
  | call hc hh hts hvs hf hp => cases ht; exact EvalTerm.call hc hh (ha _ hts) hvs hf hp
  | callUndef hc hh hts hvs hp => cases ht; exact EvalTerm.callUndef hc hh (ha _ hts) hvs hp
  | ovl hc ho hts hnf => cases ht; exact EvalTerm.ovl hc ho (ha _ hts) hnf
  | ovlFn hc ho hts hvs hlo hcov hf => cases ht; exact EvalTerm.ovlFn hc ho (ha _ hts) hvs hlo hcov hf
  | _ => cases ht

theorem EvalTerm.as_false {σ : Subst} {t : Term} {i : Nat} {r : Option GroundTerm}
    (h : EvalTerm c σ (.as t i) r) : False := by
  generalize ht : Term.as t i = u at h
  cases h <;> cases ht

theorem boundBy_app {θ : List (Nat × Term)} {f : Sym} {ts : List Term} (h : boundBy θ (.app f ts) = true) :
    ∀ t ∈ ts, boundBy θ t = true := by
  intro t ht
  unfold boundBy at h ⊢
  simp only [List.all_eq_true] at h ⊢
  intro x hx
  exact h x (by simp only [varOccs]; exact mem_varOccsList_of ht hx)
where
  mem_varOccsList_of : ∀ {ts : List Term} {t : Term} {x : Nat}, t ∈ ts → x ∈ varOccs t → x ∈ varOccsList ts
    | _ :: _, _, _, ht, hx => by
      simp only [varOccsList, List.mem_append]
      rcases List.mem_cons.mp ht with rfl | ht
      · exact .inl hx
      · exact .inr (mem_varOccsList_of ht hx)

mutual
  /-- **A term and its instance have the same results**, under the first and the second match:
  each variable's value under σ is its term's one result under σ'. -/
  theorem substT_eval {σ σ' : Subst} {θ : List (Nat × Term)} (hθ : InstOK c σ σ' θ) :
      ∀ (t : Term), boundBy θ t = true → ∀ r, (EvalTerm c σ t r ↔ EvalTerm c σ' (substT θ t) r)
    | .var x, hb, r => by
      unfold boundBy at hb
      simp only [varOccs, List.all_cons, List.all_nil, Bool.and_true, Option.isSome_iff_exists] at hb
      obtain ⟨t, ht⟩ := hb
      obtain ⟨hp, v, hv, he⟩ := hθ _ (lookup_mem_nat ht)
      simp only [substT, ht, Option.getD_some]
      constructor
      · intro h; rw [EvalTerm.var_inv h, hv]; exact he
      · intro h; rw [plain_fun hp _ _ h he, ← hv]; exact EvalTerm.var
    | .dv s l, _, r => by
      simp only [substT]
      exact ⟨fun h => by rw [EvalTerm.dv_inv h]; exact EvalTerm.dv,
        fun h => by rw [EvalTerm.dv_inv h]; exact EvalTerm.dv⟩
    | .as t i, _, r => by
      simp only [substT]
      exact ⟨fun h => (EvalTerm.as_false h).elim, fun h => (EvalTerm.as_false h).elim⟩
    | .inj a b t, hb, r => by
      have hb' : boundBy θ t = true := by unfold boundBy at hb ⊢; simpa only [varOccs] using hb
      simp only [substT]
      constructor
      · intro h
        obtain ⟨r₀, h₀, rfl⟩ := EvalTerm.inj_inv h
        exact EvalTerm.inj ((substT_eval hθ t hb' r₀).mp h₀)
      · intro h
        obtain ⟨r₀, h₀, rfl⟩ := EvalTerm.inj_inv h
        exact EvalTerm.inj ((substT_eval hθ t hb' r₀).mpr h₀)
    | .app f ts, hb, r => by
      have hb' := boundBy_app hb
      simp only [substT]
      exact ⟨EvalTerm.app_args (f := f) (ts := ts) (ts' := substTList θ ts)
          fun rs h => (substTList_eval hθ ts hb' rs).mp h,
        EvalTerm.app_args (f := f) (ts := substTList θ ts) (ts' := ts)
          fun rs h => (substTList_eval hθ ts hb' rs).mpr h⟩
    termination_by structural t => t
  theorem substTList_eval {σ σ' : Subst} {θ : List (Nat × Term)} (hθ : InstOK c σ σ' θ) :
      ∀ (ts : List Term), (∀ t ∈ ts, boundBy θ t = true) → ∀ rs,
        (EvalTerms c σ ts rs ↔ EvalTerms c σ' (substTList θ ts) rs)
    | [], _, rs => by
      simp only [substTList]
      exact ⟨fun h => by rw [EvalTerms.nil_inv h]; exact EvalTerms.nil,
        fun h => by rw [EvalTerms.nil_inv h]; exact EvalTerms.nil⟩
    | t :: ts, hb, rs => by
      simp only [substTList]
      have h1 := substT_eval hθ t (hb t List.mem_cons_self)
      have h2 := substTList_eval hθ ts (fun u hu => hb u (List.mem_cons_of_mem _ hu))
      constructor
      · intro h
        cases h with
        | cons he hs => exact EvalTerms.cons ((h1 _).mp he) ((h2 _).mp hs)
      · intro h
        cases h with
        | cons he hs => exact EvalTerms.cons ((h1 _).mpr he) ((h2 _).mpr hs)
    termination_by structural ts => ts
end

mutual
  /-- The terms inside a plain term are plain. -/
  theorem plain_subterms : ∀ {t u : Term}, c.plainTerm t = true → u ∈ subterms t → c.plainTerm u = true
    | .var _, _, hp, hu => by simp only [subterms, List.mem_singleton] at hu; subst hu; exact hp
    | .dv _ _, _, hp, hu => by simp only [subterms, List.mem_singleton] at hu; subst hu; exact hp
    | .as _ _, _, hp, _ => by simp [Semantics.plainTerm] at hp
    | .inj a b t, _, hp, hu => by
      simp only [subterms, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hp
      · exact plain_subterms (by simpa [Semantics.plainTerm] using hp) hu
    | .app f ts, _, hp, hu => by
      simp only [subterms, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hp
      · simp only [Semantics.plainTerm, Bool.and_eq_true] at hp
        exact plainList_subterms hp.2 hu
    termination_by structural t => t
  theorem plainList_subterms : ∀ {ts : List Term} {u : Term}, c.plainTermList ts = true →
      u ∈ subtermsList ts → c.plainTerm u = true
    | [], _, _, hu => by simp [subtermsList] at hu
    | t :: ts, _, hp, hu => by
      simp only [Semantics.plainTermList, Bool.and_eq_true] at hp
      simp only [subtermsList, List.mem_append] at hu
      rcases hu with hu | hu
      · exact plain_subterms hp.1 hu
      · exact plainList_subterms hp.2 hu
    termination_by structural ts => ts
end

theorem boundBy_of_sub {θ : List (Nat × Term)} {t u : Term} (hb : boundBy θ t = true) (hu : u ∈ subterms t) :
    boundBy θ u = true := by
  unfold boundBy at hb ⊢
  simp only [List.all_eq_true] at hb ⊢
  exact fun x hx => hb x (varOccs_subterms hu x hx)

mutual
  /-- The terms inside an instance: instances of terms inside the term, or terms inside a term θ
  reads a variable as. -/
  theorem subterms_substT {θ : List (Nat × Term)} : ∀ {t u : Term}, u ∈ subterms (substT θ t) →
      (∃ u₀ ∈ subterms t, u = substT θ u₀) ∨ ∃ p ∈ θ, u ∈ subterms p.2
    | .var x, u, hu => by
      simp only [substT] at hu
      cases hl : θ.lookup x with
      | none =>
        rw [hl] at hu
        simp only [Option.getD_none, subterms, List.mem_singleton] at hu
        exact .inl ⟨.var x, List.mem_singleton_self _, by rw [hu]; simp [substT, hl]⟩
      | some t => rw [hl] at hu; exact .inr ⟨(x, t), lookup_mem_nat hl, hu⟩
    | .dv s l, u, hu => .inl ⟨.dv s l, List.mem_singleton_self _, by simpa [substT, subterms] using hu⟩
    | .inj a b t, u, hu => by
      simp only [substT, subterms, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact .inl ⟨.inj a b t, List.mem_cons_self, by simp [substT]⟩
      · rcases subterms_substT hu with ⟨u₀, hm, rfl⟩ | h
        · exact .inl ⟨u₀, List.mem_cons_of_mem _ hm, rfl⟩
        · exact .inr h
    | .as t i, u, hu => by
      simp only [substT, subterms, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact .inl ⟨.as t i, List.mem_cons_self, by simp [substT]⟩
      · rcases subterms_substT hu with ⟨u₀, hm, rfl⟩ | h
        · exact .inl ⟨u₀, List.mem_cons_of_mem _ hm, rfl⟩
        · exact .inr h
    | .app f ts, u, hu => by
      simp only [substT, subterms, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact .inl ⟨.app f ts, List.mem_cons_self, by simp [substT]⟩
      · rcases subtermsList_substT hu with ⟨u₀, hm, rfl⟩ | h
        · exact .inl ⟨u₀, List.mem_cons_of_mem _ hm, rfl⟩
        · exact .inr h
    termination_by structural t => t
  theorem subtermsList_substT {θ : List (Nat × Term)} : ∀ {ts : List Term} {u : Term},
      u ∈ subtermsList (substTList θ ts) → (∃ u₀ ∈ subtermsList ts, u = substT θ u₀) ∨ ∃ p ∈ θ, u ∈ subterms p.2
    | [], _, hu => by simp [substTList, subtermsList] at hu
    | t :: ts, u, hu => by
      simp only [substTList, subtermsList, List.mem_append] at hu ⊢
      rcases hu with hu | hu
      · rcases subterms_substT hu with ⟨u₀, hm, rfl⟩ | h
        · exact .inl ⟨u₀, .inl hm, rfl⟩
        · exact .inr h
      · rcases subtermsList_substT hu with ⟨u₀, hm, rfl⟩ | h
        · exact .inl ⟨u₀, .inr hm, rfl⟩
        · exact .inr h
    termination_by structural ts => ts
end

/-- The terms inside an instance have one result under σ' where those inside the term have one
under σ. -/
theorem hdet_substT {σ σ' : Subst} {θ : List (Nat × Term)} (hθ : InstOK c σ σ' θ) {t : Term}
    (hb : boundBy θ t = true) (hd : HDet c σ t) : HDet c σ' (substT θ t) := by
  intro u hu
  rcases subterms_substT hu with ⟨u₀, hm, rfl⟩ | ⟨p, hp, hu⟩
  · have hb₀ := boundBy_of_sub hb hm
    intro r r' h h'
    exact hd u₀ hm r r' ((substT_eval hθ u₀ hb₀ r).mpr h) ((substT_eval hθ u₀ hb₀ r').mpr h')
  · exact plain_fun (plain_subterms (hθ p hp).1 hu)

/-- An interpreted symbol's application to two arguments with a Bool value: the arguments' values
and the hook's (a symbol without silent points). -/
theorem hook2_inv {σ : Subst} {f : Sym} {t u : Term} {b : Bool} (hhk : isHook f = true)
    (h : EvalTerm c σ (.app f [t, u]) (some (bool b))) (hs : silentKey f = false := by decide +kernel) :
    ∃ v w, EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some w) ∧ hook f [v, w] = some (some (bool b)) := by
  generalize ht : Term.app f [t, u] = e at h
  generalize hr : some (bool b) = r at h
  cases h with
  | @ctor _ _ _ rs _ _ =>
    cases ht
    cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
  | @hook _ _ _ rs r' _ _ hts hh hund =>
    cases ht
    obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
    cases r₁ with
    | none => rw [hund (by simp [allSome])] at hr; cases hr
    | some w₁ =>
      cases r₂ with
      | none => rw [hund (by simp [allSome])] at hr; cases hr
      | some w₂ => exact ⟨w₁, w₂, h1, h2, Semantics.hookRes_of_notKey hs _ ▸ hh [w₁, w₂] (by simp [allSome])⟩
  | param _ h _ _ _ => cases ht; rw [hhk] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hhk] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hhk] at h; cases h
  | ovl _ ho _ => cases ht; have h := (c.isOvl_parts ho).2.1; rw [hhk] at h; cases h
  | ovlFn _ ho => cases ht; have h := (c.isOvl_parts ho).2.1; rw [hhk] at h; cases h
  | _ => cases ht

theorem hook_kNe (v w : GroundTerm) : hook kNe [v, w] = some (some (bool (GroundTerm.cmp v w != .eq))) := rfl

/-- A disjunction false: both disjuncts false. -/
theorem or_false_inv {σ : Subst} {t u : Term} (e : EvalTerm c σ (.app boolOr [t, u]) (some (bool false))) :
    EvalTerm c σ t (some (bool false)) ∧ EvalTerm c σ u (some (bool false)) := by
  obtain ⟨v, w, h1, h2, hv⟩ := hook2_inv rfl e
  rw [hook_or, Option.some.injEq] at hv
  unfold bool2 at hv
  cases hx : asBool v with
  | none => simp [hx] at hv
  | some x =>
  cases hy : asBool w with
  | none => simp [hx, hy] at hv
  | some y =>
  simp only [hx, hy, Option.bind_some, Option.map_some, Option.some.injEq] at hv
  have hxy := bool_inj hv
  simp only [Bool.or_eq_false_iff] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  rw [asBool_some hx] at h1
  rw [asBool_some hy] at h2
  exact ⟨h1, h2⟩

theorem mem_subterms_arg₁ {f : Sym} {t u : Term} : t ∈ subterms (.app f [t, u]) := by
  show t ∈ Term.app f [t, u] :: (subterms t ++ (subterms u ++ []))
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem_subterms t))

theorem mem_subterms_arg₂ {f : Sym} {t u : Term} : u ∈ subterms (.app f [t, u]) := by
  show u ∈ Term.app f [t, u] :: (subterms t ++ (subterms u ++ []))
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ (self_mem_subterms u)))

/-- A term `selfTrue` accepts is not false. -/
theorem selfTrue_sound {σ : Subst} : ∀ {A : Term}, c.selfTrue A = true → EvalTerm c σ A (some (bool false)) → False
  | .app f [t, u], h, e => by
    simp only [Semantics.selfTrue, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, hb⟩, hg⟩ | ⟨rfl, ht | hu⟩
    · have := Term.beq_sound hb
      subst this
      obtain ⟨v, w, h1, h2, hv⟩ := hook2_inv rfl e
      have e1 := Option.some.inj (gval_eval hg h1)
      have e2 := Option.some.inj (gval_eval hg h2)
      subst e1 e2
      rw [hook_kEq, cmp_refl] at hv
      exact absurd (bool_inj (Option.some.inj (Option.some.inj hv))) (by decide)
    · exact selfTrue_sound ht (or_false_inv e).1
    · exact selfTrue_sound hu (or_false_inv e).2
  | .var _, h, _ => by simp [Semantics.selfTrue] at h
  | .dv _ _, h, _ => by simp [Semantics.selfTrue] at h
  | .inj _ _ _, h, _ => by simp [Semantics.selfTrue] at h
  | .as _ _, h, _ => by simp [Semantics.selfTrue] at h
  | .app _ [], h, _ => by simp [Semantics.selfTrue] at h
  | .app _ [_], h, _ => by simp [Semantics.selfTrue] at h
  | .app _ (_ :: _ :: _ :: _), h, _ => by simp [Semantics.selfTrue] at h

/-- A literal `litSelfFalse` accepts is not asserted. -/
theorem litSelfFalse_sound {σ : Subst} {A : Term} {b : Bool} (h : c.litSelfFalse (A, b) = true)
    (e : EvalTerm c σ A (some (bool b))) : False := by
  cases b with
  | false => exact selfTrue_sound (by simpa [Semantics.litSelfFalse] using h) e
  | true =>
    cases A with
    | app f ts =>
      match ts, h, e with
      | [t, u], h, e =>
        simp only [Semantics.litSelfFalse, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, hb⟩, hg⟩ := h
        have := Term.beq_sound hb
        subst this
        obtain ⟨v, w, h1, h2, hv⟩ := hook2_inv rfl e
        have e1 := Option.some.inj (gval_eval hg h1)
        have e2 := Option.some.inj (gval_eval hg h2)
        subst e1 e2
        rw [hook_kNe, cmp_refl] at hv
        exact absurd (bool_inj (Option.some.inj (Option.some.inj hv))) (by decide)
      | [], h, _ => simp [Semantics.litSelfFalse] at h
      | [_], h, _ => simp [Semantics.litSelfFalse] at h
      | _ :: _ :: _ :: _, h, _ => simp [Semantics.litSelfFalse] at h
    | _ => simp [Semantics.litSelfFalse] at h

/-- `t ==K u` and `t =/=K u` are not asserted alike where t and u have one result. -/
theorem complK_sound {σ : Subst} {l l' : Term × Bool} (h : complK l l' = true)
    (hF : (∀ X ∈ subterms l.1, Fun c σ X) ∨ ∀ X ∈ subterms l'.1, Fun c σ X)
    (e : EvalTerm c σ l.1 (some (bool l.2))) (e' : EvalTerm c σ l'.1 (some (bool l'.2))) : False := by
  obtain ⟨A, b⟩ := l
  obtain ⟨A', b'⟩ := l'
  unfold complK at h
  split at h
  · rename_i f t u b₀ g t' u' b₀' heq heq'
    simp only [Prod.mk.injEq] at heq heq'
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨rfl, rfl⟩ := heq'
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, hfg⟩, ht⟩, hu⟩ := h
    have ht := Term.beq_sound ht
    have hu := Term.beq_sound hu
    subst ht hu
    have hft : Fun c σ t := hF.elim (fun hF => hF t mem_subterms_arg₁) (fun hF => hF t mem_subterms_arg₁)
    have hfu : Fun c σ u := hF.elim (fun hF => hF u mem_subterms_arg₂) (fun hF => hF u mem_subterms_arg₂)
    rcases hfg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨v, w, h1, h2, hv⟩ := hook2_inv rfl e
      obtain ⟨v', w', h1', h2', hv'⟩ := hook2_inv rfl e'
      cases Option.some.inj (hft _ _ h1 h1')
      cases Option.some.inj (hfu _ _ h2 h2')
      rw [hook_kEq] at hv
      rw [hook_kNe] at hv'
      have a := bool_inj (Option.some.inj (Option.some.inj hv))
      have a' := bool_inj (Option.some.inj (Option.some.inj hv'))
      rw [← a'] at a
      simp only [bne] at a; generalize (GroundTerm.cmp v w == .eq) = z at a; cases z <;> simp at a
    · obtain ⟨v, w, h1, h2, hv⟩ := hook2_inv rfl e
      obtain ⟨v', w', h1', h2', hv'⟩ := hook2_inv rfl e'
      cases Option.some.inj (hft _ _ h1 h1')
      cases Option.some.inj (hfu _ _ h2 h2')
      rw [hook_kNe] at hv
      rw [hook_kEq] at hv'
      have a := bool_inj (Option.some.inj (Option.some.inj hv))
      have a' := bool_inj (Option.some.inj (Option.some.inj hv'))
      rw [← a'] at a
      simp only [bne] at a; generalize (GroundTerm.cmp v w == .eq) = z at a; cases z <;> simp at a
  · cases h

/-- Two lists of literals `litsApartI` accepts are not all asserted, where the terms inside one of
them have one result. -/
theorem litsApartI_sound {σ : Subst} {ls ls' : List (Term × Bool)} (h : c.litsApartI ls ls' = true)
    (hF : (∀ l ∈ ls, ∀ X ∈ subterms l.1, Fun c σ X) ∨ ∀ l ∈ ls', ∀ X ∈ subterms l.1, Fun c σ X)
    (e : ∀ l ∈ ls, EvalTerm c σ l.1 (some (bool l.2))) (e' : ∀ l ∈ ls', EvalTerm c σ l.1 (some (bool l.2))) :
    False := by
  simp only [Semantics.litsApartI, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ((⟨l, hl, hs⟩ | ⟨l, hl, l', hl', hk⟩) | hn) | hn
  · exact litSelfFalse_sound hs (e l hl)
  · exact complK_sound hk (hF.elim (fun hF => .inl (hF l hl)) (fun hF => .inr (hF l' hl'))) (e l hl) (e' l' hl')
  · exact negConjLits_sound hn hF e e'
  · exact negConjLits_sound hn hF.symm e' e

/-- **Two clauses `instAgree` accepts are coherent, in both orders**, in the form of clauses without
existential variables (`CoherentPlain`). -/
theorem instAgree_sound (hmc : MatchCtxO c) {heads : List CtorSig} {cl cl' : Clause} {ss ss' : List Srt}
    (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some ss)
    (hpt' : sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some ss')
    (hx : cl.exs = []) (hx' : cl'.exs = [])
    (h : c.instAgree heads cl cl' = true) : CoherentPlain c cl cl' ∧ CoherentPlain c cl' cl := by
  unfold Semantics.instAgree at h
  split at h
  · cases h
  rename_i θ hθi
  have inst : ∀ {vs σ σ'}, cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs → InstOK c σ σ' θ :=
    fun ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ =>
      instOfList_sound hmc ((wellSortedAt_univ hx).mp hσ) ((wellSortedAt_univ hx').mp hσ') cl.pats hθi hm hm' hpt hpt' (fun _ h => by cases h)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hb, he⟩, hn⟩, hn'⟩ | h
  · have he := Term.beq_sound he
    simp only [Option.isNone_iff_eq_none] at hn hn'
    refine ⟨CoherentPlain.of_rhs hn hn' fun vs σ σ' ha ha' _ hd _ => .inr fun r r' h1 h2 => ?_,
      CoherentPlain.of_rhs hn' hn fun vs σ' σ ha' ha _ hd _ => .inr fun r' r h2 h1 => ?_⟩
    · have hθ := inst ha ha'
      rw [← he] at h2
      exact hd cl.rhs (self_mem_subterms _) r r' h1 ((substT_eval hθ cl.rhs hb r').mpr h2)
    · have hθ := inst ha ha'
      rw [← he] at h2 hd
      exact hd _ (self_mem_subterms _) r' r h2 ((substT_eval hθ cl.rhs hb r).mp h1)
  · split at h
    · rename_i q hq
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hb, hx⟩ := h
      -- where both apply, the instance of the first `requires` holds under the second match
      have key : ∀ {vs σ σ'}, cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
          ((∀ t, cl.req = some t → HDet c σ t) ∨ ∀ t, cl'.req = some t → HDet c σ' t) → False := by
        intro vs σ σ' ha ha' hF
        have hθ := inst ha ha'
        obtain ⟨_, _, hreq, _⟩ := ha
        obtain ⟨_, _, hreq', _⟩ := ha'
        have hqt : EvalTerm c σ' (substT θ q) (some (bool true)) :=
          (substT_eval hθ q hb _).mp (hreq q hq)
        have hF' : HDet c σ' (substT θ q) ∨ ∀ t, cl'.req = some t → HDet c σ' t :=
          hF.elim (fun hF => .inl (hdet_substT hθ hb (hF q hq))) .inr
        rcases hx with (hx | hx) | hx
        · exact reqsExclusive_sound hx (hF'.elim (fun h => .inl fun t ht => by cases ht; exact h) .inr)
            (fun t ht => by cases ht; exact hqt) hreq'
        · exact reqsExclusive_sound hx (hF'.elim (fun h => .inr fun t ht => by cases ht; exact h) .inl)
            hreq' (fun t ht => by cases ht; exact hqt)
        · refine litsApartI_sound hx ?_ (fun l hl => lits_sound hqt hl) (fun l hl => lits_reqLits hreq' hl)
          rcases hF' with hd | hd
          · exact .inl fun l hl X hX => hd X (subterms_trans (mem_subterms_of_lits hl) hX)
          · refine .inr fun l hl X hX => ?_
            obtain ⟨t, ht, hsub⟩ := mem_subterms_reqLits hl
            exact hd t ht X (subterms_trans hsub hX)
      exact ⟨fun vs σ σ' ha ha' hd _ _ _ => (key ha ha' (.inl hd)).elim,
        fun vs σ' σ ha' ha hd _ _ _ => (key ha ha' (.inr hd)).elim⟩
    · cases h

/-! ## The functions -/

/-- Two clauses that do not compete: of different priorities, the one of the smaller priority not
`aside`, so that it blocks the other (`Eval.clause`'s priority premise reads it). An `aside` clause
of the larger priority is admitted: `ClausesAgree` asks nothing of such a pair
(`notCompeting_iff`). -/
def notCompeting (cl cl' : Clause) : Bool :=
  cl.prio != cl'.prio && !(cl.aside && decide (cl.prio < cl'.prio)) &&
    !(cl'.aside && decide (cl'.prio < cl.prio))

/-- `notCompeting` is the negation of `ClausesAgree`'s premise on a pair, exactly. -/
theorem notCompeting_iff {cl cl' : Clause} : notCompeting cl cl' = true ↔
    ¬ (cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio)) := by
  simp only [notCompeting, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or, not_and, Bool.not_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun ha => h2.resolve_left (by simp [ha]), fun ha => h3.resolve_left (by simp [ha])⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · cases ha : cl.aside
      · exact .inl rfl
      · exact .inr (h2 ha)
    · cases ha : cl'.aside
      · exact .inl rfl
      · exact .inr (h3 ha)

/-- The different-priorities case of `fnExclusiveL` (neither clause `aside`) is one of
`notCompeting`'s. -/
theorem notCompeting_of_plain {cl cl' : Clause} (h : (cl.prio != cl'.prio && !cl.aside && !cl'.aside) = true) :
    notCompeting cl cl' = true := notCompeting_iff.mpr (not_compete h)

/-- `fnExclusiveL`'s cases for one pair of clauses, or a pair that does not compete
(`notCompeting`: beyond `fnExclusiveL`'s first case, an `aside` clause of the larger priority). -/
def _root_.KCore.Semantics.pairAgreeL (c : Semantics) (heads : List CtorSig) (cl cl' : Clause) : Bool :=
  notCompeting cl cl' || (cl.prio != cl'.prio && !cl.aside && !cl'.aside) ||
    !overlapList c.meet c.collHead cl.pats cl'.pats ||
    (c.clauseFixed cl && (c.clausesExclusive heads cl cl' || c.clausesExclusive heads cl' cl)) ||
    clausesAgree cl cl' || c.clausesListApart cl cl' || guardApart cl cl' || guardApart cl' cl ||
    (c.clauseFixed cl && negConjApart cl cl')

/-- `fnExclusiveL`'s cases, or an instance at which the pair agrees (`instAgree`, either way). -/
def _root_.KCore.Semantics.fnExclusiveI (c : Semantics) (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all fun (cl, cl') => c.pairAgreeL heads cl cl' ||
    (cl.prio == cl'.prio && (c.instAgree heads cl cl' || c.instAgree heads cl' cl))

/-! ## Clause patterns that apply overloading symbols -/

/-- Two patterns (aliases peeled) headed by constructors or overloading symbols whose overload
closures (`ovlClosure`: the symbol, and those it overloads, transitively) have no symbol in
common: a value either denotes is `h(ū)`, or an injection of it, for h in its head's closure
(`patVal_head`), so they denote no value in common. -/
def _root_.KCore.Semantics.headApart (c : Semantics) (p q : Term) : Bool :=
  match peelAs p, peelAs q with
  | .app f _, .app g _ => (c.isCtor f || c.isOvl f) && (c.isCtor g || c.isOvl g) &&
      (c.ovlClosure f).all fun h => !(c.ovlClosure g).contains h
  | _, _ => false

/-- Two clauses some argument of which `headApart` finds apart. -/
def _root_.KCore.Semantics.clausesHeadApart (c : Semantics) (cl cl' : Clause) : Bool :=
  (cl.pats.zip cl'.pats).any fun (p, q) => c.headApart p q

/-- `fnExclusiveI`'s cases for a pair of clauses whose patterns may apply overloading symbols:
`pairAgreeL` where neither clause's patterns apply one that overloads a symbol (`ovlFree`, which
`overlap` reads), an instance at which the pair agrees, a pair that does not compete
(`notCompeting`), one right-hand side,
or heads apart at some argument (`clausesHeadApart`). -/
def _root_.KCore.Semantics.pairAgreeO (c : Semantics) (heads : List CtorSig) (cl cl' : Clause) : Bool :=
  (c.ovlFreeList cl.pats && c.ovlFreeList cl'.pats && c.pairAgreeL heads cl cl') ||
  (cl.prio == cl'.prio && (c.instAgree heads cl cl' || c.instAgree heads cl' cl)) ||
  notCompeting cl cl' || clausesAgree cl cl' || c.clausesHeadApart cl cl'

/-- `pairAgreeO` for each pair of clauses. -/
def _root_.KCore.Semantics.fnExclusiveIO (c : Semantics) (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all fun (cl, cl') => c.pairAgreeO heads cl cl'

/-- The functions whose equations of one priority `fnExclusiveI` does not show to agree; where
the definition has overloading symbols, `fnExclusiveIO` (a pattern applying an overloading symbol
that overloads a symbol denotes the normal form of its arguments' values, an injection or another
symbol's term where an overload covers them, which `overlap` does not read). -/
def _root_.KCore.Semantics.agreeObligationsI (c : Semantics) : List Sym :=
  (c.fns.filter fun f => !(bif c.ovls.isEmpty then c.fnExclusiveI (c.fns.map Fn.sig) f
    else c.fnExclusiveIO (c.fns.map Fn.sig) f)).map (·.label)

/-- A pair `pairAgreeL` accepts is coherent, in both orders (`fnExclusiveL_sound` on the function
with that pair as its clauses). -/
theorem pairAgreeL_sound (hmc : MatchCtxO c) {heads : List CtorSig} {f : Fn} {cl cl' : Clause}
    (hf : c.ovlFreeList cl.pats = true) (hf' : c.ovlFreeList cl'.pats = true)
    (hc : c.clauseSorted f heads cl = true) (hc' : c.clauseSorted f heads cl' = true)
    (hx : cl.exs = []) (hx' : cl'.exs = [])
    (h : c.pairAgreeL heads cl cl' = true)
    (hprio : cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio)) :
    CoherentPlain c cl cl' ∧ CoherentPlain c cl' cl := by
  by_cases hn : notCompeting cl cl' = true
  · exact (notCompeting_iff.mp hn hprio).elim
  let g : Fn := { f with clauses := [cl, cl'] }
  have hg : c.fnExclusiveL heads g = true := by
    simp only [Semantics.fnExclusiveL, g, pairs, List.map_cons, List.map_nil,
      List.append_nil, List.all_cons, List.all_nil, Bool.and_true]
    simp only [Semantics.pairAgreeL, Bool.eq_false_iff.mpr hn, Bool.false_or] at h
    exact h
  have hcls : ∀ x ∈ g.clauses, c.clauseSorted g heads x = true := by
    intro x hx
    simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hc
    · exact hc'
  have hfr : ∀ x ∈ g.clauses, c.ovlFreeList x.pats = true := by
    intro x hx
    simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hf
    · exact hf'
  have hxs : ∀ x ∈ g.clauses, x.exs = [] := by
    intro x hx''
    simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hx''
    rcases hx'' with rfl | rfl
    · exact hx
    · exact hx'
  exact fnExclusiveL_sound hmc hfr hcls hxs hg cl cl' (by simp [g, pairs]) hprio

/-- **The equations `fnExclusiveI` accepts agree.** -/
theorem fnExclusiveI_sound (hmc : MatchCtxO c) {heads : List CtorSig} {f : Fn}
    (hfr : ∀ cl ∈ f.clauses, c.ovlFreeList cl.pats = true) (hcls : ∀ cl ∈ f.clauses, c.clauseSorted f heads cl = true)
    (hxs : ∀ cl ∈ f.clauses, cl.exs = []) (h : c.fnExclusiveI heads f = true) :
    ClausesAgreePlain c f := by
  intro cl cl' hp hprio
  have hpair := List.all_eq_true.mp h _ hp
  obtain ⟨h1, h2⟩ := mem_pairs hp
  have hc1 := hcls cl h1
  have hc2 := hcls cl' h2
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hpair
  rcases hpair with hl | ⟨-, hi | hi⟩
  · exact pairAgreeL_sound hmc (hfr cl h1) (hfr cl' h2) hc1 hc2 (hxs cl h1) (hxs cl' h2) hl hprio
  · have hc1' := hc1; have hc2' := hc2
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1' hc2'
    replace hc1' := hc1'.1
    replace hc2' := hc2'.1
    exact instAgree_sound hmc hc1'.1.1.1.1.1 hc2'.1.1.1.1.1 (hxs cl h1) (hxs cl' h2) hi
  · have hc1' := hc1; have hc2' := hc2
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1' hc2'
    replace hc1' := hc1'.1
    replace hc2' := hc2'.1
    exact (instAgree_sound hmc hc2'.1.1.1.1.1 hc1'.1.1.1.1.1 (hxs cl' h2) (hxs cl h1) hi).symm

theorem ovlClosure_self (f : Sym) : f ∈ c.ovlClosure f := by
  simp [Semantics.ovlClosure, Semantics.ovlReach]

/-- A pattern headed by a constructor or an overloading symbol, of sort s, denotes `h(ū)` lifted to
s, for h in its head's overload closure (`norm_head`). -/
theorem patVal_head (hmc : MatchCtxO c) {σ : Subst} {vars : List Srt} (hσ : c.WellSorted vars σ)
    {f : Sym} {ps : List Term} {s : Srt} {v : GroundTerm}
    (hs : sortOfTerm c.patCtxAll vars (.app f ps) = some s) (hk : (c.isCtor f || c.isOvl f) = true)
    (h : PatVal c σ (.app f ps) v) : ∃ A g us, v = lift A s (.ctor g us) ∧ g ∈ c.ovlClosure f := by
  rcases Bool.or_eq_true_iff.mp hk with hc | ho
  · obtain ⟨vs, rfl, -⟩ := PatVal.ctor_shape hmc hc h
    exact ⟨s, f, vs, (OvlLaws.lift_self s _).symm, ovlClosure_self f⟩
  · obtain ⟨vs, hvs, hv⟩ := PatVal.ovl_inv ho h
    obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp hs
    obtain ⟨o, hlo, rfl⟩ := patCtxAll_ovl_lookup ho hk'
    obtain ⟨-, hn, -, -, hks, -⟩ := OvlLaws.ovl_facts_ovlF hmc.ovlHyp.fnFacts hlo
    obtain ⟨A, g, us, he, hg⟩ := OvlLaws.norm_head_ovlF hmc.ovlHyp hmc.ovlHyp.fnFacts hks
      (patVals_sortedAllO hmc hσ hvs hargs) (OvlLaws.fnCover_none_of_ok hmc.ovlHyp.ok _ _)
    rw [hn] at he hg
    exact ⟨A, g, us, by rw [← hv]; exact he, hg⟩

/-- **Two patterns of one sort that `headApart` finds apart denote no value in common.** -/
theorem headApart_sound (hmc : MatchCtxO c) {vars vars' : List Srt} {σ σ' : Subst}
    (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') {p q : Term} {s : Srt} {v : GroundTerm}
    (hs : sortOfTerm c.patCtxAll vars p = some s) (hs' : sortOfTerm c.patCtxAll vars' q = some s)
    (ha : c.headApart p q = true) (h : PatVal c σ p v) (h' : PatVal c σ' q v) : False := by
  obtain ⟨hsp, hp⟩ := peelAs_patVal hs h
  obtain ⟨hsq, hq⟩ := peelAs_patVal hs' h'
  unfold Semantics.headApart at ha
  generalize peelAs p = p₀ at hsp hp ha
  generalize peelAs q = q₀ at hsq hq ha
  cases p₀ with
  | app f ps =>
    cases q₀ with
    | app g qs =>
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at ha
      obtain ⟨⟨hkf, hkg⟩, hdis⟩ := ha
      obtain ⟨A, h₁, us, rfl, hm₁⟩ := patVal_head hmc hσ hsp hkf hp
      obtain ⟨A', h₂, us', he, hm₂⟩ := patVal_head hmc hσ' hsq hkg hq
      obtain ⟨rfl, -⟩ := OvlLaws.lift_ctor_inj he
      have := hdis h₁ hm₁
      rw [List.contains_iff_mem.mpr hm₂] at this
      cases this
    | _ => simp at ha
  | _ => simp at ha

/-- Two clauses of one argument sorts that `clausesHeadApart` accepts match no argument list in
common. -/
theorem clausesHeadApart_sound (hmc : MatchCtxO c) {cl cl' : Clause} {ss : List Srt}
    (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some ss)
    (hpt' : sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some ss)
    (ha : c.clausesHeadApart cl cl' = true) {vs : List GroundTerm} {σ σ' : Subst}
    (hσ : c.WellSorted cl.vars σ) (hσ' : c.WellSorted cl'.vars σ')
    (hm : PatVals c σ cl.pats vs) (hm' : PatVals c σ' cl'.pats vs) : False := by
  simp only [Semantics.clausesHeadApart, List.any_eq_true] at ha
  obtain ⟨⟨p, q⟩, hpq, hap⟩ := ha
  suffices key : ∀ (ps qs : List Term) (vs : List GroundTerm) (ss : List Srt),
      sortsOfTerms c.patCtxAll cl.vars ps = some ss → sortsOfTerms c.patCtxAll cl'.vars qs = some ss →
      PatVals c σ ps vs → PatVals c σ' qs vs → (p, q) ∈ ps.zip qs → False from
    key _ _ _ _ hpt hpt' hm hm' hpq
  intro ps
  induction ps with
  | nil => intro qs _ _ _ _ _ _ h; simp at h
  | cons p₀ ps ih =>
    intro qs vs ss hs hs' h h' hz
    cases qs with
    | nil => simp at hz
    | cons q₀ qs =>
      obtain ⟨v, vs₁, rfl, h1, h2⟩ := PatVals.cons_inv' h
      obtain ⟨v', vs₁', he, h1', h2'⟩ := PatVals.cons_inv' h'
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨s₁, ss₁, hs₁, hs₂, rfl⟩ := sortsOfTerms_cons.mp hs
      obtain ⟨s₁', ss₁', hs₁', hs₂', he'⟩ := sortsOfTerms_cons.mp hs'
      simp only [List.cons.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, rfl⟩ | hz
      · exact headApart_sound hmc hσ hσ' hs₁ hs₁' hap h1 h1'
      · exact ih qs vs₁ _ hs₂ hs₂' h2 h2' hz

/-- **The equations `fnExclusiveIO` accepts agree.** -/
theorem fnExclusiveIO_sound (hmc : MatchCtxO c) {heads : List CtorSig} {f : Fn}
    (hcls : ∀ cl ∈ f.clauses, c.clauseSorted f heads cl = true)
    (hxs : ∀ cl ∈ f.clauses, cl.exs = []) (h : c.fnExclusiveIO heads f = true) :
    ClausesAgreePlain c f := by
  intro cl cl' hp hprio
  have hpair := List.all_eq_true.mp h _ hp
  obtain ⟨h1, h2⟩ := mem_pairs hp
  have hc1 := hcls cl h1
  have hc2 := hcls cl' h2
  have hc1' := hc1; have hc2' := hc2
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1' hc2'
  replace hc1' := hc1'.1
  replace hc2' := hc2'.1
  simp only [Semantics.pairAgreeO, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hpair
  rcases hpair with ((((⟨⟨hf1, hf2⟩, hl⟩ | ⟨-, hi | hi⟩) | hne) | ha) | hh)
  · exact pairAgreeL_sound hmc hf1 hf2 hc1 hc2 (hxs cl h1) (hxs cl' h2) hl hprio
  · exact instAgree_sound hmc hc1'.1.1.1.1.1 hc2'.1.1.1.1.1 (hxs cl h1) (hxs cl' h2) hi
  · exact (instAgree_sound hmc hc2'.1.1.1.1.1 hc1'.1.1.1.1.1 (hxs cl' h2) (hxs cl h1) hi).symm
  · exact (notCompeting_iff.mp hne hprio).elim
  · exact ⟨fun vs σ σ' _ _ _ _ _ _ => .inl (clausesAgree_sound ha σ σ').1,
      fun vs σ' σ _ _ _ _ _ _ => .inl (clausesAgree_sound ha σ σ').2⟩
  · exact ⟨fun vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ _ _ _ _ =>
        (clausesHeadApart_sound hmc hc1'.1.1.1.1.1 hc2'.1.1.1.1.1 hh
          ((wellSortedAt_univ (hxs cl h1)).mp hσ) ((wellSortedAt_univ (hxs cl' h2)).mp hσ') hm hm').elim,
      fun vs σ' σ ⟨hσ', hm', _⟩ ⟨hσ, hm, _⟩ _ _ _ _ =>
        (clausesHeadApart_sound hmc hc1'.1.1.1.1.1 hc2'.1.1.1.1.1 hh
          ((wellSortedAt_univ (hxs cl h1)).mp hσ) ((wellSortedAt_univ (hxs cl' h2)).mp hσ') hm hm').elim⟩

/-- In a core that `sortedOK` and `srReady` accept, with the matcher's facts `MatchCtxO`
(overloading symbols admitted), each two equations of one priority of each function are coherent:
by `fnExclusiveI_sound` (without overloading symbols) or `fnExclusiveIO_sound`, and by the named
obligation for the functions `agreeObligationsI` names. -/
theorem clausesAgree_of_IO {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true)
    (hmc : MatchCtxO c)
    (hob : ∀ f ∈ c.agreeObligationsI, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) :
    ∀ fn ∈ c.fns, ClausesAgree c fn := by
  intro fn hfn
  have hsc := sortCtx_of_all hok hsr hmc.ovlCase
  by_cases hx : (bif c.ovls.isEmpty then c.fnExclusiveI (c.fns.map Fn.sig) fn
      else c.fnExclusiveIO (c.fns.map Fn.sig) fn) = true
  · have hf := hok
    replace hf := Semantics.sortedOK_sorted hf
    simp only [Bool.and_eq_true, List.all_eq_true] at hf
    cases he : c.ovls.isEmpty
    · rw [he, Bool.cond_false] at hx
      exact (fnExclusiveIO_sound hmc (hf.1.2 fn hfn) (Semantics.fnsNoExs_of_sortedOK hok fn hfn) hx).agree (Semantics.fnsNoExs_of_sortedOK hok fn hfn)
    · rw [he, Bool.cond_true] at hx
      exact (fnExclusiveI_sound hmc (fun _ _ => ovlFreeList_of_nil (List.isEmpty_iff.mp he) _) (hf.1.2 fn hfn)
        (Semantics.fnsNoExs_of_sortedOK hok fn hfn) hx).agree
        (Semantics.fnsNoExs_of_sortedOK hok fn hfn)
  · refine hob fn.label ?_ fn ?_
    · simp only [Semantics.agreeObligationsI, List.mem_map, List.mem_filter]
      exact ⟨fn, ⟨hfn, by rw [Bool.eq_false_iff.mpr hx]; rfl⟩, rfl⟩
    · rw [Semantics.lookupFn_eq]
      exact find?_label hsc.nodupFns (List.mem_append_left _ hfn)

/-- `clausesAgree_of_IO` where `matchReady` holds (no overloading symbol). -/
theorem clausesAgree_of_I {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true)
    (hob : ∀ f ∈ c.agreeObligationsI, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) :
    ∀ fn ∈ c.fns, ClausesAgree c fn :=
  clausesAgree_of_IO hok hsr (Exec.matchCtx_of hmr) hob

/-! ## Read from the tables -/

def _root_.KCore.Semantics.instAgreeT (T : Tables) (c : Semantics) (heads : List CtorSig) (cl cl' : Clause) : Bool :=
  match c.instOfList [] cl.pats cl'.pats with
  | none => false
  | some θ =>
    (boundBy θ cl.rhs && Term.beq (substT θ cl.rhs) cl'.rhs && cl.ens.isNone && cl'.ens.isNone) ||
    (match cl.req with
     | some q => boundBy θ q &&
         (c.reqsExclusiveT T heads cl'.vars (some (substT θ q)) cl'.req ||
          c.reqsExclusiveT T heads cl'.vars cl'.req (some (substT θ q)) ||
          c.litsApartI (lits (substT θ q)) (reqLits cl'.req))
     | none => false)

def _root_.KCore.Semantics.fnExclusiveIT (T : Tables) (c : Semantics) (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all fun (cl, cl') => (notCompeting cl cl' || (cl.prio != cl'.prio && !cl.aside && !cl'.aside) ||
    !overlapList (Semantics.meetT T) c.collHead cl.pats cl'.pats ||
    (c.clauseFixed cl && (c.clausesExclusiveT T heads cl cl' || c.clausesExclusiveT T heads cl' cl)) ||
    clausesAgree cl cl' || c.clausesListApartT T cl cl' || guardApart cl cl' || guardApart cl' cl ||
    (c.clauseFixed cl && negConjApart cl cl')) ||
    (cl.prio == cl'.prio && (c.instAgreeT T heads cl cl' || c.instAgreeT T heads cl' cl))

def _root_.KCore.Semantics.fnExclusiveIOT (T : Tables) (c : Semantics) (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all fun (cl, cl') =>
    (c.ovlFreeList cl.pats && c.ovlFreeList cl'.pats && (notCompeting cl cl' || (cl.prio != cl'.prio && !cl.aside && !cl'.aside) ||
      !overlapList (Semantics.meetT T) c.collHead cl.pats cl'.pats ||
      (c.clauseFixed cl && (c.clausesExclusiveT T heads cl cl' || c.clausesExclusiveT T heads cl' cl)) ||
      clausesAgree cl cl' || c.clausesListApartT T cl cl' || guardApart cl cl' || guardApart cl' cl ||
      (c.clauseFixed cl && negConjApart cl cl'))) ||
    (cl.prio == cl'.prio && (c.instAgreeT T heads cl cl' || c.instAgreeT T heads cl' cl)) ||
    notCompeting cl cl' || clausesAgree cl cl' || c.clausesHeadApart cl cl'

/-- `agreeObligationsI`, read from the tables. -/
def _root_.KCore.Semantics.agreeObligationsIT (T : Tables) (c : Semantics) : List Sym :=
  (c.fns.filter fun f => !(bif c.ovls.isEmpty then c.fnExclusiveIT T (c.fns.map Fn.sig) f
    else c.fnExclusiveIOT T (c.fns.map Fn.sig) f)).map (·.label)

theorem fnExclusiveIT_tables (heads : List CtorSig) (f : Fn) :
    c.fnExclusiveIT (tables c) heads f = c.fnExclusiveI heads f := by
  simp only [Semantics.fnExclusiveIT, Semantics.fnExclusiveI, Semantics.pairAgreeL,
    Semantics.instAgreeT, Semantics.instAgree, Semantics.clausesListApartT,
    Semantics.clausesListApart, Semantics.listApartT, Semantics.listApart, meetT_tables]; rfl

theorem fnExclusiveIOT_tables (heads : List CtorSig) (f : Fn) :
    c.fnExclusiveIOT (tables c) heads f = c.fnExclusiveIO heads f := by
  simp only [Semantics.fnExclusiveIOT, Semantics.fnExclusiveIO, Semantics.pairAgreeO, Semantics.pairAgreeL,
    Semantics.instAgreeT, Semantics.instAgree, Semantics.clausesListApartT,
    Semantics.clausesListApart, Semantics.listApartT, Semantics.listApart, meetT_tables]; rfl

/-- The functions `agreeObligationsI` names, read from the tables. -/
theorem agreeObligationsI_of_T {T : Tables} (hT : T = tables c) {l : List Sym}
    (h : c.agreeObligationsIT T = l) : c.agreeObligationsI = l := by
  subst hT
  rw [← h]
  simp only [Semantics.agreeObligationsIT, Semantics.agreeObligationsI, fnExclusiveIT_tables,
    fnExclusiveIOT_tables]

kernel_rfl Semantics.agreeObligationsI_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).agreeObligationsI = c.agreeObligationsI

end KCore.Det
