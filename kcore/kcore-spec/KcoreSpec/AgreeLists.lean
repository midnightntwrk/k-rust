/-
  KCore, checked layer: more functions whose equations of one priority agree (`fnExclusiveL`,
  `fnExclusiveL_sound`, `ClausesAgree`) than `fnExclusiveOK` confirms. Two more cases, each a pair of
  equations that never both apply:

  - **list patterns apart** (`listApart`): `overlap` reads two patterns headed by collection symbols
    as overlapping whatever they are, since a map or a set is the same value however it is built.
    A list pattern of the forms KCore matches is different: `.List` denotes the empty list, and
    `ListItem(P)` and `ListItem(P) L` denote lists whose first element is P's value. So `.List` and
    a pattern with a first element are apart, and so are two patterns with first elements that
    `overlap` finds apart (`ListItem(inj{Bytes,KItem}(B)) L` and
    `ListItem(inj{SubstateLogEntry,KItem}(E)) L'`). Read only where no constructor bears the list
    symbols' numbers (`listSymsFree`), so that the patterns denote lists.
  - **exclusive `requires` in the other order**: `clausesExclusive` compares the first clause's
    literals against the second's; the exclusion is symmetric (both apply under one match, the
    patterns being one list), so the second clause's literals may be compared against the first's
    (`sgn`'s `0 <=Int W andBool W <Int 2^255` against `W <Int 0 orBool 2^256 <=Int W`).

  - **a literal against a guard** (`guardApart`): one clause has the Int literal k at an argument
    where the other has a variable x, and the other's `requires` asserts of x a bound k is outside
    (`x >Int 1`, `x >=Int 128`, `x ==Int 3`) or `x =/=Int k`: where the first matches, the second's
    `requires` is not true (`#rlpEncodeInt(0)` against `#rlpEncodeInt(I) requires I >=Int 128`);
  - **a negated conjunction** (`negConjApart`): two clauses with one variable list and one pattern
    list, the first fixed, one asserting `notBool (A₁ andBool A₂ …)` and the other each `Aᵢ`
    (`bit`'s `0 <=Int N andBool N <Int 256` and its negation).

  `agreeObligationsL` names the functions `fnExclusiveL` does not confirm.
-/
import KcoreSpec.FnExclusive
import KcoreSpec.UniqLists
import KcoreSpec.TablesChecked

set_option autoImplicit false

namespace KCore.Det

open KCore KCore.Exec GroundTerm

variable {c : Semantics}

/-- No constructor bears the number of a list pattern symbol. -/
def _root_.KCore.Semantics.listSymsFree (c : Semantics) : Bool :=
  listPatternHooks.all fun f => !(lookupSig c.ctorSigs f).isSome

/-- The first element's pattern of a list pattern with one: `ListItem(P)`, `ListItem(P) L`. -/
def listFirst : Term → Option Term
  | .app f [x] => if f == listElem then some x else none
  | .app f [.app e [x], _] => if f == listConcat && e == listElem then some x else none
  | _ => none

/-- `.List`. -/
def isListUnit : Term → Bool
  | .app f [] => f == listUnit
  | _ => false

/-- Two patterns (aliases peeled) that denote no list in common: the empty list against one with a
first element, or two with first elements `overlap` finds apart. -/
def _root_.KCore.Semantics.listApart (c : Semantics) (p q : Term) : Bool :=
  (isListUnit (peelAs p) && (listFirst (peelAs q)).isSome) ||
  (isListUnit (peelAs q) && (listFirst (peelAs p)).isSome) ||
  (match listFirst (peelAs p), listFirst (peelAs q) with
   | some x, some y => !overlap c.meet c.collHead x y
   | _, _ => false)

/-- Two clauses some argument of which `listApart` finds apart. -/
def _root_.KCore.Semantics.clausesListApart (c : Semantics) (cl cl' : Clause) : Bool :=
  c.listSymsFree && (cl.pats.zip cl'.pats).any fun (p, q) => c.listApart p q

/-- The literals of a `requires` (none without one). -/
def reqLits : Option Term → List (Term × Bool)
  | some q => lits q
  | none => []

/-- A literal of the variable x that the Int value k does not meet: a bound outside which k lies,
or `x =/=Int k`. -/
def guardExcludes (x : Nat) (k : Int) (l : Term × Bool) : Bool :=
  (match Semantics.intBound l with
   | some (.var y, lo, hi) => y == x && ((match lo with | some a => decide (k < a) | none => false) ||
       (match hi with | some b => decide (b < k) | none => false))
   | _ => false) ||
  (match l with
   | (.app f [.var y, .dv s (.int k')], true) => f == intNe && y == x && s == Srt.int && k' == k
   | (.app f [.dv s (.int k'), .var y], true) => f == intNe && y == x && s == Srt.int && k' == k
   | _ => false)

/-- At some argument, the first clause's pattern is the Int literal k and the second's a variable x,
and a literal of the second's `requires` excludes k for x (`guardExcludes`). -/
def guardApart (cl cl' : Clause) : Bool :=
  (cl.pats.zip cl'.pats).any fun (p, q) => match peelAs p, peelAs q with
    | .dv s (.int k), .var x => s == Srt.int && (reqLits cl'.req).any (guardExcludes x k)
    | _, _ => false

/-- One `requires` asserts `notBool A` for a conjunction A (two literals or more) whose literals
the other asserts each. -/
def negConjLits (ls ls' : List (Term × Bool)) : Bool :=
  ls.any fun (t, b) => !b && decide (2 ≤ (lits t).length) &&
    (lits t).all fun (A, d) => ls'.any fun (A', d') => Term.beq A A' && d == d'

/-- Two clauses with one variable list and one pattern list whose `requires` are a negated
conjunction and its conjuncts (`negConjLits`, either way). -/
def negConjApart (cl cl' : Clause) : Bool :=
  cl.vars == cl'.vars && Term.beqList cl.pats cl'.pats &&
    (negConjLits (reqLits cl.req) (reqLits cl'.req) || negConjLits (reqLits cl'.req) (reqLits cl.req))

/-- `fnExclusiveOK`'s cases, with list patterns apart and the `requires` compared in either order. -/
def _root_.KCore.Semantics.fnExclusiveL (c : Semantics) (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all (fun (cl, cl') => (cl.prio != cl'.prio && !cl.aside && !cl'.aside) ||
    !overlapList c.meet c.collHead cl.pats cl'.pats ||
    (c.clauseFixed cl && (c.clausesExclusive heads cl cl' || c.clausesExclusive heads cl' cl)) ||
    clausesAgree cl cl' || c.clausesListApart cl cl' || guardApart cl cl' || guardApart cl' cl ||
    (c.clauseFixed cl && negConjApart cl cl'))

/-- The functions whose equations of one priority `fnExclusiveL` does not show to agree. -/
def _root_.KCore.Semantics.agreeObligationsL (c : Semantics) : List Sym :=
  (c.fns.filter fun f => !c.fnExclusiveL (c.fns.map Fn.sig) f).map (·.label)

/-! ## Soundness -/

theorem listSymsFree_ctor (h : c.listSymsFree = true) {f : Sym} (hf : f ∈ listPatternHooks) :
    c.isCtor f = false := by
  have := List.all_eq_true.mp h f hf
  simpa [Semantics.isCtor] using this

theorem sig_listElem : lookupSig hookSigs listElem = some ⟨listElem, [Srt.kitem], Srt.list⟩ := by decide

/-- `ListItem(P)`'s argument has a sort in a left-hand side's context. -/
theorem patCtxAll_listElem {vars : List Srt} {ps : List Term} {s : Srt}
    (hct : c.isCtor listElem = false) (ht : sortOfTerm c.patCtxAll vars (.app listElem ps) = some s) :
    sortsOfTerms c.patCtxAll vars ps = some [Srt.kitem] := by
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  rcases patCtxAll_collPat_lookup hct (isCollPat_list (by decide)) hk' with ⟨-, hk⟩ | ⟨hh, -⟩
  · rw [sig_listElem] at hk
    cases hk
    exact hargs
  · cases hh

/-- What a pattern with a first element denotes: a list whose first element its first element's
pattern denotes, the pattern having a sort. -/
theorem listFirst_val (hfree : c.listSymsFree = true) {σ : Subst} {vars : List Srt} {p x : Term}
    {s : Srt} {v : GroundTerm} (hx : listFirst p = some x) (hs : sortOfTerm c.patCtxAll vars p = some s)
    (h : PatVal c σ p v) :
    ∃ w es sx, v = .list Srt.list (w :: es) ∧ PatVal c σ x w ∧ sortOfTerm c.patCtxAll vars x = some sx := by
  have hce := listSymsFree_ctor hfree (f := listElem) (by decide)
  have hcc := listSymsFree_ctor hfree (f := listConcat) (by decide)
  unfold listFirst at hx
  split at hx
  · rename_i f x'
    split at hx
    · rename_i hf
      have hf := beq_iff_eq.mp hf
      subst hf
      cases hx
      obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hce (isCollPat_list (by decide)) h
      obtain ⟨w, rfl, rfl⟩ := collVal_listElem hv
      obtain ⟨_, _, he, hw, -⟩ := PatVals.cons_inv' hvs
      cases he
      obtain ⟨sx, _, hsx, -, -⟩ := sortsOfTerms_cons.mp (patCtxAll_listElem hce hs)
      exact ⟨w, [], sx, rfl, hw, hsx⟩
    · cases hx
  · rename_i f e x' rest
    split at hx
    · rename_i hfe
      simp only [Bool.and_eq_true, beq_iff_eq] at hfe
      obtain ⟨rfl, rfl⟩ := hfe
      cases hx
      obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hcc (isCollPat_list (by decide)) h
      obtain ⟨s₁, a, t, b, rfl, rfl⟩ := collVal_listConcat hv
      obtain ⟨_, _, he1, hE, -⟩ := PatVals.cons_inv' hvs
      cases he1
      obtain ⟨ws, hws, hw⟩ := PatVal.coll_inv hce (isCollPat_list (by decide)) hE
      obtain ⟨w, rfl, hw⟩ := collVal_listElem hw
      cases hw
      obtain ⟨_, _, he2, hW, -⟩ := PatVals.cons_inv' hws
      cases he2
      obtain ⟨hsE, -⟩ := sortsOfTerms_two (patCtxAll_listConcat hcc hs)
      obtain ⟨sx, _, hsx, -, -⟩ := sortsOfTerms_cons.mp (patCtxAll_listElem hce hsE)
      exact ⟨w, b, sx, rfl, hW, hsx⟩
    · cases hx
  · cases hx

theorem listUnit_val (hfree : c.listSymsFree = true) {σ : Subst} {p : Term} {v : GroundTerm}
    (hu : isListUnit p = true) (h : PatVal c σ p v) : v = .list Srt.list [] := by
  have hcu := listSymsFree_ctor hfree (f := listUnit) (by decide)
  unfold isListUnit at hu
  split at hu
  · rename_i f
    have hf := beq_iff_eq.mp hu
    subst hf
    obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hcu (isCollPat_list (by decide)) h
    cases hvs
    unfold Semantics.collVal at hv
    rw [if_pos (by decide), hook_listUnit_eq] at hv
    exact (Option.some.inj hv).symm
  · cases hu

theorem listFirst_free {p x : Term} (hf : c.ovlFree p = true) (hx : listFirst p = some x) :
    c.ovlFree x = true := by
  unfold listFirst at hx
  split at hx
  · split at hx
    · cases hx; exact (ovlFreeList_cons (ovlFree_app hf).2).1
    · cases hx
  · split at hx
    · cases hx; exact (ovlFreeList_cons (ovlFree_app (ovlFreeList_cons (ovlFree_app hf).2).1).2).1
    · cases hx
  · cases hx

/-- **Two patterns `listApart` finds apart, applying no overloading symbol, denote no value in
common.** -/
theorem listApart_sound (hmc : MatchCtxO c) (hfree : c.listSymsFree = true) {vars vars' : List Srt}
    {σ σ' : Subst} (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') {p q : Term} {s s' : Srt}
    {v : GroundTerm} (hpf : c.ovlFree p = true) (hqf : c.ovlFree q = true)
    (hs : sortOfTerm c.patCtxAll vars p = some s)
    (hs' : sortOfTerm c.patCtxAll vars' q = some s') (ha : c.listApart p q = true)
    (h : PatVal c σ p v) (h' : PatVal c σ' q v) : False := by
  obtain ⟨hsp, hp⟩ := peelAs_patVal hs h
  obtain ⟨hsq, hq⟩ := peelAs_patVal hs' h'
  simp only [Semantics.listApart, Bool.or_eq_true, Bool.and_eq_true, Option.isSome_iff_exists] at ha
  rcases ha with ((⟨hu, x, hx⟩ | ⟨hu, x, hx⟩) | ha)
  · obtain ⟨w, es, _, rfl, -⟩ := listFirst_val hfree hx hsq hq
    have := listUnit_val hfree hu hp
    simp at this
  · obtain ⟨w, es, _, rfl, -⟩ := listFirst_val hfree hx hsp hp
    have := listUnit_val hfree hu hq
    simp at this
  · split at ha
    · rename_i x y hx hy
      obtain ⟨w, es, sx, rfl, hw, hsx⟩ := listFirst_val hfree hx hsp hp
      obtain ⟨w', es', sy, he, hw', hsy⟩ := listFirst_val hfree hy hsq hq
      simp only [GroundTerm.list.injEq, List.cons.injEq, true_and] at he
      obtain ⟨rfl, -⟩ := he
      exact overlap_sound_termF hmc hσ hσ' x (listFirst_free (ovlFree_peelAs hpf) hx)
        (listFirst_free (ovlFree_peelAs hqf) hy) hsx hsy (by simpa using ha) hw hw'
    · cases ha

/-- Two clauses `clausesListApart` accepts match no argument list in common. -/
theorem clausesListApart_sound (hmc : MatchCtxO c) {cl cl' : Clause} {ss ss' : List Srt}
    (hf : c.ovlFreeList cl.pats = true) (hf' : c.ovlFreeList cl'.pats = true)
    (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some ss)
    (hpt' : sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some ss')
    (ha : c.clausesListApart cl cl' = true) {vs : List GroundTerm} {σ σ' : Subst}
    (hσ : c.WellSorted cl.vars σ) (hσ' : c.WellSorted cl'.vars σ')
    (hm : PatVals c σ cl.pats vs) (hm' : PatVals c σ' cl'.pats vs) : False := by
  simp only [Semantics.clausesListApart, Bool.and_eq_true, List.any_eq_true] at ha
  obtain ⟨hfree, ⟨p, q⟩, hpq, hap⟩ := ha
  have hpf := ovlFreeList_iff.mp hf p (List.of_mem_zip hpq).1
  have hqf := ovlFreeList_iff.mp hf' q (List.of_mem_zip hpq).2
  suffices key : ∀ (ps qs : List Term) (vs : List GroundTerm) (ss ss' : List Srt),
      sortsOfTerms c.patCtxAll cl.vars ps = some ss → sortsOfTerms c.patCtxAll cl'.vars qs = some ss' →
      PatVals c σ ps vs → PatVals c σ' qs vs → (p, q) ∈ ps.zip qs → False from
    key _ _ _ _ _ hpt hpt' hm hm' hpq
  intro ps
  induction ps with
  | nil => intro qs _ _ _ _ _ _ _ h; simp at h
  | cons p₀ ps ih =>
    intro qs vs ss ss' hs hs' h h' hz
    cases qs with
    | nil => simp at hz
    | cons q₀ qs =>
      obtain ⟨v, vs₁, rfl, h1, h2⟩ := PatVals.cons_inv' h
      obtain ⟨v', vs₁', he, h1', h2'⟩ := PatVals.cons_inv' h'
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨_, _, hs₁, hs₂, -⟩ := sortsOfTerms_cons.mp hs
      obtain ⟨_, _, hs₁', hs₂', -⟩ := sortsOfTerms_cons.mp hs'
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, rfl⟩ | hz
      · exact listApart_sound hmc hfree hσ hσ' hpf hqf hs₁ hs₁' hap h1 h1'
      · exact ih qs vs₁ _ _ hs₂ hs₂' h2 h2' hz

theorem lits_reqLits {σ : Subst} {q : Option Term} (h : ∀ t, q = some t → EvalTerm c σ t (some (bool true)))
    {A : Term} {b : Bool} (hm : (A, b) ∈ reqLits q) : EvalTerm c σ A (some (bool b)) := by
  cases q with
  | none => simp [reqLits] at hm
  | some t => exact lits_sound (h t rfl) hm

theorem mem_subterms_reqLits {q : Option Term} {A : Term} {b : Bool} (hm : (A, b) ∈ reqLits q) :
    ∃ t, q = some t ∧ A ∈ subterms t := by
  cases q with
  | none => simp [reqLits] at hm
  | some t => exact ⟨t, rfl, mem_subterms_of_lits hm⟩

theorem peelAs_patVal' {σ : Subst} : ∀ {p : Term} {v : GroundTerm}, PatVal c σ p v → PatVal c σ (peelAs p) v
  | .as p _, _, h => by simp only [peelAs]; exact peelAs_patVal' (PatVal.as_inv h).1
  | .var _, _, h => h
  | .dv _ _, _, h => h
  | .app _ _, _, h => h
  | .inj _ _ _, _, h => h

/-- A literal `guardExcludes` accepts is not asserted where x is the Int k. -/
theorem guardExcludes_sound {σ : Subst} {x : Nat} {k : Int} {l : Term × Bool}
    (hg : guardExcludes x k l = true) (hx : σ.lookup x = some (.dv Srt.int (.int k)))
    (e : EvalTerm c σ l.1 (some (bool l.2))) : False := by
  obtain ⟨A, b⟩ := l
  simp only [guardExcludes, Bool.or_eq_true] at hg
  rcases hg with hg | hg
  · split at hg
    · rename_i y lo hi hb
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hg
      obtain ⟨rfl, hk⟩ := hg
      obtain ⟨v, X, ev, hX, hlo, hhi⟩ := intBound_sound hb e
      have := EvalTerm.var_inv ev
      rw [hx] at this
      cases this
      simp only [asInt, beq_self_eq_true, ite_true, Option.some.injEq] at hX
      subst hX
      rcases hk with hk | hk
      · cases hlo' : lo with
        | none => rw [hlo'] at hk; cases hk
        | some a => rw [hlo'] at hk; have := hlo a hlo'; simp at hk; omega
      · cases hhi' : hi with
        | none => rw [hhi'] at hk; cases hk
        | some u => rw [hhi'] at hk; have := hhi u hhi'; simp at hk; omega
    · cases hg
  · split at hg
    · rename_i f y s k' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hg
      obtain ⟨v, w, X, Y, ev, ew, hX, hY, hb⟩ := int2_inv rfl hook_intNe e
      have := EvalTerm.var_inv ev
      rw [hx] at this; cases this
      cases ew
      simp only [asInt, beq_self_eq_true, ite_true, Option.some.injEq] at hX hY
      subst hX hY
      simp at hb
    · rename_i f s k' y heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hg
      obtain ⟨v, w, X, Y, ev, ew, hX, hY, hb⟩ := int2_inv rfl hook_intNe e
      have := EvalTerm.var_inv ew
      rw [hx] at this; cases this
      cases ev
      simp only [asInt, beq_self_eq_true, ite_true, Option.some.injEq] at hX hY
      subst hX hY
      simp at hb
    · cases hg

/-- Two clauses `guardApart` accepts never both apply at one argument list. -/
theorem guardApart_sound {cl cl' : Clause} (hg : guardApart cl cl' = true) {vs : List GroundTerm}
    {σ σ' : Subst} (hm : PatVals c σ cl.pats vs) (hm' : PatVals c σ' cl'.pats vs)
    (hq' : ∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) : False := by
  simp only [guardApart, List.any_eq_true] at hg
  obtain ⟨⟨p, q⟩, hpq, hg⟩ := hg
  suffices key : ∀ (ps qs : List Term) (vs : List GroundTerm), PatVals c σ ps vs → PatVals c σ' qs vs →
      (p, q) ∈ ps.zip qs → False from key _ _ _ hm hm' hpq
  intro ps
  induction ps with
  | nil => intro qs _ _ _ h; simp at h
  | cons p₀ ps ih =>
    intro qs vs h h' hz
    cases qs with
    | nil => simp at hz
    | cons q₀ qs =>
      obtain ⟨v, vs₁, rfl, h1, h2⟩ := PatVals.cons_inv' h
      obtain ⟨v', vs₁', he, h1', h2'⟩ := PatVals.cons_inv' h'
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, rfl⟩ | hz
      · have hp := peelAs_patVal' h1
        have hq := peelAs_patVal' h1'
        split at hg
        · rename_i s k x hpk hqx
          simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hg
          obtain ⟨rfl, l, hl, hex⟩ := hg
          rw [hpk] at hp
          rw [hqx] at hq
          cases hp
          exact guardExcludes_sound hex (PatVal.var_inv hq) (lits_reqLits hq' hl)
        · cases hg
      · exact ih qs vs₁ h2 h2' hz

theorem hook_and_false {w₁ w₂ : GroundTerm} (h : bool2 [w₁, w₂] (· && ·) = some (bool false)) :
    w₁ = bool false ∨ w₂ = bool false := by
  unfold bool2 at h
  cases hx : asBool w₁ with
  | none => simp [hx] at h
  | some x =>
  cases hy : asBool w₂ with
  | none => simp [hx, hy] at h
  | some y =>
  simp only [hx, hy, Option.bind_some, Option.map_some, Option.some.injEq] at h
  have := bool_inj h
  cases x <;> cases y <;> simp at this
  · exact .inl (asBool_some hx)
  · exact .inl (asBool_some hx)
  · exact .inr (asBool_some hy)

/-- Where a `requires` is false, one of its literals is asserted the other way. -/
theorem lits_false {σ : Subst} : ∀ {t : Term}, EvalTerm c σ t (some (bool false)) →
    ∃ A b, (A, b) ∈ lits t ∧ EvalTerm c σ A (some (bool (!b)))
  | .app f [t₁, t₂], h => by
    by_cases hf : f = boolAnd
    · subst hf
      generalize ht : Term.app boolAnd [t₁, t₂] = t at h
      generalize hr : some (bool false) = r at h
      cases h with
      | @ctor _ _ _ rs _ _ => cases ht; cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
      | @hook _ _ _ rs r' _ _ hts hh hund =>
        cases ht
        obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
        cases r₁ with
        | none => rw [hund (by simp [allSome])] at hr; cases hr
        | some w₁ =>
          cases r₂ with
          | none => rw [hund (by simp [allSome])] at hr; cases hr
          | some w₂ =>
            have hv := hh [w₁, w₂] (by simp [allSome])
            rw [Semantics.hookRes_of_notKey silentKey_boolAnd, hook_and, Option.some.injEq] at hv
            subst hv
            rcases hook_and_false hr.symm with rfl | rfl
            · obtain ⟨A, b, hm, he⟩ := lits_false h1
              exact ⟨A, b, by simp only [lits, beq_self_eq_true, if_true]; exact List.mem_append_left _ hm, he⟩
            · obtain ⟨A, b, hm, he⟩ := lits_false h2
              exact ⟨A, b, by simp only [lits, beq_self_eq_true, if_true]; exact List.mem_append_right _ hm, he⟩
      | param _ hhk _ _ _ => cases ht; rw [isHook_and] at hhk; cases hhk
      | call _ hhk _ _ _ _ => cases ht; rw [isHook_and] at hhk; cases hhk
      | callUndef _ _ _ _ _ => cases ht; cases hr
      | ovl _ ho _ => cases ht; have hhk := (c.isOvl_parts ho).2.1; rw [isHook_and] at hhk; cases hhk
      | ovlFn _ ho => cases ht; have hhk := (c.isOvl_parts ho).2.1; rw [isHook_and] at hhk; cases hhk
      | _ => cases ht
    · refine ⟨.app f [t₁, t₂], true, ?_, h⟩
      simp [lits, hf]
  | .app f [t], h => by
    by_cases hf : f = boolNot
    · subst hf
      generalize ht : Term.app boolNot [t] = t' at h
      generalize hr : some (bool false) = r at h
      cases h with
      | @ctor _ _ _ rs _ _ => cases ht; cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
      | @hook _ _ _ rs r' _ _ hts hh hund =>
        cases ht
        obtain ⟨r₁, rfl, h1⟩ := evalTerms_one hts
        cases r₁ with
        | none => rw [hund (by simp [allSome])] at hr; cases hr
        | some w =>
          have hv := hh [w] (by simp [allSome])
          rw [Semantics.hookRes_of_notKey silentKey_boolNot, hook_not, Option.some.injEq] at hv
          subst hv
          obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.mp hr.symm
          have := bool_inj he
          simp only [Bool.not_eq_false'] at this
          subst this
          rw [asBool_some hx] at h1
          exact ⟨t, false, by simp [lits], h1⟩
      | param _ hhk _ _ _ => cases ht; rw [isHook_not] at hhk; cases hhk
      | call _ hhk _ _ _ _ => cases ht; rw [isHook_not] at hhk; cases hhk
      | callUndef _ _ _ _ _ => cases ht; cases hr
      | ovl _ ho _ => cases ht; have hhk := (c.isOvl_parts ho).2.1; rw [isHook_not] at hhk; cases hhk
      | ovlFn _ ho => cases ht; have hhk := (c.isOvl_parts ho).2.1; rw [isHook_not] at hhk; cases hhk
      | _ => cases ht
    · exact ⟨.app f [t], true, by simp [lits, hf], h⟩
  | .dv s l, h => by
    by_cases hl : s == Srt.bool && l == .bool true
    · cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hl
      exact absurd hl.2 (by decide)
    · exact ⟨.dv s l, true, by simp [lits, hl], h⟩
  | .var i, h => ⟨.var i, true, by simp [lits], h⟩
  | .inj a b t, h => ⟨.inj a b t, true, by simp [lits], h⟩
  | .as t i, h => ⟨.as t i, true, by simp [lits], h⟩
  | .app f [], h => ⟨.app f [], true, by simp [lits], h⟩
  | .app f (_ :: _ :: _ :: _), h => ⟨_, true, by simp [lits], h⟩

/-- Two lists of literals `negConjLits` accepts are not all asserted under one substitution,
where the terms inside the first have one result. -/
theorem negConjLits_sound {σ : Subst} {ls ls' : List (Term × Bool)} (h : negConjLits ls ls' = true)
    (hF : (∀ l ∈ ls, ∀ X ∈ subterms l.1, Fun c σ X) ∨ ∀ l ∈ ls', ∀ X ∈ subterms l.1, Fun c σ X)
    (e : ∀ l ∈ ls, EvalTerm c σ l.1 (some (bool l.2))) (e' : ∀ l ∈ ls', EvalTerm c σ l.1 (some (bool l.2))) :
    False := by
  simp only [negConjLits, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨t, b⟩, hm, ⟨⟨hb, -⟩, hall⟩⟩ := h
  simp only at hb hall
  subst hb
  obtain ⟨A, d, hAm, hAe⟩ := lits_false (e _ hm)
  obtain ⟨⟨A', d'⟩, hm', hbeq, hdd⟩ := hall (A, d) hAm
  simp only [beq_iff_eq] at hdd
  subst hdd
  have hA := Term.beq_sound hbeq
  subst hA
  have he' := e' _ hm'
  have hfun : Fun c σ A := hF.elim
    (fun hF => hF _ hm A (subterms_trans (mem_subterms_of_lits hAm) (self_mem_subterms A)))
    (fun hF => hF _ hm' A (self_mem_subterms A))
  have := Option.some.inj (hfun _ _ hAe he')
  have := bool_inj this
  cases d <;> simp at this

/-- Two clauses `negConjApart` accepts, the first fixed, never both apply at one argument list,
where the terms of one of their `requires` have one result under its match. -/
theorem negConjApart_sound (hmc : MatchCtxO c) {cl cl' : Clause} {ss : List Srt}
    (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some ss) (hfx : c.clauseFixed cl = true)
    {x : TermCtx} (hrq' : reqOK x cl'.vars cl'.req = true)
    (h : negConjApart cl cl' = true) {vs : List GroundTerm} {σ σ' : Subst}
    (hσ : c.WellSorted cl.vars σ) (hm : PatVals c σ cl.pats vs)
    (hq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hσ' : c.WellSorted cl'.vars σ') (hm' : PatVals c σ' cl'.pats vs)
    (hq' : ∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true)))
    (hF : (∀ t, cl.req = some t → HDet c σ t) ∨ ∀ t, cl'.req = some t → HDet c σ' t) : False := by
  simp only [negConjApart, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨hv, hp⟩, hx⟩ := h
  have hp := Term.beqList_sound hp
  rw [← hv] at hσ' hrq'
  rw [← hp] at hm'
  unfold Semantics.clauseFixed at hfx
  split at hfx
  · rename_i D hD
    simp only [List.all_eq_true, List.contains_iff_mem, List.mem_range] at hfx
    have hag := uniqList_sound hmc hσ' hσ cl.pats hD hm' hm hpt (fun _ h => by cases h)
    have hagt : ∀ t, cl'.req = some t → ∀ i ∈ varOccs t, σ'.lookup i = σ.lookup i := fun t ht i hi => by
      rw [ht] at hrq'
      exact hag i (hfx i (sortOfTerm_vars (reqOK_some hrq') i hi))
    -- the second clause's literals, read under the first's match
    have e' : ∀ l ∈ reqLits cl'.req, EvalTerm c σ l.1 (some (bool l.2)) := fun l hl => by
      obtain ⟨t, ht, hsub⟩ := mem_subterms_reqLits hl
      exact Exec.EvalTerm.congr (lits_reqLits hq' hl) (fun i hi => hagt t ht i (varOccs_subterms hsub i hi))
    have e : ∀ l ∈ reqLits cl.req, EvalTerm c σ l.1 (some (bool l.2)) := fun l hl => lits_reqLits hq hl
    have hF' : (∀ l ∈ reqLits cl.req, ∀ X ∈ subterms l.1, Fun c σ X) ∨
        ∀ l ∈ reqLits cl'.req, ∀ X ∈ subterms l.1, Fun c σ X := by
      rcases hF with hF | hF
      · refine .inl fun l hl X hX => ?_
        obtain ⟨t, ht, hsub⟩ := mem_subterms_reqLits hl
        exact hF t ht X (subterms_trans hsub hX)
      · refine .inr fun l hl X hX => ?_
        obtain ⟨t, ht, hsub⟩ := mem_subterms_reqLits hl
        exact Fun.congr (fun i hi => (hagt t ht i (varOccs_subterms (subterms_trans hsub hX) i hi)).symm)
          (hF t ht X (subterms_trans hsub hX))
    rcases hx with hx | hx
    · exact negConjLits_sound hx hF' e e'
    · exact negConjLits_sound hx hF'.symm e' e
  · cases hfx

/-- **The equations `fnExclusiveL` accepts agree**: each two of one priority are coherent, in both
orders: `fnExclusiveOK`'s three cases, the `requires` exclusive in either order, or an argument
whose list patterns are apart. -/
theorem fnExclusiveL_sound (hmc : MatchCtxO c) {heads : List CtorSig} {f : Fn}
    (hfr : ∀ cl ∈ f.clauses, c.ovlFreeList cl.pats = true) (hcls : ∀ cl ∈ f.clauses, c.clauseSorted f heads cl = true) (h : c.fnExclusiveL heads f = true) :
    ClausesAgreePlain c f := by
  intro cl cl' hp hprio
  have hpair := List.all_eq_true.mp h _ hp
  obtain ⟨h1, h2⟩ := mem_pairs hp
  have hc1 := hcls cl h1
  have hc2 := hcls cl' h2
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1 hc2
  replace hc1 := hc1.1
  replace hc2 := hc2.1
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, bne_iff_ne, ne_eq] at hpair
  rcases hpair with (((((((hne | ho) | ⟨hfx, hx | hx⟩) | ha) | hl) | hg) | hg) | ⟨hfx, hn⟩)
  · exact (not_compete (by revert hne; simp) hprio).elim
  · exact ⟨fun vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ _ _ _ _ =>
        (overlap_soundF hmc hσ hσ' cl.pats (hfr cl h1) (hfr cl' h2) hc1.1.1.1.1.1 hc2.1.1.1.1.1 ho hm hm').elim,
      fun vs σ' σ ⟨hσ', hm', _⟩ ⟨hσ, hm, _⟩ _ _ _ _ =>
        (overlap_soundF hmc hσ hσ' cl.pats (hfr cl h1) (hfr cl' h2) hc1.1.1.1.1.1 hc2.1.1.1.1.1 ho hm hm').elim⟩
  · exact ⟨fun vs σ σ' ⟨hσ, hm, hq, _⟩ ⟨hσ', hm', hq', _⟩ hd _ _ _ =>
        (clausesExclusive_sound hmc hc1.1.1.1.1.1 hfx hc2.1.1.1.2 hx hσ hm hq hσ' hm' hq' (.inl hd)).elim,
      fun vs σ' σ ⟨hσ', hm', hq', _⟩ ⟨hσ, hm, hq, _⟩ hd _ _ _ =>
        (clausesExclusive_sound hmc hc1.1.1.1.1.1 hfx hc2.1.1.1.2 hx hσ hm hq hσ' hm' hq' (.inr hd)).elim⟩
  · -- the second clause's literals against the first's: one variable list and one pattern list,
    -- so the second clause is fixed too
    simp only [Semantics.clausesExclusive, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨⟨hv, hpb⟩, hx'⟩ := hx
    have hpp := Term.beqList_sound hpb
    have hfx' : c.clauseFixed cl' = true := by
      unfold Semantics.clauseFixed at hfx ⊢; rw [hpp, hv]; exact hfx
    have hpt' : sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some f.args := hc2.1.1.1.1.1
    have hx2 : c.clausesExclusive heads cl' cl = true := by
      simp only [Semantics.clausesExclusive, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨hv, ?_⟩, hx'⟩
      have hpb' := hpb
      rw [← hpp] at hpb' ⊢
      exact hpb'
    exact ⟨fun vs σ σ' ⟨hσ, hm, hq, _⟩ ⟨hσ', hm', hq', _⟩ hd _ _ _ =>
        (clausesExclusive_sound hmc hpt' hfx' hc1.1.1.1.2 hx2 hσ' hm' hq' hσ hm hq (.inr hd)).elim,
      fun vs σ' σ ⟨hσ', hm', hq', _⟩ ⟨hσ, hm, hq, _⟩ hd _ _ _ =>
        (clausesExclusive_sound hmc hpt' hfx' hc1.1.1.1.2 hx2 hσ' hm' hq' hσ hm hq (.inl hd)).elim⟩
  · exact ⟨fun vs σ σ' _ _ _ _ _ _ => .inl (clausesAgree_sound ha σ σ').1,
      fun vs σ' σ _ _ _ _ _ _ => .inl (clausesAgree_sound ha σ σ').2⟩
  · exact ⟨fun vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ _ _ _ _ =>
        (clausesListApart_sound hmc (hfr cl h1) (hfr cl' h2) hc1.1.1.1.1.1 hc2.1.1.1.1.1 hl hσ hσ' hm hm').elim,
      fun vs σ' σ ⟨hσ', hm', _⟩ ⟨hσ, hm, _⟩ _ _ _ _ =>
        (clausesListApart_sound hmc (hfr cl h1) (hfr cl' h2) hc1.1.1.1.1.1 hc2.1.1.1.1.1 hl hσ hσ' hm hm').elim⟩
  · exact ⟨fun vs σ σ' ⟨_, hm, _⟩ ⟨_, hm', hq', _⟩ _ _ _ _ => (guardApart_sound hg hm hm' hq').elim,
      fun vs σ' σ ⟨_, hm', hq', _⟩ ⟨_, hm, _⟩ _ _ _ _ => (guardApart_sound hg hm hm' hq').elim⟩
  · exact ⟨fun vs σ σ' ⟨_, hm, hq, _⟩ ⟨_, hm', _⟩ _ _ _ _ => (guardApart_sound hg hm' hm hq).elim,
      fun vs σ' σ ⟨_, hm', _⟩ ⟨_, hm, hq, _⟩ _ _ _ _ => (guardApart_sound hg hm' hm hq).elim⟩
  · exact ⟨fun vs σ σ' ⟨hσ, hm, hq, _⟩ ⟨hσ', hm', hq', _⟩ hd _ _ _ =>
        (negConjApart_sound hmc hc1.1.1.1.1.1 hfx hc2.1.1.1.2 hn hσ hm hq hσ' hm' hq' (.inl hd)).elim,
      fun vs σ' σ ⟨hσ', hm', hq', _⟩ ⟨hσ, hm, hq, _⟩ hd _ _ _ =>
        (negConjApart_sound hmc hc1.1.1.1.1.1 hfx hc2.1.1.1.2 hn hσ hm hq hσ' hm' hq' (.inr hd)).elim⟩

/-- In a core that `sortedOK`, `srReady` and `matchReady` accept, each two equations of one
priority of each function are coherent: by `fnExclusiveL_sound` where `fnExclusiveL` confirms it,
and by the named obligation for the functions it does not (`agreeObligationsL`). -/
theorem clausesAgree_of_L {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true)
    (hob : ∀ f ∈ c.agreeObligationsL, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) :
    ∀ fn ∈ c.fns, ClausesAgree c fn := by
  intro fn hfn
  have hsc := sortCtx_of_all hok hsr (Exec.ovlCase_of hmr)
  by_cases hx : c.fnExclusiveL (c.fns.map Fn.sig) fn = true
  · have hf := hok
    replace hf := Semantics.sortedOK_sorted hf
    simp only [Bool.and_eq_true, List.all_eq_true] at hf
    exact (fnExclusiveL_sound (Exec.matchCtx_of hmr) (fun _ _ => ovlFreeList_of_nil (Exec.matchCtx_of hmr).noOvl _)
      (hf.1.2 fn hfn) hx).agree (Semantics.fnsNoExs_of_sortedOK hok fn hfn)
  · refine hob fn.label ?_ fn ?_
    · simp only [Semantics.agreeObligationsL, List.mem_map, List.mem_filter]
      exact ⟨fn, ⟨hfn, by simpa using hx⟩, rfl⟩
    · rw [Semantics.lookupFn_eq]
      exact find?_label hsc.nodupFns (List.mem_append_left _ hfn)

/-! ## Read from the tables -/

/-- `listApart` with the meet of two sorts read from the tables. -/
def _root_.KCore.Semantics.listApartT (T : Tables) (c : Semantics) (p q : Term) : Bool :=
  (isListUnit (peelAs p) && (listFirst (peelAs q)).isSome) ||
  (isListUnit (peelAs q) && (listFirst (peelAs p)).isSome) ||
  (match listFirst (peelAs p), listFirst (peelAs q) with
   | some x, some y => !overlap (Semantics.meetT T) c.collHead x y
   | _, _ => false)

def _root_.KCore.Semantics.clausesListApartT (T : Tables) (c : Semantics) (cl cl' : Clause) : Bool :=
  c.listSymsFree && (cl.pats.zip cl'.pats).any fun (p, q) => c.listApartT T p q

def _root_.KCore.Semantics.fnExclusiveLT (T : Tables) (c : Semantics) (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all (fun (cl, cl') => (cl.prio != cl'.prio && !cl.aside && !cl'.aside) ||
    !overlapList (Semantics.meetT T) c.collHead cl.pats cl'.pats ||
    (c.clauseFixed cl && (c.clausesExclusiveT T heads cl cl' || c.clausesExclusiveT T heads cl' cl)) ||
    clausesAgree cl cl' || c.clausesListApartT T cl cl' || guardApart cl cl' || guardApart cl' cl ||
    (c.clauseFixed cl && negConjApart cl cl'))

/-- `agreeObligationsL`, read from the tables. -/
def _root_.KCore.Semantics.agreeObligationsLT (T : Tables) (c : Semantics) : List Sym :=
  (c.fns.filter fun f => !c.fnExclusiveLT T (c.fns.map Fn.sig) f).map (·.label)

theorem fnExclusiveLT_tables (heads : List CtorSig) (f : Fn) :
    c.fnExclusiveLT (tables c) heads f = c.fnExclusiveL heads f := by
  simp only [Semantics.fnExclusiveLT, Semantics.fnExclusiveL, Semantics.clausesListApartT,
    Semantics.clausesListApart, Semantics.listApartT, Semantics.listApart, meetT_tables]; rfl

/-- The functions `agreeObligationsL` names, read from the tables. -/
theorem agreeObligationsL_of_T {T : Tables} (hT : T = tables c) {l : List Sym}
    (h : c.agreeObligationsLT T = l) : c.agreeObligationsL = l := by
  subst hT
  rw [← h]
  simp only [Semantics.agreeObligationsLT, Semantics.agreeObligationsL, fnExclusiveLT_tables]

kernel_rfl Semantics.agreeObligationsL_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).agreeObligationsL = c.agreeObligationsL

end KCore.Det
