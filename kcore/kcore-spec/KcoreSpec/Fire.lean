/-
  One step by a rule, with the substitution and the successor found by a tactic.

  - `Term.instP`: the value a left-hand side denotes under σ when every subpattern is read by its
    symbol: a constructor builds, a map pattern symbol (`.Map`, `|->`, `_Map_`) and a collection
    pattern symbol build their value by the evaluation `PatVal` reads them by. `PatVal.of_instP`:
    that value, with the aliases' values (`Term.aliasPairsP`), is a match (`PatVal`). So the match
    of a rule whose left-hand side holds `K |-> V M` against a map with concrete keys is one
    equation the kernel decides, as for a constructor pattern.
  - `stepsTo_fire`: one step by the `i`-th rule from that equation, the sorts of the substitution's
    values, the `requires` and the right-hand side evaluated, and that no rule of a smaller
    priority applies to the term (`FireFacts.noPrio` where the rule has the definition's smallest
    priority).
  - `PatVal.mapLookup`: the pattern `K |-> V M` matches a map of sorted keys in which K's entry is
    V, M taking the other entries, whatever they are (a map whose rest is not known).
  - Sort lemmas the tactics use: `sortOf_ctor_of` (a constructor applied to values of its argument
    sorts), `sortsAre_of_ctor` (the inversion: the arguments of a constructor term of a sort have
    the constructor's argument sorts), `sortOf_of_inj`.
  - The tactics `fire`, `fire?`, `run_end`, `run_by`, `ksort`, `config_sorts` (FireTac.lean).
-/
import KcoreSpec.Runs
import KcoreSpec.Tm
import KcoreSpec.OrderLaws
import KcoreSpec.MatchSound

set_option autoImplicit false

namespace KCore

variable {c : Semantics}

/-! ## The value of a left-hand side read symbol by symbol -/

mutual
  /-- The value the pattern denotes under σ, reading a constructor as building, a map pattern
  symbol by its hook and a collection pattern symbol by its operation; an alias is its subpattern's
  value. -/
  def Term.instP (c : Semantics) (σ : Subst) : Term → Option GroundTerm
    | .var i => σ.lookup i
    | .dv s lit => some (.dv s lit)
    | .app f ps => (Term.instPList c σ ps).bind fun vs =>
        if patternHooks.contains f then (hook f vs).join
        else if c.isCtor f then some (.ctor f vs)
        else if c.isCollPat f then c.collVal f vs
        else none
    | .inj a b p => (Term.instP c σ p).map (injNormal a b)
    | .as p _ => Term.instP c σ p
  def Term.instPList (c : Semantics) (σ : Subst) : List Term → Option (List GroundTerm)
    | [] => some []
    | p :: ps => (Term.instP c σ p).bind fun v => (Term.instPList c σ ps).map (v :: ·)
end

mutual
  /-- For each alias `p #as i`, the value σ gives `i` and `p`'s value (`Term.instP`). -/
  def Term.aliasPairsP (c : Semantics) (σ : Subst) : Term → List (Option GroundTerm × Option GroundTerm)
    | .var _ => []
    | .dv _ _ => []
    | .app _ ps => Term.aliasPairsPList c σ ps
    | .inj _ _ p => Term.aliasPairsP c σ p
    | .as p i => (σ.lookup i, Term.instP c σ p) :: Term.aliasPairsP c σ p
  def Term.aliasPairsPList (c : Semantics) (σ : Subst) :
      List Term → List (Option GroundTerm × Option GroundTerm)
    | [] => []
    | p :: ps => Term.aliasPairsP c σ p ++ Term.aliasPairsPList c σ ps
end

mutual
  /-- The value read symbol by symbol, its aliases holding, is a match. -/
  theorem PatVal.of_instP (σ : Subst) : ∀ (p : Term) {v : GroundTerm}, Term.instP c σ p = some v →
      (Term.aliasPairsP c σ p).map Prod.fst = (Term.aliasPairsP c σ p).map Prod.snd →
      PatVal c σ p v
    | .var _, _, h, _ => .var h
    | .dv _ _, _, h, _ => by cases h; exact .dv
    | .app f ps, v, h, ha => by
      simp only [Term.instP] at h
      obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
      have hs := PatVals.of_instP σ ps hvs ha
      by_cases hp : patternHooks.contains f = true
      · rw [if_pos hp] at h; exact .hook hp hs (Option.join_eq_some_iff.mp h)
      · rw [if_neg hp] at h
        by_cases hc : c.isCtor f = true
        · rw [if_pos hc] at h; cases h; exact .ctor hc hs
        · rw [if_neg hc] at h
          by_cases hq : c.isCollPat f = true
          · rw [if_pos hq] at h; exact .coll (by simpa using hc) hq hs h
          · rw [if_neg hq] at h; cases h
    | .inj _ _ p, _, h, ha => by
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .inj (PatVal.of_instP σ p hw ha)
    | .as p i, _, h, ha => by
      simp only [Term.aliasPairsP, List.map_cons, List.cons.injEq] at ha
      exact .as (PatVal.of_instP σ p h ha.2) (ha.1.trans h)
  theorem PatVals.of_instP (σ : Subst) : ∀ (ps : List Term) {vs : List GroundTerm},
      Term.instPList c σ ps = some vs →
      (Term.aliasPairsPList c σ ps).map Prod.fst = (Term.aliasPairsPList c σ ps).map Prod.snd →
      PatVals c σ ps vs
    | [], _, h, _ => by cases h; exact .nil
    | p :: ps, _, h, ha => by
      simp only [Term.instPList] at h
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Term.aliasPairsPList] at ha
      obtain ⟨h1, h2⟩ := pairs_eq_append ha
      exact .cons (PatVal.of_instP σ p hv h1) (PatVals.of_instP σ ps hvs' h2)
end

/-! ## The facts a step needs of the definition -/

/-- What `stepsTo_fire` reads of the definition: the conditions the executable evaluation's
soundness takes, and a priority no rule's is below. A package emits its instance. -/
class FireFacts (c : Semantics) where
  ok : c.ok = true
  srReady : c.srReady = true
  matchReady : c.matchReady = true
  minPrio : Nat
  floor : c.rules.all (fun r => Nat.ble minPrio r.prio) = true

/-- No rule of a smaller priority than r's applies to x. -/
def PrioOK (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x

/-- A rule of the smallest priority waits on no rule. -/
theorem FireFacts.noPrio (F : FireFacts c) {r : Rule} (h : Nat.ble r.prio F.minPrio = true)
    (x : GroundTerm) : PrioOK c r x := by
  intro r' hr' hlt
  have h2 := List.all_eq_true.mp F.floor r' hr'
  simp only [Nat.ble_eq] at h h2
  omega

/-- The `requires` of a rule holds: there is none, or it evaluates to `true`. -/
def ReqOK (c : Semantics) (n : Nat) (σ : Subst) : Option Term → Prop
  | none => True
  | some t => Exec.evalT c n σ t = some (some (bool true))

/-- **One step by the `i`-th rule** under the substitution `sub vs`: the values have the rule's
variable sorts, the left-hand side read symbol by symbol is `u` with its aliases holding, the
`requires` holds, the right-hand side evaluates to `v` in the executable evaluation, the `ensures`
holds, and no rule of a smaller priority applies to `u`. -/
theorem stepsTo_fire (F : FireFacts c) {i : Nat} {r : Rule} (hr : c.rules[i]? = some r)
    {vs : List GroundTerm} {u v : GroundTerm} (hσ : SortsAre c r.vars vs)
    (hu : Term.instP c (sub vs) r.lhs = some u)
    (ha : (Term.aliasPairsP c (sub vs) r.lhs).map Prod.fst =
      (Term.aliasPairsP c (sub vs) r.lhs).map Prod.snd)
    (n : Nat) (hq : ReqOK c n (sub vs) r.req)
    (he : Exec.evalT c n (sub vs) r.rhs = some (some v)) (hens : ReqOK c n (sub vs) r.ens)
    (hprio : PrioOK c r u) : StepsTo c u v := by
  intro x hx
  subst hx
  have hσ' := wellSorted_sub hσ
  have hok := F.ok
  have hsc := sortCtx_of hok F.srReady (Exec.ovlCase_of F.matchReady)
  have hcc := Exec.clauseCtx_of hok
  have hmc := Exec.matchCtx_of F.matchReady
  obtain ⟨_, _, _, hreq, hrhs⟩ := Exec.ruleOK_of hok (List.mem_of_getElem? hr)
  have hen := Exec.ruleOK_ens_of hok (List.mem_of_getElem? hr)
  refine Step.exists_of_rule hok F.srReady hr hσ' (PatVal.of_instP _ r.lhs hu ha) (fun t ht => ?_)
    hprio (Exec.evalT_sound hsc hcc hmc n he Exec.headsOK_fns hσ' hrhs) (fun t ht => ?_)
    (Exec.ovlCase_of F.matchReady)
  · have hq' : Exec.evalT c n (sub vs) t = some (some (bool true)) := by
      rw [ht] at hq; exact hq
    rw [ht] at hreq
    exact Exec.evalT_sound hsc hcc hmc n hq' Exec.headsOK_fns hσ' (Exec.reqOK_some hreq)
  · have hq' : Exec.evalT c n (sub vs) t = some (some (bool true)) := by
      rw [ht] at hens; exact hens
    rw [ht] at hen
    exact Exec.evalT_sound hsc hcc hmc n hq' Exec.headsOK_fns hσ' (Exec.reqOK_some hen)

/-- A `requires` whose value is the Boolean b, where b is true. -/
theorem req_of_bool {e : Option (Option GroundTerm)} {b : Bool} (h : e = some (some (bool b)))
    (hb : b = true) : e = some (some (bool true)) := hb ▸ h

/-- The `i`-th rule. -/
def ruleAt (c : Semantics) (i : Nat) : Option Rule := c.rules[i]?

/-- Keys equal for the maps' order (the tactic's search of a map entry). -/
def keyEq (a b : GroundTerm) : Bool := GroundTerm.cmp a b == .eq

/-- A sort, as computed, is s. -/
def sortIs (o : Option Srt) (s : Srt) : Bool := o == some s

/-- `a` is below `b` among the definition's subsorts. -/
def subsortB (c : Semantics) (a b : Srt) : Bool := c.subsorts.contains (a, b)

/-! ## A run's ends -/

theorem Runs.of_eq_left {u u' w : GroundTerm} (he : u = u') (h : Runs c u' w) : Runs c u w :=
  he ▸ h

theorem Runs.of_eq_refl {u w : GroundTerm} (he : u = w) : Runs c u w := he ▸ Runs.refl u

/-- A run from `u'`, entered where `u = u'`, then continued. -/
theorem Runs.by_run {u u' w' w : GroundTerm} (he : u = u') (h : Runs c u' w') (h' : Runs c w' w) :
    Runs c u w := he ▸ h.trans h'

/-! ## Sorts, forward and backward -/

theorem sortsOf_of_sortsAre : ∀ {ss : List Srt} {vs : List GroundTerm}, SortsAre c ss vs →
    c.sortsOf vs = some ss
  | [], [], _ => sortsOf_nil
  | _ :: _, _ :: _, h => sortsOf_cons.mpr ⟨_, _, h.1, sortsOf_of_sortsAre h.2, rfl⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem sortsAre_of_sortsOf : ∀ {ss : List Srt} {vs : List GroundTerm}, c.sortsOf vs = some ss →
    SortsAre c ss vs
  | ss, [], h => by
    rw [sortsOf_nil] at h; cases h; trivial
  | ss, _ :: _, h => by
    obtain ⟨_, _, h1, h2, rfl⟩ := sortsOf_cons.mp h
    exact ⟨h1, sortsAre_of_sortsOf h2⟩

/-- A constructor applied to values of its argument sorts has its result sort. -/
theorem sortOf_ctor_of {f : Sym} {ts : List GroundTerm} {k : CtorSig}
    (hk : lookupSig c.ctorSigs f = some k) (hts : SortsAre c k.args ts) :
    c.sortOf (.ctor f ts) = some k.result :=
  sortOf_ctor_intro ⟨k, hk, sortsOf_of_sortsAre hts, rfl⟩

/-- The arguments of a constructor term of a sort have the constructor's argument sorts. -/
theorem sortsAre_of_ctor {f : Sym} {ts : List GroundTerm} {s : Srt} {k : CtorSig}
    (h : c.sortOf (.ctor f ts) = some s) (hk : lookupSig c.ctorSigs f = some k) :
    SortsAre c k.args ts := by
  obtain ⟨k', hk', hts, -⟩ := (sortOf_ctor_of_isCtor (by simp [Semantics.isCtor, hk])).mp h
  rw [hk] at hk'; cases hk'
  exact sortsAre_of_sortsOf hts

/-- An injection from a subsort, of a value that is not an injection, has the larger sort. -/
theorem sortOf_inj_of {a b : Srt} {t : GroundTerm} (hab : c.subsorts.contains (a, b) = true)
    (hn : t.isInj = false) (ht : c.sortOf t = some a) : c.sortOf (.inj a b t) = some b :=
  sortOf_inj.mpr ⟨List.contains_iff_mem.mp hab, hn, ht, rfl⟩

theorem sortOf_of_inj {a b : Srt} {t : GroundTerm} {s : Srt} (h : c.sortOf (.inj a b t) = some s) :
    c.sortOf t = some a :=
  (sortOf_inj.mp h).2.2.1

/-! ## `K |-> V M` against a map whose rest is not known -/

open GroundTerm in
/-- `findK` finds an entry whose key compares equal. -/
theorem findK_key {k : GroundTerm} : ∀ {es : Entries} {v : GroundTerm}, findK k es = some v →
    ∃ k', cmp k k' = .eq ∧ (k', v) ∈ es
  | [], _, h => nomatch h
  | (k', v') :: es, v, h => by
    simp only [findK] at h
    split at h
    · cases h; exact ⟨k', beq_iff_eq.mp ‹_›, List.mem_cons_self ..⟩
    · obtain ⟨k'', he, hm⟩ := findK_key h
      exact ⟨k'', he, List.mem_cons_of_mem _ hm⟩

open GroundTerm in
/-- In sorted entries where k's entry is v, putting k's entry back into the others gives the
entries, and k is not among the others. -/
theorem findK_split {k v : GroundTerm} : ∀ {es : Entries}, keysSorted es = true →
    findK k es = some v → insertE k v (eraseK k es) = es ∧ hasKey k (eraseK k es) = false
  | [], _, h => nomatch h
  | (k', v') :: es, hs, h => by
    have hlt := keysSorted_lt_all hs
    simp only [findK] at h
    by_cases hk : (cmp k k' == .eq) = true
    · rw [if_pos hk] at h; cases h
      have he : k = k' := cmp_eq _ _ (beq_iff_eq.mp hk)
      subst he
      simp only [eraseK, if_pos hk]
      refine ⟨?_, ?_⟩
      · cases es with
        | nil => rfl
        | cons e es =>
          obtain ⟨k2, v2⟩ := e
          simp only [insertE, hlt _ (List.mem_cons_self ..)]
      · simp only [hasKey, List.any_eq_false]
        intro e he h'
        rw [hlt e he] at h'
        cases h'
    · rw [if_neg hk] at h
      obtain ⟨h1, h2⟩ := findK_split (keysSorted_cons.mp hs).1 h
      obtain ⟨k'', he, hm⟩ := findK_key h
      have hkk : k = k'' := cmp_eq _ _ he
      subst hkk
      have hgt : cmp k k' = .gt := by
        rw [cmp_swap, hlt _ hm]; rfl
      have hE : eraseK k ((k', v') :: es) = (k', v') :: eraseK k es := by
        simp only [eraseK]; rw [if_neg hk]
      rw [hE]
      refine ⟨?_, ?_⟩
      · simp only [insertE, hgt]; rw [h1]
      · have h2' : (eraseK k es).any (fun e => cmp k e.1 == .eq) = false := h2
        simp only [hasKey, List.any_cons, Bool.or_eq_false_iff]
        exact ⟨Bool.eq_false_iff.mpr hk, h2'⟩

/-- **`K |-> V M` against a map whose rest is not known**: in a map of sorted keys whose entry at
the value of K is the value of V (`findK`, decided by evaluation when the keys are closed terms),
the pattern matches with M taking the other entries (`eraseK`). Nothing is required of the other
entries. -/
theorem PatVal.mapLookup {σ : Subst} {kp vp mp : Term} {k v : GroundTerm} {es : Entries} {s : Srt}
    (hs : keysSorted es = true) (hf : findK k es = some v)
    (hk : PatVal c σ kp k) (hv : PatVal c σ vp v) (hm : PatVal c σ mp (.map s (eraseK k es))) :
    PatVal c σ (.app mapConcat [.app mapElem [kp, vp], mp]) (.map Srt.map es) := by
  obtain ⟨h1, h2⟩ := findK_split hs hf
  refine .hook Exec.patternHooks_concat
    (.cons (.hook Exec.patternHooks_elem (.cons hk (.cons hv .nil)) (Exec.hook_mapElem k v))
      (.cons hm .nil)) ?_
  rw [Exec.hook_mapConcat]
  simp only [union, Option.bind_some, addNew, h2, Bool.false_eq_true, if_false, h1, Option.map_some]

end KCore
