/-
  KCore, checked layer: self calls that decrease in a measure that counts a list's elements
  (`decreasingOKL`), so more functions terminate (`terminates_of_decreasingL`) than `decreasingOK`
  (Terminates.lean) shows.

  `decreasingOK` measures a value by its constructor and injection nodes (`GroundTerm.size`), a
  collection counting one, and accepts a self call whose argument at the decreasing position is a
  variable strictly inside the clause's pattern there, under constructors only. `weight` counts a
  list as one more than the weights of its elements, so:
  - a variable under a list pattern `ListItem(P) L` or `ListItem(P)` (L, or inside P) is lighter
    than the list: the list is P's value followed by L's, and every value weighs at least one;
  - the alias variable of a pattern (`p #as V`) weighs what the pattern's value weighs, so V under a
    constructor is strictly lighter than the whole (`typedArgs(A, typedArgs(B, R) #as V)` calls
    itself at V);
  - an argument that applies the clause's head constructor to arguments each no heavier than the
    pattern's, one of them strictly lighter, is strictly lighter (`JSONObject(R)` against
    `JSONObject(JSONs(E, R))`);
  - an injected argument `inj(T)` against a pattern `inj(Q)` whose Q is a constructor application,
    with T no heavier (strictly lighter) than Q, is no heavier (strictly lighter): the pattern's
    value is one injection node over Q's constructor value, and the argument's at most one over
    T's (`kseq(inj(K0), dotk)` against `kseq(inj(pair(K0, K1)), dotk)`). A constructor is asked
    under the pattern's injection because `injNormal` collapses an injection of an injected value:
    where Q can denote an injected value, the pattern's value weighs what Q's does, while a
    non-injected value of T's weighs one more under its injection, so neither bound lifts.
  A map or a set still counts one: a frame variable of a map pattern can denote the whole map.

  `decObligationsL` names the functions with a self call no argument position shows decreasing;
  `terminates_of_rankL` (CallGroups.lean) gives every function's termination from the rank and these.
-/
import KcoreSpec.CallRank
import KcoreSpec.UniqLists

set_option autoImplicit false

namespace KCore

open Det

mutual
  /-- The weight of a value: its constructor and injection nodes, a list one more than its
  elements' weights, a domain value, a map or a set one. -/
  def GroundTerm.weight : GroundTerm → Nat
    | .ctor _ ts => GroundTerm.weightList ts + 1
    | .inj _ _ t => GroundTerm.weight t + 1
    | .dv _ _ => 1
    | .map _ _ => 1
    | .set _ _ => 1
    | .list _ es => GroundTerm.weightList es + 1
    termination_by structural t => t
  def GroundTerm.weightList : List GroundTerm → Nat
    | [] => 0
    | t :: ts => GroundTerm.weight t + GroundTerm.weightList ts
    termination_by structural ts => ts
end

theorem weight_pos (w : GroundTerm) : 1 ≤ w.weight := by
  cases w <;> simp [GroundTerm.weight]

theorem weight_injNormal (a b : Srt) (w : GroundTerm) : w.weight ≤ (injNormal a b w).weight := by
  cases w <;> simp [injNormal, GroundTerm.weight]

/-- An injection adds at most one node: `injNormal` of an injected value keeps its weight. -/
theorem weight_injNormal_leInjL (a b : Srt) (w : GroundTerm) : (injNormal a b w).weight ≤ w.weight + 1 := by
  cases w <;> simp [injNormal, GroundTerm.weight]

/-- An injection of a constructor value adds exactly one node. -/
theorem weight_injNormal_ctorInjL (a b : Srt) (g : Sym) (vs : List GroundTerm) :
    (injNormal a b (.ctor g vs)).weight = (GroundTerm.ctor g vs).weight + 1 := rfl

namespace Semantics
variable (c : Semantics)

mutual
  /-- The variable `j` occurs in the pattern on a path of constructors (`ctorPat`), injections,
  aliases (the alias variable itself among them) and list patterns `ListItem(P) L`, `ListItem(P)`. -/
  def pathL (j : Nat) : Term → Bool
    | .var i => i == j
    | .app g ts =>
      if c.ctorPat g then pathLList j ts
      else if g == listElem then pathLElem j ts
      else if g == listConcat then pathLCat j ts
      else false
    | .inj _ _ t => pathL j t
    | .as t i => i == j || pathL j t
    | .dv _ _ => false
    termination_by structural t => t
  def pathLList (j : Nat) : List Term → Bool
    | [] => false
    | t :: ts => pathL j t || pathLList j ts
    termination_by structural ts => ts
  def pathLElem (j : Nat) : List Term → Bool
    | [x] => pathL j x
    | _ => false
    termination_by structural ts => ts
  def pathLCat (j : Nat) : List Term → Bool
    | [.app e [x], r] => e == listElem && !c.ctorPat e && (pathL j x || pathL j r)
    | _ => false
    termination_by structural ts => ts
end

/-- The variable `j` lies strictly inside the pattern: on a `pathL` path under at least one
constructor or list node. -/
def strictL (j : Nat) : Term → Bool
  | .app g ts =>
    if c.ctorPat g then c.pathLList j ts
    else if g == listElem then c.pathLElem j ts
    else if g == listConcat then c.pathLCat j ts
    else false
  | .inj _ _ t => strictL j t
  | .as t _ => strictL j t
  | _ => false

/-- The pattern, its aliases aside, applies a constructor (`ctorPat`): its value is a constructor
value, never an injection. -/
def ctorHeadInjL (q : Term) : Bool :=
  match peelAs q with
  | .app g _ => c.ctorPat g
  | _ => false

mutual
  /-- An argument no heavier than the value the pattern denotes: a variable on a `pathL` path, the
  pattern's literal, the pattern's head constructor applied to arguments each no heavier, or an
  injection of an argument no heavier than the term under the pattern's injection, where that term
  applies a constructor (`ctorHeadInjL`; `injNormal` collapses an injected value, so the bound
  does not lift through two injections otherwise). -/
  def argLe : Term → Term → Bool
    | .var j, p => c.pathL j p
    | .dv s l, p => match peelAs p with
      | .dv s' l' => s == s' && l == l'
      | _ => false
    | .app g ts, p => match peelAs p with
      | .app g' ps => g == g' && c.ctorPat g && argLeList ts ps
      | _ => false
    | .inj _ _ t, p => match peelAs p with
      | .inj _ _ q => c.ctorHeadInjL q && argLe t q
      | _ => false
    | _, _ => false
    termination_by structural t => t
  def argLeList : List Term → List Term → Bool
    | [], [] => true
    | t :: ts, p :: ps => argLe t p && argLeList ts ps
    | _, _ => false
    termination_by structural ts => ts
end

mutual
  /-- An argument strictly lighter than the value the pattern denotes: a variable strictly inside
  it (`strictL`), the pattern's head constructor applied to arguments each no heavier, one of
  them strictly lighter, or an injection of an argument strictly lighter than the term under the
  pattern's injection, where that term applies a constructor (`ctorHeadInjL`; under an injected
  value `injNormal` adds no node to the pattern's value, so `<` does not lift otherwise). -/
  def argLt : Term → Term → Bool
    | .var j, p => c.strictL j p
    | .app g ts, p => match peelAs p with
      | .app g' ps => g == g' && c.ctorPat g && c.argLeList ts ps && argLtList ts ps
      | _ => false
    | .inj _ _ t, p => match peelAs p with
      | .inj _ _ q => c.ctorHeadInjL q && argLt t q
      | _ => false
    | _, _ => false
    termination_by structural t => t
  def argLtList : List Term → List Term → Bool
    | t :: ts, p :: ps => argLt t p || argLtList ts ps
    | _, _ => false
    termination_by structural ts => ts
end

/-- Self calls decrease at `dec` in weight: the argument there is strictly lighter than the
clause's pattern there (`argLt`). -/
def decreasingOKL (f : Fn) (dec : Option Nat) : Bool :=
  let calls := selfCalls f
  calls.isEmpty || match dec with
    | none => false
    | some i => calls.all fun (pats, args) => match args[i]?, pats[i]? with
      | some a, some p => c.argLt a p
      | _, _ => false

/-- The first argument at which f's self calls decrease in weight, if any. -/
def decArgL (f : Fn) : Option Nat :=
  (List.range f.args.length).find? fun i => c.decreasingOKL f (some i)

/-- The lower bound a literal of a `requires` puts on the variable x (`x >=Int k`, `x >Int k`,
`k <Int x`, …; `intBound`). -/
def _root_.KCore.lowerOf (x : Nat) (l : Term × Bool) : Option Int :=
  match intBound l with
  | some (.var y, some lo, _) => if y == x then some lo else none
  | _ => none

/-- A self call's argument at an Int counter x that the clause's `requires` bounds below by lo, whose
value is below x's: `x -Int k` (k ≥ 1), `x /Int k` (k ≥ 2 and lo ≥ 1, so x is positive), or an Int
literal below lo. -/
def _root_.KCore.ctrArg (lo : Int) (x : Nat) : Term → Bool
  | .app f [.var y, .dv s (.int k)] => s == Srt.int && y == x &&
      ((f == intSub && decide (1 ≤ k)) || (f == intTDiv && decide (2 ≤ k) && decide (1 ≤ lo)))
  | .dv s (.int k) => s == Srt.int && decide (k < lo)
  | _ => false

/-- The counter at argument i of a clause: its pattern there is a variable x, and a literal of its
`requires` bounds x below by lo. -/
def _root_.KCore.ctrLo (i : Nat) (cl : Clause) : Option (Nat × Int) :=
  match cl.pats[i]? with
  | some (.var x) => (((cl.req.map lits).getD []).findSome? (lowerOf x)).map (x, ·)
  | _ => none

/-- Self calls decrease at the Int argument i read as a counter bounded below: the argument is an
Int; no self call is in a `requires` or an `ensures`; in each clause with a self call (in its right-hand side) the
pattern at i is a variable its `requires` bounds below (`ctrLo`) and each self call's argument at i
is below it (`ctrArg`). -/
def _root_.KCore.ctrOK (f : Fn) (i : Nat) : Bool :=
  f.args[i]? == some Srt.int &&
  f.clauses.all fun cl =>
    ((cl.req.map (callsOf f.label)).getD []).isEmpty &&
    ((cl.ens.map (callsOf f.label)).getD []).isEmpty &&
    ((callsOf f.label cl.rhs).isEmpty || match ctrLo i cl with
      | some (x, lo) => (callsOf f.label cl.rhs).all fun ts => match ts[i]? with
          | some a => ctrArg lo x a
          | none => false
      | none => false)

/-- The first argument that is a counter of f's self calls (`ctrOK`), if any. -/
def _root_.KCore.ctrArgOf (f : Fn) : Option Nat :=
  (List.range f.args.length).find? fun i => ctrOK f i

/-- Below every lower bound `ctrLo` finds at argument i: the counter's measure is its distance
from this floor. -/
def _root_.KCore.ctrFloor (i : Nat) (f : Fn) : Int :=
  (f.clauses.filterMap fun cl => (ctrLo i cl).map (·.2)).foldl min 0 - 1

/-- What reading Int counters needs of the core: an Int value is a literal (`shapesOK`), and
`_-Int_`, `_/Int_` are no constructors (they have their meaning). -/
def ctrReady : Bool := c.shapesOK && !c.isCtor intSub && !c.isCtor intTDiv

/-- The functions with a self call that no argument shows decreasing in weight, nor as an Int
counter bounded below (`ctrOK`). -/
def decObligationsL : List Sym :=
  (c.fns.filter fun f => !c.decreasingOKL f (c.decArgL f) && !(c.ctrReady && (ctrArgOf f).isSome)).map (·.label)

end Semantics

/-! ## Soundness -/

variable {c : Semantics}

theorem isCtor_of_not_ctorPat_list {g : Sym} (h : c.ctorPat g = false) (hg : patternHooks.contains g = false) :
    c.isCtor g = false := by
  simp only [Semantics.ctorPat, Bool.and_eq_false_iff, hg, Bool.not_false, Bool.false_eq_true, or_false] at h
  simpa [Semantics.isCtor] using h

theorem pathLCat_inv {j : Nat} {ts : List Term} (h : c.pathLCat j ts = true) :
    ∃ e x r, ts = [.app e [x], r] := by
  unfold Semantics.pathLCat at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · cases h

mutual
  /-- On a `pathL` path, a variable's value is no heavier than the value the pattern denotes. -/
  theorem pathL_weight {σ : Subst} {j : Nat} : ∀ (p : Term) {v : GroundTerm}, PatVal c σ p v →
      c.pathL j p = true → ∃ w, σ.lookup j = some w ∧ w.weight ≤ v.weight
    | .var i, v, h, hp => by
      simp only [Semantics.pathL, beq_iff_eq] at hp
      subst hp
      exact ⟨v, PatVal.var_inv h, Nat.le_refl _⟩
    | .dv _ _, _, _, hp => by simp [Semantics.pathL] at hp
    | .inj a b t, _, h, hp => by
      obtain ⟨w', hw', rfl⟩ := PatVal.inj_inv h
      obtain ⟨w, hw, hle⟩ := pathL_weight t hw' (by simpa [Semantics.pathL] using hp)
      exact ⟨w, hw, Nat.le_trans hle (weight_injNormal a b _)⟩
    | .as t i, v, h, hp => by
      obtain ⟨ht, hi⟩ := PatVal.as_inv h
      simp only [Semantics.pathL, Bool.or_eq_true, beq_iff_eq] at hp
      rcases hp with rfl | hp
      · exact ⟨v, hi, Nat.le_refl _⟩
      · exact pathL_weight t ht hp
    | .app g ts, v, h, hp => by
      simp only [Semantics.pathL] at hp
      split at hp
      · rename_i hg
        cases h with
        | ctor _ hs =>
          obtain ⟨w, hw, hle⟩ := pathLList_weight ts hs hp
          exact ⟨w, hw, by simp only [GroundTerm.weight]; omega⟩
        | hook hph _ _ => rw [not_patternHook_of_ctorPat hg] at hph; cases hph
        | coll hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
        | ovl hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
      · rename_i hg
        have hg := Bool.eq_false_iff.mpr hg
        split at hp
        · rename_i he
          have he := beq_iff_eq.mp he
          subst he
          have hct := isCtor_of_not_ctorPat_list hg (by decide)
          obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hct (isCollPat_list (by decide)) h
          obtain ⟨w, rfl, rfl⟩ := collVal_listElem hv
          obtain ⟨w', hw', hle⟩ := pathLElem_weight ts hvs hp
          exact ⟨w', hw', by simp only [GroundTerm.weight, GroundTerm.weightList] at hle ⊢; omega⟩
        · split at hp
          · rename_i hcat
            have hcat := beq_iff_eq.mp hcat
            subst hcat
            have hct := isCtor_of_not_ctorPat_list hg (by decide)
            obtain ⟨w, hw, hlt⟩ := pathLCat_weight ts hct h hp
            exact ⟨w, hw, Nat.le_of_lt hlt⟩
          · cases hp
  theorem pathLList_weight {σ : Subst} {j : Nat} : ∀ (ts : List Term) {vs : List GroundTerm},
      PatVals c σ ts vs → c.pathLList j ts = true → ∃ w, σ.lookup j = some w ∧ w.weight ≤ GroundTerm.weightList vs
    | [], _, _, hp => by simp [Semantics.pathLList] at hp
    | t :: ts, _, h, hp => by
      cases h with
      | cons h1 h2 =>
        simp only [Semantics.pathLList, Bool.or_eq_true] at hp
        rcases hp with hp | hp
        · obtain ⟨w, hw, hle⟩ := pathL_weight t h1 hp
          exact ⟨w, hw, by simp only [GroundTerm.weightList]; omega⟩
        · obtain ⟨w, hw, hle⟩ := pathLList_weight ts h2 hp
          exact ⟨w, hw, by simp only [GroundTerm.weightList]; omega⟩
  theorem pathLElem_weight {σ : Subst} {j : Nat} : ∀ (ts : List Term) {vs : List GroundTerm},
      PatVals c σ ts vs → c.pathLElem j ts = true → ∃ w, σ.lookup j = some w ∧ w.weight ≤ GroundTerm.weightList vs
    | [x], _, h, hp => by
      cases h with
      | cons h1 h2 =>
        cases h2
        obtain ⟨w, hw, hle⟩ := pathL_weight x h1 (by simpa [Semantics.pathLElem] using hp)
        exact ⟨w, hw, by simp only [GroundTerm.weightList]; omega⟩
    | [], _, _, hp => by simp [Semantics.pathLElem] at hp
    | _ :: _ :: _, _, _, hp => by simp [Semantics.pathLElem] at hp
  /-- `ListItem(P) L`: a variable on a path in P or in L is strictly lighter than the list, which
  holds P's value and L's elements and weighs one more. -/
  theorem pathLCat_weight {σ : Subst} {j : Nat} : ∀ (ts : List Term) {v : GroundTerm},
      c.isCtor listConcat = false → PatVal c σ (.app listConcat ts) v → c.pathLCat j ts = true →
      ∃ w, σ.lookup j = some w ∧ w.weight < v.weight
    | [.app e [x], r], v, hct, h, hp => by
      simp only [Semantics.pathLCat, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        Bool.or_eq_true] at hp
      obtain ⟨⟨rfl, hce⟩, hp⟩ := hp
      have hcte := isCtor_of_not_ctorPat_list hce (by decide)
      obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hct (isCollPat_list (by decide)) h
      obtain ⟨s₁, a, t, b, rfl, rfl⟩ := collVal_listConcat hv
      obtain ⟨_, _, he1, hE, hRa⟩ := PatVals.cons_inv' hvs
      obtain ⟨_, _, he2, hR, -⟩ := PatVals.cons_inv' hRa
      cases he1; cases he2
      obtain ⟨ws, hws, hw⟩ := PatVal.coll_inv hcte (isCollPat_list (by decide)) hE
      obtain ⟨w, rfl, hw⟩ := collVal_listElem hw
      cases hw
      obtain ⟨_, _, he3, hX, -⟩ := PatVals.cons_inv' hws
      cases he3
      have hpos := weight_pos w
      rcases hp with hp | hp
      · obtain ⟨w', hw', hle⟩ := pathL_weight x hX hp
        exact ⟨w', hw', by simp only [GroundTerm.weight, GroundTerm.weightList, List.cons_append,
          List.nil_append] at hle ⊢; omega⟩
      · obtain ⟨w', hw', hle⟩ := pathL_weight r hR hp
        exact ⟨w', hw', by simp only [GroundTerm.weight, GroundTerm.weightList, List.cons_append,
          List.nil_append] at hle ⊢; omega⟩
    | [], _, _, _, hp | [_], _, _, _, hp | _ :: _ :: _ :: _, _, _, _, hp
    | [.var _, _], _, _, _, hp | [.dv _ _, _], _, _, _, hp | [.inj _ _ _, _], _, _, _, hp
    | [.as _ _, _], _, _, _, hp | [.app _ [], _], _, _, _, hp
    | [.app _ (_ :: _ :: _), _], _, _, _, hp => by
      obtain ⟨_, _, _, he⟩ := pathLCat_inv hp
      simp at he
end

/-- Strictly inside a pattern (`strictL`), a variable's value is strictly lighter than the value
the pattern denotes. -/
theorem strictL_weight {σ : Subst} {j : Nat} : ∀ (p : Term) {v : GroundTerm}, PatVal c σ p v →
    c.strictL j p = true → ∃ w, σ.lookup j = some w ∧ w.weight < v.weight
  | .var _, _, _, hp => by simp [Semantics.strictL] at hp
  | .dv _ _, _, _, hp => by simp [Semantics.strictL] at hp
  | .inj a b t, _, h, hp => by
    obtain ⟨w', hw', rfl⟩ := PatVal.inj_inv h
    obtain ⟨w, hw, hlt⟩ := strictL_weight t hw' (by simpa [Semantics.strictL] using hp)
    exact ⟨w, hw, Nat.lt_of_lt_of_le hlt (weight_injNormal a b _)⟩
  | .as t _, _, h, hp => strictL_weight t (PatVal.as_inv h).1 (by simpa [Semantics.strictL] using hp)
  | .app g ts, v, h, hp => by
    simp only [Semantics.strictL] at hp
    split at hp
    · rename_i hg
      cases h with
      | ctor _ hs =>
        obtain ⟨w, hw, hle⟩ := pathLList_weight ts hs hp
        exact ⟨w, hw, by simp only [GroundTerm.weight]; omega⟩
      | hook hph _ _ => rw [not_patternHook_of_ctorPat hg] at hph; cases hph
      | coll hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
      | ovl hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
    · rename_i hg
      have hg := Bool.eq_false_iff.mpr hg
      split at hp
      · rename_i he
        have he := beq_iff_eq.mp he
        subst he
        have hct := isCtor_of_not_ctorPat_list hg (by decide)
        obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hct (isCollPat_list (by decide)) h
        obtain ⟨w, rfl, rfl⟩ := collVal_listElem hv
        obtain ⟨w', hw', hle⟩ := pathLElem_weight ts hvs hp
        exact ⟨w', hw', by simp only [GroundTerm.weight, GroundTerm.weightList] at hle ⊢; omega⟩
      · split at hp
        · rename_i hcat
          have hcat := beq_iff_eq.mp hcat
          subst hcat
          exact pathLCat_weight ts (isCtor_of_not_ctorPat_list hg (by decide)) h hp
        · cases hp

theorem peelAs_patVal' {σ : Subst} : ∀ {p : Term} {v : GroundTerm}, PatVal c σ p v → PatVal c σ (peelAs p) v
  | .as p _, _, h => by simp only [peelAs]; exact peelAs_patVal' (PatVal.as_inv h).1
  | .var _, _, h => h
  | .dv _ _, _, h => h
  | .app _ _, _, h => h
  | .inj _ _ _, _, h => h

theorem evalTerms_some_inv {σ : Subst} : ∀ {ts : List Term} {vs : List GroundTerm},
    EvalTerms c σ ts (vs.map some) → ∀ {i : Nat} {t : Term}, ts[i]? = some t → ∃ v, vs[i]? = some v ∧ EvalTerm c σ t (some v)
  | [], _, _, _, _, h => by simp at h
  | t :: ts, vs, h, i, u, hi => by
    cases vs with
    | nil => cases h
    | cons v vs =>
      cases h with
      | cons h1 h2 =>
        cases i with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨v, rfl, h1⟩
        | succ i => simp only [List.getElem?_cons_succ] at hi ⊢; exact evalTerms_some_inv h2 hi

theorem allSome_eq_map {rs : List (Option GroundTerm)} {vs : List GroundTerm} (h : allSome rs = some vs) :
    rs = vs.map some := by
  induction rs generalizing vs with
  | nil => simp only [allSome, Option.some.injEq] at h; subst h; rfl
  | cons r rs ih =>
    cases r with
    | none => simp [allSome] at h
    | some w =>
      simp only [allSome, Option.bind_some, Option.map_eq_some_iff] at h
      obtain ⟨ws, hws, rfl⟩ := h
      rw [ih hws]; rfl

/-- A pattern `ctorHeadInjL` accepts denotes a constructor value. -/
theorem ctorHeadInjL_val {σ : Subst} {q : Term} {w : GroundTerm} (hq : c.ctorHeadInjL q = true)
    (hw : PatVal c σ q w) : ∃ g vs, w = .ctor g vs := by
  unfold Semantics.ctorHeadInjL at hq
  split at hq
  · rename_i g ps hpe
    have hp' := peelAs_patVal' hw
    rw [hpe] at hp'
    cases hp' with
    | ctor _ _ => exact ⟨_, _, rfl⟩
    | hook hph _ _ => rw [not_patternHook_of_ctorPat hq] at hph; cases hph
    | coll hc _ _ _ => rw [isCtor_of_ctorPat hq] at hc; cases hc
    | ovl hc _ _ _ => rw [isCtor_of_ctorPat hq] at hc; cases hc
  · cases hq

mutual
  /-- An argument `argLe` accepts against a pattern weighs no more than the value the pattern
  denotes. -/
  theorem argLe_weight {σ : Subst} : ∀ (a : Term) {p : Term} {v v' : GroundTerm}, c.argLe a p = true →
      PatVal c σ p v → EvalTerm c σ a (some v') → v'.weight ≤ v.weight
    | .var j, p, v, v', ha, hp, he => by
      obtain ⟨w, hw, hle⟩ := pathL_weight p hp (by simpa [Semantics.argLe] using ha)
      have := EvalTerm.var_inv he
      rw [hw] at this
      cases this
      exact hle
    | .dv s l, p, v, v', ha, hp, he => by
      simp only [Semantics.argLe] at ha
      split at ha
      · rename_i s' l' hpe
        simp only [Bool.and_eq_true, beq_iff_eq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        have hp' := peelAs_patVal' hp
        rw [hpe] at hp'
        cases hp'
        cases he
        exact Nat.le_refl _
      · cases ha
    | .app g ts, p, v, v', ha, hp, he => by
      simp only [Semantics.argLe] at ha
      split at ha
      · rename_i g' ps hpe
        simp only [Bool.and_eq_true, beq_iff_eq] at ha
        obtain ⟨⟨rfl, hg⟩, hl⟩ := ha
        have hp' := peelAs_patVal' hp
        rw [hpe] at hp'
        cases hp' with
        | ctor _ hs =>
          obtain ⟨rs, hrs, hr⟩ := EvalTerm.ctor_inv (isCtor_of_ctorPat hg) he
          cases hall : allSome rs with
          | none => rw [hall] at hr; cases hr
          | some vs' =>
            rw [hall] at hr
            cases hr
            rw [allSome_eq_map hall] at hrs
            have := argLeList_weight ts hl hs hrs
            simp only [GroundTerm.weight]; omega
        | hook hph _ _ => rw [not_patternHook_of_ctorPat hg] at hph; cases hph
        | coll hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
        | ovl hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
      · cases ha
    | .inj a b t, p, v, v', ha, hp, he => by
      simp only [Semantics.argLe] at ha
      split at ha
      · rename_i a' b' q hpe
        simp only [Bool.and_eq_true] at ha
        obtain ⟨hq, ht⟩ := ha
        have hp' := peelAs_patVal' hp
        rw [hpe] at hp'
        obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv hp'
        obtain ⟨r', he', hr⟩ := EvalTerm.inj_inv he
        cases r' with
        | none => cases hr
        | some u =>
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          obtain ⟨g, vs, rfl⟩ := ctorHeadInjL_val hq hw
          have := argLe_weight t ht hw he'
          have := weight_injNormal_leInjL a b u
          rw [weight_injNormal_ctorInjL]
          omega
      · cases ha
    | .as _ _, _, _, _, ha, _, _ => by simp [Semantics.argLe] at ha
  theorem argLeList_weight {σ : Subst} : ∀ (ts : List Term) {ps : List Term} {vs vs' : List GroundTerm},
      c.argLeList ts ps = true → PatVals c σ ps vs → EvalTerms c σ ts (vs'.map some) →
      GroundTerm.weightList vs' ≤ GroundTerm.weightList vs
    | [], [], _, vs', _, h, he => by
      cases h
      cases vs' with
      | nil => exact Nat.le_refl _
      | cons _ _ => cases he
    | t :: ts, p :: ps, _, vs', ha, h, he => by
      simp only [Semantics.argLeList, Bool.and_eq_true] at ha
      cases h with
      | cons h1 h2 =>
        cases vs' with
        | nil => cases he
        | cons v' vs' =>
          cases he with
          | cons e1 e2 =>
            have := argLe_weight t ha.1 h1 e1
            have := argLeList_weight ts ha.2 h2 e2
            simp only [GroundTerm.weightList]; omega
    | [], _ :: _, _, _, ha, _, _ => by simp [Semantics.argLeList] at ha
    | _ :: _, [], _, _, ha, _, _ => by simp [Semantics.argLeList] at ha
end

mutual
  /-- An argument `argLt` accepts against a pattern weighs strictly less than the value the pattern
  denotes. -/
  theorem argLt_weight {σ : Subst} : ∀ (a : Term) {p : Term} {v v' : GroundTerm}, c.argLt a p = true →
      PatVal c σ p v → EvalTerm c σ a (some v') → v'.weight < v.weight
    | .var j, p, v, v', ha, hp, he => by
      obtain ⟨w, hw, hlt⟩ := strictL_weight p hp (by simpa [Semantics.argLt] using ha)
      have := EvalTerm.var_inv he
      rw [hw] at this
      cases this
      exact hlt
    | .app g ts, p, v, v', ha, hp, he => by
      simp only [Semantics.argLt] at ha
      split at ha
      · rename_i g' ps hpe
        simp only [Bool.and_eq_true, beq_iff_eq] at ha
        obtain ⟨⟨⟨rfl, hg⟩, hl⟩, hs⟩ := ha
        have hp' := peelAs_patVal' hp
        rw [hpe] at hp'
        cases hp' with
        | ctor _ hps =>
          obtain ⟨rs, hrs, hr⟩ := EvalTerm.ctor_inv (isCtor_of_ctorPat hg) he
          cases hall : allSome rs with
          | none => rw [hall] at hr; cases hr
          | some vs' =>
            rw [hall] at hr
            cases hr
            rw [allSome_eq_map hall] at hrs
            have := argLtList_weight ts hl hs hps hrs
            simp only [GroundTerm.weight]; omega
        | hook hph _ _ => rw [not_patternHook_of_ctorPat hg] at hph; cases hph
        | coll hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
        | ovl hc _ _ _ => rw [isCtor_of_ctorPat hg] at hc; cases hc
      · cases ha
    | .dv _ _, _, _, _, ha, _, _ => by simp [Semantics.argLt] at ha
    | .inj a b t, p, v, v', ha, hp, he => by
      simp only [Semantics.argLt] at ha
      split at ha
      · rename_i a' b' q hpe
        simp only [Bool.and_eq_true] at ha
        obtain ⟨hq, ht⟩ := ha
        have hp' := peelAs_patVal' hp
        rw [hpe] at hp'
        obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv hp'
        obtain ⟨r', he', hr⟩ := EvalTerm.inj_inv he
        cases r' with
        | none => cases hr
        | some u =>
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          obtain ⟨g, vs, rfl⟩ := ctorHeadInjL_val hq hw
          have := argLt_weight t ht hw he'
          have := weight_injNormal_leInjL a b u
          rw [weight_injNormal_ctorInjL]
          omega
      · cases ha
    | .as _ _, _, _, _, ha, _, _ => by simp [Semantics.argLt] at ha
  theorem argLtList_weight {σ : Subst} : ∀ (ts : List Term) {ps : List Term} {vs vs' : List GroundTerm},
      c.argLeList ts ps = true → c.argLtList ts ps = true → PatVals c σ ps vs →
      EvalTerms c σ ts (vs'.map some) → GroundTerm.weightList vs' < GroundTerm.weightList vs
    | t :: ts, p :: ps, _, vs', hl, ha, h, he => by
      simp only [Semantics.argLeList, Bool.and_eq_true] at hl
      simp only [Semantics.argLtList, Bool.or_eq_true] at ha
      cases h with
      | cons h1 h2 =>
        cases vs' with
        | nil => cases he
        | cons v' vs' =>
          cases he with
          | cons e1 e2 =>
            simp only [GroundTerm.weightList]
            rcases ha with ha | ha
            · have := argLt_weight t ha h1 e1
              have := argLeList_weight ts hl.2 h2 e2
              omega
            · have := argLe_weight t hl.1 h1 e1
              have := argLtList_weight ts hl.2 ha h2 e2
              omega
    | [], _, _, _, _, ha, _, _ => by simp [Semantics.argLtList] at ha
    | _ :: _, [], _, _, _, ha, _, _ => by simp [Semantics.argLtList] at ha
end

/-- A self call in a clause of a function whose self calls decrease in weight at `dec`: its
argument there is strictly lighter than the clause's pattern there. -/
theorem decreasingOKL_clause {f : Fn} {dec : Option Nat} (h : c.decreasingOKL f dec = true)
    {cl : Clause} (hcl : cl ∈ f.clauses) {t : Term} (ht : t = cl.rhs ∨ cl.req = some t ∨ cl.ens = some t)
    {ts : List Term} (hts : ts ∈ callsOf f.label t) :
    ∃ i a p, dec = some i ∧ ts[i]? = some a ∧ cl.pats[i]? = some p ∧ c.argLt a p = true := by
  have hmem : (cl.pats, ts) ∈ selfCalls f := by
    simp only [selfCalls, List.mem_flatMap, List.mem_map]
    refine ⟨cl, hcl, ts, ?_, rfl⟩
    rcases ht with rfl | ht | ht
    · exact List.mem_append_left _ (List.mem_append_left _ hts)
    · rw [ht]; exact List.mem_append_left _ (List.mem_append_right _ hts)
    · rw [ht]; exact List.mem_append_right _ hts
  unfold Semantics.decreasingOKL at h
  have hne : (selfCalls f).isEmpty = false := by
    cases hs : selfCalls f with
    | nil => rw [hs] at hmem; cases hmem
    | cons _ _ => rfl
  simp only [hne, Bool.false_or] at h
  cases dec with
  | none => cases h
  | some i =>
    have := List.all_eq_true.mp h _ hmem
    simp only at this
    split at this
    · rename_i a p ha hp
      exact ⟨i, a, p, rfl, ha, hp, this⟩
    · cases this

/-- The measure of a self call: the weight of the argument at the decreasing position. -/
def decMeasureL (dec : Option Nat) (vs : List GroundTerm) : Nat :=
  ((vs[dec.getD 0]?).map GroundTerm.weight).getD 0

/-- **A function whose self calls decrease in weight, and whose other callees terminate,
terminates**: by induction on the weight of the argument at the decreasing position. The held variables are
read of this function alone (`hb`). -/
theorem terminates_of_decreasingLN (hc : EvalCtxN c) {fn : Fn} (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn)
    {dec : Option Nat}
    (hdec : c.decreasingOKL fn dec = true)
    (hcall : ∀ g ∈ fn.callees, g ≠ fn.label → Terminates c g)
    (hovl : ∀ g ∈ fn.callees, OvlTerminates c g) : Terminates c fn.label := by
  have hlook := lookupFn_of_memN hc hfn
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  suffices h : ∀ n vs, c.sortsOf vs = some fn.args → decMeasureL dec vs < n →
      ∃ r, Eval c fn.label vs r from h _ vs hvs (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro vs hvs hlt
    refine eval_of_callsN hc hfn hb hvs hovl (fun cl hcl σ hm t ht g ts hts gfn hg rs vs' hrs hall hsrt => ?_)
    by_cases hgl : g = fn.label
    · subst hgl
      rw [hlook] at hg
      cases hg
      obtain ⟨i, a, p, rfl, hai, hpi, hlti⟩ := decreasingOKL_clause hdec hcl ht hts
      obtain ⟨v, hvi, hpv⟩ := patVals_get hm hpi
      rw [allSome_eq_map hall] at hrs
      obtain ⟨v', hv'i, hev⟩ := evalTerms_some_inv hrs hai
      have hw := argLt_weight a hlti hpv hev
      refine ih vs' hsrt ?_
      have h1 : decMeasureL (some i) vs' = v'.weight := by simp [decMeasureL, hv'i]
      have h2 : decMeasureL (some i) vs = v.weight := by simp [decMeasureL, hvi]
      omega
    · exact hcall g (heads_callees hcl ht (mem_heads_of_callsOf t hts)) hgl gfn hg vs' hsrt

/-- **A function whose self calls decrease in weight, and whose other callees terminate,
terminates**: by induction on the weight of the argument at the decreasing position. -/
theorem terminates_of_decreasingL (hc : EvalCtx c) {fn : Fn} (hfn : fn ∈ c.allFns) {dec : Option Nat}
    (hdec : c.decreasingOKL fn dec = true)
    (hcall : ∀ g ∈ fn.callees, g ≠ fn.label → Terminates c g)
    (hovl : ∀ g ∈ fn.callees, OvlTerminates c g) : Terminates c fn.label :=
  terminates_of_decreasingLN hc.toN hfn (hc.binds fn hfn) hdec hcall hovl

/-! ## Int counters -/

theorem foldl_min_le : ∀ (l : List Int) (a : Int), l.foldl min a ≤ a ∧ ∀ b ∈ l, l.foldl min a ≤ b
  | [], a => ⟨Int.le_refl a, fun b hb => nomatch hb⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_min_le l (min a x)
    refine ⟨Int.le_trans h1 (Int.min_le_left a x), fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Int.le_trans h1 (Int.min_le_right a b)
    · exact h2 b hb

theorem ctrFloor_le {i : Nat} {f : Fn} {cl : Clause} (hcl : cl ∈ f.clauses) {x : Nat} {lo : Int}
    (h : ctrLo i cl = some (x, lo)) : ctrFloor i f ≤ lo - 1 := by
  unfold ctrFloor
  have := (foldl_min_le (f.clauses.filterMap fun cl => (ctrLo i cl).map (·.2)) 0).2 lo
    (List.mem_filterMap.mpr ⟨cl, hcl, by rw [h]; rfl⟩)
  omega

/-- An Int operation on two Ints, its value: what the operation gives on their values. -/
theorem int2_val_inv {σ : Subst} {f : Sym} {t u : Term} {g : Int → Int → Option GroundTerm}
    {w : GroundTerm} (hct : c.isCtor f = false) (hhk : isHook f = true)
    (hf : ∀ vs, hook f vs = some (int2 vs g)) (h : EvalTerm c σ (.app f [t, u]) (some w))
    (hs : silentKey f = false := by decide +kernel) :
    ∃ a b x y, EvalTerm c σ t (some a) ∧ EvalTerm c σ u (some b) ∧ asInt a = some x ∧
      asInt b = some y ∧ g x y = some w := by
  generalize ht : Term.app f [t, u] = e at h
  generalize hr : some w = r at h
  cases h with
  | var => cases ht
  | dv => cases ht
  | inj _ => cases ht
  | ctor hk _ => cases ht; rw [hct] at hk; cases hk
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
        rw [Semantics.hookRes_of_notKey hs, hf, Option.some.injEq] at hv
        subst hv
        cases hx : asInt w₁ with
        | none => simp [int2, hx] at hr
        | some x =>
          cases hy : asInt w₂ with
          | none => simp [int2, hx, hy] at hr
          | some y =>
            refine ⟨w₁, w₂, x, y, h1, h2, hx, hy, ?_⟩
            simp only [int2, hx, hy, Option.bind_some] at hr ⊢
  | param _ hh _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | call _ hh _ _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | callUndef _ hh _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | ovl _ ho _ => cases ht; rw [(c.isOvl_parts ho).2.1] at hhk; cases hhk
  | ovlFn _ ho => cases ht; rw [(c.isOvl_parts ho).2.1] at hhk; cases hhk

theorem evalTerm_var_inv {σ : Subst} {x : Nat} {v : GroundTerm} (h : EvalTerm c σ (.var x) (some v)) :
    σ.lookup x = some v := by
  generalize ht : Term.var x = t at h
  generalize hr : some v = r at h
  cases h with
  | var => cases ht; rfl
  | _ => cases ht

theorem evalTerm_dv_inv {σ : Subst} {s : Srt} {l : Lit} {v : GroundTerm} (h : EvalTerm c σ (.dv s l) (some v)) :
    v = .dv s l := by
  generalize ht : Term.dv s l = t at h
  generalize hr : some v = r at h
  cases h with
  | dv => cases ht; exact Option.some.inj hr
  | _ => cases ht

theorem hook_intSub (vs : List GroundTerm) : hook intSub vs = some (int2 vs fun x y => some (int (x - y))) := rfl
theorem hook_intTDiv (vs : List GroundTerm) : hook intTDiv vs = some (int2 vs fun x y => nonzero y (x.tdiv y)) := rfl

/-- The value of an Int counter at a self call, as its measure: its distance from the floor `L`. -/
def ctrMeasure (i : Nat) (L : Int) (vs : List GroundTerm) : Nat :=
  match vs[i]? with
  | some v => match asInt v with
    | some x => (x - L).toNat
    | none => 0
  | none => 0

/-- **A function whose self calls decrease at an Int counter bounded below, and whose other callees
terminate, terminates**: by induction on the counter's distance from the floor `ctrFloor`; a self
call's `requires` holds where its right-hand side is evaluated, so the bound applies there. The
held variables are read of this function alone (`hb`). -/
theorem terminates_of_ctrN (hc : EvalCtxN c) (hs : c.shapesOK = true) (hsub : c.isCtor intSub = false)
    (hdiv : c.isCtor intTDiv = false) {fn : Fn} (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn)
    {i : Nat} (hctr : ctrOK fn i = true)
    (hcall : ∀ g ∈ fn.callees, g ≠ fn.label → Terminates c g)
    (hovl : ∀ g ∈ fn.callees, OvlTerminates c g) : Terminates c fn.label := by
  have hlook := lookupFn_of_memN hc hfn
  obtain ⟨L, hL, hrs⟩ := hc.sort.fns fn hfn
  obtain ⟨L', hL', hreqs⟩ := hc.reqs fn hfn
  simp only [ctrOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hctr
  obtain ⟨hi, hcls⟩ := hctr
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  suffices h : ∀ n vs, c.sortsOf vs = some fn.args → ctrMeasure i (ctrFloor i fn) vs < n →
      ∃ r, Eval c fn.label vs r from h _ vs hvs (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro vs hvs hlt
    refine eval_resultRH hlook (hc.plain fn hfn) hb
      (fun cl hcl σ hσ _ => ⟨fun t ht => ?_, true, Clause.holds_preTop (hc.pres fn hfn cl hcl) σ⟩)
      (fun cl hcl σ ha => ?_) (fun cl hcl σ ha t ht => ?_)
    · have hq := hreqs cl hcl
      rw [ht] at hq
      simp only [reqOK, beq_iff_eq] at hq
      have hnoself := (hcls cl hcl).1.1
      rw [ht] at hnoself
      simp only [Option.map_some, Option.getD_some, List.isEmpty_iff] at hnoself
      exact evalTerm_result hc.sort hL' hσ t hq (fun g hg => hovl g (heads_req_callees hcl ht hg)) fun g ts hts gfn hg _ vs' _ _ hsrt => by
        have hgl : g ≠ fn.label := by
          rintro rfl
          rw [hnoself] at hts
          cases hts
        exact hcall g (heads_req_callees hcl ht (mem_heads_of_callsOf t hts)) hgl gfn hg vs' hsrt
    · obtain ⟨hσ, hm, hq, -⟩ := ha
      replace hσ := (wellSortedAt_univ (hc.plain fn hfn cl hcl).1).mp hσ
      exact evalTerm_result hc.sort hL hσ cl.rhs (hrs cl hcl) (fun g hg => hovl g (heads_rhs_callees hcl hg)) fun g ts hts gfn hg rs vs' hrs' hall hsrt => by
        by_cases hgl : g = fn.label
        · subst hgl
          rw [hlook] at hg
          cases hg
          refine ih vs' hsrt ?_
          have hcl2 := (hcls cl hcl).2
          simp only [Bool.or_eq_true, List.isEmpty_iff] at hcl2
          rcases hcl2 with hne | hcl2
          · rw [hne] at hts; cases hts
          cases hlo : ctrLo i cl with
          | none => rw [hlo] at hcl2; cases hcl2
          | some p =>
          obtain ⟨x, lo⟩ := p
          rw [hlo] at hcl2
          simp only [List.all_eq_true] at hcl2
          have hts' := hcl2 ts hts
          cases hti : ts[i]? with
          | none => rw [hti] at hts'; cases hts'
          | some a =>
          rw [hti] at hts'
          dsimp only at hts'
          -- the counter's value in the clause
          have hpat : cl.pats[i]? = some (.var x) := by
            unfold ctrLo at hlo
            split at hlo
            · rename_i y hy
              obtain ⟨lo', _, he⟩ := Option.map_eq_some_iff.mp hlo
              cases he
              exact hy
            · cases hlo
          obtain ⟨v, hvi, hpv⟩ := patVals_get hm hpat
          have hσx : σ.lookup x = some v := by cases hpv with | var h => exact h
          have hvsrt : c.sortOf v = some Srt.int := by
            obtain ⟨v', hv', hs'⟩ := sortsOf_get hvs hi
            rw [hvi] at hv'
            cases hv'
            exact hs'
          obtain ⟨X, rfl⟩ := shape_int hs hvsrt
          have hloX : lo ≤ X := by
            unfold ctrLo at hlo
            rw [hpat] at hlo
            obtain ⟨lo', hfs, he⟩ := Option.map_eq_some_iff.mp hlo
            cases he
            obtain ⟨l, hl, hlow⟩ := List.exists_of_findSome?_eq_some hfs
            cases hr : cl.req with
            | none => rw [hr] at hl; simp at hl
            | some q =>
            rw [hr] at hl
            simp only [Option.map_some, Option.getD_some] at hl
            have hle := lits_sound (hq q hr) hl
            unfold lowerOf at hlow
            split at hlow
            · rename_i y lo₀ hi₀ hb
              split at hlow
              · rename_i hyx
                cases hlow
                have hyx := beq_iff_eq.mp hyx
                subst hyx
                obtain ⟨v', X', ev', hX', hlo', _⟩ := intBound_sound hb hle
                rw [evalTerm_var_inv ev'] at hσx
                cases hσx
                simp [asInt, int] at hX'
                subst hX'
                exact hlo' _ rfl
              · cases hlow
            · cases hlow
          have hfl := ctrFloor_le hcl hlo
          rw [allSome_eq_map hall] at hrs'
          obtain ⟨w, hwi, hw⟩ := evalTerms_some_inv hrs' hti
          have hmv : ctrMeasure i (ctrFloor i fn) vs = (X - ctrFloor i fn).toNat := by
            simp [ctrMeasure, hvi, asInt, int]
          -- the argument's value
          have hval : ∃ W, w = int W ∧ W < X := by
            unfold ctrArg at hts'
            split at hts'
            · rename_i f' y s k
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hts'
              obtain ⟨⟨rfl, rfl⟩, hop⟩ := hts'
              rcases hop with ⟨rfl, hk⟩ | ⟨⟨rfl, hk⟩, hlo1⟩
              · obtain ⟨a', b', x', y', ea, eb, hxa, hyb, hg⟩ := int2_val_inv hsub rfl hook_intSub hw
                rw [evalTerm_var_inv ea] at hσx
                cases hσx
                rw [evalTerm_dv_inv eb] at hyb
                simp [asInt, int] at hxa hyb
                subst hxa; subst hyb
                simp only [Option.some.injEq] at hg
                exact ⟨_, hg.symm, by omega⟩
              · obtain ⟨a', b', x', y', ea, eb, hxa, hyb, hg⟩ := int2_val_inv hdiv rfl hook_intTDiv hw
                rw [evalTerm_var_inv ea] at hσx
                cases hσx
                rw [evalTerm_dv_inv eb] at hyb
                simp [asInt, int] at hxa hyb
                subst hxa; subst hyb
                simp only [nonzero, show k ≠ 0 by omega, ite_false, Option.some.injEq] at hg
                refine ⟨_, hg.symm, ?_⟩
                rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
                exact Int.ediv_lt_of_lt_mul (by omega) (by
                  have : X * 2 ≤ X * k := Int.mul_le_mul_of_nonneg_left hk (by omega)
                  omega)
            · rename_i s k
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hts'
              obtain ⟨rfl, hk⟩ := hts'
              rw [evalTerm_dv_inv hw]
              exact ⟨k, rfl, by omega⟩
            · cases hts'
          obtain ⟨W, rfl, hW⟩ := hval
          have hmw : ctrMeasure i (ctrFloor i fn) vs' = (W - ctrFloor i fn).toNat := by
            simp [ctrMeasure, hwi, asInt, int]
          rw [hmw]
          rw [hmv] at hlt
          omega
        · exact hcall g (heads_rhs_callees hcl (mem_heads_of_callsOf _ hts)) hgl gfn hg vs' hsrt
    · obtain ⟨L'', hL'', hens⟩ := hc.enss fn hfn
      have hq := hens cl hcl
      rw [ht] at hq
      simp only [reqOK, beq_iff_eq] at hq
      have hnoself := (hcls cl hcl).1.2
      rw [ht] at hnoself
      simp only [Option.map_some, Option.getD_some, List.isEmpty_iff] at hnoself
      exact evalTerm_result hc.sort hL'' ((wellSortedAt_univ (hc.plain fn hfn cl hcl).1).mp ha.1) t hq (fun g hg => hovl g (heads_ens_callees hcl ht hg)) fun g ts hts gfn hg _ vs' _ _ hsrt => by
        have hgl : g ≠ fn.label := by
          rintro rfl
          rw [hnoself] at hts
          cases hts
        exact hcall g (heads_ens_callees hcl ht (mem_heads_of_callsOf t hts)) hgl gfn hg vs' hsrt

/-- **A function whose self calls decrease at an Int counter bounded below, and whose other callees
terminate, terminates**: by induction on the counter's distance from the floor `ctrFloor`; a self
call's `requires` holds where its right-hand side is evaluated, so the bound applies there. -/
theorem terminates_of_ctr (hc : EvalCtx c) (hs : c.shapesOK = true) (hsub : c.isCtor intSub = false)
    (hdiv : c.isCtor intTDiv = false) {fn : Fn} (hfn : fn ∈ c.allFns)
    {i : Nat} (hctr : ctrOK fn i = true)
    (hcall : ∀ g ∈ fn.callees, g ≠ fn.label → Terminates c g)
    (hovl : ∀ g ∈ fn.callees, OvlTerminates c g) : Terminates c fn.label :=
  terminates_of_ctrN hc.toN hs hsub hdiv hfn (hc.binds fn hfn) hctr hcall hovl

kernel_rfl Semantics.decObligationsL_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).decObligationsL = c.decObligationsL

end KCore
