/-
  KCore: noninterference for definitions whose secrets are whole cells, a decided condition of the
  noninterference kind (Noninterference.lean, ARCHITECTURE.md §3.7).

  **The policy.** A set H of high positions in the configuration (`HPaths`: argument indices from
  the top cell down; `highOf p names` is the contents of the cells named in the presentation's
  cell tree). An observer sees
  everything outside H.

  **The relation** (`LowEq c lo H`, `EqOut`): two configurations are equal outside H; at a high
  position they may differ, keeping the same sort. It is the `Start` and `Obs` of the statement:
  runs from configurations that agree outside H end, when both stop (`Stuck`), in configurations
  that agree outside H.

  **The decided condition, per rule** (`cellsCond c H r`, read off the rule's syntax):
  - the left-hand side follows H through constructor applications and binds a variable at each
    high position or above it (`lhsOK`); those variables, the rule's *high variables*
    (`hiVars`), occur once in the left-hand side, nowhere in its low part (`loVars`) and not in
    the `requires` or the `pre` (`appOK`). So whether the rule applies, its `requires` and its
    `pre`, do not depend on what is at H (a condition's truth value reads its variables only,
    `Holds.congr_NI`);
  - the right-hand side places each high variable at a position with the same high part as
    where the left-hand side bound it, through constructor applications only (`rhsOK`); every
    other subterm reads no high variable. So the result is defined at both configurations or at
    neither, and the two results agree outside H; the `ensures` and the `post` read no high
    variable (`ensOK`), so each has one result at both;
  - every rule of a smaller priority satisfies the first condition, so the same rules are blocked
    at both configurations.

  **The generic theorem** (`tini_cells`): if every rule satisfies the condition (one kernel
  decision, `allExcept`), `Step` is noninterfering for H. The relation is a lockstep unwinding:
  a step of one configuration is matched by the same rule's step of the other
  (`cellsCond_sound`), and `Noninterference.tini_of_unwinding` gives the statement. Rules the
  decision does not cover are named obligations (`tini_cells_of`). As a `Kind` (Kind.lean):
  `cellsKind`, indexed by the rules, the obligation at a rule its unwinding, `cellsCond` its
  decider; `cellsKindOn` relative to an invariant; `cellsKindAll`, `cellsKindOnAll` and their
  deciders for an interpretation of the parameters, decided once on the data.

  **Keyed positions** (`keyedOf`): a map cell secret except at the keys the observer is given
  (`lo`). There the relation is `KeyRel` (the same keys, the same entries at `lo`, and
  well-sorted entries at the same keys), and the right-hand side may also update the map by a key
  and a value that read no high variable (`updOK`), which keeps the maps related. Every relation
  takes `lo`; the condition does not read it, so one decision covers every choice of observed keys.

  **Relative to an invariant** (`tini_cells_on`, `tini_cells_on_all`): from configurations where
  `Init` holds, given an invariant `Invariant c Init Inv`, determinism where `Inv` holds
  (`DeterministicOn`, which determinism up to overlaps gives with each listed overlap refuted
  where `Inv` holds: `deterministicOn_of_except_all`; or the determinism kind with its
  obligations where `Inv` holds, `Det.kindAll`), and the listed rules' unwinding where `Inv`
  holds (`RuleUnwindsOn`). The condition is sound at every pair of configurations
  (`cellsCond_sound_on` for every `Inv`). The kinds without an invariant glue through the instance
  `Init = Inv = fun _ => True` (`tini_cells_of_rules`).

  **Every interpretation of the parameters** (`tini_cells_of_all`): the policy (`highOf`,
  `keyedOf`, of the presentation) and the condition (`cellsCond`) do not read `hooks`, so the decision on the data gives
  the statement for every `c.withHooks H`.

  What it does not cover: reading a keyed map at a key (`X |-> V` in the left-hand side), a branch
  on a secret, and a computation on a secret other than by constructors and that update
  (`S +Int 1` written back to the high cell).
-/
import KcoreSpec.Noninterference
import KcoreSpec.Collections
import KcoreSpec.HoldsCongr

set_option autoImplicit false

namespace KCore.NI

open KCore KCore.Exec

variable {c : Semantics} {lo : GroundTerm → Prop}

/-! ## High positions -/

/-- High positions, as argument indices from a term down. -/
abbrev HPaths := List (List Nat)

/-- The high positions below argument i. -/
def subH (H : HPaths) (i : Nat) : HPaths :=
  H.filterMap fun | j :: q => if j == i then some q else none | [] => none

theorem subH_nil (i : Nat) : subH [] i = [] := rfl

mutual
  /-- The positions of the contents of the cells named n (a leaf's content, a node's whole). -/
  def cellPaths (n : String) : Cell → HPaths
    | .leaf m _ _ => if m == n then [[0]] else []
    | .node m cs _ => if m == n then [[]] else cellPathsL n 0 cs
    | .coll _ => []
    termination_by structural x => x
  def cellPathsL (n : String) : Nat → List Cell → HPaths
    | _, [] => []
    | i, x :: xs => (cellPaths n x).map (i :: ·) ++ cellPathsL n (i + 1) xs
    termination_by structural _ xs => xs
end

/-- The high positions of a policy that keeps the cells named secret. -/
def highOf (p : Presentation) (names : List String) : HPaths := names.flatMap (cellPaths · p.topCell)

/-- The marker that ends a keyed position (`keyedOf`): no constructor has this many arguments. -/
def keyTag : Nat := 1000000

/-- The keyed positions of a policy that keeps the cells named secret except at the observed keys:
each holds a map, of which the observer sees the keys and the entries at the keys `lo` names. -/
def keyedOf (p : Presentation) (names : List String) : HPaths :=
  (names.flatMap (cellPaths · p.topCell)).map (· ++ [keyTag])

/-! ## Maps related at a keyed position -/

/-- At a key: both maps have no entry, or both have one, well-sorted at both or at neither. -/
def OkSame (c : Semantics) (k : GroundTerm) : Option GroundTerm → Option GroundTerm → Prop
  | none, none => True
  | some v, some w => c.entryOK Srt.kitem Srt.kitem (k, v) = c.entryOK Srt.kitem Srt.kitem (k, w)
  | _, _ => False

/-- Two canonical maps with the same keys, the same entries at the keys `lo` names, and entries
well-sorted at the same keys. -/
def KeyRel (c : Semantics) (lo : GroundTerm → Prop) (a b : Entries) : Prop :=
  Map.Canon a ∧ Map.Canon b ∧ ∀ k, (lo k → Map.find a k = Map.find b k) ∧ OkSame c k (Map.find a k) (Map.find b k)

theorem OkSame.symm {k : GroundTerm} : ∀ {a b : Option GroundTerm}, OkSame c k a b → OkSame c k b a
  | none, none, _ => trivial
  | some _, some _, h => Eq.symm h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem KeyRel.symm {a b : Entries} (h : KeyRel c lo a b) : KeyRel c lo b a :=
  ⟨h.2.1, h.1, fun k => ⟨fun hk => ((h.2.2 k).1 hk).symm, (h.2.2 k).2.symm⟩⟩

/-- Related maps have the same sort. -/
theorem KeyRel.sortOf_eq {a b : Entries} (h : KeyRel c lo a b) :
    c.sortOf (.map Srt.map a) = c.sortOf (.map Srt.map b) := by
  obtain ⟨ha, hb, hr⟩ := h
  have half : ∀ {x y : Entries}, Map.Canon x → Map.Canon y →
      (∀ k, OkSame c k (Map.find x k) (Map.find y k)) → c.entriesOK Srt.kitem Srt.kitem x = true →
        c.entriesOK Srt.kitem Srt.kitem y = true := by
    intro x y hx hy hk hex
    rw [Map.entriesOK_iff] at hex ⊢
    intro ⟨k, w⟩ hm
    have hfy := Map.find_of_mem hy hm
    have hk' := hk k
    rw [hfy] at hk'
    cases hfx : Map.find x k with
    | none => rw [hfx] at hk'; exact hk'.elim
    | some v =>
      rw [hfx] at hk'
      exact hk' ▸ hex _ (Map.mem_of_find hfx)
  have he : c.entriesOK Srt.kitem Srt.kitem a = c.entriesOK Srt.kitem Srt.kitem b := by
    cases h1 : c.entriesOK Srt.kitem Srt.kitem a <;> cases h2 : c.entriesOK Srt.kitem Srt.kitem b
    · rfl
    · exact absurd (half hb ha (fun k => (hr k).2.symm) h2) (by simp [h1])
    · exact absurd (half ha hb (fun k => (hr k).2) h1) (by simp [h2])
    · rfl
  rw [Map.sortOf_map, Map.sortOf_map, he, show keysSorted a = true from ha, show keysSorted b = true from hb]

/-- An update by the same key and value keeps maps related. -/
theorem KeyRel.insert {a b : Entries} (h : KeyRel c lo a b) (k v : GroundTerm) :
    KeyRel c lo (insertE k v a) (insertE k v b) := by
  obtain ⟨ha, hb, hr⟩ := h
  refine ⟨Map.insert_canon ha, Map.insert_canon hb, fun k' => ?_⟩
  rw [Map.find_insert, Map.find_insert]
  by_cases he : k' = k
  · rw [if_pos he, if_pos he]; exact ⟨fun _ => rfl, rfl⟩
  · rw [if_neg he, if_neg he]; exact hr k'

/-! ## Equal outside the high positions -/

/-- `EqOut c lo H v₁ v₂`: v₁ and v₂ are equal outside H; at a high position both have the same sort. -/
inductive EqOut (c : Semantics) (lo : GroundTerm → Prop) : HPaths → GroundTerm → GroundTerm → Prop where
  | high {H : HPaths} {v₁ v₂ : GroundTerm} (h : [] ∈ H) (hs : c.sortOf v₁ = c.sortOf v₂) : EqOut c lo H v₁ v₂
  | same {H : HPaths} {v : GroundTerm} : EqOut c lo H v v
  | ctor {H : HPaths} {f : Sym} {vs₁ vs₂ : List GroundTerm} (hl : vs₁.length = vs₂.length)
      (h : ∀ i a b, vs₁[i]? = some a → vs₂[i]? = some b → EqOut c lo (subH H i) a b) :
      EqOut c lo H (.ctor f vs₁) (.ctor f vs₂)
  /-- At a keyed position, two maps related by `KeyRel`. -/
  | keyed {H : HPaths} {es₁ es₂ : Entries} (h : [keyTag] ∈ H) (hk : KeyRel c lo es₁ es₂) :
      EqOut c lo H (.map Srt.map es₁) (.map Srt.map es₂)

theorem EqOut.symm {H : HPaths} {v₁ v₂ : GroundTerm} (h : EqOut c lo H v₁ v₂) : EqOut c lo H v₂ v₁ := by
  induction h with
  | high h hs => exact .high h hs.symm
  | same => exact .same
  | ctor hl _ ih => exact .ctor hl.symm fun i a b ha hb => ih i b a hb ha
  | keyed h hk => exact .keyed h hk.symm

theorem sortsOf_eq {l₁ l₂ : List GroundTerm} (hl : l₁.length = l₂.length)
    (h : ∀ (i : Nat) (a b : GroundTerm), l₁[i]? = some a → l₂[i]? = some b → c.sortOf a = c.sortOf b) :
    c.sortsOf l₁ = c.sortsOf l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => cases hl
  | cons a as ih => cases l₂ with
    | nil => cases hl
    | cons b bs =>
      have h0 := h 0 a b (by simp) (by simp)
      have h1 := ih (by simpa using hl) fun i x y hx hy => h (i + 1) x y hx hy
      simp only [Semantics.sortsOf, h0, h1]

/-- Terms equal outside H have the same sort, where no symbol's being a value reads its arguments
(no overloading symbol, no raw parameter). -/
theorem EqOut.sortOf_eq (hno : c.ovls = []) (_hr : ∀ k ∈ c.params, k.raw = false) {H : HPaths} {v₁ v₂ : GroundTerm} (h : EqOut c lo H v₁ v₂) :
    c.sortOf v₁ = c.sortOf v₂ := by
  induction h with
  | high _ hs => exact hs
  | same => rfl
  | ctor hl _ ih =>
    simp only [Semantics.sortOf, sortsOf_eq hl ih, Semantics.lookupOvl, hno, List.find?_nil,
      c.lookupOpen_of_noRaw _hr]
  | keyed _ hk => exact hk.sortOf_eq

/-- With no high positions, equal outside them is equal. -/
theorem EqOut.eq_of_nil {H : HPaths} {v₁ v₂ : GroundTerm} (h : EqOut c lo H v₁ v₂) (hH : H = []) : v₁ = v₂ := by
  induction h with
  | high h _ => subst hH; cases h
  | keyed h _ => subst hH; cases h
  | same => rfl
  | @ctor H' f vs₁ vs₂ hl _ ih =>
    subst hH
    congr 1
    apply List.ext_getElem? ; intro i
    cases ha : vs₁[i]? with
    | none =>
      cases hb : vs₂[i]? with
      | none => rfl
      | some b =>
        have := (List.getElem?_eq_some_iff.mp hb).1
        rw [List.getElem?_eq_none_iff] at ha; omega
    | some a =>
      cases hb : vs₂[i]? with
      | none =>
        have := (List.getElem?_eq_some_iff.mp ha).1
        rw [List.getElem?_eq_none_iff] at hb; omega
      | some b => rw [ih i a b ha hb (subH_nil i)]

/-- A constructor term equal outside H, above every high position: the same constructor, its
arguments equal outside the positions below them. -/
theorem EqOut.ctor_inv {H : HPaths} {f : Sym} {vs₁ : List GroundTerm} {v₂ : GroundTerm}
    (h : EqOut c lo H (.ctor f vs₁) v₂) (hH : [] ∉ H) :
    ∃ vs₂, v₂ = .ctor f vs₂ ∧ vs₁.length = vs₂.length ∧
      ∀ i a b, vs₁[i]? = some a → vs₂[i]? = some b → EqOut c lo (subH H i) a b := by
  cases h with
  | high h _ => exact absurd h hH
  | same =>
    refine ⟨vs₁, rfl, rfl, fun i a b ha hb => ?_⟩
    rw [ha] at hb; cases hb; exact .same
  | ctor hl h => exact ⟨_, rfl, hl, h⟩

/-! ## The condition on a rule's sides -/

mutual
  /-- The left-hand side follows the high positions H through constructor applications and binds
  a variable at or above each of them. -/
  def lhsOK (c : Semantics) : HPaths → Term → Bool
    | _, .var _ => true
    | H, .app f ps => H.isEmpty ||
        (!H.contains [] && c.isCtor f && !patternHooks.contains f && lhsOKL c H 0 ps)
    | H, .inj .. => H.isEmpty
    | H, .as .. => H.isEmpty
    | H, .dv .. => H.isEmpty
    termination_by structural _ t => t
  def lhsOKL (c : Semantics) : HPaths → Nat → List Term → Bool
    | _, _, [] => true
    | H, i, p :: ps => lhsOK c (subH H i) p && lhsOKL c H (i + 1) ps
    termination_by structural _ _ ps => ps
end

mutual
  /-- The left-hand side's high variables, each with the high positions below it. -/
  def hiVars : HPaths → Term → List (Nat × HPaths)
    | H, .var j => if H.isEmpty then [] else [(j, H)]
    | H, .app _ ps => if H.isEmpty then [] else hiVarsL H 0 ps
    | _, .inj .. => []
    | _, .as .. => []
    | _, .dv .. => []
    termination_by structural _ t => t
  def hiVarsL : HPaths → Nat → List Term → List (Nat × HPaths)
    | _, _, [] => []
    | H, i, p :: ps => hiVars (subH H i) p ++ hiVarsL H (i + 1) ps
    termination_by structural _ _ ps => ps
end

mutual
  /-- The variables of the left-hand side's low part. -/
  def loVars : HPaths → Term → List Nat
    | H, .var j => if H.isEmpty then [j] else []
    | H, .app f ps => if H.isEmpty then varOccs (.app f ps) else loVarsL H 0 ps
    | H, .inj a b t => if H.isEmpty then varOccs (.inj a b t) else []
    | H, .as t j => if H.isEmpty then varOccs (.as t j) else []
    | _, .dv .. => []
    termination_by structural _ t => t
  def loVarsL : HPaths → Nat → List Term → List Nat
    | _, _, [] => []
    | H, i, p :: ps => loVars (subH H i) p ++ loVarsL H (i + 1) ps
    termination_by structural _ _ ps => ps
end

mutual
  /-- The values the left-hand side's high variables take at a configuration. -/
  def hiVals : HPaths → Term → GroundTerm → List (Nat × GroundTerm)
    | H, .var j, v => if H.isEmpty then [] else [(j, v)]
    | H, .app _ ps, .ctor _ vs => if H.isEmpty then [] else hiValsL H 0 ps vs
    | _, _, _ => []
    termination_by structural _ t => t
  def hiValsL : HPaths → Nat → List Term → List GroundTerm → List (Nat × GroundTerm)
    | H, i, p :: ps, v :: vs => hiVals (subH H i) p v ++ hiValsL H (i + 1) ps vs
    | _, _, _, _ => []
    termination_by structural _ _ ps => ps
end

/-- No number occurs twice. -/
def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- `t` reads a variable of `hv`. -/
def readsHigh (hv : List (Nat × HPaths)) (t : Term) : Bool :=
  (varOccs t).any fun j => hv.any (·.1 == j)

/-- `M[K <- V]` at a keyed position, where M is a high variable bound at that same keyed position
and K, V read no high variable: the update by the same key and value keeps the maps related. -/
def updOK (c : Semantics) (hv : List (Nat × HPaths)) (H : HPaths) (f : Sym) (ts : List Term) : Bool :=
  f == mapUpdate && !c.isCtor f && H == [[keyTag]] &&
    match ts with
    | [.var j, a, b] => hv.any (fun p => p.1 == j && p.2 == H) && !readsHigh hv a && !readsHigh hv b
    | _ => false

mutual
  /-- The right-hand side places each high variable where its high part is the left-hand side's,
  through constructor applications, and reads no high variable elsewhere. -/
  def rhsOK (c : Semantics) (hv : List (Nat × HPaths)) : HPaths → Term → Bool
    | H, .var j => !readsHigh hv (.var j) || hv.any (fun p => p.1 == j && p.2 == H)
    | H, .app f ts => !readsHigh hv (.app f ts) || (c.isCtor f && rhsOKL c hv H 0 ts) || updOK c hv H f ts
    | _, t => !readsHigh hv t
    termination_by structural _ t => t
  def rhsOKL (c : Semantics) (hv : List (Nat × HPaths)) : HPaths → Nat → List Term → Bool
    | _, _, [] => true
    | H, i, t :: ts => rhsOK c hv (subH H i) t && rhsOKL c hv H (i + 1) ts
    termination_by structural _ _ ts => ts
end

/-- Whether the rule applies, its `requires` and its `pre`, do not depend on what is at H (no
variable of `pre` is a high variable); no symbol's being a value reads its arguments (no
overloading symbol, no raw parameter), so that terms equal outside H have one sort; and its left
side binds every variable. -/
def appOK (c : Semantics) (H : HPaths) (r : Rule) : Bool :=
  let ks := (hiVars H r.lhs).map (·.1)
  lhsOK c H r.lhs && nodupB ks && !(loVars H r.lhs).any ks.contains &&
    (match r.req with
      | none => true
      | some t => !(varOccs t).any ks.contains) && c.ovls.isEmpty && !c.params.any (·.raw) &&
    !(varOccsCond r.vars.length r.pre).any ks.contains && binds r.vars.length (varOccs r.lhs)

/-- The rule's `ensures` and its `post` read none of its high variables. -/
def ensOK (H : HPaths) (r : Rule) : Bool :=
  (match r.ens with
  | none => true
  | some t => !(varOccs t).any ((hiVars H r.lhs).map (·.1)).contains) &&
  !(varOccsCond r.vars.length r.post).any ((hiVars H r.lhs).map (·.1)).contains

/-- **The decided condition** at a rule. -/
def cellsCond (c : Semantics) (H : HPaths) (r : Rule) : Bool :=
  appOK c H r && rhsOK c (hiVars H r.lhs) H r.rhs && ensOK H r &&
    c.rules.all fun r' => !decide (r'.prio < r.prio) || appOK c H r'

/-! ## Substitutions -/

theorem lookup_cons (j k : Nat) (w : GroundTerm) (σ : Subst) :
    ((k, w) :: σ).lookup j = if j = k then some w else σ.lookup j := by
  by_cases h : j = k
  · subst h; simp [List.lookup]
  · have : (j == k) = false := by simp [h]
    simp [List.lookup, this, h]

theorem lookup_append_of_not_mem {τ σ : Subst} {j : Nat} (h : j ∉ τ.map (·.1)) :
    (τ ++ σ).lookup j = σ.lookup j := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.cons_append, lookup_cons, if_neg h.1, ih h.2]

theorem nodupB_cons {x : Nat} {xs : List Nat} (h : nodupB (x :: xs) = true) :
    x ∉ xs ∧ nodupB xs = true := by
  simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun hm => ?_, h.2⟩
  have : xs.contains x = true := List.contains_iff_mem.mpr hm
  rw [this] at h; cases h.1

theorem lookup_append_of_mem {τ σ : Subst} {j : Nat} {w : GroundTerm}
    (hn : nodupB (τ.map (·.1)) = true) (h : (j, w) ∈ τ) : (τ ++ σ).lookup j = some w := by
  induction τ with
  | nil => cases h
  | cons p τ ih =>
    obtain ⟨k, w'⟩ := p
    have ⟨hk, hn'⟩ := nodupB_cons hn
    rw [List.cons_append, lookup_cons]
    rcases List.mem_cons.mp h with h | h
    · cases h; simp
    · have : j ≠ k := fun e => hk (e ▸ List.mem_map_of_mem (f := (·.1)) h)
      rw [if_neg this]; exact ih hn' h

theorem mem_unique {β : Type} {l : List (Nat × β)} (hn : nodupB (l.map (·.1)) = true) {j : Nat} {a b : β}
    (ha : (j, a) ∈ l) (hb : (j, b) ∈ l) : a = b := by
  induction l with
  | nil => cases ha
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    have ⟨hk, hn'⟩ := nodupB_cons hn
    rcases List.mem_cons.mp ha with ha1 | ha2 <;> rcases List.mem_cons.mp hb with hb1 | hb2
    · obtain ⟨_, rfl⟩ := Prod.mk.inj ha1; obtain ⟨_, rfl⟩ := Prod.mk.inj hb1; rfl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha1
      exact absurd (List.mem_map.mpr ⟨(j, b), hb2, rfl⟩ : j ∈ l.map (·.1)) hk
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb1
      exact absurd (List.mem_map.mpr ⟨(j, a), ha2, rfl⟩ : j ∈ l.map (·.1)) hk
    · exact ih hn' ha2 hb2

/-! ## Matching does not read the high positions -/

mutual
  theorem PatVal.congr {σ σ' : Subst} : ∀ {p : Term} {v : GroundTerm}, PatVal c σ p v →
      (∀ j ∈ varOccs p, σ'.lookup j = σ.lookup j) → PatVal c σ' p v
    | .var j, v, h, ha => by
      cases h with
      | var h => exact .var (by rw [ha j (by simp [varOccs]), h])
    | .dv s l, v, h, _ => by cases h; exact .dv
    | .app f ps, v, h, ha => by
      have ha' : ∀ j ∈ varOccsList ps, σ'.lookup j = σ.lookup j := fun j hj => ha j (by simpa [varOccs] using hj)
      cases h with
      | ctor hc hs => exact .ctor hc (PatVals.congr hs ha')
      | hook hp hs hv => exact .hook hp (PatVals.congr hs ha') hv
      | coll hc hp hs hv => exact .coll hc hp (PatVals.congr hs ha') hv
      | ovl hc ho hs hv => exact .ovl hc ho (PatVals.congr hs ha') hv
    | .inj a b p, v, h, ha => by
      cases h with
      | inj h => exact .inj (PatVal.congr h fun j hj => ha j (by simpa [varOccs] using hj))
    | .as p i, v, h, ha => by
      cases h with
      | as h hi =>
        exact .as (PatVal.congr h fun j hj => ha j (by simp [varOccs, hj]))
          (by rw [ha i (by simp [varOccs]), hi])
    termination_by structural p => p
  theorem PatVals.congr {σ σ' : Subst} : ∀ {ps : List Term} {vs : List GroundTerm}, PatVals c σ ps vs →
      (∀ j ∈ varOccsList ps, σ'.lookup j = σ.lookup j) → PatVals c σ' ps vs
    | [], vs, h, _ => by cases h; exact .nil
    | p :: ps, vs, h, ha => by
      cases h with
      | cons h hs =>
        exact .cons (PatVal.congr h fun j hj => ha j (by simp [varOccsList, hj]))
          (PatVals.congr hs fun j hj => ha j (by simp [varOccsList, hj]))
    termination_by structural ps => ps
end

theorem loVars_of_empty {H : HPaths} (hH : H.isEmpty = true) (p : Term) : loVars H p = varOccs p := by
  cases p <;> simp [loVars, hH, varOccs]

theorem hiVars_of_empty {H : HPaths} (hH : H.isEmpty = true) (p : Term) : hiVars H p = [] := by
  cases p <;> simp [hiVars, hH]

theorem hiVals_of_empty {H : HPaths} (hH : H.isEmpty = true) (p : Term) (v : GroundTerm) :
    hiVals H p v = [] := by
  cases p <;> cases v <;> simp [hiVals, hH]

theorem nil_of_isEmpty {H : HPaths} (h : H.isEmpty = true) : H = [] := List.isEmpty_iff.mp h

/-- What matching at the other configuration needs: the high variables' keys, their values there
equal outside their high parts to their values here, and a match from any σ' with the low
variables' values and the high variables' new ones. -/
def Transfer (c : Semantics) (lo : GroundTerm → Prop) (σ : Subst) (hv : List (Nat × HPaths)) (hl : List Nat)
    (vals : List (Nat × GroundTerm)) (m : Subst → Prop) : Prop :=
  vals.map (·.1) = hv.map (·.1) ∧
  (∀ j w, (j, w) ∈ vals → ∃ w₁ Hq, σ.lookup j = some w₁ ∧ (j, Hq) ∈ hv ∧ EqOut c lo Hq w₁ w) ∧
  (∀ σ', (∀ j ∈ hl, σ'.lookup j = σ.lookup j) → (∀ j w, (j, w) ∈ vals → σ'.lookup j = some w) → m σ')

theorem transfer_empty {H : HPaths} (hH : H.isEmpty = true) (p : Term) {σ : Subst} {v₁ v₂ : GroundTerm}
    (hm : PatVal c σ p v₁) (he : EqOut c lo H v₁ v₂) :
    Transfer c lo σ (hiVars H p) (loVars H p) (hiVals H p v₂) (fun σ' => PatVal c σ' p v₂) := by
  have := he.eq_of_nil (nil_of_isEmpty hH); subst this
  rw [hiVars_of_empty hH, loVars_of_empty hH, hiVals_of_empty hH]
  exact ⟨rfl, fun _ _ h => (nomatch h), fun σ' ha _ => PatVal.congr hm ha⟩

mutual
  theorem transfer : ∀ (H : HPaths) (p : Term) {σ : Subst} {v₁ v₂ : GroundTerm},
      lhsOK c H p = true → PatVal c σ p v₁ → EqOut c lo H v₁ v₂ →
      Transfer c lo σ (hiVars H p) (loVars H p) (hiVals H p v₂) (fun σ' => PatVal c σ' p v₂)
    | H, .var j, σ, v₁, v₂, _, hm, he => by
      by_cases hH : H.isEmpty = true
      · exact transfer_empty hH _ hm he
      · have hH' : H.isEmpty = false := by simpa using hH
        cases hm with
        | var hj =>
          simp only [hiVars, loVars, hiVals, hH', Bool.false_eq_true, if_false]
          refine ⟨rfl, fun k w hk => ?_, fun σ' _ hv => .var (hv j v₂ (by simp))⟩
          simp only [List.mem_singleton, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          exact ⟨v₁, H, hj, by simp, he⟩
    | H, .app f ps, σ, v₁, v₂, hok, hm, he => by
      by_cases hH : H.isEmpty = true
      · exact transfer_empty hH _ hm he
      · have hH' : H.isEmpty = false := by simpa using hH
        simp only [lhsOK, hH', Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hok
        obtain ⟨⟨⟨hnil, hc⟩, hph⟩, hokl⟩ := hok
        have hnil' : [] ∉ H := by simpa using hnil
        cases hm with
        | hook hp _ _ => rw [hp] at hph; cases hph
        | coll hc' _ _ _ => rw [hc] at hc'; cases hc'
        | ovl hc' _ _ _ => rw [hc] at hc'; cases hc'
        | ctor _ hs =>
          obtain ⟨vs₂, rfl, hl, hr⟩ := he.ctor_inv hnil'
          simp only [hiVars, loVars, hiVals, hH', Bool.false_eq_true, if_false]
          obtain ⟨h1, h2, h3⟩ := transferL H 0 ps hokl hs hl (fun k a b ha hb => by simpa using hr k a b ha hb)
          exact ⟨h1, h2, fun σ' ha hv => .ctor hc (h3 σ' ha hv)⟩
    | H, .inj a b t, σ, v₁, v₂, hok, hm, he => by
      by_cases hH : H.isEmpty = true
      · exact transfer_empty hH _ hm he
      · simp [lhsOK, hH] at hok
    | H, .as t j, σ, v₁, v₂, hok, hm, he => by
      by_cases hH : H.isEmpty = true
      · exact transfer_empty hH _ hm he
      · simp [lhsOK, hH] at hok
    | H, .dv s l, σ, v₁, v₂, hok, hm, he => by
      by_cases hH : H.isEmpty = true
      · exact transfer_empty hH _ hm he
      · simp [lhsOK, hH] at hok
    termination_by structural _ p => p
  theorem transferL : ∀ (H : HPaths) (i : Nat) (ps : List Term) {σ : Subst} {vs₁ vs₂ : List GroundTerm},
      lhsOKL c H i ps = true → PatVals c σ ps vs₁ → vs₁.length = vs₂.length →
      (∀ k a b, vs₁[k]? = some a → vs₂[k]? = some b → EqOut c lo (subH H (i + k)) a b) →
      Transfer c lo σ (hiVarsL H i ps) (loVarsL H i ps) (hiValsL H i ps vs₂) (fun σ' => PatVals c σ' ps vs₂)
    | H, i, [], σ, vs₁, vs₂, _, hm, hl, _ => by
      cases hm
      cases vs₂ with
      | nil => exact ⟨rfl, fun _ _ h => (nomatch h), fun _ _ _ => PatVals.nil⟩
      | cons _ _ => cases hl
    | H, i, p :: ps, σ, vs₁, vs₂, hok, hm, hl, hr => by
      simp only [lhsOKL, Bool.and_eq_true] at hok
      cases hm with
      | cons h hs =>
        cases vs₂ with
        | nil => cases hl
        | cons v₂ vs₂ =>
          obtain ⟨a1, a2, a3⟩ := transfer (subH H i) p hok.1 h (by simpa using hr 0 _ v₂ (by simp) (by simp))
          obtain ⟨b1, b2, b3⟩ := transferL H (i + 1) ps hok.2 hs (by simpa using hl)
            (fun k a b ha hb => by simpa [Nat.add_assoc, Nat.add_comm 1 k] using hr (k + 1) a b ha hb)
          simp only [hiVarsL, loVarsL, hiValsL]
          refine ⟨by simp only [List.map_append, a1, b1], fun j w hj => ?_, fun σ' ha hv => ?_⟩
          · rcases List.mem_append.mp hj with hj | hj
            · obtain ⟨w₁, Hq, h1, h2, h3⟩ := a2 j w hj
              exact ⟨w₁, Hq, h1, List.mem_append_left _ h2, h3⟩
            · obtain ⟨w₁, Hq, h1, h2, h3⟩ := b2 j w hj
              exact ⟨w₁, Hq, h1, List.mem_append_right _ h2, h3⟩
          · exact .cons (a3 σ' (fun j hj => ha j (List.mem_append_left _ hj))
                (fun j w hj => hv j w (List.mem_append_left _ hj)))
              (b3 σ' (fun j hj => ha j (List.mem_append_right _ hj))
                (fun j w hj => hv j w (List.mem_append_right _ hj)))
    termination_by structural _ _ ps => ps
end

/-! ## Evaluation of the right-hand side -/

/-- Both undefined, or both defined and related. -/
inductive OptRel {α : Type} (R : α → α → Prop) : Option α → Option α → Prop where
  | none : OptRel R none none
  | some {a b : α} (h : R a b) : OptRel R (some a) (some b)

theorem optRel_cases {α : Type} {R : α → α → Prop} {a b : Option α} (h : OptRel R a b) :
    (a = none ∧ b = none) ∨ ∃ x y, a = some x ∧ b = some y ∧ R x y := by
  cases h with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some h => exact Or.inr ⟨_, _, rfl, rfl, h⟩

/-- Results related outside the high positions below each argument. -/
inductive RelL (c : Semantics) (lo : GroundTerm → Prop) (H : HPaths) : Nat → List (Option GroundTerm) → List (Option GroundTerm) → Prop where
  | nil {i : Nat} : RelL c lo H i [] []
  | cons {i : Nat} {r₁ r₂ : Option GroundTerm} {rs₁ rs₂ : List (Option GroundTerm)}
      (h : OptRel (EqOut c lo (subH H i)) r₁ r₂) (hs : RelL c lo H (i + 1) rs₁ rs₂) : RelL c lo H i (r₁ :: rs₁) (r₂ :: rs₂)

theorem allSome_rel {H : HPaths} : ∀ {i : Nat} {rs₁ rs₂ : List (Option GroundTerm)}, RelL c lo H i rs₁ rs₂ →
    OptRel (fun vs₁ vs₂ => vs₁.length = vs₂.length ∧
      ∀ k a b, vs₁[k]? = some a → vs₂[k]? = some b → EqOut c lo (subH H (i + k)) a b) (allSome rs₁) (allSome rs₂)
  | _, _, _, .nil => .some ⟨rfl, fun _ _ _ h => nomatch h⟩
  | i, _, _, .cons h hs => by
    have ih := allSome_rel hs
    cases h with
    | none => exact .none
    | some hab =>
      simp only [allSome, Option.bind_some]
      rcases optRel_cases ih with ⟨h1, h2⟩ | ⟨x, y, h1, h2, h'⟩
      · rw [h1, h2]; exact .none
      · rw [h1, h2]
        refine .some ⟨by simp [h'.1], fun k a b ha hb => ?_⟩
        cases k with
        | zero => simp at ha hb; subst ha; subst hb; exact hab
        | succ k =>
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using h'.2 k a b (by simpa using ha) (by simpa using hb)

/-- σ₂ has σ's values at the low variables and related ones at the high variables. -/
def SubstRel (c : Semantics) (lo : GroundTerm → Prop) (hv : List (Nat × HPaths)) (σ σ₂ : Subst) : Prop :=
  (∀ j, ¬ (hv.any (·.1 == j)) = true → σ₂.lookup j = σ.lookup j) ∧
  ∀ j Hq, (j, Hq) ∈ hv → ∃ w₁ w₂, σ.lookup j = some w₁ ∧ σ₂.lookup j = some w₂ ∧ EqOut c lo Hq w₁ w₂

theorem not_readsHigh {hv : List (Nat × HPaths)} {t : Term} (h : readsHigh hv t = false) :
    ∀ j ∈ varOccs t, ¬ (hv.any (·.1 == j)) = true := by
  intro j hj hh
  have : readsHigh hv t = true := List.any_eq_true.mpr ⟨j, hj, hh⟩
  rw [this] at h; cases h

theorem hook_mapUpdate_any (w x y : GroundTerm) :
    hook mapUpdate [w, x, y] =
      some (match w with | .map _ m => some (.map Srt.map (insertE x y m)) | _ => none) := by
  cases w <;> rfl

/-- `M[K <- V]` on values: undefined if K or V is, or M is not a map. -/
def updRes (w : GroundTerm) : Option GroundTerm → Option GroundTerm → Option GroundTerm
  | some x, some y => match w with | .map _ m => some (.map Srt.map (insertE x y m)) | _ => none
  | _, _ => none

/-- The update case of the right-hand side (`updOK`): `M[K <- V]` evaluates at both
substitutions, to maps related at the keyed position. -/
theorem upd_transfer {hv : List (Nat × HPaths)} {σ σ₂ : Subst} (hs : SubstRel c lo hv σ σ₂)
    {H : HPaths} {f : Sym} {ts : List Term} {r₁ : Option GroundTerm}
    (hup : updOK c hv H f ts = true) (he : EvalTerm c σ (.app f ts) r₁) :
    ∃ r₂, EvalTerm c σ₂ (.app f ts) r₂ ∧ OptRel (EqOut c lo H) r₁ r₂ := by
  unfold updOK at hup
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hup
  obtain ⟨⟨⟨hf, hnc⟩, hH⟩, hm⟩ := hup
  subst hf; subst hH
  match ts, hm with
  | [.var j, a, b], hm =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨⟨k, Hq⟩, hmem, hk, hq⟩, ha⟩, hb⟩ := hm
    simp only at hk hq; subst hk; subst hq
    obtain ⟨w₁, w₂, h1, h2, h3⟩ := hs.2 _ _ hmem
    have hhk : isHook mapUpdate = true := rfl
    have hcg : ∀ t, readsHigh hv t = false → ∀ {r}, EvalTerm c σ t r → EvalTerm c σ₂ t r :=
      fun t ht r h => EvalTerm.congr h fun i hi => (hs.1 i (not_readsHigh ht i hi)).symm
    cases he with
    | ctor h _ => rw [hnc] at h; cases h
    | param _ hk _ _ _ => rw [hhk] at hk; cases hk
    | call _ hk _ _ _ _ => rw [hhk] at hk; cases hk
    | callUndef _ hk _ _ _ => rw [hhk] at hk; cases hk
    | ovl _ ho _ => have hk := (c.isOvl_parts ho).2.1; rw [hhk] at hk; cases hk
    | ovlFn _ ho => have hk := (c.isOvl_parts ho).2.1; rw [hhk] at hk; cases hk
    | hook _ _ hts hh hund =>
      obtain ⟨r0, rs', rfl, hv0, hts'⟩ := EvalTerms.cons_inv hts
      obtain ⟨ra, rs'', rfl, hva, hts''⟩ := EvalTerms.cons_inv hts'
      obtain ⟨rb, rs''', rfl, hvb, hts'''⟩ := EvalTerms.cons_inv hts''
      cases EvalTerms.nil_inv hts'''
      have := EvalTerm.var_inv hv0; subst this
      have ha₂ := hcg a ha hva
      have hb₂ := hcg b hb hvb
      have hv₂ : EvalTerm c σ₂ (.var k) (some w₂) := h2 ▸ .var
      let r₂ : Option GroundTerm := updRes w₂ ra rb
      have hev₂ : EvalTerm c σ₂ (.app mapUpdate [.var k, a, b]) r₂ := by
        refine .hook hnc hhk (.cons hv₂ (.cons ha₂ (.cons hb₂ .nil))) (fun vs hvs => ?_) (fun hn => ?_)
        · cases ra <;> cases rb <;> simp [allSome] at hvs
          subst hvs; rw [Semantics.hookRes_of_notKey (f := mapUpdate) (silentKey_of_mem rfl), hook_mapUpdate_any]; rfl
        · cases ra <;> cases rb <;> simp [allSome] at hn ⊢ <;> rfl
      refine ⟨r₂, hev₂, ?_⟩
      cases ra with
      | none => rw [hund (by simp [allSome, h1])]; exact .none
      | some x =>
        cases rb with
        | none => rw [hund (by simp [allSome, h1])]; exact .none
        | some y =>
          have hr₁ := hh [w₁, x, y] (by simp [allSome, h1])
          rw [Semantics.hookRes_of_notKey (f := mapUpdate) (silentKey_of_mem rfl), hook_mapUpdate_any] at hr₁
          cases hr₁
          cases h3 with
          | high h _ => simp at h
          | same => cases w₁ <;> first | exact .none | exact .some .same
          | ctor _ _ => exact .none
          | keyed h hk => exact .some (.keyed (by simp) (hk.insert x y))

mutual
  theorem rhs_transfer {hv : List (Nat × HPaths)} {σ σ₂ : Subst} (hs : SubstRel c lo hv σ σ₂) :
      ∀ (H : HPaths) (t : Term) {r₁ : Option GroundTerm}, rhsOK c hv H t = true → EvalTerm c σ t r₁ →
      ∃ r₂, EvalTerm c σ₂ t r₂ ∧ OptRel (EqOut c lo H) r₁ r₂
    | H, t, r₁, hok, he => by
      by_cases hrd : readsHigh hv t = true
      · match t, hok, he with
        | .var j, hok, he =>
          simp only [rhsOK, hrd, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
            beq_iff_eq] at hok
          obtain ⟨⟨k, Hq⟩, hm, rfl, rfl⟩ := hok
          obtain ⟨w₁, w₂, h1, h2, h3⟩ := hs.2 k Hq hm
          have := EvalTerm.var_inv he; subst this
          exact ⟨_, .var, by rw [h1, h2]; exact .some h3⟩
        | .app f ts, hok, he =>
          simp only [rhsOK, hrd, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at hok
          rcases hok with ⟨hc, hokl⟩ | hup
          · obtain ⟨rs₁, hts, rfl⟩ := EvalTerm.ctor_inv hc he
            obtain ⟨rs₂, hts₂, hrel⟩ := rhs_transferL hs H 0 ts hokl hts
            refine ⟨_, .ctor hc hts₂, ?_⟩
            rcases optRel_cases (allSome_rel hrel) with ⟨h1, h2⟩ | ⟨x, y, h1, h2, h⟩
            · rw [h1, h2]; exact .none
            · rw [h1, h2]; exact .some (.ctor h.1 fun k a b ha hb => by simpa using h.2 k a b ha hb)
          · exact upd_transfer hs hup he
        | .inj .., hok, _ => simp [rhsOK, hrd] at hok
        | .as .., hok, _ => simp [rhsOK, hrd] at hok
        | .dv .., hok, _ => simp [rhsOK, hrd] at hok
      · have hn := not_readsHigh (by simpa using hrd)
        refine ⟨r₁, EvalTerm.congr he fun j hj => (hs.1 j (hn j hj)).symm, ?_⟩
        cases r₁ with
        | none => exact .none
        | some _ => exact .some .same
    termination_by structural _ t => t
  theorem rhs_transferL {hv : List (Nat × HPaths)} {σ σ₂ : Subst} (hs : SubstRel c lo hv σ σ₂) :
      ∀ (H : HPaths) (i : Nat) (ts : List Term) {rs₁ : List (Option GroundTerm)}, rhsOKL c hv H i ts = true →
      EvalTerms c σ ts rs₁ → ∃ rs₂, EvalTerms c σ₂ ts rs₂ ∧ RelL c lo H i rs₁ rs₂
    | _, _, [], _, _, he => by cases he; exact ⟨[], .nil, .nil⟩
    | H, i, t :: ts, _, hok, he => by
      simp only [rhsOKL, Bool.and_eq_true] at hok
      cases he with
      | cons h hs' =>
        obtain ⟨r₂, h1, h2⟩ := rhs_transfer hs (subH H i) t hok.1 h
        obtain ⟨rs₂, h3, h4⟩ := rhs_transferL hs H (i + 1) ts hok.2 hs'
        exact ⟨r₂ :: rs₂, .cons h1 h3, .cons h2 h4⟩
    termination_by structural _ _ ts => ts
end

/-! ## The rule's steps at the other configuration -/

/-- The relation: equal outside H. -/
def LowEq (c : Semantics) (lo : GroundTerm → Prop) (H : HPaths) (x₁ x₂ : Config c) : Prop := EqOut c lo H x₁.val x₂.val

/-- A configuration with no successor. -/
def Stuck (c : Semantics) (y : Config c) : Prop := ∀ z, ¬ Step c y z

/-- A rule `appOK` accepts has a left side that binds every variable. -/
theorem appOK_plain {H : HPaths} {r : Rule} (h : appOK c H r = true) :
    binds r.vars.length (varOccs r.lhs) = true := by
  simp only [appOK, Bool.and_eq_true] at h
  exact h.2

/-- No variable of the `pre` of a rule `appOK` accepts is one of its high variables. -/
theorem appOK_pre {H : HPaths} {r : Rule} (h : appOK c H r = true) :
    ∀ j ∈ varOccsCond r.vars.length r.pre, j ∉ (hiVars H r.lhs).map (·.1) := by
  simp only [appOK, Bool.and_eq_true] at h
  intro j hj hm
  have : (varOccsCond r.vars.length r.pre).any ((hiVars H r.lhs).map (·.1)).contains = true :=
    List.any_eq_true.mpr ⟨j, hj, List.contains_iff_mem.mpr hm⟩
  have h' := h.1.2
  rw [this] at h'; cases h'

/-- No variable of the `ensures` or the `post` of a rule `ensOK` accepts is one of its high
variables. -/
theorem ensOK_parts {H : HPaths} {r : Rule} (h : ensOK H r = true) :
    (∀ t, r.ens = some t → ∀ j ∈ varOccs t, j ∉ (hiVars H r.lhs).map (·.1)) ∧
    ∀ j ∈ varOccsCond r.vars.length r.post, j ∉ (hiVars H r.lhs).map (·.1) := by
  unfold ensOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨he, hp⟩ := h
  refine ⟨fun t ht j hj hm => ?_, fun j hj hm => ?_⟩
  · rw [ht] at he
    have : (varOccs t).any ((hiVars H r.lhs).map (·.1)).contains = true :=
      List.any_eq_true.mpr ⟨j, hj, List.contains_iff_mem.mpr hm⟩
    simp only [this, Bool.not_true] at he; cases he
  · have : (varOccsCond r.vars.length r.post).any ((hiVars H r.lhs).map (·.1)).contains = true :=
      List.any_eq_true.mpr ⟨j, hj, List.contains_iff_mem.mpr hm⟩
    simp only [this, Bool.not_true] at hp; cases hp

theorem appOK_parts {H : HPaths} {r : Rule} (h : appOK c H r = true) :
    lhsOK c H r.lhs = true ∧ nodupB ((hiVars H r.lhs).map (·.1)) = true ∧
    (∀ j ∈ loVars H r.lhs, j ∉ (hiVars H r.lhs).map (·.1)) ∧
    (∀ t, r.req = some t → ∀ j ∈ varOccs t, j ∉ (hiVars H r.lhs).map (·.1)) ∧ c.ovls = [] ∧
    ∀ k ∈ c.params, k.raw = false := by
  simp only [appOK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩ := h
  refine ⟨h1, h2, fun j hj hm => ?_, fun t ht j hj hm => ?_, h5,
    fun k hk => by simpa using List.any_eq_false.mp h6 k hk⟩
  · have : (loVars H r.lhs).any ((hiVars H r.lhs).map (·.1)).contains = true :=
      List.any_eq_true.mpr ⟨j, hj, List.contains_iff_mem.mpr hm⟩
    rw [this] at h3; cases h3
  · rw [ht] at h4
    simp only [Bool.not_eq_true'] at h4
    have : (varOccs t).any ((hiVars H r.lhs).map (·.1)).contains = true :=
      List.any_eq_true.mpr ⟨j, hj, List.contains_iff_mem.mpr hm⟩
    rw [this] at h4; cases h4

/-- A rule whose applicability does not read H matches the other configuration under the high
variables' values there (`hiVals`) put before σ, a well-sorted substitution, and its `requires`
has the same result under both. -/
theorem match_other {H : HPaths} {r : Rule} (hap : appOK c H r = true) {σ : Subst} {x₁ x₂ : GroundTerm}
    (hσ : c.WellSorted r.vars σ) (hm : PatVal c σ r.lhs x₁) (he : EqOut c lo H x₁ x₂) :
    let σ₂ := hiVals H r.lhs x₂ ++ σ
    c.WellSorted r.vars σ₂ ∧ PatVal c σ₂ r.lhs x₂ ∧
    (∀ t, r.req = some t → ∀ j ∈ varOccs t, σ₂.lookup j = σ.lookup j) ∧
    SubstRel c lo (hiVars H r.lhs) σ σ₂ := by
  obtain ⟨hl, hn, hlo, hrq, hno, hr⟩ := appOK_parts hap
  obtain ⟨t1, t2, t3⟩ := transfer H r.lhs hl hm he
  have hn' : nodupB ((hiVals H r.lhs x₂).map (·.1)) = true := by rw [t1]; exact hn
  have hmem : ∀ j w, (j, w) ∈ hiVals H r.lhs x₂ → (hiVals H r.lhs x₂ ++ σ).lookup j = some w :=
    fun j w h => lookup_append_of_mem hn' h
  have hnot : ∀ j, j ∉ (hiVars H r.lhs).map (·.1) → (hiVals H r.lhs x₂ ++ σ).lookup j = σ.lookup j :=
    fun j h => lookup_append_of_not_mem (by rw [t1]; exact h)
  refine ⟨fun i s hs => ?_, t3 _ (fun j hj => hnot j (hlo j hj)) hmem,
    fun t ht j hj => hnot j (hrq t ht j hj), fun j hj => hnot j ?_, fun j Hq hjm => ?_⟩
  · by_cases hi : i ∈ (hiVars H r.lhs).map (·.1)
    · rw [← t1] at hi
      obtain ⟨⟨k, w⟩, hkw, rfl⟩ := List.mem_map.mp hi
      obtain ⟨w₁, _, h1, _, h3⟩ := t2 _ w hkw
      obtain ⟨v, hv, hsv⟩ := hσ _ s hs
      rw [h1] at hv; cases hv
      exact ⟨w, hmem _ w hkw, by rw [← h3.sortOf_eq hno hr, hsv]⟩
    · rw [hnot i hi]; exact hσ i s hs
  · intro hm'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm'
    exact hj (List.any_eq_true.mpr ⟨p, hp, by simp⟩)
  · have : j ∈ (hiVals H r.lhs x₂).map (·.1) := by
      rw [t1]; exact List.mem_map_of_mem (f := (·.1)) hjm
    obtain ⟨⟨k, w⟩, hkw, rfl⟩ := List.mem_map.mp this
    obtain ⟨w₁, Hq', h1, h2, h3⟩ := t2 _ w hkw
    have := mem_unique hn h2 hjm; subst this
    exact ⟨w₁, w, h1, hmem _ w hkw, h3⟩

/-- Off the rule's high variables, the substitution of `match_other` is σ. -/
theorem match_other_off {H : HPaths} {r : Rule} (hap : appOK c H r = true) {σ : Subst} {x₁ x₂ : GroundTerm}
    (hm : PatVal c σ r.lhs x₁) (he : EqOut c lo H x₁ x₂) :
    ∀ j, j ∉ (hiVars H r.lhs).map (·.1) → (hiVals H r.lhs x₂ ++ σ).lookup j = σ.lookup j := by
  obtain ⟨hl, -, -, -, -, -⟩ := appOK_parts hap
  obtain ⟨t1, -, -⟩ := transfer H r.lhs hl hm he
  exact fun j h => lookup_append_of_not_mem (by rw [t1]; exact h)

/-- A rule whose applicability does not read H, blocked at one configuration, is blocked at
every configuration equal to it outside H. -/
theorem notApplies_other {H : HPaths} {r : Rule} (hap : appOK c H r = true) {x₁ x₂ : GroundTerm}
    (he : EqOut c lo H x₁ x₂) (h : NotApplies c r x₁) : NotApplies c r x₂ := by
  intro σ hσ hm
  obtain ⟨hσ', hm', hrq, _⟩ := match_other hap (Rule.wellSorted_of_at (appOK_plain hap) hσ) hm he.symm
  have hoff := match_other_off hap hm he.symm
  cases h _ (hσ'.at _) hm' with
  | intro ht he' hv => exact .intro ht (EvalTerm.congr he' (hrq _ ht)) hv
  | pre hp => exact .pre (hp.congr_NI fun j hj => hoff j (appOK_pre hap j hj))

/-- **The condition is sound, where any `Inv` holds**: a rule that satisfies it makes matched steps
from configurations equal outside H, into configurations equal outside H. The proof reads no
`Inv`: the condition holds at every pair of configurations. -/
theorem cellsCond_sound_on {H : HPaths} (Inv : Config c → Prop) :
    ∀ r ∈ c.rules, cellsCond c H r = true → RuleUnwindsOn c Inv (LowEq c lo H) r := by
  intro r mem hc x₁ x₂ y₁ _ _ hR hb
  simp only [cellsCond, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at hc
  obtain ⟨⟨⟨hap, hrhs⟩, hens⟩, hlow⟩ := hc
  obtain ⟨σ, hσ, hm, hreq, hpre, hev, hen, hpost, hprio⟩ := hb
  obtain ⟨hσ₂, hm₂, hrq, hsr⟩ := match_other hap hσ hm hR
  have hoff := match_other_off hap hm hR
  obtain ⟨r₂, hev₂, hrel⟩ := rhs_transfer hsr H r.rhs hrhs hev
  rcases optRel_cases hrel with ⟨h1, _⟩ | ⟨y₁', y₂, h1, rfl, hy⟩
  · cases h1
  · cases h1
    have hs₂ : c.sortOf y₂ = some topCellSort := by
      rw [← hy.sortOf_eq (appOK_parts hap).2.2.2.2.1 (appOK_parts hap).2.2.2.2.2]; exact y₁.property
    refine Or.inr ⟨⟨y₂, hs₂⟩, step_of_stepBy_pp mem ⟨_, hσ₂, hm₂, fun t ht => ?_,
      hpre.congr_NI fun j hj => (hoff j (appOK_pre hap j hj)).symm, hev₂, fun t ht => ?_,
      hpost.congr_NI fun j hj => (hoff j ((ensOK_parts hens).2 j hj)).symm, fun r' hr' hlt => ?_⟩, hy⟩
    · exact EvalTerm.congr (hreq t ht) fun j hj => (hrq t ht j hj).symm
    · exact EvalTerm.congr (hen t ht) fun j hj => (hoff j ((ensOK_parts hens).1 t ht j hj)).symm
    · have hap' : appOK c H r' = true := by
        rcases hlow r' hr' with h | h
        · exact absurd hlt (Nat.not_lt.mpr h)
        · exact h
      exact notApplies_other hap' hR (hprio r' hr' hlt)

/-- **The condition is sound**: `cellsCond_sound_on` with `Inv = fun _ => True`. -/
theorem cellsCond_sound {H : HPaths} : ∀ r ∈ c.rules, cellsCond c H r = true → RuleUnwinds c (LowEq c lo H) r :=
  fun r mem hc => (cellsCond_sound_on (fun _ => True) r mem hc).of_true

theorem lowEq_symm {H : HPaths} (a b : Config c) (h : LowEq c lo H a b) : LowEq c lo H b a := EqOut.symm h

/-! ## The generic theorem

The kind (`cellsKindOn`, `cellsKind`): indexed by the rules, the obligation at a rule its unwinding
(where `Inv` holds), the goal noninterference; `cellsCond` its decider. -/

/-- Equal outside H, as a lockstep unwinding where `Inv` holds, from the unwinding condition. -/
theorem unwindingOn_of_unwinds {Init Inv : Config c → Prop} {H : HPaths} (hl : UnwindsOn c Inv (LowEq c lo H)) :
    UnwindingOn c Init Inv (LowEq c lo H) (Stuck c) (LowEq c lo H) (LowEq c lo H) :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h _ _ => h, fun _ _ hs z => hs z, hl, UnwindsOn.flip_of_symm lowEq_symm hl⟩

/-- Equal outside H, as a lockstep unwinding: the rules not listed satisfy the condition (one
decision), and every listed rule is an obligation proved. -/
theorem unwinding_cells {H : HPaths} {obl : List Nat} (h : allExcept (cellsCond c H) obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleUnwinds c (LowEq c lo H) r) :
    Unwinding c (LowEq c lo H) (Stuck c) (LowEq c lo H) (LowEq c lo H) :=
  have hl := unwinds_of (fun r mem hc => cellsCond_sound r mem hc) h ho
  ⟨fun _ _ h => h, fun _ _ h _ _ => h, fun _ hs z => hs z, hl, Unwinds.flip_of_symm lowEq_symm hl⟩

/-- Equal outside H, as a lockstep unwinding where `Inv` holds: the rules not listed satisfy the
condition (one decision), and every listed rule is an obligation proved where `Inv` holds. -/
theorem unwinding_cells_on {Init Inv : Config c → Prop} {H : HPaths} {obl : List Nat}
    (h : allExcept (cellsCond c H) obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleUnwindsOn c Inv (LowEq c lo H) r) :
    UnwindingOn c Init Inv (LowEq c lo H) (Stuck c) (LowEq c lo H) (LowEq c lo H) :=
  unwindingOn_of_unwinds (unwindsOn_of (fun r mem hc => cellsCond_sound_on Inv r mem hc) h ho)

/-- Every rule's unwinding where `Inv` holds gives noninterference from the configurations where
`Init` holds, given the invariant and determinism where it holds. -/
theorem tini_cells_of_rules_on {Init Inv : Config c → Prop} {H : HPaths} (hinv : Invariant c Init Inv)
    (hdet : DeterministicOn c Inv) (h : ∀ r ∈ c.rules, RuleUnwindsOn c Inv (LowEq c lo H) r) :
    TINIOn c Init (LowEq c lo H) (Stuck c) (LowEq c lo H) :=
  tini_of_unwinding_on hinv hdet (unwindingOn_of_unwinds (unwindsOn_of_rules h))

/-- Every rule's unwinding gives noninterference, given determinism. -/
theorem tini_cells_of_rules {H : HPaths} (hdet : Deterministic c)
    (h : ∀ r ∈ c.rules, RuleUnwinds c (LowEq c lo H) r) : TINI c (LowEq c lo H) (Stuck c) (LowEq c lo H) :=
  tiniOn_true_iff.mp (tini_cells_of_rules_on invariant_true (hdet.on _) fun r hr => (h r hr).on _)

/-- **The noninterference kind for secrets in whole cells, relative to an invariant**: indexed by
the rules, the obligation at a rule its unwinding where `Inv` holds, the goal noninterference from
the configurations where `Init` holds. -/
@[reducible] def cellsKindOn (c : Semantics) (lo : GroundTerm → Prop) (H : HPaths) {Init Inv : Config c → Prop}
    (hinv : Invariant c Init Inv) (hdet : DeterministicOn c Inv) : Kind :=
  Kind.ofList c.rules (RuleUnwindsOn c Inv (LowEq c lo H)) (TINIOn c Init (LowEq c lo H) (Stuck c) (LowEq c lo H))
    (tini_cells_of_rules_on hinv hdet)

/-- **The noninterference kind for secrets in whole cells**: indexed by the rules, the obligation at
a rule its unwinding, the goal noninterference. -/
@[reducible] def cellsKind (c : Semantics) (lo : GroundTerm → Prop) (H : HPaths) (hdet : Deterministic c) : Kind :=
  Kind.ofList c.rules (RuleUnwinds c (LowEq c lo H)) (TINI c (LowEq c lo H) (Stuck c) (LowEq c lo H))
    (tini_cells_of_rules hdet)

/-- **Noninterference for secrets in whole cells, relative to an invariant**, with named
obligations: from two configurations where `Init` holds, equal outside H, two runs that both stop
end equal outside H; given an invariant `Inv` of the configurations where `Init` holds,
determinism where `Inv` holds, and the listed rules' unwinding where `Inv` holds. -/
theorem tini_cells_on {Init Inv : Config c → Prop} {H : HPaths} {obl : List Nat}
    (hinv : Invariant c Init Inv) (hdet : DeterministicOn c Inv)
    (h : allExcept (cellsCond c H) obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleUnwindsOn c Inv (LowEq c lo H) r) :
    TINIOn c Init (LowEq c lo H) (Stuck c) (LowEq c lo H) :=
  Kind.of_decided (cellsKindOn c lo H hinv hdet) (Kind.listDecider (cellsCond c H) (cellsCond_sound_on Inv))
    obl (decides_of_allExcept h) ho

/-- **Noninterference for secrets in whole cells**, with named obligations: from two
configurations equal outside H, two runs that both stop end equal outside H. -/
theorem tini_cells_of {H : HPaths} {obl : List Nat} (hdet : Deterministic c)
    (h : allExcept (cellsCond c H) obl 0 c.rules = true)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleUnwinds c (LowEq c lo H) r) :
    TINI c (LowEq c lo H) (Stuck c) (LowEq c lo H) :=
  Kind.of_decided (cellsKind c lo H hdet) (Kind.listDecider (cellsCond c H) cellsCond_sound)
    obl (decides_of_allExcept h) ho

/-- **Noninterference for secrets in whole cells**: every rule satisfies the condition. -/
theorem tini_cells {H : HPaths} (hdet : Deterministic c) (h : allExcept (cellsCond c H) [] 0 c.rules = true) :
    TINI c (LowEq c lo H) (Stuck c) (LowEq c lo H) :=
  tini_cells_of hdet h fun _ h => nomatch h

/-! ## Every interpretation of the parameters

The policy reads the presentation's cell tree, and the condition the rules' syntax, never `hooks`:
each equation is `rfl` for a variable `c`, checked by the kernel (`kernel_rfl`, Params.lean). So one
decision on the data gives noninterference for every interpretation H of the parameters. -/

kernel_rfl appOK_withHooks : ∀ (c : Semantics) (H : HookParams) (hp : HPaths) (r : Rule),
  appOK (c.withHooks H) hp r = appOK c hp r
kernel_rfl rhsOK_withHooks : ∀ (c : Semantics) (H : HookParams) (hv : List (Nat × HPaths)) (hp : HPaths) (t : Term),
  rhsOK (c.withHooks H) hv hp t = rhsOK c hv hp t
kernel_rfl cellsCond_withHooks : ∀ (c : Semantics) (H : HookParams) (hp : HPaths) (r : Rule),
  cellsCond (c.withHooks H) hp r = cellsCond c hp r

/-- **The noninterference kind relative to an invariant, for an interpretation H of the
parameters**: `cellsKindOn (c.withHooks H)` indexed by the data's rules (the same list). -/
@[reducible] def cellsKindOnAll (c : Semantics) (lo : GroundTerm → Prop) (high : HPaths) (H : HookParams)
    {Init Inv : Config (c.withHooks H) → Prop} (hinv : Invariant (c.withHooks H) Init Inv)
    (hdet : DeterministicOn (c.withHooks H) Inv) : Kind :=
  Kind.ofList c.rules (RuleUnwindsOn (c.withHooks H) Inv (LowEq (c.withHooks H) lo high))
    (TINIOn (c.withHooks H) Init (LowEq (c.withHooks H) lo high) (Stuck (c.withHooks H)) (LowEq (c.withHooks H) lo high))
    (tini_cells_of_rules_on (c := c.withHooks H) hinv hdet)

/-- **The noninterference kind, for an interpretation H of the parameters**: `cellsKind (c.withHooks H)`
indexed by the data's rules. -/
@[reducible] def cellsKindAll (c : Semantics) (lo : GroundTerm → Prop) (high : HPaths) (H : HookParams)
    (hdet : Deterministic (c.withHooks H)) : Kind :=
  Kind.ofList c.rules (RuleUnwinds (c.withHooks H) (LowEq (c.withHooks H) lo high))
    (TINI (c.withHooks H) (LowEq (c.withHooks H) lo high) (Stuck (c.withHooks H)) (LowEq (c.withHooks H) lo high))
    (tini_cells_of_rules (c := c.withHooks H) hdet)

/-- The decider of `cellsKindOnAll`: the condition on the data, which does not read `hooks`. -/
def cellsDeciderOnAll (c : Semantics) (lo : GroundTerm → Prop) (high : HPaths) (H : HookParams)
    {Init Inv : Config (c.withHooks H) → Prop} {hinv : Invariant (c.withHooks H) Init Inv}
    {hdet : DeterministicOn (c.withHooks H) Inv} : (cellsKindOnAll c lo high H hinv hdet).Decider :=
  Kind.listDecider (cellsCond c high) fun r hr h => cellsCond_sound_on Inv r hr ((cellsCond_withHooks c H high r).trans h)

/-- The decider of `cellsKindAll`: the condition on the data, which does not read `hooks`. -/
def cellsDeciderAll (c : Semantics) (lo : GroundTerm → Prop) (high : HPaths) (H : HookParams)
    {hdet : Deterministic (c.withHooks H)} : (cellsKindAll c lo high H hdet).Decider :=
  Kind.listDecider (cellsCond c high) fun r hr h => cellsCond_sound r hr ((cellsCond_withHooks c H high r).trans h)

/-- **Noninterference for secrets in whole cells relative to an invariant, for every
interpretation of the parameters**, with named obligations: the condition decided once on the
data, an invariant `Inv` under H of the configurations where `Init` holds, determinism under H
where `Inv` holds, and the listed rules' unwinding under H where `Inv` holds give, from two
configurations of `c.withHooks H` where `Init` holds, equal outside `high`, that two runs that both
stop end equal outside `high`. -/
theorem tini_cells_on_all {high : HPaths} {obl : List Nat} (h : allExcept (cellsCond c high) obl 0 c.rules = true)
    (H : HookParams) {Init Inv : Config (c.withHooks H) → Prop} (hinv : Invariant (c.withHooks H) Init Inv)
    (hdet : DeterministicOn (c.withHooks H) Inv)
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r →
      RuleUnwindsOn (c.withHooks H) Inv (LowEq (c.withHooks H) lo high) r) :
    TINIOn (c.withHooks H) Init (LowEq (c.withHooks H) lo high) (Stuck (c.withHooks H))
      (LowEq (c.withHooks H) lo high) :=
  Kind.of_decided (cellsKindOnAll c lo high H hinv hdet) (cellsDeciderOnAll c lo high H) obl (decides_of_allExcept h) ho

/-- **Noninterference for secrets in whole cells, for every interpretation of the parameters**,
with named obligations: the condition decided once on the data, determinism and the listed rules'
unwinding under H give, from two configurations of `c.withHooks H` equal outside `high`, that two
runs that both stop end equal outside `high`. -/
theorem tini_cells_of_all {high : HPaths} {obl : List Nat} (h : allExcept (cellsCond c high) obl 0 c.rules = true)
    (H : HookParams) (hdet : Deterministic (c.withHooks H))
    (ho : ∀ i ∈ obl, ∀ r, c.rules[i]? = some r → RuleUnwinds (c.withHooks H) (LowEq (c.withHooks H) lo high) r) :
    TINI (c.withHooks H) (LowEq (c.withHooks H) lo high) (Stuck (c.withHooks H)) (LowEq (c.withHooks H) lo high) :=
  Kind.of_decided (cellsKindAll c lo high H hdet) (cellsDeciderAll c lo high H) obl (decides_of_allExcept h) ho

end KCore.NI
