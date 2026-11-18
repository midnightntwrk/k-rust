/-
  KCore. Negated premises in a model of `Γ c`: a clause that fails at arguments, or a rule that
  does not apply to a configuration, in the kernel's sense (`Fails`, `NotApplies`), has an empty
  `exclusion` / `applies` pattern there.

  The proof reads `Γ` downwards from a value. If the element of a value `w` lies in the
  translation of a plain pattern at a valuation of its variables in their sorts, then the
  pattern denotes `w` under the substitution that gives each variable the value whose element
  the valuation gives it (`patVal_back`). That reading takes, for a value of a constructor sort,
  the constructors' axioms: functionality and injectivity (Cons-Fun, Cons-Inj), distinctness of
  two generators (Cons-Dist, Cons-Dist′ for injections from sorts with a common lower bound) and
  the coherence of injections (Cons-Coh). It also takes that distinct values of one sort are
  distinct elements (`values_apart`): for Int, Bool, the token and byte sorts and the collection
  sorts this is `Γ`'s distinctness axiom; for K and the sorts below KItem it follows from the
  graph of `_==K_` and the distinctness of `true` and `false`. A `requires` that evaluates to
  something other than `true` makes `⌈req = true⌉` empty by the same distinctness of Bool.
-/
import KcoreSpec.FaithfulStep
import KcoreSpec.OvlLawsFn

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-! ## Lists of elements -/

/-- Two lists related pointwise. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} (h : R a b) (hs : All2 R as bs) :
      All2 R (a :: as) (b :: bs)

theorem All2.length {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, All2 R as bs →
    as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [hs.length]

theorem All2.get {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, All2 R as bs →
    ∀ {i : Nat} {a : α} {b : β}, as[i]? = some a → bs[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h hs, 0, _, _, ha, hb => by simp at ha hb; subst ha; subst hb; exact h
  | _, _, .cons _ hs, i + 1, _, _, ha, hb => hs.get (by simpa using ha) (by simpa using hb)

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- `m` is in the application of the element `a` to the elements `bs`, left to right. -/
def AppE (I : Interpretation KoreAML.Sym M) : M → List M → M → Prop
  | a, [], m => m = a
  | a, b :: bs, m => ∃ a', I.evalApp a b a' ∧ AppE I a' bs m

theorem interp_appList {e : Valuation M} : ∀ (h : KoreAML.P) (φs : List KoreAML.P) (m : M),
    (KoreAML.appList h φs).interpret I e m ↔
      ∃ a, h.interpret I e a ∧ ∃ bs, All2 (fun φ b => φ.interpret I e b) φs bs ∧ AppE I a bs m
  | h, [], m => by
    simp only [KoreAML.appList]
    constructor
    · intro hm; exact ⟨m, hm, [], .nil, rfl⟩
    · rintro ⟨a, ha, bs, hbs, hm⟩
      cases hbs; subst hm; exact ha
  | h, φ :: φs, m => by
    simp only [KoreAML.appList]
    rw [interp_appList (h ⬝ φ) φs m]
    constructor
    · rintro ⟨a', ha', bs, hbs, hm⟩
      obtain ⟨a, b, ha, hb, happ⟩ := KoreAML.interp_app.mp ha'
      exact ⟨a, ha, b :: bs, .cons hb hbs, a', happ, hm⟩
    · rintro ⟨a, ha, bs, hbs, hm⟩
      cases hbs with
      | cons hb hbs =>
        obtain ⟨a', happ, hm⟩ := hm
        exact ⟨a', KoreAML.interp_app.mpr ⟨a, _, ha, hb, happ⟩, _, hbs, hm⟩

theorem trArgs_appList (ctx : KoreAML.Ctx) : ∀ (acc : KoreAML.P) (ps : List Kore.Pattern),
    KoreAML.trArgs ctx acc ps = KoreAML.appList acc (ps.map (KoreAML.tr ctx))
  | acc, [] => by rw [KoreAML.trArgs_nil]; rfl
  | acc, p :: ps => by rw [KoreAML.trArgs_cons, trArgs_appList ctx _ ps]; rfl

theorem appList_append : ∀ (h : KoreAML.P) (φs ψs : List KoreAML.P),
    KoreAML.appList h (φs ++ ψs) = KoreAML.appList (KoreAML.appList h φs) ψs
  | _, [], _ => rfl
  | h, φ :: φs, ψs => appList_append (h ⬝ φ) φs ψs

/-- Patterns that each denote one element, applied to a head. -/
theorem interp_appList_sing {e : Valuation M} (h : KoreAML.P) :
    ∀ (φs : List KoreAML.P) (xs : List M), All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x) φs xs →
      ∀ m, (KoreAML.appList h φs).interpret I e m ↔ ∃ a, h.interpret I e a ∧ AppE I a xs m := by
  intro φs xs hx m
  rw [interp_appList]
  constructor
  · rintro ⟨a, ha, bs, hbs, hm⟩
    suffices hb : bs = xs by subst hb; exact ⟨a, ha, hm⟩
    clear ha hm
    induction hbs generalizing xs with
    | nil => cases hx; rfl
    | cons hb _ ih =>
      cases hx with
      | cons h1 h2 => rw [ih _ h2, (h1 _).mp hb]
  · rintro ⟨a, ha, hm⟩
    refine ⟨a, ha, xs, ?_, hm⟩
    clear ha hm
    induction hx with
    | nil => exact .nil
    | cons h1 _ ih => exact .cons ((h1 _).mpr rfl) ih

end

/-! ## The generators of a sort, as sets of elements -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The head a generator applies to its arguments (`genPat N g args = appList (genHead N g) args`). -/
def genHead (N : String) : KoreAML.Gen → KoreAML.P
  | .ctor k => KoreAML.sym (.symbol k.name)
  | .inj A => KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP N]

theorem genPat_eq (N : String) (g : KoreAML.Gen) (args : List KoreAML.P) :
    KoreAML.Cons.genPat N g args = KoreAML.appList (genHead N g) args := by
  cases g with
  | ctor k => rfl
  | inj A =>
    show KoreAML.appList _ ([_, _] ++ args) = _
    rw [appList_append]; rfl

theorem genHead_closed (N : String) (g : KoreAML.Gen) : Closed (genHead N g) := by
  cases g with
  | ctor k => exact Closed.sym _
  | inj A =>
    exact Closed.appList (Closed.sym _) (fun ψ hψ => by
      rcases mem_two hψ with rfl | rfl <;> exact Closed.sym _)

/-- The elements the generator `g` of the sort named `N` builds from the elements `xs`. -/
def GS (I : Interpretation KoreAML.Sym M) [Inhabited M] (N : String) (g : KoreAML.Gen) (xs : List M) (m : M) : Prop :=
  ∃ a, (genHead N g).interpret I KoreAML.val0 a ∧ AppE I a xs m

/-- An element of the sort named `s`. -/
def InS (I : Interpretation KoreAML.Sym M) [Inhabited M] (s : String) (a : M) : Prop :=
  (KoreAML.inhOf (KoreAML.Cons.sortP s)).interpret I KoreAML.val0 a

theorem inS_iff [Inhabited M] {s : String} {a : M} (e : Valuation M) :
    (KoreAML.inhOf (KoreAML.Cons.sortP s)).interpret I e a ↔ InS I s a :=
  ((Closed.sym _).app (Closed.sym _)).interp e _ a

/-- The valuation that gives the variable `i + 1` the `i`-th element of `L`. -/
def listVal [Inhabited M] (L : List M) : Valuation M := ⟨fun x => L.getD (x.val - 1) default, fun _ _ => False⟩

theorem listVal_xs [Inhabited M] (L : List M) : ∀ (off n : Nat), off + n ≤ L.length →
    (KoreAML.Cons.xs off n).map (listVal L).evalEvar = (L.drop off).take n := by
  intro off n
  induction n generalizing off with
  | zero => intro _; simp [KoreAML.Cons.xs]
  | succ n ih =>
    intro hl
    have h1 : KoreAML.Cons.xs off (n + 1) = ⟨off + 0 + 1⟩ :: KoreAML.Cons.xs (off + 1) n := by
      simp only [KoreAML.Cons.xs, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, EVar.mk.injEq]
      omega
    rw [h1, List.map_cons, ih (off + 1) (by omega)]
    have hlt : off < L.length := by omega
    rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
    simp only [listVal, Nat.add_zero, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, Option.getD_some]

theorem interp_genPat_vars [Inhabited M] (N : String) (g : KoreAML.Gen) (e : Valuation M) (vs : List EVar) (m : M) :
    (KoreAML.Cons.genPat N g (vs.map .evar)).interpret I e m ↔ GS I N g (vs.map e.evalEvar) m := by
  rw [genPat_eq, interp_appList_sing _ _ (vs.map e.evalEvar) (by
    clear m
    induction vs with
    | nil => exact .nil
    | cons v vs ih => exact .cons (fun m => KoreAML.interp_evar) ih)]
  unfold GS
  simp only [(genHead_closed N g).interp e KoreAML.val0]

/-- The `i`-th guard of a list of membership guards. -/
theorem memGuards_hold [Inhabited M] (hD : DefOK I) {e : Valuation M} : ∀ (vs : List EVar) (ss : List String),
    vs.length = ss.length → (∀ (i : Nat) v s, vs[i]? = some v → ss[i]? = some s → InS I s (e.evalEvar v)) →
    ∀ w ∈ KoreAML.Cons.memGuards vs ss, ∀ m, w.interpret I e m
  | [], _, _, _, w, hw, _ => by simp [KoreAML.Cons.memGuards] at hw
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | v :: vs, s :: ss, hl, h, w, hw, m => by
    simp only [KoreAML.Cons.memGuards, List.zip_cons_cons, List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · rw [KoreAML.interp_member hD, inS_iff]
      exact h 0 v s rfl rfl
    · exact memGuards_hold hD vs ss (by simpa using hl)
        (fun i v' s' h1 h2 => h (i + 1) v' s' (by simpa using h1) (by simpa using h2)) w hw m

theorem xs_get {off n i : Nat} {v : EVar} (h : (KoreAML.Cons.xs off n)[i]? = some v) :
    i < n ∧ v = ⟨off + i + 1⟩ := by
  simp only [KoreAML.Cons.xs, List.getElem?_map] at h
  by_cases hi : i < n
  · simp [hi] at h; exact ⟨hi, h.symm⟩
  · simp [hi] at h

theorem xs_length (off n : Nat) : (KoreAML.Cons.xs off n).length = n := by simp [KoreAML.Cons.xs]

theorem listVal_at [Inhabited M] (L : List M) (k : Nat) : (listVal L).evalEvar ⟨k + 1⟩ = L.getD k default := by
  simp [listVal]

theorem map_update_xs (off n : Nat) (f : EVar → M) (y : EVar) (a : M) (hy : ∀ i < n, y ≠ ⟨off + i + 1⟩) :
    (KoreAML.Cons.xs off n).map (Function.update f y a) = (KoreAML.Cons.xs off n).map f := by
  apply List.map_congr_left
  intro v hv
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hv
  obtain ⟨hin, rfl⟩ := xs_get hi
  exact Function.update_noteq (fun h => hy i hin h.symm) _ _

theorem conjList_mem {e : Valuation M} {m : M} : ∀ {ws : List KoreAML.P},
    (KoreAML.conjList ws).interpret I e m → ∀ w ∈ ws, w.interpret I e m
  | [], _, w, hw => absurd hw List.not_mem_nil
  | [w'], h, w, hw => by rw [mem_one hw]; exact h
  | w' :: w'' :: ws, h, w, hw => by
    unfold KoreAML.conjList at h
    rw [interpret_conj] at h
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h.1
    · exact conjList_mem h.2 w hw

theorem disjList_mem {e : Valuation M} {m : M} : ∀ {ws : List KoreAML.P},
    (KoreAML.disjList ws).interpret I e m → ∃ w ∈ ws, w.interpret I e m
  | [], h => by simp [KoreAML.disjList] at h
  | [w'], h => ⟨w', List.mem_singleton_self _, h⟩
  | w' :: w'' :: ws, h => by
    unfold KoreAML.disjList at h
    rw [interpret_disj] at h
    rcases h with h | h
    · exact ⟨w', List.mem_cons_self .., h⟩
    · obtain ⟨w, hw, h⟩ := disjList_mem h
      exact ⟨w, List.mem_cons_of_mem _ hw, h⟩

/-- `inj{s,t}(φ)` as the elements the generator `inj{s}` of `t` builds from `φ`'s. -/
theorem interp_injApp [Inhabited M] {e : Valuation M} (s t : String) (φ : KoreAML.P) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP s, KoreAML.Cons.sortP t, φ]).interpret I e m ↔
      ∃ x, φ.interpret I e x ∧ GS I t (.inj s) [x] m := by
  rw [show [KoreAML.Cons.sortP s, KoreAML.Cons.sortP t, φ] = [KoreAML.Cons.sortP s, KoreAML.Cons.sortP t] ++ [φ] from rfl,
    appList_append, interp_appList]
  constructor
  · rintro ⟨a, ha, bs, hbs, hm⟩
    cases hbs with
    | cons hb hbs => cases hbs; exact ⟨_, hb, a, ((genHead_closed t (.inj s)).interp e KoreAML.val0 a).mp ha, hm⟩
  · rintro ⟨x, hx, a, ha, hm⟩
    exact ⟨a, ((genHead_closed t (.inj s)).interp e KoreAML.val0 a).mpr ha, [x], .cons hx .nil, hm⟩

theorem listVal_split [Inhabited M] (xs ys : List M) (n k : Nat) (hn : xs.length = n) (hk : ys.length = k) :
    (KoreAML.Cons.xs 0 n).map (listVal (xs ++ ys)).evalEvar = xs ∧
      (KoreAML.Cons.xs n k).map (listVal (xs ++ ys)).evalEvar = ys := by
  subst hn; subst hk
  rw [listVal_xs _ 0 _ (by simp), listVal_xs _ _ _ (by simp)]
  simp

theorem listVal_get [Inhabited M] (L : List M) {off n i : Nat} {v : EVar} (h : (KoreAML.Cons.xs off n)[i]? = some v) :
    (listVal L).evalEvar v = L.getD (off + i) default := by
  obtain ⟨_, rfl⟩ := xs_get h
  exact listVal_at L _

theorem single_sorts [Inhabited M] {x : M} {s : String} (hx : InS I s x) :
    ∀ (i : Nat) y s', [x][i]? = some y → [s][i]? = some s' → InS I s' y := by
  intro i y s' h1 h2
  cases i with
  | zero => simp at h1 h2; subst h1; subst h2; exact hx
  | succ i => simp at h1

/-- The elements `xs` of the argument sorts `bs` are covered by none of the overloads whose argument
sorts are among `covs`, read in the model: for each, at some position whose two sorts differ, the
element is not what the injection from the overload's sort builds from an element of it. -/
def UncE [Inhabited M] (I : Interpretation KoreAML.Sym M) (covs : List (List String)) (bs : List String)
    (xs : List M) : Prop :=
  ∀ as ∈ covs, ∃ (i : Nat) (A B : String) (x : M), as[i]? = some A ∧ bs[i]? = some B ∧ A ≠ B ∧ xs[i]? = some x ∧
    ¬ ∃ y, InS I A y ∧ GS I B (.inj A) [y] x

section
variable [Inhabited M] (hD : DefOK I)
include hD

/-- **Cons-Fun** at elements of the argument sorts: the generator builds one element, of its sort. -/
theorem fun_at {N : String} {g : KoreAML.Gen} (h : I ⊧ᴵ (KoreAML.Cons.funItem N g).pat)
    {xs : List M} (hl : xs.length = g.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x) :
    ∃ y, InS I N y ∧ ∀ m, GS I N g xs m ↔ m = y := by
  have hsplit := (listVal_split xs [] _ 0 hl rfl).1
  rw [List.append_nil] at hsplit
  have h1 := h (listVal xs) default
  unfold KoreAML.Cons.funItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (fun w hw => memGuards_hold hD _ _ (xs_length 0 _)
    (fun i v s hv hs => by
      obtain ⟨hi, _⟩ := xs_get hv
      rw [listVal_get xs hv, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hl]; exact hi)]
      exact hxs i _ s (List.getElem?_eq_getElem _) hs) w hw default)
  rw [KoreAML.interp_sExists] at hb
  obtain ⟨y, hy1, hy2⟩ := hb
  rw [KoreAML.interp_member hD] at hy1
  simp only [Function.update_same] at hy1
  rw [inS_iff] at hy1
  rw [KoreAML.interp_equal hD] at hy2
  refine ⟨y, hy1, fun m => ?_⟩
  have := hy2 m
  rw [interp_genPat_vars, KoreAML.interp_evar] at this
  simp only [Function.update_same] at this
  rw [map_update_xs 0 _ _ _ _ (fun i hi he => by simp only [EVar.mk.injEq] at he; omega), hsplit] at this
  exact this

/-- **Cons-Inj** at elements of the argument sorts: a generator with arguments that builds the
same elements from two argument lists has equal arguments. -/
theorem inj_at {N : String} {g : KoreAML.Gen} (h : I ⊧ᴵ (KoreAML.Cons.injItem N g).pat)
    {xs ys : List M} (hl : xs.length = g.argSorts.length) (hl' : ys.length = g.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (heq : ∀ m, GS I N g xs m ↔ GS I N g ys m) : xs = ys := by
  have hL : (xs ++ ys).length = g.argSorts.length + g.argSorts.length := by simp [hl, hl']
  have h1 := h (listVal (xs ++ ys)) default
  unfold KoreAML.Cons.injItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · refine memGuards_hold hD _ _ (xs_length 0 _) (fun i v s hv hs => ?_) w hw default
      obtain ⟨hi, _⟩ := xs_get hv
      rw [listVal_get _ hv, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega)]
      exact hxs i _ s (List.getElem?_eq_getElem _) hs
    · refine memGuards_hold hD _ _ (xs_length _ _) (fun i v s hv hs => ?_) w hw default
      obtain ⟨hi, _⟩ := xs_get hv
      rw [listVal_get _ hv, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        show g.argSorts.length + i - xs.length = i by omega, List.getElem?_eq_getElem (by omega)]
      exact hys i _ s (List.getElem?_eq_getElem _) hs)
  simp only [Pattern.interpret] at hb
  have hsp := listVal_split xs ys _ _ hl hl'
  have hc := hb ((KoreAML.interp_equal hD).mpr (fun m => by
    rw [interp_genPat_vars, interp_genPat_vars, hsp.1, hsp.2]
    exact heq m))
  apply List.ext_getElem?
  intro i
  by_cases hi : i < g.argSorts.length
  · have hm : (Pattern.evar ⟨0 + i + 1⟩ ≡ Pattern.evar ⟨g.argSorts.length + i + 1⟩ : KoreAML.P) ∈
        ((KoreAML.Cons.xs 0 g.argSorts.length).zip (KoreAML.Cons.xs g.argSorts.length g.argSorts.length)).map
          fun (a, b) => (Pattern.evar a ≡ Pattern.evar b : KoreAML.P) := by
      refine List.mem_map.mpr ⟨(⟨0 + i + 1⟩, ⟨g.argSorts.length + i + 1⟩), ?_, rfl⟩
      refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
      simp [KoreAML.Cons.xs, List.getElem?_zip_eq_some, hi]
    have he := (KoreAML.interp_equal hD).mp (conjList_mem hc _ hm) ((listVal (xs ++ ys)).evalEvar ⟨0 + i + 1⟩)
    simp only [KoreAML.interp_evar] at he
    have hx : xs[i]? = ((KoreAML.Cons.xs 0 g.argSorts.length).map (listVal (xs ++ ys)).evalEvar)[i]? := by
      rw [hsp.1]
    have hy : ys[i]? = ((KoreAML.Cons.xs g.argSorts.length g.argSorts.length).map (listVal (xs ++ ys)).evalEvar)[i]? := by
      rw [hsp.2]
    rw [hx, hy, List.getElem?_map, List.getElem?_map]
    simp only [KoreAML.Cons.xs, List.getElem?_map, List.getElem?_range, hi, if_true, Option.map_some]
    simp only [Function.comp, Option.map_some, Option.some.injEq]
    exact he.mp trivial
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **Cons-Dist** at elements of the argument sorts: two generators build different elements. -/
theorem dist_at {N : String} {g g' : KoreAML.Gen} (h : I ⊧ᴵ (KoreAML.Cons.distItem N g g').pat)
    {xs ys : List M} (hl : xs.length = g.argSorts.length) (hl' : ys.length = g'.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → g'.argSorts[i]? = some s → InS I s x) :
    ¬ ∀ m, GS I N g xs m ↔ GS I N g' ys m := by
  have h1 := h (listVal (xs ++ ys)) default
  unfold KoreAML.Cons.distItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · refine memGuards_hold hD _ _ (xs_length 0 _) (fun i v s hv hs => ?_) w hw default
      obtain ⟨hi, _⟩ := xs_get hv
      rw [listVal_get _ hv, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega)]
      exact hxs i _ s (List.getElem?_eq_getElem _) hs
    · refine memGuards_hold hD _ _ (xs_length _ _) (fun i v s hv hs => ?_) w hw default
      obtain ⟨hi, _⟩ := xs_get hv
      rw [listVal_get _ hv, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        show g.argSorts.length + i - xs.length = i by omega, List.getElem?_eq_getElem (by omega)]
      exact hys i _ s (List.getElem?_eq_getElem _) hs)
  rw [KoreAML.interp_notEqual hD] at hb
  intro heq
  have hsp := listVal_split xs ys _ _ hl hl'
  refine hb fun m => ?_
  rw [interp_genPat_vars, interp_genPat_vars, hsp.1, hsp.2]
  exact heq m

omit hD in
theorem disjList_intro {e : Valuation M} {m : M} : ∀ {ws : List KoreAML.P} {w : KoreAML.P}, w ∈ ws →
    w.interpret I e m → (KoreAML.disjList ws).interpret I e m
  | [], _, hw, _ => absurd hw List.not_mem_nil
  | [_], _, hw, h => by rw [mem_one hw] at h; exact h
  | _ :: _ :: _, _, hw, h => by
    unfold KoreAML.disjList
    rw [interpret_disj]
    rcases List.mem_cons.mp hw with rfl | hw
    · exact .inl h
    · exact .inr (disjList_intro hw h)

omit hD in
theorem not_mem_xs {off n k : Nat} (h : off + n < k) : (⟨k⟩ : EVar) ∉ KoreAML.Cons.xs off n := fun hm => by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  obtain ⟨hin, he⟩ := xs_get hi
  simp only [EVar.mk.injEq] at he
  omega

/-- The guard of Cons-Dist at uncovered arguments holds where, for each overload, some argument at
a position whose two sorts differ is no injection's image from the overload's sort (`UncE`). -/
theorem uncoveredP_of {bs : List String} {covs : List (List String)} {xv : List EVar} {z : EVar}
    {e : Valuation M} {xs : List M} (hxv : xv.map e.evalEvar = xs) (hz : z ∉ xv) (hu : UncE I covs bs xs)
    (m : M) : (KoreAML.Cons.uncoveredP bs covs xv z).interpret I e m := by
  unfold KoreAML.Cons.uncoveredP
  refine KoreAML.interp_conjList fun w hw => ?_
  obtain ⟨as, has, rfl⟩ := List.mem_map.mp hw
  obtain ⟨i, A, B, x, hA, hB, hne, hx, hnl⟩ := hu as has
  rw [← hxv, List.getElem?_map] at hx
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
  have hvz : v ≠ z := fun h => hz (h ▸ List.mem_of_getElem? hv)
  refine disjList_intro (I := I) (w := ∼(KoreAML.Cons.liesP A B (.evar v) z)) ?_ ?_
  · refine List.mem_filterMap.mpr ⟨((A, B), v), ?_, by simp [hne]⟩
    exact List.mem_iff_getElem?.mpr ⟨i, by simp [List.getElem?_zip_eq_some, hA, hB, hv]⟩
  · rw [interpret_neg]
    intro hl
    unfold KoreAML.Cons.liesP at hl
    rw [KoreAML.interp_sExists] at hl
    obtain ⟨a, ha1, ha2⟩ := hl
    rw [KoreAML.interp_member hD] at ha1
    simp only [Function.update_same] at ha1
    rw [KoreAML.interp_equal hD] at ha2
    have := (ha2 (e.evalEvar v)).mp (by
      rw [KoreAML.interp_evar]; exact (Function.update_noteq hvz _ _).symm)
    rw [interp_injApp] at this
    obtain ⟨x', hx', hm⟩ := this
    rw [KoreAML.interp_evar] at hx'
    simp only [Function.update_same] at hx'
    subst hx'
    exact hnl ⟨_, (inS_iff _).mp ha1, hm⟩

/-- **Cons-Fun at uncovered arguments** at elements of the argument sorts that no overload covers
in the model (`hu`): the generator builds one element, of its sort. -/
theorem funUnc_at {N : String} {g : KoreAML.Gen} {covs : List (List String)}
    (h : I ⊧ᴵ (KoreAML.Cons.funUncItem N g covs).pat)
    {xs : List M} (hl : xs.length = g.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hu : UncE I covs g.argSorts xs) :
    ∃ y, InS I N y ∧ ∀ m, GS I N g xs m ↔ m = y := by
  have hsplit := (listVal_split xs [] _ 0 hl rfl).1
  rw [List.append_nil] at hsplit
  have h1 := h (listVal xs) default
  unfold KoreAML.Cons.funUncItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · refine memGuards_hold hD _ _ (xs_length 0 _) (fun i v s hv hs => ?_) w hw default
      obtain ⟨hi, _⟩ := xs_get hv
      rw [listVal_get xs hv, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hl]; exact hi)]
      exact hxs i _ s (List.getElem?_eq_getElem _) hs
    · rw [List.mem_singleton] at hw
      subst hw
      exact uncoveredP_of hD hsplit (not_mem_xs (off := 0) (by omega)) hu default)
  rw [KoreAML.interp_sExists] at hb
  obtain ⟨y, hy1, hy2⟩ := hb
  rw [KoreAML.interp_member hD] at hy1
  simp only [Function.update_same] at hy1
  rw [inS_iff] at hy1
  rw [KoreAML.interp_equal hD] at hy2
  refine ⟨y, hy1, fun m => ?_⟩
  have := hy2 m
  rw [interp_genPat_vars, KoreAML.interp_evar] at this
  simp only [Function.update_same] at this
  rw [map_update_xs 0 _ _ _ _ (fun i hi he => by simp only [EVar.mk.injEq] at he; omega), hsplit] at this
  exact this

/-- **Cons-Inj at uncovered arguments** at elements of the argument sorts that no overload covers
in the model (`hu`, `hu'`): a generator with arguments that builds the same elements from two
argument lists has equal arguments. -/
theorem injUnc_at {N : String} {g : KoreAML.Gen} {covs : List (List String)}
    (h : I ⊧ᴵ (KoreAML.Cons.injUncItem N g covs).pat)
    {xs ys : List M} (hl : xs.length = g.argSorts.length) (hl' : ys.length = g.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hu : UncE I covs g.argSorts xs) (hu' : UncE I covs g.argSorts ys)
    (heq : ∀ m, GS I N g xs m ↔ GS I N g ys m) : xs = ys := by
  have hL : (xs ++ ys).length = g.argSorts.length + g.argSorts.length := by simp [hl, hl']
  have hsp := listVal_split xs ys _ _ hl hl'
  have h1 := h (listVal (xs ++ ys)) default
  unfold KoreAML.Cons.injUncItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · refine memGuards_hold hD _ _ (xs_length 0 _) (fun i v s hv hs => ?_) w hw default
        obtain ⟨hi, _⟩ := xs_get hv
        rw [listVal_get _ hv, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          List.getElem?_eq_getElem (by omega)]
        exact hxs i _ s (List.getElem?_eq_getElem _) hs
      · refine memGuards_hold hD _ _ (xs_length _ _) (fun i v s hv hs => ?_) w hw default
        obtain ⟨hi, _⟩ := xs_get hv
        rw [listVal_get _ hv, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          show g.argSorts.length + i - xs.length = i by omega, List.getElem?_eq_getElem (by omega)]
        exact hys i _ s (List.getElem?_eq_getElem _) hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact uncoveredP_of hD hsp.1 (not_mem_xs (off := 0) (by omega)) hu default
      · exact uncoveredP_of hD hsp.2 (not_mem_xs (off := g.argSorts.length) (by omega)) hu' default)
  simp only [Pattern.interpret] at hb
  have hc := hb ((KoreAML.interp_equal hD).mpr (fun m => by
    rw [interp_genPat_vars, interp_genPat_vars, hsp.1, hsp.2]
    exact heq m))
  apply List.ext_getElem?
  intro i
  by_cases hi : i < g.argSorts.length
  · have hm : (Pattern.evar ⟨0 + i + 1⟩ ≡ Pattern.evar ⟨g.argSorts.length + i + 1⟩ : KoreAML.P) ∈
        ((KoreAML.Cons.xs 0 g.argSorts.length).zip (KoreAML.Cons.xs g.argSorts.length g.argSorts.length)).map
          fun (a, b) => (Pattern.evar a ≡ Pattern.evar b : KoreAML.P) := by
      refine List.mem_map.mpr ⟨(⟨0 + i + 1⟩, ⟨g.argSorts.length + i + 1⟩), ?_, rfl⟩
      refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
      simp [KoreAML.Cons.xs, List.getElem?_zip_eq_some, hi]
    have he := (KoreAML.interp_equal hD).mp (conjList_mem hc _ hm) ((listVal (xs ++ ys)).evalEvar ⟨0 + i + 1⟩)
    simp only [KoreAML.interp_evar] at he
    have hx : xs[i]? = ((KoreAML.Cons.xs 0 g.argSorts.length).map (listVal (xs ++ ys)).evalEvar)[i]? := by
      rw [hsp.1]
    have hy : ys[i]? = ((KoreAML.Cons.xs g.argSorts.length g.argSorts.length).map (listVal (xs ++ ys)).evalEvar)[i]? := by
      rw [hsp.2]
    rw [hx, hy, List.getElem?_map, List.getElem?_map]
    simp only [KoreAML.Cons.xs, List.getElem?_map, List.getElem?_range, hi, if_true, Option.map_some]
    simp only [Function.comp, Option.map_some, Option.some.injEq]
    exact he.mp trivial
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **Cons-Dist at uncovered arguments** at elements of the argument sorts where the guards on the
overloading generators' arguments hold (`hu`, `hu'`): two generators build different elements. -/
theorem distUnc_at {N : String} {g g' : KoreAML.Gen} {ug ug' : Option (List (List String))}
    (h : I ⊧ᴵ (KoreAML.Cons.distUncItem N g g' ug ug').pat)
    {xs ys : List M} (hl : xs.length = g.argSorts.length) (hl' : ys.length = g'.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → g'.argSorts[i]? = some s → InS I s x)
    (hu : ∀ covs, ug = some covs → ∀ m, (KoreAML.Cons.uncoveredP g.argSorts covs
      (KoreAML.Cons.xs 0 g.argSorts.length) ⟨g.argSorts.length + g'.argSorts.length + 1⟩).interpret I
      (listVal (xs ++ ys)) m)
    (hu' : ∀ covs, ug' = some covs → ∀ m, (KoreAML.Cons.uncoveredP g'.argSorts covs
      (KoreAML.Cons.xs g.argSorts.length g'.argSorts.length) ⟨g.argSorts.length + g'.argSorts.length + 1⟩).interpret I
      (listVal (xs ++ ys)) m) :
    ¬ ∀ m, GS I N g xs m ↔ GS I N g' ys m := by
  have h1 := h (listVal (xs ++ ys)) default
  unfold KoreAML.Cons.distUncItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · refine memGuards_hold hD _ _ (xs_length 0 _) (fun i v s hv hs => ?_) w hw default
          obtain ⟨hi, _⟩ := xs_get hv
          rw [listVal_get _ hv, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            List.getElem?_eq_getElem (by omega)]
          exact hxs i _ s (List.getElem?_eq_getElem _) hs
        · refine memGuards_hold hD _ _ (xs_length _ _) (fun i v s hv hs => ?_) w hw default
          obtain ⟨hi, _⟩ := xs_get hv
          rw [listVal_get _ hv, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
            show g.argSorts.length + i - xs.length = i by omega, List.getElem?_eq_getElem (by omega)]
          exact hys i _ s (List.getElem?_eq_getElem _) hs
      · cases ug with
        | none => simp at hw
        | some covs => simp only [List.mem_singleton] at hw; subst hw; exact hu covs rfl default
    · cases ug' with
      | none => simp at hw
      | some covs => simp only [List.mem_singleton] at hw; subst hw; exact hu' covs rfl default)
  rw [KoreAML.interp_notEqual hD] at hb
  intro heq
  have hsp := listVal_split xs ys _ _ hl hl'
  refine hb fun m => ?_
  rw [interp_genPat_vars, interp_genPat_vars, hsp.1, hsp.2]
  exact heq m

end

/-- A guarded pattern entails the same pattern under more guards. -/
theorem guarded_append_unc {ws vs : List KoreAML.P} {φ : KoreAML.P} (h : I ⊧ᴵ KoreAML.guarded ws φ) :
    I ⊧ᴵ KoreAML.guarded (ws ++ vs) φ := by
  intro e m
  have key : (∀ w ∈ ws ++ vs, w.interpret I e m) → φ.interpret I e m := fun hw =>
    KoreAML.interp_guarded (h e m) fun w hw' => hw w (List.mem_append_left _ hw')
  generalize ws ++ vs = us at key ⊢
  cases us with
  | nil => exact key (fun _ hw => nomatch hw)
  | cons u us => intro hc; exact key (conjList_mem hc)

/-- **Cons-Fun entails Cons-Fun at uncovered arguments**: the second is the first with the guard
`uncoveredP` added. -/
theorem funUncItem_of_funItem {N : String} {g : KoreAML.Gen} (covs : List (List String))
    (h : I ⊧ᴵ (KoreAML.Cons.funItem N g).pat) : I ⊧ᴵ (KoreAML.Cons.funUncItem N g covs).pat := by
  unfold KoreAML.Cons.funUncItem
  unfold KoreAML.Cons.funItem at h
  exact guarded_append_unc h

/-- **Cons-Inj entails Cons-Inj at uncovered arguments**: the second is the first with the guards
`uncoveredP` on both argument lists added. -/
theorem injUncItem_of_injItem {N : String} {g : KoreAML.Gen} (covs : List (List String))
    (h : I ⊧ᴵ (KoreAML.Cons.injItem N g).pat) : I ⊧ᴵ (KoreAML.Cons.injUncItem N g covs).pat := by
  unfold KoreAML.Cons.injUncItem
  unfold KoreAML.Cons.injItem at h
  exact guarded_append_unc h

/-- `inj{s,t}(φ)` written with the sort constants `sortP` (Statements.lean). -/
theorem interp_injApp' [Inhabited M] {e : Valuation M} (s t : String) (φ : KoreAML.P) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [sortP s, sortP t, φ]).interpret I e m ↔
      ∃ x, φ.interpret I e x ∧ GS I t (.inj s) [x] m :=
  interp_injApp s t φ m

section
variable [Inhabited M] (hD : DefOK I)
include hD

/-- **Cons-Dist′** at elements: two injections from incomparable sorts with common lower bounds
build one element only from the injections of one element of a common lower bound. -/
theorem distLb_at {N A B : String} {lbs : List String} (h : I ⊧ᴵ (distLbItem N A B lbs).pat)
    {x y : M} (hx : InS I A x) (hy : InS I B y) (heq : ∀ m, GS I N (.inj A) [x] m ↔ GS I N (.inj B) [y] m) :
    ∃ C ∈ lbs, ∃ z, InS I C z ∧ (∀ m, GS I A (.inj C) [z] m ↔ m = x) ∧ (∀ m, GS I B (.inj C) [z] m ↔ m = y) := by
  have h1 := h (listVal [x, y]) default
  unfold distLbItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (by
    intro w hw
    rcases mem_two hw with rfl | rfl
    · rw [KoreAML.interp_member hD]; exact (inS_iff _).mpr hx
    · rw [KoreAML.interp_member hD]; exact (inS_iff _).mpr hy)
  simp only [Pattern.interpret] at hb
  have hc := hb ((KoreAML.interp_equal hD).mpr (fun m => by
    rw [interp_injApp', interp_injApp']
    simp only [KoreAML.interp_evar]
    constructor
    · rintro ⟨x', rfl, hm⟩; exact ⟨_, rfl, (heq m).mp hm⟩
    · rintro ⟨y', rfl, hm⟩; exact ⟨_, rfl, (heq m).mpr hm⟩))
  obtain ⟨φ, hφ, hφm⟩ := disjList_mem hc
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hφ
  rw [KoreAML.interp_sExists] at hφm
  obtain ⟨z, hz1, hz2⟩ := hφm
  rw [KoreAML.interp_member hD] at hz1
  simp only [Function.update_same] at hz1
  rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hz2
  refine ⟨C, hC, z, (inS_iff _).mp hz1, fun m => ?_, fun m => ?_⟩
  · have := (hz2.1 m).symm
    rw [interp_injApp', KoreAML.interp_evar] at this
    simp only [KoreAML.interp_evar, Function.update_same, exists_eq_left] at this
    rw [this]; rfl
  · have := (hz2.2 m).symm
    rw [interp_injApp', KoreAML.interp_evar] at this
    simp only [KoreAML.interp_evar, Function.update_same, exists_eq_left] at this
    rw [this]; rfl

end

end

/-! ## Generators in `Γ` -/

theorem mem_insertBy {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (a x : α) :
    ∀ l : List α, x ∈ insertBy key a l ↔ x = a ∨ x ∈ l
  | [] => by simp [insertBy]
  | b :: bs => by
    unfold insertBy
    split
    · exact List.mem_cons
    · rw [List.mem_cons, mem_insertBy key a x bs, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem mem_sortBy {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (x : α) :
    ∀ l : List α, x ∈ sortBy key l ↔ x ∈ l
  | [] => by simp [sortBy]
  | a :: l => by
    have : sortBy key (a :: l) = insertBy key a (sortBy key l) := rfl
    rw [this, mem_insertBy, mem_sortBy key x l, List.mem_cons]

theorem mem_pairs_of {α : Type} {x y : α} (hne : x ≠ y) : ∀ {l : List α}, x ∈ l → y ∈ l →
    (x, y) ∈ pairs l ∨ (y, x) ∈ pairs l
  | [], h, _ => absurd h List.not_mem_nil
  | a :: l, hx, hy => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.mp hx with hxa | hx'
    · rcases List.mem_cons.mp hy with hya | hy'
      · exact absurd (hxa.trans hya.symm) hne
      · exact Or.inl (Or.inl ⟨y, hy', hxa.symm, rfl⟩)
    · rcases List.mem_cons.mp hy with hya | hy'
      · exact Or.inr (Or.inl ⟨x, hx', hya.symm, rfl⟩)
      · rcases mem_pairs_of hne hx' hy' with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

section
variable {c : Semantics}

theorem gens_ctor {k : CtorSig} (hk : k ∈ c.ctorSigs) : Gen.ctor k ∈ c.gens k.result := by
  unfold Semantics.gens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, by simp⟩, rfl⟩)))

/-- A constructor of the semantics is no overloading symbol. -/
theorem isOvl_of_ctorSigs {k : CtorSig} (hk : k ∈ c.ctorSigs) : c.isOvl k.name = false := by
  have : c.isCtor k.name = true := by
    unfold Semantics.isCtor
    rw [lookupSig_eq, List.find?_isSome]
    exact ⟨k, hk, by simp⟩
  simp [Semantics.isOvl, this]

/-- A constructor is no function-overloaded symbol. -/
theorem fnOvl_ctorSigs {k : CtorSig} (hk : k ∈ c.ctorSigs) : c.fnOvl (.ctor k) = false := by
  simp [Semantics.fnOvl, isOvl_of_ctorSigs hk]

/-- A symbol with no function among its overloads is no function-overloaded symbol. -/
theorem fnOvl_of_noFnOver [OvlOK c] {k : CtorSig} (h : OvlLaws.NoFnOver c k.name) : c.fnOvl (.ctor k) = false := by
  cases hf : c.fnOvl (.ctor k) with
  | false => rfl
  | true =>
    exfalso
    simp only [Semantics.fnOvl, Bool.and_eq_true, List.contains_iff_mem] at hf
    cases hlk : c.lookupOvl k.name with
    | none => rw [hlk] at hf; simp at hf
    | some ok =>
      obtain ⟨kg, hkg, hb⟩ := OvlOK.fnOver ok (OvlLaws.mem_of_lookupOvl hlk)
        (by rw [(OvlLaws.lookupOvl_spec hlk).1]; exact hf.2)
      rw [h ok hlk kg hkg] at hb
      cases hb

/-- Two generators that are constructors of the semantics or injections are apart unguarded. -/
theorem distGuarded_ctorSigs {g g' : Gen} (h : ∀ k, g = .ctor k → k ∈ c.ctorSigs)
    (h' : ∀ k, g' = .ctor k → k ∈ c.ctorSigs) : c.distGuarded g g' = false := by
  cases g with
  | ctor k =>
    cases g' with
    | ctor k' => simp [Semantics.distGuarded, Semantics.fnOvl, isOvl_of_ctorSigs (h k rfl), isOvl_of_ctorSigs (h' k' rfl)]
    | inj _ => simp [Semantics.distGuarded, Semantics.fnOvl, isOvl_of_ctorSigs (h k rfl)]
  | inj _ =>
    cases g' with
    | ctor k' => simp [Semantics.distGuarded, Semantics.fnOvl, isOvl_of_ctorSigs (h' k' rfl)]
    | inj _ => rfl

theorem gens_of_ovl {o : OvlSig} (ho : o ∈ c.ovls) : Gen.ctor o.sig ∈ c.gens o.sig.result := by
  unfold Semantics.gens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨o.sig, List.mem_filter.mpr ⟨List.mem_map_of_mem ho, by simp⟩, rfl⟩)))

theorem gens_inj {a b : Srt} (h : (a, b) ∈ c.subsorts) : Gen.inj a ∈ c.gens b := by
  unfold Semantics.gens
  refine List.mem_append_right _ (List.mem_map.mpr ⟨a, (mem_sortBy id a _).mpr ?_, rfl⟩)
  exact List.mem_map.mpr ⟨(a, b), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

/-- An injection is no open generator: `consItemsK` writes its items. -/
theorem gensF_inj {a b : Srt} (h : (a, b) ∈ c.subsorts) : Gen.inj a ∈ (c.gens b).filter (!c.isOpenGen ·) :=
  List.mem_filter.mpr ⟨gens_inj h, rfl⟩

/-- The argument sorts of the overloads of a generator that is an overloading symbol, as the items
at uncovered arguments guard it (`none` for any other generator). -/
def ovlArgsOf (c : Semantics) : Gen → Option (List (List String))
  | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o =>
      (c.ovlOver o).map fun kg => kg.args.map c.sortName else none
  | .inj _ => none

theorem perSort_mem {N : Srt} (hN : N ∈ consSorts c) {it : KoreAML.Item}
    (h : it ∈ ((c.gens N).filter (!c.isOpenGen ·)).map (fun g =>
        if c.fnOvl g then KoreAML.Cons.funUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD [])
        else KoreAML.Cons.funItem (c.sortName N) (Gen.toK c g)) ∨
      it ∈ (((c.gens N).filter (!c.isOpenGen ·)).filter fun g => !(Gen.toK c g).argSorts.isEmpty).map (fun g =>
        if c.fnOvl g then KoreAML.Cons.injUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD [])
        else KoreAML.Cons.injItem (c.sortName N) (Gen.toK c g)) ∨
      it ∈ (pairs ((c.gens N).filter (!c.isOpenGen ·))).flatMap (fun (g, g') => match g, g' with
        | .inj a, .inj b =>
          if c.le a b || c.le b a then []
          else match c.lowerBounds a b with
            | [] => [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')]
            | lbs => [distLbItem (c.sortName N) (c.sortName a) (c.sortName b) (lbs.map c.sortName)]
        | _, _ =>
          if c.distGuarded g g' then
            [KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')
              (match g with
                | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o =>
                    (c.ovlOver o).map fun kg => kg.args.map c.sortName else none
                | .inj _ => none)
              (match g' with
                | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o =>
                    (c.ovlOver o).map fun kg => kg.args.map c.sortName else none
                | .inj _ => none)]
          else [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')])) :
    it ∈ consItemsK c := by
  unfold consItemsK
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨N, hN, ?_⟩)))
  rcases h with h | h | h
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  · exact List.mem_append_left _ (List.mem_append_right _ h)

/-- Cons-Fun of a generator that is no function-overloaded symbol is in `Γ`. -/
theorem funItem_mem {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hnf : c.fnOvl g = false) :
    KoreAML.Cons.funItem (c.sortName N) (Gen.toK c g) ∈ consItemsK c :=
  perSort_mem hN (Or.inl (List.mem_map.mpr ⟨g, hg, by simp [hnf]⟩))

/-- Cons-Fun at uncovered arguments of a function-overloaded symbol is in `Γ`. -/
theorem funUncItem_mem {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hf : c.fnOvl g = true) :
    KoreAML.Cons.funUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD []) ∈ consItemsK c :=
  perSort_mem hN (Or.inl (List.mem_map.mpr ⟨g, hg, by simp [hf]⟩))

theorem toK_argSorts (g : Gen) : (Gen.toK c g).argSorts = g.argSorts.map c.sortName := by
  cases g <;> rfl

/-- Cons-Inj of a generator with arguments that is no function-overloaded symbol is in `Γ`. -/
theorem injItem_mem {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g.argSorts ≠ []) (hnf : c.fnOvl g = false) :
    KoreAML.Cons.injItem (c.sortName N) (Gen.toK c g) ∈ consItemsK c := by
  refine perSort_mem hN (Or.inr (Or.inl (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, ?_⟩, by simp [hnf]⟩)))
  rw [toK_argSorts]
  cases h : g.argSorts with
  | nil => exact absurd h hne
  | cons _ _ => rfl

/-- Cons-Inj at uncovered arguments of a function-overloaded symbol with arguments is in `Γ`. -/
theorem injUncItem_mem {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g.argSorts ≠ []) (hf : c.fnOvl g = true) :
    KoreAML.Cons.injUncItem (c.sortName N) (Gen.toK c g) ((ovlArgsOf c g).getD []) ∈ consItemsK c := by
  refine perSort_mem hN (Or.inr (Or.inl (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, ?_⟩, by simp [hf]⟩)))
  rw [toK_argSorts]
  cases h : g.argSorts with
  | nil => exact absurd h hne
  | cons _ _ => rfl

/-- Two generators of a constructor sort, not both injections, are apart in `Γ` (Cons-Dist). -/
theorem distItem_mem {N : Srt} (hN : N ∈ consSorts c) {g g' : Gen}
    (hp : (g, g') ∈ pairs ((c.gens N).filter (!c.isOpenGen ·)))
    (hni : ∀ a b, g = .inj a → g' = .inj b → False) (hgd : c.distGuarded g g' = false) :
    KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') ∈ consItemsK c := by
  refine perSort_mem hN (Or.inr (Or.inr (List.mem_flatMap.mpr ⟨(g, g'), hp, ?_⟩)))
  cases g with
  | ctor k =>
    cases g' <;> (simp only [hgd, Bool.false_eq_true, ↓reduceIte]; exact List.mem_singleton_self _)
  | inj a =>
    cases g' with
    | ctor k => simp only [hgd, Bool.false_eq_true, ↓reduceIte]; exact List.mem_singleton_self _
    | inj b => exact absurd rfl (hni a b rfl)

/-- Two generators of a constructor sort, not both injections, that `distGuarded` names are apart
in `Γ` at uncovered arguments (Cons-Dist at uncovered arguments). -/
theorem distUncItem_mem {N : Srt} (hN : N ∈ consSorts c) {g g' : Gen}
    (hp : (g, g') ∈ pairs ((c.gens N).filter (!c.isOpenGen ·)))
    (hni : ∀ a b, g = .inj a → g' = .inj b → False) (hgd : c.distGuarded g g' = true) :
    KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsOf c g) (ovlArgsOf c g') ∈
      consItemsK c := by
  refine perSort_mem hN (Or.inr (Or.inr (List.mem_flatMap.mpr ⟨(g, g'), hp, ?_⟩)))
  cases g with
  | ctor k =>
    cases g' <;> (simp only [hgd, ↓reduceIte]; exact List.mem_singleton_self _)
  | inj a =>
    cases g' with
    | ctor k => simp only [hgd, ↓reduceIte]; exact List.mem_singleton_self _
    | inj b => exact absurd rfl (hni a b rfl)

/-- Two injections from incomparable sorts into a constructor sort: Cons-Dist without a common
lower bound, Cons-Dist′ with one. -/
theorem injPair_mem {N : Srt} (hN : N ∈ consSorts c) {a b : Srt}
    (hp : (Gen.inj a, Gen.inj b) ∈ pairs ((c.gens N).filter (!c.isOpenGen ·)))
    (hab : (c.le a b || c.le b a) = false) :
    (c.lowerBounds a b = [] ∧ KoreAML.Cons.distItem (c.sortName N) (.inj (c.sortName a)) (.inj (c.sortName b)) ∈ consItemsK c) ∨
    (c.lowerBounds a b ≠ [] ∧
      distLbItem (c.sortName N) (c.sortName a) (c.sortName b) ((c.lowerBounds a b).map c.sortName) ∈ consItemsK c) := by
  cases hl : c.lowerBounds a b with
  | nil =>
    refine Or.inl ⟨rfl, perSort_mem hN (Or.inr (Or.inr (List.mem_flatMap.mpr ⟨_, hp, ?_⟩)))⟩
    simp only [hab, Bool.false_eq_true, ↓reduceIte, hl, List.mem_singleton]
    rfl
  | cons l ls =>
    refine Or.inr ⟨List.cons_ne_nil _ _, perSort_mem hN (Or.inr (Or.inr (List.mem_flatMap.mpr ⟨_, hp, ?_⟩)))⟩
    simp only [hab, Bool.false_eq_true, ↓reduceIte, hl, List.mem_singleton]

end

/-! ## The well-formedness the downward reading takes -/

section
variable {c : Semantics} (hg : genWf c = true)
include hg

theorem genWf_ctor {k : CtorSig} (hk : k ∈ c.ctorSigs) : k.result ∈ consSorts c := by
  simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg
  exact List.contains_iff_mem.mp (hg.1.1.1.1 k hk)

theorem genWf_sub {a b : Srt} (h : (a, b) ∈ c.subsorts) : b ∈ consSorts c ∧ a ≠ b := by
  simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.1.2 (a, b) h
  simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne] at this
  exact this

theorem genWf_cons {s : Srt} (h : s ∈ consSorts c) :
    apartSort c s = true ∧ s ≠ Srt.int ∧ s ≠ Srt.bool ∧ s ≠ Srt.kconfigVar ∧ s ∉ c.lib.tokenSorts ∧
      s ∉ c.lib.byteSorts ∧ c.collOf s = none := by
  simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.2 s h
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Option.isNone_iff_eq_none] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩, -⟩ := this
  refine ⟨h1, h2, h3, h4, fun hm => ?_, fun hm => ?_, h7⟩
  · have := List.contains_iff_mem.mpr hm; rw [h5] at this; cases this
  · have := List.contains_iff_mem.mpr hm; rw [h6] at this; cases this

/-- A constructor sort is not Float. -/
theorem genWf_float {s : Srt} (h : s ∈ consSorts c) : s ≠ Srt.float := by
  simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.2 s h
  simp only [Bool.and_eq_true, bne_iff_ne] at this
  exact this.1.1.2

/-- A constructor sort is neither String nor Bytes. -/
theorem genWf_lit {s : Srt} (h : s ∈ consSorts c) : s ≠ Srt.string ∧ s ≠ Srt.bytes := by
  simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.2 s h
  simp only [Bool.and_eq_true, bne_iff_ne] at this
  exact ⟨this.1.2, this.2⟩

/-- An open generator's result sort is a constructor sort. -/
theorem genWf_raw_cons {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) : k.sig.result ∈ consSorts c := by
  simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.2 k hk
  simp only [hr, Bool.not_true, Bool.false_or] at this
  exact List.contains_iff_mem.mp this

/-- The flat conjunct of `genWf` at a raw parameter `k`, unfolded. -/
theorem genWf_flat_parts {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) :
    (∀ g ∈ c.ctorSigs, g.name ≠ k.sig.name ∧ (g.result = k.sig.result → g.args = [])) ∧
    (∀ g ∈ c.ovlSigs, g.name ≠ k.sig.name ∧ g.result ≠ k.sig.result) ∧
    (∀ p ∈ c.subsorts, p.2 ≠ k.sig.result) := by
  simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.2 k hk
  simp only [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, List.isEmpty_iff] at this
  obtain ⟨⟨hc, ho⟩, hs⟩ := this
  refine ⟨fun g hgm => ⟨(hc g hgm).1, fun he => ?_⟩, fun g hgm => ho g hgm, fun p hp => hs p hp⟩
  rcases (hc g hgm).2 with h | h
  · exact absurd he h
  · exact h

/-- A constructor of an open generator's result sort has no argument. -/
theorem genWf_flat_ctor {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) {g : CtorSig}
    (hgm : g ∈ c.ctorSigs) (hres : g.result = k.sig.result) : g.args = [] :=
  ((genWf_flat_parts hg hk hr).1 g hgm).2 hres

/-- No overloading symbol has an open generator's result sort. -/
theorem genWf_flat_ovl {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) {g : CtorSig}
    (hgm : g ∈ c.ovlSigs) : g.result ≠ k.sig.result :=
  ((genWf_flat_parts hg hk hr).2.1 g hgm).2

/-- No subsort pair has an open generator's result sort as upper sort. -/
theorem genWf_flat_sub {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) {a b : Srt}
    (hab : (a, b) ∈ c.subsorts) : b ≠ k.sig.result :=
  (genWf_flat_parts hg hk hr).2.2 (a, b) hab

/-- No constructor and no overloading symbol bears an open generator's name. -/
theorem genWf_flat_name {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) :
    (∀ g ∈ c.ctorSigs, g.name ≠ k.sig.name) ∧ (∀ g ∈ c.ovlSigs, g.name ≠ k.sig.name) :=
  ⟨fun g hgm => ((genWf_flat_parts hg hk hr).1 g hgm).1, fun g hgm => ((genWf_flat_parts hg hk hr).2.1 g hgm).1⟩

/-- A constructor is no open generator. -/
theorem isOpenGen_ctor {k : CtorSig} (hk : k ∈ c.ctorSigs) : c.isOpenGen (.ctor k) = false := by
  cases ho : c.lookupOpen k.name with
  | none => simp [Semantics.isOpenGen, ho]
  | some p =>
    obtain ⟨hp, hr, hn, -⟩ := c.lookupOpen_spec ho
    exact absurd hn.symm ((genWf_flat_name hg hp hr).1 k hk)

/-- An overloading symbol is no open generator. -/
theorem isOpenGen_ovl {k : CtorSig} (hk : k ∈ c.ovlSigs) : c.isOpenGen (.ctor k) = false := by
  cases ho : c.lookupOpen k.name with
  | none => simp [Semantics.isOpenGen, ho]
  | some p =>
    obtain ⟨hp, hr, hn, -⟩ := c.lookupOpen_spec ho
    exact absurd hn.symm ((genWf_flat_name hg hp hr).2 k hk)

theorem gensF_ctor {k : CtorSig} (hk : k ∈ c.ctorSigs) : Gen.ctor k ∈ (c.gens k.result).filter (!c.isOpenGen ·) :=
  List.mem_filter.mpr ⟨gens_ctor hk, by simp [isOpenGen_ctor hg hk]⟩

theorem gensF_of_ovl {o : OvlSig} (ho : o ∈ c.ovls) : Gen.ctor o.sig ∈ (c.gens o.sig.result).filter (!c.isOpenGen ·) :=
  List.mem_filter.mpr ⟨gens_of_ovl ho, by simp [isOpenGen_ovl hg (List.mem_map_of_mem (f := (·.sig)) ho)]⟩

omit hg in
/-- KConfigVar is `apartSort`: it is among `distinctSorts`. -/
theorem genWf_kcv : apartSort c Srt.kconfigVar = true := by
  have h : Srt.kconfigVar ∈ distinctSorts c := List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  simp only [apartSort, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr h)

/-- A constructor term's sort: its constructor's result sort, or, for a raw application of an
overloading symbol at arguments no overload covers, the symbol's result sort, a constructor sort,
or, for an application of an open generator that the interpretation leaves raw, the generator's
result sort, a constructor sort. -/
theorem sortOf_ctor_cases [h : OvlOK c] {f : Sym} {ts : List GroundTerm} {s : Srt}
    (hw : c.sortOf (.ctor f ts) = some s) :
    (∃ k, lookupSig c.ctorSigs f = some k ∧ c.sortsOf ts = some k.args ∧ s = k.result) ∨
    (∃ o, c.lookupOvl f = some o ∧ c.isOvl f = true ∧ c.sortsOf ts = some o.sig.args ∧
      c.uncovered f ts = true ∧ s = o.sig.result ∧ o.sig.result ∈ consSorts c) ∨
    (∃ k, c.lookupOpen f = some k ∧ lookupSig c.ctorSigs f = none ∧ c.lookupOvl f = none ∧
      c.sortsOf ts = some k.sig.args ∧ c.keepsRaw f ts = true ∧ s = k.sig.result ∧ k.sig.result ∈ consSorts c) := by
  rcases c.sortOf_ctor_iff.mp hw with hk | ⟨-, o, ho, hts, hu, rfl⟩ | ⟨hk, ho, k, hko, hts, hkr, rfl⟩
  · exact .inl hk
  · obtain ⟨-, -, hio, -, hcs⟩ := OvlLaws.ovl_parts h.ok ho
    exact .inr (.inl ⟨o, ho, hio, hts, hu, rfl, hcs⟩)
  · obtain ⟨hm, hr, -, -⟩ := c.lookupOpen_spec hko
    exact .inr (.inr ⟨k, hko, hk, ho, hts, hkr, rfl, genWf_raw_cons hg hm hr⟩)

/-- A constructor term's sort is a constructor sort. -/
theorem ctor_sort_cons [OvlOK c] {f : Sym} {ts : List GroundTerm} {s : Srt} (hw : c.sortOf (.ctor f ts) = some s) :
    s ∈ consSorts c := by
  rcases sortOf_ctor_cases hg hw with ⟨k, hk, -, rfl⟩ | ⟨o, -, -, -, -, rfl, hcs⟩ | ⟨k, -, -, -, -, -, rfl, hcs⟩
  · exact genWf_ctor hg (lookupSig_spec hk).1
  · exact hcs
  · exact hcs

/-- A value of a constructor sort is a constructor or an injection applied to values. -/
theorem consSort_shape {s : Srt} (hs : s ∈ consSorts c) {w : GroundTerm} (hw : c.sortOf w = some s) :
    (∃ f ws, w = .ctor f ws) ∨ (∃ a b w0, w = .inj a b w0) := by
  obtain ⟨-, hi, hb, hk, ht, hy, hco⟩ := genWf_cons hg hs
  have hcs := carrier_of_consSorts hs
  cases w with
  | ctor f ws => exact Or.inl ⟨f, ws, rfl⟩
  | inj a b w0 => exact Or.inr ⟨a, b, w0, rfl⟩
  | dv s' lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hw
    exfalso
    cases lit with
    | int _ => simp only [dvOK, hcs] at hok; exact hi (beq_iff_eq.mp hok)
    | bool _ => simp only [dvOK, hcs] at hok; exact hb (beq_iff_eq.mp hok)
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.and_eq_true] at hok
      rcases hok with ((h | h) | h) | ⟨h | h, -⟩
      · exact hk h
      · exact (genWf_lit hg hs).1 h
      · exact ht h
      · exact (genWf_lit hg hs).2 h
      · exact hy h
    | float _ _ _ =>
      simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hok
      exact genWf_float hg hs hok.1
  | map s' es =>
    obtain ⟨k, -, hk', -, -, -, -, rfl⟩ := sortOf_mapS_fwd hw
    rw [hco] at hk'; cases hk'
  | set s' es =>
    simp only [Semantics.sortOf] at hw
    split at hw
    · rename_i k ss hk' _; split at hw
      · cases hw; rw [hco] at hk'; cases hk'
      · cases hw
    · cases hw
  | list s' es =>
    simp only [Semantics.sortOf] at hw
    split at hw
    · rename_i k ss hk' _; split at hw
      · cases hw; rw [hco] at hk'; cases hk'
      · cases hw
    · cases hw

end

/-! ## Values as generator applications, in a model -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

theorem koreList_tr : ∀ ws : List GroundTerm, (GroundTerm.koreList c ws).map (KoreAML.tr ⟨[], []⟩) = ws.map (den c)
  | [] => by rw [GroundTerm.koreList]; rfl
  | w :: ws => by rw [GroundTerm.koreList, List.map_cons, List.map_cons, koreList_tr ws]; rfl

omit hI in
theorem koreList_tr' : ∀ ws : List GroundTerm, (GroundTerm.koreList c ws).map (KoreAML.tr ⟨[], []⟩) = ws.map (den c)
  | [] => by rw [GroundTerm.koreList]; rfl
  | w :: ws => by rw [GroundTerm.koreList, List.map_cons, List.map_cons, koreList_tr' ws]; rfl

theorem elems_all2 (e : Valuation M) : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss →
    All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x) (ws.map (den c)) (ws.map (elemOf c I))
  | [], _, _ => .nil
  | w :: ws, ss, h => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOf_cons.mp h
    exact .cons (elemOf_spec hI h1 e).1 (elems_all2 e h2)

theorem elems_sorts : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss →
    ∀ (i : Nat) x s, (ws.map (elemOf c I))[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x := by
  intro ws ss h i x s hx hs
  rw [List.getElem?_map] at hx hs
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨w', hw', hsw⟩ := sortsOf_get h hs'
  rw [hw] at hw'; cases hw'
  exact (inS_iff _).mp (elemOf_spec hI hsw KoreAML.val0).2

theorem elems_length {ws : List GroundTerm} {ss : List Srt} (h : c.sortsOf ws = some ss) :
    (ws.map (elemOf c I)).length = (ss.map c.sortName).length := by
  rw [List.length_map, List.length_map]; exact sortsOf_length h

/-- The element of a constructor value is the one its constructor builds from its arguments'. -/
theorem den_ctor_gs {f : Sym} {ws : List GroundTerm} {k : CtorSig} (hk : lookupSig c.ctorSigs f = some k)
    (hws : c.sortsOf ws = some k.args) (e : Valuation M) (m : M) :
    (den c (.ctor f ws)).interpret I e m ↔ GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m := by
  rw [den_ctor, trArgs_appList, koreList_tr hI, interp_appList_sing _ _ _ (elems_all2 hI e hws)]
  have hn := (lookupSig_spec hk).2
  unfold GS
  simp only [Gen.toK, toK, genHead, hn]
  rfl

/-- The element of a raw application of a symbol with the signature `k` is the one `k`'s generator
builds from its arguments'. -/
theorem den_sig_gs {f : Sym} {ws : List GroundTerm} {k : CtorSig} (hn : k.name = f)
    (hws : c.sortsOf ws = some k.args) (e : Valuation M) (m : M) :
    (den c (.ctor f ws)).interpret I e m ↔ GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m := by
  rw [den_ctor, trArgs_appList, koreList_tr hI, interp_appList_sing _ _ _ (elems_all2 hI e hws)]
  unfold GS
  simp only [Gen.toK, toK, genHead, hn]
  rfl

/-- The element of an injection value is the one the injection builds from its argument's. -/
theorem den_inj_gs {a b : Srt} {w : GroundTerm} (hw : c.sortOf w = some a) (e : Valuation M) (m : M) :
    (den c (.inj a b w)).interpret I e m ↔ GS I (c.sortName b) (.inj (c.sortName a)) [elemOf c I w] m := by
  rw [den_inj, interp_injApp]
  constructor
  · rintro ⟨x, hx, hm⟩; rw [(elemOf_spec hI hw e).1 x] at hx; subst hx; exact hm
  · intro hm; exact ⟨_, ((elemOf_spec hI hw e).1 _).mpr rfl, hm⟩

/-- Cons-Fun for a generator of a constructor sort, read in a model of `Γ`. -/
theorem gen_fun {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hnf : c.fnOvl g = false) {xs : List M}
    (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x) :
    ∃ y, InS I (c.sortName N) y ∧ ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ m = y :=
  fun_at (defOK hI) (sat_cons hI (Or.inl ⟨_, funItem_mem hN hgm hnf, rfl⟩)) (by rw [toK_argSorts]; exact hl)
    (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))

/-- Cons-Inj for a generator of a constructor sort with arguments, read in a model of `Γ`. -/
theorem gen_inj {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g.argSorts ≠ []) (hnf : c.fnOvl g = false)
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g) ys m) : xs = ys :=
  inj_at (defOK hI) (sat_cons hI (Or.inl ⟨_, injItem_mem hN hgm hne hnf, rfl⟩)) (by rw [toK_argSorts]; exact hl)
    (by rw [toK_argSorts]; exact hl')
    (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
    (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2)) heq

omit hI [OvlOK c] in
/-- The arguments that no overload of a generator covers in the model, read against the argument
sorts the items at uncovered arguments of a function-overloaded symbol name. -/
theorem uncE_getD {g : Gen} {bs : List String} {xs : List M}
    (h : ∀ covs, ovlArgsOf c g = some covs → UncE I covs bs xs) (hf : c.fnOvl g = true) :
    UncE I ((ovlArgsOf c g).getD []) bs xs := by
  cases g with
  | inj a => simp [Semantics.fnOvl] at hf
  | ctor k =>
    simp only [Semantics.fnOvl, Bool.and_eq_true] at hf
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hf.1.2
    have hov : ovlArgsOf c (.ctor k) = some ((c.ovlOver o).map fun kg => kg.args.map c.sortName) := by
      simp [ovlArgsOf, hf.1.1, ho]
    rw [hov]
    exact h _ hov

/-- Cons-Fun for a generator of a constructor sort, read in a model of `Γ`, at arguments that no
overload covers in the model where the generator is a function-overloaded symbol (`UncE`). -/
theorem gen_funU {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    {xs : List M}
    (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hu : c.fnOvl g = true → UncE I ((ovlArgsOf c g).getD []) (Gen.toK c g).argSorts xs) :
    ∃ y, InS I (c.sortName N) y ∧ ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ m = y := by
  cases hf : c.fnOvl g with
  | false => exact gen_fun hI hN hgm hf hl hxs
  | true =>
    exact funUnc_at (defOK hI) (sat_cons hI (Or.inl ⟨_, funUncItem_mem hN hgm hf, rfl⟩)) (by rw [toK_argSorts]; exact hl)
      (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2)) (hu hf)

/-- Cons-Inj for a generator of a constructor sort with arguments, read in a model of `Γ`, at
arguments that no overload covers in the model where the generator is a function-overloaded symbol
(`UncE`). -/
theorem gen_injU {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g.argSorts ≠ [])
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hu : c.fnOvl g = true → UncE I ((ovlArgsOf c g).getD []) (Gen.toK c g).argSorts xs)
    (hu' : c.fnOvl g = true → UncE I ((ovlArgsOf c g).getD []) (Gen.toK c g).argSorts ys)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g) ys m) : xs = ys := by
  cases hf : c.fnOvl g with
  | false => exact gen_inj hI hN hgm hne hf hl hl' hxs hys heq
  | true =>
    exact injUnc_at (defOK hI) (sat_cons hI (Or.inl ⟨_, injUncItem_mem hN hgm hne hf, rfl⟩))
      (by rw [toK_argSorts]; exact hl) (by rw [toK_argSorts]; exact hl')
      (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
      (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2)) (hu hf) (hu' hf) heq

/-- Cons-Dist for two generators of a constructor sort, not both injections, read in a model of
`Γ`: they build no element in common from arguments of their sorts. -/
theorem gen_dist {N : Srt} (hN : N ∈ consSorts c) {g g' : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hgm' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g ≠ g') (hni : ∀ a b, g = .inj a → g' = .inj b → False)
    (hgd : c.distGuarded g g' = false) (hgd' : c.distGuarded g' g = false)
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g'.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g'.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g') ys m) : False := by
  rcases mem_pairs_of hne hgm hgm' with hp | hp
  · exact dist_at (defOK hI) (sat_cons hI (Or.inl ⟨_, distItem_mem hN hp hni hgd, rfl⟩))
      (by rw [toK_argSorts]; exact hl) (by rw [toK_argSorts]; exact hl')
      (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
      (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2)) heq
  · exact dist_at (defOK hI) (sat_cons hI (Or.inl ⟨_, distItem_mem hN hp (fun a b h1 h2 => hni b a h2 h1) hgd', rfl⟩))
      (by rw [toK_argSorts]; exact hl') (by rw [toK_argSorts]; exact hl)
      (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2))
      (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2)) (fun m => (heq m).symm)

omit hI in
theorem distGuarded_symm (g g' : Gen) : c.distGuarded g g' = c.distGuarded g' g := by
  cases g <;> cases g' <;> simp only [Semantics.distGuarded]
  rename_i k k'
  have hc : (c.ovlClosure k.name).any (c.ovlClosure k'.name).contains =
      (c.ovlClosure k'.name).any (c.ovlClosure k.name).contains := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.contains_iff_mem]
    exact ⟨fun ⟨x, h1, h2⟩ => ⟨x, h2, h1⟩, fun ⟨x, h1, h2⟩ => ⟨x, h2, h1⟩⟩
  rw [hc, Bool.or_comm (c.fnOvl (.ctor k)), Bool.or_comm (c.isOvl k.name)]

/-- Cons-Dist for two generators of a constructor sort, not both injections, read in a model of
`Γ`, guarded or not: they build no element in common from arguments of their sorts that, for each
overloading generator among them, no overload covers in the model (`UncE`). -/
theorem gen_dist' {N : Srt} (hN : N ∈ consSorts c) {g g' : Gen} (hgm : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hgm' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : g ≠ g') (hni : ∀ a b, g = .inj a → g' = .inj b → False)
    {xs ys : List M} (hl : xs.length = (g.argSorts.map c.sortName).length)
    (hl' : ys.length = (g'.argSorts.map c.sortName).length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → (g.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) x s, ys[i]? = some x → (g'.argSorts.map c.sortName)[i]? = some s → InS I s x)
    (hu : ∀ covs, ovlArgsOf c g = some covs → UncE I covs (Gen.toK c g).argSorts xs)
    (hu' : ∀ covs, ovlArgsOf c g' = some covs → UncE I covs (Gen.toK c g').argSorts ys)
    (heq : ∀ m, GS I (c.sortName N) (Gen.toK c g) xs m ↔ GS I (c.sortName N) (Gen.toK c g') ys m) : False := by
  cases hgd : c.distGuarded g g' with
  | false => exact gen_dist hI hN hgm hgm' hne hni hgd (by rw [distGuarded_symm]; exact hgd) hl hl' hxs hys heq
  | true =>
    have hgd' : c.distGuarded g' g = true := by rw [distGuarded_symm]; exact hgd
    have hl1 : xs.length = (Gen.toK c g).argSorts.length := by rw [toK_argSorts]; exact hl
    have hl2 : ys.length = (Gen.toK c g').argSorts.length := by rw [toK_argSorts]; exact hl'
    rcases mem_pairs_of hne hgm hgm' with hp | hp
    · have hsp := listVal_split xs ys _ _ hl1 hl2
      exact distUnc_at (defOK hI) (sat_cons hI (Or.inl ⟨_, distUncItem_mem hN hp hni hgd, rfl⟩)) hl1 hl2
        (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun covs hc m => uncoveredP_of (defOK hI) hsp.1
          (not_mem_xs (off := 0) (n := (Gen.toK c g).argSorts.length)
            (k := (Gen.toK c g).argSorts.length + (Gen.toK c g').argSorts.length + 1) (by omega)) (hu covs hc) m)
        (fun covs hc m => uncoveredP_of (defOK hI) hsp.2
          (not_mem_xs (off := (Gen.toK c g).argSorts.length) (n := (Gen.toK c g').argSorts.length)
            (k := (Gen.toK c g).argSorts.length + (Gen.toK c g').argSorts.length + 1) (by omega))
          (hu' covs hc) m) heq
    · have hsp := listVal_split ys xs _ _ hl2 hl1
      exact distUnc_at (defOK hI) (sat_cons hI (Or.inl ⟨_, distUncItem_mem hN hp (fun a b h1 h2 => hni b a h2 h1) hgd',
          rfl⟩)) hl2 hl1
        (fun i x s h1 h2 => hys i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun i x s h1 h2 => hxs i x s h1 (by rw [← toK_argSorts]; exact h2))
        (fun covs hc m => uncoveredP_of (defOK hI) hsp.1
          (not_mem_xs (off := 0) (n := (Gen.toK c g').argSorts.length)
            (k := (Gen.toK c g').argSorts.length + (Gen.toK c g).argSorts.length + 1) (by omega)) (hu' covs hc) m)
        (fun covs hc m => uncoveredP_of (defOK hI) hsp.2
          (not_mem_xs (off := (Gen.toK c g').argSorts.length) (n := (Gen.toK c g).argSorts.length)
            (k := (Gen.toK c g').argSorts.length + (Gen.toK c g).argSorts.length + 1) (by omega))
          (hu covs hc) m)
        (fun m => (heq m).symm)

/-- Cons-Coh between generator sets: for `x` of `A'` and `y` the element `inj{A',A}(x)`,
`inj{A,B}(y)` and `inj{A',B}(x)` build the same elements. -/
theorem coh_gs {a' a b : Srt} (h1 : (a', a) ∈ c.subsorts) (h2 : (a, b) ∈ c.subsorts) {x y : M}
    (hx : InS I (c.sortName a') x) (hy : ∀ m, GS I (c.sortName a) (.inj (c.sortName a')) [x] m ↔ m = y) (m : M) :
    GS I (c.sortName b) (.inj (c.sortName a)) [y] m ↔ GS I (c.sortName b) (.inj (c.sortName a')) [x] m := by
  have hX : ∀ m, (Pattern.evar ⟨1⟩ : KoreAML.P).interpret I (listVal [x]) m ↔ m = x := fun m => by
    rw [KoreAML.interp_evar, listVal_at]; rfl
  have h := coh_at hI h1 h2 hX ((inS_iff _).mpr hx) m
  rw [interp_injApp, interp_injApp] at h
  simp only [interp_injApp, hX, exists_eq_left] at h
  constructor
  · intro hm; exact h.mp ⟨y, (hy y).mpr rfl, hm⟩
  · intro hm; obtain ⟨y', hy', hm'⟩ := h.mpr hm; rw [(hy y').mp hy'] at hm'; exact hm'

end

theorem sortsOf_nil_eq {c : Semantics} {ws : List GroundTerm} (h : c.sortsOf ws = some []) : ws = [] := by
  cases ws with
  | nil => rfl
  | cons w ws => obtain ⟨_, _, _, _, h'⟩ := sortsOf_cons.mp h; cases h'

theorem mem_lowerBounds {c : Semantics} {a b x : Srt} (h : x ∈ c.lowerBounds a b) :
    (x, a) ∈ c.subsorts ∧ (x, b) ∈ c.subsorts := by
  unfold Semantics.lowerBounds at h
  rw [mem_sortBy] at h
  have := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true, List.contains_iff_mem] at this
  exact this

theorem injNormal_isInj (a b : Srt) (w : GroundTerm) : (injNormal a b w).isInj = true := by
  cases w <;> rfl

theorem injNormal_of_not {a b : Srt} {w : GroundTerm} (h : w.isInj = false) : injNormal a b w = .inj a b w := by
  cases w with
  | inj => cases h
  | _ => rfl

/-! ## Distinct values are distinct elements -/

/-- A value of K, KItem or a sort below KItem, as a value of K: itself, or `kseq(·, dotk)` of its
injection into KItem. -/
def wrapK (s : Srt) (v : GroundTerm) : GroundTerm :=
  if s = Srt.k then v else .ctor kseq [if s = Srt.kitem then v else injNormal s Srt.kitem v, .ctor dotk []]

theorem lookup_kseq (c : Semantics) : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩ := by
  rw [lookupSig_eq]; rfl

theorem lookup_dotk (c : Semantics) : lookupSig c.ctorSigs dotk = some ⟨dotk, [], Srt.k⟩ := by
  rw [lookupSig_eq]; rfl

theorem kitem_sub {c : Semantics} {s : Srt} (h : s ∈ c.sortsBelowKItem) : (s, Srt.kitem) ∈ c.subsorts :=
  List.mem_append_right _ (List.mem_map.mpr ⟨s, h, rfl⟩)

/-- The sorts that `wrapK` takes to K. -/
def BelowK (c : Semantics) (s : Srt) : Prop := s = Srt.k ∨ s = Srt.kitem ∨ s ∈ c.sortsBelowKItem

theorem sortOf_wrapK {c : Semantics} (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {s : Srt} (hs : BelowK c s) {v : GroundTerm} (hv : c.sortOf v = some s) : c.sortOf (wrapK s v) = some Srt.k := by
  unfold wrapK
  split
  · rename_i h; subst h; exact hv
  · rename_i hk
    have hx : c.sortOf (if s = Srt.kitem then v else injNormal s Srt.kitem v) = some Srt.kitem := by
      split
      · rename_i h; subst h; exact hv
      · rename_i hki
        have hb : s ∈ c.sortsBelowKItem := by
          rcases hs with h | h | h
          · exact absurd h hk
          · exact absurd h hki
          · exact h
        exact sortOf_injNormal htr (kitem_sub hb) hv
    refine sortOf_ctor_intro ⟨_, lookup_kseq c, ?_, rfl⟩
    exact sortsOf_cons.mpr ⟨_, _, hx, sortsOf_cons.mpr ⟨_, _, sortOf_ctor_intro ⟨_, lookup_dotk c, sortsOf_nil, rfl⟩,
      sortsOf_nil, rfl⟩, rfl⟩

theorem injNormal_inj {c : Semantics} (hg : genWf c = true) [OvlOK c] {s b : Srt} {v w : GroundTerm}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s) (h : injNormal s b v = injNormal s b w) : v = w := by
  cases hvi : v.isInj <;> cases hwi : w.isInj
  · rw [injNormal_of_not hvi, injNormal_of_not hwi] at h; injection h
  · exfalso
    cases w with
    | inj a s' w0 =>
      obtain ⟨has, -, -, rfl⟩ := sortOf_inj.mp hw
      rw [injNormal_of_not hvi] at h
      injection h with h1
      exact (genWf_sub hg has).2 h1.symm
    | _ => cases hwi
  · exfalso
    cases v with
    | inj a s' v0 =>
      obtain ⟨has, -, -, rfl⟩ := sortOf_inj.mp hv
      rw [injNormal_of_not hwi] at h
      injection h with h1
      exact (genWf_sub hg has).2 h1
    | _ => cases hvi
  · cases v with
    | inj a s' v0 =>
      cases w with
      | inj a' s'' w0 =>
        obtain ⟨-, -, -, rfl⟩ := sortOf_inj.mp hv
        obtain ⟨-, -, -, h'⟩ := sortOf_inj.mp hw
        subst h'
        injection h with h1 _ h3
        rw [h1, h3]
      | _ => cases hwi
    | _ => cases hvi

theorem wrapK_inj {c : Semantics} (hg : genWf c = true) [OvlOK c] {s : Srt} {v w : GroundTerm}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s) (h : wrapK s v = wrapK s w) : v = w := by
  unfold wrapK at h
  split at h
  · exact h
  · injection h with _ h
    injection h with h _
    split at h
    · exact h
    · exact injNormal_inj hg hv hw h

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- The graph of `_==K_` at two values of K. -/
theorem eqK_den {u u' : GroundTerm} (hu : c.sortOf u = some Srt.k) (hu' : c.sortOf u' = some Srt.k)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c kEq (GroundTerm.koreList c [u, u']))).interpret I e m ↔
      (den c (bool (GroundTerm.cmp u u' == .eq))).interpret I e m := by
  have hk : (⟨kEq, [Srt.k, Srt.k], Srt.bool⟩ : CtorSig) ∈ hookSigs := by decide
  have hax := sat_dom hI (Or.inl ⟨_, [u, u'], some (bool (GroundTerm.cmp u u' == .eq)), hk,
    sortsOf_cons.mpr ⟨_, _, hu, sortsOf_cons.mpr ⟨_, _, hu', sortsOf_nil, rfl⟩, rfl⟩, rfl, (by intro h; cases h), rfl⟩)
  exact (KoreAML.interp_equal (defOK hI)).mp (hax e default) m

omit hI in
theorem eqK_congr {u u' : GroundTerm} {e : Valuation M} (h : ∀ m, (den c u).interpret I e m ↔ (den c u').interpret I e m)
    (m : M) :
    (KoreAML.den (symApp c kEq (GroundTerm.koreList c [u, u']))).interpret I e m ↔
      (KoreAML.den (symApp c kEq (GroundTerm.koreList c [u, u]))).interpret I e m := by
  unfold KoreAML.den
  rw [tr_symApp, tr_symApp]
  simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  exact KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => (h m).symm) m

/-- The distinctness axiom of `Γ`: distinct values of a sort of `distinctSorts` share no element. -/
theorem dom_apart {s : Srt} (hs : (distinctSorts c).contains s = true) {v w : GroundTerm}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s) (hne : v ≠ w) (e : Valuation M) (m : M) :
    ¬ ((den c v).interpret I e m ∧ (den c w).interpret I e m) := by
  have hax := sat_dom hI (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, w, s, hs, hv, hw,
    fun h => hne (GroundTerm.cmp_eq _ _ h), rfl⟩))))
  have := hax e m
  rw [interpret_neg, interpret_conj] at this
  exact this

omit hI in
theorem float_distinct : Srt.float ∈ distinctSorts c :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))

omit hI in
theorem string_distinct : Srt.string ∈ distinctSorts c :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))

omit hI in
theorem bytes_distinct : Srt.bytes ∈ distinctSorts c :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))

omit hI in
theorem int_distinct : Srt.int ∈ distinctSorts c :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)))

omit hI in
theorem bool_distinct : Srt.bool ∈ distinctSorts c :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

omit hI in
theorem apart_of_distinct {x : Srt} (hx : x ∈ distinctSorts c) : apartSort c x = true := by
  simp only [apartSort, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr hx)

omit hI in
theorem coll_distinct {s : Srt} {k : CollSig} (hk : c.collOf s = some k) : s ∈ distinctSorts c := by
  unfold Semantics.collOf at hk
  have hm := List.mem_of_find?_eq_some hk
  have hs := List.find?_some hk
  simp only [beq_iff_eq] at hs
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, hm, hs⟩))

omit hI in
/-- A sort hooked to a library carrier is a distinct sort. -/
theorem carrier_distinct {s : Srt} (h : ¬ c.lib.carriers.all (·.1 != s) = true) : s ∈ distinctSorts c := by
  refine Classical.byContradiction fun hn => h ?_
  rw [List.all_eq_true]; intro p hp
  have : p.1 ≠ s := fun he => hn (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, he⟩))
  simpa using this

/-- An injection of a value, normalised, builds the element the injection builds from the
value's element. -/
theorem den_injNormal_gs (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {s b : Srt} (hsb : (s, b) ∈ c.subsorts) {v : GroundTerm} (hv : c.sortOf v = some s) (e : Valuation M) (m : M) :
    (den c (injNormal s b v)).interpret I e m ↔ GS I (c.sortName b) (.inj (c.sortName s)) [elemOf c I v] m := by
  cases hvi : v.isInj
  · rw [injNormal_of_not hvi]; exact den_inj_gs hI hv e m
  · cases v with
    | inj a0 s' v0 =>
      obtain ⟨has0, hni, hv0, rfl⟩ := sortOf_inj.mp hv
      show (den c (.inj a0 b v0)).interpret I e m ↔ _
      rw [den_inj_gs hI hv0]
      have hx0 : InS I (c.sortName a0) (elemOf c I v0) := (inS_iff _).mp (elemOf_spec hI hv0 KoreAML.val0).2
      exact (coh_gs hI has0 hsb hx0 (fun m => by
        rw [← den_inj_gs hI hv0 KoreAML.val0 m]; exact (elemOf_spec hI hv KoreAML.val0).1 m) m).symm
    | _ => cases hvi

theorem den_wrapK_congr (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {s : Srt} (hs : BelowK c s) {v w : GroundTerm} (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (he : elemOf c I v = elemOf c I w) (e : Valuation M) (m : M) :
    (den c (wrapK s v)).interpret I e m ↔ (den c (wrapK s w)).interpret I e m := by
  have hvw : ∀ m, (den c v).interpret I e m ↔ (den c w).interpret I e m := fun m => by
    rw [(elemOf_spec hI hv e).1, (elemOf_spec hI hw e).1, he]
  unfold wrapK
  split
  · exact hvw m
  · rename_i hk
    rw [den_ctor, den_ctor]
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    refine KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => ?_)) (fun _ => Iff.rfl) m
    show (den c _).interpret I e m ↔ (den c _).interpret I e m
    split
    · exact hvw m
    · rename_i hki
      have hb : s ∈ c.sortsBelowKItem := by
        rcases hs with h | h | h
        · exact absurd h hk
        · exact absurd h hki
        · exact h
      rw [den_injNormal_gs hI htr (kitem_sub hb) hv, den_injNormal_gs hI htr (kitem_sub hb) hw, he]

/-- **Distinct values are distinct elements**, at a sort that is `apartSort`. -/
theorem values_apart (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {s : Srt} (hap : apartSort c s = true) {v w : GroundTerm} (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (he : elemOf c I v = elemOf c I w) : v = w := by
  refine Classical.byContradiction fun hne => ?_
  have key : BelowK c s → False := by
    intro hs
    have hwv := sortOf_wrapK htr hs hv
    have hww := sortOf_wrapK htr hs hw
    have hne' : GroundTerm.cmp (wrapK s v) (wrapK s w) ≠ .eq := fun h =>
      hne (wrapK_inj hg hv hw (GroundTerm.cmp_eq _ _ h))
    have hset := den_wrapK_congr hI htr hs hv hw he KoreAML.val0
    have h3 : (GroundTerm.cmp (wrapK s v) (wrapK s w) == .eq) = false := by
      cases h : GroundTerm.cmp (wrapK s v) (wrapK s w) with
      | eq => exact absurd h hne'
      | lt => rfl
      | gt => rfl
    have hb : ∀ m, (den c (bool false)).interpret I KoreAML.val0 m ↔
        (den c (bool true)).interpret I KoreAML.val0 m := by
      intro m
      have h1 := eqK_den hI hwv hww KoreAML.val0 m
      have h2 := eqK_den hI hwv hwv KoreAML.val0 m
      rw [GroundTerm.cmp_refl] at h2
      have h2 : _ ↔ (den c (bool true)).interpret I KoreAML.val0 m := h2
      rw [h3] at h1
      rw [← h1, ← h2]
      exact eqK_congr hset m
    have ht := elemOf_spec hI (sortOf_bool (c := c) true) KoreAML.val0
    exact dom_apart hI (List.contains_iff_mem.mpr bool_distinct) (sortOf_bool false) (sortOf_bool true)
      (by intro h; cases h) KoreAML.val0 (elemOf c I (bool true))
      ⟨(hb _).mpr ((ht.1 _).mpr rfl), (ht.1 _).mpr rfl⟩
  unfold apartSort at hap
  simp only [Bool.or_eq_true, beq_iff_eq] at hap
  rcases hap with ((hK | hKI) | hB) | hD'
  · exact key (Or.inl hK)
  · exact key (Or.inr (Or.inl hKI))
  · exact key (Or.inr (Or.inr (List.contains_iff_mem.mp hB)))
  · exact dom_apart hI hD' hv hw hne KoreAML.val0 (elemOf c I v)
      ⟨((elemOf_spec hI hv _).1 _).mpr rfl, ((elemOf_spec hI hw _).1 _).mpr he⟩

omit hI in
/-- Every sort a value has is `apartSort`. -/
theorem apartSort_of_sorted (hg : genWf c = true) [OvlOK c] {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    apartSort c s = true := by
  cases v with
  | ctor f ws =>
    exact (genWf_cons hg (ctor_sort_cons hg hv)).1
  | inj a b w =>
    obtain ⟨hab, -, -, rfl⟩ := sortOf_inj.mp hv
    exact (genWf_cons hg (genWf_sub hg hab).1).1
  | dv s' lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hv
    by_cases hcar : c.lib.carriers.all (·.1 != s) = false
    · exact apart_of_distinct (carrier_distinct (by rw [hcar]; exact Bool.false_ne_true))
    have hcs := Lib.carrier_of_not _ (by rw [Bool.not_eq_false] at hcar; exact hcar)
    cases lit with
    | int _ => simp only [dvOK, hcs] at hok; rw [beq_iff_eq.mp hok]; exact apart_of_distinct int_distinct
    | bool _ => simp only [dvOK, hcs] at hok; rw [beq_iff_eq.mp hok]; exact apart_of_distinct bool_distinct
    | float _ _ _ =>
      simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1]; exact apart_of_distinct float_distinct
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.and_eq_true] at hok
      rcases hok with ((h | h) | h) | ⟨h | h, -⟩
      · rw [h]; exact genWf_kcv
      · rw [h]; exact apart_of_distinct string_distinct
      · exact apart_of_distinct (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
      · rw [h]; exact apart_of_distinct bytes_distinct
      · exact apart_of_distinct (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
  | map s' es =>
    obtain ⟨k, -, hk, -, -, -, -, rfl⟩ := sortOf_mapS_fwd hv
    exact apart_of_distinct (coll_distinct hk)
  | set s' es =>
    simp only [Semantics.sortOf] at hv
    split at hv
    · rename_i k ss hk _; split at hv
      · cases hv; exact apart_of_distinct (coll_distinct hk)
      · cases hv
    · cases hv
  | list s' es =>
    simp only [Semantics.sortOf] at hv
    split at hv
    · rename_i k ss hk _; split at hv
      · cases hv; exact apart_of_distinct (coll_distinct hk)
      · cases hv
    · cases hv

end

/-! ## Reading a value downwards -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hg : genWf c = true)
include hI hg

omit hI hg [OvlOK c] in
/-- An injection, normalised, of a value of `A` lies in `A`. -/
theorem lies_injNormal {A B : Srt} {w : GroundTerm} (hw : c.sortOf w = some A) : c.lies A B (injNormal A B w) = true := by
  cases w with
  | inj C A' x =>
    obtain ⟨h1, -, -, rfl⟩ := sortOf_inj.mp hw
    simp [injNormal, Semantics.lies, Semantics.le, h1]
  | _ => simp [injNormal, Semantics.lies, Semantics.le]

/-- **The arguments of a raw overloading value are uncovered in a model**, where every injection's
image at an argument is the injection of a value of its source sort (`hback`, which `inj_back`
gives): no overload covers them as values, and its sorts are named apart (`OvlOK`). -/
theorem uncE_of_value (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {g : Sym} {o : OvlSig} {ws : List GroundTerm} (hlo : c.lookupOvl g = some o)
    (hws : c.sortsOf ws = some o.sig.args) (hu : c.uncovered g ws = true)
    (hback : ∀ u ∈ ws, ∀ (A B : Srt), (A, B) ∈ c.subsorts → c.sortOf u = some B → ∀ (y : M),
      InS I (c.sortName A) y → GS I (c.sortName B) (.inj (c.sortName A)) [y] (elemOf c I u) → c.lies A B u = true) :
    ∀ covs, ovlArgsOf c (.ctor o.sig) = some covs →
      UncE I covs (Gen.toK c (.ctor o.sig)).argSorts (ws.map (elemOf c I)) := by
  have H : OvlLaws.OvlHyp c := OvlOK.hyp inferInstance htr
  obtain ⟨hom, hn, hio, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts hlo
  intro covs hcov
  simp only [ovlArgsOf, hn, hio, ↓reduceIte, hlo, Option.map_some, Option.some.injEq] at hcov
  subst hcov
  intro as has
  obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp has
  obtain ⟨hlen, hle, -, -⟩ := OvlLaws.over_ovlF H.fnFacts hlo hkg
  have hwl : ws.length = o.sig.args.length := sortsOf_length hws
  have hnc : c.ovlCovers o.sig kg ws = false := by
    simp only [Semantics.uncovered, hlo, List.all_eq_true, Bool.not_eq_true'] at hu
    exact hu kg hkg
  have hall : ¬ ((kg.args.zip o.sig.args).zip ws).all (fun ((A, B), v) => c.lies A B v) = true := fun h => by
    rw [OvlLaws.covers_iff.mpr ⟨hlen, hwl, h⟩] at hnc; cases hnc
  rw [OvlLaws.zip3_all_iff] at hall
  obtain ⟨i, h1, h2, h3, hli⟩ : ∃ i, ∃ h1 : i < kg.args.length, ∃ h2 : i < o.sig.args.length,
      ∃ h3 : i < ws.length, c.lies kg.args[i] o.sig.args[i] ws[i] ≠ true :=
    Classical.byContradiction fun hc => hall fun i h1 h2 h3 =>
      Classical.byContradiction fun hl => hc ⟨i, h1, h2, h3, hl⟩
  have hAB : kg.args[i] ≠ o.sig.args[i] := fun h => hli (h ▸ OvlLaws.lies_self _ _)
  have hsub : (kg.args[i], o.sig.args[i]) ∈ c.subsorts :=
    OvlLaws.mem_of_le ((OvlLaws.zip2_all_iff.mp hle) i h1 h2) hAB
  obtain ⟨u, hu', hsu⟩ := sortsOf_get hws (List.getElem?_eq_getElem h2)
  rw [List.getElem?_eq_getElem h3] at hu'
  cases hu'
  refine ⟨i, c.sortName kg.args[i], c.sortName o.sig.args[i], elemOf c I ws[i], by simp [h1], by
    show (o.sig.args.map c.sortName)[i]? = _
    simp [h2], fun he => hAB ((inferInstance : OvlOK c).names o hom kg hkg _
      (List.mem_cons_of_mem _ (List.getElem_mem h1)) _ (List.mem_cons_of_mem _ (List.getElem_mem h2)) he),
    by simp [h3], ?_⟩
  rintro ⟨y, hy, hm⟩
  exact hli (hback _ (List.getElem_mem h3) _ _ hsub hsu y hy hm)

/-- **An injection's image at a value.** If the element of a value of sort `s` lies in what
`inj{a,s}` builds from an element `b` of `a`, the value is the injection of a value of `a` whose
element is `b` (normalised: an injection of an injection is the injection from the inner sort). -/
theorem inj_back (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) :
    ∀ (w : GroundTerm) {a s : Srt}, (a, s) ∈ c.subsorts → c.sortOf w = some s →
    ∀ {b : M}, InS I (c.sortName a) b → GS I (c.sortName s) (.inj (c.sortName a)) [b] (elemOf c I w) →
    ∃ w', c.sortOf w' = some a ∧ w = injNormal a s w' ∧ b = elemOf c I w'
  | .inj a0 s' w0, a, s, has, hsw, b, hb, hm => by
    have hN := (genWf_sub hg has).1
    obtain ⟨y, -, hy⟩ := gen_fun hI hN (gensF_inj has) rfl (xs := [b]) rfl (single_sorts hb)
    have hset : ∀ m, GS I (c.sortName s) (.inj (c.sortName a)) [b] m ↔ m = elemOf c I (.inj a0 s' w0) :=
      fun m => by rw [show (.inj (c.sortName a) : KoreAML.Gen) = Gen.toK c (.inj a) from rfl, hy, ((hy _).mp hm)]
    obtain ⟨has0, hni, hw0, rfl⟩ := sortOf_inj.mp hsw
    have hx0 : InS I (c.sortName a0) (elemOf c I w0) := (inS_iff _).mp (elemOf_spec hI hw0 KoreAML.val0).2
    have hvset : ∀ m, GS I (c.sortName s) (.inj (c.sortName a0)) [elemOf c I w0] m ↔ m = elemOf c I (.inj a0 s w0) :=
      fun m => by rw [← den_inj_gs hI hw0 KoreAML.val0 m]; exact (elemOf_spec hI hsw KoreAML.val0).1 m
    by_cases h0 : a0 = a
    · subst h0
      have := gen_inj hI hN (gensF_inj has) (by simp [Gen.argSorts]) rfl (xs := [b]) (ys := [elemOf c I w0]) rfl rfl
        (single_sorts hb) (single_sorts hx0) (fun m => by
          show GS I _ (.inj _) _ m ↔ GS I _ (.inj _) _ m
          rw [hset, hvset])
      exact ⟨w0, hw0, (injNormal_of_not hni).symm, by simpa using this⟩
    by_cases h1 : (a0, a) ∈ c.subsorts
    · have hw' : c.sortOf (.inj a0 a w0) = some a := sortOf_inj.mpr ⟨h1, hni, hw0, rfl⟩
      have hy1 : ∀ m, GS I (c.sortName a) (.inj (c.sortName a0)) [elemOf c I w0] m ↔ m = elemOf c I (.inj a0 a w0) :=
        fun m => by rw [← den_inj_gs hI hw0 KoreAML.val0 m]; exact (elemOf_spec hI hw' KoreAML.val0).1 m
      have hc := coh_gs hI h1 has hx0 hy1
      have := gen_inj hI hN (gensF_inj has) (by simp [Gen.argSorts]) rfl (xs := [b]) (ys := [elemOf c I (.inj a0 a w0)]) rfl rfl
        (single_sorts hb) (single_sorts ((inS_iff _).mp (elemOf_spec hI hw' KoreAML.val0).2)) (fun m => by
          show GS I _ (.inj _) _ m ↔ GS I _ (.inj _) _ m
          rw [hset, hc, hvset])
      exact ⟨.inj a0 a w0, hw', rfl, by simpa using this⟩
    by_cases h2 : (a, a0) ∈ c.subsorts
    · exfalso
      have hN0 := (genWf_sub hg h2).1
      obtain ⟨y2, hy2s, hy2⟩ := gen_fun hI hN0 (gensF_inj h2) rfl (xs := [b]) rfl (single_sorts hb)
      have hc := coh_gs hI h2 has0 hb hy2
      have := gen_inj hI hN (gensF_inj has0) (by simp [Gen.argSorts]) rfl (xs := [y2]) (ys := [elemOf c I w0]) rfl rfl
        (single_sorts hy2s) (single_sorts hx0) (fun m => by
          show GS I _ (.inj _) _ m ↔ GS I _ (.inj _) _ m
          rw [hc, hset, hvset])
      have hy2w : y2 = elemOf c I w0 := by simpa using this
      obtain ⟨w'', -, hw'', -⟩ := inj_back htr w0 h2 hw0 hb (by
        show GS I _ (Gen.toK c (.inj a)) _ _
        rw [hy2, hy2w])
      have := injNormal_isInj a a0 w''
      rw [← hw''] at this; rw [hni] at this; cases this
    · exfalso
      have hle : (c.le a0 a || c.le a a0) = false := by
        simp only [Semantics.le, Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_iff_mem]
        exact ⟨⟨h0, by simpa using h1⟩, ⟨fun h => h0 h.symm, by simpa using h2⟩⟩
      have hle' : (c.le a a0 || c.le a0 a) = false := by rw [Bool.or_comm]; exact hle
      have hseq : ∀ m, GS I (c.sortName s) (.inj (c.sortName a0)) [elemOf c I w0] m ↔
          GS I (c.sortName s) (.inj (c.sortName a)) [b] m := fun m => by rw [hset, hvset]
      have hdist : ∀ (C : Srt) (z : M), (C, a0) ∈ c.subsorts → InS I (c.sortName C) z →
          (∀ m, GS I (c.sortName a0) (.inj (c.sortName C)) [z] m ↔ m = elemOf c I w0) → False := by
        intro C z hC hz hzs
        obtain ⟨w'', -, hw'', -⟩ := inj_back htr w0 hC hw0 hz (by rw [hzs])
        have := injNormal_isInj C a0 w''
        rw [← hw''] at this; rw [hni] at this; cases this
      rcases mem_pairs_of (fun h => h0 (by cases h; rfl)) (gensF_inj has0) (gensF_inj has) with hp | hp
      · rcases injPair_mem hN hp hle with ⟨-, hit⟩ | ⟨-, hit⟩
        · exact dist_at (defOK hI) (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [elemOf c I w0]) (ys := [b]) rfl rfl
            (single_sorts hx0) (single_sorts hb) hseq
        · obtain ⟨C, hC, z, hz, hz1, -⟩ := distLb_at (defOK hI) (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) hx0 hb hseq
          obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
          exact hdist C' z (mem_lowerBounds hC').1 hz hz1
      · rcases injPair_mem hN hp hle' with ⟨-, hit⟩ | ⟨-, hit⟩
        · exact dist_at (defOK hI) (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [b]) (ys := [elemOf c I w0]) rfl rfl
            (single_sorts hb) (single_sorts hx0) (fun m => (hseq m).symm)
        · obtain ⟨C, hC, z, hz, -, hz2⟩ := distLb_at (defOK hI) (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) hb hx0
            (fun m => (hseq m).symm)
          obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
          exact hdist C' z (mem_lowerBounds hC').2 hz hz2
  | .ctor g ws, a, s, has, hsw, b, hb, hm => by
    exfalso
    have hN := (genWf_sub hg has).1
    obtain ⟨y, -, hy⟩ := gen_fun hI hN (gensF_inj has) rfl (xs := [b]) rfl (single_sorts hb)
    have hset : ∀ m, GS I (c.sortName s) (Gen.toK c (.inj a)) [b] m ↔ m = elemOf c I (.ctor g ws) :=
      fun m => by rw [hy, ((hy _).mp hm)]
    rcases sortOf_ctor_cases hg hsw with ⟨kg, hkg, hws, hres⟩ | ⟨o, hlo, -, hws, hu, hres, -⟩ |
      ⟨kp, hko, -, -, -, -, hres, -⟩
    rotate_right
    · -- an open generator's sort has no subsort pair below it (`genWf`'s flat conjunct)
      obtain ⟨hpm, hpr, -, -⟩ := c.lookupOpen_spec hko
      exact genWf_flat_sub hg hpm hpr has hres
    rotate_left
    · obtain ⟨hom, hn, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
      have hvset : ∀ m, GS I (c.sortName s) (Gen.toK c (.ctor o.sig)) (ws.map (elemOf c I)) m ↔
          m = elemOf c I (.ctor g ws) := fun m => by
        rw [hres, ← den_sig_gs hI hn hws KoreAML.val0 m]; exact (elemOf_spec hI hsw KoreAML.val0).1 m
      exact gen_dist' hI hN (gensF_inj has) (by rw [hres]; exact gensF_of_ovl hg hom) (fun h => by cases h)
        (fun _ _ _ h => by cases h) rfl (elems_length hI hws) (single_sorts hb) (elems_sorts hI hws)
        (fun covs h => by simp [ovlArgsOf] at h)
        (uncE_of_value hI hg htr hlo hws hu fun u hu' A B hAB hsu y hy hmy => by
          have _hlt := List.sizeOf_lt_of_mem hu'
          obtain ⟨w', hw', rfl, -⟩ := inj_back htr u hAB hsu hy hmy
          exact lies_injNormal hw')
        (fun m => by rw [hset, hvset])
    obtain ⟨hkgm, -⟩ := lookupSig_spec hkg
    have hvset : ∀ m, GS I (c.sortName kg.result) (Gen.toK c (.ctor kg)) (ws.map (elemOf c I)) m ↔
        m = elemOf c I (.ctor g ws) := fun m => by
      rw [← den_ctor_gs hI hkg hws KoreAML.val0 m]; exact (elemOf_spec hI hsw KoreAML.val0).1 m
    rw [← hres] at hvset
    exact gen_dist hI hN (gensF_inj has) (by rw [hres]; exact gensF_ctor hg hkgm) (fun h => by cases h)
      (fun _ _ _ h => by cases h)
      (distGuarded_ctorSigs (fun _ h => by cases h) (fun _ h => by cases h; exact hkgm))
      (distGuarded_ctorSigs (fun _ h => by cases h; exact hkgm) (fun _ h => by cases h)) rfl (elems_length hI hws) (single_sorts hb)
      (elems_sorts hI hws) (fun m => by rw [hset, hvset])
  | .dv s' lit, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | .map s' es, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | .set s' es, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | .list s' es, a, s, has, hsw, _, _, _ => by
    exfalso
    rcases consSort_shape hg (genWf_sub hg has).1 hsw with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  termination_by w => w
  decreasing_by all_goals (simp_wf; omega)


/-- **A constructor's image at a value.** If the element of a value lies in what the constructor
`f` builds from elements of its argument sorts, the value is `f` applied to values whose elements
those are. -/
theorem ctor_back (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {k : CtorSig} (hk : lookupSig c.ctorSigs f = some k)
    {w : GroundTerm} (hsw : c.sortOf w = some k.result) {bs : List M}
    (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs (elemOf c I w)) :
    ∃ ws, w = .ctor f ws ∧ c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I) := by
  obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
  have hN := genWf_ctor hg hkm
  have hgk := gensF_ctor hg hkm
  obtain ⟨y, -, hy⟩ := gen_fun hI hN hgk (fnOvl_ctorSigs hkm) hbl hbs
  have hyw : y = elemOf c I w := ((hy _).mp hm).symm
  have hset : ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs m ↔ m = elemOf c I w := fun m => by
    rw [hy, hyw]
  have hwe := (elemOf_spec hI hsw KoreAML.val0).1
  rcases consSort_shape hg hN hsw with ⟨g, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
  · rcases sortOf_ctor_cases hg hsw with ⟨kg, hkg, hws, hres⟩ | ⟨o, hlo, hio, hws, hu, hres, -⟩ |
      ⟨kp, hko, hgn, -, -, -, hres, -⟩
    rotate_right
    · -- an open generator's application: the constructor k of its sort has no argument
      -- (`genWf`'s flat conjunct), so the element is the one of the value `f()`, and distinct
      -- values of a constructor sort are distinct elements (`values_apart`)
      exfalso
      obtain ⟨hpm, hpr, -, -⟩ := c.lookupOpen_spec hko
      have hka : k.args = [] := genWf_flat_ctor hg hpm hpr hkm hres
      have hb0 : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hbl, hka]; rfl)
      subst hb0
      have hn0 : c.sortsOf [] = some k.args := by rw [hka]; exact sortsOf_nil
      have hfs : c.sortOf (.ctor f []) = some k.result := sortOf_ctor_intro ⟨k, hk, hn0, rfl⟩
      have h2 := (den_ctor_gs hI hk hn0 KoreAML.val0 _).mp (((elemOf_spec hI hfs KoreAML.val0).1 _).mpr rfl)
      have he : elemOf c I (.ctor f []) = elemOf c I (.ctor g ws) := (hset _).mp h2
      have hfg := values_apart hI hg htr (genWf_cons hg hN).1 hfs hsw he
      injection hfg with hfg
      subst hfg
      rw [hk] at hgn; cases hgn
    rotate_left
    · exfalso
      obtain ⟨hom, hn, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
      have hgf : g ≠ f := fun h => by
        have := (c.isOvl_parts hio).1
        rw [h] at this
        simp [Semantics.isCtor, hk] at this
      have hvset : ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor o.sig)) (ws.map (elemOf c I)) m ↔
          m = elemOf c I (.ctor g ws) := fun m => by
        rw [hres, ← den_sig_gs hI hn hws KoreAML.val0 m]; exact hwe m
      exact gen_dist' hI hN hgk (by rw [hres]; exact gensF_of_ovl hg hom)
        (fun h => by cases h; exact hgf (hn.symm.trans hkn))
        (fun _ _ h _ => by cases h) hbl (elems_length hI hws) hbs (elems_sorts hI hws)
        (fun covs h => by simp [ovlArgsOf, isOvl_of_ctorSigs hkm] at h)
        (uncE_of_value hI hg htr hlo hws hu fun u hu' A B hAB hsu y hy hmy => by
          obtain ⟨w', hw', rfl, -⟩ := inj_back hI hg htr u hAB hsu hy hmy
          exact lies_injNormal hw')
        (fun m => by rw [hset, hvset])
    obtain ⟨hkgm, hkgn⟩ := lookupSig_spec hkg
    have hvset : ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor kg)) (ws.map (elemOf c I)) m ↔
        m = elemOf c I (.ctor g ws) := fun m => by
      rw [hres, ← den_ctor_gs hI hkg hws KoreAML.val0 m]; exact hwe m
    by_cases hgf : g = f
    · subst hgf
      rw [hk] at hkg; cases hkg
      refine ⟨ws, rfl, hws, ?_⟩
      by_cases hne : k.args = []
      · have h1 : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hbl, hne]; rfl)
        rw [hne] at hws
        rw [h1, sortsOf_nil_eq hws]; rfl
      · exact gen_inj hI hN hgk hne (fnOvl_ctorSigs hkm) hbl (elems_length hI hws) hbs (elems_sorts hI hws)
          (fun m => by rw [hset, hvset])
    · exfalso
      have hgm' : Gen.ctor kg ∈ (c.gens k.result).filter (!c.isOpenGen ·) := by rw [hres]; exact gensF_ctor hg hkgm
      exact gen_dist hI hN hgk hgm' (fun h => by cases h; exact hgf (hkgn.symm.trans hkn))
        (fun _ _ h _ => by cases h)
        (distGuarded_ctorSigs (fun _ h => by cases h; exact hkm) (fun _ h => by cases h; exact hkgm))
        (distGuarded_ctorSigs (fun _ h => by cases h; exact hkgm) (fun _ h => by cases h; exact hkm)) hbl (elems_length hI hws) hbs
        (elems_sorts hI hws) (fun m => by rw [hset, hvset])
  · exfalso
    obtain ⟨hab, -, hw0, hb⟩ := sortOf_inj.mp hsw
    subst hb
    have hvset : ∀ m, GS I (c.sortName k.result) (.inj (c.sortName a)) [elemOf c I w0] m ↔
        m = elemOf c I (.inj a k.result w0) :=
      fun m => by rw [← den_inj_gs hI hw0 KoreAML.val0 m]; exact hwe m
    exact gen_dist hI hN hgk (gensF_inj hab) (fun h => by cases h) (fun _ _ h _ => by cases h)
      (distGuarded_ctorSigs (fun _ h => by cases h; exact hkm) (fun _ h => by cases h))
      (distGuarded_ctorSigs (fun _ h => by cases h) (fun _ h => by cases h; exact hkm)) (ys := [elemOf c I w0])
      hbl rfl hbs (single_sorts ((inS_iff _).mp (elemOf_spec hI hw0 KoreAML.val0).2))
      (fun m => by rw [hset]; exact (hvset m).symm)

end

/-! ## The substitution a valuation gives -/

open Classical in
/-- A value of the sort `s` whose element is `a`, where there is one. -/
noncomputable def pick {M : Type} [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (s : Srt) (a : M) :
    GroundTerm :=
  if h : ∃ v, c.sortOf v = some s ∧ elemOf c I v = a then Classical.choose h else default

/-- The key of the variable `i` of `vs`. -/
def keyAt (vs : List KoreAML.Var) (i : Nat) : VarKey := KoreAML.evarKey (vs.getD i default).kore

/-- The substitution a valuation gives the variables `vars` (named by `vs`, read through the table
`tbl`): each variable the value of its sort whose element the valuation gives it. -/
noncomputable def substOf {M : Type} [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (tbl : VarTable)
    (vs : List KoreAML.Var) (vars : List Srt) (e : Valuation M) : Subst :=
  (List.range vars.length).map fun i => (i, pick c I (vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i))))

theorem lookup_range' {α : Type} (f : Nat → α) (i : Nat) : ∀ (st n : Nat),
    ((List.range' st n).map fun j => (j, f j)).lookup i = if st ≤ i ∧ i < st + n then some (f i) else none
  | st, 0 => by simp
  | st, n + 1 => by
    rw [List.range'_succ, List.map_cons, List.lookup_cons]
    by_cases h : i = st
    · subst h; simp
    · have : (i == st) = false := by simpa using h
      rw [this, lookup_range' f i (st + 1) n]
      by_cases h1 : st + 1 ≤ i ∧ i < st + 1 + n
      · rw [if_pos h1, if_pos ⟨by omega, by omega⟩]
      · rw [if_neg h1, if_neg (by omega)]

theorem substOf_lookup {M : Type} [Inhabited M] {c : Semantics} {I : Interpretation KoreAML.Sym M} {tbl : VarTable}
    {vs : List KoreAML.Var} {vars : List Srt} {e : Valuation M} {i : Nat} (hi : i < vars.length) :
    (substOf c I tbl vs vars e).lookup i = some (pick c I (vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i)))) := by
  unfold substOf
  rw [List.range_eq_range', lookup_range', if_pos ⟨Nat.zero_le _, by omega⟩]

theorem substOf_lookup_some {M : Type} [Inhabited M] {c : Semantics} {I : Interpretation KoreAML.Sym M} {tbl : VarTable}
    {vs : List KoreAML.Var} {vars : List Srt} {e : Valuation M} {i : Nat} {v : GroundTerm}
    (h : (substOf c I tbl vs vars e).lookup i = some v) :
    i < vars.length ∧ v = pick c I (vars.getD i 0) (e.evalEvar (tbl.ev (keyAt vs i))) := by
  unfold substOf at h
  rw [List.range_eq_range', lookup_range'] at h
  split at h
  · rename_i hi; exact ⟨by omega, (Option.some.inj h).symm⟩
  · cases h

theorem pick_spec {M : Type} [Inhabited M] {c : Semantics} {I : Interpretation KoreAML.Sym M} {s : Srt} {a : M}
    (h : ∃ v, c.sortOf v = some s ∧ elemOf c I v = a) : c.sortOf (pick c I s a) = some s ∧ elemOf c I (pick c I s a) = a := by
  unfold pick; rw [dif_pos h]; exact Classical.choose_spec h

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hg : genWf c = true) (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI hg htr

/-- The value `pick` finds is any value of the sort with that element. -/
theorem pick_eq {s : Srt} {w : GroundTerm} (hw : c.sortOf w = some s) : pick c I s (elemOf c I w) = w := by
  obtain ⟨h1, h2⟩ := pick_spec (c := c) (I := I) ⟨w, hw, rfl⟩
  exact values_apart hI hg htr (apartSort_of_sorted hg hw) h1 hw h2

end

/-! ## Plain patterns read downwards -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]

include hI in
/-- G-arity of a constructor, at elements of its argument sorts. -/
theorem ctor_arity (hnm : NamesPlain c) {f : Sym} {k : CtorSig} (hk : lookupSig c.ctorSigs f = some k)
    {bs : List M} (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) {m : M}
    (hm : GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs m) : InS I (c.sortName k.result) m := by
  have hD := defOK hI
  have hkm := (lookupSig_spec hk).1
  have hit := sat_sigItem hI (sig_arity (c := c) (k := k)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hkm)))))
  unfold symArityItem at hit
  rw [show iteSort? (c.symName k.name) = none from hnm k hkm] at hit
  dsimp only at hit
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  apply hinc
  obtain ⟨a, ha, hm⟩ := hm
  rw [interp_appList]
  refine ⟨a, ha, bs, ?_, hm⟩
  clear ha hm hinc hit
  have : ∀ (ss : List Srt) (bs : List M), bs.length = (ss.map c.sortName).length →
      (∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x) →
      All2 (fun φ b => φ.interpret I KoreAML.val0 b)
        ((ss.map (srtOf c)).map fun s => KoreAML.inhOf (KoreAML.trSort [] s)) bs := by
    intro ss
    induction ss with
    | nil => intro bs hl _; cases bs with
      | nil => exact .nil
      | cons _ _ => simp at hl
    | cons s ss ih =>
      intro bs hl hb
      cases bs with
      | nil => simp at hl
      | cons b bs =>
        refine .cons ?_ (ih bs (by simpa using hl) (fun i x s' h1 h2 => hb (i + 1) x s' (by simpa using h1) (by simpa using h2)))
        unfold srtOf; dsimp only; rw [trSort_srt]
        exact hb 0 b (c.sortName s) rfl rfl
  exact this k.args bs hbl hbs

variable (hg : genWf c = true) (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) [OvlOK c]
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
include hI hg htr hnm hvs hin

theorem tr_kore_dv {s : Srt} {lit : Lit} (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.dv s lit))).interpret I e m ↔ (den c (.dv s lit)).interpret I e m := by
  rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
  rw [KoreAML.tr_dv, KoreAML.tr_dv]

theorem tr_kore_as (p : Term) (i : Nat) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.as p i))).interpret I e m ↔
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret I e m ∧ m = e.evalEvar (tbl.ev (keyAt vs i)) := by
  rw [Term.kore, KoreAML.tr]
  simp only [KoreAML.trAndList]
  rw [KoreAML.interp_sAnd]
  have hv := tr_var (c := c) (I := I) (vs := vs) (t := tbl) (e := e) i m
  rw [Term.kore] at hv
  rw [hv]; rfl

mutual
  /-- The elements of a plain pattern's translation, at a valuation of its variables in their
  sorts, lie in the pattern's sort. -/
  theorem patSort : ∀ {p : Term} {s : Srt}, plainPat c p = true → sortOfTerm c.patCtxAll vars p = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret I e m → InS I (c.sortName s) m
    | .var i, s, _, ht, m, hm => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [tr_var] at hm
      rw [hm]
      have := hin i hlt
      rwa [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
    | .dv s' lit, s, _, ht, m, hm => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      rw [tr_kore_dv hI hg htr hnm hvs hin] at hm
      have hs := elemOf_spec hI (sortOf_dv.mpr ⟨hok, rfl⟩) e
      rw [(hs.1 m).mp hm]
      exact (inS_iff _).mp hs.2
    | .app f ps, s, hp, ht, m, hm => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      rw [plainPat] at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hc, -⟩, hps⟩ := hp
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hc
      have hkk := lookup_patCtxAll hk0 hk'
      subst hkk
      rw [kore_app_plain hnm hk0, trArgs_appList, interp_appList] at hm
      obtain ⟨a, ha, bs, hbs, hm⟩ := hm
      have hsorts := patSorts hps hargs hbs
      exact ctor_arity hI hnm hk0 hsorts.1 hsorts.2 ⟨a, by
        show (KoreAML.sym (.symbol (c.symName k.name))).interpret I KoreAML.val0 a
        rw [(lookupSig_spec hk0).2]; exact ha, hm⟩
    | .inj a b p, s, hp, ht, m, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [plainPat] at hp
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := patSort hp ht' x hx
      obtain ⟨y, hy, hys⟩ := gen_fun hI (genWf_sub hg hab).1 (gensF_inj hab) rfl (xs := [x]) rfl (single_sorts hxs)
      rw [(hys m).mp hm]; exact hy
    | .as p i, s, hp, ht, m, hm => by
      obtain ⟨-, ht'⟩ := Exec.sortOfTerm_as ht
      rw [plainPat] at hp
      rw [tr_kore_as hI hg htr hnm hvs hin] at hm
      exact patSort hp ht' m hm.1
  theorem patSorts : ∀ {ps : List Term} {ss : List Srt} {bs : List M}, plainPats c ps = true →
      sortsOfTerms c.patCtxAll vars ps = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ps).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      bs.length = (ss.map c.sortName).length ∧
        ∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x
    | [], ss, bs, _, ht, hbs => by
      rw [sortsOfTerms_nil.mp ht]
      rw [Term.koreList] at hbs
      cases hbs
      exact ⟨rfl, fun i x s h _ => by simp at h⟩
    | p :: ps, ss, bs, hp, ht, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [plainPats] at hp
      simp only [Bool.and_eq_true] at hp
      rw [Term.koreList, List.map_cons] at hbs
      cases hbs with
      | cons hb hbs =>
        have ih := patSorts hp.2 h2 hbs
        refine ⟨by simp [ih.1], fun i x s' hx hs' => ?_⟩
        cases i with
        | zero =>
          simp at hx hs'; subst hx; subst hs'
          exact patSort hp.1 h1 _ hb
        | succ i => exact ih.2 i x s' (by simpa using hx) (by simpa using hs')
end

/-- The variable `i` of a valuation: if the element it gives `i` is a value's of `i`'s sort, the
substitution of the valuation gives `i` that value. -/
theorem substOf_var {i : Nat} {s : Srt} (hi : vars[i]? = some s) {w : GroundTerm} (hw : c.sortOf w = some s)
    (he : elemOf c I w = e.evalEvar (tbl.ev (keyAt vs i))) : (substOf c I tbl vs vars e).lookup i = some w := by
  have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [substOf_lookup hlt, ← he, List.getD_eq_getElem?_getD, hi, Option.getD_some, pick_eq hI hg htr hw]

/-- The valuation gives the variable `i` the element of a value of its sort. -/
def Witnessed (c : Semantics) (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (vs : List KoreAML.Var)
    (vars : List Srt) (e : Valuation M) (i : Nat) : Prop :=
  ∃ v, c.sortOf v = some (vars.getD i 0) ∧ elemOf c I v = e.evalEvar (tbl.ev (keyAt vs i))

omit hI hg htr hnm hvs hin in
theorem witnessed_of {i : Nat} {s : Srt} (hi : vars[i]? = some s) {w : GroundTerm} (hw : c.sortOf w = some s)
    (he : elemOf c I w = e.evalEvar (tbl.ev (keyAt vs i))) : Witnessed c I tbl vs vars e i :=
  ⟨w, by rw [List.getD_eq_getElem?_getD, hi, Option.getD_some]; exact hw, he⟩

mutual
  /-- **Plain patterns, downwards.** If the element of a value of a plain pattern's sort lies in
  the pattern's translation, at a valuation of its variables in their sorts, the pattern denotes
  the value under the valuation's substitution, and the valuation gives each of the pattern's
  variables the element of a value of its sort. -/
  theorem patVal_back : ∀ {p : Term} {s : Srt} {w : GroundTerm}, plainPat c p = true →
      sortOfTerm c.patCtxAll vars p = some s → c.sortOf w = some s →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret I e (elemOf c I w) →
      PatVal c (substOf c I tbl vs vars e) p w ∧ ∀ i ∈ varOccs p, Witnessed c I tbl vs vars e i
    | .var i, s, w, _, ht, hw, hm => by
      rw [tr_var] at hm
      refine ⟨.var (substOf_var hI hg htr hnm hvs hin (sortOfTerm_var.mp ht) hw hm), fun j hj => ?_⟩
      rw [varOccs] at hj
      rw [mem_one hj]
      exact witnessed_of (sortOfTerm_var.mp ht) hw hm
    | .dv s' lit, s, w, _, ht, hw, hm => by
      obtain ⟨hok, hs⟩ := sortOfTerm_dv.mp ht
      subst hs
      rw [tr_kore_dv hI hg htr hnm hvs hin] at hm
      have hdv : c.sortOf (.dv s lit) = some s := sortOf_dv.mpr ⟨hok, rfl⟩
      have h1 := ((elemOf_spec hI hdv e).1 _).mp hm
      rw [values_apart hI hg htr (apartSort_of_sorted hg hw) hw hdv h1]
      exact ⟨.dv, fun j hj => by rw [varOccs] at hj; cases hj⟩
    | .app f ps, s, w, hp, ht, hw, hm => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      rw [plainPat] at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hc, -⟩, hps⟩ := hp
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hc
      have hkk := lookup_patCtxAll hk0 hk'
      subst hkk
      rw [kore_app_plain hnm hk0, trArgs_appList, interp_appList] at hm
      obtain ⟨a, ha, bs, hbs, hm⟩ := hm
      have hsorts := patSorts hI hg htr hnm hvs hin hps hargs hbs
      obtain ⟨ws, rfl, hws, rfl⟩ := ctor_back hI hg htr hk0 hw hsorts.1 hsorts.2 ⟨a, by
        show (KoreAML.sym (.symbol (c.symName k.name))).interpret I KoreAML.val0 a
        rw [(lookupSig_spec hk0).2]; exact ha, hm⟩
      have ih := patVals_back hps hargs hws hbs
      exact ⟨.ctor hc ih.1, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
    | .inj a b p, s, w, hp, ht, hw, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [plainPat] at hp
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := patSort hI hg htr hnm hvs hin hp ht' x hx
      obtain ⟨w', hw', rfl, rfl⟩ := inj_back hI hg htr w hab hw hxs hm
      have ih := patVal_back hp ht' hw' hx
      exact ⟨.inj ih.1, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
    | .as p i, s, w, hp, ht, hw, hm => by
      obtain ⟨hvi, ht'⟩ := Exec.sortOfTerm_as ht
      rw [plainPat] at hp
      rw [tr_kore_as hI hg htr hnm hvs hin] at hm
      have ih := patVal_back hp ht' hw hm.1
      refine ⟨.as ih.1 (substOf_var hI hg htr hnm hvs hin hvi hw hm.2), fun j hj => ?_⟩
      rw [varOccs] at hj
      rcases List.mem_append.mp hj with hj | hj
      · exact ih.2 j hj
      · rw [mem_one hj]; exact witnessed_of hvi hw hm.2
  theorem patVals_back : ∀ {ps : List Term} {ss : List Srt} {ws : List GroundTerm}, plainPats c ps = true →
      sortsOfTerms c.patCtxAll vars ps = some ss → c.sortsOf ws = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ps).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map (elemOf c I)) →
      PatVals c (substOf c I tbl vs vars e) ps ws ∧ ∀ i ∈ varOccsList ps, Witnessed c I tbl vs vars e i
    | [], ss, ws, _, ht, hws, _ => by
      rw [sortsOfTerms_nil.mp ht] at hws
      rw [sortsOf_nil_eq hws]
      exact ⟨.nil, fun j hj => by rw [varOccsList] at hj; cases hj⟩
    | p :: ps, ss, ws, hp, ht, hws, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [plainPats] at hp
      simp only [Bool.and_eq_true] at hp
      cases ws with
      | nil => rw [sortsOf_nil] at hws; cases hws
      | cons w ws =>
        obtain ⟨s0, ss0, hw, hws', he⟩ := sortsOf_cons.mp hws
        cases he
        rw [Term.koreList, List.map_cons, List.map_cons] at hbs
        cases hbs with
        | cons hb hbs =>
          have ih1 := patVal_back hp.1 h1 hw hb
          have ih2 := patVals_back hp.2 h2 hws' hbs
          refine ⟨.cons ih1.1 ih2.1, fun j hj => ?_⟩
          rw [varOccsList] at hj
          rcases List.mem_append.mp hj with hj | hj
          · exact ih1.2 j hj
          · exact ih2.2 j hj
end

end

/-! ## Translated premises read downwards -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem All2.of_get {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, as.length = bs.length →
    (∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → R a b) → All2 R as bs
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, hr => .cons (hr 0 a b rfl rfl)
      (All2.of_get (by simpa using h) (fun i a' b' h1 h2 => hr (i + 1) a' b' (by simpa using h1) (by simpa using h2)))

theorem ev_inj {tbl : VarTable} {k k' : VarKey} (hk : k ∈ tbl) (hk' : k' ∈ tbl) (h : tbl.ev k = tbl.ev k') : k = k' := by
  simp only [VarTable.ev, VarTable.index, EVar.mk.injEq, Nat.add_right_cancel_iff] at h
  rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hk), ← List.getElem_idxOf (List.idxOf_lt_length_of_mem hk')]
  simp only [h]

/-- Under the binders of `existsAll`: a valuation that differs from the outer one at the binders
only, gives each binder an element of its sort, and satisfies the body. -/
theorem existsAll_elim (hD : DefOK I) {tbl : VarTable} {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (e : Valuation M) (m : M),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)).interpret I e m →
    ∃ e' : Valuation M, (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e'.evalEvar x = e.evalEvar x) ∧
      (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS I n (e'.evalEvar (tbl.ev (KoreAML.evarKey b)))) ∧
      (KoreAML.tr ⟨tbl, []⟩ body).interpret I e' m
  | [], e, m, _, _, h => ⟨e, fun _ _ => rfl, fun _ hb => absurd hb List.not_mem_nil, h⟩
  | b :: bs, e, m, hnd, hs, h => by
    have h' : (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret I e m := h
    rw [KoreAML.tr, KoreAML.interp_sExists] at h'
    obtain ⟨a, ha, h'⟩ := h'
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨e', h1, h2, h3⟩ := existsAll_elim hD bs _ m hnd.2 (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb')) h'
    refine ⟨e', fun x hx => ?_, fun b' hb' n hn => ?_, h3⟩
    · rw [h1 x (fun b'' hb'' => hx b'' (List.mem_cons_of_mem _ hb''))]
      exact Function.update_noteq (hx b (List.mem_cons_self ..)) _ _
    · rcases List.mem_cons.mp hb' with rfl | hb'
      · have hev : e'.evalEvar (tbl.ev (KoreAML.evarKey b')) = a := by
          rw [h1 _ (fun b'' hb'' heq => hnd.1 (List.mem_map.mpr ⟨b'', hb'', heq.symm⟩))]
          exact Function.update_same _ _ _
        rw [hev]
        rw [KoreAML.interp_member hD] at ha
        simp only [Function.update_same] at ha
        rw [hn, trSort_srt] at ha
        exact (inS_iff _).mp ha
      · exact h2 b' hb' n hn

/-- The argument part of a premise, downwards: each formal argument's element lies in its pattern. -/
theorem argsConj_back {tbl : VarTable} {e : Valuation M} {m : M} : ∀ (j : Nat) (l : List (String × Kore.Pattern)),
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.argsConj j l)).interpret I e m →
    ∀ (n : Nat) s p, l[n]? = some (s, p) →
      (KoreAML.tr ⟨tbl, []⟩ p).interpret I e (e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))))
  | _, [], _, n, s, p, h => by simp at h
  | j, (s', p') :: l, hm, n, s, p, hn => by
    simp only [KoreAML.argsConj] at hm
    rw [tr_and2, KoreAML.interp_sAnd] at hm
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have h1 := hm.1
      rw [KoreAML.tr] at h1
      unfold KoreAML.sIn at h1
      rw [KoreAML.interp_sCeil_raw] at h1
      obtain ⟨_, _, x, _, _, hx, _⟩ := h1
      rw [KoreAML.interp_sAnd] at hx
      have hx1 : x = e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s'))) := hx.1
      rw [Nat.add_zero, ← hx1]
      exact hx.2
    | succ n =>
      have := argsConj_back (j + 1) l hm.2 n s p (by simpa using hn)
      rwa [show j + (n + 1) = j + 1 + n by omega]

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- **A `requires` that is not `true`.** If `t` denotes what a result other than `true` denotes,
`⌈t = true⌉` is empty: undefined, it denotes nothing; defined, it is a Bool other than `true`,
and distinct values of Bool are distinct elements. -/
theorem reqFalse_empty {tbl : VarTable} {e : Valuation M} {S' : Kore.KSort} {σ' : M}
    (hS' : ∀ a, (KoreAML.trSort tbl S').interpret I e a ↔ a = σ') (hσ' : IsSort I σ')
    {tp : Kore.Pattern} {r : Option GroundTerm} (hr : r ≠ some (bool true))
    (hrs : ∀ v, r = some v → c.sortOf v = some Srt.bool)
    (ht : ∀ m, (KoreAML.tr ⟨tbl, []⟩ tp).interpret I e m ↔ Res c I e r m) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (reqPat S' (some tp))).interpret I e m := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  simp only [reqPat]
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hS' hσB2 hσ']
  rintro ⟨-, hall⟩
  have hts := elemOf_spec hI (sortOf_bool (c := c) true) e
  have hin : Inh I σB (elemOf c I (bool true)) := by
    have := hts.2
    rw [sortName_bool] at this
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσB1).mp this
  have h1 := (hall _ hin).mpr (by
    rw [KoreAML.tr_dv]
    have := (hts.1 (elemOf c I (bool true))).mpr rfl
    unfold den KoreAML.den bool at this
    rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv] at this
    exact this)
  rw [ht] at h1
  cases r with
  | none => exact h1
  | some v =>
    exact dom_apart hI (List.contains_iff_mem.mpr bool_distinct) (hrs v rfl) (sortOf_bool true)
      (fun h => hr (by rw [h])) e _ ⟨h1, (hts.1 _).mpr rfl⟩


/-- **A clause's right side where its `ensures` denotes a result other than `true`**: nothing,
`⌈E = true⌉` being empty there. -/
theorem right_empty (hnn : NamesNumbered c) {fn : Fn} (hfnm : fn ∈ c.allFns) {cl : Clause} {tbl : VarTable} {e : Valuation M}
    {t : Term} {w : Option GroundTerm} (ht : cl.ens = some t) (hw : w ≠ some (bool true))
    (hws : ∀ v, w = some v → c.sortOf v = some Srt.bool)
    (ihe : ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e w m) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e none m := by
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..))
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c fn.result)).interpret I e b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  intro m
  unfold clauseRight
  rw [tr_and2, KoreAML.interp_sAnd, ht]
  simp only [Option.map_some, Res, iff_false, not_and]
  exact fun _ => reqFalse_empty hI hS hσr2 hw hws ihe m

end

/-! ## Canonical binders -/

section
variable {c : Semantics}

theorem nodup_map_range {β : Type} (f : Nat → β) : ∀ n : Nat,
    (∀ i j, i < n → j < n → f i = f j → i = j) → ((List.range n).map f).Nodup
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.Nodup, List.pairwise_append]
    refine ⟨nodup_map_range f n (fun i j hi hj => h i j (by omega) (by omega)), by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hb' : b = f n := by simpa using hb
    subst hb'
    intro heq
    exact absurd (h i n (by omega) (by omega) heq) (by omega)

theorem canonVars_kore_mem {vars : List Srt} {b : Kore.EVar} (hb : b ∈ (canonVars c vars).map KoreAML.Var.kore) :
    ∃ i < vars.length, b = ((canonVars c vars).getD i default).kore := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  rw [canonVars_length] at hi
  refine ⟨i, hi, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [canonVars_length]; exact hi)]
  rfl

theorem canonKey_inj {vars : List Srt} {i j : Nat} (hi : i < vars.length) (hj : j < vars.length)
    (h : canonKey c vars i = canonKey c vars j) : i = j := by
  rw [canonKey_eq c hi, canonKey_eq c hj] at h
  injection h with h _
  exact varName_inj h

/-- The binders of a clause's or rule's canonical variables, at their indices in a table holding
their keys: one index each, at a constant sort. -/
theorem canon_binders {vars : List Srt} {tbl : VarTable} (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl) :
    (((canonVars c vars).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup ∧
      ∀ b ∈ (canonVars c vars).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := by
  refine ⟨?_, fun b hb => by obtain ⟨i, _, rfl⟩ := canonVars_kore_mem hb; exact ⟨_, rfl⟩⟩
  rw [List.map_map]
  have hl : (canonVars c vars).map ((fun b => tbl.ev (KoreAML.evarKey b)) ∘ KoreAML.Var.kore) =
      (List.range vars.length).map (fun i => tbl.ev (canonKey c vars i)) := by
    apply List.ext_getElem (by simp [canonVars_length])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    unfold canonKey
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
    rfl
  rw [hl]
  exact nodup_map_range _ _ (fun i j hi hj h => canonKey_inj hi hj (ev_inj (hkeys i hi) (hkeys j hj) h))

end

/-! ## The core lemmas: a failing clause has an empty exclusion, a rule that does not apply an empty
`applies` -/

/-- **A clause fails in the model** at the arguments `ws`: under every well-sorted substitution
under which its patterns denote `ws`, and at every valuation that agrees with that substitution, it
has a `requires` whose translation denotes a result other than `true` (nothing, or a Bool other
than `true`). With total functions, a clause that fails in the kernel's sense (`Fails`) fails in
the model (`evalTerm_den2`). -/
def ModelFails {M : Type} (c : Semantics) (I : Interpretation KoreAML.Sym M) (cl : Clause) (ws : List GroundTerm) :
    Prop :=
  ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws → ∀ (tbl : VarTable) (e : Valuation M),
    Agrees c I tbl (canonVars c cl.vars) σ e →
    ∃ t r, cl.req = some t ∧ r ≠ some (bool true) ∧ (∀ v, r = some v → c.sortOf v = some Srt.bool) ∧
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r m

/-- **A rule does not apply in the model** to `x`: under every well-sorted substitution under which
its left-hand side denotes `x`, at every valuation that agrees with it, its `requires` denotes a
result other than `true`. The model's reading of `NotApplies`. -/
def ModelNotApplies {M : Type} (c : Semantics) (I : Interpretation KoreAML.Sym M) (r : Rule) (x : GroundTerm) : Prop :=
  ∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x → ∀ (tbl : VarTable) (e : Valuation M),
    Agrees c I tbl (canonVars c r.vars) σ e →
    ∃ t v, r.req = some t ∧ v ≠ some (bool true) ∧ (∀ u, v = some u → c.sortOf u = some Srt.bool) ∧
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) t)).interpret I e m ↔ Res c I e v m

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hg : genWf c = true) (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c)
include hI hg htr

/-- The substitution of a valuation that gives every variable the element of a value of its sort
is well sorted and agrees with the valuation. -/
theorem substOf_ok {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
    (hvs : vs.length = vars.length) (hwit : ∀ i < vars.length, Witnessed c I tbl vs vars e i) :
    c.WellSorted vars (substOf c I tbl vs vars e) ∧ Agrees c I tbl vs (substOf c I tbl vs vars e) e := by
  constructor
  · intro i s hi
    have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨_, substOf_lookup hlt, ?_⟩
    have := (pick_spec (hwit i hlt)).1
    rwa [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this ⊢
  · intro i v hi hv m
    obtain ⟨hlt, rfl⟩ := substOf_lookup_some hv
    obtain ⟨h1, h2⟩ := pick_spec (hwit i hlt)
    rw [(elemOf_spec hI h1 e).1, h2]
    exact Iff.rfl

theorem canonKey_ne_X {vars : List Srt} {i : Nat} (hi : i < vars.length) (n : String) (s : Kore.KSort) :
    VarKey.evar ("X" ++ n) s ≠ canonKey c vars i := by
  rw [canonKey_eq c hi]
  intro h
  injection h with h
  exact x_ne_var h

include hnm in
/-- **The core lemma for clauses.** At arguments where a clause fails in the model, its exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄` is empty, at a valuation that gives each formal argument `Xⱼ` the
element of the argument and the sort variable `R` a sort. -/
theorem exclusion_empty {fn : Fn} {cl : Clause} (hpre : cl.pre = .top)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) (hplain : plainPats c cl.pats = true)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {tbl : VarTable} (hkeys : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl)
    (hXkeys : ∀ (j : Nat) s, fn.args[j]? = some s → VarKey.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)) ∈ tbl)
    (hRkey : VarKey.sortVar "R" ∈ tbl)
    {e : Valuation M}
    (hX : ∀ (j : Nat) w s, ws[j]? = some w → fn.args[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = elemOf c I w)
    {σR : M} (hR : e.evalEvar (tbl.ev (.sortVar "R")) = σR) (hσR : IsSort I σR)
    (hfail : ModelFails c I cl ws) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret I e m := by
  intro hm
  rw [exclusion_top _ hpre (List.all_eq_true.mpr fun i hi => by simpa using hbinds i (List.mem_range.mp hi))] at hm
  have hD := defOK hI
  let vs := canonVars c cl.vars
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hm' : (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll KoreAML.R (vs.map KoreAML.Var.kore)
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats)))).interpret I e m := hm
  obtain ⟨e', hag, hguard, hbody⟩ := existsAll_elim hD _ e m hnd hsrt hm'
  have hnotb : ∀ k, k ∈ tbl → (∀ i < cl.vars.length, k ≠ canonKey c cl.vars i) →
      ∀ b ∈ vs.map KoreAML.Var.kore, tbl.ev k ≠ tbl.ev (KoreAML.evarKey b) := by
    intro k hk hne b hb heq
    obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb
    exact hne i hi (ev_inj hk (hkeys i hi) heq)
  have he'X : ∀ (j : Nat) s, fn.args[j]? = some s →
      e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) =
        e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) :=
    fun j s hj => hag _ (hnotb _ (hXkeys j s hj) (fun i hi => canonKey_ne_X hI hg htr hi _ _))
  have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) :=
    hag _ (hnotb _ hRkey (fun i hi h => by rw [canonKey_eq c hi] at h; cases h))
  unfold premise at hbody
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  obtain ⟨hreq, hargs⟩ := hbody
  have hcon := argsConj_back 0 _ hargs
  have hin : ∀ i < cl.vars.length, InS I (c.sortName (cl.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    have hb : (vs.getD i default).kore ∈ vs.map KoreAML.Var.kore := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.mem_map_of_mem (List.getElem_mem hlt)
    exact hguard _ hb _ (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  have hlenp : (Term.koreList c vs cl.pats).length = fn.args.length := by
    rw [koreList_length]; exact sortsOfTerms_length hpats
  have hall : All2 (fun φ b => φ.interpret I e' b) ((Term.koreList c vs cl.pats).map (KoreAML.tr ⟨tbl, []⟩))
      (ws.map (elemOf c I)) := by
    refine All2.of_get (by simp [hlenp, sortsOf_length hws]) (fun j φ b hφ hb => ?_)
    rw [List.getElem?_map] at hφ hb
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hφ
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hjl : j < fn.args.length := by
      rw [← sortsOf_length hws]; exact (List.getElem?_eq_some_iff.mp hw).1
    have hs : fn.args[j]? = some fn.args[j] := List.getElem?_eq_getElem hjl
    have hl : ((fn.args.map c.sortName).zip (Term.koreList c vs cl.pats))[j]? = some (c.sortName fn.args[j], p) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨by rw [List.getElem?_map, hs]; rfl, hp⟩
    have := hcon j _ p hl
    rw [Nat.zero_add, he'X j _ hs, hX j w _ hw hs] at this
    exact this
  obtain ⟨hpv, hwit⟩ := patVals_back hI hg htr hnm (canonVars_length c cl.vars) hin hplain hpats hws hall
  obtain ⟨hws', hagr⟩ := substOf_ok hI hg htr (canonVars_length c cl.vars) (fun i hi => hwit i (hbinds i hi))
  obtain ⟨t, r, ht, hr, hrs, hden⟩ := hfail _ hws' hpv tbl e' hagr
  rw [ht] at hreq
  exact reqFalse_empty hI (S' := KoreAML.R) (fun a => by rw [trSort_R, KoreAML.interp_evar, he'R, hR]) hσR hr hrs hden m hreq

include hnm in
/-- **The core lemma for rules.** If a rule does not apply to a configuration in the model, the
configuration's element is not in the rule's `applies` pattern `∃x̄. (lhs ∧ ⌈req = true⌉)`. -/
theorem applies_empty {r : Rule} (hlhs : sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort)
    (hbinds : ∀ i < r.vars.length, i ∈ varOccs r.lhs) (hplain : plainPat c r.lhs = true)
    (hpre : r.pre = .top) {x : GroundTerm} (hx : c.sortOf x = some topCellSort)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) (e : Valuation M)
    (hfail : ModelNotApplies c I r x) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x) := by
  intro hm
  rw [applies_top _ hpre (List.all_eq_true.mpr fun i hi => by simpa using hbinds i (List.mem_range.mp hi))] at hm
  have hD := defOK hI
  let vs := canonVars c r.vars
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hm' : (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll (srtOf c topCellSort) (vs.map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs))]))).interpret
        I e (elemOf c I x) := hm
  obtain ⟨e', -, hguard, hbody⟩ := existsAll_elim hD _ e _ hnd hsrt hm'
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  obtain ⟨hl, hreq⟩ := hbody
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    have hb : (vs.getD i default).kore ∈ vs.map KoreAML.Var.kore := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.mem_map_of_mem (List.getElem_mem hlt)
    exact hguard _ hb _ (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  obtain ⟨hpv, hwit⟩ := patVal_back hI hg htr hnm (canonVars_length c r.vars) hin hplain hlhs hx hl
  obtain ⟨hws', hagr⟩ := substOf_ok hI hg htr (canonVars_length c r.vars) (fun i hi => hwit i (hbinds i hi))
  obtain ⟨t, v, ht, hv, hvs, hden⟩ := hfail _ hws' hpv tbl e' hagr
  rw [ht] at hreq
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  exact reqFalse_empty hI (S' := srtOf c topCellSort) (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2
    hv hvs hden _ hreq

end


/-! ## The overloading symbols in a model -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An overload equation** at elements `zs` of the overloaded symbol's argument sorts: the
overloading symbol applied to their lifts `ys` (each the element itself where the two sorts are
named alike, the injection's image otherwise) builds what the overloaded symbol builds from `zs`,
lifted alike. -/
theorem ovlEq_at (hD : DefOK I) {N N' : String} {F G : KoreAML.CtorSig} (h : I ⊧ᴵ (KoreAML.Cons.ovlEqItem F G).pat)
    {zs ys : List M} (hl : zs.length = G.args.length) (hlF : F.args.length = G.args.length)
    (hly : ys.length = G.args.length)
    (hzs : ∀ (i : Nat) x s, zs[i]? = some x → G.args[i]? = some s → InS I s x)
    (hys : ∀ (i : Nat) A B z y, G.args[i]? = some A → F.args[i]? = some B → zs[i]? = some z → ys[i]? = some y →
      ∀ m, (if A == B then m = z else GS I B (.inj A) [z] m) ↔ m = y) (m : M) :
    GS I N (.ctor F) ys m ↔ (if G.result == F.result then GS I N' (.ctor G) zs m
      else ∃ x, GS I N' (.ctor G) zs x ∧ GS I F.result (.inj G.result) [x] m) := by
  have h1 := h (listVal zs) default
  unfold KoreAML.Cons.ovlEqItem at h1
  dsimp only at h1
  have hb := KoreAML.interp_guarded h1 (fun w hw => memGuards_hold hD _ _ (xs_length 0 _)
    (fun i v s hv hs => by
      obtain ⟨hi, _⟩ := xs_get hv
      rw [listVal_get zs hv, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hl]; exact hi)]
      exact hzs i _ s (List.getElem?_eq_getElem _) hs) w hw default)
  rw [KoreAML.interp_equal hD] at hb
  have hxs : (KoreAML.Cons.xs 0 G.args.length).map (listVal zs).evalEvar = zs := by
    have := (listVal_split zs [] _ 0 hl rfl).1
    rwa [List.append_nil] at this
  have hlhs : ∀ m, (KoreAML.appList (KoreAML.sym (.symbol F.name)) (((G.args.zip F.args).zip
      (KoreAML.Cons.xs 0 G.args.length)).map fun ((A, B), xi) =>
        if A == B then Pattern.evar xi else KoreAML.appList (KoreAML.sym (.symbol "inj"))
          [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, Pattern.evar xi])).interpret I (listVal zs) m ↔
      GS I N (.ctor F) ys m := by
    intro m
    rw [interp_appList_sing _ _ ys (All2.of_get (by simp [hlF, hly, xs_length]) (fun i φ y hφ hy => by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hφ
      obtain ⟨⟨⟨A, B⟩, xi⟩, hp, rfl⟩ := hφ
      simp only [List.getElem?_zip_eq_some] at hp
      obtain ⟨⟨hA, hB⟩, hxi⟩ := hp
      obtain ⟨hi, rfl⟩ := xs_get hxi
      have hz : zs[i]? = some (zs[i]'(by rw [hl]; exact hi)) := List.getElem?_eq_getElem _
      have hev : (listVal zs).evalEvar ⟨0 + i + 1⟩ = zs[i]'(by rw [hl]; exact hi) := by
        rw [listVal_get zs (show (KoreAML.Cons.xs 0 G.args.length)[i]? = some ⟨0 + i + 1⟩ from hxi),
          Nat.zero_add, List.getD_eq_getElem?_getD, hz, Option.getD_some]
      intro m'
      rw [← hys i A B _ y hA hB hz hy m']
      split
      · rw [KoreAML.interp_evar, hev]
      · rw [interp_injApp]
        constructor
        · rintro ⟨x, hx, hm⟩; rw [KoreAML.interp_evar, hev] at hx; subst hx; exact hm
        · intro hm; exact ⟨_, by rw [KoreAML.interp_evar, hev], hm⟩))]
    unfold GS
    simp only [genHead]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ((Closed.sym _).interp _ _ a).mp ha, h⟩,
      fun ⟨a, ha, h⟩ => ⟨a, ((Closed.sym _).interp _ _ a).mpr ha, h⟩⟩
  have hg : ∀ m, (KoreAML.appList (KoreAML.sym (.symbol G.name))
      ((KoreAML.Cons.xs 0 G.args.length).map Pattern.evar)).interpret I (listVal zs) m ↔ GS I N' (.ctor G) zs m := by
    intro m
    have := interp_genPat_vars (I := I) N' (.ctor G) (listVal zs) (KoreAML.Cons.xs 0 G.args.length) m
    rw [hxs] at this
    exact this
  rw [← hlhs m, hb m]
  split
  · exact hg m
  · rw [interp_injApp]
    exact ⟨fun ⟨x, hx, hm⟩ => ⟨x, (hg x).mp hx, hm⟩, fun ⟨x, hx, hm⟩ => ⟨x, (hg x).mpr hx, hm⟩⟩

/-- Each overload equation is an item of `Γ`. -/
theorem ovlEqItem_mem {o : OvlSig} {kg : CtorSig} (ho : o ∈ c.ovls) (hkg : kg ∈ c.ovlOver o) :
    KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg) ∈ consItemsK c := by
  unfold consItemsK
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨kg, hkg, rfl⟩⟩))

variable (hI : I ⊧ᴵP Γ c) [hO : OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI htr

/-- **Normal forms in a model.** A constructor or an overloading symbol applied to the elements of
values of its argument sorts that no function overload covers builds exactly the element of their
normal form (`norm`): a raw application where no overload covers them, else, by the overload
equation of the first overload that does, the lift of the overloaded symbol's normal form. By
induction on the rank. -/
theorem norm_gs : ∀ (n : Nat) (k : CtorSig), OvlLaws.KnownSig c k → OvlLaws.ovlRank c k.name ≤ n →
    ∀ ws, c.sortsOf ws = some k.args → c.fnCover k.name ws = none →
      ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m ↔
        m = elemOf c I (c.norm k.name ws) := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  have F := H.fnFacts
  have raw : ∀ (k : CtorSig) ws, c.sortsOf ws = some k.args → c.sortOf (.ctor k.name ws) = some k.result →
      ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) m ↔
        m = elemOf c I (.ctor k.name ws) := fun k ws hws hs m => by
    rw [← den_sig_gs hI rfl hws KoreAML.val0 m]; exact (elemOf_spec hI hs KoreAML.val0).1 m
  intro n
  induction n with
  | zero =>
    intro k hk hr ws hws _ m
    have hn := OvlLaws.lookupOvl_none_of_rank (c := c) (f := k.name) (by omega)
    rw [OvlLaws.norm_none hn]
    exact raw k ws hws (sortOf_ctor_intro ⟨k, OvlLaws.known_ctor_parts H hk hn, hws, rfl⟩) m
  | succ n ih =>
    intro k hk hr ws hws hnf m
    cases ho : c.lookupOvl k.name with
    | none =>
      rw [OvlLaws.norm_none ho]
      exact raw k ws hws (sortOf_ctor_intro ⟨k, OvlLaws.known_ctor_parts H hk ho, hws, rfl⟩) m
    | some o =>
      obtain ⟨hom, hn, -, hct, hks, -⟩ := OvlLaws.ovl_facts_ovlF F ho
      have hko : k = o.sig := OvlLaws.knownSig_inj hk hks hn.symm
      subst hko
      cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg ws) with
      | none =>
        rw [OvlLaws.norm_find_none ho hf]
        exact raw o.sig ws hws (c.sortOf_ctor_iff.mpr (.inr (.inl ⟨hct, o, ho, hws,
          OvlLaws.uncovered_of_find_none ho hf, rfl⟩))) m
      | some kg =>
        have hkg := List.mem_of_find?_eq_some hf
        have hcov := List.find?_some hf
        have hb := OvlLaws.not_byFn_of_fnCover_none hnf ho hkg hcov
        have hkk := OvlLaws.known_of_not_byFn hkg hb
        obtain ⟨hlen, hle, hres, hrank⟩ := OvlLaws.over_ovlF F ho hkg
        obtain ⟨-, hwl, hlies⟩ := OvlLaws.covers_iff.mp hcov
        have hrk : OvlLaws.ovlRank c kg.name ≤ n := by omega
        have hus := OvlLaws.sortsOf_stripAll hlen hws hlies
        have hwsl := (OvlLaws.liftAll_stripAll hlen hws hlies).symm
        have hnfk := OvlLaws.fnCover_strip_none_ovlF H F ho hkg hws hcov hnf
        generalize stripAll kg.args o.sig.args ws = us at hus hwsl hnfk
        subst hwsl
        rw [OvlLaws.norm_find_some_ovlF F ho hf hb, OvlLaws.stripAll_liftAll H hlen hus]
        have ihk := ih kg hkk hrk us hus hnfk
        have hsn := OvlLaws.sortOf_norm_known_ovlF H F _ kg hkk (OvlLaws.ovlRank_le _) us hus hnfk
        have hax := sat_cons hI (Or.inl ⟨_, ovlEqItem_mem hom hkg, rfl⟩)
        have hname : ∀ A ∈ kg.result :: kg.args, ∀ B ∈ o.sig.result :: o.sig.args,
            A ≠ B → c.sortName A ≠ c.sortName B := fun A hA B hB hne he => hne (hO.names o hom kg hkg A hA B hB he)
        have hl2 := sortsOf_length hus
        have key := ovlEq_at (defOK hI) (N := c.sortName o.sig.result) (N' := c.sortName kg.result) hax
          (zs := us.map (elemOf c I)) (ys := (liftAll kg.args o.sig.args us).map (elemOf c I))
          (by simp [toK, hl2]) (by simp [toK, hlen])
          (by simp [toK, OvlLaws.length_liftAll, hl2, hlen])
          (elems_sorts hI hus)
          (by
            intro i A B z y hA hB hz hy m'
            simp only [toK, List.getElem?_map, Option.map_eq_some_iff] at hA hB hz hy
            obtain ⟨Ai, hAi, rfl⟩ := hA
            obtain ⟨Bi, hBi, rfl⟩ := hB
            obtain ⟨u, hu, rfl⟩ := hz
            obtain ⟨w, hw, rfl⟩ := hy
            have hwu : w = lift Ai Bi u := by
              simp only [liftAll, List.getElem?_map, Option.map_eq_some_iff, List.getElem?_zip_eq_some] at hw
              obtain ⟨⟨⟨A', B'⟩, u'⟩, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hw
              rw [hAi] at h1; rw [hBi] at h2; rw [hu] at h3
              cases h1; cases h2; cases h3; rfl
            subst hwu
            obtain ⟨u', hu', hsu⟩ := sortsOf_get hus hAi
            rw [hu] at hu'; cases hu'
            by_cases hAB : Ai = Bi
            · subst hAB
              simp only [beq_self_eq_true, ↓reduceIte, OvlLaws.lift_self]
            · have hne := hname Ai (List.mem_cons_of_mem _ (List.mem_of_getElem? hAi)) Bi
                (List.mem_cons_of_mem _ (List.mem_of_getElem? hBi)) hAB
              have hsub : (Ai, Bi) ∈ c.subsorts := by
                obtain ⟨i', hi'⟩ : ∃ h : i < kg.args.length, kg.args[i] = Ai := List.getElem?_eq_some_iff.mp hAi
                obtain ⟨i'', hi''⟩ : ∃ h : i < o.sig.args.length, o.sig.args[i] = Bi := List.getElem?_eq_some_iff.mp hBi
                have := (OvlLaws.zip2_all_iff.mp hle) i i' i''
                rw [hi', hi''] at this
                exact OvlLaws.mem_of_le this hAB
              simp only [beq_iff_eq, hne, ↓reduceIte, OvlLaws.lift_ne hAB]
              rw [← den_injNormal_gs hI htr hsub hsu KoreAML.val0 m']
              exact (elemOf_spec hI (sortOf_injNormal htr hsub hsu) KoreAML.val0).1 m') m
        refine key.trans ?_
        by_cases hRR : kg.result = o.sig.result
        · rw [hRR] at ihk hsn
          simp only [toK, hRR, beq_self_eq_true, ↓reduceIte, OvlLaws.lift_self]
          exact ihk m
        · have hne := hname _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) hRR
          have hsub : (kg.result, o.sig.result) ∈ c.subsorts := OvlLaws.mem_of_le hres hRR
          simp only [toK, beq_iff_eq, hne, ↓reduceIte, OvlLaws.lift_ne hRR]
          rw [← (elemOf_spec hI (sortOf_injNormal htr hsub hsn) KoreAML.val0).1 m,
            den_injNormal_gs hI htr hsub hsn KoreAML.val0 m]
          exact ⟨fun ⟨x, hx, hm⟩ => by rw [(ihk x).mp hx] at hm; exact hm,
            fun hm => ⟨_, (ihk _).mpr rfl, hm⟩⟩

omit hI hO htr in
theorem choose_list {α : Type} {n : Nat} {P : Nat → α → Prop} (h : ∀ i < n, ∃ a, P i a) :
    ∃ l : List α, l.length = n ∧ ∀ (i : Nat) a, l[i]? = some a → P i a := by
  induction n with
  | zero => exact ⟨[], rfl, fun i a h => by simp at h⟩
  | succ n ih =>
    obtain ⟨l, hl, hP⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨a, ha⟩ := h n (by omega)
    refine ⟨l ++ [a], by simp [hl], fun i b hb => ?_⟩
    rw [List.getElem?_append] at hb
    split at hb
    · exact hP i b hb
    · rename_i hi
      have : i - l.length = 0 := by
        cases h' : i - l.length with
        | zero => rfl
        | succ k => rw [h'] at hb; simp at hb
      rw [this] at hb
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      have : i = n := by omega
      rw [this]; exact ha

set_option maxHeartbeats 1600000 in
/-- **An overloading symbol's image at a value.** If the element of a value lies in what a
constructor or an overloading symbol builds from elements of its argument sorts, those are the
elements of values whose normal form the value is. By induction on the rank: where an overload
covers the elements in the model, by its equation and the overloaded symbol's image; otherwise the
value is a raw application of the symbol itself, every other generator of its sort being apart from
it there. -/
theorem ovl_back (hg : genWf c = true) : ∀ (n : Nat) (k : CtorSig), OvlLaws.KnownSig c k →
    OvlLaws.ovlRank c k.name ≤ n → OvlLaws.NoFnOver c k.name → ∀ {w : GroundTerm}, c.sortOf w = some k.result →
    ∀ {bs : List M}, bs.length = (k.args.map c.sortName).length →
    (∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) →
    GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs (elemOf c I w) →
    ∃ ws, c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I) ∧ c.norm k.name ws = w := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  have F := H.fnFacts
  have ctorCase : ∀ k : CtorSig, OvlLaws.KnownSig c k → c.lookupOvl k.name = none → ∀ {w : GroundTerm},
      c.sortOf w = some k.result → ∀ {bs : List M}, bs.length = (k.args.map c.sortName).length →
      (∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) →
      GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs (elemOf c I w) →
      ∃ ws, c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I) ∧ c.norm k.name ws = w := by
    intro k hk hn w hw bs hbl hbs hm
    obtain ⟨ws, rfl, hws, rfl⟩ := ctor_back hI hg htr (OvlLaws.known_ctor_parts H hk hn) hw hbl hbs hm
    exact ⟨ws, hws, rfl, OvlLaws.norm_none hn ws⟩
  intro n
  induction n with
  | zero =>
    intro k hk hr _
    exact ctorCase k hk (OvlLaws.lookupOvl_none_of_rank (c := c) (f := k.name) (by omega))
  | succ n ih =>
    intro k hk hr hnb w hw bs hbl hbs hm
    cases ho : c.lookupOvl k.name with
    | none => exact ctorCase k hk ho hw hbl hbs hm
    | some o =>
    obtain ⟨-, hn, hio, hct, hks, -⟩ := OvlLaws.ovl_facts_ovlF F ho
    have hko : k = o.sig := OvlLaws.knownSig_inj hk hks hn.symm
    subst hko
    obtain ⟨hom, -, -, -, hN⟩ := OvlLaws.ovl_parts H.ok ho
    have hgo : Gen.ctor o.sig ∈ (c.gens o.sig.result).filter (!c.isOpenGen ·) := gensF_of_ovl hg hom
    have hnfo : c.fnOvl (.ctor o.sig) = false := fnOvl_of_noFnOver hnb
    obtain ⟨y, -, hy⟩ := gen_fun hI hN hgo hnfo hbl hbs
    have hyw : y = elemOf c I w := ((hy _).mp hm).symm
    have hset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) bs m ↔ m = elemOf c I w :=
      fun m => by rw [hy, hyw]
    have hname : ∀ kg ∈ c.ovlOver o, ∀ A ∈ kg.result :: kg.args, ∀ B ∈ o.sig.result :: o.sig.args,
        A ≠ B → c.sortName A ≠ c.sortName B := fun kg hkg A hA B hB hne he => hne (hO.names o hom kg hkg A hA B hB he)
    have hbl' : bs.length = o.sig.args.length := by simpa using hbl
    by_cases hcov : ∃ kg ∈ c.ovlOver o, ∀ (i : Nat) (A B : Srt) (b : M), kg.args[i]? = some A →
        o.sig.args[i]? = some B → bs[i]? = some b → A ≠ B →
        ∃ y, InS I (c.sortName A) y ∧ GS I (c.sortName B) (.inj (c.sortName A)) [y] b
    · obtain ⟨kg, hkg, hcv⟩ := hcov
      have hkk := OvlLaws.known_of_not_byFn hkg (hnb o ho kg hkg)
      have hnbk := hnb.over F ho hkg
      obtain ⟨hlen, hle, hres, hrank⟩ := OvlLaws.over_ovlF F ho hkg
      have hrk : OvlLaws.ovlRank c kg.name ≤ n := by omega
      have hsubAt : ∀ (i : Nat) (A B : Srt), kg.args[i]? = some A → o.sig.args[i]? = some B → A ≠ B →
          (A, B) ∈ c.subsorts := fun i A B hA hB hAB => by
        obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp hA
        obtain ⟨h2, rfl⟩ := List.getElem?_eq_some_iff.mp hB
        exact OvlLaws.mem_of_le ((OvlLaws.zip2_all_iff.mp hle) i h1 h2) hAB
      -- the elements of kg's argument sorts that the arguments lift
      obtain ⟨zs, hzl, hzs⟩ := choose_list (n := bs.length) (P := fun i z => ∀ A B b, kg.args[i]? = some A →
          o.sig.args[i]? = some B → bs[i]? = some b → InS I (c.sortName A) z ∧ (A = B → z = b) ∧
            (A ≠ B → GS I (c.sortName B) (.inj (c.sortName A)) [z] b)) (fun i hi => by
        obtain ⟨A, hA⟩ : ∃ A, kg.args[i]? = some A := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨B, hB⟩ : ∃ B, o.sig.args[i]? = some B := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨_, List.getElem?_eq_getElem hi⟩
        have hbB : InS I (c.sortName B) b := hbs i b _ hb (by simp [hB])
        by_cases hAB : A = B
        · subst hAB
          exact ⟨b, fun A' B' b' hA' hB' hb' => by
            rw [hA] at hA'; rw [hB] at hB'; rw [hb] at hb'; cases hA'; cases hB'; cases hb'
            exact ⟨hbB, fun _ => rfl, fun h => absurd rfl h⟩⟩
        · obtain ⟨z, hz, hzb⟩ := hcv i A B b hA hB hb hAB
          exact ⟨z, fun A' B' b' hA' hB' hb' => by
            rw [hA] at hA'; rw [hB] at hB'; rw [hb] at hb'; cases hA'; cases hB'; cases hb'
            exact ⟨hz, fun h => absurd h hAB, fun _ => hzb⟩⟩)
      have hax := sat_cons hI (Or.inl ⟨_, ovlEqItem_mem hom hkg, rfl⟩)
      have hzsorts : ∀ (i : Nat) x s, zs[i]? = some x → (kg.args.map c.sortName)[i]? = some s → InS I s x := by
        intro i x s hx hs
        simp only [List.getElem?_map, Option.map_eq_some_iff] at hs
        obtain ⟨A, hA, rfl⟩ := hs
        have hi : i < bs.length := by rw [← hzl]; exact (List.getElem?_eq_some_iff.mp hx).1
        exact (hzs i x hx A _ _ hA (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)).1
      have key := ovlEq_at (defOK hI) (N := c.sortName o.sig.result) (N' := c.sortName kg.result) hax
        (zs := zs) (ys := bs) (by simp [toK, hzl, hbl', hlen]) (by simp [toK, hlen]) (by simp [toK, hbl', hlen])
        hzsorts (by
          intro i A B z b hA hB hz hb m'
          simp only [toK, List.getElem?_map, Option.map_eq_some_iff] at hA hB
          obtain ⟨Ai, hAi, rfl⟩ := hA
          obtain ⟨Bi, hBi, rfl⟩ := hB
          obtain ⟨hzA, heq, hne⟩ := hzs i z hz Ai Bi b hAi hBi hb
          by_cases hAB : Ai = Bi
          · subst hAB; simp only [beq_self_eq_true, ↓reduceIte, heq rfl]
          · have hn' := hname kg hkg Ai (List.mem_cons_of_mem _ (List.mem_of_getElem? hAi)) Bi
              (List.mem_cons_of_mem _ (List.mem_of_getElem? hBi)) hAB
            simp only [beq_iff_eq, hn', ↓reduceIte]
            have hsub := hsubAt i Ai Bi hAi hBi hAB
            obtain ⟨y', -, hy'⟩ := gen_fun hI (genWf_sub hg hsub).1 (gensF_inj hsub) rfl (xs := [z]) rfl (single_sorts hzA)
            have : y' = b := ((hy' b).mp (hne hAB)).symm
            subst this
            exact hy' m') (elemOf c I w)
      have hk := key.mp hm
      -- the overloaded symbol's image, at a value of its result sort lifted to w
      have hkgres : kg.result ∈ consSorts c := by
        rcases OvlLaws.knownSig_mem hkk with h | h
        · exact genWf_ctor hg h
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp h
          exact (OvlLaws.ovl_parts H.ok (OvlLaws.lookupOvl_of_mem H ho')).2.2.2.2
      have hgkg : Gen.ctor kg ∈ (c.gens kg.result).filter (!c.isOpenGen ·) := by
        rcases OvlLaws.knownSig_mem hkk with h | h
        · exact gensF_ctor hg h
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp h
          exact gensF_of_ovl hg ho'
      have hzl' : zs.length = (kg.args.map c.sortName).length := by simp [hzl, hbl', hlen]
      obtain ⟨w0, hw0, hww, us, hus, hzu, hnu⟩ : ∃ w0, c.sortOf w0 = some kg.result ∧
          w = lift kg.result o.sig.result w0 ∧ ∃ us, c.sortsOf us = some kg.args ∧ zs = us.map (elemOf c I) ∧
            c.norm kg.name us = w0 := by
        by_cases hRR : kg.result = o.sig.result
        · simp only [toK, hRR, beq_self_eq_true, ↓reduceIte] at hk
          rw [← hRR] at hw hk
          obtain ⟨us, hus, hzu, hnu⟩ := ih kg hkk hrk hnbk hw hzl' hzsorts hk
          exact ⟨w, hw, by rw [hRR, OvlLaws.lift_self], us, hus, hzu, hnu⟩
        · have hn' := hname kg hkg _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) hRR
          have hsub : (kg.result, o.sig.result) ∈ c.subsorts := OvlLaws.mem_of_le hres hRR
          simp only [toK, beq_iff_eq, hn', ↓reduceIte] at hk
          obtain ⟨x, hx, hxw⟩ := hk
          obtain ⟨y2, hy2s, hy2⟩ := gen_fun hI hkgres hgkg (fnOvl_of_noFnOver hnbk) hzl' hzsorts
          have hxy : x = y2 := (hy2 x).mp hx
          subst hxy
          obtain ⟨w', hw', rfl, rfl⟩ := inj_back hI hg htr w hsub hw hy2s hxw
          obtain ⟨us, hus, hzu, hnu⟩ := ih kg hkk hrk hnbk hw' hzl' hzsorts hx
          exact ⟨w', hw', (OvlLaws.lift_ne hRR w').symm, us, hus, hzu, hnu⟩
      subst hzu
      refine ⟨liftAll kg.args o.sig.args us, OvlLaws.sortsOf_liftAll H hlen hus hle, ?_, ?_⟩
      · have hul := sortsOf_length hus
        refine List.ext_getElem? fun i => ?_
        by_cases hi : i < bs.length
        · obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨_, List.getElem?_eq_getElem hi⟩
          obtain ⟨A, hA⟩ : ∃ A, kg.args[i]? = some A := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨B, hB⟩ : ∃ B, o.sig.args[i]? = some B := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨u, hu⟩ : ∃ u, us[i]? = some u := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hz : (us.map (elemOf c I))[i]? = some (elemOf c I u) := by simp [hu]
          obtain ⟨-, heq, hne⟩ := hzs i _ hz A B b hA hB hb
          obtain ⟨u', hu', hsu⟩ := sortsOf_get hus hA
          rw [hu] at hu'; cases hu'
          have hli : (liftAll kg.args o.sig.args us)[i]? = some (lift A B u) := by
            have hz3 : ((kg.args.zip o.sig.args).zip us)[i]? = some ((A, B), u) :=
              List.getElem?_zip_eq_some.mpr ⟨List.getElem?_zip_eq_some.mpr ⟨hA, hB⟩, hu⟩
            rw [liftAll, List.getElem?_map, hz3]; rfl
          rw [hb, List.getElem?_map, hli]
          by_cases hAB : A = B
          · subst hAB; rw [OvlLaws.lift_self, ← heq rfl]; rfl
          · have hsub := hsubAt i A B hA hB hAB
            rw [OvlLaws.lift_ne hAB]
            have := (den_injNormal_gs hI htr hsub hsu KoreAML.val0 b).mpr (hne hAB)
            rw [(elemOf_spec hI (sortOf_injNormal htr hsub hsu) KoreAML.val0).1 b] at this
            rw [this]; rfl
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [OvlLaws.length_liftAll]; omega)]
      · have hws := OvlLaws.sortsOf_liftAll H hlen hus hle
        have hcv' : c.ovlCovers o.sig kg (liftAll kg.args o.sig.args us) = true :=
          OvlLaws.covers_iff.mpr ⟨hlen, sortsOf_length hws, OvlLaws.lies_liftAll hlen hus⟩
        rw [OvlLaws.norm_coherent_ovlF H F _ o.sig.name o ho (OvlLaws.ovlRank_le _) _ hws (hnb.fnCover_none _) kg hkg hcv',
          OvlLaws.stripAll_liftAll H hlen hus, hnu, hww]
    · -- no overload covers the elements: the value is a raw application of o itself
      have hU : ∀ covs, ovlArgsOf c (.ctor o.sig) = some covs → UncE I covs (Gen.toK c (.ctor o.sig)).argSorts bs := by
        intro covs hcovs
        simp only [ovlArgsOf, hn, hio, ↓reduceIte, ho, Option.map_some, Option.some.injEq] at hcovs
        subst hcovs
        intro as has
        obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp has
        obtain ⟨i, A, B, b, hA, hB, hb, hAB, hnl⟩ : ∃ (i : Nat) (A B : Srt) (b : M), kg.args[i]? = some A ∧
            o.sig.args[i]? = some B ∧ bs[i]? = some b ∧ A ≠ B ∧
            ¬ ∃ y, InS I (c.sortName A) y ∧ GS I (c.sortName B) (.inj (c.sortName A)) [y] b :=
          Classical.byContradiction fun hc => hcov ⟨kg, hkg, fun i A B b hA hB hb hAB =>
            Classical.byContradiction fun hl => hc ⟨i, A, B, b, hA, hB, hb, hAB, hl⟩⟩
        exact ⟨i, c.sortName A, c.sortName B, b, by simp [hA], by
          show (o.sig.args.map c.sortName)[i]? = _
          simp [hB], hname kg hkg A (List.mem_cons_of_mem _ (List.mem_of_getElem? hA)) B
            (List.mem_cons_of_mem _ (List.mem_of_getElem? hB)) hAB, hb, hnl⟩
      have hback : ∀ u : GroundTerm, ∀ (A B : Srt), (A, B) ∈ c.subsorts → c.sortOf u = some B → ∀ (y : M),
          InS I (c.sortName A) y → GS I (c.sortName B) (.inj (c.sortName A)) [y] (elemOf c I u) →
          c.lies A B u = true := fun u A B hAB hsu y hy hmy => by
        obtain ⟨w', hw', rfl, -⟩ := inj_back hI hg htr u hAB hsu hy hmy
        exact lies_injNormal hw'
      rcases consSort_shape hg hN hw with ⟨g, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
      · rcases sortOf_ctor_cases hg hw with ⟨kg, hkg, hws, hres⟩ | ⟨o', hlo', -, hws, hu, hres, -⟩ |
          ⟨kp, hko, -, -, -, -, hres, -⟩
        rotate_right
        · -- no overloading symbol has an open generator's sort (`genWf`'s flat conjunct)
          exact absurd hres (genWf_flat_ovl hg (c.lookupOpen_spec hko).1 (c.lookupOpen_spec hko).2.1
            (List.mem_map_of_mem (f := (·.sig)) hom))
        · exfalso
          obtain ⟨hkgm, -⟩ := lookupSig_spec hkg
          have hvset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor kg)) (ws.map (elemOf c I)) m ↔
              m = elemOf c I (.ctor g ws) := fun m => by
            rw [hres, ← den_ctor_gs hI hkg hws KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
          rw [lookupSig_eq] at hct
          exact gen_dist' hI hN hgo (by rw [hres]; exact gensF_ctor hg hkgm)
            (fun h => by injection h with h; subst h; exact absurd (List.find?_eq_none.mp hct _ hkgm) (by simp))
            (fun _ _ h _ => by cases h) hbl (elems_length hI hws) hbs (elems_sorts hI hws) hU
            (fun covs h => by simp [ovlArgsOf, isOvl_of_ctorSigs hkgm] at h) (fun m => by rw [hset, hvset])
        · by_cases hgf : g = o.sig.name
          · subst hgf
            rw [ho] at hlo'
            cases hlo'
            have hvset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (ws.map (elemOf c I)) m ↔
                m = elemOf c I (.ctor o.sig.name ws) := fun m => by
              rw [← den_sig_gs hI rfl hws KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
            refine ⟨ws, hws, ?_, OvlLaws.norm_fixed_ovlF H F ho hw⟩
            by_cases hne : o.sig.args = []
            · have h1 : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hbl, hne]; rfl)
              rw [hne] at hws
              rw [h1, sortsOf_nil_eq hws]; rfl
            · exact gen_inj hI hN hgo hne hnfo hbl (elems_length hI hws) hbs (elems_sorts hI hws)
                (fun m => by rw [hset, hvset])
          · exfalso
            obtain ⟨hom', hn', -⟩ := OvlLaws.ovl_parts H.ok hlo'
            have hvset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o'.sig)) (ws.map (elemOf c I)) m ↔
                m = elemOf c I (.ctor g ws) := fun m => by
              rw [hres, ← den_sig_gs hI hn' hws KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
            exact gen_dist' hI hN hgo (by rw [hres]; exact gensF_of_ovl hg hom')
              (fun h => by injection h with h; exact hgf (by rw [← hn', ← h]))
              (fun _ _ h _ => by cases h) hbl (elems_length hI hws) hbs (elems_sorts hI hws) hU
              (uncE_of_value hI hg htr hlo' hws hu fun u _ => hback u) (fun m => by rw [hset, hvset])
      · exfalso
        obtain ⟨hab, -, hw0, hb⟩ := sortOf_inj.mp hw
        subst hb
        have hvset : ∀ m, GS I (c.sortName o.sig.result) (.inj (c.sortName a)) [elemOf c I w0] m ↔
            m = elemOf c I (.inj a o.sig.result w0) := fun m => by
          rw [← den_inj_gs hI hw0 KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
        exact gen_dist' hI hN hgo (gensF_inj hab) (fun h => by cases h) (fun _ _ h _ => by cases h) hbl rfl hbs
          (single_sorts ((inS_iff _).mp (elemOf_spec hI hw0 KoreAML.val0).2)) hU
          (fun covs h => by simp [ovlArgsOf] at h) (fun m => by rw [hset]; exact (hvset m).symm)

/-- **A function-covered application in a model.** An overloading symbol applied to the elements
of values of its argument sorts that the function overload `kg` covers is what `kg` applied to the
elements of the stripped arguments is, lifted to the symbol's result sort: by the overload's
equation, which `Γ` holds of every overload, a function's too. Where the function's application
denotes nothing, so does the symbol's. -/
theorem covDen_of {f : Sym} {o : OvlSig} {ws : List GroundTerm} {kg : CtorSig} {r : Option GroundTerm}
    (hlo : c.lookupOvl f = some o) (hws : c.sortsOf ws = some o.sig.args) (hcov : c.fnCover f ws = some kg)
    (hpl : iteSort? (c.symName kg.name) = none) (hr : ∀ v, r = some v → c.sortOf v = some kg.result)
    (e : Valuation M)
    (hg : ∀ m, (KoreAML.den (symApp c kg.name (GroundTerm.koreList c (stripAll kg.args o.sig.args ws)))).interpret I e m ↔
      Res c I e r m) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔
      Res c I e (r.map (lift kg.result o.sig.result)) m := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  have F := H.fnFacts
  obtain ⟨hom, hn, -, -, -, -⟩ := OvlLaws.ovl_facts_ovlF F hlo
  obtain ⟨-, -, -, hplain, -⟩ := OvlLaws.ovl_parts H.ok hlo
  obtain ⟨o', ho', hkg, -, hcv⟩ := OvlLaws.fnCover_some_parts hcov
  rw [hlo] at ho'; cases ho'
  obtain ⟨hlen, hle, hres, -⟩ := OvlLaws.over_ovlF F hlo hkg
  obtain ⟨-, -, hlies⟩ := OvlLaws.covers_iff.mp hcv
  have hus := OvlLaws.sortsOf_stripAll hlen hws hlies
  have hwsl := (OvlLaws.liftAll_stripAll hlen hws hlies).symm
  have hsym : KoreAML.den (symApp c f (GroundTerm.koreList c ws)) = den c (.ctor f ws) := by
    unfold symApp; rw [hplain]; rfl
  rw [hsym, den_sig_gs hI hn hws e m]
  generalize stripAll kg.args o.sig.args ws = us at hus hwsl hg
  -- the function's application, as the generator `kg` at the elements of the stripped arguments
  have hgs : ∀ x, GS I (c.sortName kg.result) (Gen.toK c (.ctor kg)) (us.map (elemOf c I)) x ↔ Res c I e r x := by
    intro x
    rw [← hg x]
    have hsym' : KoreAML.den (symApp c kg.name (GroundTerm.koreList c us)) = den c (.ctor kg.name us) := by
      unfold symApp; rw [hpl]; rfl
    rw [hsym', den_sig_gs hI rfl hus e x]
  have hax := sat_cons hI (Or.inl ⟨_, ovlEqItem_mem hom hkg, rfl⟩)
  have hname : ∀ A ∈ kg.result :: kg.args, ∀ B ∈ o.sig.result :: o.sig.args,
      A ≠ B → c.sortName A ≠ c.sortName B := fun A hA B hB hne he => hne (hO.names o hom kg hkg A hA B hB he)
  have hl2 := sortsOf_length hus
  have key := ovlEq_at (defOK hI) (N := c.sortName o.sig.result) (N' := c.sortName kg.result) hax
    (zs := us.map (elemOf c I)) (ys := ws.map (elemOf c I))
    (by simp [toK, hl2]) (by simp [toK, hlen])
    (by rw [hwsl]; simp [toK, OvlLaws.length_liftAll, hl2, hlen])
    (elems_sorts hI hus)
    (by
      rw [hwsl]
      intro i A B z y hA hB hz hy m'
      simp only [toK, List.getElem?_map, Option.map_eq_some_iff] at hA hB hz hy
      obtain ⟨Ai, hAi, rfl⟩ := hA
      obtain ⟨Bi, hBi, rfl⟩ := hB
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨w, hw, rfl⟩ := hy
      have hwu : w = lift Ai Bi u := by
        simp only [liftAll, List.getElem?_map, Option.map_eq_some_iff, List.getElem?_zip_eq_some] at hw
        obtain ⟨⟨⟨A', B'⟩, u'⟩, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hw
        rw [hAi] at h1; rw [hBi] at h2; rw [hu] at h3
        cases h1; cases h2; cases h3; rfl
      subst hwu
      obtain ⟨u', hu', hsu⟩ := sortsOf_get hus hAi
      rw [hu] at hu'; cases hu'
      by_cases hAB : Ai = Bi
      · subst hAB
        simp only [beq_self_eq_true, ↓reduceIte, OvlLaws.lift_self]
      · have hne := hname Ai (List.mem_cons_of_mem _ (List.mem_of_getElem? hAi)) Bi
          (List.mem_cons_of_mem _ (List.mem_of_getElem? hBi)) hAB
        have hsub : (Ai, Bi) ∈ c.subsorts := by
          obtain ⟨i', hi'⟩ : ∃ h : i < kg.args.length, kg.args[i] = Ai := List.getElem?_eq_some_iff.mp hAi
          obtain ⟨i'', hi''⟩ : ∃ h : i < o.sig.args.length, o.sig.args[i] = Bi := List.getElem?_eq_some_iff.mp hBi
          have := (OvlLaws.zip2_all_iff.mp hle) i i' i''
          rw [hi', hi''] at this
          exact OvlLaws.mem_of_le this hAB
        simp only [beq_iff_eq, hne, ↓reduceIte, OvlLaws.lift_ne hAB]
        rw [← den_injNormal_gs hI htr hsub hsu KoreAML.val0 m']
        exact (elemOf_spec hI (sortOf_injNormal htr hsub hsu) KoreAML.val0).1 m') m
  refine key.trans ?_
  by_cases hRR : kg.result = o.sig.result
  · simp only [toK, hRR, beq_self_eq_true, ↓reduceIte, OvlLaws.lift_self]
    rw [hRR] at hgs
    refine (hgs m).trans ?_
    cases r with
    | none => exact Iff.rfl
    | some v => rw [Option.map_some, OvlLaws.lift_self]
  · have hne := hname _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) hRR
    have hsub : (kg.result, o.sig.result) ∈ c.subsorts := OvlLaws.mem_of_le hres hRR
    simp only [toK, beq_iff_eq, hne, ↓reduceIte]
    cases r with
    | none =>
      simp only [Option.map_none, Res, iff_false]
      rintro ⟨x, hx, -⟩
      exact (hgs x).mp hx
    | some v =>
      have hv := hr v rfl
      simp only [Option.map_some, Res, OvlLaws.lift_ne hRR]
      rw [den_injNormal_gs hI htr hsub hv e m]
      have hx : ∀ x, GS I (c.sortName kg.result) (Gen.toK c (.ctor kg)) (us.map (elemOf c I)) x ↔ x = elemOf c I v :=
        fun x => (hgs x).trans ((elemOf_spec hI hv e).1 x)
      exact ⟨fun ⟨x, hx', hm⟩ => by rw [(hx x).mp hx'] at hm; exact hm,
        fun hm => ⟨_, (hx _).mpr rfl, hm⟩⟩

/-- **Every model of `Γ` reads the overloading symbols by their normal forms** at arguments no
function overload covers, and by the covering function's value at the others (`NormDen`). -/
theorem normDen_of : NormDen c I := by
  refine ⟨?_, fun hlo hws hcov hpl hr e hg m => covDen_of hI htr hlo hws hcov hpl hr e hg m⟩
  intro f o ws hlo hws hnf e m
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  obtain ⟨-, hn, -, -, hks, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts hlo
  obtain ⟨-, -, -, hplain, -⟩ := OvlLaws.ovl_parts H.ok hlo
  have hg := norm_gs hI htr _ o.sig hks (OvlLaws.ovlRank_le _) ws hws (by rw [hn]; exact hnf)
  rw [hn] at hg
  have hsym : KoreAML.den (symApp c f (GroundTerm.koreList c ws)) = den c (.ctor f ws) := by
    unfold symApp; rw [hplain]; rfl
  rw [hsym, den_sig_gs hI hn hws e m, (elemOf_spec hI (OvlLaws.sortOf_norm_ovlF H H.fnFacts hlo hws hnf) e).1 m]
  exact hg m

end

/-- **L4.** In the first stage, every step of `Step` is a consequence of `Γ`: in every model, the
configuration `x` has the configuration `y` as a successor. -/
theorem step_sound_stage1 (c : Semantics) [OvlOK c] (hy : Hyp c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hs : Stage1 c) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := by
  have hy : HypCore c := hy.core (Semantics.overloadsOK_pats OvlOK.ok)
  have hnn : NamesNumbered c := hy.2.2.2.2.2.2
  intro x y hstep M _ I hI e m hm
  obtain ⟨r, hr, σ, hσ, hmatch, hreq, -, heval, hens, -, -⟩ := hstep
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hsc := sortCtx_of_all hy.1 hy.2.1 (OvlOK.ovlCase inferInstance)
  have hmi := CoherentAll_of hy
  obtain ⟨hlhs, hreqs, hrhss⟩ := rule_ctx hy.1 hr
  have hbinds := Exec.binds_all (hb _ hr)
  have hensS := rule_ctx_ens hy.1 hr
  obtain ⟨hplain, hcalls⟩ := hs.2.1 r hr
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  -- the rule's axiom is the one without competitors
  have hprio : prioRuleK c r = (ruleAxiom c r).pattern := by
    have hnil : c.rules.filter (·.prio < r.prio) = [] :=
      List.filter_eq_nil_iff.mpr (fun r' hr' => by simpa using hs.1 r hr r' hr')
    obtain ⟨hpre, hpost⟩ := htop _ hr
    have hex : r.exs = [] := Semantics.sortedOK_exsNil hy.1 hr (hb r hr)
    rw [prioRuleK_top hex hpre hpost]
    dsimp only
    rw [hnil]
    rfl
  have hax := sat_rules hI (Or.inl ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩)
  rw [hprio] at hax
  let vs := canonVars c r.vars
  let tbl : VarTable := KoreAML.tableOf (ruleAxiom c r).sortVars (ruleAxiom c r).pattern
  let e' : Valuation M := valOf tbl (ruleVal c I r.vars.length σ)
  have hVmem : ∀ i, i < r.vars.length → canonKey c r.vars i ∈ tbl := fun i hi => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    unfold ruleAxiom; dsimp only
    rw [KoreAML.varsOf, KoreAML.varsOf, KoreAML.varsOfList]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (varsOf_kore c vs r.lhs (hbinds i hi)))))
  have hVv : ∀ i, i < r.vars.length → e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      (match σ.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [ruleVal]
    rw [varIdx_eq hi]
    try rfl
  have hvsort : ∀ i, i < r.vars.length → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  have hfree : ∀ k, k ∈ KoreAML.freeOf [] (ruleAxiom c r).pattern → ∃ i, i < r.vars.length ∧ k = canonKey c r.vars i := by
    intro k hk
    unfold ruleAxiom at hk; dsimp only at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append, List.not_mem_nil,
      or_false] at hk
    obtain ⟨i, hi, h⟩ : ∃ i < r.vars.length, k = canonKey c r.vars i := by
      rcases hk with (hk | hk | hk | hk) | hk | hk
      · exact freeOf_rule_parts hy.1 hr (Or.inl hk)
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inl hk))
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inr (Or.inl hk)))
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inr (Or.inr hk)))
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inr (Or.inl hk)))
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inr (Or.inr hk)))
    exact ⟨i, hi, h⟩
  have hg : ∀ k ∈ ((ruleAxiom c r).sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (ruleAxiom c r).pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] (ruleAxiom c r).pattern := by
      simpa [ruleAxiom] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, rfl⟩ := hfree k hk'
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hVv i hi, hw]
    exact (elemOf_spec hI hsw e').2
  -- the configuration x and its element
  obtain ⟨a, ha, has⟩ := den_single hI x.property e'
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  have hP' : (KoreAML.tr ⟨tbl, []⟩ (.rewrites (srtOf c topCellSort)
      (.and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs)),
        .ceil (srtOf c topCellSort) (srtOf c topCellSort) (.and (srtOf c topCellSort) [Term.kore c vs r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs))])])
      (.and (srtOf c topCellSort) [Term.kore c vs r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs))]))).interpret I e' a := hP
  have hrhsR := fun b => evalTerm_den hI hnn hsc hs hy.1 hbc hmi (normDen_of hI hsc.trans) heval fns_headsOK hσ (canonVars_length c r.vars) hag hrhss
    (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_left _ hg))) b
  have hrightR := right_den hI hrhsR (fun a' ha' => reqPat_holds hI (fun t ht b =>
    evalTerm_den hI hnn hsc hs hy.1 hbc hmi (normDen_of hI hsc.trans) (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag
      (hensS t ht) (fun g hg => hcalls g (List.mem_append_right _ (by rw [ht]; exact hg))) b) ha')
  rw [KoreAML.tr] at hP'
  unfold KoreAML.sRewrites at hP'
  rw [KoreAML.interp_sImp] at hP'
  obtain ⟨-, himp⟩ := hP'
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e' b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have haC : Inh I σC a := by
    unfold srtOf at hSC
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp has
  have hL := himp (by
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    refine ⟨(patVal_den hI hnn.1 hsc.trans hσ (canonVars_length c r.vars) hag hmatch hplain hlhs).2 a |>.mpr
      ((ha a).mpr rfl), ?_, ceil_rhs_at hI hrightR (by unfold srtOf; rw [trSort_srt]; exact has)⟩
    cases hq : r.req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSC]
      exact haC
    | some t =>
      simp only [Option.map_some, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hSC hσB2 hσC2]
      refine ⟨haC, fun b _ => ?_⟩
      rw [evalTerm_den hI hnn hsc hs hy.1 hbc hmi (normDen_of hI hsc.trans) (hreq t hq) fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t hq)
        (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_right _ (by rw [hq]; exact hg)))) b, KoreAML.tr_dv]
      show (den c (bool true)).interpret I e' b ↔ _
      unfold den KoreAML.den bool
      rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
      exact Iff.rfl)
  -- the successor
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL
  rw [tr_and2, KoreAML.interp_sAnd] at hb
  have hby := (hrhsR b).mp hb.1
  have hma : m = a := by
    have := ((den_closed c x.val).interp e e' m).mp hm
    exact (ha m).mp this
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, ((den_closed c y.val).interp e' e b).mp hby, happ⟩

end Faithful

end KCore
