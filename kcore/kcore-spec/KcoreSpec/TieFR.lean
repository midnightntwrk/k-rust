/-
  An equation whose right side is a union of alternatives, of a function with its `functional`
  sentence, against the n+1 equations of its split (`Parse.frClauses`), on the translated axioms:
  the sorted form of the union tie (TieUnion.lean).

  A translated equation axiom has the shape `ws → ((prem →_R F =_{S,R} B) = ⟦R⟧)` (`eqnPat`;
  `trAxiom_eqnPat`): where the guards `ws` hold, at every element m of the sort R holds, if `prem`
  holds at m then F and B agree on the sort S. A translated functional axiom has the shape
  `ws → ((∃v:S. v =_{S,R} F') = ⟦R⟧)` (`fnlPat`; `trAxiom_fnlPat`).

  The sentence is `prem → F = rhs`, its right side holding at an element of S exactly the elements
  of the alternatives aₖ at which their predicates Gₖ hold. The split:
  - for each k, `Q k → F = aₖ ∧ ⊤_S`, where `Q k` holds exactly where `prem` holds, aₖ is defined
    and Gₖ holds;
  - `QN → F = BN`, where `QN` holds exactly where `prem` holds and no alternative is defined with
    its predicates.
  What each pattern means at a valuation that satisfies the guards (`Readings`) is a hypothesis:
  it is the reading of the patterns the split writes, not a statement about K.

  - `clause_of_text`: the sentence and the functional sentence give each alternative's equation.
    The functional sentence, read at the equation's arguments (`one_of_fnl`), makes F one element
    of S; a defined alternative lies in S (`Readings.inSort`), is inside the right side, so is F's
    element.
  - `none_of_text`: the sentence and the functional sentence give the last equation, vacuously:
    where no alternative is defined with its predicates the sentence leaves F no element of S, and
    the functional sentence gives it one. The last clause's right side is not read.
  - `text_of_split`: the n+1 equations give the sentence, with no functional sentence, where the
    last clause's right side has no element of S wherever no alternative is defined with its
    predicates (`NoneEmpty`). The split writes that right side as `a₁ ∧ ⌈false = true⌉`. Where
    a₁'s predicates are none, `¬⌈a₁⌉` empties it (`noneEmpty_of_sub`). Where they are not, a₁ may
    be defined there, and its emptiness is that `false` and `true` are distinct elements of Bool
    (`noneEmpty_of_empty`): a fact neither the sentence nor the functional sentence states.

  The functional sentence names its own variables (`K0, …`, the bound `Val`): `one_of_fnl` reads
  it at the valuation that gives each `Kj` the equation's j-th argument (`renameVal`).
-/
import KcoreSpec.TieUnion

set_option autoImplicit false

namespace KoreAML

open ML

namespace TieFR

/-! ## The shapes of the translated axioms -/

/-- `ws → ((prem →_R F =_{S,R} B) = ⟦R⟧)`, R the sort the variable r holds. -/
def eqnPat (ws : List P) (r : EVar) (prem S F B : P) : P :=
  conjList ws ⇒ (sImp (.evar r) prem (sEquals S (.evar r) F B) ≡ inhOf (.evar r))

/-- `ws → ((∃v:S. v =_{S,R} F) = ⟦R⟧)`, R the sort the variable r holds. -/
def fnlPat (ws : List P) (r v : EVar) (S F : P) : P :=
  conjList ws ⇒ (sExists v S (sEquals S (.evar r) (.evar v) F) ≡ inhOf (.evar r))

/-- The guards `trAxiom` writes for an axiom. -/
def guardsOf (a : Kore.Axiom) : List P :=
  (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups.map (guardOf (tableOf a.sortVars a.pattern))

/-- **A translated equation axiom** `prem → F =_{S,R} (rhs ∧ ens)` over the sort variable R has the
shape `eqnPat`. -/
theorem trAxiom_eqnPat (ds : List SymbolDecl) (al : List String) (i : Nat) (mod : String) (a : Kore.Axiom)
    {prem F rhs ens : Kore.Pattern} {S : Kore.KSort} (hv : a.sortVars = [Rv])
    (hp : a.pattern = .implies R prem (.equals S R F (.and S [rhs, ens]))) :
    (trAxiom ds al ⟨i, mod, a⟩).pat =
      eqnPat (guardsOf a) ((tableOf a.sortVars a.pattern).ev (sortVarKey Rv))
        (tr ⟨tableOf a.sortVars a.pattern, al⟩ prem) (trSort (tableOf a.sortVars a.pattern) S)
        (tr ⟨tableOf a.sortVars a.pattern, al⟩ F)
        (sAnd (tr ⟨tableOf a.sortVars a.pattern, al⟩ rhs) (tr ⟨tableOf a.sortVars a.pattern, al⟩ ens)) := by
  unfold trAxiom eqnPat guardsOf
  simp only [hp, hv]
  simp only [sortOf, tr, trAndList, R, trSort]

/-- **A translated functional axiom** `∃v:S. v =_{S,R} F` over the sort variable R has the shape
`fnlPat`. -/
theorem trAxiom_fnlPat (ds : List SymbolDecl) (al : List String) (i : Nat) (mod : String) (a : Kore.Axiom)
    {F : Kore.Pattern} {v : Kore.EVar} (hv : a.sortVars = [Rv])
    (hp : a.pattern = .exist R v (.equals v.sort R (.var (.evar v)) F)) :
    (trAxiom ds al ⟨i, mod, a⟩).pat =
      fnlPat (guardsOf a) ((tableOf a.sortVars a.pattern).ev (sortVarKey Rv))
        ((tableOf a.sortVars a.pattern).ev (evarKey v)) (trSort (tableOf a.sortVars a.pattern) v.sort)
        (tr ⟨tableOf a.sortVars a.pattern, al⟩ F) := by
  unfold trAxiom fnlPat guardsOf
  simp only [hp, hv]
  simp only [sortOf, tr, R, trSort]

variable {M : Type} {I : Interpretation Sym M}

/-! ## Reading the shapes at a valuation -/

/-- The guards `ws` hold at e and m, and m is in the sort the variable r holds. -/
def At (I : Interpretation Sym M) (ws : List P) (r : EVar) (e : Valuation M) (m : M) : Prop :=
  (∀ w ∈ ws, w.interpret I e m) ∧ Inh I (e.evalEvar r) m

/-- A guard holds at every element where it holds at one. -/
def GuardsPred (I : Interpretation Sym M) (ws : List P) : Prop :=
  ∀ w ∈ ws, ∀ (e : Valuation M) (m m' : M), w.interpret I e m → w.interpret I e m'

/-! ## The functional sentence at the equation's arguments -/

/-- `f` updated so that, for each triple t of `ts`, the variable `t.2.1` holds what `e` gives `t.1`. -/
def updT (e : Valuation M) (f : EVar → M) : List (EVar × EVar × P) → EVar → M
  | [] => f
  | t :: ts => Function.update (updT e f ts) t.2.1 (e.evalEvar t.1)

theorem updT_out (e : Valuation M) (f : EVar → M) :
    ∀ (ts : List (EVar × EVar × P)) (k : EVar), k ∉ ts.map (·.2.1) → updT e f ts k = f k
  | [], _, _ => rfl
  | t :: ts, k, hk => by
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    simp only [updT]
    rw [Function.update_noteq hk.1]
    exact updT_out e f ts k hk.2

theorem updT_in (e : Valuation M) (f : EVar → M) :
    ∀ (ts : List (EVar × EVar × P)), (ts.map (·.2.1)).Nodup → ∀ t ∈ ts, updT e f ts t.2.1 = e.evalEvar t.1
  | [], _, _, ht => by cases ht
  | t0 :: ts, hnd, t, ht => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [updT]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Function.update_same ..
    · have hne : t.2.1 ≠ t0.2.1 := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)
      rw [Function.update_noteq hne]
      exact updT_in e f ts hnd.2 t ht

/-- The valuation that reads the functional sentence at the equation's arguments: r' holds what r
holds, and each `t.2.1` what `t.1` holds. -/
def renameVal (e : Valuation M) (r r' : EVar) (ts : List (EVar × EVar × P)) : Valuation M :=
  ⟨updT e (Function.update e.evalEvar r' (e.evalEvar r)) ts, e.evalSvar⟩

/-- An application to variables, read at two valuations that give its arguments the same values. -/
theorem appList_rename {e e' : Valuation M} :
    ∀ (ts : List (EVar × EVar × P)) {h h' : P}, (∀ a, h.interpret I e a ↔ h'.interpret I e' a) →
    (∀ t ∈ ts, e'.evalEvar t.2.1 = e.evalEvar t.1) →
    ∀ a, (appList h (ts.map fun t => .evar t.1)).interpret I e a ↔
      (appList h' (ts.map fun t => .evar t.2.1)).interpret I e' a
  | [], _, _, hh, _ => hh
  | t :: ts, h, h', hh, hv => by
    simp only [List.map_cons, appList]
    refine appList_rename ts (fun a => interp_app_congr hh (fun b => ?_) a)
      (fun t' ht' => hv t' (List.mem_cons_of_mem _ ht'))
    rw [interp_evar, interp_evar, hv t (List.mem_cons_self ..)]

section
variable (hD : DefOK I)
include hD

/-- A guard of `trAxiom` holds at every element where it holds at one. -/
theorem guardOf_pred (t : VarTable) (k : VarKey) (e : Valuation M) (m m' : M)
    (h : (guardOf t k).interpret I e m) : (guardOf t k).interpret I e m' := by
  cases k with
  | sortVar n => unfold guardOf sortGuard at h ⊢; rw [interp_member hD] at h ⊢; exact h
  | evar n s => unfold guardOf at h ⊢; rw [interp_member hD] at h ⊢; exact h
  | svar n s => unfold guardOf at h ⊢; rw [interp_included hD] at h ⊢; exact h

/-- The guards of a translated axiom. -/
theorem guardsOf_pred (a : Kore.Axiom) : GuardsPred I (guardsOf a) := by
  intro w hw e m m' h
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw
  exact guardOf_pred hD _ k e m m' h

/-- The guard on the sort variable gives a sort. -/
theorem isSort_of_at {ws : List P} {r : EVar} (hr : sortGuard r ∈ ws) {e : Valuation M} {m : M}
    (h : At I ws r e m) : IsSort I (e.evalEvar r) := by
  have := h.1 _ hr
  unfold sortGuard at this
  rwa [interp_member hD, interp_sortsDomain] at this

section
variable [Inhabited M] (hc : I ⊧ᴵ ceilDefItem.pat)
include hc

/-- **An equation axiom read at a valuation**: where its guards hold, at an element of R at which
its premise holds, F and B agree on S. -/
theorem eqnPat_at {ws : List P} {r : EVar} {prem S F B : P} {σ : M}
    (hS : ∀ (e : Valuation M) a, S.interpret I e a ↔ a = σ) (hσ : IsSort I σ) (hr : sortGuard r ∈ ws)
    (h : I ⊧ᴵ eqnPat ws r prem S F B) {e : Valuation M} {m : M} (hat : At I ws r e m)
    (hp : prem.interpret I e m) : ∀ a, Inh I σ a → (F.interpret I e a ↔ B.interpret I e a) := by
  have h1 := h e m
  unfold eqnPat at h1
  rw [interpret_impl] at h1
  have h2 := h1 (interp_conjList hat.1)
  rw [interp_equal hD] at h2
  have hR : ∀ a, (Pattern.evar r : P).interpret I e a ↔ a = e.evalEvar r := fun _ => interp_evar
  have h3 := (h2 m).mpr ((interp_inhOf_of hR).mpr hat.2)
  rw [interp_sImp] at h3
  have h4 := h3.2 hp
  rw [interp_sEquals hD hc (hS e) hR hσ (isSort_of_at hD hr hat)] at h4
  exact h4.2

/-- **An equation axiom from its reading**: it holds where, at every valuation satisfying its
guards and every element of R at which its premise holds, F and B agree on S. -/
theorem eqnPat_of {ws : List P} {r : EVar} {prem S F B : P} {σ : M}
    (hS : ∀ (e : Valuation M) a, S.interpret I e a ↔ a = σ) (hσ : IsSort I σ) (hr : sortGuard r ∈ ws)
    (hG : GuardsPred I ws)
    (h : ∀ (e : Valuation M) (m : M), At I ws r e m → prem.interpret I e m →
      ∀ a, Inh I σ a → (F.interpret I e a ↔ B.interpret I e a)) :
    I ⊧ᴵ eqnPat ws r prem S F B := by
  intro e m
  unfold eqnPat
  rw [interpret_impl]
  intro hws
  have hws' : ∀ w ∈ ws, ∀ m', w.interpret I e m' := fun w hw m' =>
    hG w hw e m m' ((TieUnion.interp_conjListAll.mp hws) w hw)
  rw [interp_equal hD]
  have hR : ∀ a, (Pattern.evar r : P).interpret I e a ↔ a = e.evalEvar r := fun _ => interp_evar
  intro a
  rw [interp_sImp, interp_inhOf_of hR]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hp => ?_⟩
    have hat : At I ws r e a := ⟨fun w hw => hws' w hw a, ha⟩
    rw [interp_sEquals hD hc (hS e) hR hσ (isSort_of_at hD hr hat)]
    exact ⟨ha, h e a hat hp⟩

/-- **The functional sentence makes the application at the equation's arguments one element of
S.** The functional axiom applies the head h to its variables `t.2.1`, the equation to its
variables `t.1` (`ts`); the functional axiom's guards are the sort guard on r' and, for each t,
`t.2.1 ∈ ⟦t.2.2⟧`, the equation's hold `t.1 ∈ ⟦t.2.2⟧` (each sort `t.2.2` closed); the bound v is
none of them. -/
theorem one_of_fnl {ws wsF : List P} {r rF v : EVar} {S h : P} {σ : M} {ts : List (EVar × EVar × P)}
    (hS : ∀ (e : Valuation M) a, S.interpret I e a ↔ a = σ) (hσ : IsSort I σ) (hr : sortGuard r ∈ ws)
    (hfnl : I ⊧ᴵ fnlPat wsF rF v S (appList h (ts.map fun t => .evar t.2.1))) (hh : Closed h)
    (hnd : (ts.map (·.2.1)).Nodup) (hrk : rF ∉ ts.map (·.2.1)) (hvk : v ∉ ts.map (·.2.1)) (hvr : v ≠ rF)
    (hwsF : wsF = sortGuard rF :: ts.map fun t => (t.2.1 ∈∈ inhOf t.2.2))
    (hts : ∀ t ∈ ts, (t.1 ∈∈ inhOf t.2.2) ∈ ws ∧ Closed t.2.2)
    {e : Valuation M} {m : M} (hat : At I ws r e m) :
    ∃ y, Inh I σ y ∧ ∀ a, Inh I σ a →
      ((appList h (ts.map fun t => .evar t.1)).interpret I e a ↔ a = y) := by
  let e' := renameVal e r rF ts
  have hrF : e'.evalEvar rF = e.evalEvar r := by
    show updT e _ ts rF = _
    rw [updT_out e _ ts rF hrk, Function.update_same]
  have hk : ∀ t ∈ ts, e'.evalEvar t.2.1 = e.evalEvar t.1 := updT_in e _ ts hnd
  have hF : ∀ a, (appList h (ts.map fun t => .evar t.2.1)).interpret I e' a ↔
      (appList h (ts.map fun t => .evar t.1)).interpret I e a := fun a =>
    (appList_rename ts (fun b => hh.interp e e' b) hk a).symm
  have hsr : IsSort I (e.evalEvar r) := isSort_of_at hD hr hat
  have hgF : ∀ w ∈ wsF, w.interpret I e' m := by
    intro w hw
    rw [hwsF] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · unfold sortGuard; rw [interp_member hD, interp_sortsDomain, hrF]; exact hsr
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
      rw [interp_member hD, hk t ht]
      have := hat.1 _ (hts t ht).1
      rw [interp_member hD] at this
      exact ((Closed.app (Closed.sym _) (hts t ht).2).interp e e' _).mp this
  have h1 := hfnl e' m
  unfold fnlPat at h1
  rw [interpret_impl] at h1
  have h2 := h1 (interp_conjList hgF)
  rw [interp_equal hD] at h2
  have hR' : ∀ a, (Pattern.evar rF : P).interpret I e' a ↔ a = e.evalEvar r := fun a => by
    rw [interp_evar, hrF]
  have h3 := (h2 m).mpr ((interp_inhOf_of hR').mpr hat.2)
  rw [interp_sExists] at h3
  obtain ⟨y, hy1, hy2⟩ := h3
  let e'' : Valuation M := ⟨Function.update e'.evalEvar v y, e'.evalSvar⟩
  have hR'' : ∀ a, (Pattern.evar rF : P).interpret I e'' a ↔ a = e.evalEvar r := fun a => by
    show a = Function.update e'.evalEvar v y rF ↔ _
    rw [Function.update_noteq (Ne.symm hvr), hrF]
  rw [interp_member hD] at hy1
  have hy : Inh I σ y := by
    rw [interp_inhOf_of (hS e'')] at hy1
    simpa [e''] using hy1
  refine ⟨y, hy, fun a ha => ?_⟩
  rw [interp_sEquals hD hc (hS e'') hR'' hσ hsr] at hy2
  have h4 := (hy2.2 a ha)
  have hFv : (appList h (ts.map fun t => .evar t.2.1)).isFreeEvar v = false := by
    have : ∀ (us : List EVar) (h0 : P), h0.isFreeEvar v = false → v ∉ us →
        (appList h0 (us.map Pattern.evar)).isFreeEvar v = false := by
      intro us
      induction us with
      | nil => intro h0 h0v _; exact h0v
      | cons u us ih =>
        intro h0 h0v hu
        simp only [List.mem_cons, not_or] at hu
        simp only [List.map_cons, appList]
        refine ih _ ?_ hu.2
        simp [Pattern.isFreeEvar, h0v, hu.1]
    have := this (ts.map (·.2.1)) h (hh.1 v) hvk
    simpa [List.map_map, Function.comp_def] using this
  have h5 : (appList h (ts.map fun t => .evar t.2.1)).interpret I e'' a ↔
      (appList h (ts.map fun t => .evar t.2.1)).interpret I e' a :=
    only_free_var_relevant _ _ _ _ (fun x hx => by
      have hxv : x ≠ v := by rintro rfl; rw [hFv] at hx; cases hx
      exact Function.update_noteq hxv _ _) (fun _ _ => rfl) a
  rw [h5, hF] at h4
  rw [← h4]
  show a = Function.update e'.evalEvar v y v ↔ _
  rw [Function.update_same]

/-! ## The sentence and its split -/

/-- What the patterns of the sentence and of its split mean, at every valuation satisfying the
guards and every element of R (`At`). The alternatives `alts` (of any type α) are the patterns
`A x` with the predicates `G x`; the clause of x has the premise `Q x`, the last clause `QN`; the
sentence has the premise `prem` and the right side `rhs`. -/
structure Readings (I : Interpretation Sym M) (ws : List P) (r : EVar) (σ : M) (prem rhs : P)
    {α : Type} (alts : List α) (A : α → P) (G : α → Valuation M → Prop) (Q : α → P) (QN : P) : Prop where
  /-- Each alternative lies in S. -/
  inSort : ∀ e m, At I ws r e m → ∀ x ∈ alts, ∀ a, (A x).interpret I e a → Inh I σ a
  /-- The clause of x applies where the premise holds, x is defined and its predicates hold. -/
  clause : ∀ e m, At I ws r e m → ∀ x ∈ alts,
    ((Q x).interpret I e m ↔ prem.interpret I e m ∧ (∃ b, (A x).interpret I e b) ∧ G x e)
  /-- The last clause applies where the premise holds and no alternative is defined with its
  predicates. -/
  none : ∀ e m, At I ws r e m →
    (QN.interpret I e m ↔ prem.interpret I e m ∧ ∀ x ∈ alts, ¬ ((∃ b, (A x).interpret I e b) ∧ G x e))
  /-- On S, the right side of the sentence holds the alternatives at which their predicates hold. -/
  rhs : ∀ e m, At I ws r e m → ∀ a, Inh I σ a →
    (rhs.interpret I e a ↔ ∃ x ∈ alts, (A x).interpret I e a ∧ G x e)

/-- The last clause's right side `BN` has no element of S wherever no alternative is defined with
its predicates. -/
def NoneEmpty (I : Interpretation Sym M) (ws : List P) (r : EVar) (σ : M) {α : Type} (alts : List α)
    (A : α → P) (G : α → Valuation M → Prop) (BN : P) : Prop :=
  ∀ e m, At I ws r e m → (∀ x ∈ alts, ¬ ((∃ b, (A x).interpret I e b) ∧ G x e)) →
    ∀ a, Inh I σ a → ¬ BN.interpret I e a

omit hD hc [Inhabited M] in
/-- `NoneEmpty` where `BN` lies inside an alternative x₁ of `alts` whose predicates hold wherever
the guards do (an alternative with no predicates): there x₁ is not defined. -/
theorem noneEmpty_of_sub {ws : List P} {r : EVar} {σ : M} {α : Type} {alts : List α} {A : α → P}
    {G : α → Valuation M → Prop} {BN : P} {x₁ : α} (hx₁ : x₁ ∈ alts)
    (hG : ∀ e m, At I ws r e m → G x₁ e) (hB : ∀ e m, At I ws r e m → ∀ a, BN.interpret I e a → (A x₁).interpret I e a) :
    NoneEmpty I ws r σ alts A G BN :=
  fun e m hat hn a _ ha => hn x₁ hx₁ ⟨⟨a, hB e m hat a ha⟩, hG e m hat⟩

omit hD hc [Inhabited M] in
/-- `NoneEmpty` where `BN` has no element of S at all (`a₁ ∧ ⌈false = true⌉` where `false` and
`true` are distinct elements of Bool). -/
theorem noneEmpty_of_empty {ws : List P} {r : EVar} {σ : M} {α : Type} {alts : List α} {A : α → P}
    {G : α → Valuation M → Prop} {BN : P}
    (hB : ∀ e m, At I ws r e m → ∀ a, Inh I σ a → ¬ BN.interpret I e a) :
    NoneEmpty I ws r σ alts A G BN :=
  fun e m hat _ a ha => hB e m hat a ha

/-- The sort `S` is `σ` at every valuation, and `σ` is a sort. -/
structure SortAt (I : Interpretation Sym M) (S : P) (σ : M) : Prop where
  den : ∀ (e : Valuation M) a, S.interpret I e a ↔ a = σ
  isSort : IsSort I σ
  closed : S.isFreeEvar topVar = false

omit hc [Inhabited M] in
/-- `aₖ ∧ ⊤_S` holds on S exactly the elements of aₖ. -/
theorem andTop_on {S A : P} {σ : M} (hS : SortAt I S σ) {e : Valuation M} {a : M} (ha : Inh I σ a) :
    (sAnd A (sTop S)).interpret I e a ↔ A.interpret I e a := by
  rw [interp_sAnd, interp_sTop hD hS.closed, interp_inhOf_of (hS.den e)]
  exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩

/-- **The sentence and the functional sentence give the equation of each alternative**:
`Q x → F = aₓ ∧ ⊤_S`. -/
theorem clause_of_text {ws : List P} {r : EVar} {σ : M} {prem rhs S F : P}
    {α : Type} {alts : List α} {A : α → P} {G : α → Valuation M → Prop} {Q : α → P} {QN : P}
    (hS : SortAt I S σ) (hr : sortGuard r ∈ ws) (hG : GuardsPred I ws)
    (hR : Readings I ws r σ prem rhs alts A G Q QN)
    (hT : I ⊧ᴵ eqnPat ws r prem S F rhs)
    (hone : ∀ e m, At I ws r e m → ∃ y, Inh I σ y ∧ ∀ a, Inh I σ a → (F.interpret I e a ↔ a = y))
    {x : α} (hx : x ∈ alts) : I ⊧ᴵ eqnPat ws r (Q x) S F (sAnd (A x) (sTop S)) := by
  refine eqnPat_of hD hc hS.den hS.isSort hr hG fun e m hat hq a ha => ?_
  obtain ⟨hp, ⟨b, hb⟩, hgx⟩ := (hR.clause e m hat x hx).mp hq
  have hT' := eqnPat_at hD hc hS.den hS.isSort hr hT hat hp
  obtain ⟨y, -, hy⟩ := hone e m hat
  have hbσ := hR.inSort e m hat x hx b hb
  have hFb : F.interpret I e b := (hT' b hbσ).mpr ((hR.rhs e m hat b hbσ).mpr ⟨x, hx, hb, hgx⟩)
  have hby := (hy b hbσ).mp hFb
  rw [andTop_on hD hS ha]
  constructor
  · intro hFa
    rw [(hy a ha).mp hFa, ← hby]; exact hb
  · intro hxa
    exact (hT' a ha).mpr ((hR.rhs e m hat a ha).mpr ⟨x, hx, hxa, hgx⟩)

/-- **The sentence and the functional sentence give the last equation** `QN → F = BN`, whatever
`BN` is: where it applies, the sentence leaves F no element of S and the functional sentence
gives it one. -/
theorem none_of_text {ws : List P} {r : EVar} {σ : M} {prem rhs S F : P}
    {α : Type} {alts : List α} {A : α → P} {G : α → Valuation M → Prop} {Q : α → P} {QN : P}
    (hS : SortAt I S σ) (hr : sortGuard r ∈ ws) (hG : GuardsPred I ws)
    (hR : Readings I ws r σ prem rhs alts A G Q QN)
    (hT : I ⊧ᴵ eqnPat ws r prem S F rhs)
    (hone : ∀ e m, At I ws r e m → ∃ y, Inh I σ y ∧ ∀ a, Inh I σ a → (F.interpret I e a ↔ a = y))
    (BN : P) : I ⊧ᴵ eqnPat ws r QN S F BN := by
  refine eqnPat_of hD hc hS.den hS.isSort hr hG fun e m hat hq a ha => ?_
  obtain ⟨hp, hn⟩ := (hR.none e m hat).mp hq
  have hT' := eqnPat_at hD hc hS.den hS.isSort hr hT hat hp
  obtain ⟨y, hyσ, hy⟩ := hone e m hat
  obtain ⟨x, hx, hxy, hgx⟩ := (hR.rhs e m hat y hyσ).mp ((hT' y hyσ).mp ((hy y hyσ).mpr rfl))
  exact (hn x hx ⟨⟨y, hxy⟩, hgx⟩).elim

/-- **The n+1 equations give the sentence**, with no functional sentence, where the last clause's
right side is empty on S wherever no alternative applies (`NoneEmpty`). -/
theorem text_of_split {ws : List P} {r : EVar} {σ : M} {prem rhs S F BN : P}
    {α : Type} {alts : List α} {A : α → P} {G : α → Valuation M → Prop} {Q : α → P} {QN : P}
    (hS : SortAt I S σ) (hr : sortGuard r ∈ ws) (hG : GuardsPred I ws)
    (hR : Readings I ws r σ prem rhs alts A G Q QN)
    (hk : ∀ x ∈ alts, I ⊧ᴵ eqnPat ws r (Q x) S F (sAnd (A x) (sTop S)))
    (hn : I ⊧ᴵ eqnPat ws r QN S F BN) (hN : NoneEmpty I ws r σ alts A G BN) :
    I ⊧ᴵ eqnPat ws r prem S F rhs := by
  refine eqnPat_of hD hc hS.den hS.isSort hr hG fun e m hat hp a ha => ?_
  rw [hR.rhs e m hat a ha]
  by_cases hsome : ∃ x ∈ alts, (∃ b, (A x).interpret I e b) ∧ G x e
  · obtain ⟨x, hx, hxd, hgx⟩ := hsome
    have hq := (hR.clause e m hat x hx).mpr ⟨hp, hxd, hgx⟩
    have hFx := eqnPat_at hD hc hS.den hS.isSort hr (hk x hx) hat hq
    constructor
    · intro hFa
      exact ⟨x, hx, (andTop_on hD hS ha).mp ((hFx a ha).mp hFa), hgx⟩
    · rintro ⟨x', hx', hx'a, hgx'⟩
      have hq' := (hR.clause e m hat x' hx').mpr ⟨hp, ⟨a, hx'a⟩, hgx'⟩
      have hFx' := eqnPat_at hD hc hS.den hS.isSort hr (hk x' hx') hat hq'
      exact (hFx' a ha).mpr ((andTop_on hD hS ha).mpr hx'a)
  · have hno : ∀ x ∈ alts, ¬ ((∃ b, (A x).interpret I e b) ∧ G x e) :=
      fun x hx hxd => hsome ⟨x, hx, hxd⟩
    have hq := (hR.none e m hat).mpr ⟨hp, hno⟩
    have hFn := eqnPat_at hD hc hS.den hS.isSort hr hn hat hq
    constructor
    · intro hFa
      exact (hN e m hat hno a ha ((hFn a ha).mp hFa)).elim
    · rintro ⟨x, hx, hxa, hgx⟩
      exact (hno x hx ⟨⟨a, hxa⟩, hgx⟩).elim

end

end

end TieFR

end KoreAML
