import KPrelude.Invariant
import KClaims.Reach

/-!
# Claims under a preserved invariant

A preserved invariant `P` should be usable inside a claim proof, so that a circularity need not
re-establish `P` at every loop head. The direct statements are two lemmas over the restriction
`R_P d e := P d ∧ R d e` (`restrict R P` below):

- all-path, `AF.of_restrict`: `Preserved R P → P c → AF R_P Q c → AF R Q c`;
- one-path, `EF.of_restrict`: `EF R_P Q c → EF R Q c`, for any `P`.

Both hold, and with `P c` and `Preserved R P` both are equivalences (`AF_restrict_iff`,
`EF_restrict_iff`), so proving a claim over `R_P` loses nothing.

They do not by themselves put `P` in context at every state of a claim proof.
Unfolding `AF R_P Q d` asks for `Q d`, or for a successor `∃ e, P d ∧ R d e` together with
`∀ e, P d ∧ R d e → AF R_P Q e`: `P d` is a hypothesis only when inverting a step from `d`, and it
is an obligation when exhibiting one.
Nothing records `P e` for the successor either, so at the next state the obligation `P e`
reappears.
The executable-step lemmas of `KClaims.Exec` (`AF.next`) need `ExecDet R_P step`, whose
soundness half `step c = .next c' → P c ∧ R c c'` is false for a `c` outside `P`, so the
claim tactic (`KClaims.Tactic`) cannot run over `R_P` as it is.

The forms below do give `P d` at every state `d`, at no cost:

- `AF.coind_inv`, `EF.coind_inv`: the coinduction principles with `P d` as a hypothesis of the
  obligation at every `d` (the candidate set is intersected with `P`, which `Preserved`
  closes under steps);
- `AF.step_inv`, `AFn.step_inv`, `EF.step_inv`: one step with `P e` given at each successor
  `e`; these are what a symbolic-execution tactic applies at each step to carry `P` forward;
- `AF.circularity_inv`: guarded circularities whose preconditions include `P`, so a circularity
  is used at a state where `P` is in context (from `AFn.step_inv`);
- `AF_typed_iff`, `EF_typed_iff`: claims over the typed view `TStep R P` on `{c // P c}`, where
  every state carries its proof of `P`.

A claim tactic that wants `P` in context should therefore use `AF.step_inv` (or the typed view)
rather than `R_P`; `AF.of_restrict` is the statement to cite when a claim is proved over a
restricted relation by other means.
-/

namespace KClaims

open KPrelude

section

variable {α : Type} (R : α → α → Prop) (P : α → Prop)

/-- The steps of `R` from configurations satisfying `P`. -/
def restrict (d e : α) : Prop := P d ∧ R d e

end

variable {α : Type} {R : α → α → Prop} {P Q : α → Prop} {c : α}

/-! ## The restricted relation -/

/-- All-path claims over the restricted relation hold over `R` (needs `Preserved`: without it
the restriction drops successors the all-path claim must cover). -/
theorem AF.of_restrict (hP : Preserved R P) (hc : P c) (h : AF (restrict R P) Q c) : AF R Q c := by
  refine AF.coind (fun d => P d ∧ AF (restrict R P) Q d) ?_ ⟨hc, h⟩
  rintro d ⟨hd, hd'⟩
  rcases AF.unfold.1 hd' with hq | ⟨⟨e, _, he⟩, hall⟩
  · exact Or.inl hq
  · exact Or.inr ⟨⟨e, he⟩, fun e' he' => ⟨hP d e' hd he', hall e' ⟨hd, he'⟩⟩⟩

theorem AF.restrict_of (hP : Preserved R P) (hc : P c) (h : AF R Q c) : AF (restrict R P) Q c := by
  refine AF.coind (fun d => P d ∧ AF R Q d) ?_ ⟨hc, h⟩
  rintro d ⟨hd, hd'⟩
  rcases AF.unfold.1 hd' with hq | ⟨⟨e, he⟩, hall⟩
  · exact Or.inl hq
  · exact Or.inr ⟨⟨e, hd, he⟩, fun e' ⟨_, he'⟩ => ⟨hP d e' hd he', hall e' he'⟩⟩

theorem AF_restrict_iff (hP : Preserved R P) (hc : P c) : AF (restrict R P) Q c ↔ AF R Q c :=
  ⟨AF.of_restrict hP hc, AF.restrict_of hP hc⟩

/-- One-path claims over the restricted relation hold over `R`, for any `P` (`R_P ⊆ R`). -/
theorem EF.of_restrict (h : EF (restrict R P) Q c) : EF R Q c := by
  refine EF.coind (EF (restrict R P) Q) (fun d hd => ?_) h
  rcases EF.unfold.1 hd with hq | ⟨e, ⟨_, he⟩, hef⟩
  · exact Or.inl hq
  · exact Or.inr ⟨e, he, hef⟩

theorem EF.restrict_of (hP : Preserved R P) (hc : P c) (h : EF R Q c) : EF (restrict R P) Q c := by
  refine EF.coind (fun d => P d ∧ EF R Q d) ?_ ⟨hc, h⟩
  rintro d ⟨hd, hd'⟩
  rcases EF.unfold.1 hd' with hq | ⟨e, he, hef⟩
  · exact Or.inl hq
  · exact Or.inr ⟨e, ⟨hd, he⟩, hP d e hd he, hef⟩

theorem EF_restrict_iff (hP : Preserved R P) (hc : P c) : EF (restrict R P) Q c ↔ EF R Q c :=
  ⟨EF.of_restrict, EF.restrict_of hP hc⟩

/-! ## `P` in context at every state -/

/-- Coinduction for `AF` with `P d` available at every state `d`. -/
theorem AF.coind_inv (hP : Preserved R P) (X : α → Prop)
    (hX : ∀ d, P d → X d → Q d ∨ ((∃ e, R d e) ∧ ∀ e, R d e → X e)) (hc : P c) (h : X c) :
    AF R Q c := by
  refine AF.coind (fun d => P d ∧ X d) ?_ ⟨hc, h⟩
  rintro d ⟨hd, hx⟩
  rcases hX d hd hx with hq | ⟨hs, hall⟩
  · exact Or.inl hq
  · exact Or.inr ⟨hs, fun e he => ⟨hP d e hd he, hall e he⟩⟩

/-- Coinduction for `EF` with `P d` available at every state `d`. -/
theorem EF.coind_inv (hP : Preserved R P) (X : α → Prop)
    (hX : ∀ d, P d → X d → Q d ∨ ∃ e, R d e ∧ X e) (hc : P c) (h : X c) : EF R Q c := by
  refine EF.coind (fun d => P d ∧ X d) ?_ ⟨hc, h⟩
  rintro d ⟨hd, hx⟩
  rcases hX d hd hx with hq | ⟨e, he, hxe⟩
  · exact Or.inl hq
  · exact Or.inr ⟨e, he, hP d e hd he, hxe⟩

/-- One all-path step, with `P` given at each successor. -/
theorem AF.step_inv (hP : Preserved R P) (hc : P c) (hs : ∃ e, R c e)
    (hall : ∀ e, R c e → P e → AF R Q e) : AF R Q c :=
  AF.step hs fun e he => hall e he (hP c e hc he)

theorem AFn.step_inv {n : Nat} (hP : Preserved R P) (hc : P c) (hs : ∃ e, R c e)
    (hall : ∀ e, R c e → P e → AFn R Q n e) : AFn R Q (n + 1) c :=
  AFn.step hs fun e he => hall e he (hP c e hc he)

/-- One one-path step, with `P` given at the successor. -/
theorem EF.step_inv {e : α} (hP : Preserved R P) (hc : P c) (he : R c e) (h : P e → EF R Q e) :
    EF R Q c :=
  EF.step he (h (hP c e hc he))

/-- Guarded circularities whose preconditions include the invariant: each claim may assume
`P` at its start state, and so may each use of a circularity. With `AFn.step_inv`, `P` is
available at the state where a circularity is applied. -/
theorem AF.circularity_inv {ι : Type} (Pre Post : ι → α → Prop)
    (h : ∀ n, (∀ m < n, ∀ i d, P d → Pre i d → AFn R (Post i) m d) →
      ∀ i d, P d → Pre i d → AFn R (Post i) n d) :
    ∀ i d, P d → Pre i d → AF R (Post i) d := by
  intro i d hd hpre
  exact AF.circularity (fun i d => P d ∧ Pre i d) Post
    (fun n ih i d ⟨hd, hpre⟩ => h n (fun m hm i d hd hpre => ih m hm i d ⟨hd, hpre⟩) i d hd hpre)
    i d ⟨hd, hpre⟩

/-! ## The typed view -/

/-- An all-path claim over the typed view (every state carries its proof of `P`) is the same
claim over `R`. -/
theorem AF_typed_iff (hP : Preserved R P) (t : TConfig P) :
    AF (TStep R P) (fun t => Q t.1) t ↔ AF R Q t.1 := by
  constructor
  · intro h
    refine AF.coind (fun d => ∃ t : TConfig P, t.1 = d ∧ AF (TStep R P) (fun t => Q t.1) t) ?_
      ⟨t, rfl, h⟩
    rintro d ⟨t, rfl, ht⟩
    rcases AF.unfold.1 ht with hq | ⟨⟨t', ht'⟩, hall⟩
    · exact Or.inl hq
    · exact Or.inr ⟨⟨t'.1, ht'⟩, fun e he => ⟨⟨e, hP _ _ t.2 he⟩, rfl, hall _ he⟩⟩
  · intro h
    refine AF.coind (fun t : TConfig P => AF R Q t.1) ?_ h
    intro t ht
    rcases AF.unfold.1 ht with hq | ⟨⟨e, he⟩, hall⟩
    · exact Or.inl hq
    · exact Or.inr ⟨⟨⟨e, hP _ _ t.2 he⟩, he⟩, fun t' ht' => hall t'.1 ht'⟩

/-- A one-path claim over the typed view is the same claim over `R`. -/
theorem EF_typed_iff (hP : Preserved R P) (t : TConfig P) :
    EF (TStep R P) (fun t => Q t.1) t ↔ EF R Q t.1 := by
  constructor
  · intro h
    refine EF.coind (fun d => ∃ t : TConfig P, t.1 = d ∧ EF (TStep R P) (fun t => Q t.1) t) ?_
      ⟨t, rfl, h⟩
    rintro d ⟨t, rfl, ht⟩
    rcases EF.unfold.1 ht with hq | ⟨t', ht', hef⟩
    · exact Or.inl hq
    · exact Or.inr ⟨t'.1, ht', t', rfl, hef⟩
  · intro h
    refine EF.coind (fun t : TConfig P => EF R Q t.1) ?_ h
    intro t ht
    rcases EF.unfold.1 ht with hq | ⟨e, he, hef⟩
    · exact Or.inl hq
    · exact Or.inr ⟨⟨e, hP _ _ t.2 he⟩, he, hef⟩

end KClaims
