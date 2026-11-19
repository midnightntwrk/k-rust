/-
  KCore. The Bools that bound a condition's binders, beside `Cond.bound`.

  `Cond.boundConf c` asks of every binder a sort where the values and the elements agree in every
  interpretation whose confined sorts hold values' elements only: an `ex` or `all` variable of a
  confined sort, a match variable held by its pattern under constructors and injections or of a
  confined sort. The Holds lemmas that read a binder by its sort alone (`BinderFacts`) are stated
  over it. `Cond.boundV c val` admits also an `ex` binder of a sort `val` admits whose body fixes
  the bound variable by a term over the other variables (`Cond.fixes`).
  - `Cond.boundV_false`, `Cond.boundV_of_boundConf`: `Cond.boundConf` is `Cond.boundV` with `val`
    admitting no sort, and every `Cond.boundV` accepts what it accepts;
  - `Cond.bound_eq_boundV`: `Cond.bound` is `Cond.boundV` with `val` the test of a sort with a
    value, `Semantics.valued`;
  - `Cond.bound_of_boundConf`, `Cond.boundV_valued_of_bound`: so `Cond.bound` accepts what
    `Cond.boundConf` accepts, and `Cond.boundV c c.valued` what `Cond.bound` accepts.
-/
import KcoreSpec.FaithOK
import KcoreSpec.RightHeld

set_option autoImplicit false

namespace KCore

/-- The binders of a condition range where values and elements agree by their sorts alone: an
`exMatch` variable is held by its pattern under constructors and injections, or is of a confined
sort; an `ex` or `all` variable is of a confined sort. -/
def Cond.boundConf (c : Semantics) (n : Nat) : Cond → Bool
  | .exMatch ys _ p _ body =>
      (List.range ys.length).all (fun j =>
        (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) &&
      Cond.boundConf c (n + ys.length) body
  | .ex s body | .all s body => c.confined s && Cond.boundConf c (n + 1) body
  | .not p => Cond.boundConf c n p
  | .and p q | .or p q | .implies p q => Cond.boundConf c n p && Cond.boundConf c n q
  | _ => true

/-- `Cond.boundConf` with one more case at an `ex` binder: its sort is confined, or `val` admits it
and the body fixes the bound variable by a term over the other variables (`Cond.fixes`). An `all`
binder and the binders of a match are as in `Cond.boundConf`. `Cond.bound` is it at
`Semantics.valued` (`Cond.bound_eq_boundV`). -/
def Cond.boundV (c : Semantics) (val : Srt → Bool) (n : Nat) : Cond → Bool
  | .exMatch ys _ p _ body =>
      (List.range ys.length).all (fun j =>
        (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) &&
      Cond.boundV c val (n + ys.length) body
  | .ex s body =>
      (c.confined s || (val s && Cond.fixes c.confined val (fun j => j != n) n (n + 1) body)) &&
      Cond.boundV c val (n + 1) body
  | .all s body => c.confined s && Cond.boundV c val (n + 1) body
  | .not p => Cond.boundV c val n p
  | .and p q | .or p q | .implies p q => Cond.boundV c val n p && Cond.boundV c val n q
  | _ => true

/-- `Cond.bound` is `Cond.boundV` where `val` is the test of a sort with a value,
`Semantics.valued`. -/
theorem Cond.bound_eq_boundV (c : Semantics) : Cond.bound c = Cond.boundV c c.valued :=
  funext fun n => funext fun p => go p n
where
  go : ∀ (p : Cond) (n : Nat), Cond.bound c n p = Cond.boundV c c.valued n p
  | .top, _ | .bot, _ | .ceil .., _ | .equals .., _ | .mem .., _ => by simp [Cond.bound, Cond.boundV]
  | .not p, n => by rw [Cond.bound, Cond.boundV, go p n]
  | .and p q, n | .or p q, n | .implies p q, n => by rw [Cond.bound, Cond.boundV, go p n, go q n]
  | .exMatch ys s p t body, n => by rw [Cond.bound, Cond.boundV, go body _]
  | .ex s body, n => by rw [Cond.bound, Cond.boundV, go body _]
  | .all s body, n => by rw [Cond.bound, Cond.boundV, go body _]

/-- A condition `Cond.boundConf` accepts, every `Cond.boundV` accepts. -/
theorem Cond.boundV_of_boundConf (c : Semantics) (val : Srt → Bool) :
    ∀ (p : Cond) (n : Nat), Cond.boundConf c n p = true → Cond.boundV c val n p = true
  | .top, _, _ | .bot, _, _ | .ceil .., _, _ | .equals .., _, _ | .mem .., _, _ => by simp [Cond.boundV]
  | .not p, n, h => by
    rw [Cond.boundConf] at h; rw [Cond.boundV]; exact Cond.boundV_of_boundConf c val p n h
  | .and p q, n, h | .or p q, n, h | .implies p q, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true]
    exact ⟨Cond.boundV_of_boundConf c val p n h.1, Cond.boundV_of_boundConf c val q n h.2⟩
  | .exMatch ys s p t body, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true]
    exact ⟨h.1, Cond.boundV_of_boundConf c val body _ h.2⟩
  | .ex s body, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true, Bool.or_eq_true]
    exact ⟨.inl h.1, Cond.boundV_of_boundConf c val body _ h.2⟩
  | .all s body, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true]
    exact ⟨h.1, Cond.boundV_of_boundConf c val body _ h.2⟩

/-- Where `val` admits no sort, `Cond.boundV` is `Cond.boundConf`. -/
theorem Cond.boundV_false (c : Semantics) :
    ∀ (p : Cond) (n : Nat), Cond.boundV c (fun _ => false) n p = Cond.boundConf c n p
  | .top, _ | .bot, _ | .ceil .., _ | .equals .., _ | .mem .., _ => by simp [Cond.boundV, Cond.boundConf]
  | .not p, n => by rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c p n]
  | .and p q, n | .or p q, n | .implies p q, n => by
    rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c p n, Cond.boundV_false c q n]
  | .exMatch ys s p t body, n => by rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c body _]
  | .ex s body, n => by
    rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c body _]; simp
  | .all s body, n => by rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c body _]

/-- A condition `Cond.boundConf` accepts, `Cond.bound` accepts. -/
theorem Cond.bound_of_boundConf (c : Semantics) (p : Cond) (n : Nat)
    (h : Cond.boundConf c n p = true) : Cond.bound c n p = true := by
  rw [Cond.bound_eq_boundV]; exact Cond.boundV_of_boundConf c c.valued p n h

/-- **A condition `Cond.bound` accepts, `Cond.boundV c c.valued` accepts**: the Bool the Holds
lemma reads in a model of `Γc` (`CE.holds_den_fixed`, with `Semantics.valued_value`) bounds every
condition `Cond.bound` bounds. -/
theorem Cond.boundV_valued_of_bound (c : Semantics) (p : Cond) (n : Nat)
    (h : Cond.bound c n p = true) : Cond.boundV c c.valued n p = true := by
  rw [← Cond.bound_eq_boundV]; exact h

end KCore
