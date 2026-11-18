/-
  KCore. A truth value of a condition together with what each term it evaluates is known to
  satisfy (`HoldsReadT`), and an instance of a clause's right side likewise (`InstIsRead`).

  `Holds c n σ p b` is a derivation; a term evaluation inside it is reached by case analysis only.
  A proof by recursion on the evaluations of a function's clauses knows the reading of a term's
  evaluation in an interpretation (`TermAt`) at the evaluations below the one at hand, and loses
  it when the derivation is handed to a lemma that analyses it. `HoldsReadT c T n σ p b` is
  `Holds c n σ p b` with a proof of `T σ t r` beside each evaluation `EvalTerm c σ t r` of the
  derivation, so that a lemma that takes it reads the terms it meets. `HoldsRead c I` is it for
  `T = TermAt c I`; with `T = EvalTerm c` it is `Holds` (`HoldsReadT.of_holds`).

  `InstIsRead c I σ cl r` is `InstIs c σ cl r` with the readings of the terms the instance
  evaluates and `HoldsRead` of its predicate.
-/
import KcoreSpec.HoldsNode

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace HoldsShape

/-- `Holds c n σ p b` with `T σ t r` at each term evaluation `EvalTerm c σ t r` of the
derivation. -/
inductive HoldsReadT (c : Semantics) (T : Subst → Term → Option GroundTerm → Prop) :
    Nat → Subst → Cond → Bool → Prop where
  | top {n σ} : HoldsReadT c T n σ .top true
  | bot {n σ} : HoldsReadT c T n σ .bot false
  | not {n σ p b} (h : HoldsReadT c T n σ p b) : HoldsReadT c T n σ (.not p) (!b)
  | and {n σ p q b b'} (h : HoldsReadT c T n σ p b) (h' : HoldsReadT c T n σ q b') :
      HoldsReadT c T n σ (.and p q) (b && b')
  | or {n σ p q b b'} (h : HoldsReadT c T n σ p b) (h' : HoldsReadT c T n σ q b') :
      HoldsReadT c T n σ (.or p q) (b || b')
  | implies {n σ p q b b'} (h : HoldsReadT c T n σ p b) (h' : HoldsReadT c T n σ q b') :
      HoldsReadT c T n σ (.implies p q) (!b || b')
  | ceil {n σ s t r} (h : EvalTerm c σ t r) (hT : T σ t r) : HoldsReadT c T n σ (.ceil s t) r.isSome
  | equals {n σ s t u r r'} (h : EvalTerm c σ t r) (hT : T σ t r) (h' : EvalTerm c σ u r') (hT' : T σ u r') :
      HoldsReadT c T n σ (.equals s t u) (sameResult r r')
  | mem {n σ s t u r r'} (h : EvalTerm c σ t r) (hT : T σ t r) (h' : EvalTerm c σ u r') (hT' : T σ u r') :
      HoldsReadT c T n σ (.mem s t u) (r.isSome && sameResult r r')
  | exNone {n σ ys s p t body} (h : EvalTerm c σ t none) (hT : T σ t none) :
      HoldsReadT c T n σ (.exMatch ys s p t body) false
  | exSome {n σ ys s p t body v b} (g : Subst → Bool) (h : EvalTerm c σ t (some v)) (hT : T σ t (some v))
      (hb : ∀ σ', Extends c n ys σ σ' → PatVal c σ' p v → HoldsReadT c T (n + ys.length) σ' body (g σ'))
      (hr : b = true ↔ ∃ σ', Extends c n ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true) :
      HoldsReadT c T n σ (.exMatch ys s p t body) b
  | ex {n σ s body b} (g : Subst → Bool)
      (hb : ∀ σ', Extends c n [s] σ σ' → HoldsReadT c T (n + 1) σ' body (g σ'))
      (hr : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) : HoldsReadT c T n σ (.ex s body) b
  | all {n σ s body b} (g : Subst → Bool)
      (hb : ∀ σ', Extends c n [s] σ σ' → HoldsReadT c T (n + 1) σ' body (g σ'))
      (hr : b = true ↔ ∀ σ', Extends c n [s] σ σ' → g σ' = true) : HoldsReadT c T n σ (.all s body) b

section
variable {c : Semantics} {T T' : Subst → Term → Option GroundTerm → Prop}

/-- The derivation of `Holds` it carries. -/
theorem HoldsReadT.holds {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (h : HoldsReadT c T n σ p b) :
    Holds c n σ p b := by
  induction h with
  | top => exact .top
  | bot => exact .bot
  | not _ ih => exact .not ih
  | and _ _ ih ih' => exact .and ih ih'
  | or _ _ ih ih' => exact .or ih ih'
  | implies _ _ ih ih' => exact .implies ih ih'
  | ceil h _ => exact .ceil h
  | equals h _ h' _ => exact .equals h h'
  | mem h _ h' _ => exact .mem h h'
  | exNone h _ => exact .exNone h
  | exSome g h _ _ hr ih => exact .exSome g h ih hr
  | ex g _ hr ih => exact .ex g ih hr
  | all g _ hr ih => exact .all g ih hr

/-- What holds of each term evaluation may be weakened. -/
theorem HoldsReadT.mono (hT : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, T σ t r → T' σ t r)
    {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (h : HoldsReadT c T n σ p b) : HoldsReadT c T' n σ p b := by
  induction h with
  | top => exact .top
  | bot => exact .bot
  | not _ ih => exact .not ih
  | and _ _ ih ih' => exact .and ih ih'
  | or _ _ ih ih' => exact .or ih ih'
  | implies _ _ ih ih' => exact .implies ih ih'
  | ceil h h1 => exact .ceil h (hT h1)
  | equals h h1 h' h2 => exact .equals h (hT h1) h' (hT h2)
  | mem h h1 h' h2 => exact .mem h (hT h1) h' (hT h2)
  | exNone h h1 => exact .exNone h (hT h1)
  | exSome g h h1 _ hr ih => exact .exSome g h (hT h1) ih hr
  | ex g _ hr ih => exact .ex g ih hr
  | all g _ hr ih => exact .all g ih hr

/-- **A truth value `Holds` gives, with what holds of every term evaluation.** -/
theorem HoldsReadT.of_holds (hT : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r → T σ t r) :
    ∀ (p : Cond) {n : Nat} {σ : Subst} {b : Bool}, Holds c n σ p b → HoldsReadT c T n σ p b
  | .top, _, _, _, h => by cases h; exact .top
  | .bot, _, _, _, h => by cases h; exact .bot
  | .not p, _, _, _, h => by
    cases h with
    | not h => exact .not (HoldsReadT.of_holds hT p h)
  | .and p q, _, _, _, h => by
    cases h with
    | and h h' => exact .and (HoldsReadT.of_holds hT p h) (HoldsReadT.of_holds hT q h')
  | .or p q, _, _, _, h => by
    cases h with
    | or h h' => exact .or (HoldsReadT.of_holds hT p h) (HoldsReadT.of_holds hT q h')
  | .implies p q, _, _, _, h => by
    cases h with
    | implies h h' => exact .implies (HoldsReadT.of_holds hT p h) (HoldsReadT.of_holds hT q h')
  | .ceil _ _, _, _, _, h => by
    cases h with
    | ceil h => exact .ceil h (hT h)
  | .equals _ _ _, _, _, _, h => by
    cases h with
    | equals h h' => exact .equals h (hT h) h' (hT h')
  | .mem _ _ _, _, _, _, h => by
    cases h with
    | mem h h' => exact .mem h (hT h) h' (hT h')
  | .exMatch _ _ _ _ body, _, _, _, h => by
    cases h with
    | exNone h => exact .exNone h (hT h)
    | exSome g h hb hr => exact .exSome g h (hT h) (fun σ' hx hpv => HoldsReadT.of_holds hT body (hb σ' hx hpv)) hr
  | .ex _ body, _, _, _, h => by
    cases h with
    | ex g hb hr => exact .ex g (fun σ' hx => HoldsReadT.of_holds hT body (hb σ' hx)) hr
  | .all _ body, _, _, _, h => by
    cases h with
    | all g hb hr => exact .all g (fun σ' hx => HoldsReadT.of_holds hT body (hb σ' hx)) hr

end

/-- `Holds c n σ p b` with the reading in I of each term the derivation evaluates. -/
abbrev HoldsRead (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) :
    Nat → Subst → Cond → Bool → Prop :=
  HoldsReadT c (TermAt c I)

/-- `InstFails c σ cl` with the readings in I of the terms the instance evaluates. -/
inductive InstFailsRead (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Subst → Clause → Prop where
  | ens {σ : Subst} {cl : Clause} {t : Term} {w : Option GroundTerm}
      (ht : cl.ens = some t) (he : EvalTerm c σ t w) (hT : TermAt c I σ t w) (hw : w ≠ some (bool true)) :
      InstFailsRead c I σ cl
  | post {σ : Subst} {cl : Clause} (h : HoldsRead c I cl.vars.length σ cl.post false) : InstFailsRead c I σ cl
  | rhs {σ : Subst} {cl : Clause} (h : EvalTerm c σ cl.rhs none) (hT : TermAt c I σ cl.rhs none) :
      InstFailsRead c I σ cl

/-- `InstIs c σ cl r` with the readings in I of the terms the instance evaluates. -/
inductive InstIsRead (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) :
    Subst → Clause → Option GroundTerm → Prop where
  | fails {σ : Subst} {cl : Clause} {r : Option GroundTerm} {b : Bool}
      (hp : HoldsRead c I cl.vars.length σ cl.post b) (h : InstFailsRead c I σ cl) : InstIsRead c I σ cl r
  | gives {σ : Subst} {cl : Clause} {v : GroundTerm} (hrhs : EvalTerm c σ cl.rhs (some v))
      (hrhsT : TermAt c I σ cl.rhs (some v))
      (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) ∧ TermAt c I σ t (some (bool true)))
      (hpost : HoldsRead c I cl.vars.length σ cl.post true) : InstIsRead c I σ cl (some v)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- The instance's failure it carries. -/
theorem InstFailsRead.instFails {σ : Subst} {cl : Clause} (h : InstFailsRead c I σ cl) : InstFails c σ cl := by
  cases h with
  | ens ht he _ hw => exact .ens ht he hw
  | post h => exact .post h.holds
  | rhs h _ => exact .rhs h

omit [Inhabited M] in
/-- The decided instance it carries. -/
theorem InstIsRead.instIs {σ : Subst} {cl : Clause} {r : Option GroundTerm} (h : InstIsRead c I σ cl r) :
    InstIs c σ cl r := by
  cases h with
  | fails hp h => exact .fails hp.holds h.instFails
  | gives hrhs _ hens hpost => exact .gives hrhs (fun t ht => (hens t ht).1) hpost.holds

omit [Inhabited M] in
/-- The truth value of the instance's predicate, read. -/
theorem InstIsRead.post {σ : Subst} {cl : Clause} {r : Option GroundTerm} (h : InstIsRead c I σ cl r) :
    ∃ b, HoldsRead c I cl.vars.length σ cl.post b := by
  cases h with
  | fails hp _ => exact ⟨_, hp⟩
  | gives _ _ _ hpost => exact ⟨true, hpost⟩

/-- With the atoms' facts, a decided instance comes with the readings of its terms. -/
theorem InstIsRead.of_instIs (F : AtomFacts c I) {σ : Subst} {cl : Clause} {r : Option GroundTerm}
    (h : InstIs c σ cl r) : InstIsRead c I σ cl r := by
  cases h with
  | fails hp hf =>
    refine .fails (HoldsReadT.of_holds F.termAt _ hp) ?_
    cases hf with
    | ens ht he hw => exact .ens ht he (F.termAt he) hw
    | post h => exact .post (HoldsReadT.of_holds F.termAt _ h)
    | rhs h => exact .rhs h (F.termAt h)
  | gives hrhs hens hpost =>
    exact .gives hrhs (F.termAt hrhs) (fun t ht => ⟨hens t ht, F.termAt (hens t ht)⟩)
      (HoldsReadT.of_holds F.termAt _ hpost)

/-- **A truth value with its terms' readings is read in I** (`HoldsAt`): each constructor by its
lemma. Asked of I: the constructors' facts, and the binders' where the condition holds a binder. -/
theorem HoldsReadT.holdsAt (F : NodeFacts c I) {n : Nat} {σ : Subst} {p : Cond} {b : Bool}
    (h : HoldsRead c I n σ p b) (G : hasBinder p = true → BinderFacts c I) : HoldsAt c I n σ p b := by
  induction h with
  | top => exact holdsAt_top F
  | bot => exact holdsAt_bot F
  | not _ ih => exact holdsAt_not (ih G)
  | and _ _ ih ih' =>
    exact holdsAt_and (ih fun hp => G (by rw [hasBinder, hp, Bool.true_or]))
      (ih' fun hq => G (by rw [hasBinder, hq, Bool.or_true]))
  | or _ _ ih ih' =>
    exact holdsAt_or (ih fun hp => G (by rw [hasBinder, hp, Bool.true_or]))
      (ih' fun hq => G (by rw [hasBinder, hq, Bool.or_true]))
  | implies _ _ ih ih' =>
    exact holdsAt_implies (ih fun hp => G (by rw [hasBinder, hp, Bool.true_or]))
      (ih' fun hq => G (by rw [hasBinder, hq, Bool.or_true]))
  | ceil h hT => exact holdsAt_ceil F h hT
  | equals h hT h' hT' => exact holdsAt_equals F h hT h' hT'
  | mem h hT h' hT' => exact holdsAt_mem F h hT h' hT'
  | exNone h hT => exact holdsAt_exMatch F (G rfl) h hT (Or.inl ⟨rfl, rfl⟩)
  | exSome g h hT _ hr ih =>
    exact holdsAt_exMatch F (G rfl) h hT (Or.inr ⟨_, g, rfl, fun σ' hx hpv => ih σ' hx hpv fun _ => G rfl, hr⟩)
  | ex g _ hr ih => exact holdsAt_ex F (G rfl) g (fun σ' hx => ih σ' hx fun _ => G rfl) hr
  | all g _ hr ih => exact holdsAt_all F (G rfl) g (fun σ' hx => ih σ' hx fun _ => G rfl) hr

end

end HoldsShape

end KCore
