/-
  KCore. Application is strict in every interpretation, so `andThenBool`, `orElseBool` and `ite`
  are strict in every model of `Γ`.

  Applicative matching logic interprets an application `φ ψ` as the pointwise extension of the
  interpretation's application to the sets `φ` and `ψ` denote (`Pattern.interpret`, aml-port
  MatchingLogic/Semantics.lean): `m ∈ φ ψ` iff some `a ∈ φ` and `b ∈ ψ` have `m ∈ a · b`. If either
  set is empty, so is the application (`app_strict_left`, `app_strict_right`). A symbol applied to
  several arguments is a left-nested application (`appList`, the translation's `trArgs`), so it
  denotes the empty set as soon as one argument does (`appList_strict`, `tr_app_strict`). This
  holds in every interpretation, before any axiom is read; in particular in every model of `Γ c`.

  A term of the semantics applying a symbol, `Term.kore` translated as `Γ`'s axioms are, is such an
  application whatever the symbol (`term_app_strict`, `symApp_strict`). So `andThenBool(t₁, t₂)`,
  `orElseBool(t₁, t₂)` and `ite(t₀, t₁, t₂)` denote nothing in a model wherever one of their
  arguments denotes nothing there, the argument a short-circuiting evaluation would skip included
  (`andThen_strict`, `orElse_strict`, `ite_strict`), and with KORE's `\bottom` as an argument they
  denote nothing in every model of `Γ c` (`Γ c ⊧ ¬ andThenBool(⊥, b)` and the like,
  `andThen_bot`, `orElse_bot`, `ite_bot`). No interpretation of these declarations as symbols of
  the signature can short-circuit them.
-/
import KcoreSpec.Sound

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

section
variable {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M}

/-! ## Application in applicative matching logic -/

/-- An application whose argument denotes nothing denotes nothing. -/
theorem app_strict_right {φ ψ : KoreAML.P} (hψ : ∀ b, ¬ ψ.interpret I e b) (m : M) :
    ¬ (φ ⬝ ψ).interpret I e m := by
  rw [interpret_app]
  rintro ⟨_, b, -, hb, -⟩
  exact hψ b hb

/-- An application whose head denotes nothing denotes nothing. -/
theorem app_strict_left {φ ψ : KoreAML.P} (hφ : ∀ a, ¬ φ.interpret I e a) (m : M) :
    ¬ (φ ⬝ ψ).interpret I e m := by
  rw [interpret_app]
  rintro ⟨a, _, ha, -, -⟩
  exact hφ a ha

theorem appList_strict_head {h : KoreAML.P} (hh : ∀ a, ¬ h.interpret I e a) :
    ∀ (args : List KoreAML.P) (m : M), ¬ (KoreAML.appList h args).interpret I e m := by
  intro args
  induction args generalizing h with
  | nil => exact hh
  | cons φ args ih => exact ih (app_strict_left hh)

/-- **A head applied to arguments denotes nothing where one argument denotes nothing.** -/
theorem appList_strict {h φ : KoreAML.P} {args : List KoreAML.P} (hφ : φ ∈ args)
    (hempty : ∀ b, ¬ φ.interpret I e b) (m : M) : ¬ (KoreAML.appList h args).interpret I e m := by
  induction args generalizing h with
  | nil => exact absurd hφ List.not_mem_nil
  | cons ψ args ih =>
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact appList_strict_head (app_strict_right hempty) args m
    · exact ih hφ

/-! ## KORE applications, as `Γ` translates them -/

/-- **A KORE application denotes nothing where one argument denotes nothing**, for every head that
is not an alias. -/
theorem tr_app_strict {ctx : KoreAML.Ctx} {h : Kore.SymbolIdent} {ss : List Kore.KSort} {ps : List Kore.Pattern}
    (hal : ctx.aliases.contains h.ident.name = false) {p : Kore.Pattern} (hp : p ∈ ps)
    (hempty : ∀ b, ¬ (KoreAML.tr ctx p).interpret I e b) (m : M) :
    ¬ (KoreAML.tr ctx (.app h ss ps)).interpret I e m := by
  rw [KoreAML.tr]
  simp only [hal, Bool.false_eq_true, ↓reduceIte]
  rw [trArgs_appList]
  exact appList_strict (List.mem_map_of_mem hp) hempty m

/-- A symbol applied as `Γ` writes it (`symApp`) denotes nothing where one argument does. -/
theorem symApp_strict {c : Semantics} {tbl : KoreAML.VarTable} (f : Sym) {ps : List Kore.Pattern}
    {p : Kore.Pattern} (hp : p ∈ ps) (hempty : ∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ p).interpret I e b) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (symApp c f ps)).interpret I e m := by
  unfold symApp
  split <;> exact tr_app_strict rfl hp hempty m

/-- **A term applying a symbol denotes nothing where one of its arguments denotes nothing**, at
every valuation of every interpretation. -/
theorem term_app_strict {c : Semantics} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} (f : Sym)
    {ts : List Term} {t : Term} (ht : t ∈ ts)
    (hempty : ∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e b) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.app f ts))).interpret I e m := by
  have hp : Term.kore c vs t ∈ Term.koreList c vs ts := by
    rw [Model.koreList_eq_map]; exact List.mem_map_of_mem ht
  have := symApp_strict (c := c) (tbl := tbl) (I := I) (e := e) f hp hempty m
  unfold symApp at this
  rw [Term.kore]
  exact this

/-! ## `andThenBool`, `orElseBool`, `ite` -/

/-- `andThenBool(t₁, t₂)` denotes nothing where `t₁` or `t₂` does, `false andThenBool t₂` with `t₂`
denoting nothing included. -/
theorem andThen_strict {c : Semantics} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {t₁ t₂ : Term}
    (h : (∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t₁)).interpret I e b) ∨
      (∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t₂)).interpret I e b)) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.app boolAndThen [t₁, t₂]))).interpret I e m := by
  rcases h with h | h
  · exact term_app_strict boolAndThen (List.mem_cons_self ..) h m
  · exact term_app_strict boolAndThen (List.mem_cons_of_mem _ (List.mem_singleton_self _)) h m

/-- `orElseBool(t₁, t₂)` denotes nothing where `t₁` or `t₂` does, `true orElseBool t₂` with `t₂`
denoting nothing included. -/
theorem orElse_strict {c : Semantics} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {t₁ t₂ : Term}
    (h : (∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t₁)).interpret I e b) ∨
      (∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t₂)).interpret I e b)) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.app boolOrElse [t₁, t₂]))).interpret I e m := by
  rcases h with h | h
  · exact term_app_strict boolOrElse (List.mem_cons_self ..) h m
  · exact term_app_strict boolOrElse (List.mem_cons_of_mem _ (List.mem_singleton_self _)) h m

/-- `ite(t₀, t₁, t₂)`, for the registry's `ite` and for every symbol named `ite{X}` alike, denotes
nothing where one of `t₀`, `t₁`, `t₂` does, the branch not taken included. -/
theorem ite_strict {c : Semantics} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} (f : Sym) {t₀ t₁ t₂ : Term}
    (h : (∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t₀)).interpret I e b) ∨
      (∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t₁)).interpret I e b) ∨
      (∀ b, ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t₂)).interpret I e b)) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.app f [t₀, t₁, t₂]))).interpret I e m := by
  rcases h with h | h | h
  · exact term_app_strict f (List.mem_cons_self ..) h m
  · exact term_app_strict f (List.mem_cons_of_mem _ (List.mem_cons_self ..)) h m
  · exact term_app_strict f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) h m

/-- KORE's `\bottom` at a sort of the semantics denotes nothing where definedness holds. -/
theorem bottom_empty (hD : KoreAML.DefOK I) {tbl : KoreAML.VarTable} (n : String) (b : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (.bottom (KoreAML.srt n))).interpret I e b := by
  rw [KoreAML.tr]
  unfold KoreAML.sBot
  rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl)]
  exact fun ⟨h1, h2⟩ => h1 h2

end

/-! ## In every model of `Γ` -/

variable {c : Semantics}

/-- **`andThenBool(⊥, p)` and `andThenBool(p, ⊥)` denote nothing in every model of `Γ c`.** -/
theorem andThen_bot (tbl : KoreAML.VarTable) (n : String) (p : Kore.Pattern) :
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c boolAndThen [.bottom (KoreAML.srt n), p]))) ∧
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c boolAndThen [p, .bottom (KoreAML.srt n)]))) :=
  ⟨by intro M _ I hI e m; exact interpret_neg.mpr (symApp_strict _ (List.mem_cons_self ..) (bottom_empty (defOK hI) n) m),
   by intro M _ I hI e m; exact interpret_neg.mpr (symApp_strict _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
     (bottom_empty (defOK hI) n) m)⟩

/-- **`orElseBool(⊥, p)` and `orElseBool(p, ⊥)` denote nothing in every model of `Γ c`.** -/
theorem orElse_bot (tbl : KoreAML.VarTable) (n : String) (p : Kore.Pattern) :
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c boolOrElse [.bottom (KoreAML.srt n), p]))) ∧
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c boolOrElse [p, .bottom (KoreAML.srt n)]))) :=
  ⟨by intro M _ I hI e m; exact interpret_neg.mpr (symApp_strict _ (List.mem_cons_self ..) (bottom_empty (defOK hI) n) m),
   by intro M _ I hI e m; exact interpret_neg.mpr (symApp_strict _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
     (bottom_empty (defOK hI) n) m)⟩

/-- **`ite(⊥, a, b)`, `ite(c, ⊥, b)` and `ite(c, a, ⊥)` denote nothing in every model of `Γ c`**, for
the registry's `ite` and every symbol named `ite{X}` (`f`). -/
theorem ite_bot (tbl : KoreAML.VarTable) (f : Sym) (n : String) (p q : Kore.Pattern) :
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c f [.bottom (KoreAML.srt n), p, q]))) ∧
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c f [p, .bottom (KoreAML.srt n), q]))) ∧
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c f [p, q, .bottom (KoreAML.srt n)]))) :=
  ⟨by intro M _ I hI e m; exact interpret_neg.mpr (symApp_strict _ (List.mem_cons_self ..) (bottom_empty (defOK hI) n) m),
   by intro M _ I hI e m; exact interpret_neg.mpr (symApp_strict _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
     (bottom_empty (defOK hI) n) m),
   by intro M _ I hI e m; exact interpret_neg.mpr (symApp_strict _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
     (List.mem_singleton_self _))) (bottom_empty (defOK hI) n) m)⟩

theorem ite_bot_kIte (tbl : KoreAML.VarTable) (n : String) (p q : Kore.Pattern) :
    (Γ c ⊧ ∼(KoreAML.tr ⟨tbl, []⟩ (symApp c kIte [.bottom (KoreAML.srt n), p, q]))) :=
  (ite_bot tbl kIte n p q).1

end Faithful

end KCore
