/-
  A right side with an `\exists` under applications holds the elements of the right side with
  that `\exists` at its top, decided on the text (`hoistB`), and an equation sentence with the one
  right side holds in the models where the sentence with the other does (`eqnPat_hoistB`).

  `KoreAML.tr_app_exists` is the equality `K[∃x. φ] = ∃x. K[φ]` for an application context K whose
  side patterns do not read x in the interpretation. Here the context is found on the pattern
  (`exCtx?`: the path of applications to the first `\exists`), and that no side pattern reads x is
  decided on the translations: x is not free in them (`sidesFreeB`, `noRead_of_notFree`).

  - `hoistB ctx p p'`: p's translation is that of `K[∃x. φ]` for the context `exCtx?` finds, no
    head on the path is an alias, x is free in no side pattern, and p' translates as `∃x. K[φ]`.
    The pattern p' is given: the reader's (`Parse.hoistExists`) where it does not rename the binder.
  - `tr_hoistB`: p and p' then hold the same elements at every valuation, in every interpretation
    where definedness is definedness.
  - `eqnPat_congr`, `eqnPat_hoistB`: the sentence `prem → F = B` reads its right side only by its
    elements, so the sentences with `tr p ∧ ens` and with `tr p' ∧ ens` hold in the same models.
-/
import KcoreSpec.ExistsHoist
import KcoreSpec.TieFR

set_option autoImplicit false

namespace KCore

namespace TieExHoistB

open ML KoreAML KoreAML.TieFR

mutual
  /-- The path of applications to the first `\exists` of a pattern (arguments left to right, an
  argument's own before the next argument), with the binder's sort and variable and its body. -/
  def exCtx? : Kore.Pattern → Option (KoreCutCtx × Kore.KSort × Kore.EVar × Kore.Pattern)
    | .exist r x φ => some (.hole, r, x, φ)
    | .app h ss ps => match exCtxList? ps with
      | some (pre, K, r, x, φ, post) => some (.app h ss pre K post, r, x, φ)
      | none => none
    | _ => none
    termination_by structural p => p
  def exCtxList? : List Kore.Pattern →
      Option (List Kore.Pattern × KoreCutCtx × Kore.KSort × Kore.EVar × Kore.Pattern × List Kore.Pattern)
    | [] => none
    | p :: ps => match exCtx? p with
      | some (K, r, x, φ) => some ([], K, r, x, φ, ps)
      | none => match exCtxList? ps with
        | some (pre, rest) => some (p :: pre, rest)
        | none => none
    termination_by structural ps => ps
end

/-- x is free in no side pattern of the context's translation: at each layer the head with the
arguments before the hole, and each argument after it. -/
def sidesFreeB (ctx : Ctx) (x : EVar) : KoreCutCtx → Bool
  | .hole => true
  | .app h ss pre C post =>
    !(trArgs ctx (trSortApp ctx.vars (sym (.symbol h.ident.name)) ss) pre).isFreeEvar x &&
      post.all (fun q => !(tr ctx q).isFreeEvar x) && sidesFreeB ctx x C

/-- p translates as `K[∃x. φ]`, K the path to its first `\exists`, no head of K an alias and x free
in no side pattern of K; and p' translates as `∃x. K[φ]`. -/
def hoistB (ctx : Ctx) (p p' : Kore.Pattern) : Bool :=
  match exCtx? p with
  | some (K, r, x, φ) =>
    K.noAlias ctx && sidesFreeB ctx (ctx.vars.ev (evarKey x)) K &&
      decide (tr ctx (K.fill (.exist r x φ)) = tr ctx p) &&
      decide (tr ctx (.exist r x (K.fill φ)) = tr ctx p')
  | none => false

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A pattern in which x is not free does not read x. -/
theorem noRead_of_notFree {x : EVar} {ψ : P} (h : ψ.isFreeEvar x = false) : NoReadCut I x ψ :=
  fun e a m => only_free_var_relevant _ _ _ _ (fun y hy => by
    have hyx : y ≠ x := by rintro rfl; rw [h] at hy; cases hy
    exact Function.update_noteq hyx _ _) (fun _ _ => rfl) m

theorem sidesNoRead_of_freeB {ctx : Ctx} {x : EVar} : ∀ (K : KoreCutCtx), sidesFreeB ctx x K = true →
    K.SidesNoRead I ctx x
  | .hole, _ => trivial
  | .app _ _ _ C _, h => by
    simp only [sidesFreeB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact ⟨noRead_of_notFree h.1.1, fun q hq => noRead_of_notFree (h.1.2 q hq), sidesNoRead_of_freeB C h.2⟩

/-- **The right side with its `\exists` at the top holds the same elements** (`hoistB`). -/
theorem tr_hoistB (hD : DefOK I) {ctx : Ctx} {p p' : Kore.Pattern} (h : hoistB ctx p p' = true)
    (e : Valuation M) (m : M) : (tr ctx p).interpret I e m ↔ (tr ctx p').interpret I e m := by
  unfold hoistB at h
  split at h
  · rename_i K r x φ _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hK, hx⟩, hp⟩, hp'⟩ := h
    rw [← hp, ← hp']
    exact tr_app_exists hD ctx r r x φ K hK (sidesNoRead_of_freeB K hx) e m
  · cases h

/-- **An equation sentence reads its right side by its elements**: two right sides that hold the
same elements at every valuation give sentences that hold in the same models. -/
theorem eqnPat_congr {ws : List P} {r : EVar} {prem S F B B' : P}
    (h : ∀ (e : Valuation M) m, B.interpret I e m ↔ B'.interpret I e m) :
    (I ⊧ᴵ eqnPat ws r prem S F B) ↔ (I ⊧ᴵ eqnPat ws r prem S F B') := by
  have hf : ∀ e, B.interpret I e = B'.interpret I e := fun e => funext fun m => propext (h e m)
  have key : ∀ e, (eqnPat ws r prem S F B).interpret I e = (eqnPat ws r prem S F B').interpret I e := by
    intro e
    simp only [eqnPat, sImp, sOr, sNot, sAnd, sEquals, sFloor, sCeil, sIff, equal, total,
      Pattern.conjunction, Pattern.negation, Pattern.equivalence, Pattern.disjunction, Pattern.interpret]
    rw [hf e]
  exact ⟨fun H e m => by rw [← key]; exact H e m, fun H e m => by rw [key]; exact H e m⟩

/-- **The sentence with the `\exists` under applications holds where the sentence with it at the
top of the right side does** (`hoistB`), whatever its `ensures` part. -/
theorem eqnPat_hoistB (hD : DefOK I) {ctx : Ctx} {p p' : Kore.Pattern} (h : hoistB ctx p p' = true)
    {ws : List P} {r : EVar} {prem S F ens : P} :
    (I ⊧ᴵ eqnPat ws r prem S F (sAnd (tr ctx p) ens)) ↔ (I ⊧ᴵ eqnPat ws r prem S F (sAnd (tr ctx p') ens)) :=
  eqnPat_congr fun e m => by rw [interp_sAnd, interp_sAnd, tr_hoistB hD h e m]

end

end TieExHoistB

end KCore
