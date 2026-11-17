/-
  KCore, outside the cone: a rewrite axiom whose left side the text writes in another form than
  Γ's item, in the direction from the text to Γ's item (W1). For a tie file where a reading note
  rewrites a rule's left side (`orSplit`, `topAsVariable`, `existsAsVariable`, `predicateAtBool`,
  `andAtBool`), and for the conjuncts Γ adds to every rule (the negation of the rules of a smaller
  priority, the definedness of the right side).

  - `itemAt t free C L r`: the item of the rewrite axiom `\rewrites{C}(L, r)` under the variable
    table `t` with the guards of the variables `free`. `trAxiom` of the axiom is `itemAt` at the
    axiom's own table and free variables (`trAxiom_rule`). Stating the text's form at Γ's table
    lets the two sides be compared at one valuation where Γ's axiom has a variable more than the
    text's (a variable for `\top`, a variable the text binds).
  - `lhs_entails`: the item of `\rewrites{C}(L, r)` with the guards of `fT` entails the item of
    `\rewrites{C}(L', r)` with the guards of `fG ⊇ fT`, where at every valuation at which the guards
    of `fG` hold every element of `L'` is one of `L`. `rule_w1`: the same from a sentence's
    translation that is the first item up to the indices of its variables (`TiePair.sameB`), to
    `trAxiom` of Γ's axiom.
  - Inclusions for the readings: an application context is monotone (`tr_fill_mono`); a disjunct
    whose elements are in the sort is in the disjunction (`sub_or_left`, `sub_or_right`); a
    variable of the sort S is in `\top{S}` (`sub_top`); `φ` is in `\exists x. φ` (`sub_exists`); a
    value of a sort denotes an element of it (`ground_inh`, from `ΓDomains`).
  - `cfgH`, `step_everyH`, `stuck_everyH`: a step and a stuck configuration the checkers accept on
    the data hold under every interpretation.
-/
import KcoreSpec.TieRhs
import KcoreSpec.TieUnion
import KcoreSpec.CutIdentity

set_option autoImplicit false

namespace KCore

namespace TieRuleLhs

open ML Faithful KoreAML

/-- The item of the rewrite axiom `\rewrites{C}(L, r)` under the table `t`, with the guards of
`free`. -/
def itemAt (t : VarTable) (free : List VarKey) (C : Kore.KSort) (L r : Kore.Pattern) : P :=
  conjList (free.map (guardOf t)) ⇒ (tr ⟨t, []⟩ (.rewrites C L r) ≡ inhOf (trSort t C))

/-- `trAxiom` of a rewrite axiom without sort variables is `itemAt` at its table and its free
variables. -/
theorem trAxiom_rule (C : Kore.KSort) (L r : Kore.Pattern) :
    (trAxiom [] [] ⟨0, "kernel", ⟨[], .rewrites C L r, []⟩⟩).pat =
      itemAt (tableOf [] (.rewrites C L r)) (freeOf [] (.rewrites C L r)).eraseDups C L r := rfl

/-- A rewrite axiom, read as its parts. -/
def rwParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern)
  | .rewrites C L r => some (C, L, r)
  | _ => none

theorem rwParts_eq {p : Kore.Pattern} {C : Kore.KSort} {L r : Kore.Pattern}
    (h : rwParts p = some (C, L, r)) : p = .rewrites C L r := by
  unfold rwParts at h
  split at h
  · cases h; rfl
  · cases h

/-- The application context around the subterm at `path` (the argument indices from the top), and
the subterm. -/
def cutAt : List Nat → Kore.Pattern → Option (KoreCutCtx × Kore.Pattern)
  | [], p => some (.hole, p)
  | i :: is, .app h ss ps =>
    match ps[i]? with
    | some q => (cutAt is q).map fun Kx => (.app h ss (ps.take i) Kx.1 (ps.drop (i + 1)), Kx.2)
    | none => none
  | _ :: _, _ => none

/-- The variable a pattern is. -/
def evarOf : Kore.Pattern → Option Kore.EVar
  | .var (.evar x) => some x
  | _ => none

/-- The first operand of a conjunction. -/
def andHead : Kore.Pattern → Kore.Pattern
  | .and _ (p :: _) => p
  | p => p

/-- The operands of a conjunction after the first. -/
def andTail : Kore.Pattern → List Kore.Pattern
  | .and _ (_ :: ps) => ps
  | _ => []

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A rule axiom entails the one with a smaller left side.** The item of `\rewrites{C}(L, r)`
with the guards of `fT` holds in `I`; at the valuation `e`, where the guards of `fG ⊇ fT` hold,
every element of `L'` is an element of `L`. Then the item of `\rewrites{C}(L', r)` with the guards
of `fG` holds at `e`. -/
theorem lhs_entails (hD : DefOK I) {t : VarTable} {fT fG : List VarKey} {C : Kore.KSort} {L L' r : Kore.Pattern}
    (hsub : ∀ k ∈ fT, k ∈ fG) (h : I ⊧ᴵ itemAt t fT C L r) (e : Valuation M) (m : M)
    (hL : (∀ k ∈ fG, (guardOf t k).interpret I e m) →
      ∀ a, (tr ⟨t, []⟩ L').interpret I e a → (tr ⟨t, []⟩ L).interpret I e a) :
    (itemAt t fG C L' r).interpret I e m := by
  have h1 := h e m
  unfold itemAt at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  have hg' : ∀ k ∈ fG, (guardOf t k).interpret I e m := fun k hk => hg _ (List.mem_map_of_mem hk)
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
    exact hg' k (hsub k hk))
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  have hT : ∀ X, tr ⟨t, []⟩ (.rewrites C X r) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ r) :=
    fun X => by rw [tr]
  rw [hT] at h3 ⊢
  unfold sRewrites at h3 ⊢
  rw [interp_sImp] at h3 ⊢
  exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 (hL hg' a hl)⟩⟩

/-- **W1 for a rule whose left side Γ reads in another form.** `p` is Γ's axiom
`\rewrites{C}(L', r)`; the sentence's translation `tp` is the item of `\rewrites{C}(L, r)` at
`p`'s table with the guards of `fT`, under the renaming `ren` of its free variables' indices; `fT` are free variables
of `p`; and where the guards of `p`'s free variables hold, every element of `L'` is one of `L`.
Then a model of the sentence is a model of Γ's item. -/
theorem rule_w1 (hD : DefOK I) {p : Kore.Pattern} {C : Kore.KSort} {L L' r : Kore.Pattern} {fT : List VarKey}
    {tp : P} {ren : List (Nat × Nat)} (hp : rwParts p = some (C, L', r))
    (hsame : TiePair.renSeq (itemAt (tableOf [] p) fT C L r) ren = some tp)
    (hsub : fT.all (fun k => (freeOf [] p).eraseDups.contains k) = true) (h : I ⊧ᴵ tp)
    (hL : ∀ (e : Valuation M) (m : M),
      (∀ k ∈ (freeOf [] p).eraseDups, (guardOf (tableOf [] p) k).interpret I e m) →
        ∀ a, (tr ⟨tableOf [] p, []⟩ L').interpret I e a → (tr ⟨tableOf [] p, []⟩ L).interpret I e a) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p, []⟩⟩).pat := by
  have hpe := rwParts_eq hp
  intro e m
  have h1 := lhs_entails hD (fT := fT) (fG := (freeOf [] p).eraseDups) (C := C) (L := L) (L' := L') (r := r)
    (fun k hk => List.contains_iff_mem.mp (List.all_eq_true.mp hsub k hk))
    ((TiePair.renSeq_iff hsame).mp h) e m (hL e m)
  have h2 := trAxiom_rule C L' r
  rw [← hpe] at h2
  rw [h2]; exact h1

/-- The guard of an element variable: its value is an element of its sort. -/
theorem guard_evarKey (hD : DefOK I) {t : VarTable} {x : Kore.EVar} {e : Valuation M} {m : M} :
    (guardOf t (evarKey x)).interpret I e m ↔
      (inhOf (trSort t x.sort)).interpret I e (e.evalEvar (t.ev (evarKey x))) := by
  unfold evarKey guardOf; exact interp_member hD

/-- An application context is monotone. -/
theorem fill_mono {φ ψ : P} {e : Valuation M} (h : ∀ a, φ.interpret I e a → ψ.interpret I e a) :
    ∀ (C : CutCtx) (m : M), (C.fill φ).interpret I e m → (C.fill ψ).interpret I e m
  | .hole, m, hm => h m hm
  | .fn C χ, m, hm => by
    obtain ⟨a, b, ha, hb, hab⟩ := interp_app.mp hm
    exact interp_app.mpr ⟨a, b, fill_mono h C a ha, hb, hab⟩
  | .arg χ C, m, hm => by
    obtain ⟨a, b, ha, hb, hab⟩ := interp_app.mp hm
    exact interp_app.mpr ⟨a, b, ha, fill_mono h C b hb, hab⟩

/-- **A KORE application context is monotone under `tr`**, no head on the path to the hole an
alias. -/
theorem tr_fill_mono (ctx : Ctx) (K : KoreCutCtx) (hK : K.noAlias ctx = true) {p q : Kore.Pattern} {e : Valuation M}
    (h : ∀ a, (tr ctx p).interpret I e a → (tr ctx q).interpret I e a) (m : M) :
    (tr ctx (K.fill p)).interpret I e m → (tr ctx (K.fill q)).interpret I e m := by
  rw [tr_cutCtx ctx p K hK, tr_cutCtx ctx q K hK]
  exact fill_mono h _ m

/-- A disjunct whose elements are in the sort is in the disjunction. -/
theorem sub_or_left {t : VarTable} {S : Kore.KSort} {p q : Kore.Pattern} {e : Valuation M}
    (hp : ∀ a, (tr ⟨t, []⟩ p).interpret I e a → (inhOf (trSort t S)).interpret I e a) (a : M) :
    (tr ⟨t, []⟩ p).interpret I e a → (tr ⟨t, []⟩ (.or S [p, q])).interpret I e a := by
  intro h
  simp only [tr, trOrList]
  rw [interp_sOr]
  exact ⟨hp a h, .inl h⟩

theorem sub_or_right {t : VarTable} {S : Kore.KSort} {p q : Kore.Pattern} {e : Valuation M}
    (hq : ∀ a, (tr ⟨t, []⟩ q).interpret I e a → (inhOf (trSort t S)).interpret I e a) (a : M) :
    (tr ⟨t, []⟩ q).interpret I e a → (tr ⟨t, []⟩ (.or S [p, q])).interpret I e a := by
  intro h
  simp only [tr, trOrList]
  rw [interp_sOr]
  exact ⟨hq a h, .inr h⟩

/-- A variable whose value is an element of the sort S is in `\top{S}`. -/
theorem sub_top (hD : DefOK I) {t : VarTable} {x : Kore.EVar} {S : Kore.KSort}
    (hs : (trSort t S).isFreeEvar topVar = false) {e : Valuation M}
    (hg : (inhOf (trSort t S)).interpret I e (e.evalEvar (t.ev (evarKey x)))) (a : M) :
    (tr ⟨t, []⟩ (.var (.evar x))).interpret I e a → (tr ⟨t, []⟩ (.top S)).interpret I e a := by
  intro h
  simp only [tr] at h ⊢
  rw [interp_sTop hD hs]
  rw [interp_evar] at h
  rw [h]; exact hg

/-- `φ` is in `\exists x. φ`, where the value of `x` is an element of its sort. -/
theorem sub_exists (hD : DefOK I) {t : VarTable} {x : Kore.EVar} {R : Kore.KSort} {φ : Kore.Pattern} {e : Valuation M}
    (hg : (inhOf (trSort t x.sort)).interpret I e (e.evalEvar (t.ev (evarKey x)))) (a : M) :
    (tr ⟨t, []⟩ φ).interpret I e a → (tr ⟨t, []⟩ (.exist R x φ)).interpret I e a := by
  intro h
  have he : (⟨Function.update e.evalEvar (t.ev (evarKey x)) (e.evalEvar (t.ev (evarKey x))), e.evalSvar⟩ : Valuation M) = e := by
    cases e with
    | mk ev sv =>
      congr 1
      funext y
      by_cases hy : y = t.ev (evarKey x)
      · subst hy; simp
      · simp [Function.update, hy]
  have hT : tr ⟨t, []⟩ (.exist R x φ) = sExists (t.ev (evarKey x)) (trSort t x.sort) (tr ⟨t, []⟩ φ) := by rw [tr]
  rw [hT, interp_sExists]
  refine ⟨e.evalEvar (t.ev (evarKey x)), ?_, ?_⟩
  · rw [he, interp_member hD]; exact hg
  · rw [he]; exact h

/-- **A value of the sort `s` denotes an element of `s`**, in a model of the domains. -/
theorem ground_inh [Inhabited M] (hD : DefOK I) {c : Semantics} (hDom : I ⊧ᴵP ΓDomains c) {v : GroundTerm} {s : Srt}
    (hv : c.sortOf v = some s) {t : VarTable} {e : Valuation M} (a : M) :
    (tr ⟨t, []⟩ (v.kore c)).interpret I e a → (inhOf (sortP (c.sortName s))).interpret I e a := by
  intro h
  rw [tr_groundKore] at h
  obtain ⟨a0, h1, h2⟩ := TieRhs.den_single_dom hD hDom hv e
  have : a = a0 := (h1 a).mp h
  rw [this]; exact h2

end

/-! ## Steps under every interpretation -/

section EveryH
open KCore.Exec KCore.Cert
variable {c : Semantics}

/-- A configuration of the data is one under every interpretation, where no parameter is an open
generator. -/
def cfgH (hr : ∀ k ∈ c.params, k.raw = false) (x : Config c) (H : HookParams) : Config (c.withHooks H) :=
  ⟨x.val, by rw [Semantics.sortOf_withHooks _ _ hr]; exact x.property⟩

/-- A step some rule's check accepts on the data is a step under every interpretation. -/
theorem step_everyH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) {x y : Config c} {n : Nat}
    (hc : c.rules.any (fun r => checkStep c n r x.val y.val) = true) (H : HookParams) :
    Step (c.withHooks H) (cfgH hr x H) (cfgH hr y H) := by
  obtain ⟨r, hmem, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨_, hstep⟩ := step_of_listed ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    (x := cfgH hr x H)
    (listed_of_checkStep (c := c.withHooks H) (r := r) hmem ((checkStep_withHooks c H hr n r _ _).trans hc))
  exact hstep

/-- A configuration `stuckCheck` accepts on the data has no successor under any interpretation. -/
theorem stuck_everyH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) (hcf : c.clausesFixed = true) (hag : c.agreeObligations = [])
    (hna : c.asideFree = true) {x : Config c} {n : Nat} (h : stuckCheck c n x.val = true) (H : HookParams) :
    ∀ y, ¬ Step (c.withHooks H) (cfgH hr x H) y :=
  stuckCheck_sound hok hsr hmr H
    (Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
      ((Semantics.matchReady_withHooks c H).trans hmr) ((Semantics.clausesFixed_withHooks c H).trans hcf)
      ((Semantics.agreeObligations_withHooks c H).trans hag))
    (x := cfgH hr x H) h hna hr

end EveryH

end TieRuleLhs

end KCore
