/-
  The rewrite rules of kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`, sentences 408 to 417), in the
  direction from Γ to the text (W2), on the literals `kore` and `defn`. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKkW2.lean`.

  - `w2_checked`: for each rule, Γ's axiom (`prioRuleK`) is a rewrite at the configuration sort
    whose left side is the text's two conjuncts, the second `\top`, with a third more, the
    definedness of its right side; that right side is `\and{C}(term, \top{C}())`; its translation
    in Γ's table is the translation of the sentence's right side in the sentence's own table; and
    without the third conjunct Γ's axiom is the sentence (`TieKkRules.rules_checked`, repeated
    here as `ruleOKB`). One kernel decision.
  - `rules_w2_all`: in a model of Γ, for every H, each of the 10 sentences holds at each valuation
    at which its right side holds an element: there the third conjunct holds of every
    configuration, and Γ's axiom gives the sentence (`tieRule_more`).
  - `rules_w2`: the same at the valuations that send the sentence's variables to values
    (`AtValues`, with that guard; no rule has one of a smaller priority, so the guard has no second
    part).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

/-- A rule axiom `\rewrites{C}(\and{C}(l, t, x), r)`, read as its parts. -/
def ruleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, x]) r => some (C, l, t, x, r)
  | _ => none

/-- The rule axiom without its left side's third conjunct. -/
def dropThird (p : Kore.Pattern) : Kore.Pattern :=
  match ruleParts p with
  | some (C, l, t, _, r) => .rewrites C (.and C [l, t]) r
  | none => p

theorem ruleParts_eq {p : Kore.Pattern} {C : Kore.KSort} {l t x r : Kore.Pattern}
    (h : ruleParts p = some (C, l, t, x, r)) : ∃ C', p = .rewrites C (.and C' [l, t, x]) r ∧ dropThird p = .rewrites C (.and C [l, t]) r := by
  unfold dropThird; rw [h]
  unfold ruleParts at h
  split at h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

/-- The right side of a rewrite. -/
def rightOf : Kore.Pattern → Kore.Pattern
  | .rewrites _ _ r => r
  | p => p

/-- The term of a right side `\and{C}(term, \top{C}())`. -/
def rightTerm : Kore.Pattern → Kore.Pattern
  | .and _ (t :: _) => t
  | p => p

/-- The configuration sort. -/
noncomputable abbrev C0 : Kore.KSort := srtOf c topCellSort

/-- The account's rewrite sentences, in text order, which is the order of `c.rules`. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax408, U.ax409, U.ax410, U.ax411, U.ax412, U.ax413, U.ax414, U.ax415, U.ax416, U.ax417]

/-- Γ's axiom of the rule is the text's sentence with a third conjunct on its left side, with one
variable table and one list of free variables. -/
noncomputable def ruleOKB (r : Rule) (ad : AxiomDecl) : Bool :=
  (ruleParts (prioRuleK c r)).isSome &&
    decide (tableOf [] (prioRuleK c r) = tableOf [] (dropThird (prioRuleK c r))) &&
    decide ((freeOf [] (prioRuleK c r)).eraseDups = (freeOf [] (dropThird (prioRuleK c r))).eraseDups) &&
    decide ((trS ad).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r)))).pat)

/-- The second conjunct of a rule's left side holds only of elements of the configuration sort:
it is `\top` there or an equation at it (the `requires`). -/
noncomputable def secondOK : Kore.Pattern → Bool
  | .top s => decide (s = C0)
  | .equals _ s' _ _ => decide (s' = C0)
  | _ => false

/-- The third conjunct is the definedness of the right side, at the configuration sort, the second
is `secondOK`, the right side is `\and{C}(term, \top{C}())`, and it translates in Γ's table as the
sentence's right side in the sentence's table. -/
noncomputable def w2B (r : Rule) (ad : AxiomDecl) : Bool :=
  match ruleParts (prioRuleK c r) with
  | some (C, _, t, x, r') =>
    decide (C = C0) && secondOK t && decide (x = .ceil C0 C0 r') &&
      decide (r' = .and C0 [rightTerm r', .top C0]) &&
      decide (tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, kore.aliasNames⟩ (rightOf ad.ax.pattern) =
        tr ⟨tableOf [] (dropThird (prioRuleK c r)), []⟩ r')
  | none => false

theorem rules_length : c.rules.length = ruleText.length := by decide +kernel

theorem w2_checked : (c.rules.zip ruleText).all (fun p => ruleOKB p.1 p.2 && w2B p.1 p.2) = true := by
  decide +kernel

theorem ovls_nil : c.ovls = [] := by decide +kernel
theorem subsorts_irrefl : c.subsorts.all (fun p => p.1 != p.2) = true := by decide +kernel

theorem top_numbered (H : HookParams) : topCellSort < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)

/-- The right side of the sentence holds an element at the valuation `e`. -/
def RightDefined {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M) (ad : AxiomDecl) : Prop :=
  ∃ b, (tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, kore.aliasNames⟩ (rightOf ad.ax.pattern)).interpret I e b

/-- **W2 for the 10 rules, at every valuation**: in a model of Γ, for every H, the j-th rewrite
sentence holds at each valuation at which its right side holds an element. Γ's axiom of the j-th
rule is the sentence with the definedness of the right side on its left side (`w2_checked`),
which holds of every configuration there. -/
theorem rules_w2_all (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : ∀ (j : Nat) (r : Rule) (ad : AxiomDecl), c.rules[j]? = some r → ruleText[j]? = some ad →
      ∀ e, RightDefined I e ad → ∀ m, (trS ad).pat.interpret I e m := by
  intro j r ad hr ha e hdef m
  have hz : (r, ad) ∈ c.rules.zip ruleText :=
    List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_zip_eq_some]; exact ⟨hr, ha⟩⟩
  have hok := List.all_eq_true.mp w2_checked _ hz
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hok1, hok2⟩ := hok
  simp only [ruleOKB, Bool.and_eq_true, decide_eq_true_eq] at hok1
  obtain ⟨⟨⟨hp, htab⟩, hfree⟩, htx⟩ := hok1
  obtain ⟨⟨C, l, t, x, r'⟩, hq⟩ := Option.isSome_iff_exists.mp hp
  rw [w2B, hq] at hok2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok2
  obtain ⟨⟨⟨⟨hC, ht⟩, hx⟩, hr'⟩, htr⟩ := hok2
  subst hC hx
  obtain ⟨C', hpe, hd⟩ := ruleParts_eq hq
  rw [htx]
  haveI : OvlOK (cH H) := .of_nil ovls_nil subsorts_irrefl
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI (top_numbered H)
  have hg : I ⊧ᴵ (trAxiom [] [] (kAx (prioRuleK c r))).pat :=
    hI _ (Or.inl (Or.inr (Or.inl ⟨_, by
      rw [TiePair.ruleItems_withHooks]; exact List.mem_map_of_mem (List.mem_of_getElem? hr), rfl⟩)))
  have hS : ∀ (T : VarTable) b, (trSort T C0).interpret I e b ↔ b = σ := fun T b => by
    unfold C0 srtOf; rw [trSort_srt]; exact hσ1 b
  have htop : ∀ (T : VarTable) a, (tr ⟨T, []⟩ (.top C0)).interpret I e a → Inh I σ a := fun T a ha => by
    rw [KoreAML.tr, interp_sTop hD (by unfold C0 srtOf; rw [trSort_srt]; rfl), interp_inhOf_of (hS T)] at ha
    exact ha
  have hsec : ∀ (T : VarTable) a, (tr ⟨T, []⟩ t).interpret I e a → Inh I σ a := fun T a ha => by
    unfold secondOK at ht
    split at ht
    · rename_i s
      rw [of_decide_eq_true ht] at ha
      exact htop T a ha
    · rename_i s s' p q
      rw [of_decide_eq_true ht] at ha
      rw [KoreAML.tr] at ha
      unfold sEquals sFloor at ha
      rw [interp_sNot] at ha
      exact (interp_inhOf_of (hS T)).mp ha.2
    · cases ht
  refine tieRule_more hD (g := kAx (prioRuleK c r)) (t := kAx (dropThird (prioRuleK c r))) (ls := [l, t])
    (xs := [.ceil C0 C0 r']) (List.cons_ne_nil _ _) hpe hd htab hfree hg e (fun x hx a hls => ?_) m
  rw [List.mem_singleton.mp hx, KoreAML.tr]
  refine (interp_sCeil hD hc (hS _) (hS _) hσ2 hσ2 (fun b hb => ?_) a).mpr ⟨?_, hsec _ a (hls t (by simp))⟩
  · rw [hr'] at hb
    exact htop _ b ((interp_and (List.cons_ne_nil _ _)).mp hb _ (by simp))
  · obtain ⟨b, hb⟩ := hdef
    exact ⟨b, htr ▸ hb⟩

/-- **W2 for the 10 rules** (`AtValues` with the guard): in a model of Γ, for every H, the j-th
rewrite sentence holds at each valuation that sends its variables to values and at which its right
side holds an element. No rule has one of a smaller priority, so the guard has no second part. -/
theorem rules_w2 (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ∀ (j : Nat) (r : Rule) (ad : AxiomDecl), c.rules[j]? = some r → ruleText[j]? = some ad →
      ∀ e, AtValues (cH H) I e ad.ax → RightDefined I e ad → ∀ m, (trS ad).pat.interpret I e m :=
  fun _ _ _ hI j r ad hr ha e _ hdef m => rules_w2_all H hI j r ad hr ha e hdef m

end KCore.TieKk

#check @KCore.TieKk.rules_w2
#print axioms KCore.TieKk.rules_w2
