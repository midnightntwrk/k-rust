/-
  The rules of `f2-examples/e3-cells.kompile.kore` (construct fixture e3-cells, `test/TieE3Cells.lean`
  ties its other sentences) against their text sentences, and the converse over Γ's content, for
  every interpretation H, on the literal `defn`. Nothing here reads `Parse.parse` or `emit`. Run from
  the package root: `lake env lean -j1 test/TieE3CellsRules.lean`.

  The rules, sentences 197 to 201 in the order of `c.rules` (`rule_prios`): four of priority 50 over
  the cells `<k>`, `<s>`, `<m>` of `<t>` (two of them name the cells `<s>` and `<m>` with `#as`) and
  one of priority 60, `<k> e ~> R </k> => <k> a ~> R </k>`, beside the priority-50 rule of the same
  left side.
  - `rules_tie` (kernel): Γ's axiom of each rule (`prioRuleK`) is its sentence with conjuncts more on
    the left side (the definedness of the right side; for the priority-60 rule also the negation of
    the left sides and `requires` of the rules of priority 50), the two with one variable table and
    one list of free variables. Γ's variable names differ from the text's (`VarV0`, ... for
    `_DotVar2`, `N`, ...), in the same order of first occurrence, so the translations agree.
  - `rules_from_text` (W1, every H): each of Γ's rule items is a consequence of its sentence.
  - `gamma_origin`, `gamma_from`: every premise of Γ is a function sentence's translation (the 43
    equations, `fn_shape`), a rule item (a consequence of its sentence), one of the five parts Γ
    defines by predicates (`Families`), or definedness; so every premise of Γ is a consequence of
    `Pre`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3CellsRules

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-cells.kompile.kore"
definition_of defn from "f2-examples/e3-cells.kompile.kore"
user_axioms U from "f2-examples/e3-cells.kompile.kore" module "E3-CELLS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c

/-! ## The rule sentences -/

/-- The rule sentences, in the order of `c.rules`. -/
noncomputable def ruleText : List AxiomDecl := [U.ax197, U.ax198, U.ax199, U.ax200, U.ax201]

noncomputable def rulePats : List P := ruleText.map (trS · |>.pat)

/-- The rules' priorities (the text's `priority` attributes) and their sentences' indices. -/
theorem rule_prios : c.rules.map (·.prio) = [50, 50, 50, 50, 60] ∧
    ruleText.map (·.index) = [197, 198, 199, 200, 201] := by
  decide +kernel

/-- **Γ's axiom of each rule is its sentence with conjuncts more on the left side** (kernel). -/
theorem rules_tie : TieRulePair.rulesTieB c rulePats = true := by decide +kernel

theorem rules_tieH (H : HookParams) : TieRulePair.rulesTieB (cH H) rulePats = true :=
  (TieRulePair.rulesTieB_withHooks c H rulePats).trans rules_tie

/-- **W1 for the rules**: each of Γ's rule items is a consequence of its sentence, for every H. -/
theorem rules_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (ruleItems (cH H))[j]? = some it →
      ∃ ad, ruleText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TieRulePair.rules_from_text (rules_tieH H) j it hj
  unfold rulePats at ht
  rw [List.getElem?_map] at ht
  cases hf : ruleText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- Each rule item, by membership: a consequence of a sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts [(trS ad).pat] ⊧ it.pat := by
  intro it hit
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hit
  obtain ⟨ad, had, hent⟩ := rules_from_text H j it (he ▸ List.getElem?_eq_getElem hj)
  exact ⟨ad, List.mem_of_getElem? had, hent⟩

/-! ## The converse over Γ's content -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 43 equations, in `fnItems`'s order (`TieE3Cells.fnText`). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax277, U.ax285, U.ax284, U.ax283, U.ax282, U.ax293, U.ax292, U.ax299, U.ax298, U.ax287,
   U.ax286, U.ax264, U.ax263, U.ax276, U.ax275, U.ax272, U.ax271, U.ax274, U.ax273, U.ax301,
   U.ax300, U.ax305, U.ax304, U.ax303, U.ax302, U.ax279, U.ax278, U.ax281, U.ax280, U.ax295,
   U.ax294, U.ax297, U.ax296, U.ax289, U.ax288, U.ax291, U.ax290, U.ax268, U.ax267, U.ax270,
   U.ax269, U.ax266, U.ax265]

/-- Γ's equations are the text's sentences' translations, pattern for pattern. -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, Γ's rule items (each a consequence of its
text sentence, `rule_from_text`), and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ ΓRules (cH H) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; a rule item is a consequence of a text sentence of `ruleText`; everything else is one of
the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ (ΓRules (cH H) φ ∧ ∃ ad ∈ ruleText, TiePair.Texts [(trS ad).pat] ⊧ φ) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
  · exact hI _ (Or.inl (Or.inr hr))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inl (Or.inr hx)))

end KCore.TieE3CellsRules

#check @KCore.TieE3CellsRules.rule_prios
#check @KCore.TieE3CellsRules.rules_tie
#check @KCore.TieE3CellsRules.rules_from_text
#check @KCore.TieE3CellsRules.rule_from_text
#check @KCore.TieE3CellsRules.fn_shape
#check @KCore.TieE3CellsRules.gamma_origin
#check @KCore.TieE3CellsRules.gamma_from
#print axioms KCore.TieE3CellsRules.rules_tie
#print axioms KCore.TieE3CellsRules.rules_from_text
#print axioms KCore.TieE3CellsRules.rule_from_text
#print axioms KCore.TieE3CellsRules.gamma_origin
#print axioms KCore.TieE3CellsRules.gamma_from
