/-
  The rules of `f2-examples/e6-float-literals.kompile.kore` (construct fixture e6-float-literals,
  `test/TieE6FloatLiterals.lean` ties its other sentences) against their text sentences, for every
  interpretation H, on the literal `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the
  package root: `lake env lean -j1 test/TieE6FloatLiteralsRules.lean`.

  The 27 rules, sentences 174 to 200 in the order of `c.rules`, are `<k> go(n) => l(F) ... </k>`, one
  per Float literal F the text writes (`rule_lits`). Γ's axiom of each writes F at the text of the
  datum the reader reads it as (`Lit.text`: significand, exponent and format, `pPxE`), and the
  translation sends each `\dv` string to a symbol of its own (`sym (.dv lit)`).
  - `rule_lits` (kernel): for each rule, the `\dv` literals of Γ's axiom and of its sentence, in
    order: the Int argument of `go`, the same on both sides, then the Float literal, once in the
    sentence's right side and twice in Γ's axiom (its right side, and `⌈r⌉` on its left side).
  - `rule189_tie` (kernel): rule 15, sentence 189 (`l(-Infinityp24x8)`), the one literal the text
    writes as Γ does: Γ's axiom is its sentence with the conjunct `⌈r⌉` more on the left side
    (`TieRulePair.ruleTextB`). `rule189_from_text` (W1, every H): Γ's item of rule 15 is a
    consequence of sentence 189 alone (`TieRulePair.rule_weaker`).
  - The other 26 rules are not tied here: Γ's item applies the symbol of the datum's text, the
    sentence that of the text's string (`lits_apart`), and no sentence of the text and no item of
    its signature relates two `\dv` symbols of Float (the signature's `\dv` items are arities), so
    the sentence states nothing of the literal Γ's item holds. That the two strings denote one datum
    is the meaning of the Float literal (a decimal rounded to the suffix's format), which the
    sentences of the text do not state.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6FloatLiteralsRules

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-float-literals.kompile.kore"
definition_of defn from "f2-examples/e6-float-literals.kompile.kore"
user_axioms U from "f2-examples/e6-float-literals.kompile.kore" module "E6-FLOAT-LITERALS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem rules_len : c.rules.length = 27 := by decide +kernel

/-- Per rule, in the order of `c.rules`: its position, its sentence's index, the Int argument of
`go`, the Float literal as the text writes it, and as Γ's axiom writes it. -/
def litRows : List (Nat × Nat × String × String × String) :=
  [(0, 174, "1", "1.0", "10000000000000000000000000000000000000000000000000000e-52p53x11"),
   (1, 175, "10", "1.0f", "100000000000000000000000e-23p24x8"),
   (2, 176, "11", "1.0F", "100000000000000000000000e-23p24x8"),
   (3, 177, "12", "1.0d", "10000000000000000000000000000000000000000000000000000e-52p53x11"),
   (4, 178, "13", "1.0D", "10000000000000000000000000000000000000000000000000000e-52p53x11"),
   (5, 179, "14", "1.0p24x8", "100000000000000000000000e-23p24x8"),
   (6, 180, "15", "1.0P24X8", "100000000000000000000000e-23p24x8"),
   (7, 181, "16", "1.0p53x11", "10000000000000000000000000000000000000000000000000000e-52p53x11"),
   (8, 182, "17", ".5f", "500000000000000000000000e-24p24x8"),
   (9, 183, "18", "Infinity", "Infinityp53x11"),
   (10, 184, "19", "+Infinity", "Infinityp53x11"),
   (11, 185, "2", "1.", "10000000000000000000000000000000000000000000000000000e-52p53x11"),
   (12, 186, "20", "-Infinity", "-Infinityp53x11"),
   (13, 187, "21", "Infinityf", "Infinityp24x8"),
   (14, 188, "22", "-InfinityD", "-Infinityp53x11"),
   (15, 189, "23", "-Infinityp24x8", "-Infinityp24x8"),
   (16, 190, "24", "NaN", "NaNp53x11"),
   (17, 191, "25", "NaNf", "NaNp24x8"),
   (18, 192, "26", "NaNd", "NaNp53x11"),
   (19, 193, "27", "NaNP24X8", "NaNp24x8"),
   (20, 194, "3", "1e3", "10000000000000000000000000000000000000000000000e-43p53x11"),
   (21, 195, "4", "1.5e-3", "150000000000000003122502256758252769941464066505432128906250e-62p53x11"),
   (22, 196, "5", "1.5E+3", "1500000000000000000000000000000000000000000000e-42p53x11"),
   (23, 197, "6", "+1.5", "15000000000000000000000000000000000000000000000000000e-52p53x11"),
   (24, 198, "7", "-1.5", "-15000000000000000000000000000000000000000000000000000e-52p53x11"),
   (25, 199, "8", ".5", "50000000000000000000000000000000000000000000000000000e-53p53x11"),
   (26, 200, "9", ".5e2", "5000000000000000000000000000000000000000000000000e-47p53x11")]

/-- The sentence of the user module of an index. -/
noncomputable def sentAt (i : Nat) : Option AxiomDecl := U.all.find? (·.index == i)

/-- **The literals of each rule** (kernel): Γ's axiom of rule j holds the `\dv` literals `[n, g, g]`
and its sentence i the literals `[n, t]`, for each row `(j, i, n, t, g)` of `litRows`; the rows are
the 27 rules, and their sentences are the class rewrite rule of the tie. -/
theorem rule_lits : litRows.map (·.1) = List.range 27 ∧
    litRows.map (·.2.1) = (List.range 27).map (174 + ·) ∧
    litRows.all (fun (j, i, n, t, g) =>
      (c.rules[j]?.map fun r => KoreAML.dvLitsOf (prioRuleK c r)) == some [n, g, g] &&
      ((sentAt i).map fun ad => KoreAML.dvLitsOf ad.ax.pattern) == some [n, t]) = true := by
  decide +kernel

/-- **The rows whose two literals differ** (kernel): every rule but rule 15 (sentence 189). -/
theorem lits_apart : (litRows.filter fun (_, _, _, t, g) => t != g).map (·.2.1) =
    ((List.range 27).map (174 + ·)).erase 189 := by
  decide +kernel

/-- Rule 15, `<k> go(23) => l(-Infinityp24x8) ... </k>`. -/
noncomputable def rInf : Rule := c.rules[15]'(by decide +kernel)

/-- **Γ's axiom of rule 15 is sentence 189 with the conjunct `⌈r⌉` more on the left side**
(kernel). -/
theorem rule189_tie : TieRulePair.ruleTextB (trS U.ax189).pat (prioRuleK c rInf) = true := by decide +kernel

/-- **W1 for rule 15**: Γ's item of it is a consequence of sentence 189, for every H. -/
theorem rule189_from_text (H : HookParams) :
    ∀ it, (ruleItems (cH H))[15]? = some it → TiePair.Texts [(trS U.ax189).pat] ⊧ it.pat := by
  intro it hit
  rw [TiePair.ruleItems_withHooks] at hit
  unfold ruleItems at hit
  rw [List.getElem?_map, show c.rules[15]? = some rInf from List.getElem?_eq_getElem _] at hit
  cases hit
  exact fun {M} _ {I} hI =>
    TieRulePair.rule_weaker (TiePair.defOK_texts hI) rule189_tie (hI _ (Or.inl (List.mem_singleton_self _)))

end KCore.TieE6FloatLiteralsRules

#check @KCore.TieE6FloatLiteralsRules.rules_len
#check @KCore.TieE6FloatLiteralsRules.rule_lits
#check @KCore.TieE6FloatLiteralsRules.lits_apart
#check @KCore.TieE6FloatLiteralsRules.rule189_tie
#check @KCore.TieE6FloatLiteralsRules.rule189_from_text
#print axioms KCore.TieE6FloatLiteralsRules.rule_lits
#print axioms KCore.TieE6FloatLiteralsRules.lits_apart
#print axioms KCore.TieE6FloatLiteralsRules.rule189_tie
#print axioms KCore.TieE6FloatLiteralsRules.rule189_from_text
