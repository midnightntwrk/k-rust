/-
  The account of the tie on `f2-examples/rulecool.kompile.kore` (fixture e2-rule): every sentence
  of the user module is in exactly one class of the tie's directions (`account`, `account_sizes`,
  `account_classes`), the class lists agree with the lists the class theorems are stated over
  (`account_lists`; the theorems are test/TieRuleCoolText.lean's, test/TieRuleCoolCons.lean's,
  test/TieRuleCool.lean's and test/TieRuleCoolAtValues.lean's), and the no-direction class is
  exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  Run from the package root: `lake env lean -j1 test/TieRuleCoolAccount.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleCoolAccount

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rulecool.kompile.kore"
definition_of defn from "f2-examples/rulecool.kompile.kore"
user_axioms U from "f2-examples/rulecool.kompile.kore" module "E2-RULE"

noncomputable abbrev c : Semantics := defn.sem

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-RULE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- The function sentences, in the order of Γ's equations (test/TieRuleCoolText.lean's `fnText`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-! ## Symbols the text's sentences apply that Γ has no symbol for

The cell initializers and the counter's getter (91, 227 to 230), the projections (268 to 282),
seven hooked symbols' `functional` sentences (39, 43, 45, 76, 78, 121, 122) and two library
sentences (174, 206) apply a symbol that is not among
Γ's symbols (`kernelSyms`): Γ states nothing of it, so no direction holds for these sentences.
The same holds of 109 (`ite{Sort}`'s `functional` sentence, at the sort variable `Sort`) and 262,
263 (`ite{K}`'s two equations): a symbol with sort parameters is one symbol at each instance, and
Γ applies its `ite`, the registry's `kIte` at KItem, at no sort argument (`ite_absent`).
`<<Int` and `>>Int` are symbols of Γ (interpreted hooks), so the sentences over them alone are
not of this kind (`shift_syms`, `account_absent`); nor are the equations of `bitRangeInt` and
`signExtendBitRangeInt` (225, 284), which apply symbols Γ interprets and are of the class library. -/

theorem absent_syms : ["LblinitKCell", "LblgetGeneratedCounterCell", "Lblproject'Coln'Int",
    "Lbl'UndsAnd-'Int'Unds'"].all (fun n => (kernelSyms c).all (fun k => c.symName k.name != n)) = true := by
  decide +kernel

theorem ite_absent : [U.ax109, U.ax262, U.ax263].all (fun ad =>
      (appHeadsOf ad.ax.pattern).any (fun h => h.1 == "Lblite" && !gammaHasHead c h)) = true ∧
    gammaHasHead c ("Lblite", []) = true := by
  decide +kernel

theorem shift_syms : ["Lbl'Unds-LT--LT-'Int'Unds'", "Lbl'Unds-GT--GT-'Int'Unds'"].all
    (fun n => (kernelSyms c).any (fun k => c.symName k.name == n)) = true := by
  decide +kernel

/-! ## The account: every sentence of the user module is in exactly one class

The classes are those of the tie's directions. The lists are checked for one thing here, that they
partition the 282 sentences; what holds of a class is its own theorem, stated over its list. -/

/-- Per class, the indices (`AxiomDecl.index`) of its sentences.
- function equation: the 31 of `fnText`, equal to Γ's items;
- rewrite rule: 164 to 172, the nine rules (test/TieRuleCool.lean);
- priority equation: an equation with `priority(n)` that is not `owise` (none here);
- constructor functional, subsort, injectivity, distinctness, no junk: the constructor sentences;
- function functional: the `functional` sentence of a function of the definition (the 16 sort
  predicates), which Γ does not hold;
- hooked functional: the `functional` sentence of a symbol Γ states by its graph (`freshInt`'s
  among them, 90: the registry interprets it);
- collection law: associativity and the two units of `_List_`, `_Map_`, `_Set_`;
- library: an equation or a lemma of the builtin library over symbols Γ has;
- set idempotence: 64, refuted;
- set-variable lemma: 135 to 139 and 285, listed in their class;
- no direction: a sentence that applies a head Γ does not have (`appHeadsOf`, `gammaHasHead`). -/
def classes : List (String × List Nat) :=
  [("function equation", [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
      250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261]),
   ("rewrite rule", [164, 165, 166, 167, 168, 169, 170, 171, 172]),
   ("priority equation", []),
   ("constructor functional", [25, 27, 29, 31, 80, 85, 88, 113, 114]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]),
   ("injectivity", [26, 28, 30, 32, 81, 86, 89]),
   ("distinctness", [82, 83, 87]),
   ("no junk", [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]),
   ("function functional", [93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]),
   ("hooked functional", [22, 23, 24, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 59,
      67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 79, 84, 90, 92, 110, 111, 112, 115, 116, 117, 118, 119,
      120]),
   ("collection law", [56, 57, 58, 60, 61, 62, 63, 65, 66]),
   ("library", [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
      159, 160, 161, 162, 163, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
      188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 207,
      208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226,
      264, 265, 266, 267, 283, 284]),
   ("set idempotence", [64]),
   ("set-variable lemma", [135, 136, 137, 138, 139, 285]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("no direction", [39, 43, 45, 76, 78, 91, 109, 121, 122, 174, 206, 227, 228, 229, 230, 262, 263, 268, 269, 270,
      271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 31), ("rewrite rule", 9), ("priority equation", 0), ("constructor functional", 9), ("subsort", 18), ("injectivity", 7), ("distinctness", 3), ("no junk", 12), ("function functional", 16), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("no direction", 32)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The class lists agree with the lists the class theorems are stated over: the function
equations are `fnText`'s, the rules are 164 to 172, the no-junk sentences are the three trivial ones and
the nine over generators, the refuted one is 64, and the set-variable lemmas are six. -/
theorem account_lists : (classOf "function equation").isPerm (fnText.map (·.index)) = true ∧
    classOf "rewrite rule" = [U.ax164, U.ax165, U.ax166, U.ax167, U.ax168, U.ax169, U.ax170, U.ax171, U.ax172].map (·.index) ∧
    classOf "no junk" = [U.ax123, U.ax124, U.ax125, U.ax126, U.ax127, U.ax128, U.ax129, U.ax130, U.ax131, U.ax132,
      U.ax133, U.ax134].map (·.index) ∧
    classOf "set idempotence" = [U.ax64.index] ∧
    classOf "set-variable lemma" = [U.ax135, U.ax136, U.ax137, U.ax138, U.ax139, U.ax285].map (·.index) := by
  decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]; decide +kernel

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it
(`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

end KCore.TieRuleCoolAccount

#print axioms KCore.TieRuleCoolAccount.absent_syms
#print axioms KCore.TieRuleCoolAccount.ite_absent
#print axioms KCore.TieRuleCoolAccount.account
#print axioms KCore.TieRuleCoolAccount.account_sizes
#print axioms KCore.TieRuleCoolAccount.account_classes
#print axioms KCore.TieRuleCoolAccount.account_lists
#print axioms KCore.TieRuleCoolAccount.account_absent
#print axioms KCore.TieRuleCoolAccount.absent_closed
