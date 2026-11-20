/-
  The rule sentence of construct fixture e3-ml-req-or-unheld against the reading `requiresOrSplit`:
  `rule <k> go(X) => done ... </k> requires X >Int 0 #Or Y:Int >Int 2 [unboundVariables(Y)]`. The
  text is `f2-examples/e3-ml-req-or-unheld.kompile.kore`, the one test/TieE3MlReqOrUnheld.lean
  ties sentence by sentence, the rule sentence 154 in its section `The rules` by W1 from the text
  (`TieE3MlReqOrUnheld.Rules.rule_from_text_aux`, this file's proof); this file holds that
  sentence's theorems. Run from the package root: `lake env lean -j1 test/CondBoolReqOrUnheld.lean`.
  Every statement is on the literals `kore` and `defn`, for every interpretation H; nothing reads
  `Parse.parse` or `emit`.

  The sentence's `requires` is
  `\equals{SortBool{}, C}(\and{SortBool{}}(\or{SortBool{}}(X >Int 0, Y >Int 2), _Gen0), true)`
  with `_Gen0:Bool` a free variable of the sentence that Γ's items do not have, and Y a variable
  the left side's term does not hold. Γ holds two rule items of one priority, one per disjunct:
  `requires` `X >Int 0`, and `requires` `Y >Int 2`, whose `CondDecided` is owed (Y:Int is bound by
  nothing and Int is not confined).

  - `text_item`, `gamma_item0`, `gamma_item1` (kernel): the sentence and Γ's two items are the items
    of `\rewrites{C}(L, r)` at one variable table with one right side, the sentence's left side
    `Ltext` and Γ's `LG A`, `LG B` (`left0_eq`, `q1_eq`).
  - W1, `rule_from_text_aux`: each of Γ's two items is a consequence of the sentence with the
    text's sentences 135 (`INT-KORE.eq-int-true-left`) and 49 (the functional sentence of
    `_==Int_`) (`ruleAux`), the text's G-nonempty item of Int (`ruleSigAux`, `ruleSigAux_text`) and
    the signature (`ΓSig`), at every valuation; no item of `ΓDomains` is among the premises. The
    sentence is taken at `_Gen0 := true` (`true` denotes one element of Bool, from 135, 49 and an
    element of Int: `true_one`), where `(A ∨ B) ∧ true` equals `true` as soon as one disjunct does
    (`gamma_sub_text`); Γ's items do not read `_Gen0` (`item0_noG`, `item1_noG`), and the first
    does not read Y, to which Int's G-nonempty item gives an element (`item_drop`).
  - The converse at values, `rule154_at_values` (`EntailsAtValues`): at values of X and Y each
    disjunct denotes the element of `true`, the element of `false` or nothing (`atom_dich`), so
    where the sentence's left side holds an element, one disjunct is exactly `true`: the element is
    in that disjunct's item's left side (`text_sub_gamma`).
  - The owed `CondDecided`, for every H: the rule of the disjunct `Y >Int 2` is `Witnessed` at
    Y := 3 (`witnessedH`), so `OpenDecided` holds (`openDecidedH`), and with it `FnHyp` and
    `consistent` for every H.

  `rule154_at_values` is over Γ, and holds of `Γc`, which is Γ with `boolClosed` here
  (`readsConfined` is true: no left side binds Y); `consistent` is over `Γc`. `rule_from_text_aux`
  reads neither: its premises are the text's sentences and signature items with `ΓSig`.

  No expectation is stated here. The kernel decisions of `Semantics.ok` and `CExec.execReady` do
  not reduce on this text, so no checker lists its steps, and `sound_at_step` asks
  `readsConfined = false`: a step, and its family over `Γc`, would be built by hand.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.CondBoolReqOrUnheld

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-req-or-unheld.kompile.kore"
definition_of defn from "f2-examples/e3-ml-req-or-unheld.kompile.kore"
user_axioms U from "f2-examples/e3-ml-req-or-unheld.kompile.kore" module "E3-ML-REQ-OR-UNHELD"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-! ## The rule sentence 154 and Γ's two rule items -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)

/-- Γ's axioms of the two rules. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
noncomputable def p1 : Kore.Pattern := prioRuleK c r1

/-- Their parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)
noncomputable def q1 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p1).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0
kernel_rfl q1_eq' : TieRuleLhs.rwParts p1 = some q1

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩] := by
  kernel_rfl

theorem names : c.symName 383 = "Lbl'-LT-'k'-GT-'" ∧ c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" ∧
    c.sortName 32 = "Exp" ∧ c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" := by
  decide +kernel

/-- Γ's variables: X, the rest of the K cell, the counter cell, Y; and a variable for the
sentence's `_Gen0`, which Γ's axioms do not have. -/
def xX : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Int")
def xK : Kore.EVar := KoreAML.evar "VarV1" (KoreAML.srt "K")
def xC : Kore.EVar := KoreAML.evar "VarV2" (KoreAML.srt "GeneratedCounterCell")
def xY : Kore.EVar := KoreAML.evar "VarV3" (KoreAML.srt "Int")
def xG : Kore.EVar := KoreAML.evar "VarG" (KoreAML.srt "Bool")

/-- The two disjuncts: `X >Int 0` and `Y >Int 2`. -/
def atomA : Kore.Pattern := .app ⟨⟨"Lbl'Unds-GT-'Int'Unds'"⟩⟩ [] [.var (.evar xX), .dv (KoreAML.srt "Int") "0"]
def atomB : Kore.Pattern := .app ⟨⟨"Lbl'Unds-GT-'Int'Unds'"⟩⟩ [] [.var (.evar xY), .dv (KoreAML.srt "Int") "2"]

/-- The left side's term. -/
noncomputable def hd : Kore.Pattern := TieRuleLhs.andHead q0.2.1

/-- `\equals{SortBool{}, C}(p, true)`. -/
noncomputable def eqT (p : Kore.Pattern) : Kore.Pattern :=
  .equals (KoreAML.srt "Bool") q0.1 p (.dv (KoreAML.srt "Bool") "true")

/-- Γ's left side of the rule with the `requires` `p`: the term, `p = true`, and `⌈r⌉`. -/
noncomputable def LG (p : Kore.Pattern) : Kore.Pattern := .and q0.1 [hd, eqT p, .ceil q0.1 q0.1 q0.2.2]

kernel_rfl left0_eq : q0.2.1 = LG atomA
kernel_rfl q1_eq : q1 = (q0.1, LG atomB, q0.2.2)

/-- The left side as the text writes it: the term, and the `requires`
`\and{SortBool{}}(\or{SortBool{}}(A, B), _Gen0)` equated with `true`. -/
noncomputable def Ltext : Kore.Pattern :=
  .and q0.1 [hd, eqT (.and (KoreAML.srt "Bool") [.or (KoreAML.srt "Bool") [atomA, atomB], .var (.evar xG)])]

/-- The one variable table: the sentence's variables, Γ's four first. -/
noncomputable def tb : VarTable := tableOf [] (.rewrites q0.1 Ltext q0.2.2)
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups
noncomputable def f0 : List VarKey := (freeOf [] p0).eraseDups
noncomputable def f1 : List VarKey := (freeOf [] p1).eraseDups
/-- The first rule's free variables with Y. -/
noncomputable def f0Y : List VarKey := f0 ++ [evarKey xY]

/-- **The rule sentence is the item of `\rewrites{C}(Ltext, r)`** (kernel). -/
theorem text_item : (trS U.ax154).pat = TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2 := by
  have h : TiePair.renSeq (TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2) [] = some (trS U.ax154).pat := by
    decide +kernel
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **Γ's two rule items are the items of `\rewrites{C}(LG A, r)` and `\rewrites{C}(LG B, r)` at
the same table** (kernel). -/
theorem gamma_item0 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat = TieRuleLhs.itemAt tb f0 q0.1 (LG atomA) q0.2.2 := by
  decide +kernel
theorem gamma_item1 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩).pat = TieRuleLhs.itemAt tb f1 q0.1 (LG atomB) q0.2.2 := by
  decide +kernel

/-- Γ's free variables are the sentence's, and the sentence's are Γ's and `_Gen0`. -/
theorem free_sub0 : ∀ k ∈ f0, k ∈ fT := by decide +kernel
theorem free_sub1 : ∀ k ∈ f1, k ∈ fT := by decide +kernel
theorem free_more0 : ∀ k ∈ fT, k ∈ f0Y ∨ k = evarKey xG := by decide +kernel
theorem free_moreY : ∀ k ∈ f0Y, k ∈ f0 ∨ k = evarKey xY := by decide +kernel
theorem free_more1 : ∀ k ∈ fT, k ∈ f1 ∨ k = evarKey xG := by decide +kernel

/-- Γ's items do not read `_Gen0`, and the first rule's does not read Y. -/
theorem item0_noG : (TieRuleLhs.itemAt tb f0Y q0.1 (LG atomA) q0.2.2).isFreeEvar (tb.ev (evarKey xG)) = false := by
  decide +kernel
theorem item0_noY : (TieRuleLhs.itemAt tb f0 q0.1 (LG atomA) q0.2.2).isFreeEvar (tb.ev (evarKey xY)) = false := by
  decide +kernel
theorem item1_noG : (TieRuleLhs.itemAt tb f1 q0.1 (LG atomB) q0.2.2).isFreeEvar (tb.ev (evarKey xG)) = false := by
  decide +kernel

/-- The sentence's variables but `_Gen0` are free in it and have the table's indices. -/
theorem idx :
    (KoreAML.VarKey.evar "VarX" (KoreAML.srt "Int") ∈ (freeOf [] U.ax154.ax.pattern).eraseDups ∧
      (tableOf U.ax154.ax.sortVars U.ax154.ax.pattern).ev (.evar "VarX" (KoreAML.srt "Int")) = tb.ev (evarKey xX)) ∧
    (KoreAML.VarKey.evar "Var'Unds'DotVar1" (KoreAML.srt "K") ∈ (freeOf [] U.ax154.ax.pattern).eraseDups ∧
      (tableOf U.ax154.ax.sortVars U.ax154.ax.pattern).ev (.evar "Var'Unds'DotVar1" (KoreAML.srt "K")) = tb.ev (evarKey xK)) ∧
    (KoreAML.VarKey.evar "Var'Unds'DotVar0" (KoreAML.srt "GeneratedCounterCell") ∈ (freeOf [] U.ax154.ax.pattern).eraseDups ∧
      (tableOf U.ax154.ax.sortVars U.ax154.ax.pattern).ev (.evar "Var'Unds'DotVar0" (KoreAML.srt "GeneratedCounterCell")) =
        tb.ev (evarKey xC)) ∧
    (KoreAML.VarKey.evar "VarY" (KoreAML.srt "Int") ∈ (freeOf [] U.ax154.ax.pattern).eraseDups ∧
      (tableOf U.ax154.ax.sortVars U.ax154.ax.pattern).ev (.evar "VarY" (KoreAML.srt "Int")) = tb.ev (evarKey xY)) := by
  decide +kernel

/-! ## Sorts and values -/

/-- A sort is the one of its name. -/
theorem sort_of_name {n : String} {S0 : Srt}
    (hd : ∀ S ∈ List.range (nRegSorts + c.sortNames.length), KoreAML.srt (c.sortName S) = KoreAML.srt n → S = S0)
    (hn : n ≠ "") (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt n) : S = S0 := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact hd S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    unfold KoreAML.srt at h
    injection h with h; injection h with h; injection h with h
    exact hn (by simpa using h.symm)

theorem int_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Int") : S = Srt.int :=
  sort_of_name (by decide +kernel) (by decide) S h
theorem k_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "K") : S = Srt.k :=
  sort_of_name (by decide +kernel) (by decide) S h
theorem cnt_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "GeneratedCounterCell") : S = 19 :=
  sort_of_name (by decide +kernel) (by decide) S h

/-- `<generatedTop>(<k>(done ~> q1), q2)`. -/
def rForm (q1 q2 : Kore.Pattern) : Kore.Pattern :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] [.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] [.app ⟨⟨"kseq"⟩⟩ []
    [KoreAML.injP "Exp" "KItem" (.app ⟨⟨"Lbldone"⟩⟩ [] []), q1]], q2]

-- The right side, the text's: the term and `\top`.
kernel_rfl r_eq : q0.2.2 = .and q0.1 [rForm (.var (.evar xK)) (.var (.evar xC)), .top q0.1]

/-- The successor `<generatedTop>(<k>(done ~> v1), v2)`. -/
def yOf (v1 v2 : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor 383 [.ctor kseq [.inj 32 Srt.kitem (.ctor 385 []), v1]], v2]

theorem y_kore : (fun (H : HookParams) (v1 v2 : GroundTerm) => GroundTerm.kore (cH H) (yOf v1 v2)) =
    (fun H v1 v2 => rForm (v1.kore (cH H)) (v2.kore (cH H))) := by
  kernel_rfl

theorem y_sort {v1 v2 : GroundTerm} (h1 : c.sortOf v1 = some Srt.k) (h2 : c.sortOf v2 = some 19) :
    c.sortOf (yOf v1 v2) = some topCellSort := by
  have hd : c.sortOf (.inj 32 Srt.kitem (.ctor 385 [])) = some Srt.kitem := by decide +kernel
  have hq : c.sortOf (.ctor kseq [.inj 32 Srt.kitem (.ctor 385 []), v1]) = some Srt.k :=
    sortOf_ctor_of (k := ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩) (by decide +kernel) ⟨hd, h1, trivial⟩
  have hk : c.sortOf (.ctor 383 [.ctor kseq [.inj 32 Srt.kitem (.ctor 385 []), v1]]) = some 30 :=
    sortOf_ctor_of (k := ⟨383, [Srt.k], 30⟩) (by decide +kernel) ⟨hq, trivial⟩
  exact sortOf_ctor_of (k := ⟨topLabel, [30, 19], 17⟩) (by decide +kernel) ⟨hk, h2, trivial⟩

/-- `rForm` at the variables, with the variables replaced. -/
def ρK (q1 q2 : Kore.Pattern) : Kore.EVar → Option Kore.Pattern :=
  fun y => if y = xK then some q1 else if y = xC then some q2 else none

theorem rForm_subst : (fun q1 q2 => TieReqBool.substAt (ρK q1 q2) (rForm (.var (.evar xK)) (.var (.evar xC)))) = rForm := by
  kernel_rfl

kernel_rfl C_eq : q0.1 = KoreAML.srt "GeneratedTopCell"
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")
theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = KoreAML.sym (.dv "false") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool false) = _; decide +kernel
theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool true) = _; decide +kernel

theorem tr_dv {t : VarTable} (n : String) :
    tr ⟨t, []⟩ (.dv (KoreAML.srt "Bool") n) = KoreAML.sym (.dv n) ⬝ KoreAML.sym (.sort "SortBool") := by
  rw [tr, trSort_srt]; rfl

theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

/-! ## The disjuncts as library terms -/

/-- `V >Int 0` and `V >Int 2`, each over one variable. -/
def termA : Term := .app intGt [.var 0, .dv Srt.int (.int 0)]
def termB : Term := .app intGt [.var 0, .dv Srt.int (.int 2)]
def varsX : LibEv.Vars := [("VarV0", Srt.int)]
def varsY : LibEv.Vars := [("VarV3", Srt.int)]

theorem atomA_kore_all : (fun H : HookParams => LibEv.kore (cH H) varsX termA) = fun _ => atomA := by kernel_rfl
theorem atomB_kore_all : (fun H : HookParams => LibEv.kore (cH H) varsY termB) = fun _ => atomB := by kernel_rfl
theorem atomA_srt (H : HookParams) : LibEv.srt? (cH H) varsX termA = some Srt.bool := by
  simp only [termA, LibEv.srt?, LibEv.srts?, Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel
theorem atomB_srt (H : HookParams) : LibEv.srt? (cH H) varsY termB = some Srt.bool := by
  simp only [termB, LibEv.srt?, LibEv.srts?, Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel
theorem varsX_key (H : HookParams) : LibEv.vkey (cH H) varsX 0 = evarKey xX := by
  show LibEv.vkey c varsX 0 = _; decide +kernel
theorem varsY_key (H : HookParams) : LibEv.vkey (cH H) varsY 0 = evarKey xY := by
  show LibEv.vkey c varsY 0 = _; decide +kernel

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A disjunct at a value of its variable denotes the element of `true` alone, or does not
hold it**: a term over the variable, domain values and interpreted symbols, of sort Bool,
denotes the element of its value or nothing (`LibEv.den_val`), and a value of Bool is `true` or
`false`. -/
theorem atom_dich (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) {x : Kore.EVar} {vars : LibEv.Vars} {t : Term}
    {pat : Kore.Pattern}
    (hlen : vars.length = 1) (hs0 : vars[0]?.map (·.2) = some Srt.int)
    (hk : LibEv.kore (cH H) vars t = pat) (hs : LibEv.srt? (cH H) vars t = some Srt.bool)
    (hkey : LibEv.vkey (cH H) vars 0 = evarKey x) {v : GroundTerm} (hv : (cH H).sortOf v = some Srt.int)
    (hden : (den (cH H) v).interpret I e (e.evalEvar (tb.ev (evarKey x)))) {aT : M}
    (hT : ∀ m, (den (cH H) (KCore.bool true)).interpret I e m ↔ m = aT)
    (hF : ¬ (den (cH H) (KCore.bool false)).interpret I e aT) :
    (∀ m, (tr ⟨tb, []⟩ pat).interpret I e m ↔ m = aT) ∨ ¬ (tr ⟨tb, []⟩ pat).interpret I e aT := by
  obtain ⟨a0, ha0, -⟩ := den_single hI hv e
  have hσ : ∀ i p, vars[i]? = some p → ∃ w, [(0, v)].lookup i = some w ∧ (cH H).sortOf w = some p.2 := by
    intro i p hp
    have hi : i < vars.length := (List.getElem?_eq_some_iff.mp hp).1
    rw [hlen] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hp] at hs0
    simp only [Option.map_some, Option.some.injEq] at hs0
    exact ⟨v, rfl, by rw [hs0]; exact hv⟩
  have hag : ∀ i w, i < vars.length → [(0, v)].lookup i = some w →
      ∀ m, m = e.evalEvar (tb.ev (LibEv.vkey (cH H) vars i)) ↔ (den (cH H) w).interpret I e m := by
    intro i w hi hw m
    rw [hlen] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    cases (show some v = some w from hw)
    rw [hkey, ha0, (ha0 _).mp hden]
  obtain ⟨hval, hsrt⟩ := LibEv.den_val (coreOKH H) hI hσ hag t hs
  rw [hk] at hval
  cases hw : LibEv.val (cH H) [(0, v)] t with
  | none =>
    right; intro h
    rw [hval, hw] at h; exact h
  | some w =>
    have hws := hsrt w hw
    rw [Semantics.sortOf_withHooks _ _ noRaw] at hws
    obtain ⟨b, rfl⟩ := shape_bool shapesOK_c hws
    cases b with
    | true => left; intro m; rw [hval, hw]; exact hT m
    | false =>
      right; intro h
      rw [hval, hw] at h; exact hF h

end

/-! ## `true` from the text

Sentence 135 (`INT-KORE.eq-int-true-left`, `{K1 ==Int K2 #Equals true} = {K1 #Equals K2}` over
element variables of Int, with no condition) and sentence 49 (the functional sentence of
`_==Int_`), at an element of Int given to both variables (the text's G-nonempty item of Int), state
that `true` denotes one element of Bool (`TieReqBool.boolTrue_of_text_sig`). -/

/-- **Sentences 135 and 49 are `INT-KORE.eq-int-true-left` and the functional sentence of
`_==Int_`**, as `TieReqBool` writes them (kernel). -/
theorem sents_true : (trS U.ax135).pat = TieReqBool.sentPat TieReqBool.eqIntTrueLeftAx ∧
    (trS U.ax49).pat = TieReqBool.sentPat (TieReqBool.fnlBoolAx TieReqBool.eqIntName) := by
  constructor <;> decide +kernel

/-- `true` is one element of Bool, in a model of definedness and the signature in which Int has an
element and sentences 135 and 49 hold. -/
theorem true_one (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hSig : I ⊧ᴵP ΓSig (cH H)) (hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat)
    (h1 : I ⊧ᴵ (trS U.ax135).pat) (hf1 : I ⊧ᴵ (trS U.ax49).pat) (e : Valuation M) :
    ∃ σB aT, (∀ x, (trSort tb (KoreAML.srt "Bool")).interpret I e x ↔ x = σB) ∧ IsSort I σB ∧
      (∀ m, (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e m ↔ m = aT) ∧ Inh I σB aT := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact TieReqBool.boolTrue_of_text_sig hD hSig (int_numbered H) (int_name H) hN
    (sents_true.1 ▸ h1) (sents_true.2 ▸ hf1) tb e

/-! ## W1: the sentence at `_Gen0 := true` -/

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Where `_Gen0` is `true`, every element of Γ's left side of a disjunct's rule is one of the
text's left side**, at every valuation: where the disjunct `p` equals `true`,
`(A ∨ B) ∧ _Gen0` holds, of the elements of Bool, exactly `true`. -/
theorem gamma_sub_text (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H)) (hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat)
    (h1 : I ⊧ᴵ (trS U.ax135).pat) (hf1 : I ⊧ᴵ (trS U.ax49).pat) (e : Valuation M)
    (hG : (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e (e.evalEvar (tb.ev (evarKey xG))))
    {p : Kore.Pattern} (hp : p = atomA ∨ p = atomB) (a : M)
    (h : (tr ⟨tb, []⟩ (LG p)).interpret I e a) : (tr ⟨tb, []⟩ Ltext).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σC, hσC1, hσC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσC1
  have hSC : ∀ b, (trSort tb q0.1).interpret I e b ↔ b = σC := by
    rw [C_eq, trSort_srt]; exact hσC1
  obtain ⟨σB, aT, hSB, hσB, hat, -⟩ := true_one H hD hSig hN h1 hf1 e
  have hg : e.evalEvar (tb.ev (evarKey xG)) = aT := (hat _).mp hG
  have hTe : ∀ (p q : Kore.Pattern), tr ⟨tb, []⟩ (.equals (KoreAML.srt "Bool") q0.1 p q) =
      sEquals (trSort tb (KoreAML.srt "Bool")) (trSort tb q0.1) (tr ⟨tb, []⟩ p) (tr ⟨tb, []⟩ q) := fun p q => by rw [tr]
  unfold LG at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have hterm := h _ (List.mem_cons_self ..)
  have heq := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold eqT at heq
  rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2] at heq
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hterm
  rw [List.mem_singleton.mp hq]
  unfold eqT
  rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2]
  refine ⟨heq.1, fun x hx => ?_⟩
  rw [tr_and2, interp_sAnd, Model.tr_or2Stdi, interp_sOr, interp_inhOf_of hSB]
  have hv : (tr ⟨tb, []⟩ (.var (.evar xG))).interpret I e x ↔ x = aT := by
    rw [tr, interp_evar, hg]
  rw [hv, hat x]
  constructor
  · exact fun h' => h'.2
  · intro hxT
    refine ⟨⟨hx, ?_⟩, hxT⟩
    have hpx := (heq.2 x hx).mpr ((hat x).mpr hxT)
    rcases hp with rfl | rfl
    · exact Or.inl hpx
    · exact Or.inr hpx

/-- Γ's item of a disjunct's rule from the sentence's item, at one valuation: the sentence at
`_Gen0 := true`, which Γ's item does not read. -/
theorem item_of_text (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H)) (hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat)
    (h1 : I ⊧ᴵ (trS U.ax135).pat) (hf1 : I ⊧ᴵ (trS U.ax49).pat)
    (hT : I ⊧ᴵ TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2) {fG : List VarKey} {p : Kore.Pattern}
    (hp : p = atomA ∨ p = atomB) (hmore : ∀ k ∈ fT, k ∈ fG ∨ k = evarKey xG)
    (hno : (TieRuleLhs.itemAt tb fG q0.1 (LG p) q0.2.2).isFreeEvar (tb.ev (evarKey xG)) = false) :
    I ⊧ᴵ TieRuleLhs.itemAt tb fG q0.1 (LG p) q0.2.2 := by
  intro e m
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, aT, hSB, hσB, hat, hit⟩ := true_one H hD hSig hN h1 hf1 e
  let e' : Valuation M := ⟨Function.update e.evalEvar (tb.ev (evarKey xG)) aT, e.evalSvar⟩
  rw [← interp_evarAt_svin (a := aT) hno m]
  obtain ⟨σB', aT', hSB', hσB', hat', hit'⟩ := true_one H hD hSig hN h1 hf1 e'
  have hgv : e'.evalEvar (tb.ev (evarKey xG)) = aT := by simp [e']
  have hTT : aT' = aT := by
    have h1 : (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e aT := (hat aT).mpr rfl
    rw [tr_dv, ← den_true H] at h1
    have h2 := ((den_closed (cH H) (KCore.bool true)).interp e e' aT).mp h1
    rw [den_true H, ← tr_dv (t := tb)] at h2
    exact ((hat' aT).mp h2).symm
  have hG : (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e' (e'.evalEvar (tb.ev (evarKey xG))) := by
    rw [hgv]; exact (hat' aT).mpr hTT.symm
  have h1 := TieRuleLhs.lhs_entails hD (fT := fT) (fG := fT) (C := q0.1) (L := Ltext) (L' := LG p) (r := q0.2.2)
    (fun _ hk => hk) hT e' m (fun _ a ha => gamma_sub_text H hD hSig hN h1 hf1 e' hG hp a ha)
  show (TieRuleLhs.itemAt tb fG q0.1 (LG p) q0.2.2).interpret I e' m
  unfold TieRuleLhs.itemAt at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  refine h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
  rcases hmore k hk with hk | rfl
  · exact hg _ (List.mem_map_of_mem hk)
  · show (guardOf tb (.evar _ _)).interpret I e' m
    rw [interp_guard_evar hD]
    have hin : (inhOf (trSort tb (KoreAML.srt "Bool"))).interpret I e' aT' := (interp_inhOf_of hSB').mpr hit'
    rw [hTT] at hin
    show (inhOf (trSort tb (KoreAML.srt "Bool"))).interpret I e' (e'.evalEvar (tb.ev (evarKey xG)))
    rw [hgv]; exact hin

omit [Inhabited M] in
/-- An item with the guard of a variable it does not read, of a sort with an element, gives the
item without that guard. -/
theorem item_drop (hD : DefOK I) {fA fG : List VarKey} {L : Kore.Pattern} {x : Kore.EVar}
    (hmore : ∀ k ∈ fA, k ∈ fG ∨ k = evarKey x)
    (hno : (TieRuleLhs.itemAt tb fG q0.1 L q0.2.2).isFreeEvar (tb.ev (evarKey x)) = false)
    (hin : ∃ a σ, (∀ (e' : Valuation M) b, (trSort tb x.sort).interpret I e' b ↔ b = σ) ∧ Inh I σ a)
    (h : I ⊧ᴵ TieRuleLhs.itemAt tb fA q0.1 L q0.2.2) : I ⊧ᴵ TieRuleLhs.itemAt tb fG q0.1 L q0.2.2 := by
  intro e m
  obtain ⟨a, σ, hS, hia⟩ := hin
  let e' : Valuation M := ⟨Function.update e.evalEvar (tb.ev (evarKey x)) a, e.evalSvar⟩
  rw [← interp_evarAt_svin (a := a) hno m]
  have hgv : e'.evalEvar (tb.ev (evarKey x)) = a := by simp [e']
  have h1 := h e' m
  show (TieRuleLhs.itemAt tb fG q0.1 L q0.2.2).interpret I e' m
  unfold TieRuleLhs.itemAt at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  rw [TieUnion.interp_conjListAll] at hg
  refine h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hφ
  rcases hmore k hk with hk | rfl
  · exact hg _ (List.mem_map_of_mem hk)
  · show (guardOf tb (.evar _ _)).interpret I e' m
    rw [interp_guard_evar hD]
    show (inhOf (trSort tb x.sort)).interpret I e' (e'.evalEvar (tb.ev (evarKey x)))
    rw [hgv]; exact (interp_inhOf_of (hS e')).mpr hia

end

/-- The rule sentence. -/
noncomputable def ruleText : List AxiomDecl := [U.ax154]

/-- The other sentences of the text the statement reads: 135 and 49. -/
noncomputable def ruleAux : List AxiomDecl := [U.ax135, U.ax49]

/-- The item of the text's signature the statement reads, which `ΓSig` does not hold: Int has an
element (G-nonempty of the declaration `hooked-sort SortInt{}`). -/
def ruleSigAux : List Item := [nonemptyItem ⟨"SortInt", [], true⟩]

deriving instance DecidableEq for KoreAML.SortDecl

theorem intDecl_mem : (⟨"SortInt", [], true⟩ : SortDecl) ∈ kore.sortDecls := by decide +kernel

/-- Each item of `ruleSigAux` is an item of the signature of the text's theory. -/
theorem ruleSigAux_text : ∀ it ∈ ruleSigAux, it ∈ (Theory.ofDefinition kore).signature := by
  intro it hit
  rw [List.mem_singleton.mp hit]
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, intDecl_mem, rfl⟩)))))

/-- **W1 for the rule sentence, and the converse for `ruleItems`**, from the text: each of Γ's two
rule items is a consequence of the sentence 154 with sentences 135 and 49, Int's G-nonempty item
and the signature, for every H. No item of `ΓDomains` is among the premises. The first rule's item
does not read Y, which the sentence's item guards: Int's G-nonempty item gives Y an element
(`item_drop`). -/
theorem rule_from_text_aux (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText,
    TiePair.Texts ((trS ad).pat :: (ruleAux.map (fun a => (trS a).pat) ++ ruleSigAux.map (·.pat))) ∪ ΓSig (cH H) ⊧ it.pat := by
  intro it hit
  refine ⟨U.ax154, List.mem_singleton_self _, ?_⟩
  intro M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2 := by
    rw [← text_item]; exact hI _ (Or.inl (Or.inl (List.mem_cons_self ..)))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have h1 : I ⊧ᴵ (trS U.ax135).pat := hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have hf1 : I ⊧ᴵ (trS U.ax49).pat :=
    hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hN : I ⊧ᴵ (nonemptyItem ⟨"SortInt", [], true⟩).pat :=
    hI _ (Or.inl (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
  rcases List.mem_cons.mp hit with rfl | hit
  · rw [gamma_item0]
    haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
    obtain ⟨σI, hσI1, -⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
    rw [int_name] at hσI1
    obtain ⟨n, hn⟩ := nonempty_of hD hN (e := ⟨fun _ => default, fun _ _ => False⟩)
    exact item_drop hD free_moreY item0_noY
      ⟨n, σI, fun e' b => by show (trSort tb (KoreAML.srt "Int")).interpret I e' b ↔ _; rw [trSort_srt]; exact hσI1 b,
        (interp_inhOf_of (S := sym (.sort "SortInt")) hσI1).mp hn⟩
      (item_of_text H hD hSig hN h1 hf1 hT (Or.inl rfl) free_more0 item0_noG)
  · rw [List.mem_singleton.mp hit, gamma_item1]
    exact item_of_text H hD hSig hN h1 hf1 hT (Or.inr rfl) free_more1 item1_noG

/-! ## The converse at values -/

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
include hI

omit [Inhabited M] in
/-- **Γ's two rule items**, at the one table. -/
theorem gamma_items : (I ⊧ᴵ TieRuleLhs.itemAt tb f0 q0.1 (LG atomA) q0.2.2) ∧
    (I ⊧ᴵ TieRuleLhs.itemAt tb f1 q0.1 (LG atomB) q0.2.2) := by
  have hm0 : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_cons_self ..
  have hm1 : trAxiom [] [] ⟨0, "kernel", ⟨[], p1, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have h0 := sat_rules hI (Or.inl ⟨_, hm0, rfl⟩)
  have h1 := sat_rules hI (Or.inl ⟨_, hm1, rfl⟩)
  rw [gamma_item0] at h0
  rw [gamma_item1] at h1
  exact ⟨h0, h1⟩

/-- **At values of the rest of the K cell and of the counter cell, an element of the text's left
side at which the disjunct `p` is exactly `true` is one of the left side of `p`'s rule**: Γ's
`requires` `p = true` holds, and `⌈r⌉` is all of the configuration sort, the right side denoting
the element of the value `<generatedTop>(<k>(done ~> v1), v2)`. -/
theorem text_sub_gamma (e : Valuation M) {v1 v2 : GroundTerm} (h1 : c.sortOf v1 = some Srt.k) (h2 : c.sortOf v2 = some 19)
    (hK : (den (cH H) v1).interpret I e (e.evalEvar (tb.ev (evarKey xK))))
    (hC : (den (cH H) v2).interpret I e (e.evalEvar (tb.ev (evarKey xC))))
    {p : Kore.Pattern}
    (hp : ∀ m, (tr ⟨tb, []⟩ p).interpret I e m ↔ (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e m)
    (a : M) (h : (tr ⟨tb, []⟩ Ltext).interpret I e a) : (tr ⟨tb, []⟩ (LG p)).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  have hsK : (cH H).sortOf v1 = some Srt.k := by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact h1
  have hsC : (cH H).sortOf v2 = some 19 := by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact h2
  obtain ⟨σC, hσC1, hσC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσC1
  have hSC : ∀ b, (trSort tb q0.1).interpret I e b ↔ b = σC := by
    rw [C_eq, trSort_srt]; exact hσC1
  obtain ⟨σB, aF, aT, hSB, hσB, haf, hat, hne, hif, hit⟩ :=
    TieReqBool.boolTwo hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H) tb e
  have hTe : ∀ (p q : Kore.Pattern), tr ⟨tb, []⟩ (.equals (KoreAML.srt "Bool") q0.1 p q) =
      sEquals (trSort tb (KoreAML.srt "Bool")) (trSort tb q0.1) (tr ⟨tb, []⟩ p) (tr ⟨tb, []⟩ q) := fun p q => by rw [tr]
  unfold Ltext at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have hterm := h _ (List.mem_cons_self ..)
  have heqT := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold eqT at heqT
  rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2] at heqT
  have haC : Inh I σC a := heqT.1
  unfold LG
  rw [interp_and (List.cons_ne_nil _ _)]
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hterm
  rcases List.mem_cons.mp hq with rfl | hq
  · unfold eqT
    rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2]
    exact ⟨haC, fun x _ => hp x⟩
  rw [List.mem_singleton.mp hq]
  · -- `⌈r⌉`: the right side denotes the element of a value of the configuration sort
    have hyH : (cH H).sortOf (yOf v1 v2) = some topCellSort := by
      rw [Semantics.sortOf_withHooks _ _ noRaw]; exact y_sort h1 h2
    obtain ⟨a1, ha1, hin⟩ := den_single hI hyH e
    rw [top_name] at hin
    have hρ : ∀ y q, ρK (v1.kore (cH H)) (v2.kore (cH H)) y = some q → ∀ m, (tr ⟨tb, []⟩ q).interpret I e m ↔
        m = e.evalEvar (tb.ev (evarKey y)) := by
      intro y q hy m
      unfold ρK at hy
      split at hy
      · next hyK =>
        cases hy; subst hyK
        rw [tr_ground_den]
        obtain ⟨a0, ha0, -⟩ := den_single hI hsK e
        rw [ha0 m, (ha0 _).mp hK]
      · split at hy
        · next hyC =>
          cases hy; subst hyC
          rw [tr_ground_den]
          obtain ⟨a0, ha0, -⟩ := den_single hI hsC e
          rw [ha0 m, (ha0 _).mp hC]
        · cases hy
    have hr0 : ∀ b, (tr ⟨tb, []⟩ (rForm (.var (.evar xK)) (.var (.evar xC)))).interpret I e b ↔ b = a1 := by
      intro b
      rw [← TieReqBool.substAt_iff hρ, congrFun (congrFun rForm_subst (v1.kore (cH H))) (v2.kore (cH H)),
        ← congrFun (congrFun (congrFun y_kore H) v1) v2, tr_ground_den]
      exact ha1 b
    have hsC' : (trSort tb q0.1).isFreeEvar topVar = false := by rw [C_eq, trSort_srt]; rfl
    have hr : ∀ b, (tr ⟨tb, []⟩ q0.2.2).interpret I e b ↔ b = a1 := by
      intro b
      rw [r_eq, tr_and2, interp_sAnd, hr0]
      have hT : tr ⟨tb, []⟩ (.top q0.1) = sTop (trSort tb q0.1) := by rw [tr]
      rw [hT, interp_sTop hD hsC']
      constructor
      · exact fun h => h.1
      · intro h; subst h
        exact ⟨rfl, by rw [C_eq, trSort_srt]; exact hin⟩
    have hTc : tr ⟨tb, []⟩ (.ceil q0.1 q0.1 q0.2.2) =
        sCeil (trSort tb q0.1) (trSort tb q0.1) (tr ⟨tb, []⟩ q0.2.2) := by rw [tr]
    rw [hTc, interp_sCeil hD hc hSC hSC hσC2 hσC2 (fun b hb => by
      rw [(hr b).mp hb]; exact (interp_inhOf_of (S := sortP "GeneratedTopCell") hσC1).mp hin) a]
    exact ⟨⟨a1, (hr a1).mpr rfl⟩, haC⟩

end

/-- **The rule sentence 154 is entailed at values** (`EntailsAtValues`), for every H: at values of
X and Y each disjunct is exactly `true` or does not hold `true` (`atom_dich`); where the
first is `true` the sentence's left side is in the left side of the first rule's item, else in
the second's, where it holds an element at all (`text_sub_gamma`), and that item gives the
sentence. -/
theorem rule154_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax154 (trS U.ax154).pat := by
  intro M _ I hI e hat m
  have hD := defOK hI
  rw [text_item]
  obtain ⟨⟨iX, eX⟩, ⟨iK, eK⟩, ⟨iC, eC⟩, ⟨iY, eY⟩⟩ := idx
  obtain ⟨v0, S0, hS0, hv0, hd0⟩ := hat _ _ iX
  obtain ⟨v1, S1, hS1, hv1, hd1⟩ := hat _ _ iK
  obtain ⟨v2, S2, hS2, hv2, hd2⟩ := hat _ _ iC
  obtain ⟨v3, S3, hS3, hv3, hd3⟩ := hat _ _ iY
  rw [eX] at hd0; rw [eK] at hd1; rw [eC] at hd2; rw [eY] at hd3
  have := int_of_name S3 hS3; subst this
  have := int_of_name S0 hS0; subst this
  have := k_of_name S1 hS1; subst this
  have := cnt_of_name S2 hS2; subst this
  have hv1' := hv1
  have hv2' := hv2
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hv1' hv2'
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  obtain ⟨σC, hσC1, hσC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσC1
  have hSC : ∀ b, (trSort tb q0.1).interpret I e b ↔ b = σC := by
    rw [C_eq, trSort_srt]; exact hσC1
  obtain ⟨σB, aF, aT, hSB, hσB, haf, hat', hne, hif, hit⟩ :=
    TieReqBool.boolTwo hD hSig hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H) tb e
  have hT : ∀ m, (den (cH H) (KCore.bool true)).interpret I e m ↔ m = aT := fun m => by
    rw [den_true H, ← tr_dv (t := tb)]; exact hat' m
  have hF : ¬ (den (cH H) (KCore.bool false)).interpret I e aT := fun h => by
    rw [den_false H, ← tr_dv (t := tb)] at h; exact hne ((haf aT).mp h).symm
  have hTe : ∀ (p q : Kore.Pattern), tr ⟨tb, []⟩ (.equals (KoreAML.srt "Bool") q0.1 p q) =
      sEquals (trSort tb (KoreAML.srt "Bool")) (trSort tb q0.1) (tr ⟨tb, []⟩ p) (tr ⟨tb, []⟩ q) := fun p q => by rw [tr]
  -- an element of the text's left side: `true` is in one of the disjuncts
  have hor : ∀ a, (tr ⟨tb, []⟩ Ltext).interpret I e a →
      (tr ⟨tb, []⟩ atomA).interpret I e aT ∨ (tr ⟨tb, []⟩ atomB).interpret I e aT := by
    intro a ha
    unfold Ltext at ha
    rw [interp_and (List.cons_ne_nil _ _)] at ha
    have heq := ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    unfold eqT at heq
    rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2] at heq
    have h1 := (heq.2 aT hit).mpr ((hat' aT).mpr rfl)
    rw [tr_and2, interp_sAnd, Model.tr_or2Stdi, interp_sOr] at h1
    exact h1.1.2
  have hA := atom_dich H hI e (x := xX) (vars := varsX) (t := termA) (pat := atomA) rfl rfl
    (congrFun atomA_kore_all H) (atomA_srt H) (varsX_key H) hv0 hd0 hT hF
  have hB := atom_dich H hI e (x := xY) (vars := varsY) (t := termB) (pat := atomB) rfl rfl
    (congrFun atomB_kore_all H) (atomB_srt H) (varsY_key H) hv3 hd3 hT hF
  obtain ⟨g0, g1⟩ := gamma_items H hI
  rcases hA with hA | hA
  · exact TieRuleLhs.lhs_entails hD free_sub0 g0 e m
      (fun _ a ha => text_sub_gamma H hI e hv1' hv2' hd1 hd2 (fun x => by rw [hA x, hat' x]) a ha)
  · rcases hB with hB | hB
    · exact TieRuleLhs.lhs_entails hD free_sub1 g1 e m
        (fun _ a ha => text_sub_gamma H hI e hv1' hv2' hd1 hd2 (fun x => by rw [hB x, hat' x]) a ha)
    · refine TieReqBool.ruleItem_of_empty hD (fun a ha => ?_) m
      rcases hor a ha with h | h
      · exact hA h
      · exact hB h

/-! ## The facts the deciders leave, and the owed condition -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- The rule 1, `<k> go(X) => done ... </k> requires Y >Int 2`, is the one whose condition is owed:
its `requires` is closed over Y:Int, which the left side does not bind, and Int is not confined.
No clause is owed. -/
theorem owed_rules : c.owedRules = [1] := by decide +kernel
theorem owed_clauses : c.owedClauses = ([] : List (Nat × Nat)) := by decide +kernel

/-- The rule read from the disjunct `Y >Int 2`. -/
noncomputable def ruleY : Rule := c.rules[1]'(by decide +kernel)

theorem ruleY_vars : ruleY.vars = [Srt.int, Srt.k, 19, Srt.int] := rfl
theorem ruleY_req : ruleY.req = some (.app intGt [.var 3, .dv Srt.int (.int 2)]) := rfl
theorem ruleY_pre : ruleY.pre = .top := rfl

/-- Y := 3, the other variables at values of their sorts. -/
def σY3 : Subst := [(0, int 1), (1, .ctor dotk []), (2, .ctor counterLabel [.dv Srt.int (.int 0)]), (3, int 3)]

theorem σY3_sorted (H : HookParams) : (cH H).WellSorted [Srt.int, Srt.k, 19, Srt.int] σY3 := fun j s hs => by
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 1⟩
  | 1, hs => cases hs; exact ⟨_, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel⟩
  | 2, hs => cases hs; exact ⟨_, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel⟩
  | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int 3⟩

theorem gt_syms (H : HookParams) : (cH H).isCtor intGt = false ∧ isHook intGt = true :=
  (by decide +kernel : c.isCtor intGt = false ∧ isHook intGt = true)

/-- `3 >Int 2` is `true`, for every H: the value is `>Int`'s own at integers. -/
theorem reqY3 (H : HookParams) : EvalTerm (cH H) σY3 (.app intGt [.var 3, .dv Srt.int (.int 2)]) (some (bool true)) :=
  .hook (rs := [some (int 3), some (int 2)]) (gt_syms H).1 (gt_syms H).2 (.cons .var (.cons .dv .nil))
    (fun vs hvs => by
      cases (show some [int 3, int 2] = some vs from hvs)
      exact Semantics.hookRes_of_value (by decide +kernel))
    (fun h => nomatch h)

/-- **The rule of the disjunct `Y >Int 2` is `Witnessed`, for every H**, at Y := 3. -/
theorem witnessedH (H : HookParams) : ruleY.Witnessed (cH H) :=
  ⟨σY3, fun i _ s hs => σY3_sorted H i s (by rw [← ruleY_vars]; exact hs),
   fun t ht => by rw [ruleY_req] at ht; cases ht; exact reqY3 H,
   by rw [ruleY_pre]; exact .top⟩

/-- **The owed condition is decided, for every H** (`OpenDecided`): the one owed rule is
`Witnessed`, and no clause is owed. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) := by
  refine ⟨openRules_of_owed fun j hj r hr => ?_,
    openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩
  rw [Semantics.owedRules_withHooks, owed_rules] at hj
  cases List.mem_singleton.mp hj
  cases (show some ruleY = some r from (rfl : c.rules[1]? = some ruleY).symm.trans hr)
  exact Or.inl (witnessedH H)

/-- The facts the deciders leave, for every H: none is named. -/
theorem factsH (H : HookParams) : FnFacts (cH H) callOrder [] := by
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_, fun p hp => ?_, openLaws_of_plain noRaw⟩
  · rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Semantics.totalObligationsRP_withHooks _ H _ _, total_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Det.Semantics.agreeObligationsI_withHooks, agree_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Det.Semantics.matchObligationsL_withHooks, match_named] at hp
    exact absurd hp List.not_mem_nil

theorem obl (H : HookParams) : FnObligations (cH H) callOrder [] := (factsH H).obligations (openDecidedH H)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl H)

/-- **`Γc` with the step's closure has a model, for every H**: a rule has a variable its left
side does not bind (`readsConfined`), so the theory is Γ with `boolClosed`. -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

end KCore.CondBoolReqOrUnheld

#check @KCore.CondBoolReqOrUnheld.text_item
#check @KCore.CondBoolReqOrUnheld.gamma_item0
#check @KCore.CondBoolReqOrUnheld.gamma_item1
#check @KCore.CondBoolReqOrUnheld.atom_dich
#check @KCore.CondBoolReqOrUnheld.gamma_sub_text
#check @KCore.CondBoolReqOrUnheld.item_of_text
#check @KCore.CondBoolReqOrUnheld.item_drop
#check @KCore.CondBoolReqOrUnheld.text_sub_gamma
#print axioms KCore.CondBoolReqOrUnheld.sents_true
#print axioms KCore.CondBoolReqOrUnheld.true_one
#print axioms KCore.CondBoolReqOrUnheld.ruleSigAux_text
#print axioms KCore.CondBoolReqOrUnheld.rule_from_text_aux
#print axioms KCore.CondBoolReqOrUnheld.rule154_at_values
#print axioms KCore.CondBoolReqOrUnheld.witnessedH
#print axioms KCore.CondBoolReqOrUnheld.openDecidedH
#print axioms KCore.CondBoolReqOrUnheld.fnHypH
#print axioms KCore.CondBoolReqOrUnheld.consistent
