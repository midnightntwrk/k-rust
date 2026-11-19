/-
  The rule sentence of construct fixture e3-ml-req-and against the reading `andAtBool`:
  `rule <k> go(X) => done ... </k> requires X >Int 0 #And X <Int 5`. The text is
  `f2-examples/e3-ml-req-and.kompile.kore`, the one test/TieE3MlReqAnd.lean ties sentence by
  sentence with the rule sentence 157 in its `uncovered`; this file holds that sentence's theorems.
  Run from the package root: `lake env lean -j1 test/CondBoolReqAnd.lean`. Every statement is on
  the literals `kore` and `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  The sentence's `requires` is `\equals{SortBool{}, C}(\and{SortBool{}}(X >Int 0, X <Int 5), true)`,
  the intersection of the two conjuncts equated with `true`. Γ's item reads it conjunct by
  conjunct: its `requires` is `X >Int 0 = true` and its `pre` the conjunct `X <Int 5 = true`.

  - `text_item`, `gamma_item0` (kernel): the sentence and Γ's item are the items of
    `\rewrites{C}(L, r)` at one variable table with one right side, the sentence's left side
    `Ltext` and Γ's `LG` (`left0_eq`).
  - W1, `rule_from_text`: Γ's item is a consequence of the sentence with the signature, at every
    valuation: where each conjunct equals `true`, so does their intersection (`gamma_sub_text`),
    with no premise on the conjuncts.
  - The converse at values, `rule157_at_values` (`EntailsAtValues`): at a value of X each conjunct
    denotes the element of `true`, the element of `false` or nothing (`atom_dich`, from the
    graphs of `>Int` and `<Int` in `ΓDomains`), so where the intersection is `{true}` each conjunct
    is `{true}` (`text_sub_gamma`), the right side being defined at values. At an element of Int
    that is no value a conjunct may hold `true` and another element, and the intersection be
    `{true}` where the conjunct is not: the converse is stated at values.
  - `consistent` for every H.

  The expectations (C7 form (a), through the reading), from `Pre H` (the function equations as
  written, Γ's rule item, the families; it has a model, `pre_model`): `and_both`: `go(1)` steps to
  `done`; `and_second_false`: `go(7)` has no successor (the conjunct read into `pre` is `false`);
  `and_first_false`: `go(0)` has no successor (with the step's closure). The steps are decided by
  the executable step (`CExec.successorsN`), which evaluates `pre`, under `execReady`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.CondBoolReqAnd

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-req-and.kompile.kore"
definition_of defn from "f2-examples/e3-ml-req-and.kompile.kore"
user_axioms U from "f2-examples/e3-ml-req-and.kompile.kore" module "E3-ML-REQ-AND"

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

/-! ## The function equations (the premises of the expectations) -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-! ## The rule sentence 157 and Γ's rule item -/

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0

/-- Its parts `\rewrites{C}(L', r)`. -/
noncomputable def q0 : Kore.KSort × Kore.Pattern × Kore.Pattern :=
  (TieRuleLhs.rwParts p0).getD (KoreAML.R, .top KoreAML.R, .top KoreAML.R)

kernel_rfl q0_eq : TieRuleLhs.rwParts p0 = some q0

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl

theorem names : c.symName 383 = "Lbl'-LT-'k'-GT-'" ∧ c.symName 385 = "Lbldone" ∧ c.symName 386 = "Lblgo" ∧
    c.sortName 32 = "Exp" ∧ c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" ∧ c.symName intLt = "Lbl'Unds-LT-'Int'Unds'" := by
  decide +kernel

/-- Γ's variables: X, the rest of the K cell, the counter cell. -/
def xX : Kore.EVar := KoreAML.evar "VarV0" (KoreAML.srt "Int")
def xK : Kore.EVar := KoreAML.evar "VarV1" (KoreAML.srt "K")
def xC : Kore.EVar := KoreAML.evar "VarV2" (KoreAML.srt "GeneratedCounterCell")

/-- The two conjuncts: `X >Int 0` and `X <Int 5`. -/
def atomA : Kore.Pattern := .app ⟨⟨"Lbl'Unds-GT-'Int'Unds'"⟩⟩ [] [.var (.evar xX), .dv (KoreAML.srt "Int") "0"]
def atomB : Kore.Pattern := .app ⟨⟨"Lbl'Unds-LT-'Int'Unds'"⟩⟩ [] [.var (.evar xX), .dv (KoreAML.srt "Int") "5"]

/-- The left side's term. -/
noncomputable def hd : Kore.Pattern := TieRuleLhs.andHead q0.2.1

/-- `\equals{SortBool{}, C}(p, true)`. -/
noncomputable def eqT (p : Kore.Pattern) : Kore.Pattern :=
  .equals (KoreAML.srt "Bool") q0.1 p (.dv (KoreAML.srt "Bool") "true")

/-- Γ's left side: the term, the `requires` `A = true`, the `pre` `B = true`, and `⌈r⌉`. -/
noncomputable def LG : Kore.Pattern := .and q0.1 [hd, eqT atomA, eqT atomB, .ceil q0.1 q0.1 q0.2.2]

kernel_rfl left0_eq : q0.2.1 = LG

/-- The left side as the text writes it: the term, and the `requires` `\and{SortBool{}}(A, B)`
equated with `true`. -/
noncomputable def Ltext : Kore.Pattern :=
  .and q0.1 [hd, eqT (.and (KoreAML.srt "Bool") [atomA, atomB])]

/-- The one variable table: Γ's axiom's. -/
noncomputable def tb : VarTable := tableOf [] p0
noncomputable def fT : List VarKey := (freeOf [] (.rewrites q0.1 Ltext q0.2.2)).eraseDups
noncomputable def f0 : List VarKey := (freeOf [] p0).eraseDups

/-- **The rule sentence is the item of `\rewrites{C}(Ltext, r)`** (kernel). -/
theorem text_item : (trS U.ax157).pat = TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2 := by
  have h : TiePair.renSeq (TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2) [] = some (trS U.ax157).pat := by
    decide +kernel
  simp only [TiePair.renSeq, Option.some.injEq] at h
  exact h.symm

/-- **Γ's rule item is the item of `\rewrites{C}(LG, r)` at the same table** (kernel). -/
theorem gamma_item0 : (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat = TieRuleLhs.itemAt tb f0 q0.1 LG q0.2.2 := by
  decide +kernel

/-- Γ's free variables are the sentence's. -/
theorem free_sub0 : ∀ k ∈ f0, k ∈ fT := by decide +kernel
theorem free_subT : ∀ k ∈ fT, k ∈ f0 := by decide +kernel

/-- The sentence's three variables are free in it and have the table's indices. -/
theorem idx :
    (KoreAML.VarKey.evar "VarX" (KoreAML.srt "Int") ∈ (freeOf [] U.ax157.ax.pattern).eraseDups ∧
      (tableOf U.ax157.ax.sortVars U.ax157.ax.pattern).ev (.evar "VarX" (KoreAML.srt "Int")) = tb.ev (evarKey xX)) ∧
    (KoreAML.VarKey.evar "Var'Unds'DotVar1" (KoreAML.srt "K") ∈ (freeOf [] U.ax157.ax.pattern).eraseDups ∧
      (tableOf U.ax157.ax.sortVars U.ax157.ax.pattern).ev (.evar "Var'Unds'DotVar1" (KoreAML.srt "K")) = tb.ev (evarKey xK)) ∧
    (KoreAML.VarKey.evar "Var'Unds'DotVar0" (KoreAML.srt "GeneratedCounterCell") ∈ (freeOf [] U.ax157.ax.pattern).eraseDups ∧
      (tableOf U.ax157.ax.sortVars U.ax157.ax.pattern).ev (.evar "Var'Unds'DotVar0" (KoreAML.srt "GeneratedCounterCell")) =
        tb.ev (evarKey xC)) := by decide +kernel

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

/-! ## The conjuncts as library terms -/

/-- `V >Int 0` and `V <Int 5` over one variable. -/
def termA : Term := .app intGt [.var 0, .dv Srt.int (.int 0)]
def termB : Term := .app intLt [.var 0, .dv Srt.int (.int 5)]
def varsX : LibEv.Vars := [("VarV0", Srt.int)]

theorem atomA_kore_all : (fun H : HookParams => LibEv.kore (cH H) varsX termA) = fun _ => atomA := by kernel_rfl
theorem atomB_kore_all : (fun H : HookParams => LibEv.kore (cH H) varsX termB) = fun _ => atomB := by kernel_rfl
theorem atomA_srt (H : HookParams) : LibEv.srt? (cH H) varsX termA = some Srt.bool := by
  simp only [termA, LibEv.srt?, LibEv.srts?, Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel
theorem atomB_srt (H : HookParams) : LibEv.srt? (cH H) varsX termB = some Srt.bool := by
  simp only [termB, LibEv.srt?, LibEv.srts?, Semantics.sortOf_withHooks _ _ noRaw]
  decide +kernel
theorem varsX_key (H : HookParams) : LibEv.vkey (cH H) varsX 0 = evarKey xX := by
  show LibEv.vkey c varsX 0 = _; decide +kernel

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A conjunct at a value of its variable denotes the element of `true` alone, or does not
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

/-! ## W1 -/

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Every element of Γ's left side is one of the text's left side**, at every valuation: where
each conjunct holds, of the elements of Bool, exactly `true`, so does their intersection. -/
theorem gamma_sub_text (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (a : M)
    (h : (tr ⟨tb, []⟩ LG).interpret I e a) : (tr ⟨tb, []⟩ Ltext).interpret I e a := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  obtain ⟨σC, hσC1, hσC2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσC1
  have hSC : ∀ b, (trSort tb q0.1).interpret I e b ↔ b = σC := by
    rw [C_eq, trSort_srt]; exact hσC1
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered (c := cH H))
  rw [sortName_bool] at hσB1
  have hSB : ∀ b, (trSort tb (KoreAML.srt "Bool")).interpret I e b ↔ b = σB := by
    rw [trSort_srt]; exact hσB1
  have hTe : ∀ (p q : Kore.Pattern), tr ⟨tb, []⟩ (.equals (KoreAML.srt "Bool") q0.1 p q) =
      sEquals (trSort tb (KoreAML.srt "Bool")) (trSort tb q0.1) (tr ⟨tb, []⟩ p) (tr ⟨tb, []⟩ q) := fun p q => by rw [tr]
  unfold LG at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have hterm := h _ (List.mem_cons_self ..)
  have heqA := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have heqB := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  unfold eqT at heqA heqB
  rw [hTe, interp_sEquals hD hc hSB hSC hσB2 hσC2] at heqA heqB
  unfold Ltext
  rw [interp_and (List.cons_ne_nil _ _)]
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hterm
  rw [List.mem_singleton.mp hq]
  unfold eqT
  rw [hTe, interp_sEquals hD hc hSB hSC hσB2 hσC2]
  refine ⟨heqA.1, fun x hx => ?_⟩
  rw [tr_and2, interp_sAnd]
  exact ⟨fun h' => (heqA.2 x hx).mp h'.1, fun h' => ⟨(heqA.2 x hx).mpr h', (heqB.2 x hx).mpr h'⟩⟩

end

/-- **W1 for the rule sentence, and the converse for `ruleItems`**: Γ's rule item is a consequence
of the sentence 157 with the signature, for every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax157).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq, List.mem_singleton] at hit
  subst hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ TieRuleLhs.itemAt tb fT q0.1 Ltext q0.2.2 := by
    rw [← text_item]; exact hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  rw [gamma_item0]
  intro e m
  exact TieRuleLhs.lhs_entails hD free_subT hT e m (fun _ a ha => gamma_sub_text H hD hSig e a ha)

/-! ## The converse at values -/

section
variable (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
include hI

omit [Inhabited M] in
/-- **Γ's rule item**, at the one table. -/
theorem gamma_items : I ⊧ᴵ TieRuleLhs.itemAt tb f0 q0.1 LG q0.2.2 := by
  have hm0 : trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩ ∈ ruleItems (cH H) := by
    rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _
  have h0 := sat_rules hI (Or.inl ⟨_, hm0, rfl⟩)
  rw [gamma_item0] at h0
  exact h0

/-- **At values of the rest of the K cell and of the counter cell, an element of the text's left
side at which each conjunct is exactly `true` is one of Γ's left side**: Γ's `requires` and its
`pre` hold, and `⌈r⌉` is all of the configuration sort, the right side denoting the element of the
value `<generatedTop>(<k>(done ~> v1), v2)`. -/
theorem text_sub_gamma (e : Valuation M) {v1 v2 : GroundTerm} (h1 : c.sortOf v1 = some Srt.k) (h2 : c.sortOf v2 = some 19)
    (hK : (den (cH H) v1).interpret I e (e.evalEvar (tb.ev (evarKey xK))))
    (hC : (den (cH H) v2).interpret I e (e.evalEvar (tb.ev (evarKey xC))))
    (hpA : ∀ m, (tr ⟨tb, []⟩ atomA).interpret I e m ↔ (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e m)
    (hpB : ∀ m, (tr ⟨tb, []⟩ atomB).interpret I e m ↔ (tr ⟨tb, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret I e m)
    (a : M) (h : (tr ⟨tb, []⟩ Ltext).interpret I e a) : (tr ⟨tb, []⟩ LG).interpret I e a := by
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
    exact ⟨haC, fun x _ => hpA x⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · unfold eqT
    rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2]
    exact ⟨haC, fun x _ => hpB x⟩
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

/-- **The rule sentence 157 is entailed at values** (`EntailsAtValues`, the reading's direction),
for every H: at a value of X each conjunct is exactly `true` or does not hold `true`
(`atom_dich`); where both are `true` the sentence's left side is in Γ's (`text_sub_gamma`) and Γ's
item gives the sentence; otherwise the sentence's left side holds nothing. -/
theorem rule157_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat := by
  intro M _ I hI e hat m
  have hD := defOK hI
  rw [text_item]
  obtain ⟨⟨iX, eX⟩, ⟨iK, eK⟩, ⟨iC, eC⟩⟩ := idx
  obtain ⟨v0, S0, hS0, hv0, hd0⟩ := hat _ _ iX
  obtain ⟨v1, S1, hS1, hv1, hd1⟩ := hat _ _ iK
  obtain ⟨v2, S2, hS2, hv2, hd2⟩ := hat _ _ iC
  rw [eX] at hd0; rw [eK] at hd1; rw [eC] at hd2
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
  -- an element of the text's left side: `true` is in both conjuncts
  have hand : ∀ a, (tr ⟨tb, []⟩ Ltext).interpret I e a →
      (tr ⟨tb, []⟩ atomA).interpret I e aT ∧ (tr ⟨tb, []⟩ atomB).interpret I e aT := by
    intro a ha
    unfold Ltext at ha
    rw [interp_and (List.cons_ne_nil _ _)] at ha
    have heq := ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    unfold eqT at heq
    rw [hTe, interp_sEquals hD hc hSB hSC hσB hσC2] at heq
    have h1 := (heq.2 aT hit).mpr ((hat' aT).mpr rfl)
    rw [tr_and2, interp_sAnd] at h1
    exact h1
  have hA := atom_dich H hI e (x := xX) (vars := varsX) (t := termA) (pat := atomA) rfl rfl
    (congrFun atomA_kore_all H) (atomA_srt H) (varsX_key H) hv0 hd0 hT hF
  have hB := atom_dich H hI e (x := xX) (vars := varsX) (t := termB) (pat := atomB) rfl rfl
    (congrFun atomB_kore_all H) (atomB_srt H) (varsX_key H) hv0 hd0 hT hF
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · exact TieRuleLhs.lhs_entails hD free_sub0 (gamma_items H hI) e m
        (fun _ a ha => text_sub_gamma H hI e hv1' hv2' hd1 hd2 (fun x => by rw [hA x, hat' x])
          (fun x => by rw [hB x, hat' x]) a ha)
    · exact TieReqBool.ruleItem_of_empty hD (fun a ha => hB (hand a ha).2) m
  · exact TieReqBool.ruleItem_of_empty hD (fun a ha => hA (hand a ha).1) m

/-! ## The facts the deciders leave -/

/-- The executable step is ready (`execReady`): it evaluates the rule's `pre`. -/
theorem hready : CExec.execReady c = true := by decide +kernel
theorem hreadyH (H : HookParams) : CExec.execReady (cH H) = true := (CExec.execReady_withHooks c H).trans hready
theorem noFns : c.fns = [] := by decide +kernel
/-- The semantics has no function of its own: `Eval` has one result at most, for every H. -/
theorem fnDetH (H : HookParams) : FnDet (cH H) :=
  fnDet_of_agree (fun _ h => by rw [show (cH H).fns = c.fns from rfl, noFns] at h; cases h)
    (fun _ h => by rw [show (cH H).fns = c.fns from rfl, noFns] at h; cases h)

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

/-- The rule's `pre` holds no binder: the semantics reads no confined sort. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem hrcH (H : HookParams) : (cH H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c

/-- None named; `OpenDecided` as the semantics reads no confined sort (the rule has a `pre`, so the
semantics is not `plain`), `OpenLaws` as no parameter is raw. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] := by
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 := (Semantics.totalObligationsRP_withHooks _ H callOrder []).trans total_named
  have h3 := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun p hp => ?_,
    openDecided_of_readsConfined (hrcH H), openLaws_of_plain fun k hk => noRaw k hk⟩
  · rw [h1] at hf; exact absurd hf List.not_mem_nil
  · rw [h2] at hf; exact absurd hf List.not_mem_nil
  · rw [h3] at hf; exact absurd hf List.not_mem_nil
  · rw [h4] at hp; exact absurd hp List.not_mem_nil

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectations (C7 form (a)) -/

/-- **The premises of the derivations**: every function equation as written, Γ's rule item (the
reading of the rule sentence 157, a consequence of the sentence with `ΓSig` by `rule_from_text`,
which entails the sentence at values by `rule157_at_values`), and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

/-- The configuration with `it` of sort Exp in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor 383 [.ctor kseq [.inj 32 Srt.kitem it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

def Go1 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 1)]), by decide +kernel⟩
def Go7 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 7)]), by decide +kernel⟩
def Go0 : Config c := ⟨cfg (.ctor 386 [.dv Srt.int (.int 0)]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor 385 []), by decide +kernel⟩

-- The executable step at `go(1)`, `go(7)` and `go(0)` reads no interpretation of the parameters:
-- `>Int` and `<Int` have their values at integers.
kernel_rfl go1_withHooks : ∀ H : HookParams,
  CExec.successorsN (cH H) 50 Go1.val = CExec.successorsN c 50 Go1.val
kernel_rfl go7_withHooks : ∀ H : HookParams,
  CExec.successorsN (cH H) 50 Go7.val = CExec.successorsN c 50 Go7.val
kernel_rfl go7_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (cH H) 50 Go7.val = CExec.outOfFuel c 50 Go7.val
kernel_rfl go0_withHooks : ∀ H : HookParams,
  CExec.successorsN (cH H) 50 Go0.val = CExec.successorsN c 50 Go0.val
kernel_rfl go0_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (cH H) 50 Go0.val = CExec.outOfFuel c 50 Go0.val

/-- `go(1)` steps to `done`, for every H: the executable step lists it. -/
theorem step_go1 (H : HookParams) : Step (cH H) (TieRuleLhs.cfgH noRaw Go1 H) (TieRuleLhs.cfgH noRaw Done H) := by
  have hy : Done.val ∈ CExec.successorsN (cH H) 50 Go1.val := by rw [go1_withHooks]; decide +kernel
  obtain ⟨_, hs⟩ := CExec.successorsN_step_ready (hreadyH H) (x := TieRuleLhs.cfgH noRaw Go1 H) hy
  exact hs

/-- **`go(1)` steps to `done`, derived from `Pre`**, for every H: `1 >Int 0` and `1 <Int 5`. -/
theorem and_both (H : HookParams) : Pre H ⊧ (den (cH H) Go1.val ⇒ KoreAML.sNext (den (cH H) Done.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (step_go1 H))

/-- **`go(7)` has no successor, derived from `Pre` with the step's closure**, for every H: the
conjunct `7 <Int 5`, read into `pre`, is `false`. -/
theorem and_second_false (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) Go7.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H) (complete_at_step _ (coreOKH H) (hrcH H) (TieRuleLhs.cfgH noRaw Go7 H)
    (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
    fun y hy => absurd hy (CExec.noStep_at (hreadyH H) (fnDetH H) (n := 50) (x := TieRuleLhs.cfgH noRaw Go7 H)
      ((go7_fuel_withHooks H).trans (by decide +kernel)) ((go7_withHooks H).trans (by decide +kernel)) y))

/-- **`go(0)` has no successor, derived from `Pre` with the step's closure**, for every H: the
conjunct `0 >Int 0`, the `requires`, is `false`. -/
theorem and_first_false (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) Go0.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List GroundTerm).map (den (cH H))))) :=
  TiePair.cutStep (shapeH H) (complete_at_step _ (coreOKH H) (hrcH H) (TieRuleLhs.cfgH noRaw Go0 H)
    (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) _) []
    fun y hy => absurd hy (CExec.noStep_at (hreadyH H) (fnDetH H) (n := 50) (x := TieRuleLhs.cfgH noRaw Go0 H)
      ((go0_fuel_withHooks H).trans (by decide +kernel)) ((go0_withHooks H).trans (by decide +kernel)) y))

end KCore.CondBoolReqAnd

#check @KCore.CondBoolReqAnd.text_item
#check @KCore.CondBoolReqAnd.gamma_item0
#check @KCore.CondBoolReqAnd.atom_dich
#check @KCore.CondBoolReqAnd.gamma_sub_text
#check @KCore.CondBoolReqAnd.text_sub_gamma
#print axioms KCore.CondBoolReqAnd.rule_from_text
#print axioms KCore.CondBoolReqAnd.rule157_at_values
#print axioms KCore.CondBoolReqAnd.consistent
#print axioms KCore.CondBoolReqAnd.pre_model
#print axioms KCore.CondBoolReqAnd.and_both
#print axioms KCore.CondBoolReqAnd.and_second_false
#print axioms KCore.CondBoolReqAnd.and_first_false
