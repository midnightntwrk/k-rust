/-
  The rule sentence of construct fixture e3-ml-rule-lhs-implies
  (`rule <k> c(a() #Implies b()) => b() ... </k>`, kompiled to
  `c(\implies{Exp}(a(), \and{Exp}(b(), _Gen6))) => _Gen6`, axiom 104 of
  f2-examples/e3-ml-rule-lhs-implies.kompile.kore), which `Parse.parse` reads through the cut
  (`ReadingNote.connectiveCut`): the position holds the rule's variable Z:Exp and
  `pre := (Z ∈ a) → (Z ∈ b ∧ Z ∈ G)`, G the variable `_Gen6`. Run from the package root, after the
  library: `lake env lean -j1 test/TieRuleImplies.lean`.

  - `memOf_implies`: `\implies{C}` of two memberships is the membership in `\implies{S}` of the
    operands (`KoreAML.MemOf`); `implies_inh`: every element of `\implies{S}(t, u)` is in S.
  - `read`: the reader reads the text's rule as `rz`. `left_eq`: Γ's axiom of the rule,
    `prioRuleK c rz`, is `\rewrites(K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉, R)`, q the membership written by `pre`, R
    the right side (`right_eq`), which does not hold Z. `left_text`, `left_tie`: the pattern
    `K[φ] ∧ ⊤`, φ the implication, is the left argument of the text's `\rewrites`.
  - `tie`: `KoreAML.rule_cut_mem` read from right to left: `∃Z:Exp. (K[Z] ∧ ⊤ ∧ q)` is `K[φ] ∧ ⊤`,
    in an interpretation and at a table under the theorem's premises (definedness, the sorts'
    patterns, the sides, φ and the sorts not reading Z, every element of the filled context in the
    outer sort). `left_tie_def`: with the premise `⌈R⌉` of Γ's axiom; `at_rule`: at the rule's own
    Z, an element of Exp, an element of Γ's left side is one of the text's left side and of `⌈R⌉`.
  - `rule_text`: sentence 104 is the item of `\rewrites(K[φ] ∧ ⊤, R)` at the table of Γ's axiom
    (kernel). `left_sub`: in a model of definedness and the signature, where the guards of Γ's
    axiom hold, every element of Γ's left side is one of the text's (q at Z's element makes that
    element one of φ, and a context of applications is monotone). `rule_from_text`: W1, Γ's one
    rule item is a consequence of sentence 104 with the signature, for every H. The converse in
    every model of Γ is not stated here: `tie`'s premises are not discharged.
  - `implies_steps`: for every H, `c(b)` steps to `b` and to `a`, and `c(a)` has no successor. An
    element z of Exp is in `a → (b ∧ G)` exactly where z is not `a` or z is `b` and G: `b` is in it
    at every G, `a` at none.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleImplies

open KCore KCore.Faithful KoreAML ML

def topC : Kore.KSort := srt "GeneratedTopCell"

/-- The context of the `k` cell's first item at the sort X: `<generatedTop>(<k>(kseq(inj{X,
KItem}(·), k)), counter)`. -/
def cellCtx (X : String) (k counter : Kore.Pattern) : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [srt X, srt "KItem"] [] .hole []) [k]) []) [counter]

/-- The `\rewrites` axiom at the place i of the text's last module: its left and right arguments. -/
def rewritesAt (k : Kore.Definition) (i : Nat) : Option (Kore.Pattern × Kore.Pattern) :=
  match k.modules.getLast?.bind (·.sentences[i]?) with
  | some (.axiom a) => match a.pattern with
    | .rewrites _ l r => some (l, r)
    | _ => none
  | _ => none

/-- `∧` of four is `∧` of the first three and the fourth. -/
theorem and4_iff {M : Type} {I : Interpretation KoreAML.Sym M} (ctx : Ctx) (C : Kore.KSort)
    (x y q d : Kore.Pattern) (e : Valuation M) (m : M) :
    (tr ctx (.and C [x, y, q, d])).interpret I e m ↔
      (tr ctx (.and C [x, y, q])).interpret I e m ∧ (tr ctx d).interpret I e m := by
  simp only [tr, trAndList, interp_sAnd, and_assoc]

/-- `\implies{C}` of two memberships is the membership in `\implies{S}` of the operands. -/
theorem memOf_implies {M : Type} {I : Interpretation KoreAML.Sym M} {ctx : Ctx} {e : Valuation M}
    {S C : Kore.KSort} {σ σ' : M} {z : Kore.EVar}
    (hSz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars S))
    (hCz : NoReadCut I (ctx.vars.ev (evarKey z)) (trSort ctx.vars C))
    (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort ctx.vars C).interpret I e a ↔ a = σ') {q₁ q₂ φ₁ φ₂ : Kore.Pattern}
    (h₁ : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q₁ φ₁)
    (h₂ : MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' q₂ φ₂) :
    MemOf I ctx e (ctx.vars.ev (evarKey z)) σ σ' (.implies C q₁ q₂) (.implies S φ₁ φ₂) := by
  intro a ha m
  have hSu : ∀ b, (trSort ctx.vars S).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ :=
    fun b => (hSz e a b).trans (hS b)
  have hCu : ∀ b, (trSort ctx.vars C).interpret I
      ⟨Function.update e.evalEvar (ctx.vars.ev (evarKey z)) a, e.evalSvar⟩ b ↔ b = σ' :=
    fun b => (hCz e a b).trans (hC b)
  simp only [tr]
  rw [interp_sImp, interp_sImp, interp_inhOf_of hSu, interp_inhOf_of hCu, h₁ a ha m, h₂ a ha m]
  exact ⟨fun ⟨hm, h⟩ => ⟨⟨ha, fun h1 => (h ⟨h1, hm⟩).1⟩, hm⟩,
    fun ⟨⟨_, h⟩, hm⟩ => ⟨hm, fun h1 => ⟨h h1.1, hm⟩⟩⟩

/-- Every element of `\implies{S}(t, u)` is in S. -/
theorem implies_inh {M : Type} {I : Interpretation KoreAML.Sym M} {ctx : Ctx} {e : Valuation M}
    {S : Kore.KSort} {σ : M} (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ)
    (t u : Kore.Pattern) (a : M) (h : (tr ctx (.implies S t u)).interpret I e a) : Inh I σ a := by
  simp only [tr] at h
  exact (interp_inhOf_of hS).mp (interp_sImp.mp h).1

kore_term kore from "f2-examples/e3-ml-rule-lhs-implies.kompile.kore"
definition_of defn from "f2-examples/e3-ml-rule-lhs-implies.kompile.kore"
user_axioms U from "f2-examples/e3-ml-rule-lhs-implies.kompile.kore" module "E3-ML-RULE-LHS-IMPLIES"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

example : c.sortName 32 = "Exp" ∧ c.sortName 0 = "K" ∧ c.sortName 19 = "GeneratedCounterCell" ∧
    c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧ c.symName 387 = "Lblc" := by decide +kernel

def cfg (x : Term) : Term := .app 71 [.app 383 [.app 0 [.inj 32 1 x, .var 1]], .var 2]

/-- `c(Z) => G` with `pre := (Z ∈ a) → (Z ∈ b ∧ Z ∈ G)`, Z:Exp the first variable, G:Exp the
fourth. -/
def rz : Rule :=
  { vars := [32, 0, 19, 32], lhs := cfg (.app 387 [.var 0]), req := none, rhs := cfg (.var 3), ens := none,
    prio := 50,
    pre := .implies (.mem 32 (.var 0) (.app 385 []))
      (.and (.mem 32 (.var 0) (.app 386 [])) (.mem 32 (.var 0) (.var 3))) }

/-- The reader reads the text's rule as `rz` (`Parse.parse`, through the cut). -/
theorem read : c.rules = [rz] := rfl

def S : Kore.KSort := srt "Exp"
def z : Kore.EVar := evar "VarV0" S
def a : Kore.Pattern := ap "Lbla" []
def b : Kore.Pattern := ap "Lblb" []
def g : Kore.Pattern := ev "VarV3" S
/-- The connective at the position. -/
def φ : Kore.Pattern := .implies S a (.and S [b, g])
/-- The membership of Z in φ, as `pre` writes it. -/
def q : Kore.Pattern := .implies topC (.in S topC (.var (.evar z)) a)
  (.and topC [.in S topC (.var (.evar z)) b, .in S topC (.var (.evar z)) g])
def E : Kore.Pattern := .top topC
def K : KoreCutCtx := .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [S, srt "KItem"] []
        (.app ⟨⟨"Lblc"⟩⟩ [] [] .hole []) []) [ev "VarV1" (srt "K")]) [])
    [ev "VarV2" (srt "GeneratedCounterCell")]
/-- The rule's right side, `<k> G </k>`. -/
def R : Kore.Pattern := .and topC [cellCtx "Exp" (ev "VarV1" (srt "K")) (ev "VarV2" (srt "GeneratedCounterCell")) |>.fill g, E]

/-- The text's left side: the implication in its position. -/
def left : Kore.Pattern := .and topC [K.fill φ, E]
/-- Γ's left side: `K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉`. -/
def leftG : Kore.Pattern := .and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R]
/-- Γ's axiom of the rule. -/
def pG : Kore.Pattern := .rewrites topC leftG R

theorem right_eq : ruleRight c rz = R := by decide +kernel

/-- Γ's axiom of the rule: `\rewrites(K[Z] ∧ ⊤ ∧ q ∧ ⌈R⌉, R)`. -/
theorem left_eq : prioRuleK c rz = .rewrites topC (.and topC [K.fill (.var (.evar z)), E, q, .ceil topC topC R]) R := by
  decide +kernel

/-- The text's spelling of the canonical names of the rule's variables. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV1" then "Var'Unds'DotVar1" else if n == "VarV2" then "Var'Unds'DotVar0"
  else if n == "VarV3" then "Var'Unds'Gen6" else n

theorem left_text : some (renVars spell (fun n _ => n) left) = (rewritesAt kore 200).map (·.1) := by
  decide +kernel

theorem left_tie (l : Kore.Pattern) (h : (rewritesAt kore 200).map (·.1) = some l) :
    tr ⟨tableOf [] l, []⟩ l = tr ⟨tableOf [] left, []⟩ left := by
  have hl : l = renVars spell (fun n _ => n) left := by
    have := left_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hl]
  exact tr_occurrence_order spell (fun n _ => n) [] [] left (by decide +kernel)

/-- q is the membership of Z's element in φ, at a table without aliases. -/
theorem mem_q {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ') :
    MemOf I ⟨tbl, []⟩ e (tbl.ev (evarKey z)) σ σ' q φ :=
  memOf_implies (ctx := ⟨tbl, []⟩) hSz hCz hS hC
    (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' a)
    (MemOf.and (ctx := ⟨tbl, []⟩)
      (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' b)
      (MemOf.in' (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD hc hσ hσ' g))

/-- **`rule_cut_mem` at the fixture's left side**: `∃Z:Exp. (K[Z] ∧ ⊤ ∧ q)` is the text's left side
`K[a → (b ∧ G)] ∧ ⊤`, under the theorem's premises at a table without aliases. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (.exist topC z (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      (tr ⟨tbl, []⟩ left).interpret I e m :=
  rule_cut_mem hD ⟨tbl, []⟩ K rfl S topC z rfl φ q E e hsides hφ hE hSz hS
    (mem_q hD hc tbl e hSz hCz hS hC hσ hσ')
    (fun x hx => implies_inh (ctx := ⟨tbl, []⟩) hS _ _ x hx) hout m

/-- **Γ's left side, closed by `∃Z`, is the text's left side with `⌈R⌉`**: R does not hold Z. -/
theorem left_tie_def {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hR : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.ceil topC topC R)))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M) :
    (∃ x, Inh I σ x ∧ (tr ⟨tbl, []⟩ leftG).interpret I
        ⟨Function.update e.evalEvar (tbl.ev (evarKey z)) x, e.evalSvar⟩ m) ↔
      (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m := by
  have ht := tie hD hc tbl e hsides hφ hE hSz hCz hS hC hσ hσ' hout m
  have hex : (tr ⟨tbl, []⟩ (.exist topC z (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔
      ∃ x, Inh I σ x ∧ (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q])).interpret I
        ⟨Function.update e.evalEvar (tbl.ev (evarKey z)) x, e.evalSvar⟩ m := by
    show (sExists (tbl.ev (evarKey z)) (trSort tbl S) (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, q]))).interpret I e m ↔ _
    rw [interp_sExists]
    refine exists_congr fun x => and_congr_left' ?_
    rw [interp_member hD, interp_inhOf_of fun b => (hSz e x b).trans (hS b)]
    simp
  unfold leftG
  rw [← ht, hex]
  constructor
  · rintro ⟨x, hx, h4⟩
    rw [and4_iff] at h4
    exact ⟨⟨x, hx, h4.1⟩, (hR e x m).mp h4.2⟩
  · rintro ⟨⟨x, hx, h3⟩, hd⟩
    exact ⟨x, hx, (and4_iff _ _ _ _ _ _ _ _).mpr ⟨h3, (hR e x m).mpr hd⟩⟩

/-- **At the rule's own Z**: where Z's value is an element of Exp, an element of Γ's left side is
one of the text's left side and of `⌈R⌉`. -/
theorem at_rule {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ φ))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hR : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.ceil topC topC R)))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill φ)).interpret I e m → Inh I σ' m) (m : M)
    (hZ : Inh I σ (e.evalEvar (tbl.ev (evarKey z))))
    (h : (tr ⟨tbl, []⟩ leftG).interpret I e m) :
    (tr ⟨tbl, []⟩ left).interpret I e m ∧ (tr ⟨tbl, []⟩ (.ceil topC topC R)).interpret I e m :=
  (left_tie_def hD hc tbl e hsides hφ hE hR hSz hCz hS hC hσ hσ' hout m).mp
    ⟨_, hZ, by
      have hu : Function.update e.evalEvar (tbl.ev (evarKey z)) (e.evalEvar (tbl.ev (evarKey z))) = e.evalEvar := by
        funext y; rw [Function.update_apply]; by_cases hy : y = tbl.ev (evarKey z) <;> simp [hy]
      rw [hu]; exact h⟩

/-! ## W1 for every H: Γ's rule item from sentence 104 and the signature -/

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem pG_eq : prioRuleK c rz = pG := left_eq
theorem pG_parts : TieRuleLhs.rwParts pG = some (topC, leftG, R) := rfl
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], pG, []⟩⟩] := by
  rw [← pG_eq]; kernel_rfl

/-- The free variables of the sentence: G, the rest of the `k` cell, the counter cell. -/
def fT : List VarKey := (freeOf [] (.rewrites topC left R)).eraseDups

/-- **The rule sentence is the item of `\rewrites{C}(K[φ] ∧ ⊤, R)` at the table of Γ's axiom**, G's
index renamed (kernel). -/
theorem rule_text : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] pG) fT topC left R) [(4, 1)] =
    some (trS U.ax104).pat := by decide +kernel
theorem fT_free : fT.all (fun k => (freeOf [] pG).eraseDups.contains k) = true := by decide +kernel
theorem z_free : evarKey z ∈ (freeOf [] pG).eraseDups := by decide +kernel

theorem exp_name (H : HookParams) : (cH H).sortName 32 = "Exp" := (by decide +kernel : c.sortName 32 = "Exp")
theorem exp_numbered (H : HookParams) : (32 : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (32 : Srt) < nRegSorts + c.sortNames.length)
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-- **Γ's left side of the rule is inside the text's**, at a valuation where the guards of Γ's
axiom hold, in a model of definedness and the signature: q holds somewhere, so Z's element is one
of φ, and `K[Z]` is inside `K[φ]`. -/
theorem left_sub (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (hSig : I ⊧ᴵP ΓSig (cH H)) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ (freeOf [] pG).eraseDups, (guardOf (tableOf [] pG) k).interpret I e m) (x : M)
    (h : (tr ⟨tableOf [] pG, []⟩ leftG).interpret I e x) : (tr ⟨tableOf [] pG, []⟩ left).interpret I e x := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σE, hσE1, hσE2⟩ := TieRhs.sortSing_sig hD hSig (exp_numbered H)
  rw [exp_name] at hσE1
  obtain ⟨σ, hσ1, hσ2⟩ := TieRhs.sortSing_sig hD hSig (top_numbered (c := cH H))
  rw [top_name] at hσ1
  have hS : ∀ b, (trSort (tableOf [] pG) S).interpret I e b ↔ b = σE := by unfold S; rw [trSort_srt]; exact hσE1
  have hC : ∀ b, (trSort (tableOf [] pG) topC).interpret I e b ↔ b = σ := by unfold topC; rw [trSort_srt]; exact hσ1
  have hSz : NoReadCut I ((tableOf [] pG).ev (evarKey z)) (trSort (tableOf [] pG) S) := by
    unfold S; rw [trSort_srt]; exact fun _ _ _ => Iff.rfl
  have hCz : NoReadCut I ((tableOf [] pG).ev (evarKey z)) (trSort (tableOf [] pG) topC) := by
    unfold topC; rw [trSort_srt]; exact fun _ _ _ => Iff.rfl
  have hz : Inh I σE (e.evalEvar ((tableOf [] pG).ev (evarKey z))) :=
    (interp_inhOf_of hS).mp ((TieRuleLhs.guard_evarKey hD).mp (hg _ z_free))
  unfold leftG at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have hq := h q (by simp)
  have hu : Function.update e.evalEvar ((tableOf [] pG).ev (evarKey z)) (e.evalEvar ((tableOf [] pG).ev (evarKey z))) =
      e.evalEvar := by
    funext y; rw [Function.update_apply]; by_cases hy : y = (tableOf [] pG).ev (evarKey z) <;> simp [hy]
  have hm := mem_q hD hc (tableOf [] pG) e hSz hCz hS hC hσE2 hσ2 _ hz x
  rw [hu] at hm
  have hφz := (hm.mp hq).1
  unfold left
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · rw [hp]
    refine TieRuleLhs.tr_fill_mono ⟨tableOf [] pG, []⟩ K rfl (p := .var (.evar z)) (q := φ) (fun y hy => ?_) x
      (h _ (List.mem_cons_self ..))
    rw [tr, interp_evar] at hy
    rw [hy]; exact hφz
  · rw [hp]; exact h E (by simp)

/-- **W1 for the rule**: Γ's one rule item is a consequence of sentence 104 with the signature,
for every H. -/
theorem rule_from_text (H : HookParams) :
    ∀ it ∈ ruleItems (cH H), (TiePair.Texts [(trS U.ax104).pat] ∪ ΓSig (cH H)) ⊧ it.pat := by
  intro it hit M _ I hI
  rw [TiePair.ruleItems_withHooks, ruleItems_eq] at hit
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  rw [List.mem_singleton.mp hit]
  exact TieRuleLhs.rule_w1 hD pG_parts rule_text fT_free (hI _ (Or.inl (Or.inl (List.mem_singleton_self _))))
    fun e m hg x hx => left_sub H hD hc hSig e m hg x hx

/-! ## The steps, for every H -/

section Steps
open KCore.Exec KCore.Cert

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def sA : Sym := 385
def sB : Sym := 386
def sC : Sym := 387
def exp : Srt := 32

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _
/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl
theorem r0_lhs : r0.lhs =
    .app topLabel [.app 383 [.app kseq [.inj exp Srt.kitem (.app sC [.var 0]), .var 1]], .var 2] := rfl
theorem r0_rhs : r0.rhs =
    .app topLabel [.app 383 [.app kseq [.inj exp Srt.kitem (.var 3), .var 1]], .var 2] := rfl
/-- The rule as read: `c(Z) => G` with `pre := (Z ∈ a) → (Z ∈ b ∧ Z ∈ G)`. -/
theorem read_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [] ∧ r0.post = .top ∧
    r0.pre = .implies (.mem exp (.var 0) (.app sA []))
      (.and (.mem exp (.var 0) (.app sB [])) (.mem exp (.var 0) (.var 3))) := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor 383 = true ∧ c.isCtor kseq = true ∧
    c.isCtor sA = true ∧ c.isCtor sB = true ∧ c.isCtor sC = true := by decide +kernel
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains 383 = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains sC = false := by decide +kernel
theorem symsH (H : HookParams) : (c.withHooks H).isCtor topLabel = true ∧ (c.withHooks H).isCtor 383 = true ∧
    (c.withHooks H).isCtor kseq = true ∧ (c.withHooks H).isCtor sA = true ∧ (c.withHooks H).isCtor sB = true ∧
    (c.withHooks H).isCtor sC = true := syms_ok

def cfgOf (e : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor 383 [.ctor kseq [.inj exp Srt.kitem e, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]
def CA : Config c := ⟨cfgOf (.ctor sC [.ctor sA []]), by decide +kernel⟩
def CB : Config c := ⟨cfgOf (.ctor sC [.ctor sB []]), by decide +kernel⟩
def A : Config c := ⟨cfgOf (.ctor sA []), by decide +kernel⟩
def B : Config c := ⟨cfgOf (.ctor sB []), by decide +kernel⟩
def σ (z g : GroundTerm) : Subst :=
  [(0, z), (1, .ctor dotk []), (2, .ctor counterLabel [.dv Srt.int (.int 0)]), (3, g)]

theorem holds_implies_inv {c : Semantics} {n : Nat} {σ : Subst} {p p' : Cond} {v : Bool}
    (h : Holds c n σ (.implies p p') v) : ∃ b b', Holds c n σ p b ∧ Holds c n σ p' b' ∧ v = (!b || b') := by
  generalize hq : Cond.implies p p' = x at h
  cases h with
  | implies h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

theorem holds_and_inv {c : Semantics} {n : Nat} {σ : Subst} {p p' : Cond} {v : Bool}
    (h : Holds c n σ (.and p p') v) : ∃ b b', Holds c n σ p b ∧ Holds c n σ p' b' ∧ v = (b && b') := by
  generalize hq : Cond.and p p' = x at h
  cases h with
  | and h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

theorem holds_mem_inv {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {v : Bool}
    (h : Holds c n σ (.mem s t u) v) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ v = (r.isSome && sameResult r r') := by
  generalize hq : Cond.mem s t u = x at h
  cases h with
  | mem h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

theorem evalTerm_const {c : Semantics} {σ : Subst} {f : Sym} {r : Option GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f []) r) : r = some (.ctor f []) := by
  obtain ⟨rs, hrs, rfl⟩ := EvalTerm.ctor_inv hc h
  cases EvalTerms.nil_inv hrs
  rfl

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = decide (v = w) := by
  unfold sameResult
  by_cases h : v = w
  · subst h; simp [cmp_eq_iff]
  · simp [cmp_eq_iff, h]

theorem patVal_ctor2 {c : Semantics} {σ : Subst} {f : Sym} {p q : Term} {v w : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p, q]) (.ctor f [v, w])) : PatVal c σ p v ∧ PatVal c σ q w := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, hs1⟩ := PatVals.cons_inv hs
  cases he1
  obtain ⟨_, _, he2, h2, _⟩ := PatVals.cons_inv hs1
  cases he2
  exact ⟨h1, h2⟩

theorem patVal_ctor1 {c : Semantics} {σ : Subst} {f : Sym} {p : Term} {v : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p]) (.ctor f [v])) : PatVal c σ p v := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, _⟩ := PatVals.cons_inv hs
  cases he1
  exact h1

/-- `pre` under H where Z has the value `a`: false, whatever G is. -/
theorem pre_at_a (H : HookParams) {τ : Subst} (h0 : τ.lookup 0 = some (.ctor sA [])) :
    ¬ Holds (c.withHooks H) r0.vars.length τ r0.pre true := by
  rw [read_shape.2.2.2.2]
  intro h
  obtain ⟨b1, b2, h1, h2, hb⟩ := holds_implies_inv h
  obtain ⟨b3, b4, h3, h4, rfl⟩ := holds_and_inv h2
  obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv h1
  obtain ⟨r₃, r₃', e₃, e₃', rfl⟩ := holds_mem_inv h3
  rw [EvalTerm.var_inv e₁, evalTerm_const (symsH H).2.2.2.1 e₁', EvalTerm.var_inv e₃,
    evalTerm_const (symsH H).2.2.2.2.1 e₃', h0] at hb
  simp only [Option.isSome_some, Bool.true_and, sameResult_some] at hb
  have hne : (GroundTerm.ctor sA [] = .ctor sB []) = False := by simp [sA, sB]
  simp [hne] at hb

/-- A match of the left side under H at `c(z)` gives Z the value z. -/
theorem lookup0 (H : HookParams) {τ : Subst} {z : GroundTerm}
    (hm : PatVal (c.withHooks H) τ r0.lhs (cfgOf (.ctor sC [z]))) : τ.lookup 0 = some z := by
  rw [r0_lhs] at hm
  have h1 := (patVal_ctor2 hooks_ok.1 (symsH H).1 hm).1
  have h2 := patVal_ctor1 hooks_ok.2.1 (symsH H).2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 (symsH H).2.2.1 h2).1
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw (symsH H).2.2.2.2.2
  have he' : GroundTerm.inj exp Srt.kitem (.ctor sC [z]) = .inj exp Srt.kitem (.ctor sC vs) := he
  cases he'
  obtain ⟨_, _, he1, h4, _⟩ := PatVals.cons_inv hs
  cases he1
  exact PatVal.var_inv h4

/-- `c(b)` steps under H to the configuration of g where `pre` is true of `b` and g. -/
theorem step_b (H : HookParams) (g : GroundTerm) (y : Config c) (hy : y.val = cfgOf g)
    (hz : Exec.wellSorted c r0.vars (σ (.ctor sB []) g) = true)
    (hi : injNormal exp Srt.kitem g = .inj exp Srt.kitem g)
    (hp : (!((some (GroundTerm.ctor sB [])).isSome && sameResult (some (.ctor sB [])) (some (.ctor sA []))) ||
      ((some (GroundTerm.ctor sB [])).isSome && sameResult (some (.ctor sB [])) (some (.ctor sB [])) &&
        ((some (GroundTerm.ctor sB [])).isSome && sameResult (some (.ctor sB [])) (some g)))) = true) :
    Step (c.withHooks H) (TieRuleLhs.cfgH noRaw CB H) (TieRuleLhs.cfgH noRaw y H) := by
  refine .rule r0 r0_mem (σ (.ctor sB []) g) ?_ ?_ (fun t ht => by rw [read_shape.1] at ht; cases ht) ?_ ?_
    (fun t ht => by rw [read_shape.2.1] at ht; cases ht) (by rw [read_shape.2.2.2.1]; exact .top)
    (fun r' hr' hlt => absurd hlt (by rw [rule_eq hr']; exact Nat.lt_irrefl _))
  · exact Exec.wellSorted_iff.mp ((congrFun (Cert.wellSorted_withHooks_hr c H noRaw r0.vars) _).trans hz)
  · rw [r0_lhs]
    have hiz : injNormal exp Srt.kitem (.ctor sC [.ctor sB []]) = .inj exp Srt.kitem (.ctor sC [.ctor sB []]) := rfl
    exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons (.ctor (symsH H).2.2.1
      (.cons (hiz ▸ .inj (.ctor (symsH H).2.2.2.2.2 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  · rw [read_shape.2.2.2.2]
    have h : Holds (c.withHooks H) r0.vars.length (σ (.ctor sB []) g)
        (.implies (.mem exp (.var 0) (.app sA []))
          (.and (.mem exp (.var 0) (.app sB [])) (.mem exp (.var 0) (.var 3)))) _ :=
      .implies (.mem .var (.ctor (symsH H).2.2.2.1 .nil))
        (.and (.mem .var (.ctor (symsH H).2.2.2.2.1 .nil)) (.mem .var .var))
    exact hp ▸ h
  · rw [r0_rhs]
    show EvalTerm (c.withHooks H) (σ (.ctor sB []) g) _ (some y.val)
    rw [hy]
    have he : EvalTerm (c.withHooks H) (σ (.ctor sB []) g) (.inj exp Srt.kitem (.var 3))
        (some (.inj exp Srt.kitem g)) := by
      have h : EvalTerm (c.withHooks H) (σ (.ctor sB []) g) (.inj exp Srt.kitem (.var 3))
          (some (injNormal exp Srt.kitem g)) := .inj .var
      rw [hi] at h; exact h
    exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons (.ctor (symsH H).2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))

/-- **`connectiveCut` of `\implies` on a left side, for every interpretation**: `c(b)` steps to
`b` and to `a` (the sentence's right side is the variable G, and `b` is in `a → (b ∧ G)` at every
G), and `c(a)` has no successor (`a` is in it at no G). -/
theorem implies_steps (H : HookParams) :
    Step (c.withHooks H) (TieRuleLhs.cfgH noRaw CB H) (TieRuleLhs.cfgH noRaw B H) ∧
      Step (c.withHooks H) (TieRuleLhs.cfgH noRaw CB H) (TieRuleLhs.cfgH noRaw A H) ∧
      ∀ y, ¬ Step (c.withHooks H) (TieRuleLhs.cfgH noRaw CA H) y := by
  refine ⟨step_b H (.ctor sB []) B rfl (by decide +kernel) rfl (by decide +kernel),
    step_b H (.ctor sA []) A rfl (by decide +kernel) rfl (by decide +kernel), ?_⟩
  intro y h
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  have hr := rule_eq hs.mem
  subst hr
  exact pre_at_a H (lookup0 H hs.hmatch) hs.hpre

end Steps

/-- info: 'KCore.TieRuleImplies.at_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms at_rule
/-- info: 'KCore.TieRuleImplies.rule_from_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_from_text
/-- info: 'KCore.TieRuleImplies.implies_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms implies_steps

end KCore.TieRuleImplies
