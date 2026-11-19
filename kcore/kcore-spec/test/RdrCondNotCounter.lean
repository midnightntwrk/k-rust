/-
  Sentence 157 of `f2-examples/mlreqnot.kompile.kore` (the rule of construct fixture e3-ml-req-not,
  `go(X) => done requires #Not(X >Int 0)`, read through `notAsCondition`) against Γ's item of the
  rule (`prioRuleK`), for every interpretation H. Run from the package root:
  `lake env lean -j1 test/RdrCondNotCounter.lean`.

  The sentence's left side holds `\equals{Bool}(\not{Bool}(X >Int 0), true)`; Γ's item holds the
  reading's condition `\equals{Bool}(X >Int 0, false)`. `\not{Bool}(B)` is the complement of B in
  Bool's elements, so it is `true`'s element alone exactly where B is all of Bool but that element.
  Where Bool's elements are the two literals' that is `B = false`. Where Bool has a third element
  and `X >Int 0` denotes `false`'s element, the complement holds the third element too: the
  sentence's condition fails and Γ's holds. There Γ's item says more than the sentence, and the
  direction of the class `rewrite rule` (`TieDir.weaker`: the sentence entails Γ's item, W1) fails.

  - `I`: an interpretation over 13 elements. Every sort holds every element, every literal but
    `true` and `false` and every symbol but `_>Int_` denotes the element `o`, `_>Int_` applied
    twice gives `false`'s element `ff`, `true` denotes `tt`, and nothing has a successor.
  - `sat_sig`: it satisfies `ΓSig` of every semantics.
  - `text_holds`: it satisfies sentence 157 as written (`Ltext0_empty`: the left side is empty).
  - `item_fails`: it does not satisfy Γ's item of the rule (`L0_o`: the left side holds of `o`).
  - `boolDist_mem`, `gtGraph_mem`, `sat_boolDist`, `sat_gtGraph`: two items of `ΓDomains` (`true`
    and `false` denote no common element; `0 >Int 0` is `false`) that it satisfies.
  - `countermodel`, `rule_not_from_text_dom`: for every H, sentence 157 with the signature and
    those two items does not entail Γ's rule item. `rule_not_from_text`: the same from the
    premises of `TieE3MlReqAndUnderApp.rule_from_text` (the sentence and the signature), the form
    W1 has for the sibling text's rule.
  - `bool_other`: in `I` Bool has an element neither literal denotes, and the literals are apart.

  Not shown here: a model of the sentence with every family of Γ but the rules (`ΓCons`, all of
  `ΓDomains`, `ΓColls`, `ΓFns`, `ΓFallback`) that fails the item. `I` is no such model (its
  constructors are not injective and its Int literals are one element). The library's value model
  (`Model.stdI`) did not give one by the routes tried: its Bool elements are Bool's values, and
  `genWf` refuses a constructor, an injection and an open generator into Bool (`EmptyInh.plus` of
  this text at Bool fails `coreOK` at `genWf` and `paramsPlain`); an overloading symbol into Bool
  was not tried. The other direction is not refuted either: no model of Γ is given in which
  sentence 157 fails.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RdrCondNotCounter

open KCore ML Faithful KoreAML

/-! ## The interpretation -/

inductive El where
  | d | i | c0 | c1 | c2 | n | gt | gt1 | dvT | dvF | tt | ff | o
  deriving DecidableEq

instance : Inhabited El := ⟨.o⟩

def gtName : String := "Lbl'Unds-GT-'Int'Unds'"

def evS : KoreAML.Sym → Set El
  | .defined => fun m => m = .d
  | .inh => fun m => m = .i
  | .ceil => fun m => m = .c0
  | .next => fun m => m = .n
  | .dv lit => fun m => m = (if lit = "true" then El.dvT else if lit = "false" then El.dvF else El.o)
  | .symbol s => fun m => m = (if s = gtName then El.gt else El.o)
  | _ => fun m => m = .o

def evA : El → El → Set El
  | .d, _ => fun _ => True
  | .i, _ => fun _ => True
  | .c0, _ => fun m => m = .c1
  | .c1, _ => fun m => m = .c2
  | .c2, _ => fun _ => True
  | .n, _ => fun _ => False
  | .gt, _ => fun m => m = .gt1
  | .gt1, _ => fun m => m = .ff
  | .dvT, _ => fun m => m = .tt
  | .dvF, _ => fun m => m = .ff
  | _, _ => fun m => m = .o

def I : Interpretation KoreAML.Sym El := ⟨evS, evA⟩

theorem defOK_I : DefOK I := fun _ _ => ⟨.d, rfl, True.intro⟩
theorem inh_all (σ m : El) : Inh I σ m := ⟨.i, rfl, True.intro⟩
theorem isSort_all (σ : El) : IsSort I σ := ⟨.o, rfl, inh_all _ _⟩

theorem inhOf_of {S : P} {e : Valuation El} (h : ∃ σ, S.interpret I e σ) (m : El) : (inhOf S).interpret I e m :=
  interp_inhOf.mpr (h.imp fun σ hσ => ⟨hσ, inh_all σ m⟩)

theorem inhOf_sort (n : String) (e : Valuation El) (m : El) : (inhOf (sym (.sort n))).interpret I e m :=
  inhOf_of (S := sym (.sort n)) ⟨.o, (rfl : El.o = El.o)⟩ m
theorem inhOf_evar (x : EVar) (e : Valuation El) (m : El) : (inhOf (.evar x)).interpret I e m :=
  inhOf_of (S := .evar x) ⟨e.evalEvar x, (rfl : e.evalEvar x = e.evalEvar x)⟩ m

theorem sat_def (x : EVar) : I ⊧ᴵ @definedness KoreAML.Sym _ x := by
  intro e m
  simp only [definedness, Pattern.interpret]
  rintro ⟨a, ha⟩
  exact ha ⟨.d, _, rfl, rfl, True.intro⟩

theorem guarded_of {ws : List P} {φ : P} {e : Valuation El} {m : El} (h : φ.interpret I e m) :
    (guarded ws φ).interpret I e m := by
  cases ws with
  | nil => exact h
  | cons w ws => exact fun _ => h

theorem sat_ceilDef : I ⊧ᴵ ceilDefItem.pat := by
  intro e m
  unfold ceilDefItem
  dsimp only
  refine guarded_of ?_
  rw [interp_equal defOK_I]
  intro a
  constructor
  · intro _; exact inhOf_evar _ e a
  · intro _
    rw [interp_sCeil_raw]
    exact ⟨_, _, _, rfl, rfl, rfl, .c2, ⟨.c1, ⟨.c0, rfl, rfl⟩, rfl⟩, True.intro⟩

/-- **The interpretation satisfies the signature of every semantics.** -/
theorem sat_sig (c : Semantics) : I ⊧ᴵP ΓSig c := by
  intro φ hφ
  rcases hφ with hφ | ⟨lit, rfl⟩
  · rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · simp only [sigItems, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at hit
      rcases hit with ((rfl | ⟨s, hs, rfl⟩) | ⟨k, hk, rfl⟩) | rfl | rfl | rfl
      · exact sat_def _
      · intro e m
        show (sExists ⟨1⟩ (sym .sortSort) (sym (.sort ("Sort" ++ c.sortName s)) ≡ .evar ⟨1⟩)).interpret I e m
        rw [interp_sExists]
        refine ⟨.o, ?_, ?_⟩
        · rw [interp_member defOK_I]; exact inhOf_of (S := sym .sortSort) ⟨.o, (rfl : El.o = El.o)⟩ _
        · rw [interp_equal defOK_I]
          intro b
          rw [interp_evar]
          simp only [Function.update_same]
          exact Iff.rfl
      · obtain ⟨hd, xs, -, hw⟩ := symApp_head c k.name
        intro e m
        rw [symArityItem_of_symApp hw, interp_included defOK_I]
        intro a _
        exact inhOf_sort _ e a
      · intro e m
        unfold ceilArityItem
        dsimp only
        refine guarded_of ?_
        rw [interp_included defOK_I]
        intro a _
        exact inhOf_evar _ e a
      · exact sat_ceilDef
      · intro e m
        show (sNext (inhOf (sym (.sort ("Sort" ++ c.sortName topCellSort)))) ⊆⊆
          inhOf (sym (.sort ("Sort" ++ c.sortName topCellSort)))).interpret I e m
        rw [interp_included defOK_I]
        intro a _
        exact inhOf_sort _ e a
    · exact sat_def x
  · intro e m
    unfold dvArityItem
    dsimp only
    refine guarded_of ?_
    rw [interp_included defOK_I]
    intro a _
    exact inhOf_evar _ e a

/-! ## Patterns in the interpretation -/

/-- φ denotes the one element x. -/
def Sing (φ : P) (e : Valuation El) (x : El) : Prop := ∀ m, φ.interpret I e m ↔ m = x

section
variable {t : VarTable} {e : Valuation El}

theorem sing_symbol {f : String} (hf : f ≠ gtName) : Sing (sym (.symbol f)) e .o := fun m => by
  show m = (if f = gtName then El.gt else El.o) ↔ m = .o
  simp only [hf, ↓reduceIte]
theorem sing_sort (n : String) : Sing (sym (.sort n)) e .o := fun _ => Iff.rfl
theorem sing_evar (x : EVar) : Sing (.evar x) e (e.evalEvar x) := fun _ => Iff.rfl

/-- An application whose head denotes `o` denotes `o`. -/
theorem sing_app_o {φ ψ : P} {y : El} (h1 : Sing φ e .o) (h2 : Sing ψ e y) : Sing (φ ⬝ ψ) e .o := fun m => by
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    rw [(h1 a).mp ha] at hab
    exact hab
  · rintro rfl
    exact ⟨.o, y, (h1 _).mpr rfl, (h2 _).mpr rfl, rfl⟩

theorem tr_ev (n : String) (s : Kore.KSort) : tr ⟨t, []⟩ (ev n s) = .evar (t.ev (evarKey (evar n s))) := by
  unfold ev; rw [tr]

def tC : Kore.KSort := srt "GeneratedTopCell"
def xP : Kore.Pattern := ev "VarV0" (srt "Int")
def kP : Kore.Pattern := ev "VarV1" (srt "K")
def cP : Kore.Pattern := ev "VarV2" (srt "GeneratedCounterCell")
/-- `X >Int 0`. -/
def gtX : Kore.Pattern := ap gtName [xP, .dv (srt "Int") "0"]
/-- `t = lit` at Bool, in the top cell's sort. -/
def eqB (a : Kore.Pattern) (lit : String) : Kore.Pattern := .equals (srt "Bool") tC a (.dv (srt "Bool") lit)
/-- The configuration `<generatedTop> <k> inj{Exp,KItem}(t) ~> K </k> C </generatedTop>`. -/
def cfg (a : Kore.Pattern) : Kore.Pattern :=
  ap "Lbl'-LT-'generatedTop'-GT-'" [ap "Lbl'-LT-'k'-GT-'" [ap "kseq" [injP "Exp" "KItem" a, kP]], cP]
/-- The rule's right side. -/
def rhs0 : Kore.Pattern := .and tC [cfg (ap "Lbldone" []), .top tC]
/-- Γ's left side: the term, no `requires`, the reading's condition `X >Int 0 = false`, `⌈R⌉`. -/
def L0 : Kore.Pattern := .and tC [cfg (ap "Lblgo" [xP]), .top tC, eqB gtX "false", .ceil tC tC rhs0]
/-- The text's left side: the term and `\not{Bool}(X >Int 0) = true`. -/
def Ltext0 : Kore.Pattern := .and tC [cfg (ap "Lblgo" [xP]), eqB (.not (srt "Bool") gtX) "true"]

theorem sing_cfg {a : Kore.Pattern} (h : Sing (tr ⟨t, []⟩ a) e .o) : Sing (tr ⟨t, []⟩ (cfg a)) e .o := by
  unfold cfg ap kP cP
  simp only [tr_app0, trArgs_cons, trArgs_nil, tr_injP, appList, tr_ev]
  exact sing_app_o (sing_app_o (sing_symbol (by decide))
    (sing_app_o (sing_symbol (by decide))
      (sing_app_o (sing_app_o (sing_symbol (by decide))
        (sing_app_o (sing_app_o (sing_app_o (sing_symbol (by decide)) (sing_sort _)) (sing_sort _)) h))
        (sing_evar _)))) (sing_evar _)

theorem sing_go : Sing (tr ⟨t, []⟩ (ap "Lblgo" [xP])) e .o := by
  unfold ap xP
  simp only [tr_app0, trArgs_cons, trArgs_nil, tr_ev]
  exact sing_app_o (sing_symbol (by decide)) (sing_evar _)

theorem sing_done : Sing (tr ⟨t, []⟩ (ap "Lbldone" [])) e .o := by
  unfold ap
  simp only [tr_app0, trArgs_nil]
  exact sing_symbol (by decide)

/-- `X >Int 0` denotes `false`'s element at every X. -/
theorem sing_gt : Sing (tr ⟨t, []⟩ gtX) e .ff := fun m => by
  unfold gtX ap xP
  simp only [tr_app0, trArgs_cons, trArgs_nil, tr_ev, tr_dv]
  rw [interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    rw [interp_app] at ha
    obtain ⟨a', b', ha', -, hab'⟩ := ha
    have h1 : a' = .gt := ha'
    subst h1
    have h2 : a = .gt1 := hab'
    subst h2
    exact hab
  · rintro rfl
    exact ⟨.gt1, .o, interp_app.mpr ⟨.gt, _, rfl, rfl, rfl⟩, interp_app.mpr ⟨.o, .o, rfl, rfl, rfl⟩, rfl⟩

theorem sing_true : Sing (tr ⟨t, []⟩ (.dv (srt "Bool") "true")) e .tt := fun m => by
  rw [tr_dv, interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    have h1 : a = .dvT := ha
    subst h1
    exact hab
  · rintro rfl
    exact ⟨.dvT, .o, rfl, rfl, rfl⟩

theorem sing_false : Sing (tr ⟨t, []⟩ (.dv (srt "Bool") "false")) e .ff := fun m => by
  rw [tr_dv, interp_app]
  constructor
  · rintro ⟨a, b, ha, -, hab⟩
    have h1 : a = .dvF := ha
    subst h1
    exact hab
  · rintro rfl
    exact ⟨.dvF, .o, rfl, rfl, rfl⟩

theorem hS (n : String) : ∀ b, (trSort t (srt n)).interpret I e b ↔ b = .o := by
  rw [trSort_srt]; exact fun _ => Iff.rfl

theorem inh_srt (n : String) (m : El) : (inhOf (trSort t (srt n))).interpret I e m := by
  rw [trSort_srt]; exact inhOf_sort _ e m

theorem eqB_tr (p : Kore.Pattern) (lit : String) : tr ⟨t, []⟩ (eqB p lit) =
    sEquals (trSort t (srt "Bool")) (trSort t tC) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ (.dv (srt "Bool") lit)) := by
  unfold eqB; rw [tr]

theorem top_holds (m : El) : (tr ⟨t, []⟩ (.top tC)).interpret I e m := by
  rw [tr]
  refine (interp_sTop defOK_I (by unfold tC; rw [trSort_srt]; rfl) m).mpr ?_
  exact inh_srt _ m

theorem rhs_o : (tr ⟨t, []⟩ rhs0).interpret I e .o := by
  unfold rhs0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (sing_cfg sing_done _).mpr rfl
  · exact top_holds _

/-- **Γ's left side holds of `o`** at every valuation: `X >Int 0` and `false` denote one element. -/
theorem L0_o : (tr ⟨t, []⟩ L0).interpret I e .o := by
  unfold L0
  rw [interp_and (List.cons_ne_nil _ _)]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (sing_cfg sing_go _).mpr rfl
  · exact top_holds _
  · rw [eqB_tr]
    exact (interp_sEquals defOK_I sat_ceilDef (hS _) (hS _) (isSort_all _) (isSort_all _) _).mpr
      ⟨inh_all _ _, fun a _ => (sing_gt a).trans (sing_false a).symm⟩
  · rw [tr]
    exact (interp_sCeil defOK_I sat_ceilDef (hS _) (hS _) (isSort_all _) (isSort_all _)
      (fun a _ => inh_all _ a) _).mpr ⟨⟨.o, rhs_o⟩, inh_all _ _⟩

/-- **The text's left side holds of nothing**: `\not{Bool}(X >Int 0)` holds of `o`, an element of
Bool that `true` does not denote. -/
theorem Ltext0_empty (a : El) : ¬ (tr ⟨t, []⟩ Ltext0).interpret I e a := by
  intro h
  unfold Ltext0 at h
  rw [interp_and (List.cons_ne_nil _ _)] at h
  have h1 := h (eqB (.not (srt "Bool") gtX) "true") (by simp)
  rw [eqB_tr] at h1
  have h2 := ((interp_sEquals defOK_I sat_ceilDef (hS _) (hS _) (isSort_all _) (isSort_all _) a).mp h1).2
    .o (inh_all _ _)
  have h3 : (tr ⟨t, []⟩ (.not (srt "Bool") gtX)).interpret I e .o := by
    rw [tr, interp_sNot]
    exact ⟨fun hg => (by cases (sing_gt _).mp hg), inh_srt _ _⟩
  cases (sing_true _).mp (h2.mp h3)

/-- Nothing has a successor. -/
theorem next_empty (φ : P) (m : El) : ¬ (sNext φ).interpret I e m := by
  unfold sNext
  rw [interp_app]
  rintro ⟨a, b, ha, -, hab⟩
  have h1 : a = .n := ha
  subst h1
  exact hab

theorem tr_rw (C : Kore.KSort) (X r : Kore.Pattern) :
    tr ⟨t, []⟩ (.rewrites C X r) = sRewrites (trSort t C) (tr ⟨t, []⟩ X) (tr ⟨t, []⟩ r) := by rw [tr]

end

/-! ## The text and Γ's rule item -/

kore_term kore from "f2-examples/mlreqnot.kompile.kore"
definition_of defn from "f2-examples/mlreqnot.kompile.kore"
user_axioms U from "f2-examples/mlreqnot.kompile.kore" module "E3-ML-REQ-NOT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
/-- Γ's axiom of the rule. -/
noncomputable def p0 : Kore.Pattern := prioRuleK c r0
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩] := by kernel_rfl
theorem p0_eq : p0 = .rewrites tC L0 rhs0 := by decide +kernel

def fT0 : List VarKey := (freeOf [] (.rewrites tC Ltext0 rhs0)).eraseDups

/-- **Sentence 157 is the item of `\rewrites{C}(Ltext0, rhs0)` at the table of Γ's axiom** (kernel). -/
theorem rule_text0 : TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] p0) fT0 tC Ltext0 rhs0) [] = some (trS U.ax157).pat := by
  decide +kernel

theorem free0 : (freeOf [] (.rewrites tC L0 rhs0)).eraseDups =
    [.evar "VarV0" (srt "Int"), .evar "VarV1" (srt "K"), .evar "VarV2" (srt "GeneratedCounterCell")] := by
  decide +kernel

/-- **The interpretation satisfies sentence 157**: its left side holds of nothing. -/
theorem text_holds : I ⊧ᴵ (trS U.ax157).pat := by
  have h := rule_text0
  simp only [TiePair.renSeq, Option.some.injEq] at h
  rw [← h]
  intro e m
  unfold TieRuleLhs.itemAt
  rw [interpret_impl]
  intro _
  rw [interp_equal defOK_I]
  intro a
  rw [tr_rw]
  unfold sRewrites
  rw [interp_sImp]
  exact ⟨fun h => h.1, fun hi => ⟨hi, fun hl => absurd hl (Ltext0_empty a)⟩⟩

/-- **The interpretation does not satisfy Γ's item of the rule**: at every valuation its left side
holds of `o`, which has no successor. -/
theorem item_fails : ¬ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩).pat) := by
  intro h
  rw [p0_eq, TieRuleLhs.trAxiom_rule] at h
  have h1 := h ⟨fun _ => .o, fun _ _ => False⟩ .o
  unfold TieRuleLhs.itemAt at h1
  rw [interpret_impl, free0] at h1
  have h2 := h1 (TieUnion.interp_conjListAll.mpr fun φ hφ => by
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl <;>
      exact (interp_guard_evar defOK_I).mpr (inh_srt _ _))
  rw [interp_equal defOK_I] at h2
  have h3 := (h2 .o).mpr (inh_srt _ _)
  rw [tr_rw] at h3
  unfold sRewrites at h3
  rw [interp_sImp] at h3
  exact next_empty _ _ (h3.2 L0_o)

/-! ## Two items of Γ's domains the interpretation satisfies -/

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- ΓDomains' item for the values `true` and `false`: no element is both. -/
noncomputable def boolDist (H : HookParams) : P :=
  ∼(den (cH H) (KCore.bool true) ⋀ den (cH H) (KCore.bool false))
/-- ΓDomains' item for `_>Int_` at `[0, 0]`: `0 >Int 0` is `false`. -/
noncomputable def gtGraph (H : HookParams) : P :=
  KoreAML.den (symApp (cH H) intGt (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 0])) ≡
    den (cH H) (KCore.bool false)

theorem boolDist_mem (H : HookParams) : ΓDomains (cH H) (boolDist H) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.bool true, KCore.bool false, Srt.bool, (by decide +kernel : (distinctSorts c).contains Srt.bool = true),
    by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel,
    by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel, by decide, rfl⟩)))

theorem gt_sig : (⟨intGt, [Srt.int, Srt.int], Srt.bool⟩ : CtorSig) ∈ hookSigs := by decide +kernel

theorem gtGraph_mem (H : HookParams) : ΓDomains (cH H) (gtGraph H) :=
  Or.inl ⟨_, [KCore.int 0, KCore.int 0], some (KCore.bool false), gt_sig,
    by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel, by decide +kernel,
    (fun h => nomatch h), rfl⟩

theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = tr ⟨[], []⟩ (.dv (srt "Bool") "true") := by
  show den c (KCore.bool true) = _; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = tr ⟨[], []⟩ (.dv (srt "Bool") "false") := by
  show den c (KCore.bool false) = _; decide +kernel
theorem symApp_withHooks (H : HookParams) (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl
theorem den_gt00 (H : HookParams) :
    KoreAML.den (symApp (cH H) intGt (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 0])) =
      tr ⟨[], []⟩ (ap gtName [.dv (srt "Int") "0", .dv (srt "Int") "0"]) := by
  have hk : GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 0] =
      [(KCore.int 0).kore (cH H), (KCore.int 0).kore (cH H)] := by simp only [GroundTerm.koreList]
  have h0 : (KCore.int 0).kore (cH H) = .dv (srt "Int") "0" := by
    show (KCore.int 0).kore c = _; decide +kernel
  rw [hk, h0, symApp_withHooks]
  decide +kernel

theorem sat_boolDist (H : HookParams) : I ⊧ᴵ boolDist H := by
  intro e m
  unfold boolDist
  rw [den_true, den_false, interpret_neg, interpret_conj]
  rintro ⟨h1, h2⟩
  cases ((sing_true m).mp h1).symm.trans ((sing_false m).mp h2)

theorem sat_gtGraph (H : HookParams) : I ⊧ᴵ gtGraph H := by
  intro e m
  unfold gtGraph
  rw [den_gt00, den_false, interp_equal defOK_I]
  intro a
  refine Iff.trans ?_ (sing_false a).symm
  unfold ap
  simp only [tr_app0, trArgs_cons, trArgs_nil, tr_dv]
  rw [interp_app]
  constructor
  · rintro ⟨f, b, hf, -, hfb⟩
    rw [interp_app] at hf
    obtain ⟨f', b', hf', -, hfb'⟩ := hf
    have h1 : f' = .gt := hf'
    subst h1
    have h2 : f = .gt1 := hfb'
    subst h2
    exact hfb
  · rintro rfl
    exact ⟨.gt1, .o, interp_app.mpr ⟨.gt, .o, rfl, interp_app.mpr ⟨.o, .o, rfl, rfl, rfl⟩, rfl⟩,
      interp_app.mpr ⟨.o, .o, rfl, rfl, rfl⟩, rfl⟩

/-! ## The countermodel -/

/-- The premises: sentence 157, `true` and `false` apart, `0 >Int 0 = false`, the signature. -/
noncomputable abbrev Pre157 (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts [(trS U.ax157).pat, boolDist H, gtGraph H] ∪ ΓSig (cH H)

theorem sat_pre (H : HookParams) : I ⊧ᴵP Pre157 H := by
  intro φ hφ
  rcases hφ with (hφ | ⟨x, rfl⟩) | hφ
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact text_holds
    · exact sat_boolDist H
    · exact sat_gtGraph H
  · exact sat_def x
  · exact sat_sig (cH H) φ hφ

/-- **The countermodel, for every H**: an interpretation that satisfies sentence 157, the signature
of `c.withHooks H` and the two items of its domains the reading's condition rests on (`true` and
`false` denote no common element, `boolDist_mem`; `0 >Int 0` is `false`, `gtGraph_mem`), and does
not satisfy Γ's item of the rule. In it Bool has an element that neither literal denotes
(`bool_other`); `X >Int 0` denotes `false`'s element, so `\not{Bool}(X >Int 0)` holds of that
element too and is not `true`: the sentence's left side is empty, while Γ's condition
`X >Int 0 = false` holds and no element has a successor. -/
theorem countermodel (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (J : Interpretation KoreAML.Sym M),
      (J ⊧ᴵP Pre157 H) ∧ ∃ it ∈ ruleItems (cH H), ¬ (J ⊧ᴵ it.pat) := by
  refine ⟨El, inferInstance, I, sat_pre H, trAxiom [] [] ⟨0, "kernel", ⟨[], p0, []⟩⟩, ?_, item_fails⟩
  rw [TiePair.ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _

/-- **Γ's rule item is no consequence of sentence 157, for every H**, with the signature and the
two items of the domains: W1 for the rule (the direction of the class `rewrite rule`, `.weaker`:
the sentence entails Γ's item) does not hold from these premises. -/
theorem rule_not_from_text_dom (H : HookParams) :
    ∃ it ∈ ruleItems (cH H), ¬ (Pre157 H ⊧ it.pat) := by
  obtain ⟨M, hM, J, hJ, it, hit, hn⟩ := countermodel H
  exact ⟨it, hit, fun h => hn (h (I := J) hJ)⟩

/-- **The premise set of `TieE3MlReqAndUnderApp.rule_from_text`** (W1 for the rule of the sibling
text: the sentence and the signature) **does not entail Γ's rule item here, for every H.** -/
theorem rule_not_from_text (H : HookParams) :
    ∃ it ∈ ruleItems (cH H), ¬ ((TiePair.Texts [(trS U.ax157).pat] ∪ ΓSig (cH H)) ⊧ it.pat) := by
  obtain ⟨it, hit, hn⟩ := rule_not_from_text_dom H
  refine ⟨it, hit, fun h => hn fun {M} _ {J} hJ => h (I := J) fun φ hφ => hJ φ ?_⟩
  rcases hφ with (hφ | hφ) | hφ
  · exact Or.inl (Or.inl (by rw [List.mem_singleton.mp hφ]; exact List.mem_cons_self ..))
  · exact Or.inl (Or.inr hφ)
  · exact Or.inr hφ

/-- **In the model Bool has an element that neither literal denotes**, and the literals denote two
elements. -/
theorem bool_other (e : Valuation El) :
    (inhOf (sortP "Bool")).interpret I e .o ∧
    ¬ (tr ⟨[], []⟩ (.dv (srt "Bool") "true")).interpret I e .o ∧
    ¬ (tr ⟨[], []⟩ (.dv (srt "Bool") "false")).interpret I e .o ∧
    ¬ ∃ a, (tr ⟨[], []⟩ (.dv (srt "Bool") "true")).interpret I e a ∧
      (tr ⟨[], []⟩ (.dv (srt "Bool") "false")).interpret I e a :=
  ⟨inhOf_sort _ e _, fun h => (by cases (sing_true _).mp h), fun h => (by cases (sing_false _).mp h),
    fun ⟨a, h1, h2⟩ => (by cases ((sing_true a).mp h1).symm.trans ((sing_false a).mp h2))⟩

end KCore.RdrCondNotCounter

#check @KCore.RdrCondNotCounter.sat_sig
#check @KCore.RdrCondNotCounter.text_holds
#check @KCore.RdrCondNotCounter.item_fails
#check @KCore.RdrCondNotCounter.rule_not_from_text
#check @KCore.RdrCondNotCounter.rule_not_from_text_dom
#check @KCore.RdrCondNotCounter.boolDist_mem
#check @KCore.RdrCondNotCounter.gtGraph_mem
#check @KCore.RdrCondNotCounter.countermodel
#check @KCore.RdrCondNotCounter.bool_other
#print axioms KCore.RdrCondNotCounter.rule_text0
#print axioms KCore.RdrCondNotCounter.rule_not_from_text
#print axioms KCore.RdrCondNotCounter.rule_not_from_text_dom
#print axioms KCore.RdrCondNotCounter.boolDist_mem
#print axioms KCore.RdrCondNotCounter.gtGraph_mem
#print axioms KCore.RdrCondNotCounter.countermodel
#print axioms KCore.RdrCondNotCounter.bool_other
