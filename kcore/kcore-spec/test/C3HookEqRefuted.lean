/-
  C3 `hook x equation`: reader tests of the check (rows-header.toml, owed-sentence item 4). Each text
  holds a user's equation of a symbol whose value the registry gives, which the reader leaves out of
  Γ and lists owed at values (`Parse.regLemmaEqn`, class `user lemma at values`); here the sentence is
  false at values, so Γ with it has no model and the text is not tied. These are tests of the check,
  never evidence for a row. Run from the package root: `lake env lean -j1 test/C3HookEqRefuted.lean`.
  Every statement is on the literal text, for every interpretation H; nothing reads `Parse.parse`.

  Each namespace states `text` (the sentence is the pattern of an equation in the function form,
  `LibEv.FnEqn`, typed over the text's sorts), `regLemma` (the reader takes it for an owed equation
  of a registry-valued symbol), `at` (**in every model of Γ, at one valuation sending the sentence's
  variables to values, the sentence fails**, `LibEv.FnEqn.refutedPT_at`) and `refuted` (Γ with the
  sentence has no model).
  - `False` (c3-hook-eq-false, `X +Int 1 => X`): at X = 0, `0 +Int 1` is 1, not 0.
  - `Coll` (c3-hook-eq-coll, `MyListItem(0) => .MyList`, MyList hooked to LIST.List): the list of
    one element 0 and the empty list are apart.
  - `RegEq` (f2-examples/regeq.kompile.kore, K's regression test macro-rewrite, `rule (5 => 6) : _`
    with `:` a macro for `ListItem(I) L`, kompile's equation
    `_List_(ListItem(5), L) = _List_(ListItem(6), L)`): at L the empty list, the lists [5] and [6] are
    apart.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore ML Faithful KoreAML LibEv

/-! ## `X +Int 1 => X` -/

namespace KCore.C3HookEqRefuted.False

kore_term kore from "f2-examples/c3-hook-eq-false.kompile.kore"
definition_of defn from "f2-examples/c3-hook-eq-false.kompile.kore"
user_axioms U from "f2-examples/c3-hook-eq-false.kompile.kore" module "C3-HOOK-EQ-FALSE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

noncomputable abbrev lemAx : AxiomDecl := U.ax154

/-- `X +Int 1 => X` in the function form. -/
def E : FnEqn := ⟨[("VarX", Srt.int)], intAdd, [(Srt.int, .var 0, none), (Srt.int, intT 1, none)], Srt.int, none, .var 0⟩

/-- `X`, `X0` at 0 and `X1` at 1. -/
def σ : Subst := [(0, int 0), (1, int 0), (2, int 1)]

kernel_rfl pattern : ∀ H : HookParams, lemAx.ax.pattern = E.patternP (cH H)
kernel_rfl typed : ∀ H : HookParams, E.typedPT (cH H) = E.typedPT c
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i
kernel_rfl keys_wh : ∀ (H : HookParams) (vars : Vars), keysRPT (cH H) vars = keysRPT c vars
kernel_rfl lhs_wh : ∀ H : HookParams, valP (cH H) σ E.lhs = some (int 1)

theorem text : lemAx.ax.pattern = E.patternP c ∧ lemAx.ax.sortVars = [KoreAML.Rv] ∧ E.typedPT c = true ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat ∧
    (∀ k ∈ KoreAML.freeOf [] lemAx.ax.pattern, ∃ i, i < E.av.length ∧ k = vkey c E.av i) ∧
    ((keysRPT c E.av).map (KoreAML.tableOf lemAx.ax.sortVars lemAx.ax.pattern).idxOf).Nodup := by
  decide +kernel

theorem regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

/-- **`X +Int 1 = X` fails at X = 0 in every model of Γ, for every H.** -/
theorem «at» (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e lemAx.ax ∧ SetVarsAtValues (cH H) I e lemAx.ax ∧
      ¬ (trS lemAx).pat.interpret I e default := by
  rw [text.2.2.2.1]
  refine FnEqn.refutedPT_at (coreOKH H) E ((typed H).trans text.2.2.1) σ ?_ (fun _ h => by simp [E] at h)
    ⟨rfl, fun _ h => by simp at h, rfl, fun _ h => by simp at h, trivial⟩ ?_ lemAx (pattern H) text.2.1
    (fun k hk => by simp only [vkey_wh]; exact text.2.2.2.2.1 k hk) (by rw [keys_wh]; exact text.2.2.2.2.2) hI
  · intro i p hp
    match i, hp with
    | 0, hp => cases hp; exact ⟨_, rfl, sortOf_int 0⟩
    | 1, hp => cases hp; exact ⟨_, rfl, sortOf_int 0⟩
    | 2, hp => cases hp; exact ⟨_, rfl, sortOf_int 1⟩
  · rw [lhs_wh]
    show some (int 1) ≠ σ.lookup 0
    simp [σ, int]

/-- **Γ with the sentence has no model, for every H.** -/
theorem refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS lemAx).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := «at» H hI
  exact hn (hax e default)

end KCore.C3HookEqRefuted.False

/-! ## `MyListItem(0) => .MyList` -/

namespace KCore.C3HookEqRefuted.Coll

kore_term kore from "f2-examples/c3-hook-eq-coll.kompile.kore"
definition_of defn from "f2-examples/c3-hook-eq-coll.kompile.kore"
user_axioms U from "f2-examples/c3-hook-eq-coll.kompile.kore" module "C3-HOOK-EQ-COLL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sort MyList, a collection sort of the text. -/
abbrev myList : Srt := 32
/-- `.MyList` and `MyListItem`, parameter symbols implemented by LIST.unit and LIST.element. -/
abbrev myUnit : Sym := 385
abbrev myItem : Sym := 386

theorem names : c.sortName myList = "MyList" ∧ c.symName myUnit = "Lbl'Stop'MyList" ∧
    c.symName myItem = "LblMyListItem" := by decide +kernel

kernel_rfl lookups : ∀ H : HookParams,
  [myUnit, myItem].map (fun f => ((cH H).lookupParam f).map (·.impl)) = [some (some listUnit), some (some listElem)]

noncomputable abbrev lemAx : AxiomDecl := U.ax155

/-- `MyListItem(0) => .MyList` in the function form. -/
def E : FnEqn := ⟨[], myItem, [(Srt.kitem, .inj Srt.int Srt.kitem (intT 0), none)], myList, none, .app myUnit []⟩

/-- `X0` at `0` injected into KItem. -/
def σ : Subst := [(0, .inj Srt.int Srt.kitem (int 0))]

kernel_rfl pattern : ∀ H : HookParams, lemAx.ax.pattern = E.patternP (cH H)
kernel_rfl typed : ∀ H : HookParams, E.typedPT (cH H) = E.typedPT c
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i
kernel_rfl keys_wh : ∀ (H : HookParams) (vars : Vars), keysRPT (cH H) vars = keysRPT c vars
kernel_rfl sides_wh : ∀ H : HookParams, (valP (cH H) σ E.lhs, valP (cH H) σ E.rhs) = (valP c σ E.lhs, valP c σ E.rhs)
kernel_rfl sort_wh : ∀ H : HookParams, (cH H).sortOf (.inj Srt.int Srt.kitem (int 0)) = some Srt.kitem

theorem text : lemAx.ax.pattern = E.patternP c ∧ lemAx.ax.sortVars = [KoreAML.Rv] ∧ E.typedPT c = true ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat ∧
    (∀ k ∈ KoreAML.freeOf [] lemAx.ax.pattern, ∃ i, i < E.av.length ∧ k = vkey c E.av i) ∧
    ((keysRPT c E.av).map (KoreAML.tableOf lemAx.ax.sortVars lemAx.ax.pattern).idxOf).Nodup := by
  decide +kernel

theorem regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

/-- The two sides' values at σ: the list of one element `0` and the empty list, of the sort MyList,
which differ. -/
theorem sides : valP c σ E.lhs ≠ valP c σ E.rhs ∧ (valP c σ E.lhs).isSome ∧ (valP c σ E.rhs).isSome := by
  decide +kernel

/-- **`MyListItem(0) = .MyList` fails in every model of Γ, for every H.** -/
theorem «at» (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e lemAx.ax ∧ SetVarsAtValues (cH H) I e lemAx.ax ∧
      ¬ (trS lemAx).pat.interpret I e default := by
  rw [text.2.2.2.1]
  refine FnEqn.refutedPT_at (coreOKH H) E ((typed H).trans text.2.2.1) σ ?_ (fun _ h => by simp [E] at h)
    ⟨rfl, fun _ h => by simp at h, trivial⟩ ?_ lemAx (pattern H) text.2.1
    (fun k hk => by simp only [vkey_wh]; exact text.2.2.2.2.1 k hk) (by rw [keys_wh]; exact text.2.2.2.2.2) hI
  · intro i p hp
    match i, hp with
    | 0, hp => cases hp; exact ⟨_, rfl, sort_wh H⟩
  · intro heq
    have := sides_wh H
    rw [heq] at this
    simp only [Prod.mk.injEq] at this
    exact sides.1 (this.1.symm.trans this.2)

/-- **Γ with the sentence has no model, for every H.** -/
theorem refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS lemAx).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := «at» H hI
  exact hn (hax e default)

end KCore.C3HookEqRefuted.Coll

/-! ## `_List_(ListItem(5), L) => _List_(ListItem(6), L)` -/

namespace KCore.C3HookEqRefuted.RegEq

kore_term kore from "f2-examples/regeq.kompile.kore"
definition_of defn from "f2-examples/regeq.kompile.kore"
user_axioms U from "f2-examples/regeq.kompile.kore" module "REGEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

noncomputable abbrev lemAx : AxiomDecl := U.ax172

/-- `ListItem(n)` of an integer n, injected into KItem. -/
def itemT (n : Int) : Term := .app listElem [.inj Srt.int Srt.kitem (intT n)]

/-- `_List_(ListItem(5), _Gen0) => _List_(ListItem(6), _Gen0)` in the function form. -/
def E : FnEqn :=
  ⟨[("Var'Unds'Gen0", Srt.list)], listConcat, [(Srt.list, itemT 5, none), (Srt.list, .var 0, none)], Srt.list, none,
    .app listConcat [itemT 6, .var 0]⟩

/-- The empty list, Γ's value of `.List`. -/
noncomputable def nilV : GroundTerm := (c.hv listUnit []).getD default
/-- The list of one element 5, Γ's value of `ListItem(5)`. -/
noncomputable def one5 : GroundTerm := (c.hv listElem [.inj Srt.int Srt.kitem (int 5)]).getD default

/-- `_Gen0` and `X1` at the empty list, `X0` at the list of one element 5. -/
noncomputable def σ : Subst := [(0, nilV), (1, one5), (2, nilV)]

kernel_rfl pattern : ∀ H : HookParams, lemAx.ax.pattern = E.patternP (cH H)
kernel_rfl typed : ∀ H : HookParams, E.typedPT (cH H) = E.typedPT c
kernel_rfl vkey_wh : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i
kernel_rfl keys_wh : ∀ (H : HookParams) (vars : Vars), keysRPT (cH H) vars = keysRPT c vars
kernel_rfl sides_wh : ∀ H : HookParams, (valP (cH H) σ E.lhs, valP (cH H) σ E.rhs) = (valP c σ E.lhs, valP c σ E.rhs)
kernel_rfl pat0_wh : ∀ H : HookParams, valP (cH H) σ (itemT 5) = valP c σ (itemT 5)
kernel_rfl sortNil : ∀ H : HookParams, (cH H).sortOf nilV = some Srt.list
kernel_rfl sortOne5 : ∀ H : HookParams, (cH H).sortOf one5 = some Srt.list

theorem text : lemAx.ax.pattern = E.patternP c ∧ lemAx.ax.sortVars = [KoreAML.Rv] ∧ E.typedPT c = true ∧
    (trS lemAx).pat = (trAxiom [] [] lemAx).pat ∧
    (∀ k ∈ KoreAML.freeOf [] lemAx.ax.pattern, ∃ i, i < E.av.length ∧ k = vkey c E.av i) ∧
    ((keysRPT c E.av).map (KoreAML.tableOf lemAx.ax.sortVars lemAx.ax.pattern).idxOf).Nodup := by
  decide +kernel

theorem regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

/-- The values at σ: `ListItem(5)` matches `X0`, and the two sides are the lists [5] and [6], which
differ. -/
theorem vals : valP c σ (itemT 5) = σ.lookup 1 ∧ valP c σ E.lhs ≠ valP c σ E.rhs ∧ (valP c σ E.lhs).isSome := by
  decide +kernel

/-- **`_List_(ListItem(5), L) = _List_(ListItem(6), L)` fails at L the empty list in every model of
Γ, for every H.** -/
theorem «at» (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e lemAx.ax ∧ SetVarsAtValues (cH H) I e lemAx.ax ∧
      ¬ (trS lemAx).pat.interpret I e default := by
  rw [text.2.2.2.1]
  refine FnEqn.refutedPT_at (coreOKH H) E ((typed H).trans text.2.2.1) σ ?_ (fun _ h => by simp [E] at h)
    ⟨(pat0_wh H).trans vals.1, fun _ h => by simp at h, rfl, fun _ h => by simp at h, trivial⟩ ?_ lemAx (pattern H)
    text.2.1 (fun k hk => by simp only [vkey_wh]; exact text.2.2.2.2.1 k hk) (by rw [keys_wh]; exact text.2.2.2.2.2) hI
  · intro i p hp
    match i, hp with
    | 0, hp => cases hp; exact ⟨_, rfl, sortNil H⟩
    | 1, hp => cases hp; exact ⟨_, rfl, sortOne5 H⟩
    | 2, hp => cases hp; exact ⟨_, rfl, sortNil H⟩
  · intro heq
    have := sides_wh H
    rw [heq] at this
    simp only [Prod.mk.injEq] at this
    exact vals.2.1 (this.1.symm.trans this.2)

/-- **Γ with the sentence has no model, for every H.** -/
theorem refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS lemAx).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := «at» H hI
  exact hn (hax e default)

end KCore.C3HookEqRefuted.RegEq

#check @KCore.C3HookEqRefuted.False.refuted
#check @KCore.C3HookEqRefuted.Coll.refuted
#check @KCore.C3HookEqRefuted.RegEq.refuted
/-- info: 'KCore.C3HookEqRefuted.False.refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqRefuted.False.refuted
/-- info: 'KCore.C3HookEqRefuted.Coll.refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqRefuted.Coll.refuted
/-- info: 'KCore.C3HookEqRefuted.RegEq.refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3HookEqRefuted.RegEq.refuted
#print axioms KCore.C3HookEqRefuted.False.regLemma
#print axioms KCore.C3HookEqRefuted.Coll.regLemma
#print axioms KCore.C3HookEqRefuted.RegEq.regLemma
