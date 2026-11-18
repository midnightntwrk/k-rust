/-
  The fixture sentences of three inert classes (`Parse.InertReason`), each entailed by
  `Γ (c.withHooks H)` for every interpretation H, from the library's statement of its class
  (`KcoreSpec/InertEv.lean`). Run from the package root: `lake env lean test/InertEvFixtures.lean`.

  - `collectionLaw` on `f2-examples/ens.kompile.kore`: 53 (associativity of `_List_`), 54 (its right
    unit), 55 (its left unit), each entailed at values (`Ens.list_laws_ens`).
  - `parametricFunctional` on `f2-examples/lazy.kore`: sentence 39,
    `\exists{R}(Val:S, \equals{S, R}(Val:S, Lblite{S}(K0:SortBool{}, K1:S, K2:S)))` over the sort
    variable S (`Lazy.ax39_text`). The definition has `ite` at Int (its parameter `Lblite{Int}`,
    implemented by the registry's `kIte`); the sentence at S := `SortInt{}` is entailed at values
    (`Lazy.ite_int_lazy`). The sentence over the sort variable is not stated at values: no value
    has a sort variable for its sort.
  - `vacuousLeft`: the rule of fixture e3-ml-rule-lhs-bottom (`rule <k> c(#Bottom) => a() ... </k>`,
    `test/constructs/fixtures/e3-ml-rule-lhs-bottom/kore.txt` at `//@ 202`, the axiom copied to
    `LhsBottom.ax`), entailed for every semantics (`LhsBottom.vacuous_lhs_bottom`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertEvFixtures

open KCore ML Faithful KoreAML

theorem lookupParam_wh (c : Semantics) (H : HookParams) (f : Sym) :
    (c.withHooks H).lookupParam f = c.lookupParam f := rfl
theorem iteFunPat_wh (c : Semantics) (H : HookParams) (f : Sym) (S : Srt) :
    InertEv.iteFunPat (c.withHooks H) f S = InertEv.iteFunPat c f S := rfl

namespace Ens

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

theorem law53 (H : HookParams) : EntailsAtValues (cH H) U.ax53 (trS U.ax53).pat := by
  rw [(by decide +kernel : (trS U.ax53).pat = (trAxiom [] [] U.ax53).pat)]
  exact InertEv.listLaw_ev (coreOKH H) (shapesOKH H) (Or.inl rfl) U.ax53 (by decide +kernel) (by decide +kernel)

theorem law54 (H : HookParams) : EntailsAtValues (cH H) U.ax54 (trS U.ax54).pat := by
  rw [(by decide +kernel : (trS U.ax54).pat = (trAxiom [] [] U.ax54).pat)]
  exact InertEv.listLaw_ev (coreOKH H) (shapesOKH H) (Or.inr (Or.inl rfl)) U.ax54 (by decide +kernel)
    (by decide +kernel)

theorem law55 (H : HookParams) : EntailsAtValues (cH H) U.ax55 (trS U.ax55).pat := by
  rw [(by decide +kernel : (trS U.ax55).pat = (trAxiom [] [] U.ax55).pat)]
  exact InertEv.listLaw_ev (coreOKH H) (shapesOKH H) (Or.inr (Or.inr rfl)) U.ax55 (by decide +kernel)
    (by decide +kernel)

/-- The reader's class of the three sentences. -/
theorem laws_class : [U.ax53, U.ax54, U.ax55].map (fun ad => Parse.classifyShape (.axiom ad.ax)) =
    [.inert .collectionLaw, .inert .collectionLaw, .inert .collectionLaw] := by decide +kernel

/-- **The three laws of `_List_` in ens are entailed at values**, for every H. -/
theorem list_laws_ens (H : HookParams) :
    ∀ ad ∈ [U.ax53, U.ax54, U.ax55], EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · exact law53 H
  · exact law54 H
  · exact law55 H

end Ens

namespace Lazy

definition_of defn from "f2-examples/lazy.kore"
user_axioms U from "f2-examples/lazy.kore" module "LAZY"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap
theorem shapesOK : c.shapesOK = true := by decide +kernel

/-- The definition's parameter implemented by `kIte`. -/
noncomputable def kp : ParamSig := (c.params.filter (·.impl == some kIte)).headD default

theorem kp_named : c.symName kp.sig.name = "Lblite{Int}" := by decide +kernel
theorem kp_lookup : c.lookupParam kp.sig.name = some kp := by decide +kernel
theorem kp_impl : kp.impl = some kIte := by decide +kernel
theorem kp_args : kp.sig.args = [Srt.bool, Srt.int, Srt.int] := by decide +kernel
theorem kp_res : kp.sig.result = Srt.int := by decide +kernel

/-- The `functional` sentence of `ite` at the sort X, as the text writes it. -/
def iteFunAt (X : Kore.KSort) : Kore.Pattern :=
  .exist R (evar "Val" X) (.equals X R (.var (.evar (evar "Val" X)))
    (.app ⟨⟨"Lblite"⟩⟩ [X] [.var (.evar (evar "K0" (srt "Bool"))), .var (.evar (evar "K1" X)),
      .var (.evar (evar "K2" X))]))

/-- Sentence 39 is that sentence at the sort variable `SortSort`, over the sort variables R and
`SortSort`. -/
theorem ax39_text : U.ax39.ax.pattern = iteFunAt (.var ⟨⟨⟨"SortSort"⟩⟩⟩) ∧
    U.ax39.ax.sortVars = [Rv, ⟨⟨⟨"SortSort"⟩⟩⟩] := by decide +kernel

/-- The reader's class of sentence 39. -/
theorem ax39_class : Parse.classifyShape (.axiom U.ax39.ax) = .inert .parametricFunctional := by decide +kernel

/-- Sentence 39 at `SortSort := SortInt{}`. -/
noncomputable def ax39Int : AxiomDecl :=
  ⟨U.ax39.index, U.ax39.module,
    { sortVars := [Rv], pattern := iteFunAt (srt "Int"), attributes := U.ax39.ax.attributes }⟩

/-- The instance is the `functional` sentence of the parameter `Lblite{Int}`. -/
theorem ite_instance : iteFunAt (srt "Int") = InertEv.iteFunPat c kp.sig.name Srt.int := by decide +kernel

/-- **`ite` at Int is total at values in lazy**, for every H. -/
theorem ite_int_lazy (H : HookParams) :
    EntailsAtValues (c.withHooks H) ax39Int (trAxiom [] [] ax39Int).pat :=
  InertEv.iteFun_entailed (c := c.withHooks H) ((Semantics.coreOK_withHooks c H).trans coreOK) shapesOK
    ((lookupParam_wh c H _).trans kp_lookup) kp_impl kp_args kp_res
    (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)) ax39Int
    (ite_instance.trans (iteFunPat_wh c H _ _).symm) rfl

end Lazy

namespace LhsBottom

def top : Kore.KSort := srt "GeneratedTopCell"

/-- The configuration with `item` first in the `<k>` cell. -/
def cfg (item : Kore.Pattern) : Kore.Pattern :=
  ap "Lbl'-LT-'generatedTop'-GT-'"
    [ap "Lbl'-LT-'k'-GT-'" [ap "kseq" [injP "Exp" "KItem" item, ev "Var'Unds'DotVar1" (srt "K")]],
     ev "Var'Unds'DotVar0" (srt "GeneratedCounterCell")]

/-- The rule's axiom, `c(\bottom{SortExp{}}())` on the left side. -/
def ax : Kore.Axiom :=
  { sortVars := []
    pattern := .rewrites top (.and top [cfg (ap "Lblc" [.bottom (srt "Exp")]), .top top])
      (.and top [cfg (ap "Lbla" []), .top top])
    attributes := [] }

/-- info: "inert vacuousLeft" -/
#guard_msgs in #eval (Parse.classifyShape (.axiom ax)).name

/-- **The rule with `#Bottom` on its left side is entailed**, for every semantics and every H,
with any declarations, at any place in a text. -/
theorem vacuous_lhs_bottom (c : Semantics) (H : HookParams) (decls : List SymbolDecl) (i : Nat) (mod : String) :
    Γ (c.withHooks H) ⊧ (trAxiom decls [] ⟨i, mod, ax⟩).pat :=
  InertEv.vacuousLeft_entailed (c.withHooks H) (by decide +kernel) decls i mod

end LhsBottom

end KCore.InertEvFixtures

#check @KCore.InertEv.vacuousLeft_entailed
#check @KCore.InertEv.listLaw_ev
#check @KCore.InertEv.iteFun_entailed
/-- info: 'KCore.InertEvFixtures.Ens.list_laws_ens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.InertEvFixtures.Ens.list_laws_ens
/-- info: 'KCore.InertEvFixtures.Lazy.ite_int_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.InertEvFixtures.Lazy.ite_int_lazy
/-- info: 'KCore.InertEvFixtures.LhsBottom.vacuous_lhs_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.InertEvFixtures.LhsBottom.vacuous_lhs_bottom
