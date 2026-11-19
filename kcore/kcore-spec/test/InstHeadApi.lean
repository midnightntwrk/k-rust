/-
  KCore test: the lemmas through which the head `symApp` writes is read (`InstHeadOf`,
  `symApp_head`, `symApp_noInst`, `instHeadP`, `tr_instApp`, and the `_of_symApp` and `_noInst`
  lemmas of `symHead`, `symArityItem`, `DetachedB.appOK` and `gammaHead`), each at a plain name and
  at the instance name `Lblite{Int}`, on a semantics with the two symbols `Lblfoo` and
  `Lblite{Int}`. Run from the package root: `lake env lean -j1 test/InstHeadApi.lean`.
  - The plain symbol's writing is derived from `symApp_head` and the decoder alone
    (`plain_written`): a name the decoder reads as no instance is written at itself, at no sort.
  - The instance's writing, `Lblite` at `SortInt`, is the decoder's reading of its name
    (`inst_written`).
-/
import KcoreSpec.TieHeads
import KcoreSpec.DetachedB
import KcoreSpec.FaithfulStep

set_option autoImplicit false

namespace KCore.InstHeadApiTest

open KCore Faithful

/-- A semantics with two own symbols: `Lblfoo` and `Lblite{Int}`. -/
def c : Semantics :=
  { lib := {}, sortNames := [], symNames := ["Lblfoo", "Lblite{Int}"], userSorts := [], ctors := [],
    fns := [], userSubsorts := [], pgmSort := Srt.k, rules := [] }

/-- `Lblfoo : Int → Int`. -/
def kPlain : CtorSig := ⟨nRegSyms, [Srt.int], Srt.int⟩
/-- `Lblite{Int} : Bool × Int × Int → Int`. -/
def kInst : CtorSig := ⟨nRegSyms + 1, [Srt.bool, Srt.int, Srt.int], Srt.int⟩

theorem name_plain : c.symName kPlain.name = "Lblfoo" := by decide +kernel
theorem name_inst : c.symName kInst.name = "Lblite{Int}" := by decide +kernel
theorem dec_plain : instDecode? (c.symName kPlain.name) = none := by decide +kernel
theorem dec_inst : instDecode? (c.symName kInst.name) = some ("Lblite", ["Int"]) := by decide +kernel

/-! ## (1) The head as the translation writes it -/

theorem headP_plain : instHeadP "Lblfoo" [] = KoreAML.sym (.symbol "Lblfoo") := instHeadP_nil _

theorem headP_inst : instHeadP "Lblite" ["Int"] = KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort "SortInt") :=
  rfl

theorem headP_closed_plain : KoreAML.Closed (instHeadP "Lblfoo" []) := instHeadP_closed _ _
theorem headP_closed_inst : KoreAML.Closed (instHeadP "Lblite" ["Int"]) := instHeadP_closed _ _

theorem tr_plain (t : KoreAML.VarTable) (ps : List Kore.Pattern) :
    KoreAML.tr ⟨t, []⟩ (.app ⟨⟨"Lblfoo"⟩⟩ ([].map KoreAML.srt) ps) =
      KoreAML.trArgs ⟨t, []⟩ (instHeadP "Lblfoo" []) ps :=
  tr_instApp _ _ _

theorem tr_inst (t : KoreAML.VarTable) (ps : List Kore.Pattern) :
    KoreAML.tr ⟨t, []⟩ (.app ⟨⟨"Lblite"⟩⟩ (["Int"].map KoreAML.srt) ps) =
      KoreAML.trArgs ⟨t, []⟩ (instHeadP "Lblite" ["Int"]) ps :=
  tr_instApp _ _ _

/-! ## (2) The head `symApp` writes -/

theorem headOf_plain : InstHeadOf (c.symName kPlain.name) "Lblfoo" [] := .inl ⟨rfl, name_plain.symm⟩
theorem headOf_inst : InstHeadOf (c.symName kInst.name) "Lblite" ["Int"] :=
  .inr ⟨List.cons_ne_nil _ _, dec_inst⟩

/-- The plain symbol is written at its name, at no sort, from `symApp_head` and the decoder. -/
theorem plain_written : ∀ ps, symApp c kPlain.name ps = .app ⟨⟨"Lblfoo"⟩⟩ ([].map KoreAML.srt) ps := by
  obtain ⟨h, xs, hi, hw⟩ := symApp_head c kPlain.name
  rcases hi with ⟨rfl, rfl⟩ | ⟨-, hd⟩
  · rw [name_plain] at hw; exact hw
  · rw [dec_plain] at hd; cases hd

theorem inst_head : ∃ h xs, InstHeadOf (c.symName kInst.name) h xs ∧
    ∀ ps, symApp c kInst.name ps = .app ⟨⟨h⟩⟩ (xs.map KoreAML.srt) ps :=
  symApp_head c kInst.name

theorem noInst_plain (ps : List Kore.Pattern) : symApp c kPlain.name ps = .app ⟨⟨"Lblfoo"⟩⟩ [] ps := by
  rw [symApp_noInst dec_plain, name_plain]

/-- The instance is written as `Lblite` at `SortInt`: the decoder reads its name as `Lblite` at one
sort. -/
theorem inst_written : ∀ ps, symApp c kInst.name ps = .app ⟨⟨"Lblite"⟩⟩ (["Int"].map KoreAML.srt) ps := by
  intro ps; unfold symApp; rw [iteSort?_eq_some.2 dec_inst]; rfl

/-! ## (3) The readers of the head -/

theorem symHead_plain : symHead c kPlain.name = instHeadP "Lblfoo" [] := symHead_of_symApp plain_written
theorem symHead_inst : symHead c kInst.name = instHeadP "Lblite" ["Int"] := symHead_of_symApp inst_written
theorem symHead_plain' : symHead c kPlain.name = KoreAML.sym (.symbol "Lblfoo") := by
  rw [symHead_noInst dec_plain, name_plain]

theorem arity_plain : (symArityItem c kPlain).pat =
    (KoreAML.appList (instHeadP "Lblfoo" []) (kPlain.args.map fun s => KoreAML.inhOf (sortP (c.sortName s))) ⊆⊆
      KoreAML.inhOf (sortP (c.sortName kPlain.result))) :=
  symArityItem_of_symApp plain_written
theorem arity_inst : (symArityItem c kInst).pat =
    (KoreAML.appList (instHeadP "Lblite" ["Int"]) (kInst.args.map fun s => KoreAML.inhOf (sortP (c.sortName s))) ⊆⊆
      KoreAML.inhOf (sortP (c.sortName kInst.result))) :=
  symArityItem_of_symApp inst_written
theorem arity_plain' : symArityItem c kPlain =
    KoreAML.arityItem ⟨c.symName kPlain.name, [], kPlain.args.map (srtOf c), srtOf c kPlain.result, false, []⟩ :=
  symArityItem_noInst dec_plain

theorem appOK_plain : DetachedB.appOK c [] [kPlain.name] kPlain.name = false := by
  rw [DetachedB.appOK_of_symApp c [] [kPlain.name] plain_written]; decide +kernel
theorem appOK_inst : DetachedB.appOK c [Srt.int] [] kInst.name = false := by
  rw [DetachedB.appOK_of_symApp c [Srt.int] [] inst_written]; decide +kernel
theorem appOK_inst' : DetachedB.appOK c [] [] kInst.name = true := by
  rw [DetachedB.appOK_of_symApp c [] [] inst_written]; rfl
theorem appOK_plain' : DetachedB.appOK c [] [] kPlain.name = DetachedB.kOK c [] [] kPlain.name :=
  DetachedB.appOK_noInst c [] [] dec_plain

theorem gammaHead_plain : gammaHead c kPlain.name = ("Lblfoo", []) := gammaHead_of_symApp plain_written
theorem gammaHead_inst : gammaHead c kInst.name = ("Lblite", [KoreAML.srt "Int"]) :=
  gammaHead_of_symApp inst_written
theorem gammaHead_plain' : gammaHead c kPlain.name = (c.symName kPlain.name, []) := gammaHead_noInst dec_plain

end KCore.InstHeadApiTest

#print axioms KCore.InstHeadApiTest.headP_plain
#print axioms KCore.InstHeadApiTest.headP_closed_inst
#print axioms KCore.InstHeadApiTest.tr_plain
#print axioms KCore.InstHeadApiTest.tr_inst
#print axioms KCore.InstHeadApiTest.plain_written
#print axioms KCore.InstHeadApiTest.inst_head
#print axioms KCore.InstHeadApiTest.noInst_plain
#print axioms KCore.InstHeadApiTest.symHead_plain
#print axioms KCore.InstHeadApiTest.symHead_inst
#print axioms KCore.InstHeadApiTest.symHead_plain'
#print axioms KCore.InstHeadApiTest.arity_plain
#print axioms KCore.InstHeadApiTest.arity_inst
#print axioms KCore.InstHeadApiTest.arity_plain'
#print axioms KCore.InstHeadApiTest.appOK_plain
#print axioms KCore.InstHeadApiTest.appOK_inst
#print axioms KCore.InstHeadApiTest.appOK_inst'
#print axioms KCore.InstHeadApiTest.appOK_plain'
#print axioms KCore.InstHeadApiTest.gammaHead_plain
#print axioms KCore.InstHeadApiTest.gammaHead_inst
#print axioms KCore.InstHeadApiTest.gammaHead_plain'
