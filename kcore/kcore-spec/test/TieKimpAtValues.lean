/-
  Row imp, the classes hooked functional, collection law and library entailed at values on kimp's
  text as kompile wrote it (`examples/ref-kimp/RefKimp/definition.kore`, user module `IMP`), for
  every interpretation H. The semantics is the generated package's `RefKimp.defn.sem`, and its
  `coreOK`, which the library's statements take, is the package's `RefKimp.coreOK_defn` (from
  `wf defn`). Each sentence is tied by the library's one statement of it (KcoreSpec/LibEv*.lean):
  the text's axiom is compared with the statement's pattern over the registry's names, and its
  translation with the text's declarations with the translation the statement is about.
  Run from the package root with the package built (test/imp-tie-atvalues.sh does both):
  `LEAN_PATH=.lake/pins/kimp-tie/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) lean test/TieKimpAtValues.lean`.

  - Hooked functional (`fun_entailed`, `fun_indices`): the 47 sentences
    `\exists{R}(Val:s, \equals{s, R}(Val:s, f(K0:s0, …)))` whose symbol is an interpreted hooked
    symbol that is not partial (`LibEv.functional_ev`). Not among them: 633, the sentence of `ite`,
    which the text states once over a sort variable and which is not of the form `funPatR k`.
  - Collection law (`laws_entailed`, `law_indices`): associativity and the two units of `_List_`,
    `_Map_`, `_Set_` (LibEvLaw.lean), the nine sentences of the class.
  - Library (`lib_entailed`, `libSet_entailed`, `lib_indices`): 76 of the class's 82. The sixteen
    predicate equations of `==Int`, `=/=Int`, `==K`, `=/=K` (`pred_entailed`); 52 term and function
    equations, each by its own theorem (`evN`); the eight Bool predicate sentences over set
    variables (684 to 687, 692, 693, 698, 699), entailed at set values (`EntailsAtSetValues`: each
    free set variable at a set of values of its sort), which `libSet_entailed` states. Not among
    them: the shift simplifications 794, 795, 801, 802 (`X <<Int 0`, `0 <<Int Y`, `X >>Int 0`,
    `0 >>Int Y`), of which the library states no equation, and 877, 878 (`ite{SortK}` at a
    condition), whose symbol is `ite` at the sort K.
-/
import RefKimp.Sound

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimpAtValues

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
user_axioms U from "examples/ref-kimp/RefKimp/definition.kore" module "IMP"

noncomputable abbrev c : Semantics := RefKimp.defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOKH (H : HookParams) : (cH H).coreOK = true :=
  (Semantics.coreOK_withHooks c H).trans RefKimp.coreOK_defn
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)
theorem boolBelowH (H : HookParams) : Srt.bool ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.bool = true)
theorem intBelowH (H : HookParams) : Srt.int ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.int = true)

/-! ## Hooked functional (47 of 48) -/

/-- The indices of the sentences. -/
def funIdx : List Nat :=
  [433, 434, 435, 446, 447, 448, 449, 450, 451, 478, 490, 501, 520, 522, 530, 537, 538, 539, 540, 541,
   542, 556, 561, 568, 576, 584, 585, 586, 587, 588, 589, 590, 591, 593, 595, 598, 599, 612, 634, 635,
   636, 639, 640, 641, 642, 643, 644]

/-- The sentences, in text order. -/
noncomputable def funText : List AxiomDecl := U.all.filter fun ad => funIdx.contains ad.index

theorem fun_indices : funText.map (·.index) =
    [433, 434, 435, 446, 447, 448, 449, 450, 451, 478, 490, 501, 520, 522, 530, 537, 538, 539, 540, 541,
     542, 556, 561, 568, 576, 584, 585, 586, 587, 588, 589, 590, 591, 593, 595, 598, 599, 612, 634, 635,
     636, 639, 640, 641, 642, 643, 644] := by
  decide +kernel

/-- The name of the symbol a sentence of the form `\exists{R}(Val, \equals{s, R}(Val, f(…)))`
applies. -/
def headOf : Kore.Pattern → Option String
  | .exist _ _ (.equals _ _ _ (.app h _ _)) => some h.ident.name
  | _ => none

/-- The signature of the interpreted symbol with the name of the sentence's symbol. -/
def sigOf (ad : AxiomDecl) : Option KCore.CtorSig :=
  (headOf ad.ax.pattern).bind fun n => hookSigs.find? fun k => regSymNames.getD k.name "" == n

/-- The sentence is the `functional` sentence of a symbol of `hookSigs` that is not partial, over
the one sort variable `R`. -/
def funOK (ad : AxiomDecl) : Bool :=
  match sigOf ad with
  | some k => decide (ad.ax.pattern = LibEv.funPatR k) && decide (ad.ax.sortVars = [Rv]) && LibEv.funReg k &&
      !partialHooks.contains k.name
  | none => false

theorem fun_checked : funText.all funOK = true := by decide +kernel

/-- None of the 47 reads a declaration or an alias. -/
theorem fun_trS : funText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **Ev for the `functional` sentences of the interpreted symbols**: each of the 47 holds in
every model of Γ at every valuation sending its variables to values, for every H. -/
theorem fun_entailed (H : HookParams) : ∀ ad ∈ funText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fun_trS ad had)]
  have hok := List.all_eq_true.mp fun_checked ad had
  unfold funOK at hok
  cases hsig : sigOf ad with
  | none => rw [hsig] at hok; cases hok
  | some k =>
    rw [hsig] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨hp, hsv⟩, hreg⟩, hpar⟩ := hok
    obtain ⟨n, -, hfind⟩ := Option.bind_eq_some_iff.mp hsig
    exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (List.mem_of_find?_eq_some hfind) (Or.inl hpar) hreg ad hp
      hsv

/-! ## Collection laws (9) -/

theorem law565 (H : HookParams) : EntailsAtValues (cH H) U.ax565 (trS U.ax565).pat := by
  rw [(by decide +kernel : (trS U.ax565).pat = (trAxiom [] [] U.ax565).pat)]
  exact LibEv.listAssoc_ev (coreOKH H) (shapesOKH H) U.ax565 (by decide +kernel) (by decide +kernel)
theorem law566 (H : HookParams) : EntailsAtValues (cH H) U.ax566 (trS U.ax566).pat := by
  rw [(by decide +kernel : (trS U.ax566).pat = (trAxiom [] [] U.ax566).pat)]
  exact LibEv.listUnitR_ev (coreOKH H) (shapesOKH H) U.ax566 (by decide +kernel) (by decide +kernel)
theorem law567 (H : HookParams) : EntailsAtValues (cH H) U.ax567 (trS U.ax567).pat := by
  rw [(by decide +kernel : (trS U.ax567).pat = (trAxiom [] [] U.ax567).pat)]
  exact LibEv.listUnitL_ev (coreOKH H) (shapesOKH H) U.ax567 (by decide +kernel) (by decide +kernel)
theorem law569 (H : HookParams) : EntailsAtValues (cH H) U.ax569 (trS U.ax569).pat := by
  rw [(by decide +kernel : (trS U.ax569).pat = (trAxiom [] [] U.ax569).pat)]
  exact LibEv.mapAssoc_ev (coreOKH H) (shapesOKH H) U.ax569 (by decide +kernel) (by decide +kernel)
theorem law570 (H : HookParams) : EntailsAtValues (cH H) U.ax570 (trS U.ax570).pat := by
  rw [(by decide +kernel : (trS U.ax570).pat = (trAxiom [] [] U.ax570).pat)]
  exact LibEv.mapUnitR_ev (coreOKH H) (shapesOKH H) U.ax570 (by decide +kernel) (by decide +kernel)
theorem law571 (H : HookParams) : EntailsAtValues (cH H) U.ax571 (trS U.ax571).pat := by
  rw [(by decide +kernel : (trS U.ax571).pat = (trAxiom [] [] U.ax571).pat)]
  exact LibEv.mapUnitL_ev (coreOKH H) (shapesOKH H) U.ax571 (by decide +kernel) (by decide +kernel)
theorem law572 (H : HookParams) : EntailsAtValues (cH H) U.ax572 (trS U.ax572).pat := by
  rw [(by decide +kernel : (trS U.ax572).pat = (trAxiom [] [] U.ax572).pat)]
  exact LibEv.setAssoc_ev (coreOKH H) (shapesOKH H) U.ax572 (by decide +kernel) (by decide +kernel)
theorem law574 (H : HookParams) : EntailsAtValues (cH H) U.ax574 (trS U.ax574).pat := by
  rw [(by decide +kernel : (trS U.ax574).pat = (trAxiom [] [] U.ax574).pat)]
  exact LibEv.setUnitR_ev (coreOKH H) (shapesOKH H) U.ax574 (by decide +kernel) (by decide +kernel)
theorem law575 (H : HookParams) : EntailsAtValues (cH H) U.ax575 (trS U.ax575).pat := by
  rw [(by decide +kernel : (trS U.ax575).pat = (trAxiom [] [] U.ax575).pat)]
  exact LibEv.setUnitL_ev (coreOKH H) (shapesOKH H) U.ax575 (by decide +kernel) (by decide +kernel)

/-- The nine collection laws of the text. -/
noncomputable def lawText : List AxiomDecl :=
  [U.ax565, U.ax566, U.ax567, U.ax569, U.ax570, U.ax571, U.ax572, U.ax574, U.ax575]

theorem law_indices : lawText.map (·.index) = [565, 566, 567, 569, 570, 571, 572, 574, 575] := by decide +kernel

/-- **Ev for the collection laws**, for every H. -/
theorem laws_entailed (H : HookParams) : ∀ ad ∈ lawText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨law565 H, List.forall_mem_cons.mpr ⟨law566 H, List.forall_mem_cons.mpr ⟨law567 H, List.forall_mem_cons.mpr ⟨law569 H, List.forall_mem_cons.mpr ⟨law570 H, List.forall_mem_cons.mpr ⟨law571 H, List.forall_mem_cons.mpr ⟨law572 H, List.forall_mem_cons.mpr ⟨law574 H, List.forall_mem_cons.mpr ⟨law575 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the predicate equations of the equality symbols (16) -/

/-- The indices of the sentences. -/
def predIdx : List Nat := [676, 677, 678, 679, 680, 681, 682, 683, 688, 689, 690, 691, 694, 695, 696, 697]

/-- The sentences, in text order. -/
noncomputable def predText : List AxiomDecl := U.all.filter fun ad => predIdx.contains ad.index

theorem pred_indices : predText.map (·.index) = [676, 677, 678, 679, 680, 681, 682, 683, 688, 689, 690, 691, 694, 695, 696, 697] := by decide +kernel

/-- The choices of symbol (equality or difference), literal and side of the literal. -/
def choices : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

/-- The eight equations of `==Int` and `=/=Int`. -/
def intCands : List LibEv.PredEqn :=
  choices.map fun x => LibEv.eqPred Srt.int (if x.1 then intNe else intEq) x.1 x.2.1 x.2.2

/-- The eight equations of `==K` and `=/=K`. -/
def kCands : List LibEv.PredEqn :=
  choices.map fun x => LibEv.eqPred Srt.k (if x.1 then kNe else kEq) x.1 x.2.1 x.2.2

/-- The sentence is one of the sixteen equations, over the sort variables `R` and `Q0`. -/
def predOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv, LibEv.Q0v]) &&
    (intCands ++ kCands).any fun E => decide (ad.ax.pattern = E.patR)

theorem pred_checked : predText.all predOK = true := by decide +kernel

/-- None of the 16 reads a declaration or an alias. -/
theorem pred_trS : predText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **Ev for the equality symbols' predicate equations**, for every H. -/
theorem pred_entailed (H : HookParams) : ∀ ad ∈ predText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp pred_trS ad had)]
  have hok := List.all_eq_true.mp pred_checked ad had
  simp only [predOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_append] at hok
  obtain ⟨hsv, E, hE, hp⟩ := hok
  rcases hE with hE | hE
  · simp only [intCands, List.mem_map] at hE
    obtain ⟨x, -, rfl⟩ := hE
    exact LibEv.intEqPred_ev (coreOKH H) (shapesOKH H) x.1 x.2.1 x.2.2 ad hp hsv
  · simp only [kCands, List.mem_map] at hE
    obtain ⟨x, -, rfl⟩ := hE
    exact LibEv.kEqPred_ev (coreOKH H) x.1 x.2.1 x.2.2 ad hp hsv

/-! ## Library: term and function equations (52) -/

theorem ev779 (H : HookParams) : EntailsAtValues (cH H) U.ax779 (trS U.ax779).pat := by
  rw [(by decide +kernel : (trS U.ax779).pat = (trAxiom [] [] U.ax779).pat)]
  exact LibEv.tmodSmall_ev (coreOKH H) (shapesOKH H) U.ax779 (by decide +kernel) (by decide +kernel)

theorem ev781 (H : HookParams) : EntailsAtValues (cH H) U.ax781 (trS U.ax781).pat := by
  rw [(by decide +kernel : (trS U.ax781).pat = (trAxiom [] [] U.ax781).pat)]
  exact LibEv.addComm_ev (coreOKH H) (shapesOKH H) U.ax781 (by decide +kernel) (by decide +kernel)

theorem ev782 (H : HookParams) : EntailsAtValues (cH H) U.ax782 (trS U.ax782).pat := by
  rw [(by decide +kernel : (trS U.ax782).pat = (trAxiom [] [] U.ax782).pat)]
  exact LibEv.addZero_ev (coreOKH H) (shapesOKH H) U.ax782 (by decide +kernel) (by decide +kernel)

theorem ev783 (H : HookParams) : EntailsAtValues (cH H) U.ax783 (trS U.ax783).pat := by
  rw [(by decide +kernel : (trS U.ax783).pat = (trAxiom [] [] U.ax783).pat)]
  exact LibEv.addLeftComm_ev (coreOKH H) (shapesOKH H) U.ax783 (by decide +kernel) (by decide +kernel)

theorem ev784 (H : HookParams) : EntailsAtValues (cH H) U.ax784 (trS U.ax784).pat := by
  rw [(by decide +kernel : (trS U.ax784).pat = (trAxiom [] [] U.ax784).pat)]
  exact LibEv.addAssocRev_ev (coreOKH H) (shapesOKH H) U.ax784 (by decide +kernel) (by decide +kernel)

theorem ev785 (H : HookParams) : EntailsAtValues (cH H) U.ax785 (trS U.ax785).pat := by
  rw [(by decide +kernel : (trS U.ax785).pat = (trAxiom [] [] U.ax785).pat)]
  exact LibEv.addSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax785 (by decide +kernel) (by decide +kernel)

theorem ev786 (H : HookParams) : EntailsAtValues (cH H) U.ax786 (trS U.ax786).pat := by
  rw [(by decide +kernel : (trS U.ax786).pat = (trAxiom [] [] U.ax786).pat)]
  exact LibEv.addAssoc_ev (coreOKH H) (shapesOKH H) U.ax786 (by decide +kernel) (by decide +kernel)

theorem ev787 (H : HookParams) : EntailsAtValues (cH H) U.ax787 (trS U.ax787).pat := by
  rw [(by decide +kernel : (trS U.ax787).pat = (trAxiom [] [] U.ax787).pat)]
  exact LibEv.subAddComm_ev (coreOKH H) (shapesOKH H) U.ax787 (by decide +kernel) (by decide +kernel)

theorem ev788 (H : HookParams) : EntailsAtValues (cH H) U.ax788 (trS U.ax788).pat := by
  rw [(by decide +kernel : (trS U.ax788).pat = (trAxiom [] [] U.ax788).pat)]
  exact LibEv.subAsAdd_ev (coreOKH H) (shapesOKH H) U.ax788 (by decide +kernel) (by decide +kernel)

theorem ev789 (H : HookParams) : EntailsAtValues (cH H) U.ax789 (trS U.ax789).pat := by
  rw [(by decide +kernel : (trS U.ax789).pat = (trAxiom [] [] U.ax789).pat)]
  exact LibEv.subZero_ev (coreOKH H) (shapesOKH H) U.ax789 (by decide +kernel) (by decide +kernel)

theorem ev790 (H : HookParams) : EntailsAtValues (cH H) U.ax790 (trS U.ax790).pat := by
  rw [(by decide +kernel : (trS U.ax790).pat = (trAxiom [] [] U.ax790).pat)]
  exact LibEv.subAddSwap_ev (coreOKH H) (shapesOKH H) U.ax790 (by decide +kernel) (by decide +kernel)

theorem ev791 (H : HookParams) : EntailsAtValues (cH H) U.ax791 (trS U.ax791).pat := by
  rw [(by decide +kernel : (trS U.ax791).pat = (trAxiom [] [] U.ax791).pat)]
  exact LibEv.subAddAssoc_ev (coreOKH H) (shapesOKH H) U.ax791 (by decide +kernel) (by decide +kernel)

theorem ev792 (H : HookParams) : EntailsAtValues (cH H) U.ax792 (trS U.ax792).pat := by
  rw [(by decide +kernel : (trS U.ax792).pat = (trAxiom [] [] U.ax792).pat)]
  exact LibEv.subSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax792 (by decide +kernel) (by decide +kernel)

theorem ev793 (H : HookParams) : EntailsAtValues (cH H) U.ax793 (trS U.ax793).pat := by
  rw [(by decide +kernel : (trS U.ax793).pat = (trAxiom [] [] U.ax793).pat)]
  exact LibEv.subSubAdd_ev (coreOKH H) (shapesOKH H) U.ax793 (by decide +kernel) (by decide +kernel)

theorem ev796 (H : HookParams) : EntailsAtValues (cH H) U.ax796 (trS U.ax796).pat := by
  rw [(by decide +kernel : (trS U.ax796).pat = (trAxiom [] [] U.ax796).pat)]
  exact LibEv.fnNeBool_ev (coreOKH H) (shapesOKH H) U.ax796 (by decide +kernel) (by decide +kernel)

theorem ev797 (H : HookParams) : EntailsAtValues (cH H) U.ax797 (trS U.ax797).pat := by
  rw [(by decide +kernel : (trS U.ax797).pat = (trAxiom [] [] U.ax797).pat)]
  exact LibEv.fnNeInt_ev (coreOKH H) (shapesOKH H) U.ax797 (by decide +kernel) (by decide +kernel)

theorem ev798 (H : HookParams) : EntailsAtValues (cH H) U.ax798 (trS U.ax798).pat := by
  rw [(by decide +kernel : (trS U.ax798).pat = (trAxiom [] [] U.ax798).pat)]
  exact LibEv.fnNeK_ev (coreOKH H) U.ax798 (by decide +kernel) (by decide +kernel)

theorem ev799 (H : HookParams) : EntailsAtValues (cH H) U.ax799 (trS U.ax799).pat := by
  rw [(by decide +kernel : (trS U.ax799).pat = (trAxiom [] [] U.ax799).pat)]
  exact LibEv.boolKEq_ev (coreOKH H) (shapesOKH H) (boolBelowH H) U.ax799 (by decide +kernel)
    (by decide +kernel)

theorem ev800 (H : HookParams) : EntailsAtValues (cH H) U.ax800 (trS U.ax800).pat := by
  rw [(by decide +kernel : (trS U.ax800).pat = (trAxiom [] [] U.ax800).pat)]
  exact LibEv.intKEq_ev (coreOKH H) (shapesOKH H) (intBelowH H) U.ax800 (by decide +kernel)
    (by decide +kernel)

theorem ev803 (H : HookParams) : EntailsAtValues (cH H) U.ax803 (trS U.ax803).pat := by
  rw [(by decide +kernel : (trS U.ax803).pat = (trAxiom [] [] U.ax803).pat)]
  exact LibEv.fnAndFalse_ev (coreOKH H) (shapesOKH H) U.ax803 (by decide +kernel) (by decide +kernel)

theorem ev804 (H : HookParams) : EntailsAtValues (cH H) U.ax804 (trS U.ax804).pat := by
  rw [(by decide +kernel : (trS U.ax804).pat = (trAxiom [] [] U.ax804).pat)]
  exact LibEv.bAndTrue_ev (coreOKH H) (shapesOKH H) U.ax804 (by decide +kernel) (by decide +kernel)

theorem ev805 (H : HookParams) : EntailsAtValues (cH H) U.ax805 (trS U.ax805).pat := by
  rw [(by decide +kernel : (trS U.ax805).pat = (trAxiom [] [] U.ax805).pat)]
  exact LibEv.bAndFalse_ev (coreOKH H) (shapesOKH H) U.ax805 (by decide +kernel) (by decide +kernel)

theorem ev806 (H : HookParams) : EntailsAtValues (cH H) U.ax806 (trS U.ax806).pat := by
  rw [(by decide +kernel : (trS U.ax806).pat = (trAxiom [] [] U.ax806).pat)]
  exact LibEv.fnAndTrue_ev (coreOKH H) (shapesOKH H) U.ax806 (by decide +kernel) (by decide +kernel)

theorem ev807 (H : HookParams) : EntailsAtValues (cH H) U.ax807 (trS U.ax807).pat := by
  rw [(by decide +kernel : (trS U.ax807).pat = (trAxiom [] [] U.ax807).pat)]
  exact LibEv.fnAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax807 (by decide +kernel) (by decide +kernel)

theorem ev808 (H : HookParams) : EntailsAtValues (cH H) U.ax808 (trS U.ax808).pat := by
  rw [(by decide +kernel : (trS U.ax808).pat = (trAxiom [] [] U.ax808).pat)]
  exact LibEv.bAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax808 (by decide +kernel) (by decide +kernel)

theorem ev809 (H : HookParams) : EntailsAtValues (cH H) U.ax809 (trS U.ax809).pat := by
  rw [(by decide +kernel : (trS U.ax809).pat = (trAxiom [] [] U.ax809).pat)]
  exact LibEv.bAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax809 (by decide +kernel) (by decide +kernel)

theorem ev810 (H : HookParams) : EntailsAtValues (cH H) U.ax810 (trS U.ax810).pat := by
  rw [(by decide +kernel : (trS U.ax810).pat = (trAxiom [] [] U.ax810).pat)]
  exact LibEv.fnAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax810 (by decide +kernel) (by decide +kernel)

theorem ev811 (H : HookParams) : EntailsAtValues (cH H) U.ax811 (trS U.ax811).pat := by
  rw [(by decide +kernel : (trS U.ax811).pat = (trAxiom [] [] U.ax811).pat)]
  exact LibEv.fnDivInt_ev (coreOKH H) (shapesOKH H) U.ax811 (by decide +kernel) (by decide +kernel)

theorem ev813 (H : HookParams) : EntailsAtValues (cH H) U.ax813 (trS U.ax813).pat := by
  rw [(by decide +kernel : (trS U.ax813).pat = (trAxiom [] [] U.ax813).pat)]
  exact LibEv.bImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax813 (by decide +kernel) (by decide +kernel)

theorem ev814 (H : HookParams) : EntailsAtValues (cH H) U.ax814 (trS U.ax814).pat := by
  rw [(by decide +kernel : (trS U.ax814).pat = (trAxiom [] [] U.ax814).pat)]
  exact LibEv.bImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax814 (by decide +kernel) (by decide +kernel)

theorem ev815 (H : HookParams) : EntailsAtValues (cH H) U.ax815 (trS U.ax815).pat := by
  rw [(by decide +kernel : (trS U.ax815).pat = (trAxiom [] [] U.ax815).pat)]
  exact LibEv.fnImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax815 (by decide +kernel) (by decide +kernel)

theorem ev816 (H : HookParams) : EntailsAtValues (cH H) U.ax816 (trS U.ax816).pat := by
  rw [(by decide +kernel : (trS U.ax816).pat = (trAxiom [] [] U.ax816).pat)]
  exact LibEv.fnImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax816 (by decide +kernel) (by decide +kernel)

theorem ev817 (H : HookParams) : EntailsAtValues (cH H) U.ax817 (trS U.ax817).pat := by
  rw [(by decide +kernel : (trS U.ax817).pat = (trAxiom [] [] U.ax817).pat)]
  exact LibEv.emodAsTmod_ev (coreOKH H) (shapesOKH H) U.ax817 (by decide +kernel) (by decide +kernel)

theorem ev818 (H : HookParams) : EntailsAtValues (cH H) U.ax818 (trS U.ax818).pat := by
  rw [(by decide +kernel : (trS U.ax818).pat = (trAxiom [] [] U.ax818).pat)]
  exact LibEv.emodSmall_ev (coreOKH H) (shapesOKH H) U.ax818 (by decide +kernel) (by decide +kernel)

theorem ev819 (H : HookParams) : EntailsAtValues (cH H) U.ax819 (trS U.ax819).pat := by
  rw [(by decide +kernel : (trS U.ax819).pat = (trAxiom [] [] U.ax819).pat)]
  exact LibEv.bOrFalse_ev (coreOKH H) (shapesOKH H) U.ax819 (by decide +kernel) (by decide +kernel)

theorem ev820 (H : HookParams) : EntailsAtValues (cH H) U.ax820 (trS U.ax820).pat := by
  rw [(by decide +kernel : (trS U.ax820).pat = (trAxiom [] [] U.ax820).pat)]
  exact LibEv.bOrTrue_ev (coreOKH H) (shapesOKH H) U.ax820 (by decide +kernel) (by decide +kernel)

theorem ev821 (H : HookParams) : EntailsAtValues (cH H) U.ax821 (trS U.ax821).pat := by
  rw [(by decide +kernel : (trS U.ax821).pat = (trAxiom [] [] U.ax821).pat)]
  exact LibEv.fnOrFalse_ev (coreOKH H) (shapesOKH H) U.ax821 (by decide +kernel) (by decide +kernel)

theorem ev822 (H : HookParams) : EntailsAtValues (cH H) U.ax822 (trS U.ax822).pat := by
  rw [(by decide +kernel : (trS U.ax822).pat = (trAxiom [] [] U.ax822).pat)]
  exact LibEv.fnOrTrue_ev (coreOKH H) (shapesOKH H) U.ax822 (by decide +kernel) (by decide +kernel)

theorem ev823 (H : HookParams) : EntailsAtValues (cH H) U.ax823 (trS U.ax823).pat := by
  rw [(by decide +kernel : (trS U.ax823).pat = (trAxiom [] [] U.ax823).pat)]
  exact LibEv.bOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax823 (by decide +kernel) (by decide +kernel)

theorem ev824 (H : HookParams) : EntailsAtValues (cH H) U.ax824 (trS U.ax824).pat := by
  rw [(by decide +kernel : (trS U.ax824).pat = (trAxiom [] [] U.ax824).pat)]
  exact LibEv.bOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax824 (by decide +kernel) (by decide +kernel)

theorem ev825 (H : HookParams) : EntailsAtValues (cH H) U.ax825 (trS U.ax825).pat := by
  rw [(by decide +kernel : (trS U.ax825).pat = (trAxiom [] [] U.ax825).pat)]
  exact LibEv.fnOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax825 (by decide +kernel) (by decide +kernel)

theorem ev826 (H : HookParams) : EntailsAtValues (cH H) U.ax826 (trS U.ax826).pat := by
  rw [(by decide +kernel : (trS U.ax826).pat = (trAxiom [] [] U.ax826).pat)]
  exact LibEv.fnOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax826 (by decide +kernel) (by decide +kernel)

theorem ev827 (H : HookParams) : EntailsAtValues (cH H) U.ax827 (trS U.ax827).pat := by
  rw [(by decide +kernel : (trS U.ax827).pat = (trAxiom [] [] U.ax827).pat)]
  exact LibEv.fnXorSame_ev (coreOKH H) (shapesOKH H) U.ax827 (by decide +kernel) (by decide +kernel)

theorem ev828 (H : HookParams) : EntailsAtValues (cH H) U.ax828 (trS U.ax828).pat := by
  rw [(by decide +kernel : (trS U.ax828).pat = (trAxiom [] [] U.ax828).pat)]
  exact LibEv.bXorFalse_ev (coreOKH H) (shapesOKH H) U.ax828 (by decide +kernel) (by decide +kernel)

theorem ev829 (H : HookParams) : EntailsAtValues (cH H) U.ax829 (trS U.ax829).pat := by
  rw [(by decide +kernel : (trS U.ax829).pat = (trAxiom [] [] U.ax829).pat)]
  exact LibEv.fnXorFalse_ev (coreOKH H) (shapesOKH H) U.ax829 (by decide +kernel) (by decide +kernel)

theorem ev830 (H : HookParams) : EntailsAtValues (cH H) U.ax830 (trS U.ax830).pat := by
  rw [(by decide +kernel : (trS U.ax830).pat = (trAxiom [] [] U.ax830).pat)]
  exact LibEv.fnSetUnion_ev (coreOKH H) (shapesOKH H) U.ax830 (by decide +kernel) (by decide +kernel)

theorem ev832 (H : HookParams) : EntailsAtValues (cH H) U.ax832 (trS U.ax832).pat := by
  rw [(by decide +kernel : (trS U.ax832).pat = (trAxiom [] [] U.ax832).pat)]
  exact LibEv.fnFreshInt_ev (coreOKH H) (shapesOKH H) U.ax832 (by decide +kernel) (by decide +kernel)

theorem ev879 (H : HookParams) : EntailsAtValues (cH H) U.ax879 (trS U.ax879).pat := by
  rw [(by decide +kernel : (trS U.ax879).pat = (trAxiom [] [] U.ax879).pat)]
  exact LibEv.fnMinLt_ev (coreOKH H) (shapesOKH H) U.ax879 (by decide +kernel) (by decide +kernel)

theorem ev880 (H : HookParams) : EntailsAtValues (cH H) U.ax880 (trS U.ax880).pat := by
  rw [(by decide +kernel : (trS U.ax880).pat = (trAxiom [] [] U.ax880).pat)]
  exact LibEv.fnMinGe_ev (coreOKH H) (shapesOKH H) U.ax880 (by decide +kernel) (by decide +kernel)

theorem ev881 (H : HookParams) : EntailsAtValues (cH H) U.ax881 (trS U.ax881).pat := by
  rw [(by decide +kernel : (trS U.ax881).pat = (trAxiom [] [] U.ax881).pat)]
  exact LibEv.fnNotFalse_ev (coreOKH H) U.ax881 (by decide +kernel) (by decide +kernel)

theorem ev882 (H : HookParams) : EntailsAtValues (cH H) U.ax882 (trS U.ax882).pat := by
  rw [(by decide +kernel : (trS U.ax882).pat = (trAxiom [] [] U.ax882).pat)]
  exact LibEv.fnNotTrue_ev (coreOKH H) U.ax882 (by decide +kernel) (by decide +kernel)

theorem ev902 (H : HookParams) : EntailsAtValues (cH H) U.ax902 (trS U.ax902).pat := by
  rw [(by decide +kernel : (trS U.ax902).pat = (trAxiom [] [] U.ax902).pat)]
  exact LibEv.fnPushList_ev (coreOKH H) (shapesOKH H) U.ax902 (by decide +kernel) (by decide +kernel)

/-- The 52 sentences of `evN`. -/
noncomputable def evText : List AxiomDecl :=
  [U.ax779, U.ax781, U.ax782, U.ax783, U.ax784, U.ax785, U.ax786, U.ax787, U.ax788, U.ax789,
   U.ax790, U.ax791, U.ax792, U.ax793, U.ax796, U.ax797, U.ax798, U.ax799, U.ax800, U.ax803,
   U.ax804, U.ax805, U.ax806, U.ax807, U.ax808, U.ax809, U.ax810, U.ax811, U.ax813, U.ax814,
   U.ax815, U.ax816, U.ax817, U.ax818, U.ax819, U.ax820, U.ax821, U.ax822, U.ax823, U.ax824,
   U.ax825, U.ax826, U.ax827, U.ax828, U.ax829, U.ax830, U.ax832, U.ax879, U.ax880, U.ax881,
   U.ax882, U.ax902]

theorem ev_entailed (H : HookParams) : ∀ ad ∈ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev779 H, List.forall_mem_cons.mpr ⟨ev781 H, List.forall_mem_cons.mpr ⟨ev782 H, List.forall_mem_cons.mpr ⟨ev783 H, List.forall_mem_cons.mpr ⟨ev784 H, List.forall_mem_cons.mpr ⟨ev785 H, List.forall_mem_cons.mpr ⟨ev786 H, List.forall_mem_cons.mpr ⟨ev787 H, List.forall_mem_cons.mpr ⟨ev788 H, List.forall_mem_cons.mpr ⟨ev789 H, List.forall_mem_cons.mpr ⟨ev790 H, List.forall_mem_cons.mpr ⟨ev791 H, List.forall_mem_cons.mpr ⟨ev792 H, List.forall_mem_cons.mpr ⟨ev793 H, List.forall_mem_cons.mpr ⟨ev796 H, List.forall_mem_cons.mpr ⟨ev797 H, List.forall_mem_cons.mpr ⟨ev798 H, List.forall_mem_cons.mpr ⟨ev799 H, List.forall_mem_cons.mpr ⟨ev800 H, List.forall_mem_cons.mpr ⟨ev803 H, List.forall_mem_cons.mpr ⟨ev804 H, List.forall_mem_cons.mpr ⟨ev805 H, List.forall_mem_cons.mpr ⟨ev806 H, List.forall_mem_cons.mpr ⟨ev807 H, List.forall_mem_cons.mpr ⟨ev808 H, List.forall_mem_cons.mpr ⟨ev809 H, List.forall_mem_cons.mpr ⟨ev810 H, List.forall_mem_cons.mpr ⟨ev811 H, List.forall_mem_cons.mpr ⟨ev813 H, List.forall_mem_cons.mpr ⟨ev814 H, List.forall_mem_cons.mpr ⟨ev815 H, List.forall_mem_cons.mpr ⟨ev816 H, List.forall_mem_cons.mpr ⟨ev817 H, List.forall_mem_cons.mpr ⟨ev818 H, List.forall_mem_cons.mpr ⟨ev819 H, List.forall_mem_cons.mpr ⟨ev820 H, List.forall_mem_cons.mpr ⟨ev821 H, List.forall_mem_cons.mpr ⟨ev822 H, List.forall_mem_cons.mpr ⟨ev823 H, List.forall_mem_cons.mpr ⟨ev824 H, List.forall_mem_cons.mpr ⟨ev825 H, List.forall_mem_cons.mpr ⟨ev826 H, List.forall_mem_cons.mpr ⟨ev827 H, List.forall_mem_cons.mpr ⟨ev828 H, List.forall_mem_cons.mpr ⟨ev829 H, List.forall_mem_cons.mpr ⟨ev830 H, List.forall_mem_cons.mpr ⟨ev832 H, List.forall_mem_cons.mpr ⟨ev879 H, List.forall_mem_cons.mpr ⟨ev880 H, List.forall_mem_cons.mpr ⟨ev881 H, List.forall_mem_cons.mpr ⟨ev882 H, List.forall_mem_cons.mpr ⟨ev902 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the Bool predicate sentences over set variables (8), at set values -/

theorem ev684 (H : HookParams) : EntailsAtSetValues (cH H) U.ax684 (trS U.ax684).pat := by
  rw [(by decide +kernel : (trS U.ax684).pat = (trAxiom [] [] U.ax684).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) false U.ax684 (by decide +kernel) (by decide +kernel)

theorem ev685 (H : HookParams) : EntailsAtSetValues (cH H) U.ax685 (trS U.ax685).pat := by
  rw [(by decide +kernel : (trS U.ax685).pat = (trAxiom [] [] U.ax685).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) false U.ax685 (by decide +kernel) (by decide +kernel)

theorem ev686 (H : HookParams) : EntailsAtSetValues (cH H) U.ax686 (trS U.ax686).pat := by
  rw [(by decide +kernel : (trS U.ax686).pat = (trAxiom [] [] U.ax686).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false false U.ax686 (by decide +kernel) (by decide +kernel)

theorem ev687 (H : HookParams) : EntailsAtSetValues (cH H) U.ax687 (trS U.ax687).pat := by
  rw [(by decide +kernel : (trS U.ax687).pat = (trAxiom [] [] U.ax687).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true false U.ax687 (by decide +kernel) (by decide +kernel)

theorem ev692 (H : HookParams) : EntailsAtSetValues (cH H) U.ax692 (trS U.ax692).pat := by
  rw [(by decide +kernel : (trS U.ax692).pat = (trAxiom [] [] U.ax692).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) true U.ax692 (by decide +kernel) (by decide +kernel)

theorem ev693 (H : HookParams) : EntailsAtSetValues (cH H) U.ax693 (trS U.ax693).pat := by
  rw [(by decide +kernel : (trS U.ax693).pat = (trAxiom [] [] U.ax693).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false true U.ax693 (by decide +kernel) (by decide +kernel)

theorem ev698 (H : HookParams) : EntailsAtSetValues (cH H) U.ax698 (trS U.ax698).pat := by
  rw [(by decide +kernel : (trS U.ax698).pat = (trAxiom [] [] U.ax698).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) true U.ax698 (by decide +kernel) (by decide +kernel)

theorem ev699 (H : HookParams) : EntailsAtSetValues (cH H) U.ax699 (trS U.ax699).pat := by
  rw [(by decide +kernel : (trS U.ax699).pat = (trAxiom [] [] U.ax699).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true true U.ax699 (by decide +kernel) (by decide +kernel)

/-- The eight sentences over set variables. -/
noncomputable def setText : List AxiomDecl :=
  [U.ax684, U.ax685, U.ax686, U.ax687, U.ax692, U.ax693, U.ax698, U.ax699]

/-! ## The class -/

/-- **Ev for the library sentences over element variables**: the 16 predicate equations and the 52
term and function equations, for every H. -/
theorem lib_entailed (H : HookParams) : ∀ ad ∈ predText ++ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  fun ad had => (List.mem_append.mp had).elim (pred_entailed H ad) (ev_entailed H ad)

/-- **The library sentences over set variables are entailed at set values**, for every H. -/
theorem libSet_entailed (H : HookParams) : ∀ ad ∈ setText, EntailsAtSetValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev684 H, List.forall_mem_cons.mpr ⟨ev685 H, List.forall_mem_cons.mpr ⟨ev686 H, List.forall_mem_cons.mpr ⟨ev687 H, List.forall_mem_cons.mpr ⟨ev692 H, List.forall_mem_cons.mpr ⟨ev693 H, List.forall_mem_cons.mpr ⟨ev698 H, List.forall_mem_cons.mpr ⟨ev699 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩

/-- The 76 library sentences tied here. -/
theorem lib_indices : (predText ++ evText ++ setText).map (·.index) =
    [676, 677, 678, 679, 680, 681, 682, 683, 688, 689, 690, 691, 694, 695, 696, 697, 779, 781, 782, 783,
   784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 796, 797, 798, 799, 800, 803, 804, 805, 806, 807,
   808, 809, 810, 811, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828,
   829, 830, 832, 879, 880, 881, 882, 902, 684, 685, 686, 687, 692, 693, 698, 699] := by
  decide +kernel

end KCore.TieKimpAtValues

/-- info: 'KCore.TieKimpAtValues.fun_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpAtValues.fun_entailed
/-- info: 'KCore.TieKimpAtValues.laws_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpAtValues.laws_entailed
/-- info: 'KCore.TieKimpAtValues.lib_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpAtValues.lib_entailed
/-- info: 'KCore.TieKimpAtValues.libSet_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKimpAtValues.libSet_entailed
