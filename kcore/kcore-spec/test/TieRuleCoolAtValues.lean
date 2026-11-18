/-
  The classes hooked functional, collection law and library entailed at values, and the class
  set-variable lemma refuted, on `f2-examples/rulecool.kompile.kore` (fixture e2-rule), for every
  interpretation H. Each sentence is tied by the library's one statement of it (KcoreSpec/LibEv*.lean):
  the text's axiom is compared with the statement's pattern over the registry's names, and its
  translation with the text's declarations with the translation the statement is about.
  Run from the package root: `lake env lean -j1 test/TieRuleCoolAtValues.lean`.

  The library part of this text is kimp's (`examples/ref-kimp/RefKimp/definition.kore`) sentence for
  sentence up to Location, Source and UNIQUE_ID attributes; the sections below are
  test/TieKimpAtValues.lean's and the set-variable section of test/TieKimpRefuted.lean over this
  text's indices.

  - Hooked functional (`fun_entailed`, `fun_indices`): the 47 sentences
    `\exists{R}(Val:s, \equals{s, R}(Val:s, f(K0:s0, …)))` whose symbol is an interpreted hooked
    symbol that is not partial (`LibEv.functional_ev`). Owed: 109, the sentence of `ite`, which the
    text states once over a sort variable (`axiom{R, SortSort}`): it is not the functional sentence
    of a signature of `hookSigs`, whose sorts are the registry's, and the library states none of it.
  - Collection law (`laws_entailed`, `law_indices`): associativity and the two units of `_List_`,
    `_Map_`, `_Set_` (56 to 58, 60 to 63, 65, 66), the nine sentences of the class.
  - Library (`lib_entailed`, `libSet_entailed`, `lib_indices`): 80 of the class's 84. The sixteen
    predicate equations of `==Int`, `=/=Int`, `==K`, `=/=K` (`pred_entailed`); 56 term and function
    equations, each by its own theorem (`evN`); the eight Bool predicate sentences over set
    variables, entailed at set values (`EntailsAtSetValues`), which `libSet_entailed` states. Owed:
    262, 263 (`ite{SortK}` at a condition `true` or `false`), `ite` at the sort K, of which the
    library states no equation; 225, 284, the equations of `bitRangeInt` and
    `signExtendBitRangeInt`, interpreted symbols of which the library states no equation.
  - Set-variable lemmas (`sN_refuted`, `sN_one`, `setvar_indices`): 135 (`%Int`), 136 (`/Int`),
    139 (`modInt`) at `@I1 = {0}`, `@I2 = {1, 0}`; 137 (`<<Int`), 138 (`>>Int`) at `@I1 = {0}`,
    `@I2 = {0, -1}`; 285, kompile's `#Ceil(@K0 |-> @K1 @Rest)` lemma, at `@K0 = @K1 = {0}`,
    `@Rest = {.Map, 0 |-> 0}`. Each fails in every model of Γ at that valuation (`sN_at`), so Γ with
    it has no model (`sN_refuted`), and it holds where its set variables hold at most one element
    (`sN_one`).
  - The accounts (`hooked_account`, `law_account`, `library_account`, `setvar_account`): the tied
    sentences with the owed ones are the class lists of test/TieRuleCoolText.lean (`classes`).
  - The function functional class (the 16 sort predicates' `functional` sentences, isKResult's 105
    among them) is not tied: its direction is a hypothesis, `FnHyp`, which test/TieRuleCool.lean
    shows for every H (`fnHypH`); no theorem here relates the 15 sentences to it.

  The definition reads a confined sort (HOLE is left open), so its theory is `Γc = Γ ∪ Γcl`.
  Every statement above is over Γ; a model of `Γc` is one of Γ, so each holds over `Γc` as well
  (the `_c` forms at the end).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleCoolAtValues

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rulecool.kompile.kore"
definition_of defn from "f2-examples/rulecool.kompile.kore"
user_axioms U from "f2-examples/rulecool.kompile.kore" module "E2-RULE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)
theorem boolBelowH (H : HookParams) : Srt.bool ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.bool = true)
theorem intBelowH (H : HookParams) : Srt.int ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.int = true)

/-! ## Hooked functional (47 of 48; 109, `ite`'s, owed) -/

/-- The indices of the sentences. -/
def funIdx : List Nat :=
  [22, 23, 24, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 46, 47, 48, 49, 50, 51, 52,
   53, 54, 55, 59, 67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 79, 84, 90, 92, 110, 111,
   112, 115, 116, 117, 118, 119, 120]

/-- The sentences, in text order. -/
noncomputable def funText : List AxiomDecl := U.all.filter fun ad => funIdx.contains ad.index

theorem fun_indices : funText.map (·.index) =
    [22, 23, 24, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 46, 47, 48, 49, 50, 51, 52,
     53, 54, 55, 59, 67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 79, 84, 90, 92, 110, 111,
     112, 115, 116, 117, 118, 119, 120] := by
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

theorem law56 (H : HookParams) : EntailsAtValues (cH H) U.ax56 (trS U.ax56).pat := by
  rw [(by decide +kernel : (trS U.ax56).pat = (trAxiom [] [] U.ax56).pat)]
  exact LibEv.listAssoc_ev (coreOKH H) (shapesOKH H) U.ax56 (by decide +kernel) (by decide +kernel)
theorem law57 (H : HookParams) : EntailsAtValues (cH H) U.ax57 (trS U.ax57).pat := by
  rw [(by decide +kernel : (trS U.ax57).pat = (trAxiom [] [] U.ax57).pat)]
  exact LibEv.listUnitR_ev (coreOKH H) (shapesOKH H) U.ax57 (by decide +kernel) (by decide +kernel)
theorem law58 (H : HookParams) : EntailsAtValues (cH H) U.ax58 (trS U.ax58).pat := by
  rw [(by decide +kernel : (trS U.ax58).pat = (trAxiom [] [] U.ax58).pat)]
  exact LibEv.listUnitL_ev (coreOKH H) (shapesOKH H) U.ax58 (by decide +kernel) (by decide +kernel)
theorem law60 (H : HookParams) : EntailsAtValues (cH H) U.ax60 (trS U.ax60).pat := by
  rw [(by decide +kernel : (trS U.ax60).pat = (trAxiom [] [] U.ax60).pat)]
  exact LibEv.mapAssoc_ev (coreOKH H) (shapesOKH H) U.ax60 (by decide +kernel) (by decide +kernel)
theorem law61 (H : HookParams) : EntailsAtValues (cH H) U.ax61 (trS U.ax61).pat := by
  rw [(by decide +kernel : (trS U.ax61).pat = (trAxiom [] [] U.ax61).pat)]
  exact LibEv.mapUnitR_ev (coreOKH H) (shapesOKH H) U.ax61 (by decide +kernel) (by decide +kernel)
theorem law62 (H : HookParams) : EntailsAtValues (cH H) U.ax62 (trS U.ax62).pat := by
  rw [(by decide +kernel : (trS U.ax62).pat = (trAxiom [] [] U.ax62).pat)]
  exact LibEv.mapUnitL_ev (coreOKH H) (shapesOKH H) U.ax62 (by decide +kernel) (by decide +kernel)
theorem law63 (H : HookParams) : EntailsAtValues (cH H) U.ax63 (trS U.ax63).pat := by
  rw [(by decide +kernel : (trS U.ax63).pat = (trAxiom [] [] U.ax63).pat)]
  exact LibEv.setAssoc_ev (coreOKH H) (shapesOKH H) U.ax63 (by decide +kernel) (by decide +kernel)
theorem law65 (H : HookParams) : EntailsAtValues (cH H) U.ax65 (trS U.ax65).pat := by
  rw [(by decide +kernel : (trS U.ax65).pat = (trAxiom [] [] U.ax65).pat)]
  exact LibEv.setUnitR_ev (coreOKH H) (shapesOKH H) U.ax65 (by decide +kernel) (by decide +kernel)
theorem law66 (H : HookParams) : EntailsAtValues (cH H) U.ax66 (trS U.ax66).pat := by
  rw [(by decide +kernel : (trS U.ax66).pat = (trAxiom [] [] U.ax66).pat)]
  exact LibEv.setUnitL_ev (coreOKH H) (shapesOKH H) U.ax66 (by decide +kernel) (by decide +kernel)

/-- The nine collection laws of the text. -/
noncomputable def lawText : List AxiomDecl :=
  [U.ax56, U.ax57, U.ax58, U.ax60, U.ax61, U.ax62, U.ax63, U.ax65, U.ax66]

theorem law_indices : lawText.map (·.index) = [56, 57, 58, 60, 61, 62, 63, 65, 66] := by decide +kernel

/-- **Ev for the collection laws**, for every H. -/
theorem laws_entailed (H : HookParams) : ∀ ad ∈ lawText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨law56 H, List.forall_mem_cons.mpr ⟨law57 H, List.forall_mem_cons.mpr ⟨law58 H, List.forall_mem_cons.mpr ⟨law60 H, List.forall_mem_cons.mpr ⟨law61 H, List.forall_mem_cons.mpr ⟨law62 H, List.forall_mem_cons.mpr ⟨law63 H, List.forall_mem_cons.mpr ⟨law65 H, List.forall_mem_cons.mpr ⟨law66 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the predicate equations of the equality symbols (16) -/

/-- The indices of the sentences. -/
def predIdx : List Nat := [140, 141, 142, 143, 144, 145, 146, 147, 152, 153, 154, 155, 158, 159, 160, 161]

/-- The sentences, in text order. -/
noncomputable def predText : List AxiomDecl := U.all.filter fun ad => predIdx.contains ad.index

theorem pred_indices : predText.map (·.index) = [140, 141, 142, 143, 144, 145, 146, 147, 152, 153, 154, 155, 158, 159, 160, 161] := by decide +kernel

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

/-! ## Library: term and function equations (56) -/

theorem ev173 (H : HookParams) : EntailsAtValues (cH H) U.ax173 (trS U.ax173).pat := by
  rw [(by decide +kernel : (trS U.ax173).pat = (trAxiom [] [] U.ax173).pat)]
  exact LibEv.tmodSmall_ev (coreOKH H) (shapesOKH H) U.ax173 (by decide +kernel) (by decide +kernel)

theorem ev175 (H : HookParams) : EntailsAtValues (cH H) U.ax175 (trS U.ax175).pat := by
  rw [(by decide +kernel : (trS U.ax175).pat = (trAxiom [] [] U.ax175).pat)]
  exact LibEv.addComm_ev (coreOKH H) (shapesOKH H) U.ax175 (by decide +kernel) (by decide +kernel)

theorem ev176 (H : HookParams) : EntailsAtValues (cH H) U.ax176 (trS U.ax176).pat := by
  rw [(by decide +kernel : (trS U.ax176).pat = (trAxiom [] [] U.ax176).pat)]
  exact LibEv.addZero_ev (coreOKH H) (shapesOKH H) U.ax176 (by decide +kernel) (by decide +kernel)

theorem ev177 (H : HookParams) : EntailsAtValues (cH H) U.ax177 (trS U.ax177).pat := by
  rw [(by decide +kernel : (trS U.ax177).pat = (trAxiom [] [] U.ax177).pat)]
  exact LibEv.addLeftComm_ev (coreOKH H) (shapesOKH H) U.ax177 (by decide +kernel) (by decide +kernel)

theorem ev178 (H : HookParams) : EntailsAtValues (cH H) U.ax178 (trS U.ax178).pat := by
  rw [(by decide +kernel : (trS U.ax178).pat = (trAxiom [] [] U.ax178).pat)]
  exact LibEv.addAssocRev_ev (coreOKH H) (shapesOKH H) U.ax178 (by decide +kernel) (by decide +kernel)

theorem ev179 (H : HookParams) : EntailsAtValues (cH H) U.ax179 (trS U.ax179).pat := by
  rw [(by decide +kernel : (trS U.ax179).pat = (trAxiom [] [] U.ax179).pat)]
  exact LibEv.addSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax179 (by decide +kernel) (by decide +kernel)

theorem ev180 (H : HookParams) : EntailsAtValues (cH H) U.ax180 (trS U.ax180).pat := by
  rw [(by decide +kernel : (trS U.ax180).pat = (trAxiom [] [] U.ax180).pat)]
  exact LibEv.addAssoc_ev (coreOKH H) (shapesOKH H) U.ax180 (by decide +kernel) (by decide +kernel)

theorem ev181 (H : HookParams) : EntailsAtValues (cH H) U.ax181 (trS U.ax181).pat := by
  rw [(by decide +kernel : (trS U.ax181).pat = (trAxiom [] [] U.ax181).pat)]
  exact LibEv.subAddComm_ev (coreOKH H) (shapesOKH H) U.ax181 (by decide +kernel) (by decide +kernel)

theorem ev182 (H : HookParams) : EntailsAtValues (cH H) U.ax182 (trS U.ax182).pat := by
  rw [(by decide +kernel : (trS U.ax182).pat = (trAxiom [] [] U.ax182).pat)]
  exact LibEv.subAsAdd_ev (coreOKH H) (shapesOKH H) U.ax182 (by decide +kernel) (by decide +kernel)

theorem ev183 (H : HookParams) : EntailsAtValues (cH H) U.ax183 (trS U.ax183).pat := by
  rw [(by decide +kernel : (trS U.ax183).pat = (trAxiom [] [] U.ax183).pat)]
  exact LibEv.subZero_ev (coreOKH H) (shapesOKH H) U.ax183 (by decide +kernel) (by decide +kernel)

theorem ev184 (H : HookParams) : EntailsAtValues (cH H) U.ax184 (trS U.ax184).pat := by
  rw [(by decide +kernel : (trS U.ax184).pat = (trAxiom [] [] U.ax184).pat)]
  exact LibEv.subAddSwap_ev (coreOKH H) (shapesOKH H) U.ax184 (by decide +kernel) (by decide +kernel)

theorem ev185 (H : HookParams) : EntailsAtValues (cH H) U.ax185 (trS U.ax185).pat := by
  rw [(by decide +kernel : (trS U.ax185).pat = (trAxiom [] [] U.ax185).pat)]
  exact LibEv.subAddAssoc_ev (coreOKH H) (shapesOKH H) U.ax185 (by decide +kernel) (by decide +kernel)

theorem ev186 (H : HookParams) : EntailsAtValues (cH H) U.ax186 (trS U.ax186).pat := by
  rw [(by decide +kernel : (trS U.ax186).pat = (trAxiom [] [] U.ax186).pat)]
  exact LibEv.subSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax186 (by decide +kernel) (by decide +kernel)

theorem ev187 (H : HookParams) : EntailsAtValues (cH H) U.ax187 (trS U.ax187).pat := by
  rw [(by decide +kernel : (trS U.ax187).pat = (trAxiom [] [] U.ax187).pat)]
  exact LibEv.subSubAdd_ev (coreOKH H) (shapesOKH H) U.ax187 (by decide +kernel) (by decide +kernel)

theorem ev190 (H : HookParams) : EntailsAtValues (cH H) U.ax190 (trS U.ax190).pat := by
  rw [(by decide +kernel : (trS U.ax190).pat = (trAxiom [] [] U.ax190).pat)]
  exact LibEv.fnNeBool_ev (coreOKH H) (shapesOKH H) U.ax190 (by decide +kernel) (by decide +kernel)

theorem ev191 (H : HookParams) : EntailsAtValues (cH H) U.ax191 (trS U.ax191).pat := by
  rw [(by decide +kernel : (trS U.ax191).pat = (trAxiom [] [] U.ax191).pat)]
  exact LibEv.fnNeInt_ev (coreOKH H) (shapesOKH H) U.ax191 (by decide +kernel) (by decide +kernel)

theorem ev192 (H : HookParams) : EntailsAtValues (cH H) U.ax192 (trS U.ax192).pat := by
  rw [(by decide +kernel : (trS U.ax192).pat = (trAxiom [] [] U.ax192).pat)]
  exact LibEv.fnNeK_ev (coreOKH H) U.ax192 (by decide +kernel) (by decide +kernel)

theorem ev193 (H : HookParams) : EntailsAtValues (cH H) U.ax193 (trS U.ax193).pat := by
  rw [(by decide +kernel : (trS U.ax193).pat = (trAxiom [] [] U.ax193).pat)]
  exact LibEv.boolKEq_ev (coreOKH H) (shapesOKH H) (boolBelowH H) U.ax193 (by decide +kernel)
    (by decide +kernel)

theorem ev194 (H : HookParams) : EntailsAtValues (cH H) U.ax194 (trS U.ax194).pat := by
  rw [(by decide +kernel : (trS U.ax194).pat = (trAxiom [] [] U.ax194).pat)]
  exact LibEv.intKEq_ev (coreOKH H) (shapesOKH H) (intBelowH H) U.ax194 (by decide +kernel)
    (by decide +kernel)

theorem ev197 (H : HookParams) : EntailsAtValues (cH H) U.ax197 (trS U.ax197).pat := by
  rw [(by decide +kernel : (trS U.ax197).pat = (trAxiom [] [] U.ax197).pat)]
  exact LibEv.fnAndFalse_ev (coreOKH H) (shapesOKH H) U.ax197 (by decide +kernel) (by decide +kernel)

theorem ev198 (H : HookParams) : EntailsAtValues (cH H) U.ax198 (trS U.ax198).pat := by
  rw [(by decide +kernel : (trS U.ax198).pat = (trAxiom [] [] U.ax198).pat)]
  exact LibEv.bAndTrue_ev (coreOKH H) (shapesOKH H) U.ax198 (by decide +kernel) (by decide +kernel)

theorem ev199 (H : HookParams) : EntailsAtValues (cH H) U.ax199 (trS U.ax199).pat := by
  rw [(by decide +kernel : (trS U.ax199).pat = (trAxiom [] [] U.ax199).pat)]
  exact LibEv.bAndFalse_ev (coreOKH H) (shapesOKH H) U.ax199 (by decide +kernel) (by decide +kernel)

theorem ev200 (H : HookParams) : EntailsAtValues (cH H) U.ax200 (trS U.ax200).pat := by
  rw [(by decide +kernel : (trS U.ax200).pat = (trAxiom [] [] U.ax200).pat)]
  exact LibEv.fnAndTrue_ev (coreOKH H) (shapesOKH H) U.ax200 (by decide +kernel) (by decide +kernel)

theorem ev201 (H : HookParams) : EntailsAtValues (cH H) U.ax201 (trS U.ax201).pat := by
  rw [(by decide +kernel : (trS U.ax201).pat = (trAxiom [] [] U.ax201).pat)]
  exact LibEv.fnAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax201 (by decide +kernel) (by decide +kernel)

theorem ev202 (H : HookParams) : EntailsAtValues (cH H) U.ax202 (trS U.ax202).pat := by
  rw [(by decide +kernel : (trS U.ax202).pat = (trAxiom [] [] U.ax202).pat)]
  exact LibEv.bAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax202 (by decide +kernel) (by decide +kernel)

theorem ev203 (H : HookParams) : EntailsAtValues (cH H) U.ax203 (trS U.ax203).pat := by
  rw [(by decide +kernel : (trS U.ax203).pat = (trAxiom [] [] U.ax203).pat)]
  exact LibEv.bAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax203 (by decide +kernel) (by decide +kernel)

theorem ev204 (H : HookParams) : EntailsAtValues (cH H) U.ax204 (trS U.ax204).pat := by
  rw [(by decide +kernel : (trS U.ax204).pat = (trAxiom [] [] U.ax204).pat)]
  exact LibEv.fnAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax204 (by decide +kernel) (by decide +kernel)

theorem ev205 (H : HookParams) : EntailsAtValues (cH H) U.ax205 (trS U.ax205).pat := by
  rw [(by decide +kernel : (trS U.ax205).pat = (trAxiom [] [] U.ax205).pat)]
  exact LibEv.fnDivInt_ev (coreOKH H) (shapesOKH H) U.ax205 (by decide +kernel) (by decide +kernel)

theorem ev207 (H : HookParams) : EntailsAtValues (cH H) U.ax207 (trS U.ax207).pat := by
  rw [(by decide +kernel : (trS U.ax207).pat = (trAxiom [] [] U.ax207).pat)]
  exact LibEv.bImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax207 (by decide +kernel) (by decide +kernel)

theorem ev208 (H : HookParams) : EntailsAtValues (cH H) U.ax208 (trS U.ax208).pat := by
  rw [(by decide +kernel : (trS U.ax208).pat = (trAxiom [] [] U.ax208).pat)]
  exact LibEv.bImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax208 (by decide +kernel) (by decide +kernel)

theorem ev209 (H : HookParams) : EntailsAtValues (cH H) U.ax209 (trS U.ax209).pat := by
  rw [(by decide +kernel : (trS U.ax209).pat = (trAxiom [] [] U.ax209).pat)]
  exact LibEv.fnImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax209 (by decide +kernel) (by decide +kernel)

theorem ev210 (H : HookParams) : EntailsAtValues (cH H) U.ax210 (trS U.ax210).pat := by
  rw [(by decide +kernel : (trS U.ax210).pat = (trAxiom [] [] U.ax210).pat)]
  exact LibEv.fnImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax210 (by decide +kernel) (by decide +kernel)

theorem ev211 (H : HookParams) : EntailsAtValues (cH H) U.ax211 (trS U.ax211).pat := by
  rw [(by decide +kernel : (trS U.ax211).pat = (trAxiom [] [] U.ax211).pat)]
  exact LibEv.emodAsTmod_ev (coreOKH H) (shapesOKH H) U.ax211 (by decide +kernel) (by decide +kernel)

theorem ev212 (H : HookParams) : EntailsAtValues (cH H) U.ax212 (trS U.ax212).pat := by
  rw [(by decide +kernel : (trS U.ax212).pat = (trAxiom [] [] U.ax212).pat)]
  exact LibEv.emodSmall_ev (coreOKH H) (shapesOKH H) U.ax212 (by decide +kernel) (by decide +kernel)

theorem ev213 (H : HookParams) : EntailsAtValues (cH H) U.ax213 (trS U.ax213).pat := by
  rw [(by decide +kernel : (trS U.ax213).pat = (trAxiom [] [] U.ax213).pat)]
  exact LibEv.bOrFalse_ev (coreOKH H) (shapesOKH H) U.ax213 (by decide +kernel) (by decide +kernel)

theorem ev214 (H : HookParams) : EntailsAtValues (cH H) U.ax214 (trS U.ax214).pat := by
  rw [(by decide +kernel : (trS U.ax214).pat = (trAxiom [] [] U.ax214).pat)]
  exact LibEv.bOrTrue_ev (coreOKH H) (shapesOKH H) U.ax214 (by decide +kernel) (by decide +kernel)

theorem ev215 (H : HookParams) : EntailsAtValues (cH H) U.ax215 (trS U.ax215).pat := by
  rw [(by decide +kernel : (trS U.ax215).pat = (trAxiom [] [] U.ax215).pat)]
  exact LibEv.fnOrFalse_ev (coreOKH H) (shapesOKH H) U.ax215 (by decide +kernel) (by decide +kernel)

theorem ev216 (H : HookParams) : EntailsAtValues (cH H) U.ax216 (trS U.ax216).pat := by
  rw [(by decide +kernel : (trS U.ax216).pat = (trAxiom [] [] U.ax216).pat)]
  exact LibEv.fnOrTrue_ev (coreOKH H) (shapesOKH H) U.ax216 (by decide +kernel) (by decide +kernel)

theorem ev217 (H : HookParams) : EntailsAtValues (cH H) U.ax217 (trS U.ax217).pat := by
  rw [(by decide +kernel : (trS U.ax217).pat = (trAxiom [] [] U.ax217).pat)]
  exact LibEv.bOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax217 (by decide +kernel) (by decide +kernel)

theorem ev218 (H : HookParams) : EntailsAtValues (cH H) U.ax218 (trS U.ax218).pat := by
  rw [(by decide +kernel : (trS U.ax218).pat = (trAxiom [] [] U.ax218).pat)]
  exact LibEv.bOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax218 (by decide +kernel) (by decide +kernel)

theorem ev219 (H : HookParams) : EntailsAtValues (cH H) U.ax219 (trS U.ax219).pat := by
  rw [(by decide +kernel : (trS U.ax219).pat = (trAxiom [] [] U.ax219).pat)]
  exact LibEv.fnOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax219 (by decide +kernel) (by decide +kernel)

theorem ev220 (H : HookParams) : EntailsAtValues (cH H) U.ax220 (trS U.ax220).pat := by
  rw [(by decide +kernel : (trS U.ax220).pat = (trAxiom [] [] U.ax220).pat)]
  exact LibEv.fnOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax220 (by decide +kernel) (by decide +kernel)

theorem ev221 (H : HookParams) : EntailsAtValues (cH H) U.ax221 (trS U.ax221).pat := by
  rw [(by decide +kernel : (trS U.ax221).pat = (trAxiom [] [] U.ax221).pat)]
  exact LibEv.fnXorSame_ev (coreOKH H) (shapesOKH H) U.ax221 (by decide +kernel) (by decide +kernel)

theorem ev222 (H : HookParams) : EntailsAtValues (cH H) U.ax222 (trS U.ax222).pat := by
  rw [(by decide +kernel : (trS U.ax222).pat = (trAxiom [] [] U.ax222).pat)]
  exact LibEv.bXorFalse_ev (coreOKH H) (shapesOKH H) U.ax222 (by decide +kernel) (by decide +kernel)

theorem ev223 (H : HookParams) : EntailsAtValues (cH H) U.ax223 (trS U.ax223).pat := by
  rw [(by decide +kernel : (trS U.ax223).pat = (trAxiom [] [] U.ax223).pat)]
  exact LibEv.fnXorFalse_ev (coreOKH H) (shapesOKH H) U.ax223 (by decide +kernel) (by decide +kernel)

theorem ev224 (H : HookParams) : EntailsAtValues (cH H) U.ax224 (trS U.ax224).pat := by
  rw [(by decide +kernel : (trS U.ax224).pat = (trAxiom [] [] U.ax224).pat)]
  exact LibEv.fnSetUnion_ev (coreOKH H) (shapesOKH H) U.ax224 (by decide +kernel) (by decide +kernel)

theorem ev226 (H : HookParams) : EntailsAtValues (cH H) U.ax226 (trS U.ax226).pat := by
  rw [(by decide +kernel : (trS U.ax226).pat = (trAxiom [] [] U.ax226).pat)]
  exact LibEv.fnFreshInt_ev (coreOKH H) (shapesOKH H) U.ax226 (by decide +kernel) (by decide +kernel)

theorem ev264 (H : HookParams) : EntailsAtValues (cH H) U.ax264 (trS U.ax264).pat := by
  rw [(by decide +kernel : (trS U.ax264).pat = (trAxiom [] [] U.ax264).pat)]
  exact LibEv.fnMinLt_ev (coreOKH H) (shapesOKH H) U.ax264 (by decide +kernel) (by decide +kernel)

theorem ev265 (H : HookParams) : EntailsAtValues (cH H) U.ax265 (trS U.ax265).pat := by
  rw [(by decide +kernel : (trS U.ax265).pat = (trAxiom [] [] U.ax265).pat)]
  exact LibEv.fnMinGe_ev (coreOKH H) (shapesOKH H) U.ax265 (by decide +kernel) (by decide +kernel)

theorem ev266 (H : HookParams) : EntailsAtValues (cH H) U.ax266 (trS U.ax266).pat := by
  rw [(by decide +kernel : (trS U.ax266).pat = (trAxiom [] [] U.ax266).pat)]
  exact LibEv.fnNotFalse_ev (coreOKH H) U.ax266 (by decide +kernel) (by decide +kernel)

theorem ev267 (H : HookParams) : EntailsAtValues (cH H) U.ax267 (trS U.ax267).pat := by
  rw [(by decide +kernel : (trS U.ax267).pat = (trAxiom [] [] U.ax267).pat)]
  exact LibEv.fnNotTrue_ev (coreOKH H) U.ax267 (by decide +kernel) (by decide +kernel)

theorem ev283 (H : HookParams) : EntailsAtValues (cH H) U.ax283 (trS U.ax283).pat := by
  rw [(by decide +kernel : (trS U.ax283).pat = (trAxiom [] [] U.ax283).pat)]
  exact LibEv.fnPushList_ev (coreOKH H) (shapesOKH H) U.ax283 (by decide +kernel) (by decide +kernel)

theorem ev188 (H : HookParams) : EntailsAtValues (cH H) U.ax188 (trS U.ax188).pat := by
  rw [(by decide +kernel : (trS U.ax188).pat = (trAxiom [] [] U.ax188).pat)]
  exact LibEv.shlZero_ev (coreOKH H) (shapesOKH H) U.ax188 (by decide +kernel) (by decide +kernel)

theorem ev189 (H : HookParams) : EntailsAtValues (cH H) U.ax189 (trS U.ax189).pat := by
  rw [(by decide +kernel : (trS U.ax189).pat = (trAxiom [] [] U.ax189).pat)]
  exact LibEv.zeroShl_ev (coreOKH H) (shapesOKH H) U.ax189 (by decide +kernel) (by decide +kernel)

theorem ev195 (H : HookParams) : EntailsAtValues (cH H) U.ax195 (trS U.ax195).pat := by
  rw [(by decide +kernel : (trS U.ax195).pat = (trAxiom [] [] U.ax195).pat)]
  exact LibEv.shrZero_ev (coreOKH H) (shapesOKH H) U.ax195 (by decide +kernel) (by decide +kernel)

theorem ev196 (H : HookParams) : EntailsAtValues (cH H) U.ax196 (trS U.ax196).pat := by
  rw [(by decide +kernel : (trS U.ax196).pat = (trAxiom [] [] U.ax196).pat)]
  exact LibEv.zeroShr_ev (coreOKH H) (shapesOKH H) U.ax196 (by decide +kernel) (by decide +kernel)

/-- The 56 sentences of `evN`. -/
noncomputable def evText : List AxiomDecl :=
  [U.ax173, U.ax175, U.ax176, U.ax177, U.ax178, U.ax179, U.ax180, U.ax181, U.ax182, U.ax183,
   U.ax184, U.ax185, U.ax186, U.ax187, U.ax190, U.ax191, U.ax192, U.ax193, U.ax194, U.ax197,
   U.ax198, U.ax199, U.ax200, U.ax201, U.ax202, U.ax203, U.ax204, U.ax205, U.ax207, U.ax208,
   U.ax209, U.ax210, U.ax211, U.ax212, U.ax213, U.ax214, U.ax215, U.ax216, U.ax217, U.ax218,
   U.ax219, U.ax220, U.ax221, U.ax222, U.ax223, U.ax224, U.ax226, U.ax264, U.ax265, U.ax266,
   U.ax267, U.ax283,
   U.ax188, U.ax189, U.ax195, U.ax196]

theorem ev_entailed (H : HookParams) : ∀ ad ∈ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev173 H, List.forall_mem_cons.mpr ⟨ev175 H, List.forall_mem_cons.mpr ⟨ev176 H, List.forall_mem_cons.mpr ⟨ev177 H, List.forall_mem_cons.mpr ⟨ev178 H, List.forall_mem_cons.mpr ⟨ev179 H, List.forall_mem_cons.mpr ⟨ev180 H, List.forall_mem_cons.mpr ⟨ev181 H, List.forall_mem_cons.mpr ⟨ev182 H, List.forall_mem_cons.mpr ⟨ev183 H, List.forall_mem_cons.mpr ⟨ev184 H, List.forall_mem_cons.mpr ⟨ev185 H, List.forall_mem_cons.mpr ⟨ev186 H, List.forall_mem_cons.mpr ⟨ev187 H, List.forall_mem_cons.mpr ⟨ev190 H, List.forall_mem_cons.mpr ⟨ev191 H, List.forall_mem_cons.mpr ⟨ev192 H, List.forall_mem_cons.mpr ⟨ev193 H, List.forall_mem_cons.mpr ⟨ev194 H, List.forall_mem_cons.mpr ⟨ev197 H, List.forall_mem_cons.mpr ⟨ev198 H, List.forall_mem_cons.mpr ⟨ev199 H, List.forall_mem_cons.mpr ⟨ev200 H, List.forall_mem_cons.mpr ⟨ev201 H, List.forall_mem_cons.mpr ⟨ev202 H, List.forall_mem_cons.mpr ⟨ev203 H, List.forall_mem_cons.mpr ⟨ev204 H, List.forall_mem_cons.mpr ⟨ev205 H, List.forall_mem_cons.mpr ⟨ev207 H, List.forall_mem_cons.mpr ⟨ev208 H, List.forall_mem_cons.mpr ⟨ev209 H, List.forall_mem_cons.mpr ⟨ev210 H, List.forall_mem_cons.mpr ⟨ev211 H, List.forall_mem_cons.mpr ⟨ev212 H, List.forall_mem_cons.mpr ⟨ev213 H, List.forall_mem_cons.mpr ⟨ev214 H, List.forall_mem_cons.mpr ⟨ev215 H, List.forall_mem_cons.mpr ⟨ev216 H, List.forall_mem_cons.mpr ⟨ev217 H, List.forall_mem_cons.mpr ⟨ev218 H, List.forall_mem_cons.mpr ⟨ev219 H, List.forall_mem_cons.mpr ⟨ev220 H, List.forall_mem_cons.mpr ⟨ev221 H, List.forall_mem_cons.mpr ⟨ev222 H, List.forall_mem_cons.mpr ⟨ev223 H, List.forall_mem_cons.mpr ⟨ev224 H, List.forall_mem_cons.mpr ⟨ev226 H, List.forall_mem_cons.mpr ⟨ev264 H, List.forall_mem_cons.mpr ⟨ev265 H, List.forall_mem_cons.mpr ⟨ev266 H, List.forall_mem_cons.mpr ⟨ev267 H, List.forall_mem_cons.mpr ⟨ev283 H, List.forall_mem_cons.mpr ⟨ev188 H, List.forall_mem_cons.mpr ⟨ev189 H, List.forall_mem_cons.mpr ⟨ev195 H, List.forall_mem_cons.mpr ⟨ev196 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the Bool predicate sentences over set variables (8), at set values -/

theorem ev148 (H : HookParams) : EntailsAtSetValues (cH H) U.ax148 (trS U.ax148).pat := by
  rw [(by decide +kernel : (trS U.ax148).pat = (trAxiom [] [] U.ax148).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) false U.ax148 (by decide +kernel) (by decide +kernel)

theorem ev149 (H : HookParams) : EntailsAtSetValues (cH H) U.ax149 (trS U.ax149).pat := by
  rw [(by decide +kernel : (trS U.ax149).pat = (trAxiom [] [] U.ax149).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) false U.ax149 (by decide +kernel) (by decide +kernel)

theorem ev150 (H : HookParams) : EntailsAtSetValues (cH H) U.ax150 (trS U.ax150).pat := by
  rw [(by decide +kernel : (trS U.ax150).pat = (trAxiom [] [] U.ax150).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false false U.ax150 (by decide +kernel) (by decide +kernel)

theorem ev151 (H : HookParams) : EntailsAtSetValues (cH H) U.ax151 (trS U.ax151).pat := by
  rw [(by decide +kernel : (trS U.ax151).pat = (trAxiom [] [] U.ax151).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true false U.ax151 (by decide +kernel) (by decide +kernel)

theorem ev156 (H : HookParams) : EntailsAtSetValues (cH H) U.ax156 (trS U.ax156).pat := by
  rw [(by decide +kernel : (trS U.ax156).pat = (trAxiom [] [] U.ax156).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) true U.ax156 (by decide +kernel) (by decide +kernel)

theorem ev157 (H : HookParams) : EntailsAtSetValues (cH H) U.ax157 (trS U.ax157).pat := by
  rw [(by decide +kernel : (trS U.ax157).pat = (trAxiom [] [] U.ax157).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false true U.ax157 (by decide +kernel) (by decide +kernel)

theorem ev162 (H : HookParams) : EntailsAtSetValues (cH H) U.ax162 (trS U.ax162).pat := by
  rw [(by decide +kernel : (trS U.ax162).pat = (trAxiom [] [] U.ax162).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) true U.ax162 (by decide +kernel) (by decide +kernel)

theorem ev163 (H : HookParams) : EntailsAtSetValues (cH H) U.ax163 (trS U.ax163).pat := by
  rw [(by decide +kernel : (trS U.ax163).pat = (trAxiom [] [] U.ax163).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true true U.ax163 (by decide +kernel) (by decide +kernel)

/-- The eight sentences over set variables. -/
noncomputable def setText : List AxiomDecl :=
  [U.ax148, U.ax149, U.ax150, U.ax151, U.ax156, U.ax157, U.ax162, U.ax163]

/-! ## The class -/

/-- **Ev for the library sentences over element variables**: the 16 predicate equations and the 56
term and function equations, for every H. -/
theorem lib_entailed (H : HookParams) : ∀ ad ∈ predText ++ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  fun ad had => (List.mem_append.mp had).elim (pred_entailed H ad) (ev_entailed H ad)

/-- **The library sentences over set variables are entailed at set values**, for every H. -/
theorem libSet_entailed (H : HookParams) : ∀ ad ∈ setText, EntailsAtSetValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev148 H, List.forall_mem_cons.mpr ⟨ev149 H, List.forall_mem_cons.mpr ⟨ev150 H, List.forall_mem_cons.mpr ⟨ev151 H, List.forall_mem_cons.mpr ⟨ev156 H, List.forall_mem_cons.mpr ⟨ev157 H, List.forall_mem_cons.mpr ⟨ev162 H, List.forall_mem_cons.mpr ⟨ev163 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩

/-- The 80 library sentences tied here. -/
theorem lib_indices : (predText ++ evText ++ setText).map (·.index) =
    [140, 141, 142, 143, 144, 145, 146, 147, 152, 153, 154, 155, 158, 159, 160, 161, 173, 175, 176, 177,
   178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 190, 191, 192, 193, 194, 197, 198, 199, 200, 201,
   202, 203, 204, 205, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222,
   223, 224, 226, 264, 265, 266, 267, 283, 188, 189, 195, 196, 148, 149, 150, 151, 156, 157, 162, 163] := by
  decide +kernel

/-! ## The set-variable lemmas -/

section Ceil

theorem coreOKH' (H : HookParams) : (cH H).coreOK = true := coreOKH H

/-- What a refutation at values gives: Γ with the sentence has no model. -/
theorem refuted_of_at {c' : Semantics} {ad : AxiomDecl} {φ : KoreAML.P}
    (hat : ∀ (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' →
      ∃ e : Valuation M, AtValues c' I e ad.ax ∧ SetVarsAtValues c' I e ad.ax ∧ ¬ φ.interpret I e default) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c' → ¬ (I ⊧ᴵ φ) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := hat M I hI
  exact hn (hax e default)

/-! ## The Int lemmas -/

theorem t135 : (trS U.ax135).pat = (trAxiom [] [] U.ax135).pat := by decide +kernel
theorem t136 : (trS U.ax136).pat = (trAxiom [] [] U.ax136).pat := by decide +kernel
theorem t137 : (trS U.ax137).pat = (trAxiom [] [] U.ax137).pat := by decide +kernel
theorem t138 : (trS U.ax138).pat = (trAxiom [] [] U.ax138).pat := by decide +kernel
theorem t139 : (trS U.ax139).pat = (trAxiom [] [] U.ax139).pat := by decide +kernel

theorem s135_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax135.ax ∧ SetVarsAtValues (cH H) I e U.ax135.ax ∧
      ¬ (trS U.ax135).pat.interpret I e default := by
  rw [t135]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTMod intNe (by decide +kernel) (by rfl) 0 1 0
    ⟨_, LibEv.hv_intTMod (by decide)⟩ (by rw [LibEv.hv_intNe]; rfl) U.ax135 (by decide +kernel) (by decide +kernel) hI
theorem s136_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax136.ax ∧ SetVarsAtValues (cH H) I e U.ax136.ax ∧
      ¬ (trS U.ax136).pat.interpret I e default := by
  rw [t136]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTDiv intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_tdiv 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax136
    (by decide +kernel) (by decide +kernel) hI
theorem s139_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax139.ax ∧ SetVarsAtValues (cH H) I e U.ax139.ax ∧
      ¬ (trS U.ax139).pat.interpret I e default := by
  rw [t139]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intEMod intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_emod 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax139
    (by decide +kernel) (by decide +kernel) hI
theorem s137_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax137.ax ∧ SetVarsAtValues (cH H) I e U.ax137.ax ∧
      ¬ (trS U.ax137).pat.interpret I e default := by
  rw [t137]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShl intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shl 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax137
    (by decide +kernel) (by decide +kernel) hI
theorem s138_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax138.ax ∧ SetVarsAtValues (cH H) I e U.ax138.ax ∧
      ¬ (trS U.ax138).pat.interpret I e default := by
  rw [t138]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShr intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shr 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax138
    (by decide +kernel) (by decide +kernel) hI

theorem s135_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax135).pat) := refuted_of_at (s135_at H)
theorem s136_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax136).pat) := refuted_of_at (s136_at H)
theorem s137_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax137).pat) := refuted_of_at (s137_at H)
theorem s138_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax138).pat) := refuted_of_at (s138_at H)
theorem s139_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax139).pat) := refuted_of_at (s139_at H)

theorem s135_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax135 (trS U.ax135).pat := by
  rw [t135]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tmod U.ax135 (by decide +kernel) (by decide +kernel)
theorem s136_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax136 (trS U.ax136).pat := by
  rw [t136]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTDiv intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tdiv U.ax136 (by decide +kernel) (by decide +kernel)
theorem s137_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax137 (trS U.ax137).pat := by
  rw [t137]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShl intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shl U.ax137 (by decide +kernel) (by decide +kernel)
theorem s138_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax138 (trS U.ax138).pat := by
  rw [t138]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShr intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shr U.ax138 (by decide +kernel) (by decide +kernel)
theorem s139_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax139 (trS U.ax139).pat := by
  rw [t139]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intEMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_emod U.ax139 (by decide +kernel) (by decide +kernel)

/-! ## The Map lemma -/

theorem t285 : (trS U.ax285).pat = (trAxiom [] [] U.ax285).pat := by decide +kernel

/-- The KItem injection of 0. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel

theorem s285_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax285.ax ∧ SetVarsAtValues (cH H) I e U.ax285.ax ∧
      ¬ (trS U.ax285).pat.interpret I e default := by
  rw [t285]
  exact LibEv.ceilMap_refuted_at (coreOKH' H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H) (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax285 (by decide +kernel) (by decide +kernel) hI

theorem s285_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax285).pat) := refuted_of_at (s285_at H)

theorem s285_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax285 (trS U.ax285).pat := by
  rw [t285]
  exact LibEv.ceilMap_one (coreOKH' H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax285 (by decide +kernel) (by decide +kernel)

end Ceil

/-- The sentences of the class set-variable lemma. -/
theorem setvar_indices : [U.ax135, U.ax136, U.ax137, U.ax138, U.ax139, U.ax285].map (·.index) =
    [135, 136, 137, 138, 139, 285] := by decide +kernel

/-! ## The accounts against the class lists -/

/-- The class lists of test/TieRuleCoolText.lean (`classes`), as written there. -/
def hookedClass : List Nat :=
  [22, 23, 24, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 59,
   67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 79, 84, 90, 92, 109, 110, 111, 112, 115, 116, 117, 118,
   119, 120]
def lawClass : List Nat :=
  [56, 57, 58, 60, 61, 62, 63, 65, 66]
def libraryClass : List Nat :=
  [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
   159, 160, 161, 162, 163, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
   188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 207,
   208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226,
   262, 263, 264, 265, 266, 267, 283, 284]
def setvarClass : List Nat :=
  [135, 136, 137, 138, 139, 285]

/-- Hooked functional: the 47 tied and 109 (`ite`'s, owed) are the class. -/
theorem hooked_account : (funText.map (fun ad : AxiomDecl => ad.index) ++ [109]).isPerm hookedClass = true := by
  rw [fun_indices]; decide
/-- Collection law: the nine tied are the class. -/
theorem law_account : lawText.map (·.index) = lawClass := law_indices
/-- Library: the 80 tied, and 225, 284 (`bitRangeInt`, `signExtendBitRangeInt`) and 262, 263 (`ite{SortK}`),
owed, are the class. -/
theorem library_account : ((predText ++ evText ++ setText).map (fun ad : AxiomDecl => ad.index) ++ [225, 262, 263, 284]).isPerm libraryClass = true := by
  rw [lib_indices]; decide
/-- Set-variable lemma: the six refuted are the class. -/
theorem setvar_account : [U.ax135, U.ax136, U.ax137, U.ax138, U.ax139, U.ax285].map (·.index) = setvarClass :=
  setvar_indices

/-! ## Over `Γc`, the theory the statements are about -/

/-- What holds at values in every model of Γ holds at values in every model of `Γc`. -/
theorem atValues_c (H : HookParams) {ad : AxiomDecl} {φ : P} (h : EntailsAtValues (cH H) ad φ) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, φ.interpret I e m :=
  fun M hM I hI => h M hM I fun ψ hψ => hI ψ (Or.inl hψ)

theorem fun_entailed_c (H : HookParams) : ∀ ad ∈ funText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had => atValues_c H (fun_entailed H ad had)
theorem laws_entailed_c (H : HookParams) : ∀ ad ∈ lawText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had => atValues_c H (laws_entailed H ad had)
theorem lib_entailed_c (H : HookParams) : ∀ ad ∈ predText ++ evText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had => atValues_c H (lib_entailed H ad had)
theorem libSet_entailed_c (H : HookParams) : ∀ ad ∈ setText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) →
      ∀ e, AtValues (cH H) I e ad.ax → SetVarsAtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had M hM I hI => libSet_entailed H ad had M hM I fun ψ hψ => hI ψ (Or.inl hψ)

/-- **The six set-variable lemmas are refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/
theorem setvar_refuted_c (H : HookParams) : ∀ ad ∈ [U.ax135, U.ax136, U.ax137, U.ax138, U.ax139, U.ax285],
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS ad).pat) := by
  have hs : ∀ ad ∈ [U.ax135, U.ax136, U.ax137, U.ax138, U.ax139, U.ax285],
      ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS ad).pat) :=
    List.forall_mem_cons.mpr ⟨s135_refuted H, List.forall_mem_cons.mpr ⟨s136_refuted H,
      List.forall_mem_cons.mpr ⟨s137_refuted H, List.forall_mem_cons.mpr ⟨s138_refuted H,
      List.forall_mem_cons.mpr ⟨s139_refuted H, List.forall_mem_cons.mpr ⟨s285_refuted H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩
  intro ad had M hM I hI
  exact hs ad had M hM I fun ψ hψ => hI ψ (Or.inl hψ)

end KCore.TieRuleCoolAtValues

#print axioms KCore.TieRuleCoolAtValues.fun_entailed
#print axioms KCore.TieRuleCoolAtValues.fun_indices
#print axioms KCore.TieRuleCoolAtValues.laws_entailed
#print axioms KCore.TieRuleCoolAtValues.law_indices
#print axioms KCore.TieRuleCoolAtValues.pred_entailed
#print axioms KCore.TieRuleCoolAtValues.ev_entailed
#print axioms KCore.TieRuleCoolAtValues.lib_entailed
#print axioms KCore.TieRuleCoolAtValues.libSet_entailed
#print axioms KCore.TieRuleCoolAtValues.lib_indices
#print axioms KCore.TieRuleCoolAtValues.s135_refuted
#print axioms KCore.TieRuleCoolAtValues.s136_refuted
#print axioms KCore.TieRuleCoolAtValues.s137_refuted
#print axioms KCore.TieRuleCoolAtValues.s138_refuted
#print axioms KCore.TieRuleCoolAtValues.s139_refuted
#print axioms KCore.TieRuleCoolAtValues.s285_refuted
#print axioms KCore.TieRuleCoolAtValues.s135_one
#print axioms KCore.TieRuleCoolAtValues.s136_one
#print axioms KCore.TieRuleCoolAtValues.s137_one
#print axioms KCore.TieRuleCoolAtValues.s138_one
#print axioms KCore.TieRuleCoolAtValues.s139_one
#print axioms KCore.TieRuleCoolAtValues.s285_one
#print axioms KCore.TieRuleCoolAtValues.setvar_indices
#print axioms KCore.TieRuleCoolAtValues.hooked_account
#print axioms KCore.TieRuleCoolAtValues.law_account
#print axioms KCore.TieRuleCoolAtValues.library_account
#print axioms KCore.TieRuleCoolAtValues.setvar_account
#print axioms KCore.TieRuleCoolAtValues.fun_entailed_c
#print axioms KCore.TieRuleCoolAtValues.laws_entailed_c
#print axioms KCore.TieRuleCoolAtValues.lib_entailed_c
#print axioms KCore.TieRuleCoolAtValues.libSet_entailed_c
#print axioms KCore.TieRuleCoolAtValues.setvar_refuted_c
