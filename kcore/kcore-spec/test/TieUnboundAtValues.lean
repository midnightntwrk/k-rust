/-
  The classes hooked functional, collection law and library entailed at values, and the class
  set-variable lemma refuted, on `f2-examples/unbound.kompile.kore` (fixture e2-unbound), for every
  interpretation H. Each sentence is tied by the library's one statement of it (KcoreSpec/LibEv*.lean):
  the text's axiom is compared with the statement's pattern over the registry's names, and its
  translation with the text's declarations with the translation the statement is about.
  Run from the package root: `lake env lean -j1 test/TieUnboundAtValues.lean`.

  The library part of this text is kimp's (`examples/ref-kimp/RefKimp/definition.kore`) sentence for
  sentence up to Location, Source and UNIQUE_ID attributes; the sections below are
  test/TieKimpAtValues.lean's and the set-variable section of test/TieKimpRefuted.lean over this
  text's indices.

  - Hooked functional (`fun_entailed`, `fun_indices`): the 47 sentences
    `\exists{R}(Val:s, \equals{s, R}(Val:s, f(K0:s0, …)))` whose symbol is an interpreted hooked
    symbol that is not partial (`LibEv.functional_ev`). Owed: 100, the sentence of `ite`, which the
    text states once over a sort variable (`axiom{R, SortSort}`): it is not the functional sentence
    of a signature of `hookSigs`, whose sorts are the registry's, and the library states none of it.
  - Collection law (`laws_entailed`, `law_indices`): associativity and the two units of `_List_`,
    `_Map_`, `_Set_` (53 to 55, 57 to 60, 62, 63), the nine sentences of the class.
  - Library (`lib_entailed`, `libSet_entailed`, `lib_indices`): 80 of the class's 84. The sixteen
    predicate equations of `==Int`, `=/=Int`, `==K`, `=/=K` (`pred_entailed`); 56 term and function
    equations, each by its own theorem (`evN`); the eight Bool predicate sentences over set
    variables, entailed at set values (`EntailsAtSetValues`), which `libSet_entailed` states. Owed:
    242, 243 (`ite{SortK}` at a condition `true` or `false`), `ite` at the sort K, of which the
    library states no equation; 207, 263, the equations of `bitRangeInt` and
    `signExtendBitRangeInt`, interpreted symbols of which the library states no equation.
  - Set-variable lemmas (`sN_refuted`, `sN_one`, `setvar_indices`): 125 (`%Int`), 126 (`/Int`),
    129 (`modInt`) at `@I1 = {0}`, `@I2 = {1, 0}`; 127 (`<<Int`), 128 (`>>Int`) at `@I1 = {0}`,
    `@I2 = {0, -1}`; 264, kompile's `#Ceil(@K0 |-> @K1 @Rest)` lemma, at `@K0 = @K1 = {0}`,
    `@Rest = {.Map, 0 |-> 0}`. Each fails in every model of Γ at that valuation (`sN_at`), so Γ with
    it has no model (`sN_refuted`), and it holds where its set variables hold at most one element
    (`sN_one`).
  - The accounts (`hooked_account`, `law_account`, `library_account`, `setvar_account`): the tied
    sentences with the owed ones are the class lists of test/TieUnbound.lean (`classes`).
  - The function functional class (85 to 99, the 15 sort predicates' `functional` sentences) is not
    tied: its direction is a hypothesis, `FnHyp`, which test/TieUnboundRule.lean shows for every H
    (`fnHypH`); no theorem here relates the 15 sentences to it.

  The definition reads a confined sort (its rule leaves X open), so its theory is `Γc = Γ ∪ Γcl`.
  Every statement above is over Γ; a model of `Γc` is one of Γ, so each holds over `Γc` as well
  (the `_c` forms at the end).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieUnboundAtValues

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/unbound.kompile.kore"
definition_of defn from "f2-examples/unbound.kompile.kore"
user_axioms U from "f2-examples/unbound.kompile.kore" module "E2-UNBOUND"

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

/-! ## Hooked functional (47 of 48; 100, `ite`'s, owed) -/

/-- The indices of the sentences. -/
def funIdx : List Nat :=
  [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49,
   50, 51, 52, 56, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 76, 79, 82, 84, 101, 102,
   103, 106, 107, 108, 109, 110, 111]

/-- The sentences, in text order. -/
noncomputable def funText : List AxiomDecl := U.all.filter fun ad => funIdx.contains ad.index

theorem fun_indices : funText.map (·.index) =
    [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49,
     50, 51, 52, 56, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 76, 79, 82, 84, 101, 102,
     103, 106, 107, 108, 109, 110, 111] := by
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

theorem law53 (H : HookParams) : EntailsAtValues (cH H) U.ax53 (trS U.ax53).pat := by
  rw [(by decide +kernel : (trS U.ax53).pat = (trAxiom [] [] U.ax53).pat)]
  exact LibEv.listAssoc_ev (coreOKH H) (shapesOKH H) U.ax53 (by decide +kernel) (by decide +kernel)
theorem law54 (H : HookParams) : EntailsAtValues (cH H) U.ax54 (trS U.ax54).pat := by
  rw [(by decide +kernel : (trS U.ax54).pat = (trAxiom [] [] U.ax54).pat)]
  exact LibEv.listUnitR_ev (coreOKH H) (shapesOKH H) U.ax54 (by decide +kernel) (by decide +kernel)
theorem law55 (H : HookParams) : EntailsAtValues (cH H) U.ax55 (trS U.ax55).pat := by
  rw [(by decide +kernel : (trS U.ax55).pat = (trAxiom [] [] U.ax55).pat)]
  exact LibEv.listUnitL_ev (coreOKH H) (shapesOKH H) U.ax55 (by decide +kernel) (by decide +kernel)
theorem law57 (H : HookParams) : EntailsAtValues (cH H) U.ax57 (trS U.ax57).pat := by
  rw [(by decide +kernel : (trS U.ax57).pat = (trAxiom [] [] U.ax57).pat)]
  exact LibEv.mapAssoc_ev (coreOKH H) (shapesOKH H) U.ax57 (by decide +kernel) (by decide +kernel)
theorem law58 (H : HookParams) : EntailsAtValues (cH H) U.ax58 (trS U.ax58).pat := by
  rw [(by decide +kernel : (trS U.ax58).pat = (trAxiom [] [] U.ax58).pat)]
  exact LibEv.mapUnitR_ev (coreOKH H) (shapesOKH H) U.ax58 (by decide +kernel) (by decide +kernel)
theorem law59 (H : HookParams) : EntailsAtValues (cH H) U.ax59 (trS U.ax59).pat := by
  rw [(by decide +kernel : (trS U.ax59).pat = (trAxiom [] [] U.ax59).pat)]
  exact LibEv.mapUnitL_ev (coreOKH H) (shapesOKH H) U.ax59 (by decide +kernel) (by decide +kernel)
theorem law60 (H : HookParams) : EntailsAtValues (cH H) U.ax60 (trS U.ax60).pat := by
  rw [(by decide +kernel : (trS U.ax60).pat = (trAxiom [] [] U.ax60).pat)]
  exact LibEv.setAssoc_ev (coreOKH H) (shapesOKH H) U.ax60 (by decide +kernel) (by decide +kernel)
theorem law62 (H : HookParams) : EntailsAtValues (cH H) U.ax62 (trS U.ax62).pat := by
  rw [(by decide +kernel : (trS U.ax62).pat = (trAxiom [] [] U.ax62).pat)]
  exact LibEv.setUnitR_ev (coreOKH H) (shapesOKH H) U.ax62 (by decide +kernel) (by decide +kernel)
theorem law63 (H : HookParams) : EntailsAtValues (cH H) U.ax63 (trS U.ax63).pat := by
  rw [(by decide +kernel : (trS U.ax63).pat = (trAxiom [] [] U.ax63).pat)]
  exact LibEv.setUnitL_ev (coreOKH H) (shapesOKH H) U.ax63 (by decide +kernel) (by decide +kernel)

/-- The nine collection laws of the text. -/
noncomputable def lawText : List AxiomDecl :=
  [U.ax53, U.ax54, U.ax55, U.ax57, U.ax58, U.ax59, U.ax60, U.ax62, U.ax63]

theorem law_indices : lawText.map (·.index) = [53, 54, 55, 57, 58, 59, 60, 62, 63] := by decide +kernel

/-- **Ev for the collection laws**, for every H. -/
theorem laws_entailed (H : HookParams) : ∀ ad ∈ lawText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨law53 H, List.forall_mem_cons.mpr ⟨law54 H, List.forall_mem_cons.mpr ⟨law55 H, List.forall_mem_cons.mpr ⟨law57 H, List.forall_mem_cons.mpr ⟨law58 H, List.forall_mem_cons.mpr ⟨law59 H, List.forall_mem_cons.mpr ⟨law60 H, List.forall_mem_cons.mpr ⟨law62 H, List.forall_mem_cons.mpr ⟨law63 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the predicate equations of the equality symbols (16) -/

/-- The indices of the sentences. -/
def predIdx : List Nat := [130, 131, 132, 133, 134, 135, 136, 137, 142, 143, 144, 145, 148, 149, 150, 151]

/-- The sentences, in text order. -/
noncomputable def predText : List AxiomDecl := U.all.filter fun ad => predIdx.contains ad.index

theorem pred_indices : predText.map (·.index) = [130, 131, 132, 133, 134, 135, 136, 137, 142, 143, 144, 145, 148, 149, 150, 151] := by decide +kernel

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

theorem ev155 (H : HookParams) : EntailsAtValues (cH H) U.ax155 (trS U.ax155).pat := by
  rw [(by decide +kernel : (trS U.ax155).pat = (trAxiom [] [] U.ax155).pat)]
  exact LibEv.tmodSmall_ev (coreOKH H) (shapesOKH H) U.ax155 (by decide +kernel) (by decide +kernel)

theorem ev157 (H : HookParams) : EntailsAtValues (cH H) U.ax157 (trS U.ax157).pat := by
  rw [(by decide +kernel : (trS U.ax157).pat = (trAxiom [] [] U.ax157).pat)]
  exact LibEv.addComm_ev (coreOKH H) (shapesOKH H) U.ax157 (by decide +kernel) (by decide +kernel)

theorem ev158 (H : HookParams) : EntailsAtValues (cH H) U.ax158 (trS U.ax158).pat := by
  rw [(by decide +kernel : (trS U.ax158).pat = (trAxiom [] [] U.ax158).pat)]
  exact LibEv.addZero_ev (coreOKH H) (shapesOKH H) U.ax158 (by decide +kernel) (by decide +kernel)

theorem ev159 (H : HookParams) : EntailsAtValues (cH H) U.ax159 (trS U.ax159).pat := by
  rw [(by decide +kernel : (trS U.ax159).pat = (trAxiom [] [] U.ax159).pat)]
  exact LibEv.addLeftComm_ev (coreOKH H) (shapesOKH H) U.ax159 (by decide +kernel) (by decide +kernel)

theorem ev160 (H : HookParams) : EntailsAtValues (cH H) U.ax160 (trS U.ax160).pat := by
  rw [(by decide +kernel : (trS U.ax160).pat = (trAxiom [] [] U.ax160).pat)]
  exact LibEv.addAssocRev_ev (coreOKH H) (shapesOKH H) U.ax160 (by decide +kernel) (by decide +kernel)

theorem ev161 (H : HookParams) : EntailsAtValues (cH H) U.ax161 (trS U.ax161).pat := by
  rw [(by decide +kernel : (trS U.ax161).pat = (trAxiom [] [] U.ax161).pat)]
  exact LibEv.addSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax161 (by decide +kernel) (by decide +kernel)

theorem ev162 (H : HookParams) : EntailsAtValues (cH H) U.ax162 (trS U.ax162).pat := by
  rw [(by decide +kernel : (trS U.ax162).pat = (trAxiom [] [] U.ax162).pat)]
  exact LibEv.addAssoc_ev (coreOKH H) (shapesOKH H) U.ax162 (by decide +kernel) (by decide +kernel)

theorem ev163 (H : HookParams) : EntailsAtValues (cH H) U.ax163 (trS U.ax163).pat := by
  rw [(by decide +kernel : (trS U.ax163).pat = (trAxiom [] [] U.ax163).pat)]
  exact LibEv.subAddComm_ev (coreOKH H) (shapesOKH H) U.ax163 (by decide +kernel) (by decide +kernel)

theorem ev164 (H : HookParams) : EntailsAtValues (cH H) U.ax164 (trS U.ax164).pat := by
  rw [(by decide +kernel : (trS U.ax164).pat = (trAxiom [] [] U.ax164).pat)]
  exact LibEv.subAsAdd_ev (coreOKH H) (shapesOKH H) U.ax164 (by decide +kernel) (by decide +kernel)

theorem ev165 (H : HookParams) : EntailsAtValues (cH H) U.ax165 (trS U.ax165).pat := by
  rw [(by decide +kernel : (trS U.ax165).pat = (trAxiom [] [] U.ax165).pat)]
  exact LibEv.subZero_ev (coreOKH H) (shapesOKH H) U.ax165 (by decide +kernel) (by decide +kernel)

theorem ev166 (H : HookParams) : EntailsAtValues (cH H) U.ax166 (trS U.ax166).pat := by
  rw [(by decide +kernel : (trS U.ax166).pat = (trAxiom [] [] U.ax166).pat)]
  exact LibEv.subAddSwap_ev (coreOKH H) (shapesOKH H) U.ax166 (by decide +kernel) (by decide +kernel)

theorem ev167 (H : HookParams) : EntailsAtValues (cH H) U.ax167 (trS U.ax167).pat := by
  rw [(by decide +kernel : (trS U.ax167).pat = (trAxiom [] [] U.ax167).pat)]
  exact LibEv.subAddAssoc_ev (coreOKH H) (shapesOKH H) U.ax167 (by decide +kernel) (by decide +kernel)

theorem ev168 (H : HookParams) : EntailsAtValues (cH H) U.ax168 (trS U.ax168).pat := by
  rw [(by decide +kernel : (trS U.ax168).pat = (trAxiom [] [] U.ax168).pat)]
  exact LibEv.subSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax168 (by decide +kernel) (by decide +kernel)

theorem ev169 (H : HookParams) : EntailsAtValues (cH H) U.ax169 (trS U.ax169).pat := by
  rw [(by decide +kernel : (trS U.ax169).pat = (trAxiom [] [] U.ax169).pat)]
  exact LibEv.subSubAdd_ev (coreOKH H) (shapesOKH H) U.ax169 (by decide +kernel) (by decide +kernel)

theorem ev172 (H : HookParams) : EntailsAtValues (cH H) U.ax172 (trS U.ax172).pat := by
  rw [(by decide +kernel : (trS U.ax172).pat = (trAxiom [] [] U.ax172).pat)]
  exact LibEv.fnNeBool_ev (coreOKH H) (shapesOKH H) U.ax172 (by decide +kernel) (by decide +kernel)

theorem ev173 (H : HookParams) : EntailsAtValues (cH H) U.ax173 (trS U.ax173).pat := by
  rw [(by decide +kernel : (trS U.ax173).pat = (trAxiom [] [] U.ax173).pat)]
  exact LibEv.fnNeInt_ev (coreOKH H) (shapesOKH H) U.ax173 (by decide +kernel) (by decide +kernel)

theorem ev174 (H : HookParams) : EntailsAtValues (cH H) U.ax174 (trS U.ax174).pat := by
  rw [(by decide +kernel : (trS U.ax174).pat = (trAxiom [] [] U.ax174).pat)]
  exact LibEv.fnNeK_ev (coreOKH H) U.ax174 (by decide +kernel) (by decide +kernel)

theorem ev175 (H : HookParams) : EntailsAtValues (cH H) U.ax175 (trS U.ax175).pat := by
  rw [(by decide +kernel : (trS U.ax175).pat = (trAxiom [] [] U.ax175).pat)]
  exact LibEv.boolKEq_ev (coreOKH H) (shapesOKH H) (boolBelowH H) U.ax175 (by decide +kernel)
    (by decide +kernel)

theorem ev176 (H : HookParams) : EntailsAtValues (cH H) U.ax176 (trS U.ax176).pat := by
  rw [(by decide +kernel : (trS U.ax176).pat = (trAxiom [] [] U.ax176).pat)]
  exact LibEv.intKEq_ev (coreOKH H) (shapesOKH H) (intBelowH H) U.ax176 (by decide +kernel)
    (by decide +kernel)

theorem ev179 (H : HookParams) : EntailsAtValues (cH H) U.ax179 (trS U.ax179).pat := by
  rw [(by decide +kernel : (trS U.ax179).pat = (trAxiom [] [] U.ax179).pat)]
  exact LibEv.fnAndFalse_ev (coreOKH H) (shapesOKH H) U.ax179 (by decide +kernel) (by decide +kernel)

theorem ev180 (H : HookParams) : EntailsAtValues (cH H) U.ax180 (trS U.ax180).pat := by
  rw [(by decide +kernel : (trS U.ax180).pat = (trAxiom [] [] U.ax180).pat)]
  exact LibEv.bAndTrue_ev (coreOKH H) (shapesOKH H) U.ax180 (by decide +kernel) (by decide +kernel)

theorem ev181 (H : HookParams) : EntailsAtValues (cH H) U.ax181 (trS U.ax181).pat := by
  rw [(by decide +kernel : (trS U.ax181).pat = (trAxiom [] [] U.ax181).pat)]
  exact LibEv.bAndFalse_ev (coreOKH H) (shapesOKH H) U.ax181 (by decide +kernel) (by decide +kernel)

theorem ev182 (H : HookParams) : EntailsAtValues (cH H) U.ax182 (trS U.ax182).pat := by
  rw [(by decide +kernel : (trS U.ax182).pat = (trAxiom [] [] U.ax182).pat)]
  exact LibEv.fnAndTrue_ev (coreOKH H) (shapesOKH H) U.ax182 (by decide +kernel) (by decide +kernel)

theorem ev183 (H : HookParams) : EntailsAtValues (cH H) U.ax183 (trS U.ax183).pat := by
  rw [(by decide +kernel : (trS U.ax183).pat = (trAxiom [] [] U.ax183).pat)]
  exact LibEv.fnAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax183 (by decide +kernel) (by decide +kernel)

theorem ev184 (H : HookParams) : EntailsAtValues (cH H) U.ax184 (trS U.ax184).pat := by
  rw [(by decide +kernel : (trS U.ax184).pat = (trAxiom [] [] U.ax184).pat)]
  exact LibEv.bAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax184 (by decide +kernel) (by decide +kernel)

theorem ev185 (H : HookParams) : EntailsAtValues (cH H) U.ax185 (trS U.ax185).pat := by
  rw [(by decide +kernel : (trS U.ax185).pat = (trAxiom [] [] U.ax185).pat)]
  exact LibEv.bAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax185 (by decide +kernel) (by decide +kernel)

theorem ev186 (H : HookParams) : EntailsAtValues (cH H) U.ax186 (trS U.ax186).pat := by
  rw [(by decide +kernel : (trS U.ax186).pat = (trAxiom [] [] U.ax186).pat)]
  exact LibEv.fnAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax186 (by decide +kernel) (by decide +kernel)

theorem ev187 (H : HookParams) : EntailsAtValues (cH H) U.ax187 (trS U.ax187).pat := by
  rw [(by decide +kernel : (trS U.ax187).pat = (trAxiom [] [] U.ax187).pat)]
  exact LibEv.fnDivInt_ev (coreOKH H) (shapesOKH H) U.ax187 (by decide +kernel) (by decide +kernel)

theorem ev189 (H : HookParams) : EntailsAtValues (cH H) U.ax189 (trS U.ax189).pat := by
  rw [(by decide +kernel : (trS U.ax189).pat = (trAxiom [] [] U.ax189).pat)]
  exact LibEv.bImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax189 (by decide +kernel) (by decide +kernel)

theorem ev190 (H : HookParams) : EntailsAtValues (cH H) U.ax190 (trS U.ax190).pat := by
  rw [(by decide +kernel : (trS U.ax190).pat = (trAxiom [] [] U.ax190).pat)]
  exact LibEv.bImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax190 (by decide +kernel) (by decide +kernel)

theorem ev191 (H : HookParams) : EntailsAtValues (cH H) U.ax191 (trS U.ax191).pat := by
  rw [(by decide +kernel : (trS U.ax191).pat = (trAxiom [] [] U.ax191).pat)]
  exact LibEv.fnImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax191 (by decide +kernel) (by decide +kernel)

theorem ev192 (H : HookParams) : EntailsAtValues (cH H) U.ax192 (trS U.ax192).pat := by
  rw [(by decide +kernel : (trS U.ax192).pat = (trAxiom [] [] U.ax192).pat)]
  exact LibEv.fnImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax192 (by decide +kernel) (by decide +kernel)

theorem ev193 (H : HookParams) : EntailsAtValues (cH H) U.ax193 (trS U.ax193).pat := by
  rw [(by decide +kernel : (trS U.ax193).pat = (trAxiom [] [] U.ax193).pat)]
  exact LibEv.emodAsTmod_ev (coreOKH H) (shapesOKH H) U.ax193 (by decide +kernel) (by decide +kernel)

theorem ev194 (H : HookParams) : EntailsAtValues (cH H) U.ax194 (trS U.ax194).pat := by
  rw [(by decide +kernel : (trS U.ax194).pat = (trAxiom [] [] U.ax194).pat)]
  exact LibEv.emodSmall_ev (coreOKH H) (shapesOKH H) U.ax194 (by decide +kernel) (by decide +kernel)

theorem ev195 (H : HookParams) : EntailsAtValues (cH H) U.ax195 (trS U.ax195).pat := by
  rw [(by decide +kernel : (trS U.ax195).pat = (trAxiom [] [] U.ax195).pat)]
  exact LibEv.bOrFalse_ev (coreOKH H) (shapesOKH H) U.ax195 (by decide +kernel) (by decide +kernel)

theorem ev196 (H : HookParams) : EntailsAtValues (cH H) U.ax196 (trS U.ax196).pat := by
  rw [(by decide +kernel : (trS U.ax196).pat = (trAxiom [] [] U.ax196).pat)]
  exact LibEv.bOrTrue_ev (coreOKH H) (shapesOKH H) U.ax196 (by decide +kernel) (by decide +kernel)

theorem ev197 (H : HookParams) : EntailsAtValues (cH H) U.ax197 (trS U.ax197).pat := by
  rw [(by decide +kernel : (trS U.ax197).pat = (trAxiom [] [] U.ax197).pat)]
  exact LibEv.fnOrFalse_ev (coreOKH H) (shapesOKH H) U.ax197 (by decide +kernel) (by decide +kernel)

theorem ev198 (H : HookParams) : EntailsAtValues (cH H) U.ax198 (trS U.ax198).pat := by
  rw [(by decide +kernel : (trS U.ax198).pat = (trAxiom [] [] U.ax198).pat)]
  exact LibEv.fnOrTrue_ev (coreOKH H) (shapesOKH H) U.ax198 (by decide +kernel) (by decide +kernel)

theorem ev199 (H : HookParams) : EntailsAtValues (cH H) U.ax199 (trS U.ax199).pat := by
  rw [(by decide +kernel : (trS U.ax199).pat = (trAxiom [] [] U.ax199).pat)]
  exact LibEv.bOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax199 (by decide +kernel) (by decide +kernel)

theorem ev200 (H : HookParams) : EntailsAtValues (cH H) U.ax200 (trS U.ax200).pat := by
  rw [(by decide +kernel : (trS U.ax200).pat = (trAxiom [] [] U.ax200).pat)]
  exact LibEv.bOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax200 (by decide +kernel) (by decide +kernel)

theorem ev201 (H : HookParams) : EntailsAtValues (cH H) U.ax201 (trS U.ax201).pat := by
  rw [(by decide +kernel : (trS U.ax201).pat = (trAxiom [] [] U.ax201).pat)]
  exact LibEv.fnOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax201 (by decide +kernel) (by decide +kernel)

theorem ev202 (H : HookParams) : EntailsAtValues (cH H) U.ax202 (trS U.ax202).pat := by
  rw [(by decide +kernel : (trS U.ax202).pat = (trAxiom [] [] U.ax202).pat)]
  exact LibEv.fnOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax202 (by decide +kernel) (by decide +kernel)

theorem ev203 (H : HookParams) : EntailsAtValues (cH H) U.ax203 (trS U.ax203).pat := by
  rw [(by decide +kernel : (trS U.ax203).pat = (trAxiom [] [] U.ax203).pat)]
  exact LibEv.fnXorSame_ev (coreOKH H) (shapesOKH H) U.ax203 (by decide +kernel) (by decide +kernel)

theorem ev204 (H : HookParams) : EntailsAtValues (cH H) U.ax204 (trS U.ax204).pat := by
  rw [(by decide +kernel : (trS U.ax204).pat = (trAxiom [] [] U.ax204).pat)]
  exact LibEv.bXorFalse_ev (coreOKH H) (shapesOKH H) U.ax204 (by decide +kernel) (by decide +kernel)

theorem ev205 (H : HookParams) : EntailsAtValues (cH H) U.ax205 (trS U.ax205).pat := by
  rw [(by decide +kernel : (trS U.ax205).pat = (trAxiom [] [] U.ax205).pat)]
  exact LibEv.fnXorFalse_ev (coreOKH H) (shapesOKH H) U.ax205 (by decide +kernel) (by decide +kernel)

theorem ev206 (H : HookParams) : EntailsAtValues (cH H) U.ax206 (trS U.ax206).pat := by
  rw [(by decide +kernel : (trS U.ax206).pat = (trAxiom [] [] U.ax206).pat)]
  exact LibEv.fnSetUnion_ev (coreOKH H) (shapesOKH H) U.ax206 (by decide +kernel) (by decide +kernel)

theorem ev208 (H : HookParams) : EntailsAtValues (cH H) U.ax208 (trS U.ax208).pat := by
  rw [(by decide +kernel : (trS U.ax208).pat = (trAxiom [] [] U.ax208).pat)]
  exact LibEv.fnFreshInt_ev (coreOKH H) (shapesOKH H) U.ax208 (by decide +kernel) (by decide +kernel)

theorem ev244 (H : HookParams) : EntailsAtValues (cH H) U.ax244 (trS U.ax244).pat := by
  rw [(by decide +kernel : (trS U.ax244).pat = (trAxiom [] [] U.ax244).pat)]
  exact LibEv.fnMinLt_ev (coreOKH H) (shapesOKH H) U.ax244 (by decide +kernel) (by decide +kernel)

theorem ev245 (H : HookParams) : EntailsAtValues (cH H) U.ax245 (trS U.ax245).pat := by
  rw [(by decide +kernel : (trS U.ax245).pat = (trAxiom [] [] U.ax245).pat)]
  exact LibEv.fnMinGe_ev (coreOKH H) (shapesOKH H) U.ax245 (by decide +kernel) (by decide +kernel)

theorem ev246 (H : HookParams) : EntailsAtValues (cH H) U.ax246 (trS U.ax246).pat := by
  rw [(by decide +kernel : (trS U.ax246).pat = (trAxiom [] [] U.ax246).pat)]
  exact LibEv.fnNotFalse_ev (coreOKH H) U.ax246 (by decide +kernel) (by decide +kernel)

theorem ev247 (H : HookParams) : EntailsAtValues (cH H) U.ax247 (trS U.ax247).pat := by
  rw [(by decide +kernel : (trS U.ax247).pat = (trAxiom [] [] U.ax247).pat)]
  exact LibEv.fnNotTrue_ev (coreOKH H) U.ax247 (by decide +kernel) (by decide +kernel)

theorem ev262 (H : HookParams) : EntailsAtValues (cH H) U.ax262 (trS U.ax262).pat := by
  rw [(by decide +kernel : (trS U.ax262).pat = (trAxiom [] [] U.ax262).pat)]
  exact LibEv.fnPushList_ev (coreOKH H) (shapesOKH H) U.ax262 (by decide +kernel) (by decide +kernel)

theorem ev170 (H : HookParams) : EntailsAtValues (cH H) U.ax170 (trS U.ax170).pat := by
  rw [(by decide +kernel : (trS U.ax170).pat = (trAxiom [] [] U.ax170).pat)]
  exact LibEv.shlZero_ev (coreOKH H) (shapesOKH H) U.ax170 (by decide +kernel) (by decide +kernel)

theorem ev171 (H : HookParams) : EntailsAtValues (cH H) U.ax171 (trS U.ax171).pat := by
  rw [(by decide +kernel : (trS U.ax171).pat = (trAxiom [] [] U.ax171).pat)]
  exact LibEv.zeroShl_ev (coreOKH H) (shapesOKH H) U.ax171 (by decide +kernel) (by decide +kernel)

theorem ev177 (H : HookParams) : EntailsAtValues (cH H) U.ax177 (trS U.ax177).pat := by
  rw [(by decide +kernel : (trS U.ax177).pat = (trAxiom [] [] U.ax177).pat)]
  exact LibEv.shrZero_ev (coreOKH H) (shapesOKH H) U.ax177 (by decide +kernel) (by decide +kernel)

theorem ev178 (H : HookParams) : EntailsAtValues (cH H) U.ax178 (trS U.ax178).pat := by
  rw [(by decide +kernel : (trS U.ax178).pat = (trAxiom [] [] U.ax178).pat)]
  exact LibEv.zeroShr_ev (coreOKH H) (shapesOKH H) U.ax178 (by decide +kernel) (by decide +kernel)

/-- The 56 sentences of `evN`. -/
noncomputable def evText : List AxiomDecl :=
  [U.ax155, U.ax157, U.ax158, U.ax159, U.ax160, U.ax161, U.ax162, U.ax163, U.ax164, U.ax165,
   U.ax166, U.ax167, U.ax168, U.ax169, U.ax172, U.ax173, U.ax174, U.ax175, U.ax176, U.ax179,
   U.ax180, U.ax181, U.ax182, U.ax183, U.ax184, U.ax185, U.ax186, U.ax187, U.ax189, U.ax190,
   U.ax191, U.ax192, U.ax193, U.ax194, U.ax195, U.ax196, U.ax197, U.ax198, U.ax199, U.ax200,
   U.ax201, U.ax202, U.ax203, U.ax204, U.ax205, U.ax206, U.ax208, U.ax244, U.ax245, U.ax246,
   U.ax247, U.ax262,
   U.ax170, U.ax171, U.ax177, U.ax178]

theorem ev_entailed (H : HookParams) : ∀ ad ∈ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev155 H, List.forall_mem_cons.mpr ⟨ev157 H, List.forall_mem_cons.mpr ⟨ev158 H, List.forall_mem_cons.mpr ⟨ev159 H, List.forall_mem_cons.mpr ⟨ev160 H, List.forall_mem_cons.mpr ⟨ev161 H, List.forall_mem_cons.mpr ⟨ev162 H, List.forall_mem_cons.mpr ⟨ev163 H, List.forall_mem_cons.mpr ⟨ev164 H, List.forall_mem_cons.mpr ⟨ev165 H, List.forall_mem_cons.mpr ⟨ev166 H, List.forall_mem_cons.mpr ⟨ev167 H, List.forall_mem_cons.mpr ⟨ev168 H, List.forall_mem_cons.mpr ⟨ev169 H, List.forall_mem_cons.mpr ⟨ev172 H, List.forall_mem_cons.mpr ⟨ev173 H, List.forall_mem_cons.mpr ⟨ev174 H, List.forall_mem_cons.mpr ⟨ev175 H, List.forall_mem_cons.mpr ⟨ev176 H, List.forall_mem_cons.mpr ⟨ev179 H, List.forall_mem_cons.mpr ⟨ev180 H, List.forall_mem_cons.mpr ⟨ev181 H, List.forall_mem_cons.mpr ⟨ev182 H, List.forall_mem_cons.mpr ⟨ev183 H, List.forall_mem_cons.mpr ⟨ev184 H, List.forall_mem_cons.mpr ⟨ev185 H, List.forall_mem_cons.mpr ⟨ev186 H, List.forall_mem_cons.mpr ⟨ev187 H, List.forall_mem_cons.mpr ⟨ev189 H, List.forall_mem_cons.mpr ⟨ev190 H, List.forall_mem_cons.mpr ⟨ev191 H, List.forall_mem_cons.mpr ⟨ev192 H, List.forall_mem_cons.mpr ⟨ev193 H, List.forall_mem_cons.mpr ⟨ev194 H, List.forall_mem_cons.mpr ⟨ev195 H, List.forall_mem_cons.mpr ⟨ev196 H, List.forall_mem_cons.mpr ⟨ev197 H, List.forall_mem_cons.mpr ⟨ev198 H, List.forall_mem_cons.mpr ⟨ev199 H, List.forall_mem_cons.mpr ⟨ev200 H, List.forall_mem_cons.mpr ⟨ev201 H, List.forall_mem_cons.mpr ⟨ev202 H, List.forall_mem_cons.mpr ⟨ev203 H, List.forall_mem_cons.mpr ⟨ev204 H, List.forall_mem_cons.mpr ⟨ev205 H, List.forall_mem_cons.mpr ⟨ev206 H, List.forall_mem_cons.mpr ⟨ev208 H, List.forall_mem_cons.mpr ⟨ev244 H, List.forall_mem_cons.mpr ⟨ev245 H, List.forall_mem_cons.mpr ⟨ev246 H, List.forall_mem_cons.mpr ⟨ev247 H, List.forall_mem_cons.mpr ⟨ev262 H, List.forall_mem_cons.mpr ⟨ev170 H, List.forall_mem_cons.mpr ⟨ev171 H, List.forall_mem_cons.mpr ⟨ev177 H, List.forall_mem_cons.mpr ⟨ev178 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the Bool predicate sentences over set variables (8), at set values -/

theorem ev138 (H : HookParams) : EntailsAtSetValues (cH H) U.ax138 (trS U.ax138).pat := by
  rw [(by decide +kernel : (trS U.ax138).pat = (trAxiom [] [] U.ax138).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) false U.ax138 (by decide +kernel) (by decide +kernel)

theorem ev139 (H : HookParams) : EntailsAtSetValues (cH H) U.ax139 (trS U.ax139).pat := by
  rw [(by decide +kernel : (trS U.ax139).pat = (trAxiom [] [] U.ax139).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) false U.ax139 (by decide +kernel) (by decide +kernel)

theorem ev140 (H : HookParams) : EntailsAtSetValues (cH H) U.ax140 (trS U.ax140).pat := by
  rw [(by decide +kernel : (trS U.ax140).pat = (trAxiom [] [] U.ax140).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false false U.ax140 (by decide +kernel) (by decide +kernel)

theorem ev141 (H : HookParams) : EntailsAtSetValues (cH H) U.ax141 (trS U.ax141).pat := by
  rw [(by decide +kernel : (trS U.ax141).pat = (trAxiom [] [] U.ax141).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true false U.ax141 (by decide +kernel) (by decide +kernel)

theorem ev146 (H : HookParams) : EntailsAtSetValues (cH H) U.ax146 (trS U.ax146).pat := by
  rw [(by decide +kernel : (trS U.ax146).pat = (trAxiom [] [] U.ax146).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) true U.ax146 (by decide +kernel) (by decide +kernel)

theorem ev147 (H : HookParams) : EntailsAtSetValues (cH H) U.ax147 (trS U.ax147).pat := by
  rw [(by decide +kernel : (trS U.ax147).pat = (trAxiom [] [] U.ax147).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false true U.ax147 (by decide +kernel) (by decide +kernel)

theorem ev152 (H : HookParams) : EntailsAtSetValues (cH H) U.ax152 (trS U.ax152).pat := by
  rw [(by decide +kernel : (trS U.ax152).pat = (trAxiom [] [] U.ax152).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) true U.ax152 (by decide +kernel) (by decide +kernel)

theorem ev153 (H : HookParams) : EntailsAtSetValues (cH H) U.ax153 (trS U.ax153).pat := by
  rw [(by decide +kernel : (trS U.ax153).pat = (trAxiom [] [] U.ax153).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true true U.ax153 (by decide +kernel) (by decide +kernel)

/-- The eight sentences over set variables. -/
noncomputable def setText : List AxiomDecl :=
  [U.ax138, U.ax139, U.ax140, U.ax141, U.ax146, U.ax147, U.ax152, U.ax153]

/-! ## The class -/

/-- **Ev for the library sentences over element variables**: the 16 predicate equations and the 56
term and function equations, for every H. -/
theorem lib_entailed (H : HookParams) : ∀ ad ∈ predText ++ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  fun ad had => (List.mem_append.mp had).elim (pred_entailed H ad) (ev_entailed H ad)

/-- **The library sentences over set variables are entailed at set values**, for every H. -/
theorem libSet_entailed (H : HookParams) : ∀ ad ∈ setText, EntailsAtSetValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev138 H, List.forall_mem_cons.mpr ⟨ev139 H, List.forall_mem_cons.mpr ⟨ev140 H, List.forall_mem_cons.mpr ⟨ev141 H, List.forall_mem_cons.mpr ⟨ev146 H, List.forall_mem_cons.mpr ⟨ev147 H, List.forall_mem_cons.mpr ⟨ev152 H, List.forall_mem_cons.mpr ⟨ev153 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩

/-- The 80 library sentences tied here. -/
theorem lib_indices : (predText ++ evText ++ setText).map (·.index) =
    [130, 131, 132, 133, 134, 135, 136, 137, 142, 143, 144, 145, 148, 149, 150, 151, 155, 157, 158, 159,
   160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 172, 173, 174, 175, 176, 179, 180, 181, 182, 183,
   184, 185, 186, 187, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
   205, 206, 208, 244, 245, 246, 247, 262, 170, 171, 177, 178, 138, 139, 140, 141, 146, 147, 152, 153] := by
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

theorem t125 : (trS U.ax125).pat = (trAxiom [] [] U.ax125).pat := by decide +kernel
theorem t126 : (trS U.ax126).pat = (trAxiom [] [] U.ax126).pat := by decide +kernel
theorem t127 : (trS U.ax127).pat = (trAxiom [] [] U.ax127).pat := by decide +kernel
theorem t128 : (trS U.ax128).pat = (trAxiom [] [] U.ax128).pat := by decide +kernel
theorem t129 : (trS U.ax129).pat = (trAxiom [] [] U.ax129).pat := by decide +kernel

theorem s125_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax125.ax ∧ SetVarsAtValues (cH H) I e U.ax125.ax ∧
      ¬ (trS U.ax125).pat.interpret I e default := by
  rw [t125]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTMod intNe (by decide +kernel) (by rfl) 0 1 0
    ⟨_, LibEv.hv_intTMod (by decide)⟩ (by rw [LibEv.hv_intNe]; rfl) U.ax125 (by decide +kernel) (by decide +kernel) hI
theorem s126_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax126.ax ∧ SetVarsAtValues (cH H) I e U.ax126.ax ∧
      ¬ (trS U.ax126).pat.interpret I e default := by
  rw [t126]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intTDiv intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_tdiv 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax126
    (by decide +kernel) (by decide +kernel) hI
theorem s129_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax129.ax ∧ SetVarsAtValues (cH H) I e U.ax129.ax ∧
      ¬ (trS U.ax129).pat.interpret I e default := by
  rw [t129]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intEMod intNe (by decide +kernel) (by rfl) 0 1 0
    ((LibEv.ceil_fg_emod 0 1).mpr (by rw [LibEv.hv_intNe]; rfl)) (by rw [LibEv.hv_intNe]; rfl) U.ax129
    (by decide +kernel) (by decide +kernel) hI
theorem s127_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax127.ax ∧ SetVarsAtValues (cH H) I e U.ax127.ax ∧
      ¬ (trS U.ax127).pat.interpret I e default := by
  rw [t127]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShl intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shl 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax127
    (by decide +kernel) (by decide +kernel) hI
theorem s128_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax128.ax ∧ SetVarsAtValues (cH H) I e U.ax128.ax ∧
      ¬ (trS U.ax128).pat.interpret I e default := by
  rw [t128]
  exact LibEv.ceilInt_refuted_at (coreOKH' H) intShr intGe (by decide +kernel) (by rfl) 0 0 (-1)
    ((LibEv.ceil_fg_shr 0 0).mpr (by rw [LibEv.fhv_intGe]; rfl)) (by rw [LibEv.fhv_intGe]; rfl) U.ax128
    (by decide +kernel) (by decide +kernel) hI

theorem s125_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax125).pat) := refuted_of_at (s125_at H)
theorem s126_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax126).pat) := refuted_of_at (s126_at H)
theorem s127_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax127).pat) := refuted_of_at (s127_at H)
theorem s128_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax128).pat) := refuted_of_at (s128_at H)
theorem s129_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax129).pat) := refuted_of_at (s129_at H)

theorem s125_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax125 (trS U.ax125).pat := by
  rw [t125]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tmod U.ax125 (by decide +kernel) (by decide +kernel)
theorem s126_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax126 (trS U.ax126).pat := by
  rw [t126]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intTDiv intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_tdiv U.ax126 (by decide +kernel) (by decide +kernel)
theorem s127_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax127 (trS U.ax127).pat := by
  rw [t127]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShl intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shl U.ax127 (by decide +kernel) (by decide +kernel)
theorem s128_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax128 (trS U.ax128).pat := by
  rw [t128]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intShr intGe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_shr U.ax128 (by decide +kernel) (by decide +kernel)
theorem s129_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax129 (trS U.ax129).pat := by
  rw [t129]
  exact LibEv.ceilInt_one (coreOKH' H) (shapesOKH H) intEMod intNe (by decide +kernel) (by rfl)
    LibEv.ceil_fg_emod U.ax129 (by decide +kernel) (by decide +kernel)

/-! ## The Map lemma -/

theorem t264 : (trS U.ax264).pat = (trAxiom [] [] U.ax264).pat := by decide +kernel

/-- The KItem injection of 0. -/
def k0 : GroundTerm := .inj Srt.int Srt.kitem (KCore.int 0)

theorem sort_k0 (H : HookParams) : (cH H).sortOf k0 = some Srt.kitem := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem sort_m0 (H : HookParams) : (cH H).sortOf (.map Srt.map []) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel
theorem sort_m1 (H : HookParams) : (cH H).sortOf (.map Srt.map [(k0, k0)]) = some Srt.map := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel

theorem s264_at (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax264.ax ∧ SetVarsAtValues (cH H) I e U.ax264.ax ∧
      ¬ (trS U.ax264).pat.interpret I e default := by
  rw [t264]
  exact LibEv.ceilMap_refuted_at (coreOKH' H) (by decide +kernel) (by rfl) k0 k0 [] [(k0, k0)] (sort_k0 H) (sort_k0 H)
    (sort_m0 H) (sort_m1 H) rfl (by decide +kernel) U.ax264 (by decide +kernel) (by decide +kernel) hI

theorem s264_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax264).pat) := refuted_of_at (s264_at H)

theorem s264_one (H : HookParams) : LibEv.SvAtMostOne (cH H) U.ax264 (trS U.ax264).pat := by
  rw [t264]
  exact LibEv.ceilMap_one (coreOKH' H) (shapesOKH H) (by decide +kernel) (by rfl)
    (by decide +kernel : apartSort c Srt.map = true) U.ax264 (by decide +kernel) (by decide +kernel)

end Ceil

/-- The sentences of the class set-variable lemma. -/
theorem setvar_indices : [U.ax125, U.ax126, U.ax127, U.ax128, U.ax129, U.ax264].map (·.index) =
    [125, 126, 127, 128, 129, 264] := by decide +kernel

/-! ## The accounts against the class lists -/

/-- The class lists of test/TieUnbound.lean (`classes`), as written there. -/
def hookedClass : List Nat :=
  [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 56, 64,
   65, 66, 67, 68, 69, 70, 71, 72, 74, 76, 79, 82, 84, 100, 101, 102, 103, 106, 107, 108, 109, 110, 111]
def lawClass : List Nat := [53, 54, 55, 57, 58, 59, 60, 62, 63]
def libraryClass : List Nat :=
  [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
   150, 151, 152, 153, 155, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171,
   172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 189, 190, 191, 192,
   193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 242, 243, 244, 245,
   246, 247, 262, 263]
def setvarClass : List Nat := [125, 126, 127, 128, 129, 264]

/-- Hooked functional: the 47 tied and 100 (`ite`'s, owed) are the class. -/
theorem hooked_account : (funText.map (fun ad : AxiomDecl => ad.index) ++ [100]).isPerm hookedClass = true := by
  rw [fun_indices]; decide
/-- Collection law: the nine tied are the class. -/
theorem law_account : lawText.map (·.index) = lawClass := law_indices
/-- Library: the 80 tied, and 207, 263 (`bitRangeInt`, `signExtendBitRangeInt`) and 242, 243 (`ite{SortK}`),
owed, are the class. -/
theorem library_account : ((predText ++ evText ++ setText).map (fun ad : AxiomDecl => ad.index) ++ [207, 242, 243, 263]).isPerm libraryClass = true := by
  rw [lib_indices]; decide
/-- Set-variable lemma: the six refuted are the class. -/
theorem setvar_account : [U.ax125, U.ax126, U.ax127, U.ax128, U.ax129, U.ax264].map (·.index) = setvarClass :=
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
theorem setvar_refuted_c (H : HookParams) : ∀ ad ∈ [U.ax125, U.ax126, U.ax127, U.ax128, U.ax129, U.ax264],
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS ad).pat) := by
  have hs : ∀ ad ∈ [U.ax125, U.ax126, U.ax127, U.ax128, U.ax129, U.ax264],
      ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS ad).pat) :=
    List.forall_mem_cons.mpr ⟨s125_refuted H, List.forall_mem_cons.mpr ⟨s126_refuted H,
      List.forall_mem_cons.mpr ⟨s127_refuted H, List.forall_mem_cons.mpr ⟨s128_refuted H,
      List.forall_mem_cons.mpr ⟨s129_refuted H, List.forall_mem_cons.mpr ⟨s264_refuted H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩
  intro ad had M hM I hI
  exact hs ad had M hM I fun ψ hψ => hI ψ (Or.inl hψ)

end KCore.TieUnboundAtValues

#print axioms KCore.TieUnboundAtValues.fun_entailed
#print axioms KCore.TieUnboundAtValues.fun_indices
#print axioms KCore.TieUnboundAtValues.laws_entailed
#print axioms KCore.TieUnboundAtValues.law_indices
#print axioms KCore.TieUnboundAtValues.pred_entailed
#print axioms KCore.TieUnboundAtValues.ev_entailed
#print axioms KCore.TieUnboundAtValues.lib_entailed
#print axioms KCore.TieUnboundAtValues.libSet_entailed
#print axioms KCore.TieUnboundAtValues.lib_indices
#print axioms KCore.TieUnboundAtValues.s125_refuted
#print axioms KCore.TieUnboundAtValues.s126_refuted
#print axioms KCore.TieUnboundAtValues.s127_refuted
#print axioms KCore.TieUnboundAtValues.s128_refuted
#print axioms KCore.TieUnboundAtValues.s129_refuted
#print axioms KCore.TieUnboundAtValues.s264_refuted
#print axioms KCore.TieUnboundAtValues.s125_one
#print axioms KCore.TieUnboundAtValues.s126_one
#print axioms KCore.TieUnboundAtValues.s127_one
#print axioms KCore.TieUnboundAtValues.s128_one
#print axioms KCore.TieUnboundAtValues.s129_one
#print axioms KCore.TieUnboundAtValues.s264_one
#print axioms KCore.TieUnboundAtValues.setvar_indices
#print axioms KCore.TieUnboundAtValues.hooked_account
#print axioms KCore.TieUnboundAtValues.law_account
#print axioms KCore.TieUnboundAtValues.library_account
#print axioms KCore.TieUnboundAtValues.setvar_account
#print axioms KCore.TieUnboundAtValues.fun_entailed_c
#print axioms KCore.TieUnboundAtValues.laws_entailed_c
#print axioms KCore.TieUnboundAtValues.lib_entailed_c
#print axioms KCore.TieUnboundAtValues.libSet_entailed_c
#print axioms KCore.TieUnboundAtValues.setvar_refuted_c
