/-
  Row KORE in K, the classes function functional, hooked functional, collection law and library on
  kore.k's text as kompile wrote it (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`),
  entailed at values, for every interpretation H or for every H meeting `Semantics.libAdmitted`.
  The semantics is the generated package's `RefKk.defn.sem`, and its `coreOK`, which the library's
  statements take, is the package's `RefKk.coreOK_defn`. Each sentence is tied by the library's one
  statement of it (KcoreSpec/LibEv*.lean): the text's axiom is compared with the statement's
  pattern over the registry's names, and its translation with the text's declarations with the
  translation the statement is about. The class lists are those of test/TieKk.lean `classes`.
  Run from the package root with the package built (test/kk-tie-atvalues.sh does both):
  `LEAN_PATH=.lake/pins/kk-tie/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) lean test/TieKkAtValues.lean`.

  - Function functional (`fnFun_at_values`, `fnFun_indices`): the class's 32 sentences, the
    `functional` sentences of the sort predicates `isX`, hold at values in every model of `Γc` for
    every H, from the sort predicates' own results and without `FnHyp`
    (`LibEv.sortPredFun_evC_withHooks`: `coreOK`, the clauses' predicates `\top`, no `\exists` in a
    clause, and no condition over a variable the patterns leave open, `fnFun_clauses`).
  - Hooked functional (`fun_entailed`, `funS_entailed`, `fun_indices`): the class's 61 sentences
    `\exists{R}(Val:s, \equals{s, R}(Val:s, f(K0:s0, …)))` whose symbol is an interpreted hooked
    symbol (`LibEv.functional_ev`). 58 are of symbols that are not partial, for every H; 3, of
    `countAllOccurrences` (202), `replaceAll` (321) and `substrString` (341), which `hook` leaves
    without a value at points where the library's text declares them `total` (`totalSilentKeys`),
    for every H meeting `silentTotal`, the first conjunct of `libAdmitted` (`funS_entailed`;
    `funS_lib` at `HookParams.lib`).
  - Collection law (`laws_entailed`, `law_indices`): associativity and the two units of `_List_`,
    `_Map_`, `_Set_` (LibEvLaw.lean), the nine sentences of the class.
  - Library (`lib_entailed`, `libSet_entailed`, `libA_entailed`, `lib_indices`): 100 of the
    class's 101. The sixteen predicate equations of `==Int`, `=/=Int`, `==K`, `=/=K`
    (`pred_entailed`); 74 term and function equations, each by its own theorem (`evN`), those of
    STRING-COMMON among them (domains.md 1787 to 1925: `Bool2String`, `String2Bool`, the String
    comparisons, `findChar` and `rfindChar` at the empty set of characters, `countAllOccurrences`
    where the needle does not occur, `replaceFirst`, `replace`, `S1 ==K S2`); the eight Bool
    predicate sentences over set variables (392 to 395, 400, 401, 406, 407), entailed at set
    values (`EntailsAtSetValues`); and 795 (`replaceAll`, 1917) and 802 (`rfindChar`, 1893), for
    every H meeting `libAdmitted` (`libA_entailed`; `ev795_lib`, `ev802_lib` at `HookParams.lib`).
    The 101st, 521 (`countAllOccurrences`' second equation, 1898), is refuted with the class's 202
    for every H (test/TieKkRefuted.lean `s521_202_refuted`).
-/
import RefKk.CoreOK

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKkAtValues

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := RefKk.defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOKH (H : HookParams) : (cH H).coreOK = true :=
  (Semantics.coreOK_withHooks c H).trans RefKk.coreOK_defn
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)
theorem boolBelowH (H : HookParams) : Srt.bool ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.bool = true)
theorem intBelowH (H : HookParams) : Srt.int ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.int = true)
theorem stringBelowH (H : HookParams) : Srt.string ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.string = true)

/-! ## Function functional (32): the sort predicates' `functional` sentences, at values in every model of Γc -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat :=
  [249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268,
   269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) =
    [249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268,
     269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280] := by
  decide +kernel

/-- The sentence is the `functional` sentence of a sort predicate of `c`, over the one sort
variable `R`, with its variables' sorts the registry's. -/
noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- None of the 32 reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- The clauses' predicates are `\top`, no clause binds a variable by `\exists`, and no clause has
a condition over a variable its patterns leave open. -/
theorem fnFun_clauses : c.clausesPreTop = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => !cl.reqOpen) = true := by
  decide +kernel

theorem fnFun_noWitH (H : HookParams) : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = false := by
  intro fn hfn cl hcl
  have h := List.all_eq_true.mp (List.all_eq_true.mp fnFun_clauses.2.2 fn hfn) cl hcl
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  simp [Clause.needsWitness, h]

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), without `FnHyp`. -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
  simp only [fnFunOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany⟩ := hok
  obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
  exact LibEv.sortPredFun_evC_withHooks H RefKk.coreOK_defn fnFun_clauses.1
    (Semantics.fnsNoExs_of_all fnFun_clauses.2.1)
    (fun fn hfn cl hcl hw => absurd hw (by rw [fnFun_noWitH H fn hfn cl hcl]; decide)) hfn hfp.2 ad hfp.1 hsv

/-! ## Hooked functional (61) -/

/-- The indices of the 58 sentences of symbols that are not partial. -/
def funIdx : List Nat :=
  [42, 43, 48, 61, 63, 64, 65, 66, 67, 68, 69, 71, 72, 73, 74, 78, 80, 81, 82, 83,
   84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 99, 107, 108, 109, 110, 111, 112, 113,
   114, 115, 117, 119, 120, 233, 248, 287, 292, 300, 301, 311, 319, 320, 322, 330, 331, 332]

/-- The sentences, in text order. -/
noncomputable def funText : List AxiomDecl := U.all.filter fun ad => funIdx.contains ad.index

theorem fun_indices : funText.map (·.index) =
    [42, 43, 48, 61, 63, 64, 65, 66, 67, 68, 69, 71, 72, 73, 74, 78, 80, 81, 82, 83,
     84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 99, 107, 108, 109, 110, 111, 112, 113,
     114, 115, 117, 119, 120, 233, 248, 287, 292, 300, 301, 311, 319, 320, 322, 330, 331, 332] := by
  decide +kernel

/-- The indices of the 3 sentences of symbols of `totalSilentKeys`. -/
def funSIdx : List Nat := [202, 321, 341]

noncomputable def funSText : List AxiomDecl := U.all.filter fun ad => funSIdx.contains ad.index

theorem funS_indices : funSText.map (·.index) = [202, 321, 341] := by decide +kernel

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

/-- The sentence is the `functional` sentence of a symbol of `hookSigs` in `totalSilentKeys`, over
the one sort variable `R`. -/
def funSOK (ad : AxiomDecl) : Bool :=
  match sigOf ad with
  | some k => decide (ad.ax.pattern = LibEv.funPatR k) && decide (ad.ax.sortVars = [Rv]) && LibEv.funReg k &&
      totalSilentKeys.contains k.name
  | none => false

theorem fun_checked : funText.all funOK = true := by decide +kernel
theorem funS_checked : funSText.all funSOK = true := by decide +kernel

/-- None of the 61 reads a declaration or an alias. -/
theorem fun_trS : (funText ++ funSText).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **Ev for the `functional` sentences of the interpreted symbols that are not partial**: each of
the 58 holds in every model of Γ at every valuation sending its variables to values, for every H. -/
theorem fun_entailed (H : HookParams) : ∀ ad ∈ funText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fun_trS ad (List.mem_append_left _ had))]
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

/-- **Ev for the `functional` sentences of `countAllOccurrences`, `replaceAll` and
`substrString`**, for every H under which `silentTotal` holds. -/
theorem funS_entailed (H : HookParams) (ht : (cH H).silentTotal) :
    ∀ ad ∈ funSText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fun_trS ad (List.mem_append_right _ had))]
  have hok := List.all_eq_true.mp funS_checked ad had
  unfold funSOK at hok
  cases hsig : sigOf ad with
  | none => rw [hsig] at hok; cases hok
  | some k =>
    rw [hsig] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hp, hsv⟩, hreg⟩, hts⟩ := hok
    obtain ⟨n, -, hfind⟩ := Option.bind_eq_some_iff.mp hsig
    exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (List.mem_of_find?_eq_some hfind)
      (Or.inr (Or.inl ⟨List.contains_iff_mem.mp hts, ht⟩)) hreg ad hp hsv

theorem funS_lib : ∀ ad ∈ funSText, EntailsAtValues (cH HookParams.lib) ad (trS ad).pat :=
  funS_entailed HookParams.lib (libAdmitted_lib_of_coreOK RefKk.coreOK_defn).1

/-! ## Collection laws (9) -/

theorem law96 (H : HookParams) : EntailsAtValues (cH H) U.ax96 (trS U.ax96).pat := by
  rw [(by decide +kernel : (trS U.ax96).pat = (trAxiom [] [] U.ax96).pat)]
  exact LibEv.listAssoc_ev (coreOKH H) (shapesOKH H) U.ax96 (by decide +kernel) (by decide +kernel)

theorem law97 (H : HookParams) : EntailsAtValues (cH H) U.ax97 (trS U.ax97).pat := by
  rw [(by decide +kernel : (trS U.ax97).pat = (trAxiom [] [] U.ax97).pat)]
  exact LibEv.listUnitR_ev (coreOKH H) (shapesOKH H) U.ax97 (by decide +kernel) (by decide +kernel)

theorem law98 (H : HookParams) : EntailsAtValues (cH H) U.ax98 (trS U.ax98).pat := by
  rw [(by decide +kernel : (trS U.ax98).pat = (trAxiom [] [] U.ax98).pat)]
  exact LibEv.listUnitL_ev (coreOKH H) (shapesOKH H) U.ax98 (by decide +kernel) (by decide +kernel)

theorem law100 (H : HookParams) : EntailsAtValues (cH H) U.ax100 (trS U.ax100).pat := by
  rw [(by decide +kernel : (trS U.ax100).pat = (trAxiom [] [] U.ax100).pat)]
  exact LibEv.mapAssoc_ev (coreOKH H) (shapesOKH H) U.ax100 (by decide +kernel) (by decide +kernel)

theorem law101 (H : HookParams) : EntailsAtValues (cH H) U.ax101 (trS U.ax101).pat := by
  rw [(by decide +kernel : (trS U.ax101).pat = (trAxiom [] [] U.ax101).pat)]
  exact LibEv.mapUnitR_ev (coreOKH H) (shapesOKH H) U.ax101 (by decide +kernel) (by decide +kernel)

theorem law102 (H : HookParams) : EntailsAtValues (cH H) U.ax102 (trS U.ax102).pat := by
  rw [(by decide +kernel : (trS U.ax102).pat = (trAxiom [] [] U.ax102).pat)]
  exact LibEv.mapUnitL_ev (coreOKH H) (shapesOKH H) U.ax102 (by decide +kernel) (by decide +kernel)

theorem law103 (H : HookParams) : EntailsAtValues (cH H) U.ax103 (trS U.ax103).pat := by
  rw [(by decide +kernel : (trS U.ax103).pat = (trAxiom [] [] U.ax103).pat)]
  exact LibEv.setAssoc_ev (coreOKH H) (shapesOKH H) U.ax103 (by decide +kernel) (by decide +kernel)

theorem law105 (H : HookParams) : EntailsAtValues (cH H) U.ax105 (trS U.ax105).pat := by
  rw [(by decide +kernel : (trS U.ax105).pat = (trAxiom [] [] U.ax105).pat)]
  exact LibEv.setUnitR_ev (coreOKH H) (shapesOKH H) U.ax105 (by decide +kernel) (by decide +kernel)

theorem law106 (H : HookParams) : EntailsAtValues (cH H) U.ax106 (trS U.ax106).pat := by
  rw [(by decide +kernel : (trS U.ax106).pat = (trAxiom [] [] U.ax106).pat)]
  exact LibEv.setUnitL_ev (coreOKH H) (shapesOKH H) U.ax106 (by decide +kernel) (by decide +kernel)

/-- The nine collection laws of the text. -/
noncomputable def lawText : List AxiomDecl :=
  [U.ax96, U.ax97, U.ax98, U.ax100, U.ax101, U.ax102, U.ax103, U.ax105, U.ax106]

theorem law_indices : lawText.map (·.index) = [96, 97, 98, 100, 101, 102, 103, 105, 106] := by decide +kernel

/-- **Ev for the collection laws**, for every H. -/
theorem laws_entailed (H : HookParams) : ∀ ad ∈ lawText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨law96 H, List.forall_mem_cons.mpr ⟨law97 H, List.forall_mem_cons.mpr ⟨law98 H, List.forall_mem_cons.mpr ⟨law100 H, List.forall_mem_cons.mpr ⟨law101 H, List.forall_mem_cons.mpr ⟨law102 H, List.forall_mem_cons.mpr ⟨law103 H, List.forall_mem_cons.mpr ⟨law105 H, List.forall_mem_cons.mpr ⟨law106 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the predicate equations of the equality symbols (16) -/

/-- The indices of the sentences. -/
def predIdx : List Nat := [384, 385, 386, 387, 388, 389, 390, 391, 396, 397, 398, 399, 402, 403, 404, 405]

/-- The sentences, in text order. -/
noncomputable def predText : List AxiomDecl := U.all.filter fun ad => predIdx.contains ad.index

theorem pred_indices : predText.map (·.index) = [384, 385, 386, 387, 388, 389, 390, 391, 396, 397, 398, 399, 402, 403, 404, 405] := by decide +kernel

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

/-! ## Library: term and function equations (74) -/

theorem ev418 (H : HookParams) : EntailsAtValues (cH H) U.ax418 (trS U.ax418).pat := by
  rw [(by decide +kernel : (trS U.ax418).pat = (trAxiom [] [] U.ax418).pat)]
  exact LibEv.fnB2S_ev (coreOKH H) false U.ax418 (by decide +kernel) (by decide +kernel)

theorem ev419 (H : HookParams) : EntailsAtValues (cH H) U.ax419 (trS U.ax419).pat := by
  rw [(by decide +kernel : (trS U.ax419).pat = (trAxiom [] [] U.ax419).pat)]
  exact LibEv.fnB2S_ev (coreOKH H) true U.ax419 (by decide +kernel) (by decide +kernel)

theorem ev420 (H : HookParams) : EntailsAtValues (cH H) U.ax420 (trS U.ax420).pat := by
  rw [(by decide +kernel : (trS U.ax420).pat = (trAxiom [] [] U.ax420).pat)]
  exact LibEv.fnS2B_ev (coreOKH H) false U.ax420 (by decide +kernel) (by decide +kernel)

theorem ev421 (H : HookParams) : EntailsAtValues (cH H) U.ax421 (trS U.ax421).pat := by
  rw [(by decide +kernel : (trS U.ax421).pat = (trAxiom [] [] U.ax421).pat)]
  exact LibEv.fnS2B_ev (coreOKH H) true U.ax421 (by decide +kernel) (by decide +kernel)

theorem ev422 (H : HookParams) : EntailsAtValues (cH H) U.ax422 (trS U.ax422).pat := by
  rw [(by decide +kernel : (trS U.ax422).pat = (trAxiom [] [] U.ax422).pat)]
  exact LibEv.tmodSmall_ev (coreOKH H) (shapesOKH H) U.ax422 (by decide +kernel) (by decide +kernel)

theorem ev424 (H : HookParams) : EntailsAtValues (cH H) U.ax424 (trS U.ax424).pat := by
  rw [(by decide +kernel : (trS U.ax424).pat = (trAxiom [] [] U.ax424).pat)]
  exact LibEv.addComm_ev (coreOKH H) (shapesOKH H) U.ax424 (by decide +kernel) (by decide +kernel)

theorem ev425 (H : HookParams) : EntailsAtValues (cH H) U.ax425 (trS U.ax425).pat := by
  rw [(by decide +kernel : (trS U.ax425).pat = (trAxiom [] [] U.ax425).pat)]
  exact LibEv.addZero_ev (coreOKH H) (shapesOKH H) U.ax425 (by decide +kernel) (by decide +kernel)

theorem ev426 (H : HookParams) : EntailsAtValues (cH H) U.ax426 (trS U.ax426).pat := by
  rw [(by decide +kernel : (trS U.ax426).pat = (trAxiom [] [] U.ax426).pat)]
  exact LibEv.addLeftComm_ev (coreOKH H) (shapesOKH H) U.ax426 (by decide +kernel) (by decide +kernel)

theorem ev427 (H : HookParams) : EntailsAtValues (cH H) U.ax427 (trS U.ax427).pat := by
  rw [(by decide +kernel : (trS U.ax427).pat = (trAxiom [] [] U.ax427).pat)]
  exact LibEv.addAssocRev_ev (coreOKH H) (shapesOKH H) U.ax427 (by decide +kernel) (by decide +kernel)

theorem ev428 (H : HookParams) : EntailsAtValues (cH H) U.ax428 (trS U.ax428).pat := by
  rw [(by decide +kernel : (trS U.ax428).pat = (trAxiom [] [] U.ax428).pat)]
  exact LibEv.addSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax428 (by decide +kernel) (by decide +kernel)

theorem ev429 (H : HookParams) : EntailsAtValues (cH H) U.ax429 (trS U.ax429).pat := by
  rw [(by decide +kernel : (trS U.ax429).pat = (trAxiom [] [] U.ax429).pat)]
  exact LibEv.addAssoc_ev (coreOKH H) (shapesOKH H) U.ax429 (by decide +kernel) (by decide +kernel)

theorem ev430 (H : HookParams) : EntailsAtValues (cH H) U.ax430 (trS U.ax430).pat := by
  rw [(by decide +kernel : (trS U.ax430).pat = (trAxiom [] [] U.ax430).pat)]
  exact LibEv.subAddComm_ev (coreOKH H) (shapesOKH H) U.ax430 (by decide +kernel) (by decide +kernel)

theorem ev431 (H : HookParams) : EntailsAtValues (cH H) U.ax431 (trS U.ax431).pat := by
  rw [(by decide +kernel : (trS U.ax431).pat = (trAxiom [] [] U.ax431).pat)]
  exact LibEv.subAsAdd_ev (coreOKH H) (shapesOKH H) U.ax431 (by decide +kernel) (by decide +kernel)

theorem ev432 (H : HookParams) : EntailsAtValues (cH H) U.ax432 (trS U.ax432).pat := by
  rw [(by decide +kernel : (trS U.ax432).pat = (trAxiom [] [] U.ax432).pat)]
  exact LibEv.subZero_ev (coreOKH H) (shapesOKH H) U.ax432 (by decide +kernel) (by decide +kernel)

theorem ev433 (H : HookParams) : EntailsAtValues (cH H) U.ax433 (trS U.ax433).pat := by
  rw [(by decide +kernel : (trS U.ax433).pat = (trAxiom [] [] U.ax433).pat)]
  exact LibEv.subAddSwap_ev (coreOKH H) (shapesOKH H) U.ax433 (by decide +kernel) (by decide +kernel)

theorem ev434 (H : HookParams) : EntailsAtValues (cH H) U.ax434 (trS U.ax434).pat := by
  rw [(by decide +kernel : (trS U.ax434).pat = (trAxiom [] [] U.ax434).pat)]
  exact LibEv.subAddAssoc_ev (coreOKH H) (shapesOKH H) U.ax434 (by decide +kernel) (by decide +kernel)

theorem ev435 (H : HookParams) : EntailsAtValues (cH H) U.ax435 (trS U.ax435).pat := by
  rw [(by decide +kernel : (trS U.ax435).pat = (trAxiom [] [] U.ax435).pat)]
  exact LibEv.subSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax435 (by decide +kernel) (by decide +kernel)

theorem ev436 (H : HookParams) : EntailsAtValues (cH H) U.ax436 (trS U.ax436).pat := by
  rw [(by decide +kernel : (trS U.ax436).pat = (trAxiom [] [] U.ax436).pat)]
  exact LibEv.subSubAdd_ev (coreOKH H) (shapesOKH H) U.ax436 (by decide +kernel) (by decide +kernel)

theorem ev437 (H : HookParams) : EntailsAtValues (cH H) U.ax437 (trS U.ax437).pat := by
  rw [(by decide +kernel : (trS U.ax437).pat = (trAxiom [] [] U.ax437).pat)]
  exact LibEv.shlZero_ev (coreOKH H) (shapesOKH H) U.ax437 (by decide +kernel) (by decide +kernel)

theorem ev438 (H : HookParams) : EntailsAtValues (cH H) U.ax438 (trS U.ax438).pat := by
  rw [(by decide +kernel : (trS U.ax438).pat = (trAxiom [] [] U.ax438).pat)]
  exact LibEv.zeroShl_ev (coreOKH H) (shapesOKH H) U.ax438 (by decide +kernel) (by decide +kernel)

theorem ev439 (H : HookParams) : EntailsAtValues (cH H) U.ax439 (trS U.ax439).pat := by
  rw [(by decide +kernel : (trS U.ax439).pat = (trAxiom [] [] U.ax439).pat)]
  exact LibEv.fnLeStr_ev (coreOKH H) (shapesOKH H) U.ax439 (by decide +kernel) (by decide +kernel)

theorem ev440 (H : HookParams) : EntailsAtValues (cH H) U.ax440 (trS U.ax440).pat := by
  rw [(by decide +kernel : (trS U.ax440).pat = (trAxiom [] [] U.ax440).pat)]
  exact LibEv.fnNeBool_ev (coreOKH H) (shapesOKH H) U.ax440 (by decide +kernel) (by decide +kernel)

theorem ev441 (H : HookParams) : EntailsAtValues (cH H) U.ax441 (trS U.ax441).pat := by
  rw [(by decide +kernel : (trS U.ax441).pat = (trAxiom [] [] U.ax441).pat)]
  exact LibEv.fnNeInt_ev (coreOKH H) (shapesOKH H) U.ax441 (by decide +kernel) (by decide +kernel)

theorem ev442 (H : HookParams) : EntailsAtValues (cH H) U.ax442 (trS U.ax442).pat := by
  rw [(by decide +kernel : (trS U.ax442).pat = (trAxiom [] [] U.ax442).pat)]
  exact LibEv.fnNeK_ev (coreOKH H) U.ax442 (by decide +kernel) (by decide +kernel)

theorem ev443 (H : HookParams) : EntailsAtValues (cH H) U.ax443 (trS U.ax443).pat := by
  rw [(by decide +kernel : (trS U.ax443).pat = (trAxiom [] [] U.ax443).pat)]
  exact LibEv.fnNeStr_ev (coreOKH H) (shapesOKH H) U.ax443 (by decide +kernel) (by decide +kernel)

theorem ev444 (H : HookParams) : EntailsAtValues (cH H) U.ax444 (trS U.ax444).pat := by
  rw [(by decide +kernel : (trS U.ax444).pat = (trAxiom [] [] U.ax444).pat)]
  exact LibEv.boolKEq_ev (coreOKH H) (shapesOKH H) (boolBelowH H) U.ax444 (by decide +kernel)
    (by decide +kernel)

theorem ev445 (H : HookParams) : EntailsAtValues (cH H) U.ax445 (trS U.ax445).pat := by
  rw [(by decide +kernel : (trS U.ax445).pat = (trAxiom [] [] U.ax445).pat)]
  exact LibEv.intKEq_ev (coreOKH H) (shapesOKH H) (intBelowH H) U.ax445 (by decide +kernel)
    (by decide +kernel)

theorem ev446 (H : HookParams) : EntailsAtValues (cH H) U.ax446 (trS U.ax446).pat := by
  rw [(by decide +kernel : (trS U.ax446).pat = (trAxiom [] [] U.ax446).pat)]
  exact LibEv.strKEq_ev (coreOKH H) (shapesOKH H) (stringBelowH H) U.ax446 (by decide +kernel) (by decide +kernel)

theorem ev447 (H : HookParams) : EntailsAtValues (cH H) U.ax447 (trS U.ax447).pat := by
  rw [(by decide +kernel : (trS U.ax447).pat = (trAxiom [] [] U.ax447).pat)]
  exact LibEv.fnGeStr_ev (coreOKH H) (shapesOKH H) U.ax447 (by decide +kernel) (by decide +kernel)

theorem ev448 (H : HookParams) : EntailsAtValues (cH H) U.ax448 (trS U.ax448).pat := by
  rw [(by decide +kernel : (trS U.ax448).pat = (trAxiom [] [] U.ax448).pat)]
  exact LibEv.shrZero_ev (coreOKH H) (shapesOKH H) U.ax448 (by decide +kernel) (by decide +kernel)

theorem ev449 (H : HookParams) : EntailsAtValues (cH H) U.ax449 (trS U.ax449).pat := by
  rw [(by decide +kernel : (trS U.ax449).pat = (trAxiom [] [] U.ax449).pat)]
  exact LibEv.zeroShr_ev (coreOKH H) (shapesOKH H) U.ax449 (by decide +kernel) (by decide +kernel)

theorem ev450 (H : HookParams) : EntailsAtValues (cH H) U.ax450 (trS U.ax450).pat := by
  rw [(by decide +kernel : (trS U.ax450).pat = (trAxiom [] [] U.ax450).pat)]
  exact LibEv.fnGtStr_ev (coreOKH H) (shapesOKH H) U.ax450 (by decide +kernel) (by decide +kernel)

theorem ev451 (H : HookParams) : EntailsAtValues (cH H) U.ax451 (trS U.ax451).pat := by
  rw [(by decide +kernel : (trS U.ax451).pat = (trAxiom [] [] U.ax451).pat)]
  exact LibEv.fnAndFalse_ev (coreOKH H) (shapesOKH H) U.ax451 (by decide +kernel) (by decide +kernel)

theorem ev452 (H : HookParams) : EntailsAtValues (cH H) U.ax452 (trS U.ax452).pat := by
  rw [(by decide +kernel : (trS U.ax452).pat = (trAxiom [] [] U.ax452).pat)]
  exact LibEv.bAndTrue_ev (coreOKH H) (shapesOKH H) U.ax452 (by decide +kernel) (by decide +kernel)

theorem ev453 (H : HookParams) : EntailsAtValues (cH H) U.ax453 (trS U.ax453).pat := by
  rw [(by decide +kernel : (trS U.ax453).pat = (trAxiom [] [] U.ax453).pat)]
  exact LibEv.bAndFalse_ev (coreOKH H) (shapesOKH H) U.ax453 (by decide +kernel) (by decide +kernel)

theorem ev454 (H : HookParams) : EntailsAtValues (cH H) U.ax454 (trS U.ax454).pat := by
  rw [(by decide +kernel : (trS U.ax454).pat = (trAxiom [] [] U.ax454).pat)]
  exact LibEv.fnAndTrue_ev (coreOKH H) (shapesOKH H) U.ax454 (by decide +kernel) (by decide +kernel)

theorem ev455 (H : HookParams) : EntailsAtValues (cH H) U.ax455 (trS U.ax455).pat := by
  rw [(by decide +kernel : (trS U.ax455).pat = (trAxiom [] [] U.ax455).pat)]
  exact LibEv.fnAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax455 (by decide +kernel) (by decide +kernel)

theorem ev456 (H : HookParams) : EntailsAtValues (cH H) U.ax456 (trS U.ax456).pat := by
  rw [(by decide +kernel : (trS U.ax456).pat = (trAxiom [] [] U.ax456).pat)]
  exact LibEv.bAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax456 (by decide +kernel) (by decide +kernel)

theorem ev457 (H : HookParams) : EntailsAtValues (cH H) U.ax457 (trS U.ax457).pat := by
  rw [(by decide +kernel : (trS U.ax457).pat = (trAxiom [] [] U.ax457).pat)]
  exact LibEv.bAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax457 (by decide +kernel) (by decide +kernel)

theorem ev458 (H : HookParams) : EntailsAtValues (cH H) U.ax458 (trS U.ax458).pat := by
  rw [(by decide +kernel : (trS U.ax458).pat = (trAxiom [] [] U.ax458).pat)]
  exact LibEv.fnAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax458 (by decide +kernel) (by decide +kernel)

theorem ev459 (H : HookParams) : EntailsAtValues (cH H) U.ax459 (trS U.ax459).pat := by
  rw [(by decide +kernel : (trS U.ax459).pat = (trAxiom [] [] U.ax459).pat)]
  exact LibEv.fnDivInt_ev (coreOKH H) (shapesOKH H) U.ax459 (by decide +kernel) (by decide +kernel)

theorem ev461 (H : HookParams) : EntailsAtValues (cH H) U.ax461 (trS U.ax461).pat := by
  rw [(by decide +kernel : (trS U.ax461).pat = (trAxiom [] [] U.ax461).pat)]
  exact LibEv.bImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax461 (by decide +kernel) (by decide +kernel)

theorem ev462 (H : HookParams) : EntailsAtValues (cH H) U.ax462 (trS U.ax462).pat := by
  rw [(by decide +kernel : (trS U.ax462).pat = (trAxiom [] [] U.ax462).pat)]
  exact LibEv.bImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax462 (by decide +kernel) (by decide +kernel)

theorem ev463 (H : HookParams) : EntailsAtValues (cH H) U.ax463 (trS U.ax463).pat := by
  rw [(by decide +kernel : (trS U.ax463).pat = (trAxiom [] [] U.ax463).pat)]
  exact LibEv.fnImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax463 (by decide +kernel) (by decide +kernel)

theorem ev464 (H : HookParams) : EntailsAtValues (cH H) U.ax464 (trS U.ax464).pat := by
  rw [(by decide +kernel : (trS U.ax464).pat = (trAxiom [] [] U.ax464).pat)]
  exact LibEv.fnImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax464 (by decide +kernel) (by decide +kernel)

theorem ev465 (H : HookParams) : EntailsAtValues (cH H) U.ax465 (trS U.ax465).pat := by
  rw [(by decide +kernel : (trS U.ax465).pat = (trAxiom [] [] U.ax465).pat)]
  exact LibEv.emodAsTmod_ev (coreOKH H) (shapesOKH H) U.ax465 (by decide +kernel) (by decide +kernel)

theorem ev466 (H : HookParams) : EntailsAtValues (cH H) U.ax466 (trS U.ax466).pat := by
  rw [(by decide +kernel : (trS U.ax466).pat = (trAxiom [] [] U.ax466).pat)]
  exact LibEv.emodSmall_ev (coreOKH H) (shapesOKH H) U.ax466 (by decide +kernel) (by decide +kernel)

theorem ev467 (H : HookParams) : EntailsAtValues (cH H) U.ax467 (trS U.ax467).pat := by
  rw [(by decide +kernel : (trS U.ax467).pat = (trAxiom [] [] U.ax467).pat)]
  exact LibEv.bOrFalse_ev (coreOKH H) (shapesOKH H) U.ax467 (by decide +kernel) (by decide +kernel)

theorem ev468 (H : HookParams) : EntailsAtValues (cH H) U.ax468 (trS U.ax468).pat := by
  rw [(by decide +kernel : (trS U.ax468).pat = (trAxiom [] [] U.ax468).pat)]
  exact LibEv.bOrTrue_ev (coreOKH H) (shapesOKH H) U.ax468 (by decide +kernel) (by decide +kernel)

theorem ev469 (H : HookParams) : EntailsAtValues (cH H) U.ax469 (trS U.ax469).pat := by
  rw [(by decide +kernel : (trS U.ax469).pat = (trAxiom [] [] U.ax469).pat)]
  exact LibEv.fnOrFalse_ev (coreOKH H) (shapesOKH H) U.ax469 (by decide +kernel) (by decide +kernel)

theorem ev470 (H : HookParams) : EntailsAtValues (cH H) U.ax470 (trS U.ax470).pat := by
  rw [(by decide +kernel : (trS U.ax470).pat = (trAxiom [] [] U.ax470).pat)]
  exact LibEv.fnOrTrue_ev (coreOKH H) (shapesOKH H) U.ax470 (by decide +kernel) (by decide +kernel)

theorem ev471 (H : HookParams) : EntailsAtValues (cH H) U.ax471 (trS U.ax471).pat := by
  rw [(by decide +kernel : (trS U.ax471).pat = (trAxiom [] [] U.ax471).pat)]
  exact LibEv.bOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax471 (by decide +kernel) (by decide +kernel)

theorem ev472 (H : HookParams) : EntailsAtValues (cH H) U.ax472 (trS U.ax472).pat := by
  rw [(by decide +kernel : (trS U.ax472).pat = (trAxiom [] [] U.ax472).pat)]
  exact LibEv.bOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax472 (by decide +kernel) (by decide +kernel)

theorem ev473 (H : HookParams) : EntailsAtValues (cH H) U.ax473 (trS U.ax473).pat := by
  rw [(by decide +kernel : (trS U.ax473).pat = (trAxiom [] [] U.ax473).pat)]
  exact LibEv.fnOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax473 (by decide +kernel) (by decide +kernel)

theorem ev474 (H : HookParams) : EntailsAtValues (cH H) U.ax474 (trS U.ax474).pat := by
  rw [(by decide +kernel : (trS U.ax474).pat = (trAxiom [] [] U.ax474).pat)]
  exact LibEv.fnOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax474 (by decide +kernel) (by decide +kernel)

theorem ev475 (H : HookParams) : EntailsAtValues (cH H) U.ax475 (trS U.ax475).pat := by
  rw [(by decide +kernel : (trS U.ax475).pat = (trAxiom [] [] U.ax475).pat)]
  exact LibEv.fnXorSame_ev (coreOKH H) (shapesOKH H) U.ax475 (by decide +kernel) (by decide +kernel)

theorem ev476 (H : HookParams) : EntailsAtValues (cH H) U.ax476 (trS U.ax476).pat := by
  rw [(by decide +kernel : (trS U.ax476).pat = (trAxiom [] [] U.ax476).pat)]
  exact LibEv.bXorFalse_ev (coreOKH H) (shapesOKH H) U.ax476 (by decide +kernel) (by decide +kernel)

theorem ev477 (H : HookParams) : EntailsAtValues (cH H) U.ax477 (trS U.ax477).pat := by
  rw [(by decide +kernel : (trS U.ax477).pat = (trAxiom [] [] U.ax477).pat)]
  exact LibEv.fnXorFalse_ev (coreOKH H) (shapesOKH H) U.ax477 (by decide +kernel) (by decide +kernel)

theorem ev478 (H : HookParams) : EntailsAtValues (cH H) U.ax478 (trS U.ax478).pat := by
  rw [(by decide +kernel : (trS U.ax478).pat = (trAxiom [] [] U.ax478).pat)]
  exact LibEv.fnSetUnion_ev (coreOKH H) (shapesOKH H) U.ax478 (by decide +kernel) (by decide +kernel)

theorem ev496 (H : HookParams) : EntailsAtValues (cH H) U.ax496 (trS U.ax496).pat := by
  rw [(by decide +kernel : (trS U.ax496).pat = (trAxiom [] [] U.ax496).pat)]
  exact LibEv.fnBitRange_ev (coreOKH H) (shapesOKH H) U.ax496 (by decide +kernel) (by decide +kernel)

theorem ev522 (H : HookParams) : EntailsAtValues (cH H) U.ax522 (trS U.ax522).pat := by
  rw [(by decide +kernel : (trS U.ax522).pat = (trAxiom [] [] U.ax522).pat)]
  exact LibEv.fnCountNone_ev (coreOKH H) (shapesOKH H) U.ax522 (by decide +kernel) (by decide +kernel)

theorem ev550 (H : HookParams) : EntailsAtValues (cH H) U.ax550 (trS U.ax550).pat := by
  rw [(by decide +kernel : (trS U.ax550).pat = (trAxiom [] [] U.ax550).pat)]
  exact LibEv.fnCharNone_ev (coreOKH H) (shapesOKH H) false U.ax550 (by decide +kernel) (by decide +kernel)

theorem ev558 (H : HookParams) : EntailsAtValues (cH H) U.ax558 (trS U.ax558).pat := by
  rw [(by decide +kernel : (trS U.ax558).pat = (trAxiom [] [] U.ax558).pat)]
  exact LibEv.fnFreshInt_ev (coreOKH H) (shapesOKH H) U.ax558 (by decide +kernel) (by decide +kernel)

theorem ev733 (H : HookParams) : EntailsAtValues (cH H) U.ax733 (trS U.ax733).pat := by
  rw [(by decide +kernel : (trS U.ax733).pat = (trAxiom [] [] U.ax733).pat)]
  exact LibEv.fnMinLt_ev (coreOKH H) (shapesOKH H) U.ax733 (by decide +kernel) (by decide +kernel)

theorem ev734 (H : HookParams) : EntailsAtValues (cH H) U.ax734 (trS U.ax734).pat := by
  rw [(by decide +kernel : (trS U.ax734).pat = (trAxiom [] [] U.ax734).pat)]
  exact LibEv.fnMinGe_ev (coreOKH H) (shapesOKH H) U.ax734 (by decide +kernel) (by decide +kernel)

theorem ev748 (H : HookParams) : EntailsAtValues (cH H) U.ax748 (trS U.ax748).pat := by
  rw [(by decide +kernel : (trS U.ax748).pat = (trAxiom [] [] U.ax748).pat)]
  exact LibEv.fnNotFalse_ev (coreOKH H) U.ax748 (by decide +kernel) (by decide +kernel)

theorem ev749 (H : HookParams) : EntailsAtValues (cH H) U.ax749 (trS U.ax749).pat := by
  rw [(by decide +kernel : (trS U.ax749).pat = (trAxiom [] [] U.ax749).pat)]
  exact LibEv.fnNotTrue_ev (coreOKH H) U.ax749 (by decide +kernel) (by decide +kernel)

theorem ev788 (H : HookParams) : EntailsAtValues (cH H) U.ax788 (trS U.ax788).pat := by
  rw [(by decide +kernel : (trS U.ax788).pat = (trAxiom [] [] U.ax788).pat)]
  exact LibEv.fnPushList_ev (coreOKH H) (shapesOKH H) U.ax788 (by decide +kernel) (by decide +kernel)

theorem ev793 (H : HookParams) : EntailsAtValues (cH H) U.ax793 (trS U.ax793).pat := by
  rw [(by decide +kernel : (trS U.ax793).pat = (trAxiom [] [] U.ax793).pat)]
  exact LibEv.fnReplace_ev (coreOKH H) (shapesOKH H) U.ax793 (by decide +kernel) (by decide +kernel)

theorem ev794 (H : HookParams) : EntailsAtValues (cH H) U.ax794 (trS U.ax794).pat := by
  rw [(by decide +kernel : (trS U.ax794).pat = (trAxiom [] [] U.ax794).pat)]
  exact LibEv.fnReplaceOw_ev (coreOKH H) (shapesOKH H) U.ax794 (by decide +kernel) (by decide +kernel)

theorem ev796 (H : HookParams) : EntailsAtValues (cH H) U.ax796 (trS U.ax796).pat := by
  rw [(by decide +kernel : (trS U.ax796).pat = (trAxiom [] [] U.ax796).pat)]
  exact LibEv.fnRepFirst_ev (coreOKH H) (shapesOKH H) U.ax796 (by decide +kernel) (by decide +kernel)

theorem ev797 (H : HookParams) : EntailsAtValues (cH H) U.ax797 (trS U.ax797).pat := by
  rw [(by decide +kernel : (trS U.ax797).pat = (trAxiom [] [] U.ax797).pat)]
  exact LibEv.fnRepFirstNone_ev (coreOKH H) (shapesOKH H) U.ax797 (by decide +kernel) (by decide +kernel)

theorem ev803 (H : HookParams) : EntailsAtValues (cH H) U.ax803 (trS U.ax803).pat := by
  rw [(by decide +kernel : (trS U.ax803).pat = (trAxiom [] [] U.ax803).pat)]
  exact LibEv.fnCharNone_ev (coreOKH H) (shapesOKH H) true U.ax803 (by decide +kernel) (by decide +kernel)

theorem ev805 (H : HookParams) : EntailsAtValues (cH H) U.ax805 (trS U.ax805).pat := by
  rw [(by decide +kernel : (trS U.ax805).pat = (trAxiom [] [] U.ax805).pat)]
  exact LibEv.fnSignExt_ev (coreOKH H) (shapesOKH H) U.ax805 (by decide +kernel) (by decide +kernel)

/-- The 74 sentences of `evN`. -/
noncomputable def evText : List AxiomDecl :=
  [U.ax418, U.ax419, U.ax420, U.ax421, U.ax422, U.ax424, U.ax425, U.ax426, U.ax427, U.ax428,
   U.ax429, U.ax430, U.ax431, U.ax432, U.ax433, U.ax434, U.ax435, U.ax436, U.ax437, U.ax438,
   U.ax439, U.ax440, U.ax441, U.ax442, U.ax443, U.ax444, U.ax445, U.ax446, U.ax447, U.ax448,
   U.ax449, U.ax450, U.ax451, U.ax452, U.ax453, U.ax454, U.ax455, U.ax456, U.ax457, U.ax458,
   U.ax459, U.ax461, U.ax462, U.ax463, U.ax464, U.ax465, U.ax466, U.ax467, U.ax468, U.ax469,
   U.ax470, U.ax471, U.ax472, U.ax473, U.ax474, U.ax475, U.ax476, U.ax477, U.ax478, U.ax496,
   U.ax522, U.ax550, U.ax558, U.ax733, U.ax734, U.ax748, U.ax749, U.ax788, U.ax793, U.ax794,
   U.ax796, U.ax797, U.ax803, U.ax805]

theorem ev_entailed (H : HookParams) : ∀ ad ∈ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev418 H, List.forall_mem_cons.mpr ⟨ev419 H, List.forall_mem_cons.mpr ⟨ev420 H, List.forall_mem_cons.mpr ⟨ev421 H, List.forall_mem_cons.mpr ⟨ev422 H, List.forall_mem_cons.mpr ⟨ev424 H, List.forall_mem_cons.mpr ⟨ev425 H, List.forall_mem_cons.mpr ⟨ev426 H, List.forall_mem_cons.mpr ⟨ev427 H, List.forall_mem_cons.mpr ⟨ev428 H, List.forall_mem_cons.mpr ⟨ev429 H, List.forall_mem_cons.mpr ⟨ev430 H, List.forall_mem_cons.mpr ⟨ev431 H, List.forall_mem_cons.mpr ⟨ev432 H, List.forall_mem_cons.mpr ⟨ev433 H, List.forall_mem_cons.mpr ⟨ev434 H, List.forall_mem_cons.mpr ⟨ev435 H, List.forall_mem_cons.mpr ⟨ev436 H, List.forall_mem_cons.mpr ⟨ev437 H, List.forall_mem_cons.mpr ⟨ev438 H, List.forall_mem_cons.mpr ⟨ev439 H, List.forall_mem_cons.mpr ⟨ev440 H, List.forall_mem_cons.mpr ⟨ev441 H, List.forall_mem_cons.mpr ⟨ev442 H, List.forall_mem_cons.mpr ⟨ev443 H, List.forall_mem_cons.mpr ⟨ev444 H, List.forall_mem_cons.mpr ⟨ev445 H, List.forall_mem_cons.mpr ⟨ev446 H, List.forall_mem_cons.mpr ⟨ev447 H, List.forall_mem_cons.mpr ⟨ev448 H, List.forall_mem_cons.mpr ⟨ev449 H, List.forall_mem_cons.mpr ⟨ev450 H, List.forall_mem_cons.mpr ⟨ev451 H, List.forall_mem_cons.mpr ⟨ev452 H, List.forall_mem_cons.mpr ⟨ev453 H, List.forall_mem_cons.mpr ⟨ev454 H, List.forall_mem_cons.mpr ⟨ev455 H, List.forall_mem_cons.mpr ⟨ev456 H, List.forall_mem_cons.mpr ⟨ev457 H, List.forall_mem_cons.mpr ⟨ev458 H, List.forall_mem_cons.mpr ⟨ev459 H, List.forall_mem_cons.mpr ⟨ev461 H, List.forall_mem_cons.mpr ⟨ev462 H, List.forall_mem_cons.mpr ⟨ev463 H, List.forall_mem_cons.mpr ⟨ev464 H, List.forall_mem_cons.mpr ⟨ev465 H, List.forall_mem_cons.mpr ⟨ev466 H, List.forall_mem_cons.mpr ⟨ev467 H, List.forall_mem_cons.mpr ⟨ev468 H, List.forall_mem_cons.mpr ⟨ev469 H, List.forall_mem_cons.mpr ⟨ev470 H, List.forall_mem_cons.mpr ⟨ev471 H, List.forall_mem_cons.mpr ⟨ev472 H, List.forall_mem_cons.mpr ⟨ev473 H, List.forall_mem_cons.mpr ⟨ev474 H, List.forall_mem_cons.mpr ⟨ev475 H, List.forall_mem_cons.mpr ⟨ev476 H, List.forall_mem_cons.mpr ⟨ev477 H, List.forall_mem_cons.mpr ⟨ev478 H, List.forall_mem_cons.mpr ⟨ev496 H, List.forall_mem_cons.mpr ⟨ev522 H, List.forall_mem_cons.mpr ⟨ev550 H, List.forall_mem_cons.mpr ⟨ev558 H, List.forall_mem_cons.mpr ⟨ev733 H, List.forall_mem_cons.mpr ⟨ev734 H, List.forall_mem_cons.mpr ⟨ev748 H, List.forall_mem_cons.mpr ⟨ev749 H, List.forall_mem_cons.mpr ⟨ev788 H, List.forall_mem_cons.mpr ⟨ev793 H, List.forall_mem_cons.mpr ⟨ev794 H, List.forall_mem_cons.mpr ⟨ev796 H, List.forall_mem_cons.mpr ⟨ev797 H, List.forall_mem_cons.mpr ⟨ev803 H, List.forall_mem_cons.mpr ⟨ev805 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## Library: the Bool predicate sentences over set variables (8), at set values -/

theorem ev392 (H : HookParams) : EntailsAtSetValues (cH H) U.ax392 (trS U.ax392).pat := by
  rw [(by decide +kernel : (trS U.ax392).pat = (trAxiom [] [] U.ax392).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) false U.ax392 (by decide +kernel) (by decide +kernel)

theorem ev393 (H : HookParams) : EntailsAtSetValues (cH H) U.ax393 (trS U.ax393).pat := by
  rw [(by decide +kernel : (trS U.ax393).pat = (trAxiom [] [] U.ax393).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) false U.ax393 (by decide +kernel) (by decide +kernel)

theorem ev394 (H : HookParams) : EntailsAtSetValues (cH H) U.ax394 (trS U.ax394).pat := by
  rw [(by decide +kernel : (trS U.ax394).pat = (trAxiom [] [] U.ax394).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false false U.ax394 (by decide +kernel) (by decide +kernel)

theorem ev395 (H : HookParams) : EntailsAtSetValues (cH H) U.ax395 (trS U.ax395).pat := by
  rw [(by decide +kernel : (trS U.ax395).pat = (trAxiom [] [] U.ax395).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true false U.ax395 (by decide +kernel) (by decide +kernel)

theorem ev400 (H : HookParams) : EntailsAtSetValues (cH H) U.ax400 (trS U.ax400).pat := by
  rw [(by decide +kernel : (trS U.ax400).pat = (trAxiom [] [] U.ax400).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) true U.ax400 (by decide +kernel) (by decide +kernel)

theorem ev401 (H : HookParams) : EntailsAtSetValues (cH H) U.ax401 (trS U.ax401).pat := by
  rw [(by decide +kernel : (trS U.ax401).pat = (trAxiom [] [] U.ax401).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false true U.ax401 (by decide +kernel) (by decide +kernel)

theorem ev406 (H : HookParams) : EntailsAtSetValues (cH H) U.ax406 (trS U.ax406).pat := by
  rw [(by decide +kernel : (trS U.ax406).pat = (trAxiom [] [] U.ax406).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) true U.ax406 (by decide +kernel) (by decide +kernel)

theorem ev407 (H : HookParams) : EntailsAtSetValues (cH H) U.ax407 (trS U.ax407).pat := by
  rw [(by decide +kernel : (trS U.ax407).pat = (trAxiom [] [] U.ax407).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true true U.ax407 (by decide +kernel) (by decide +kernel)

/-- The eight sentences over set variables. -/
noncomputable def setText : List AxiomDecl :=
  [U.ax392, U.ax393, U.ax394, U.ax395, U.ax400, U.ax401, U.ax406, U.ax407]

/-! ## Library: `replaceAll` (1917) and `rfindChar` (1893), under `libAdmitted` -/

theorem ev795 (H : HookParams) (hA : (cH H).libAdmitted) : EntailsAtValues (cH H) U.ax795 (trS U.ax795).pat := by
  rw [(by decide +kernel : (trS U.ax795).pat = (trAxiom [] [] U.ax795).pat)]
  exact LibEv.fnReplaceAll_ev (coreOKH H) (shapesOKH H) hA.2.2.2.2.2.1 U.ax795 (by decide +kernel) (by decide +kernel)

theorem ev802 (H : HookParams) (hA : (cH H).libAdmitted) : EntailsAtValues (cH H) U.ax802 (trS U.ax802).pat := by
  rw [(by decide +kernel : (trS U.ax802).pat = (trAxiom [] [] U.ax802).pat)]
  exact LibEv.fnRfindChar_ev (coreOKH H) (shapesOKH H) hA.2.2.1 U.ax802 (by decide +kernel) (by decide +kernel)

theorem ev795_lib : EntailsAtValues (cH HookParams.lib) U.ax795 (trS U.ax795).pat :=
  ev795 HookParams.lib (libAdmitted_lib_of_coreOK RefKk.coreOK_defn)

theorem ev802_lib : EntailsAtValues (cH HookParams.lib) U.ax802 (trS U.ax802).pat :=
  ev802 HookParams.lib (libAdmitted_lib_of_coreOK RefKk.coreOK_defn)

/-- The two sentences under `libAdmitted`. -/
noncomputable def admText : List AxiomDecl := [U.ax795, U.ax802]

/-! ## The class -/

/-- **Ev for the library sentences over element variables**: the 16 predicate equations and the 74
term and function equations, for every H. -/
theorem lib_entailed (H : HookParams) : ∀ ad ∈ predText ++ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  fun ad had => (List.mem_append.mp had).elim (pred_entailed H ad) (ev_entailed H ad)

/-- **The library sentences over set variables are entailed at set values**, for every H. -/
theorem libSet_entailed (H : HookParams) : ∀ ad ∈ setText, EntailsAtSetValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev392 H, List.forall_mem_cons.mpr ⟨ev393 H, List.forall_mem_cons.mpr ⟨ev394 H, List.forall_mem_cons.mpr ⟨ev395 H, List.forall_mem_cons.mpr ⟨ev400 H, List.forall_mem_cons.mpr ⟨ev401 H, List.forall_mem_cons.mpr ⟨ev406 H, List.forall_mem_cons.mpr ⟨ev407 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩

/-- **`replaceAll`'s and `rfindChar`'s equations**, for every H meeting `libAdmitted`. -/
theorem libA_entailed (H : HookParams) (hA : (cH H).libAdmitted) :
    ∀ ad ∈ admText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev795 H hA, List.forall_mem_cons.mpr ⟨ev802 H hA, fun _ h => nomatch h⟩⟩

/-- The 100 library sentences tied here; with 521 (test/TieKkRefuted.lean) the class's list
(test/TieKk.lean `classes`) in another order. -/
theorem lib_indices : (predText ++ evText ++ setText ++ admText).map (·.index) =
    [384, 385, 386, 387, 388, 389, 390, 391, 396, 397, 398, 399, 402, 403, 404, 405, 418, 419, 420, 421,
     422, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442,
     443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 461, 462, 463,
     464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 496, 522, 550, 558, 733,
     734, 748, 749, 788, 793, 794, 796, 797, 803, 805, 392, 393, 394, 395, 400, 401, 406, 407, 795, 802] := by
  decide +kernel

end KCore.TieKkAtValues

/-- info: 'KCore.TieKkAtValues.fnFun_at_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.fnFun_at_values
/-- info: 'KCore.TieKkAtValues.fun_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.fun_entailed
/-- info: 'KCore.TieKkAtValues.funS_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.funS_entailed
/-- info: 'KCore.TieKkAtValues.funS_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.funS_lib
/-- info: 'KCore.TieKkAtValues.laws_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.laws_entailed
/-- info: 'KCore.TieKkAtValues.lib_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.lib_entailed
/-- info: 'KCore.TieKkAtValues.libSet_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.libSet_entailed
/-- info: 'KCore.TieKkAtValues.libA_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.libA_entailed
/-- info: 'KCore.TieKkAtValues.ev795_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.ev795_lib
/-- info: 'KCore.TieKkAtValues.ev802_lib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieKkAtValues.ev802_lib
