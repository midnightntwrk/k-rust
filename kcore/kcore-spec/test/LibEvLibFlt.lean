/-
  The library sentences of `f2-examples/silentflt.kompile.kore` (FLOAT, STRING, BYTES and SET
  imported) that BOOL, INT, K-EQUAL, SET and LIST state, entailed at values for every
  interpretation H, each from the library's one statement of it (KcoreSpec/LibEv*.lean): the text's
  axiom is compared with the statement's pattern over the registry's names, and its translation with
  the text's declarations with the translation the statement is about. Each is the sentence of
  `f2-examples/ens.kompile.kore` at the same place of domains.md, tied there by the same statement
  (test/LibEv*Ens.lean). Run from the package root: `lake env lean -j1 test/LibEvLibFlt.lean`.

  - `pred_entailed`: the 16 predicate equations of `==Int`, `=/=Int` (domains.md 1405 to 1412) and
    `==K`, `=/=K` (2339 to 2346), 201, 202, 203, 204, 205, 206, 207, 208, 213, 214, 215, 216, 219, 220, 221, 222
    (`LibEv.intEqPred_ev`, `LibEv.kEqPred_ev`; one kernel decision over the list).
  - `ev_entailed`: 58 term and function equations, each by its own theorem `evN`.
  - `set_entailed`: the eight Bool predicate sentences over set variables (209, 210, 211, 212, 217, 218, 223, 224;
    domains.md 1176 to 1184), entailed at set values (`EntailsAtSetValues`).
  - `lib_indices`: the 82 sentences tied here.

  With test/LibEvStrFlt.lean, test/LibEvFloatFlt.lean and test/LibEvFnOwiseFlt.lean these are the
  library class of the text (test/LibEvClassesFlt.lean `lib_partition`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvLibFlt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)
theorem boolBelowH (H : HookParams) : Srt.bool ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.bool = true)
theorem intBelowH (H : HookParams) : Srt.int ∈ (cH H).sortsBelowKItem :=
  List.contains_iff_mem.mp (by decide +kernel : c.sortsBelowKItem.contains Srt.int = true)

/-! ## The predicate equations of the equality symbols (16) -/

/-- The indices of the sentences. -/
def predIdx : List Nat := [201, 202, 203, 204, 205, 206, 207, 208, 213, 214, 215, 216, 219, 220, 221, 222]

/-- The sentences, in text order. -/
noncomputable def predText : List AxiomDecl := U.all.filter fun ad => predIdx.contains ad.index

theorem pred_indices : predText.map (·.index) = [201, 202, 203, 204, 205, 206, 207, 208, 213, 214, 215, 216, 219, 220, 221, 222] := by decide +kernel

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

/-! ## Term and function equations (58) -/

/-- domains.md 1377 (ens 156). -/
theorem ev235 (H : HookParams) : EntailsAtValues (cH H) U.ax235 (trS U.ax235).pat := by
  rw [(by decide +kernel : (trS U.ax235).pat = (trAxiom [] [] U.ax235).pat)]
  exact LibEv.tmodSmall_ev (coreOKH H) (shapesOKH H) U.ax235 (by decide +kernel) (by decide +kernel)

/-- domains.md 1415 (ens 158). -/
theorem ev237 (H : HookParams) : EntailsAtValues (cH H) U.ax237 (trS U.ax237).pat := by
  rw [(by decide +kernel : (trS U.ax237).pat = (trAxiom [] [] U.ax237).pat)]
  exact LibEv.addComm_ev (coreOKH H) (shapesOKH H) U.ax237 (by decide +kernel) (by decide +kernel)

/-- domains.md 1373 (ens 159). -/
theorem ev238 (H : HookParams) : EntailsAtValues (cH H) U.ax238 (trS U.ax238).pat := by
  rw [(by decide +kernel : (trS U.ax238).pat = (trAxiom [] [] U.ax238).pat)]
  exact LibEv.addZero_ev (coreOKH H) (shapesOKH H) U.ax238 (by decide +kernel) (by decide +kernel)

/-- domains.md 1419 (ens 160). -/
theorem ev239 (H : HookParams) : EntailsAtValues (cH H) U.ax239 (trS U.ax239).pat := by
  rw [(by decide +kernel : (trS U.ax239).pat = (trAxiom [] [] U.ax239).pat)]
  exact LibEv.addLeftComm_ev (coreOKH H) (shapesOKH H) U.ax239 (by decide +kernel) (by decide +kernel)

/-- domains.md 1421 (ens 161). -/
theorem ev240 (H : HookParams) : EntailsAtValues (cH H) U.ax240 (trS U.ax240).pat := by
  rw [(by decide +kernel : (trS U.ax240).pat = (trAxiom [] [] U.ax240).pat)]
  exact LibEv.addAssocRev_ev (coreOKH H) (shapesOKH H) U.ax240 (by decide +kernel) (by decide +kernel)

/-- domains.md 1422 (ens 162). -/
theorem ev241 (H : HookParams) : EntailsAtValues (cH H) U.ax241 (trS U.ax241).pat := by
  rw [(by decide +kernel : (trS U.ax241).pat = (trAxiom [] [] U.ax241).pat)]
  exact LibEv.addSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax241 (by decide +kernel) (by decide +kernel)

/-- domains.md 1418 (ens 163). -/
theorem ev242 (H : HookParams) : EntailsAtValues (cH H) U.ax242 (trS U.ax242).pat := by
  rw [(by decide +kernel : (trS U.ax242).pat = (trAxiom [] [] U.ax242).pat)]
  exact LibEv.addAssoc_ev (coreOKH H) (shapesOKH H) U.ax242 (by decide +kernel) (by decide +kernel)

/-- domains.md 1423 (ens 164). -/
theorem ev243 (H : HookParams) : EntailsAtValues (cH H) U.ax243 (trS U.ax243).pat := by
  rw [(by decide +kernel : (trS U.ax243).pat = (trAxiom [] [] U.ax243).pat)]
  exact LibEv.subAddComm_ev (coreOKH H) (shapesOKH H) U.ax243 (by decide +kernel) (by decide +kernel)

/-- domains.md 1416 (ens 165). -/
theorem ev244 (H : HookParams) : EntailsAtValues (cH H) U.ax244 (trS U.ax244).pat := by
  rw [(by decide +kernel : (trS U.ax244).pat = (trAxiom [] [] U.ax244).pat)]
  exact LibEv.subAsAdd_ev (coreOKH H) (shapesOKH H) U.ax244 (by decide +kernel) (by decide +kernel)

/-- domains.md 1374 (ens 166). -/
theorem ev245 (H : HookParams) : EntailsAtValues (cH H) U.ax245 (trS U.ax245).pat := by
  rw [(by decide +kernel : (trS U.ax245).pat = (trAxiom [] [] U.ax245).pat)]
  exact LibEv.subZero_ev (coreOKH H) (shapesOKH H) U.ax245 (by decide +kernel) (by decide +kernel)

/-- domains.md 1420 (ens 167). -/
theorem ev246 (H : HookParams) : EntailsAtValues (cH H) U.ax246 (trS U.ax246).pat := by
  rw [(by decide +kernel : (trS U.ax246).pat = (trAxiom [] [] U.ax246).pat)]
  exact LibEv.subAddSwap_ev (coreOKH H) (shapesOKH H) U.ax246 (by decide +kernel) (by decide +kernel)

/-- domains.md 1424 (ens 168). -/
theorem ev247 (H : HookParams) : EntailsAtValues (cH H) U.ax247 (trS U.ax247).pat := by
  rw [(by decide +kernel : (trS U.ax247).pat = (trAxiom [] [] U.ax247).pat)]
  exact LibEv.subAddAssoc_ev (coreOKH H) (shapesOKH H) U.ax247 (by decide +kernel) (by decide +kernel)

/-- domains.md 1425 (ens 169). -/
theorem ev248 (H : HookParams) : EntailsAtValues (cH H) U.ax248 (trS U.ax248).pat := by
  rw [(by decide +kernel : (trS U.ax248).pat = (trAxiom [] [] U.ax248).pat)]
  exact LibEv.subSubAssoc_ev (coreOKH H) (shapesOKH H) U.ax248 (by decide +kernel) (by decide +kernel)

/-- domains.md 1426 (ens 170). -/
theorem ev249 (H : HookParams) : EntailsAtValues (cH H) U.ax249 (trS U.ax249).pat := by
  rw [(by decide +kernel : (trS U.ax249).pat = (trAxiom [] [] U.ax249).pat)]
  exact LibEv.subSubAdd_ev (coreOKH H) (shapesOKH H) U.ax249 (by decide +kernel) (by decide +kernel)

/-- domains.md 1380 (ens 171). -/
theorem ev250 (H : HookParams) : EntailsAtValues (cH H) U.ax250 (trS U.ax250).pat := by
  rw [(by decide +kernel : (trS U.ax250).pat = (trAxiom [] [] U.ax250).pat)]
  exact LibEv.shlZero_ev (coreOKH H) (shapesOKH H) U.ax250 (by decide +kernel) (by decide +kernel)

/-- domains.md 1381 (ens 172). -/
theorem ev251 (H : HookParams) : EntailsAtValues (cH H) U.ax251 (trS U.ax251).pat := by
  rw [(by decide +kernel : (trS U.ax251).pat = (trAxiom [] [] U.ax251).pat)]
  exact LibEv.zeroShl_ev (coreOKH H) (shapesOKH H) U.ax251 (by decide +kernel) (by decide +kernel)

/-- domains.md 1170 (ens 173). -/
theorem ev253 (H : HookParams) : EntailsAtValues (cH H) U.ax253 (trS U.ax253).pat := by
  rw [(by decide +kernel : (trS U.ax253).pat = (trAxiom [] [] U.ax253).pat)]
  exact LibEv.fnNeBool_ev (coreOKH H) (shapesOKH H) U.ax253 (by decide +kernel) (by decide +kernel)

/-- domains.md 1453 (ens 174). -/
theorem ev255 (H : HookParams) : EntailsAtValues (cH H) U.ax255 (trS U.ax255).pat := by
  rw [(by decide +kernel : (trS U.ax255).pat = (trAxiom [] [] U.ax255).pat)]
  exact LibEv.fnNeInt_ev (coreOKH H) (shapesOKH H) U.ax255 (by decide +kernel) (by decide +kernel)

/-- domains.md 2355 (ens 175). -/
theorem ev256 (H : HookParams) : EntailsAtValues (cH H) U.ax256 (trS U.ax256).pat := by
  rw [(by decide +kernel : (trS U.ax256).pat = (trAxiom [] [] U.ax256).pat)]
  exact LibEv.fnNeK_ev (coreOKH H) U.ax256 (by decide +kernel) (by decide +kernel)

/-- domains.md 2338 (ens 176). -/
theorem ev258 (H : HookParams) : EntailsAtValues (cH H) U.ax258 (trS U.ax258).pat := by
  rw [(by decide +kernel : (trS U.ax258).pat = (trAxiom [] [] U.ax258).pat)]
  exact LibEv.boolKEq_ev (coreOKH H) (shapesOKH H) (boolBelowH H) U.ax258 (by decide +kernel)
    (by decide +kernel)

/-- domains.md 1404 (ens 177). -/
theorem ev259 (H : HookParams) : EntailsAtValues (cH H) U.ax259 (trS U.ax259).pat := by
  rw [(by decide +kernel : (trS U.ax259).pat = (trAxiom [] [] U.ax259).pat)]
  exact LibEv.intKEq_ev (coreOKH H) (shapesOKH H) (intBelowH H) U.ax259 (by decide +kernel)
    (by decide +kernel)

/-- domains.md 1382 (ens 178). -/
theorem ev262 (H : HookParams) : EntailsAtValues (cH H) U.ax262 (trS U.ax262).pat := by
  rw [(by decide +kernel : (trS U.ax262).pat = (trAxiom [] [] U.ax262).pat)]
  exact LibEv.shrZero_ev (coreOKH H) (shapesOKH H) U.ax262 (by decide +kernel) (by decide +kernel)

/-- domains.md 1383 (ens 179). -/
theorem ev263 (H : HookParams) : EntailsAtValues (cH H) U.ax263 (trS U.ax263).pat := by
  rw [(by decide +kernel : (trS U.ax263).pat = (trAxiom [] [] U.ax263).pat)]
  exact LibEv.zeroShr_ev (coreOKH H) (shapesOKH H) U.ax263 (by decide +kernel) (by decide +kernel)

/-- domains.md 1143 (ens 180). -/
theorem ev265 (H : HookParams) : EntailsAtValues (cH H) U.ax265 (trS U.ax265).pat := by
  rw [(by decide +kernel : (trS U.ax265).pat = (trAxiom [] [] U.ax265).pat)]
  exact LibEv.fnAndFalse_ev (coreOKH H) (shapesOKH H) U.ax265 (by decide +kernel) (by decide +kernel)

/-- domains.md 1142 (ens 181). -/
theorem ev266 (H : HookParams) : EntailsAtValues (cH H) U.ax266 (trS U.ax266).pat := by
  rw [(by decide +kernel : (trS U.ax266).pat = (trAxiom [] [] U.ax266).pat)]
  exact LibEv.bAndTrue_ev (coreOKH H) (shapesOKH H) U.ax266 (by decide +kernel) (by decide +kernel)

/-- domains.md 1144 (ens 182). -/
theorem ev267 (H : HookParams) : EntailsAtValues (cH H) U.ax267 (trS U.ax267).pat := by
  rw [(by decide +kernel : (trS U.ax267).pat = (trAxiom [] [] U.ax267).pat)]
  exact LibEv.bAndFalse_ev (coreOKH H) (shapesOKH H) U.ax267 (by decide +kernel) (by decide +kernel)

/-- domains.md 1141 (ens 183). -/
theorem ev268 (H : HookParams) : EntailsAtValues (cH H) U.ax268 (trS U.ax268).pat := by
  rw [(by decide +kernel : (trS U.ax268).pat = (trAxiom [] [] U.ax268).pat)]
  exact LibEv.fnAndTrue_ev (coreOKH H) (shapesOKH H) U.ax268 (by decide +kernel) (by decide +kernel)

/-- domains.md 1148 (ens 184). -/
theorem ev269 (H : HookParams) : EntailsAtValues (cH H) U.ax269 (trS U.ax269).pat := by
  rw [(by decide +kernel : (trS U.ax269).pat = (trAxiom [] [] U.ax269).pat)]
  exact LibEv.fnAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax269 (by decide +kernel) (by decide +kernel)

/-- domains.md 1147 (ens 185). -/
theorem ev270 (H : HookParams) : EntailsAtValues (cH H) U.ax270 (trS U.ax270).pat := by
  rw [(by decide +kernel : (trS U.ax270).pat = (trAxiom [] [] U.ax270).pat)]
  exact LibEv.bAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax270 (by decide +kernel) (by decide +kernel)

/-- domains.md 1149 (ens 186). -/
theorem ev271 (H : HookParams) : EntailsAtValues (cH H) U.ax271 (trS U.ax271).pat := by
  rw [(by decide +kernel : (trS U.ax271).pat = (trAxiom [] [] U.ax271).pat)]
  exact LibEv.bAndThenFalse_ev (coreOKH H) (shapesOKH H) U.ax271 (by decide +kernel) (by decide +kernel)

/-- domains.md 1146 (ens 187). -/
theorem ev272 (H : HookParams) : EntailsAtValues (cH H) U.ax272 (trS U.ax272).pat := by
  rw [(by decide +kernel : (trS U.ax272).pat = (trAxiom [] [] U.ax272).pat)]
  exact LibEv.fnAndThenTrue_ev (coreOKH H) (shapesOKH H) U.ax272 (by decide +kernel) (by decide +kernel)

/-- domains.md 1442 (ens 188). -/
theorem ev273 (H : HookParams) : EntailsAtValues (cH H) U.ax273 (trS U.ax273).pat := by
  rw [(by decide +kernel : (trS U.ax273).pat = (trAxiom [] [] U.ax273).pat)]
  exact LibEv.fnDivInt_ev (coreOKH H) (shapesOKH H) U.ax273 (by decide +kernel) (by decide +kernel)

/-- domains.md 1168 (ens 190). -/
theorem ev275 (H : HookParams) : EntailsAtValues (cH H) U.ax275 (trS U.ax275).pat := by
  rw [(by decide +kernel : (trS U.ax275).pat = (trAxiom [] [] U.ax275).pat)]
  exact LibEv.bImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax275 (by decide +kernel) (by decide +kernel)

/-- domains.md 1167 (ens 191). -/
theorem ev276 (H : HookParams) : EntailsAtValues (cH H) U.ax276 (trS U.ax276).pat := by
  rw [(by decide +kernel : (trS U.ax276).pat = (trAxiom [] [] U.ax276).pat)]
  exact LibEv.bImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax276 (by decide +kernel) (by decide +kernel)

/-- domains.md 1166 (ens 192). -/
theorem ev277 (H : HookParams) : EntailsAtValues (cH H) U.ax277 (trS U.ax277).pat := by
  rw [(by decide +kernel : (trS U.ax277).pat = (trAxiom [] [] U.ax277).pat)]
  exact LibEv.fnImpliesFalse_ev (coreOKH H) (shapesOKH H) U.ax277 (by decide +kernel) (by decide +kernel)

/-- domains.md 1165 (ens 193). -/
theorem ev278 (H : HookParams) : EntailsAtValues (cH H) U.ax278 (trS U.ax278).pat := by
  rw [(by decide +kernel : (trS U.ax278).pat = (trAxiom [] [] U.ax278).pat)]
  exact LibEv.fnImpliesTrue_ev (coreOKH H) (shapesOKH H) U.ax278 (by decide +kernel) (by decide +kernel)

/-- domains.md 1445 (ens 194). -/
theorem ev279 (H : HookParams) : EntailsAtValues (cH H) U.ax279 (trS U.ax279).pat := by
  rw [(by decide +kernel : (trS U.ax279).pat = (trAxiom [] [] U.ax279).pat)]
  exact LibEv.emodAsTmod_ev (coreOKH H) (shapesOKH H) U.ax279 (by decide +kernel) (by decide +kernel)

/-- domains.md 1376 (ens 195). -/
theorem ev280 (H : HookParams) : EntailsAtValues (cH H) U.ax280 (trS U.ax280).pat := by
  rw [(by decide +kernel : (trS U.ax280).pat = (trAxiom [] [] U.ax280).pat)]
  exact LibEv.emodSmall_ev (coreOKH H) (shapesOKH H) U.ax280 (by decide +kernel) (by decide +kernel)

/-- domains.md 1158 (ens 196). -/
theorem ev281 (H : HookParams) : EntailsAtValues (cH H) U.ax281 (trS U.ax281).pat := by
  rw [(by decide +kernel : (trS U.ax281).pat = (trAxiom [] [] U.ax281).pat)]
  exact LibEv.bOrFalse_ev (coreOKH H) (shapesOKH H) U.ax281 (by decide +kernel) (by decide +kernel)

/-- domains.md 1156 (ens 197). -/
theorem ev282 (H : HookParams) : EntailsAtValues (cH H) U.ax282 (trS U.ax282).pat := by
  rw [(by decide +kernel : (trS U.ax282).pat = (trAxiom [] [] U.ax282).pat)]
  exact LibEv.bOrTrue_ev (coreOKH H) (shapesOKH H) U.ax282 (by decide +kernel) (by decide +kernel)

/-- domains.md 1157 (ens 198). -/
theorem ev283 (H : HookParams) : EntailsAtValues (cH H) U.ax283 (trS U.ax283).pat := by
  rw [(by decide +kernel : (trS U.ax283).pat = (trAxiom [] [] U.ax283).pat)]
  exact LibEv.fnOrFalse_ev (coreOKH H) (shapesOKH H) U.ax283 (by decide +kernel) (by decide +kernel)

/-- domains.md 1155 (ens 199). -/
theorem ev284 (H : HookParams) : EntailsAtValues (cH H) U.ax284 (trS U.ax284).pat := by
  rw [(by decide +kernel : (trS U.ax284).pat = (trAxiom [] [] U.ax284).pat)]
  exact LibEv.fnOrTrue_ev (coreOKH H) (shapesOKH H) U.ax284 (by decide +kernel) (by decide +kernel)

/-- domains.md 1163 (ens 200). -/
theorem ev285 (H : HookParams) : EntailsAtValues (cH H) U.ax285 (trS U.ax285).pat := by
  rw [(by decide +kernel : (trS U.ax285).pat = (trAxiom [] [] U.ax285).pat)]
  exact LibEv.bOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax285 (by decide +kernel) (by decide +kernel)

/-- domains.md 1161 (ens 201). -/
theorem ev286 (H : HookParams) : EntailsAtValues (cH H) U.ax286 (trS U.ax286).pat := by
  rw [(by decide +kernel : (trS U.ax286).pat = (trAxiom [] [] U.ax286).pat)]
  exact LibEv.bOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax286 (by decide +kernel) (by decide +kernel)

/-- domains.md 1162 (ens 202). -/
theorem ev287 (H : HookParams) : EntailsAtValues (cH H) U.ax287 (trS U.ax287).pat := by
  rw [(by decide +kernel : (trS U.ax287).pat = (trAxiom [] [] U.ax287).pat)]
  exact LibEv.fnOrElseFalse_ev (coreOKH H) (shapesOKH H) U.ax287 (by decide +kernel) (by decide +kernel)

/-- domains.md 1160 (ens 203). -/
theorem ev288 (H : HookParams) : EntailsAtValues (cH H) U.ax288 (trS U.ax288).pat := by
  rw [(by decide +kernel : (trS U.ax288).pat = (trAxiom [] [] U.ax288).pat)]
  exact LibEv.fnOrElseTrue_ev (coreOKH H) (shapesOKH H) U.ax288 (by decide +kernel) (by decide +kernel)

/-- domains.md 1153 (ens 204). -/
theorem ev289 (H : HookParams) : EntailsAtValues (cH H) U.ax289 (trS U.ax289).pat := by
  rw [(by decide +kernel : (trS U.ax289).pat = (trAxiom [] [] U.ax289).pat)]
  exact LibEv.fnXorSame_ev (coreOKH H) (shapesOKH H) U.ax289 (by decide +kernel) (by decide +kernel)

/-- domains.md 1152 (ens 205). -/
theorem ev290 (H : HookParams) : EntailsAtValues (cH H) U.ax290 (trS U.ax290).pat := by
  rw [(by decide +kernel : (trS U.ax290).pat = (trAxiom [] [] U.ax290).pat)]
  exact LibEv.bXorFalse_ev (coreOKH H) (shapesOKH H) U.ax290 (by decide +kernel) (by decide +kernel)

/-- domains.md 1151 (ens 206). -/
theorem ev291 (H : HookParams) : EntailsAtValues (cH H) U.ax291 (trS U.ax291).pat := by
  rw [(by decide +kernel : (trS U.ax291).pat = (trAxiom [] [] U.ax291).pat)]
  exact LibEv.fnXorFalse_ev (coreOKH H) (shapesOKH H) U.ax291 (by decide +kernel) (by decide +kernel)

/-- domains.md 749 (ens 207). -/
theorem ev292 (H : HookParams) : EntailsAtValues (cH H) U.ax292 (trS U.ax292).pat := by
  rw [(by decide +kernel : (trS U.ax292).pat = (trAxiom [] [] U.ax292).pat)]
  exact LibEv.fnSetUnion_ev (coreOKH H) (shapesOKH H) U.ax292 (by decide +kernel) (by decide +kernel)

/-- domains.md 1438 (ens 208). -/
theorem ev293 (H : HookParams) : EntailsAtValues (cH H) U.ax293 (trS U.ax293).pat := by
  rw [(by decide +kernel : (trS U.ax293).pat = (trAxiom [] [] U.ax293).pat)]
  exact LibEv.fnBitRange_ev (coreOKH H) (shapesOKH H) U.ax293 (by decide +kernel) (by decide +kernel)

/-- domains.md 1457 (ens 209). -/
theorem ev298 (H : HookParams) : EntailsAtValues (cH H) U.ax298 (trS U.ax298).pat := by
  rw [(by decide +kernel : (trS U.ax298).pat = (trAxiom [] [] U.ax298).pat)]
  exact LibEv.fnFreshInt_ev (coreOKH H) (shapesOKH H) U.ax298 (by decide +kernel) (by decide +kernel)

/-- domains.md 1450 (ens 246). -/
theorem ev347 (H : HookParams) : EntailsAtValues (cH H) U.ax347 (trS U.ax347).pat := by
  rw [(by decide +kernel : (trS U.ax347).pat = (trAxiom [] [] U.ax347).pat)]
  exact LibEv.fnMinLt_ev (coreOKH H) (shapesOKH H) U.ax347 (by decide +kernel) (by decide +kernel)

/-- domains.md 1451 (ens 247). -/
theorem ev348 (H : HookParams) : EntailsAtValues (cH H) U.ax348 (trS U.ax348).pat := by
  rw [(by decide +kernel : (trS U.ax348).pat = (trAxiom [] [] U.ax348).pat)]
  exact LibEv.fnMinGe_ev (coreOKH H) (shapesOKH H) U.ax348 (by decide +kernel) (by decide +kernel)

/-- domains.md 1139 (ens 248). -/
theorem ev349 (H : HookParams) : EntailsAtValues (cH H) U.ax349 (trS U.ax349).pat := by
  rw [(by decide +kernel : (trS U.ax349).pat = (trAxiom [] [] U.ax349).pat)]
  exact LibEv.fnNotFalse_ev (coreOKH H) U.ax349 (by decide +kernel) (by decide +kernel)

/-- domains.md 1138 (ens 249). -/
theorem ev350 (H : HookParams) : EntailsAtValues (cH H) U.ax350 (trS U.ax350).pat := by
  rw [(by decide +kernel : (trS U.ax350).pat = (trAxiom [] [] U.ax350).pat)]
  exact LibEv.fnNotTrue_ev (coreOKH H) U.ax350 (by decide +kernel) (by decide +kernel)

/-- domains.md 955 (ens 264). -/
theorem ev371 (H : HookParams) : EntailsAtValues (cH H) U.ax371 (trS U.ax371).pat := by
  rw [(by decide +kernel : (trS U.ax371).pat = (trAxiom [] [] U.ax371).pat)]
  exact LibEv.fnPushList_ev (coreOKH H) (shapesOKH H) U.ax371 (by decide +kernel) (by decide +kernel)

/-- domains.md 1440 (ens 265). -/
theorem ev379 (H : HookParams) : EntailsAtValues (cH H) U.ax379 (trS U.ax379).pat := by
  rw [(by decide +kernel : (trS U.ax379).pat = (trAxiom [] [] U.ax379).pat)]
  exact LibEv.fnSignExt_ev (coreOKH H) (shapesOKH H) U.ax379 (by decide +kernel) (by decide +kernel)

/-- The 58 sentences of `evN`. -/
noncomputable def evText : List AxiomDecl :=
  [U.ax235, U.ax237, U.ax238, U.ax239, U.ax240, U.ax241, U.ax242, U.ax243, U.ax244, U.ax245, U.ax246,
   U.ax247, U.ax248, U.ax249, U.ax250, U.ax251, U.ax253, U.ax255, U.ax256, U.ax258, U.ax259, U.ax262,
   U.ax263, U.ax265, U.ax266, U.ax267, U.ax268, U.ax269, U.ax270, U.ax271, U.ax272, U.ax273, U.ax275,
   U.ax276, U.ax277, U.ax278, U.ax279, U.ax280, U.ax281, U.ax282, U.ax283, U.ax284, U.ax285, U.ax286,
   U.ax287, U.ax288, U.ax289, U.ax290, U.ax291, U.ax292, U.ax293, U.ax298, U.ax347, U.ax348, U.ax349,
   U.ax350, U.ax371, U.ax379]

theorem ev_entailed (H : HookParams) : ∀ ad ∈ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev235 H, List.forall_mem_cons.mpr ⟨ev237 H, List.forall_mem_cons.mpr ⟨ev238 H, List.forall_mem_cons.mpr ⟨ev239 H, List.forall_mem_cons.mpr ⟨ev240 H, List.forall_mem_cons.mpr ⟨ev241 H, List.forall_mem_cons.mpr ⟨ev242 H, List.forall_mem_cons.mpr ⟨ev243 H, List.forall_mem_cons.mpr ⟨ev244 H, List.forall_mem_cons.mpr ⟨ev245 H, List.forall_mem_cons.mpr ⟨ev246 H, List.forall_mem_cons.mpr ⟨ev247 H, List.forall_mem_cons.mpr ⟨ev248 H, List.forall_mem_cons.mpr ⟨ev249 H, List.forall_mem_cons.mpr ⟨ev250 H, List.forall_mem_cons.mpr ⟨ev251 H, List.forall_mem_cons.mpr ⟨ev253 H, List.forall_mem_cons.mpr ⟨ev255 H, List.forall_mem_cons.mpr ⟨ev256 H, List.forall_mem_cons.mpr ⟨ev258 H, List.forall_mem_cons.mpr ⟨ev259 H, List.forall_mem_cons.mpr ⟨ev262 H, List.forall_mem_cons.mpr ⟨ev263 H, List.forall_mem_cons.mpr ⟨ev265 H, List.forall_mem_cons.mpr ⟨ev266 H, List.forall_mem_cons.mpr ⟨ev267 H, List.forall_mem_cons.mpr ⟨ev268 H, List.forall_mem_cons.mpr ⟨ev269 H, List.forall_mem_cons.mpr ⟨ev270 H, List.forall_mem_cons.mpr ⟨ev271 H, List.forall_mem_cons.mpr ⟨ev272 H, List.forall_mem_cons.mpr ⟨ev273 H, List.forall_mem_cons.mpr ⟨ev275 H, List.forall_mem_cons.mpr ⟨ev276 H, List.forall_mem_cons.mpr ⟨ev277 H, List.forall_mem_cons.mpr ⟨ev278 H, List.forall_mem_cons.mpr ⟨ev279 H, List.forall_mem_cons.mpr ⟨ev280 H, List.forall_mem_cons.mpr ⟨ev281 H, List.forall_mem_cons.mpr ⟨ev282 H, List.forall_mem_cons.mpr ⟨ev283 H, List.forall_mem_cons.mpr ⟨ev284 H, List.forall_mem_cons.mpr ⟨ev285 H, List.forall_mem_cons.mpr ⟨ev286 H, List.forall_mem_cons.mpr ⟨ev287 H, List.forall_mem_cons.mpr ⟨ev288 H, List.forall_mem_cons.mpr ⟨ev289 H, List.forall_mem_cons.mpr ⟨ev290 H, List.forall_mem_cons.mpr ⟨ev291 H, List.forall_mem_cons.mpr ⟨ev292 H, List.forall_mem_cons.mpr ⟨ev293 H, List.forall_mem_cons.mpr ⟨ev298 H, List.forall_mem_cons.mpr ⟨ev347 H, List.forall_mem_cons.mpr ⟨ev348 H, List.forall_mem_cons.mpr ⟨ev349 H, List.forall_mem_cons.mpr ⟨ev350 H, List.forall_mem_cons.mpr ⟨ev371 H, List.forall_mem_cons.mpr ⟨ev379 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## The Bool predicate sentences over set variables (8), at set values -/

/-- domains.md 1182 (ens 139). -/
theorem ev209 (H : HookParams) : EntailsAtSetValues (cH H) U.ax209 (trS U.ax209).pat := by
  rw [(by decide +kernel : (trS U.ax209).pat = (trAxiom [] [] U.ax209).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) false U.ax209 (by decide +kernel) (by decide +kernel)

/-- domains.md 1184 (ens 140). -/
theorem ev210 (H : HookParams) : EntailsAtSetValues (cH H) U.ax210 (trS U.ax210).pat := by
  rw [(by decide +kernel : (trS U.ax210).pat = (trAxiom [] [] U.ax210).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) false U.ax210 (by decide +kernel) (by decide +kernel)

/-- domains.md 1179 (ens 141). -/
theorem ev211 (H : HookParams) : EntailsAtSetValues (cH H) U.ax211 (trS U.ax211).pat := by
  rw [(by decide +kernel : (trS U.ax211).pat = (trAxiom [] [] U.ax211).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false false U.ax211 (by decide +kernel) (by decide +kernel)

/-- domains.md 1177 (ens 142). -/
theorem ev212 (H : HookParams) : EntailsAtSetValues (cH H) U.ax212 (trS U.ax212).pat := by
  rw [(by decide +kernel : (trS U.ax212).pat = (trAxiom [] [] U.ax212).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true false U.ax212 (by decide +kernel) (by decide +kernel)

/-- domains.md 1183 (ens 147). -/
theorem ev217 (H : HookParams) : EntailsAtSetValues (cH H) U.ax217 (trS U.ax217).pat := by
  rw [(by decide +kernel : (trS U.ax217).pat = (trAxiom [] [] U.ax217).pat)]
  exact LibEv.boolOrSet_ev (coreOKH H) (shapesOKH H) true U.ax217 (by decide +kernel) (by decide +kernel)

/-- domains.md 1178 (ens 148). -/
theorem ev218 (H : HookParams) : EntailsAtSetValues (cH H) U.ax218 (trS U.ax218).pat := by
  rw [(by decide +kernel : (trS U.ax218).pat = (trAxiom [] [] U.ax218).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) false true U.ax218 (by decide +kernel) (by decide +kernel)

/-- domains.md 1181 (ens 153). -/
theorem ev223 (H : HookParams) : EntailsAtSetValues (cH H) U.ax223 (trS U.ax223).pat := by
  rw [(by decide +kernel : (trS U.ax223).pat = (trAxiom [] [] U.ax223).pat)]
  exact LibEv.boolAndSet_ev (coreOKH H) (shapesOKH H) true U.ax223 (by decide +kernel) (by decide +kernel)

/-- domains.md 1176 (ens 154). -/
theorem ev224 (H : HookParams) : EntailsAtSetValues (cH H) U.ax224 (trS U.ax224).pat := by
  rw [(by decide +kernel : (trS U.ax224).pat = (trAxiom [] [] U.ax224).pat)]
  exact LibEv.boolNotSet_ev (coreOKH H) (shapesOKH H) true true U.ax224 (by decide +kernel) (by decide +kernel)

/-- The eight sentences over set variables. -/
noncomputable def setText : List AxiomDecl :=
  [U.ax209, U.ax210, U.ax211, U.ax212, U.ax217, U.ax218, U.ax223, U.ax224]

theorem set_entailed (H : HookParams) : ∀ ad ∈ setText, EntailsAtSetValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨ev209 H, List.forall_mem_cons.mpr ⟨ev210 H, List.forall_mem_cons.mpr ⟨ev211 H, List.forall_mem_cons.mpr ⟨ev212 H, List.forall_mem_cons.mpr ⟨ev217 H, List.forall_mem_cons.mpr ⟨ev218 H, List.forall_mem_cons.mpr ⟨ev223 H, List.forall_mem_cons.mpr ⟨ev224 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩

/-! ## The sentences tied here -/

/-- **Ev for the library sentences over element variables tied here**, for every H. -/
theorem lib_entailed (H : HookParams) : ∀ ad ∈ predText ++ evText, EntailsAtValues (cH H) ad (trS ad).pat :=
  fun ad had => (List.mem_append.mp had).elim (pred_entailed H ad) (ev_entailed H ad)

/-- The 82 library sentences tied here. -/
theorem lib_indices : (predText ++ evText ++ setText).map (·.index) =
    [201, 202, 203, 204, 205, 206, 207, 208, 213, 214, 215, 216, 219, 220, 221, 222, 235, 237, 238,
   239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 253, 255, 256, 258, 259, 262,
   263, 265, 266, 267, 268, 269, 270, 271, 272, 273, 275, 276, 277, 278, 279, 280, 281, 282, 283,
   284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 298, 347, 348, 349, 350, 371, 379, 209, 210,
   211, 212, 217, 218, 223, 224] := by
  decide +kernel

end KCore.LibEvLibFlt

/-- info: 'KCore.LibEvLibFlt.lib_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLibFlt.lib_entailed
/-- info: 'KCore.LibEvLibFlt.set_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvLibFlt.set_entailed
