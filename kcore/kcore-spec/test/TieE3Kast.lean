/-
  The tie (C14) on `f2-examples/e3-kast.kompile.kore`, the kompiled text of construct fixture e3-kast
  (`test/constructs/fixtures/e3-kast`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e3-kast`; run from the package root: `lake env lean -j1 test/TieE3Kast.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 338 sentences of the user module E3-KAST, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 17 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 214 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (35): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (6): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
  - Constructor sentences (47): entailed by Γ (`cons_entailed`).
  - No junk (6 of a sort without generators, `nojunk_trivial_entailed`; 7 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (81): Γ with it has no model (`idem_refuted`).
  - Library sample, 216 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (90);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3Kast

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-kast.kompile.kore"
definition_of defn from "f2-examples/e3-kast.kompile.kore"
user_axioms U from "f2-examples/e3-kast.kompile.kore" module "E3-KAST"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-KAST")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 338 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-! ## The account: every sentence of the user module is in exactly one class -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291,
      292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308]),
   ("rewrite rule", [196, 197, 198, 199, 200, 201]),
   ("priority equation", []),
   ("constructor functional", [22, 30, 32, 34, 36, 98, 102, 107, 112, 139, 140, 143]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]),
   ("injectivity", [31, 33, 35, 37, 103, 108, 113]),
   ("distinctness", [23, 24, 25, 26, 99, 100, 101, 104, 105, 109]),
   ("no junk", [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]),
   ("function functional", [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]),
   ("hooked functional", [27, 28, 29, 38, 41, 42, 43, 44, 45, 46, 47, 50, 51, 52, 53, 55, 57, 58, 59, 60, 61, 62, 63,
      64, 65, 66, 67, 68, 69, 70, 71, 72, 76, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 96, 97, 106,
      111, 115, 135, 136, 137, 138, 141, 142, 144, 145, 146, 147, 148, 149, 150]),
   ("collection law", [73, 74, 75, 77, 78, 79, 80, 82, 83]),
   ("library", [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189,
      190, 191, 192, 193, 194, 195, 202, 203, 204, 205, 206, 208, 209, 210, 211, 212, 213, 214,
      215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232,
      233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 245, 246, 247, 248, 249, 250, 251,
      252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 267, 269, 311, 312,
      313, 314, 332, 333, 334, 335, 336, 337, 338, 339, 340]),
   ("set idempotence", [81]),
   ("set-variable lemma", [167, 168, 169, 170, 171, 341]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [39, 40, 48, 49, 54, 56, 93, 95, 110, 114, 134, 151, 152, 207, 244, 266, 268, 270, 271, 272,
      273, 309, 310, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329,
      330, 331])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 35), ("rewrite rule", 6), ("priority equation", 0), ("constructor functional", 12), ("subsort", 18), ("injectivity", 7), ("distinctness", 10), ("no junk", 14), ("function functional", 18), ("hooked functional", 61), ("collection law", 9), ("library", 101), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 40)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The sentence is in the no-direction class exactly where it applies a head Γ lacks. -/
noncomputable def absentP (ad : AxiomDecl) : Bool :=
  (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)

theorem absentE_0 : (((U.all).drop 0).take 8).all absentP = true := by decide +kernel
theorem absentE_8 : (((U.all).drop 8).take 8).all absentP = true := by decide +kernel
theorem absentE_16 : (((U.all).drop 16).take 8).all absentP = true := by decide +kernel
theorem absentE_24 : (((U.all).drop 24).take 8).all absentP = true := by decide +kernel
theorem absentE_32 : (((U.all).drop 32).take 8).all absentP = true := by decide +kernel
theorem absentE_40 : (((U.all).drop 40).take 8).all absentP = true := by decide +kernel
theorem absentE_48 : (((U.all).drop 48).take 8).all absentP = true := by decide +kernel
theorem absentE_56 : (((U.all).drop 56).take 8).all absentP = true := by decide +kernel
theorem absentE_64 : (((U.all).drop 64).take 8).all absentP = true := by decide +kernel
theorem absentE_72 : (((U.all).drop 72).take 8).all absentP = true := by decide +kernel
theorem absentE_80 : (((U.all).drop 80).take 8).all absentP = true := by decide +kernel
theorem absentE_88 : (((U.all).drop 88).take 8).all absentP = true := by decide +kernel
theorem absentE_96 : (((U.all).drop 96).take 8).all absentP = true := by decide +kernel
theorem absentE_104 : (((U.all).drop 104).take 8).all absentP = true := by decide +kernel
theorem absentE_112 : (((U.all).drop 112).take 8).all absentP = true := by decide +kernel
theorem absentE_120 : (((U.all).drop 120).take 8).all absentP = true := by decide +kernel
theorem absentE_128 : (((U.all).drop 128).take 8).all absentP = true := by decide +kernel
theorem absentE_136 : (((U.all).drop 136).take 8).all absentP = true := by decide +kernel
theorem absentE_144 : (((U.all).drop 144).take 8).all absentP = true := by decide +kernel
theorem absentE_152 : (((U.all).drop 152).take 8).all absentP = true := by decide +kernel
theorem absentE_160 : (((U.all).drop 160).take 8).all absentP = true := by decide +kernel
theorem absentE_168 : (((U.all).drop 168).take 8).all absentP = true := by decide +kernel
theorem absentE_176 : (((U.all).drop 176).take 8).all absentP = true := by decide +kernel
theorem absentE_184 : (((U.all).drop 184).take 8).all absentP = true := by decide +kernel
theorem absentE_192 : (((U.all).drop 192).take 8).all absentP = true := by decide +kernel
theorem absentE_200 : (((U.all).drop 200).take 8).all absentP = true := by decide +kernel
theorem absentE_208 : (((U.all).drop 208).take 8).all absentP = true := by decide +kernel
theorem absentE_216 : (((U.all).drop 216).take 8).all absentP = true := by decide +kernel
theorem absentE_224 : (((U.all).drop 224).take 8).all absentP = true := by decide +kernel
theorem absentE_232 : (((U.all).drop 232).take 8).all absentP = true := by decide +kernel
theorem absentE_240 : (((U.all).drop 240).take 8).all absentP = true := by decide +kernel
theorem absentE_248 : (((U.all).drop 248).take 8).all absentP = true := by decide +kernel
theorem absentE_256 : (((U.all).drop 256).take 8).all absentP = true := by decide +kernel
theorem absentE_264 : (((U.all).drop 264).take 8).all absentP = true := by decide +kernel
theorem absentE_272 : (((U.all).drop 272).take 8).all absentP = true := by decide +kernel
theorem absentE_280 : (((U.all).drop 280).take 8).all absentP = true := by decide +kernel
theorem absentE_288 : (((U.all).drop 288).take 8).all absentP = true := by decide +kernel
theorem absentE_296 : (((U.all).drop 296).take 8).all absentP = true := by decide +kernel
theorem absentE_304 : (((U.all).drop 304).take 8).all absentP = true := by decide +kernel
theorem absentE_312 : (((U.all).drop 312).take 8).all absentP = true := by decide +kernel
theorem absentE_320 : (((U.all).drop 320).take 8).all absentP = true := by decide +kernel
theorem absentE_328 : (((U.all).drop 328).take 8).all absentP = true := by decide +kernel
theorem absentE_336 : ((U.all).drop 336).all absentP = true := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]; exact
    tieAll_whole (l := U.all) (p := absentP) <|
      tieAll_range (l := U.all) (p := absentP) (a := 0) (n := 8) absentE_0 <|
      tieAll_range (l := U.all) (p := absentP) (a := 8) (n := 8) absentE_8 <|
      tieAll_range (l := U.all) (p := absentP) (a := 16) (n := 8) absentE_16 <|
      tieAll_range (l := U.all) (p := absentP) (a := 24) (n := 8) absentE_24 <|
      tieAll_range (l := U.all) (p := absentP) (a := 32) (n := 8) absentE_32 <|
      tieAll_range (l := U.all) (p := absentP) (a := 40) (n := 8) absentE_40 <|
      tieAll_range (l := U.all) (p := absentP) (a := 48) (n := 8) absentE_48 <|
      tieAll_range (l := U.all) (p := absentP) (a := 56) (n := 8) absentE_56 <|
      tieAll_range (l := U.all) (p := absentP) (a := 64) (n := 8) absentE_64 <|
      tieAll_range (l := U.all) (p := absentP) (a := 72) (n := 8) absentE_72 <|
      tieAll_range (l := U.all) (p := absentP) (a := 80) (n := 8) absentE_80 <|
      tieAll_range (l := U.all) (p := absentP) (a := 88) (n := 8) absentE_88 <|
      tieAll_range (l := U.all) (p := absentP) (a := 96) (n := 8) absentE_96 <|
      tieAll_range (l := U.all) (p := absentP) (a := 104) (n := 8) absentE_104 <|
      tieAll_range (l := U.all) (p := absentP) (a := 112) (n := 8) absentE_112 <|
      tieAll_range (l := U.all) (p := absentP) (a := 120) (n := 8) absentE_120 <|
      tieAll_range (l := U.all) (p := absentP) (a := 128) (n := 8) absentE_128 <|
      tieAll_range (l := U.all) (p := absentP) (a := 136) (n := 8) absentE_136 <|
      tieAll_range (l := U.all) (p := absentP) (a := 144) (n := 8) absentE_144 <|
      tieAll_range (l := U.all) (p := absentP) (a := 152) (n := 8) absentE_152 <|
      tieAll_range (l := U.all) (p := absentP) (a := 160) (n := 8) absentE_160 <|
      tieAll_range (l := U.all) (p := absentP) (a := 168) (n := 8) absentE_168 <|
      tieAll_range (l := U.all) (p := absentP) (a := 176) (n := 8) absentE_176 <|
      tieAll_range (l := U.all) (p := absentP) (a := 184) (n := 8) absentE_184 <|
      tieAll_range (l := U.all) (p := absentP) (a := 192) (n := 8) absentE_192 <|
      tieAll_range (l := U.all) (p := absentP) (a := 200) (n := 8) absentE_200 <|
      tieAll_range (l := U.all) (p := absentP) (a := 208) (n := 8) absentE_208 <|
      tieAll_range (l := U.all) (p := absentP) (a := 216) (n := 8) absentE_216 <|
      tieAll_range (l := U.all) (p := absentP) (a := 224) (n := 8) absentE_224 <|
      tieAll_range (l := U.all) (p := absentP) (a := 232) (n := 8) absentE_232 <|
      tieAll_range (l := U.all) (p := absentP) (a := 240) (n := 8) absentE_240 <|
      tieAll_range (l := U.all) (p := absentP) (a := 248) (n := 8) absentE_248 <|
      tieAll_range (l := U.all) (p := absentP) (a := 256) (n := 8) absentE_256 <|
      tieAll_range (l := U.all) (p := absentP) (a := 264) (n := 8) absentE_264 <|
      tieAll_range (l := U.all) (p := absentP) (a := 272) (n := 8) absentE_272 <|
      tieAll_range (l := U.all) (p := absentP) (a := 280) (n := 8) absentE_280 <|
      tieAll_range (l := U.all) (p := absentP) (a := 288) (n := 8) absentE_288 <|
      tieAll_range (l := U.all) (p := absentP) (a := 296) (n := 8) absentE_296 <|
      tieAll_range (l := U.all) (p := absentP) (a := 304) (n := 8) absentE_304 <|
      tieAll_range (l := U.all) (p := absentP) (a := 312) (n := 8) absentE_312 <|
      tieAll_range (l := U.all) (p := absentP) (a := 320) (n := 8) absentE_320 <|
      tieAll_range (l := U.all) (p := absentP) (a := 328) (n := 8) absentE_328 <|
      absentE_336

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it
(`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-- The sentences of the no-direction class that are equations of a projection `project:X` (their
left side applies `Lblproject'Coln'X`), each with X. -/
def absentProj : List (Nat × String) :=
  [(315, "Bool"), (316, "Exp"), (317, "Float"), (318, "GeneratedCounterCell"),
   (319, "GeneratedCounterCellOpt"), (320, "GeneratedTopCell"), (321, "GeneratedTopCellFragment"),
   (322, "Id"), (323, "Int"), (324, "K"), (325, "KCell"), (326, "KCellOpt"), (327, "KItem"),
   (328, "List"), (329, "Map"), (330, "Set"), (331, "String")]

/-- Each sort of `absentProj` is K, KItem or a sort below KItem of Γ, with K and KItem
constructor sorts. -/
theorem absent_proj_below_c : absentProj.all (fun p => GenEqs.projBelowB c p.2) = true := by
  decide +kernel

/-- **The projections the no-direction class defines are of sorts below KItem**: `absentProj` is
the list of the no-direction sentences whose left side applies a symbol `Lblproject'Coln'X`, each
with that X, and each such X is K, KItem or a sort below KItem of Γ, with K and KItem constructor
sorts (`GenEqs.projBelowB`). So the pattern each of these equations is at is functional and
injective on X in every model of Γ (`GenEqs.projSel_fun`, `GenEqs.projSel_inj`): what the
equation states of the pattern's symbols, Γ entails. -/
theorem absent_proj_below (H : HookParams) :
    (userAxioms.filter (fun ad => (classOf "no direction").contains ad.index &&
        ((AttrsAgree.eqnHead ad.ax.pattern).getD "").startsWith "Lblproject'Coln'")).map
      (fun ad => (ad.index, AttrsAgree.eqnHead ad.ax.pattern)) =
      absentProj.map (fun p => (p.1, some ("Lblproject'Coln'" ++ p.2))) ∧
    absentProj.all (fun p => GenEqs.projBelowB (cH H) p.2) = true :=
  ⟨by rw [userAxioms_eq]; decide +kernel, absent_proj_below_c⟩

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(9, "subsort"), (15, "subsort"), (17, "subsort"), (18, "subsort"),
   (22, "constructor functional"), (23, "distinctness"), (24, "distinctness"),
   (25, "distinctness"), (26, "distinctness"), (38, "hooked functional"), (39, "no direction"),
   (40, "no direction"), (41, "hooked functional"), (48, "no direction"),
   (52, "hooked functional"), (58, "hooked functional"), (60, "hooked functional"),
   (64, "hooked functional"), (68, "hooked functional"), (70, "hooked functional"),
   (72, "hooked functional"), (98, "constructor functional"), (99, "distinctness"),
   (100, "distinctness"), (101, "distinctness"), (102, "constructor functional"),
   (103, "injectivity"), (104, "distinctness"), (105, "distinctness"), (106, "hooked functional"),
   (107, "constructor functional"), (108, "injectivity"), (109, "distinctness"),
   (110, "no direction"), (112, "constructor functional"), (113, "injectivity"),
   (117, "function functional"), (118, "function functional"), (123, "function functional"),
   (133, "function functional"), (136, "hooked functional"), (143, "constructor functional"),
   (145, "hooked functional"), (146, "hooked functional"), (150, "hooked functional"),
   (154, "no junk"), (155, "no junk"), (160, "no junk"), (165, "no junk"), (166, "no junk"),
   (196, "rewrite rule"), (197, "rewrite rule"), (198, "rewrite rule"), (199, "rewrite rule"),
   (200, "rewrite rule"), (201, "rewrite rule"), (202, "library"), (203, "library"),
   (204, "library"), (205, "library"), (223, "library"), (227, "library"), (230, "library"),
   (231, "library"), (234, "library"), (264, "library"), (265, "library"), (266, "no direction"),
   (267, "library"), (268, "no direction"), (273, "no direction"), (276, "function equation"),
   (277, "function equation"), (278, "function equation"), (279, "function equation"),
   (288, "function equation"), (289, "function equation"), (307, "function equation"),
   (308, "function equation"), (316, "no direction"), (317, "no direction"), (322, "no direction"),
   (331, "no direction"), (333, "library"), (334, "library"), (335, "library"), (336, "library"),
   (337, "library"), (338, "library"), (339, "library")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

/-! ## The declarations: `sig_origin` and `decls_entailed`, by ranges -/

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-- `p` holds of the whole list where it holds from `0` on. -/
theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :
    l.all p = true := h

/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/
noncomputable def sigFrom (it : Item) : Bool :=
  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigFrom = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 13).all sigFrom = true := by decide +kernel
theorem sigE_47 : (((sigItems c).drop 47).take 13).all sigFrom = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigFrom = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigFrom = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigFrom = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigFrom = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigFrom = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigFrom = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigFrom = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigFrom = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigFrom = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigFrom = true := by decide +kernel
theorem sigE_190 : (((sigItems c).drop 190).take 13).all sigFrom = true := by decide +kernel
theorem sigE_203 : ((sigItems c).drop 203).all sigFrom = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 214 := by decide +kernel

/-- **Every item of Γ's signature has its origin**: the item of a declaration of the text, or the
sort constant of a registry sort or the arity of an interpreted hooked symbol that the text does not
declare at that shape. -/
theorem sig_origin : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=
  tieAllE_whole (p := sigFrom) <|
    tieAllE_range (a := 0) (n := 34) sigE_0 <|
    tieAllE_range (a := 34) (n := 13) sigE_34 <|
    tieAllE_range (a := 47) (n := 13) sigE_47 <|
    tieAllE_range (a := 60) (n := 13) sigE_60 <|
    tieAllE_range (a := 73) (n := 13) sigE_73 <|
    tieAllE_range (a := 86) (n := 13) sigE_86 <|
    tieAllE_range (a := 99) (n := 13) sigE_99 <|
    tieAllE_range (a := 112) (n := 13) sigE_112 <|
    tieAllE_range (a := 125) (n := 13) sigE_125 <|
    tieAllE_range (a := 138) (n := 13) sigE_138 <|
    tieAllE_range (a := 151) (n := 13) sigE_151 <|
    tieAllE_range (a := 164) (n := 13) sigE_164 <|
    tieAllE_range (a := 177) (n := 13) sigE_177 <|
    tieAllE_range (a := 190) (n := 13) sigE_190 <|
    sigE_203

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)
noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- The declarations of the text: sorts, sorts without parameters, symbols, symbols without
parameters that Γ has, symbols with parameters, symbols without parameters that Γ lacks. -/
theorem decl_counts :
    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,
      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (19, 18, 174, 123, 5, 46) := by
  decide +kernel

theorem declsE_0 : (((declItems).drop 0).take 25).all inSigItems = true := by decide +kernel
theorem declsE_25 : (((declItems).drop 25).take 25).all inSigItems = true := by decide +kernel
theorem declsE_50 : (((declItems).drop 50).take 25).all inSigItems = true := by decide +kernel
theorem declsE_75 : (((declItems).drop 75).take 25).all inSigItems = true := by decide +kernel
theorem declsE_100 : (((declItems).drop 100).take 25).all inSigItems = true := by decide +kernel
theorem declsE_125 : ((declItems).drop 125).all inSigItems = true := by decide +kernel

theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 25) declsE_0 <|
    tieAllE_range (a := 25) (n := 25) declsE_25 <|
    tieAllE_range (a := 50) (n := 25) declsE_50 <|
    tieAllE_range (a := 75) (n := 25) declsE_75 <|
    tieAllE_range (a := 100) (n := 25) declsE_100 <|
    declsE_125

/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of
a symbol Γ has, for every H. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

/-! ## Consistency for every H -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (35 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 35 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax292, U.ax300, U.ax299, U.ax298, U.ax297, U.ax304, U.ax303, U.ax306, U.ax305, U.ax302,
   U.ax301, U.ax275, U.ax274, U.ax291, U.ax290, U.ax279, U.ax278, U.ax308, U.ax307, U.ax289,
   U.ax288, U.ax285, U.ax284, U.ax287, U.ax286, U.ax294, U.ax293, U.ax296, U.ax295, U.ax281,
   U.ax280, U.ax283, U.ax282, U.ax277, U.ax276]

set_option maxHeartbeats 1000000 in
/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel
decision). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl
  rw [fn_shape, List.getElem?_map] at h1
  cases hf : fnText[j]? with
  | none => rw [hf] at h1; cases h1
  | some ad =>
    rw [hf] at h1
    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩
    have he : (trS ad).pat = it.pat := Option.some.inj h1
    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The rules (6 sentences): W1 -/

/-- A rule axiom `\rewrites{C}(\and{C}(l, t, x), r)`, read as its parts. -/
def ruleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, x]) r => some (C, l, t, x, r)
  | _ => none

/-- The rule axiom without its left side's third conjunct. -/
def dropThird (p : Kore.Pattern) : Kore.Pattern :=
  match ruleParts p with
  | some (C, l, t, _, r) => .rewrites C (.and C [l, t]) r
  | none => p

theorem ruleParts_eq {p : Kore.Pattern} {C : Kore.KSort} {l t x r : Kore.Pattern}
    (h : ruleParts p = some (C, l, t, x, r)) : ∃ C', p = .rewrites C (.and C' [l, t, x]) r ∧ dropThird p = .rewrites C (.and C [l, t]) r := by
  unfold dropThird; rw [h]
  unfold ruleParts at h
  split at h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

/-- **A conjunct more on a rule's left side gives a consequence**: in a model of definedness, the
rule axiom with the left side `l ∧ t` entails the one with the left side `l ∧ t ∧ x`, where the
two have one variable table and one list of free variables. -/
theorem rewrite_weaken {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {p : Kore.Pattern}
    {C : Kore.KSort} {l t x r : Kore.Pattern} (hq : ruleParts p = some (C, l, t, x, r))
    (ht : tableOf [] p = tableOf [] (dropThird p))
    (hf : (freeOf [] p).eraseDups = (freeOf [] (dropThird p)).eraseDups)
    (h : I ⊧ᴵ (trAxiom [] [] (kAx (dropThird p))).pat) : I ⊧ᴵ (trAxiom [] [] (kAx p)).pat := by
  obtain ⟨C', hp, hd⟩ := ruleParts_eq hq
  intro e m
  have h1 := h e m
  simp only [trAxiom, kAx, List.map_nil, List.nil_append] at h1 ⊢
  rw [ht, hf]
  rw [hd] at h1 ⊢
  rw [hp] at ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  simp only [sortOf, tr, trAndList, sRewrites, interp_sImp, interp_sAnd] at h3 ⊢
  exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 ⟨hl.1, hl.2.1⟩⟩⟩


noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
noncomputable def r2 : Rule := c.rules[2]'(by decide +kernel)
noncomputable def r3 : Rule := c.rules[3]'(by decide +kernel)
noncomputable def r4 : Rule := c.rules[4]'(by decide +kernel)
noncomputable def r5 : Rule := c.rules[5]'(by decide +kernel)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0)),
    trAxiom [] [] (kAx (prioRuleK c r1)),
    trAxiom [] [] (kAx (prioRuleK c r2)),
    trAxiom [] [] (kAx (prioRuleK c r3)),
    trAxiom [] [] (kAx (prioRuleK c r4)),
    trAxiom [] [] (kAx (prioRuleK c r5))] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax196, U.ax197, U.ax198, U.ax199, U.ax200, U.ax201]

/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

theorem rule0_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule0_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule0_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 0 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 196. -/
theorem rule0_text : (trS U.ax196).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel
/-- **W1 for rule 0**: Γ's item is a consequence of sentence 196. -/
theorem rule0_from_text : itemsPremises [trS U.ax196] ⊧ (trAxiom [] [] (kAx (prioRuleK c r0))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule0_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule0_table rule0_free ?_
  rw [← rule0_text]
  exact hI _ (Or.inl ⟨trS U.ax196, List.mem_singleton_self _, rfl⟩)

theorem rule1_parts : (ruleParts (prioRuleK c r1)).isSome = true := by decide +kernel
theorem rule1_table : tableOf [] (prioRuleK c r1) = tableOf [] (dropThird (prioRuleK c r1)) := by decide +kernel
theorem rule1_free : (freeOf [] (prioRuleK c r1)).eraseDups = (freeOf [] (dropThird (prioRuleK c r1))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 1 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 197. -/
theorem rule1_text : (trS U.ax197).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r1)))).pat := by decide +kernel
/-- **W1 for rule 1**: Γ's item is a consequence of sentence 197. -/
theorem rule1_from_text : itemsPremises [trS U.ax197] ⊧ (trAxiom [] [] (kAx (prioRuleK c r1))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule1_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule1_table rule1_free ?_
  rw [← rule1_text]
  exact hI _ (Or.inl ⟨trS U.ax197, List.mem_singleton_self _, rfl⟩)

theorem rule2_parts : (ruleParts (prioRuleK c r2)).isSome = true := by decide +kernel
theorem rule2_table : tableOf [] (prioRuleK c r2) = tableOf [] (dropThird (prioRuleK c r2)) := by decide +kernel
theorem rule2_free : (freeOf [] (prioRuleK c r2)).eraseDups = (freeOf [] (dropThird (prioRuleK c r2))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 2 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 198. -/
theorem rule2_text : (trS U.ax198).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r2)))).pat := by decide +kernel
/-- **W1 for rule 2**: Γ's item is a consequence of sentence 198. -/
theorem rule2_from_text : itemsPremises [trS U.ax198] ⊧ (trAxiom [] [] (kAx (prioRuleK c r2))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule2_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule2_table rule2_free ?_
  rw [← rule2_text]
  exact hI _ (Or.inl ⟨trS U.ax198, List.mem_singleton_self _, rfl⟩)

theorem rule3_parts : (ruleParts (prioRuleK c r3)).isSome = true := by decide +kernel
theorem rule3_table : tableOf [] (prioRuleK c r3) = tableOf [] (dropThird (prioRuleK c r3)) := by decide +kernel
theorem rule3_free : (freeOf [] (prioRuleK c r3)).eraseDups = (freeOf [] (dropThird (prioRuleK c r3))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 3 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 199. -/
theorem rule3_text : (trS U.ax199).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r3)))).pat := by decide +kernel
/-- **W1 for rule 3**: Γ's item is a consequence of sentence 199. -/
theorem rule3_from_text : itemsPremises [trS U.ax199] ⊧ (trAxiom [] [] (kAx (prioRuleK c r3))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule3_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule3_table rule3_free ?_
  rw [← rule3_text]
  exact hI _ (Or.inl ⟨trS U.ax199, List.mem_singleton_self _, rfl⟩)

theorem rule4_parts : (ruleParts (prioRuleK c r4)).isSome = true := by decide +kernel
theorem rule4_table : tableOf [] (prioRuleK c r4) = tableOf [] (dropThird (prioRuleK c r4)) := by decide +kernel
theorem rule4_free : (freeOf [] (prioRuleK c r4)).eraseDups = (freeOf [] (dropThird (prioRuleK c r4))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 4 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 200. -/
theorem rule4_text : (trS U.ax200).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r4)))).pat := by decide +kernel
/-- **W1 for rule 4**: Γ's item is a consequence of sentence 200. -/
theorem rule4_from_text : itemsPremises [trS U.ax200] ⊧ (trAxiom [] [] (kAx (prioRuleK c r4))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule4_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule4_table rule4_free ?_
  rw [← rule4_text]
  exact hI _ (Or.inl ⟨trS U.ax200, List.mem_singleton_self _, rfl⟩)

theorem rule5_parts : (ruleParts (prioRuleK c r5)).isSome = true := by decide +kernel
theorem rule5_table : tableOf [] (prioRuleK c r5) = tableOf [] (dropThird (prioRuleK c r5)) := by decide +kernel
theorem rule5_free : (freeOf [] (prioRuleK c r5)).eraseDups = (freeOf [] (dropThird (prioRuleK c r5))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 5 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 201. -/
theorem rule5_text : (trS U.ax201).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r5)))).pat := by decide +kernel
/-- **W1 for rule 5**: Γ's item is a consequence of sentence 201. -/
theorem rule5_from_text : itemsPremises [trS U.ax201] ⊧ (trAxiom [] [] (kAx (prioRuleK c r5))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule5_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule5_table rule5_free ?_
  rw [← rule5_text]
  exact hI _ (Or.inl ⟨trS U.ax201, List.mem_singleton_self _, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨U.ax196, List.mem_cons_self, rule0_from_text⟩
  · exact ⟨U.ax197, List.mem_cons_of_mem _ (List.mem_cons_self), rule1_from_text⟩
  · exact ⟨U.ax198, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)), rule2_from_text⟩
  · exact ⟨U.ax199, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))), rule3_from_text⟩
  · exact ⟨U.ax200, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))), rule4_from_text⟩
  · exact ⟨U.ax201, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))), rule5_from_text⟩

/-! ## No junk -/

/-- `\or{S}(\top{S}(), \bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/
def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)

theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}
    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by
  intro e m
  unfold orTopBot
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  rw [interp_sOr, interp_sTop hD hS]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩

theorem nj153 : (trS U.ax153).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj155 : (trS U.ax155).pat = orTopBot (sym (.sort "SortFloat")) := by decide +kernel
theorem nj160 : (trS U.ax160).pat = orTopBot (sym (.sort "SortId")) := by decide +kernel
theorem nj161 : (trS U.ax161).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj164 : (trS U.ax164).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel
theorem nj166 : (trS U.ax166).pat = orTopBot (sym (.sort "SortString")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax153, U.ax155, U.ax160, U.ax161, U.ax164, U.ax166], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [nj153]; exact orTopBot_valid hD rfl
  · rw [nj155]; exact orTopBot_valid hD rfl
  · rw [nj160]; exact orTopBot_valid hD rfl
  · rw [nj161]; exact orTopBot_valid hD rfl
  · rw [nj164]; exact orTopBot_valid hD rfl
  · rw [nj166]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax154, U.ax156, U.ax157, U.ax158, U.ax159, U.ax162, U.ax163],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax154, U.ax156, U.ax157, U.ax158, U.ax159, U.ax162, U.ax163],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax165).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (165)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax165).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax30,
   U.ax31, U.ax32, U.ax33, U.ax34, U.ax35, U.ax36, U.ax37, U.ax98, U.ax99, U.ax100, U.ax101,
   U.ax102, U.ax103, U.ax104, U.ax105, U.ax107, U.ax108, U.ax109, U.ax112, U.ax113, U.ax139,
   U.ax140, U.ax143]

theorem consE_0 : (((consText).drop 0).take 8).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_8 : (((consText).drop 8).take 8).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_16 : (((consText).drop 16).take 8).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_24 : (((consText).drop 24).take 8).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_32 : (((consText).drop 32).take 8).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_40 : ((consText).drop 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true :=
  tieAll_whole (l := consText) (p := (fun ad => tieConsB c ad.ax)) <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 0) (n := 8) consE_0 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 8) (n := 8) consE_8 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 16) (n := 8) consE_16 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 24) (n := 8) consE_24 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 32) (n := 8) consE_32 <|
    consE_40

theorem consT_0 : (((consText).drop 0).take 8).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_8 : (((consText).drop 8).take 8).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_16 : (((consText).drop 16).take 8).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_24 : (((consText).drop 24).take 8).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_32 : (((consText).drop 32).take 8).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_40 : ((consText).drop 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true :=
  tieAll_whole (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 0) (n := 8) consT_0 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 8) (n := 8) consT_8 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 16) (n := 8) consT_16 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 24) (n := 8) consT_24 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 32) (n := 8) consT_32 <|
    consT_40

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax81.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax81).pat = (trAxiom [] [] U.ax81).pat := by decide +kernel

/-- `0` as a KItem, and the set `SetItem(0)`. -/
def a0 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))
def s1 : GroundTerm := .set Srt.set [a0]

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_none : hook setConcat [s1, s1] = some none := by decide +kernel
theorem concat_heard : silent setConcat [s1, s1] = false := by decide +kernel
theorem set_numbered : Srt.set < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.set < nRegSorts + c.sortNames.length)
theorem set_name : (cH H).sortName Srt.set = "Set" := (by decide +kernel : c.sortName Srt.set = "Set")
theorem idem_vars : (U.ax81.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax81.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax81.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 81 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax81).pat) := by
  intro M _ I hI hax
  rw [idem_trS] at hax
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI (set_numbered H)
  rw [set_name] at hσS1
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (s1_sort H) KoreAML.val0
  rw [set_name] at hesort
  let a := elemOf (cH H) I s1
  have ha : KoreAML.Inh I σS a := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hesort
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax81.ax.sortVars U.ax81.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax81.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax81.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m
    rw [idem_vars] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσS2
    · rw [List.mem_singleton.mp hk, KoreAML.interp_guard_evar hD, trSort_srt, hKv]
      exact hesort
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    rw [idem_sort]
    show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' a
    rw [KoreAML.interp_inhOf_of hRv]; exact ha)
  have hP : (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar)).interpret
      I e' a := by
    have := hP; simp only [tbl] at this ⊢; rw [idem_pattern] at this ⊢; exact this
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.set)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [show c.sortName Srt.set = "Set" from set_name H, trSort_srt]; exact hσS1 b
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hK : ∀ b, (KoreAML.tr ⟨tbl, []⟩ kVar).interpret I e' b ↔ b = a := fun b => by
    unfold kVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) ↔ b = a
    rw [hKv]
  have happ := (hall a ha).mpr ((hK a).mpr rfl)
  rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at happ
  have hden : (KoreAML.den (symApp (cH H) setConcat (GroundTerm.koreList (cH H) [s1, s1]))).interpret I KoreAML.val0 a := by
    unfold KoreAML.den
    rw [symApp_withHooks, tr_symApp]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp happ
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    refine KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, ?_, (hes b0).mpr ((hK b0).mp hb0), h0⟩,
      (hes b1).mpr ((hK b1).mp hb1), h1⟩
    exact (sym_congr (e := KoreAML.val0) (e' := e') _ f0).mpr hf0
  have hgraph := sat_dom hI (Or.inl ⟨_, [s1, s1], none, concat_sig, concat_args H, concat_none,
    fun _ => concat_heard, rfl⟩)
  exact ((KoreAML.interp_equal hD).mp (hgraph KoreAML.val0 default) a).mp hden

end Idem


/-! ## Library sample: sentence 216, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax216).pat = (trAxiom [] [] U.ax216).pat := by decide +kernel
theorem s166_pattern : U.ax216.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax216.ax.sortVars.map sortVarKey ++ freeOf [] U.ax216.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax216.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 216 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax216.ax.sortVars U.ax216.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax216).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax216.ax.sortVars U.ax216.ax.pattern = t at he ⊢
  rw [s166_pattern]
  rw [interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  have hIg := (interp_guard_evar hD).mp hg.2
  rw [interp_equal hD]
  intro a
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  have hS : ∀ b, (trSort t (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) := fun b => by
    rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) e
  obtain ⟨hes0, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int 0) = some Srt.int from rfl) e
  have hgraph := sat_dom hI (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int n, KCore.int 0], some (KCore.int (n - 0)),
    by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
  have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
  simp only [Int.sub_zero] at hg2
  -- the left side at `e` is the graph's application
  have hL : ∀ b, (tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])).interpret I e b ↔
      (KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0]))).interpret I e b := by
    intro b
    have h1 : tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ .evar (t.ev kI)) ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt")) := rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int n)) ⬝ den (cH H) (KCore.int 0) := by
      unfold symApp; rw [(sub_name H).1, (sub_name H).2]; rfl
    rw [h1, h2]
    refine interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m) (fun m => ?_) b
    · rw [interp_evar, he, hes]
    · rw [den_int0]
  simp only [sortOf]
  rw [KoreAML.tr, interp_sImp]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hR]
    refine ⟨(interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [hL b, hg2 b, hes b]
    rw [KoreAML.tr]
    show _ ↔ (sAnd (tr ⟨t, []⟩ vI) (tr ⟨t, []⟩ (.top (KoreAML.srt "Int")))).interpret I e b
    rw [interp_sAnd, KoreAML.tr]
    show _ ↔ (Pattern.evar (t.ev kI)).interpret I e b ∧ (sTop (trSort t (KoreAML.srt "Int"))).interpret I e b
    rw [interp_evar, he, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of hS]
    exact ⟨fun h => ⟨h, hb⟩, And.left⟩


theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      KoreAML.srt (c.sortName S) = KoreAML.srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)
/-- **Sentence 216 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax216 (trS U.ax216).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The converse over Γ's content -/

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, Γ's rule items (each a consequence of its
text sentence, `rule_from_text`), and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ ΓRules (cH H) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; a rule item is a consequence of a text sentence of `ruleText`; everything else is one of
the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ (ΓRules (cH H) φ ∧ ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ φ) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
  · exact hI _ (Or.inl (Or.inr hr))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inl (Or.inr hx)))

end KCore.TieE3Kast

#check @KCore.TieE3Kast.noRaw
#check @KCore.TieE3Kast.readsConfined_c
#check @KCore.TieE3Kast.userAxioms_eq
#check @KCore.TieE3Kast.coreOK
#check @KCore.TieE3Kast.wf_defn
#check @KCore.TieE3Kast.account
#check @KCore.TieE3Kast.account_sizes
#check @KCore.TieE3Kast.account_classes
#check @KCore.TieE3Kast.account_absent
#check @KCore.TieE3Kast.absent_closed
#check @KCore.TieE3Kast.absent_proj_below_c
#check @KCore.TieE3Kast.absent_proj_below
#check @KCore.TieE3Kast.lists_in_account
#check @KCore.TieE3Kast.attrs_agree
#check @KCore.TieE3Kast.sig_origin
#check @KCore.TieE3Kast.decls_entailed
#check @KCore.TieE3Kast.consistent
#check @KCore.TieE3Kast.fn_shape
#check @KCore.TieE3Kast.fns_account
#check @KCore.TieE3Kast.fns_entailed
#check @KCore.TieE3Kast.fns_from_text
#check @KCore.TieE3Kast.fn_prios
#check @KCore.TieE3Kast.nojunk_trivial_entailed
#check @KCore.TieE3Kast.nojunk_items_entailed
#check @KCore.TieE3Kast.nojunk_kitem_entailed
#check @KCore.TieE3Kast.cons_entailed
#check @KCore.TieE3Kast.rules_account
#check @KCore.TieE3Kast.rule_from_text
#check @KCore.TieE3Kast.idem_refuted
#check @KCore.TieE3Kast.lib166
#check @KCore.TieE3Kast.lib166_at_values
#check @KCore.TieE3Kast.gamma_origin
#check @KCore.TieE3Kast.gamma_from
#print axioms KCore.TieE3Kast.noRaw
#print axioms KCore.TieE3Kast.readsConfined_c
#print axioms KCore.TieE3Kast.userAxioms_eq
#print axioms KCore.TieE3Kast.coreOK
#print axioms KCore.TieE3Kast.wf_defn
#print axioms KCore.TieE3Kast.account
#print axioms KCore.TieE3Kast.account_sizes
#print axioms KCore.TieE3Kast.account_classes
#print axioms KCore.TieE3Kast.account_absent
#print axioms KCore.TieE3Kast.absent_closed
#print axioms KCore.TieE3Kast.absent_proj_below_c
#print axioms KCore.TieE3Kast.absent_proj_below
#print axioms KCore.TieE3Kast.lists_in_account
#print axioms KCore.TieE3Kast.attrs_agree
#print axioms KCore.TieE3Kast.sig_origin
#print axioms KCore.TieE3Kast.decls_entailed
#print axioms KCore.TieE3Kast.consistent
#print axioms KCore.TieE3Kast.fn_shape
#print axioms KCore.TieE3Kast.fns_account
#print axioms KCore.TieE3Kast.fns_entailed
#print axioms KCore.TieE3Kast.fns_from_text
#print axioms KCore.TieE3Kast.fn_prios
#print axioms KCore.TieE3Kast.nojunk_trivial_entailed
#print axioms KCore.TieE3Kast.nojunk_items_entailed
#print axioms KCore.TieE3Kast.nojunk_kitem_entailed
#print axioms KCore.TieE3Kast.cons_entailed
#print axioms KCore.TieE3Kast.rules_account
#print axioms KCore.TieE3Kast.rule_from_text
#print axioms KCore.TieE3Kast.idem_refuted
#print axioms KCore.TieE3Kast.lib166
#print axioms KCore.TieE3Kast.lib166_at_values
#print axioms KCore.TieE3Kast.gamma_origin
#print axioms KCore.TieE3Kast.gamma_from
