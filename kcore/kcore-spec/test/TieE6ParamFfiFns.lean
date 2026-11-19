/-
  Part Fns of the tie (C14) on `f2-examples/e6-param-ffi.kompile.kore`, test/TieE6ParamFfi.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e6-param-ffi --split`; run from the package root:
  `lake env lean -j1 test/TieE6ParamFfiFns.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamFfi

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-ffi.kompile.kore"
definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"
user_axioms U from "f2-examples/e6-param-ffi.kompile.kore" module "E6-PARAM-FFI"
user_axioms PreludeKseq from "f2-examples/e6-param-ffi.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [527, 528, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628,
      629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646,
      647, 648, 649, 650, 651]),
   ("rewrite rule", [529, 530, 531, 532, 533, 534, 535, 536]),
   ("priority equation", []),
   ("constructor functional", [24, 49, 73, 96, 118, 139, 159, 178, 196, 213, 229, 244, 258, 271, 283, 294, 305, 314, 322,
      329, 335, 340, 344, 347, 349, 354, 356, 358, 360, 427, 431, 460, 463, 464, 471, 477]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]),
   ("injectivity", [295, 355, 357, 359, 361, 432]),
   ("distinctness", [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
      72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
      97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
      116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134,
      135, 136, 137, 138, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
      154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172,
      173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191,
      192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210,
      211, 212, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230,
      231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 245, 246, 247, 248, 249,
      250, 251, 252, 253, 254, 255, 256, 257, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268,
      269, 270, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 284, 285, 286, 287, 288,
      289, 290, 291, 292, 293, 296, 297, 298, 299, 300, 301, 302, 303, 304, 306, 307, 308, 309,
      310, 311, 312, 313, 315, 316, 317, 318, 319, 320, 321, 323, 324, 325, 326, 327, 328, 330,
      331, 332, 333, 334, 336, 337, 338, 339, 341, 342, 343, 345, 346, 348, 428, 472]),
   ("no junk", [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]),
   ("function functional", [435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452,
      453, 454]),
   ("hooked functional", [350, 351, 352, 353, 362, 364, 367, 369, 370, 371, 372, 373, 374, 375, 378, 379, 380, 381,
      382, 384, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401,
      405, 413, 414, 415, 416, 417, 418, 419, 420, 421, 423, 425, 426, 429, 430, 434, 456, 457,
      459, 461, 462, 465, 466, 467, 468, 469, 470, 473, 474, 475, 476]),
   ("collection law", [402, 403, 404, 406, 407, 408, 409, 411, 412]),
   ("library", [496, 497, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518,
      519, 520, 521, 522, 523, 524, 525, 526, 537, 538, 544, 545, 546, 548, 549, 550, 551, 552,
      553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570,
      571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 585, 586, 587, 588, 589,
      590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 607, 608,
      654, 655, 656, 657, 677, 678, 679, 680, 681, 682, 683, 684, 685]),
   ("set idempotence", [410]),
   ("set-variable lemma", [498, 499, 500, 501, 502, 686]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [363, 365, 366, 368, 376, 377, 383, 385, 422, 424, 433, 455, 458, 478, 479, 539, 540, 541,
      542, 543, 547, 584, 606, 609, 610, 611, 612, 652, 653, 658, 659, 660, 661, 662, 663, 664,
      665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (41 sentences, and two of the prelude) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 43 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax527, U.ax528, PreludeKseq.ax1, PreludeKseq.ax2, U.ax633, U.ax641, U.ax640, U.ax639, U.ax638,
   U.ax645, U.ax644, U.ax647, U.ax646, U.ax643, U.ax642, U.ax614, U.ax613, U.ax632, U.ax631,
   U.ax622, U.ax621, U.ax651, U.ax650, U.ax616, U.ax615, U.ax618, U.ax617, U.ax649, U.ax648,
   U.ax628, U.ax627, U.ax630, U.ax629, U.ax635, U.ax634, U.ax637, U.ax636, U.ax624, U.ax623,
   U.ax626, U.ax625, U.ax620, U.ax619]

set_option maxHeartbeats 1000000 in
/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel
decision). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- The axioms of the prelude module KSEQ, in text order. -/
theorem preludeKseq_eq : kore.axiomDecls.filter (·.module == "KSEQ") = PreludeKseq.all := by kernel_rfl

/-- **`fnText`'s user-module sentences are the account's function-equation class**: the same
indices, each once; its other sentences are the prelude's, which no user sentence is. -/
theorem fns_account :
    (classOf "function equation").isPerm ((fnText.filter (·.module == "E6-PARAM-FFI")).map (·.index)) = true ∧
    (fnText.filter (·.module != "E6-PARAM-FFI")).map (fun ad => (ad.index, ad.module)) =
      [(1, "KSEQ"), (2, "KSEQ")] := by decide +kernel

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

/-! ## The rules (8 sentences): W1 -/

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
noncomputable def r6 : Rule := c.rules[6]'(by decide +kernel)
noncomputable def r7 : Rule := c.rules[7]'(by decide +kernel)

theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0)),
    trAxiom [] [] (kAx (prioRuleK c r1)),
    trAxiom [] [] (kAx (prioRuleK c r2)),
    trAxiom [] [] (kAx (prioRuleK c r3)),
    trAxiom [] [] (kAx (prioRuleK c r4)),
    trAxiom [] [] (kAx (prioRuleK c r5)),
    trAxiom [] [] (kAx (prioRuleK c r6)),
    trAxiom [] [] (kAx (prioRuleK c r7))] := by kernel_rfl

/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax529, U.ax530, U.ax531, U.ax532, U.ax533, U.ax534, U.ax535, U.ax536]

/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/
theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel

theorem rule0_parts : (ruleParts (prioRuleK c r0)).isSome = true := by decide +kernel
theorem rule0_table : tableOf [] (prioRuleK c r0) = tableOf [] (dropThird (prioRuleK c r0)) := by decide +kernel
theorem rule0_free : (freeOf [] (prioRuleK c r0)).eraseDups = (freeOf [] (dropThird (prioRuleK c r0))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 0 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 529. -/
theorem rule0_text : (trS U.ax529).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r0)))).pat := by decide +kernel
/-- **W1 for rule 0**: Γ's item is a consequence of sentence 529. -/
theorem rule0_from_text : itemsPremises [trS U.ax529] ⊧ (trAxiom [] [] (kAx (prioRuleK c r0))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule0_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule0_table rule0_free ?_
  rw [← rule0_text]
  exact hI _ (Or.inl ⟨trS U.ax529, List.mem_singleton_self _, rfl⟩)

theorem rule1_parts : (ruleParts (prioRuleK c r1)).isSome = true := by decide +kernel
theorem rule1_table : tableOf [] (prioRuleK c r1) = tableOf [] (dropThird (prioRuleK c r1)) := by decide +kernel
theorem rule1_free : (freeOf [] (prioRuleK c r1)).eraseDups = (freeOf [] (dropThird (prioRuleK c r1))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 1 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 530. -/
theorem rule1_text : (trS U.ax530).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r1)))).pat := by decide +kernel
/-- **W1 for rule 1**: Γ's item is a consequence of sentence 530. -/
theorem rule1_from_text : itemsPremises [trS U.ax530] ⊧ (trAxiom [] [] (kAx (prioRuleK c r1))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule1_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule1_table rule1_free ?_
  rw [← rule1_text]
  exact hI _ (Or.inl ⟨trS U.ax530, List.mem_singleton_self _, rfl⟩)

theorem rule2_parts : (ruleParts (prioRuleK c r2)).isSome = true := by decide +kernel
theorem rule2_table : tableOf [] (prioRuleK c r2) = tableOf [] (dropThird (prioRuleK c r2)) := by decide +kernel
theorem rule2_free : (freeOf [] (prioRuleK c r2)).eraseDups = (freeOf [] (dropThird (prioRuleK c r2))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 2 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 531. -/
theorem rule2_text : (trS U.ax531).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r2)))).pat := by decide +kernel
/-- **W1 for rule 2**: Γ's item is a consequence of sentence 531. -/
theorem rule2_from_text : itemsPremises [trS U.ax531] ⊧ (trAxiom [] [] (kAx (prioRuleK c r2))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule2_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule2_table rule2_free ?_
  rw [← rule2_text]
  exact hI _ (Or.inl ⟨trS U.ax531, List.mem_singleton_self _, rfl⟩)

theorem rule3_parts : (ruleParts (prioRuleK c r3)).isSome = true := by decide +kernel
theorem rule3_table : tableOf [] (prioRuleK c r3) = tableOf [] (dropThird (prioRuleK c r3)) := by decide +kernel
theorem rule3_free : (freeOf [] (prioRuleK c r3)).eraseDups = (freeOf [] (dropThird (prioRuleK c r3))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 3 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 532. -/
theorem rule3_text : (trS U.ax532).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r3)))).pat := by decide +kernel
/-- **W1 for rule 3**: Γ's item is a consequence of sentence 532. -/
theorem rule3_from_text : itemsPremises [trS U.ax532] ⊧ (trAxiom [] [] (kAx (prioRuleK c r3))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule3_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule3_table rule3_free ?_
  rw [← rule3_text]
  exact hI _ (Or.inl ⟨trS U.ax532, List.mem_singleton_self _, rfl⟩)

theorem rule4_parts : (ruleParts (prioRuleK c r4)).isSome = true := by decide +kernel
theorem rule4_table : tableOf [] (prioRuleK c r4) = tableOf [] (dropThird (prioRuleK c r4)) := by decide +kernel
theorem rule4_free : (freeOf [] (prioRuleK c r4)).eraseDups = (freeOf [] (dropThird (prioRuleK c r4))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 4 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 533. -/
theorem rule4_text : (trS U.ax533).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r4)))).pat := by decide +kernel
/-- **W1 for rule 4**: Γ's item is a consequence of sentence 533. -/
theorem rule4_from_text : itemsPremises [trS U.ax533] ⊧ (trAxiom [] [] (kAx (prioRuleK c r4))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule4_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule4_table rule4_free ?_
  rw [← rule4_text]
  exact hI _ (Or.inl ⟨trS U.ax533, List.mem_singleton_self _, rfl⟩)

theorem rule5_parts : (ruleParts (prioRuleK c r5)).isSome = true := by decide +kernel
theorem rule5_table : tableOf [] (prioRuleK c r5) = tableOf [] (dropThird (prioRuleK c r5)) := by decide +kernel
theorem rule5_free : (freeOf [] (prioRuleK c r5)).eraseDups = (freeOf [] (dropThird (prioRuleK c r5))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 5 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 534. -/
theorem rule5_text : (trS U.ax534).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r5)))).pat := by decide +kernel
/-- **W1 for rule 5**: Γ's item is a consequence of sentence 534. -/
theorem rule5_from_text : itemsPremises [trS U.ax534] ⊧ (trAxiom [] [] (kAx (prioRuleK c r5))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule5_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule5_table rule5_free ?_
  rw [← rule5_text]
  exact hI _ (Or.inl ⟨trS U.ax534, List.mem_singleton_self _, rfl⟩)

theorem rule6_parts : (ruleParts (prioRuleK c r6)).isSome = true := by decide +kernel
theorem rule6_table : tableOf [] (prioRuleK c r6) = tableOf [] (dropThird (prioRuleK c r6)) := by decide +kernel
theorem rule6_free : (freeOf [] (prioRuleK c r6)).eraseDups = (freeOf [] (dropThird (prioRuleK c r6))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 6 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 535. -/
theorem rule6_text : (trS U.ax535).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r6)))).pat := by decide +kernel
/-- **W1 for rule 6**: Γ's item is a consequence of sentence 535. -/
theorem rule6_from_text : itemsPremises [trS U.ax535] ⊧ (trAxiom [] [] (kAx (prioRuleK c r6))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule6_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule6_table rule6_free ?_
  rw [← rule6_text]
  exact hI _ (Or.inl ⟨trS U.ax535, List.mem_singleton_self _, rfl⟩)

theorem rule7_parts : (ruleParts (prioRuleK c r7)).isSome = true := by decide +kernel
theorem rule7_table : tableOf [] (prioRuleK c r7) = tableOf [] (dropThird (prioRuleK c r7)) := by decide +kernel
theorem rule7_free : (freeOf [] (prioRuleK c r7)).eraseDups = (freeOf [] (dropThird (prioRuleK c r7))).eraseDups := by
  decide +kernel
/-- Γ's item of rule 7 without its premise `⌈rhs ∧ ens⌉` is the text's sentence 536. -/
theorem rule7_text : (trS U.ax536).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r7)))).pat := by decide +kernel
/-- **W1 for rule 7**: Γ's item is a consequence of sentence 536. -/
theorem rule7_from_text : itemsPremises [trS U.ax536] ⊧ (trAxiom [] [] (kAx (prioRuleK c r7))).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule7_parts
  obtain ⟨C, l, t, x, r⟩ := q
  refine rewrite_weaken hD hq rule7_table rule7_free ?_
  rw [← rule7_text]
  exact hI _ (Or.inl ⟨trS U.ax536, List.mem_singleton_self _, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a
consequence of a text sentence of `ruleText`, for every H. -/
theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by
  intro it hit
  rw [ruleItems_withHooks, ruleItems_eq] at hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨U.ax529, List.mem_cons_self, rule0_from_text⟩
  · exact ⟨U.ax530, List.mem_cons_of_mem _ (List.mem_cons_self), rule1_from_text⟩
  · exact ⟨U.ax531, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)), rule2_from_text⟩
  · exact ⟨U.ax532, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))), rule3_from_text⟩
  · exact ⟨U.ax533, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))), rule4_from_text⟩
  · exact ⟨U.ax534, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))), rule5_from_text⟩
  · exact ⟨U.ax535, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))), rule6_from_text⟩
  · exact ⟨U.ax536, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))), rule7_from_text⟩

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

end KCore.TieE6ParamFfi

#check @KCore.TieE6ParamFfi.preludeKseq_eq
#check @KCore.TieE6ParamFfi.fn_shape
#check @KCore.TieE6ParamFfi.fns_account
#check @KCore.TieE6ParamFfi.fns_entailed
#check @KCore.TieE6ParamFfi.fns_from_text
#check @KCore.TieE6ParamFfi.fn_prios
#check @KCore.TieE6ParamFfi.rules_account
#check @KCore.TieE6ParamFfi.rule_from_text
#check @KCore.TieE6ParamFfi.gamma_origin
#check @KCore.TieE6ParamFfi.gamma_from
#print axioms KCore.TieE6ParamFfi.preludeKseq_eq
#print axioms KCore.TieE6ParamFfi.fn_shape
#print axioms KCore.TieE6ParamFfi.fns_account
#print axioms KCore.TieE6ParamFfi.fns_entailed
#print axioms KCore.TieE6ParamFfi.fns_from_text
#print axioms KCore.TieE6ParamFfi.fn_prios
#print axioms KCore.TieE6ParamFfi.rules_account
#print axioms KCore.TieE6ParamFfi.rule_from_text
#print axioms KCore.TieE6ParamFfi.gamma_origin
#print axioms KCore.TieE6ParamFfi.gamma_from
