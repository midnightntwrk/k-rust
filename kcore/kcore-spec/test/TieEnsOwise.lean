/-
  The tie of the function equations on `f2-examples/ens-owise.kompile.kore`: an equation with an
  `ensures` beside a user `[owise]` equation of one function, `half`, whose `[owise]` sentence
  (212) binds a variable of the sort of its outer variable. Run from the package root:
  `lake env lean test/TieEnsOwise.lean`.

  - Of Γ's 31 function equations, 30 are the translations of their text sentences, pattern for
    pattern (`shape`): `half`'s first equation (211) and the 29 sort predicates' equations.
  - The 31st, `half`'s `[owise]` equation, is not (`owise_differs`). The reason is the binder's key
    (`owise_tables`): the text names the exclusion's bound variable `_Gen1` and the equation's own
    variable `_Gen0`, two keys of the sentence's table; Γ's sentence gives both the name `VarV0`
    (an exclusion binds its variables, so it reuses the equation's names), one key. The bound
    variable has index 2 on both sides; the equation's own variable has index 4 in the text and 2
    in Γ's. So the text's pattern is Γ's with its free variable 2 renamed to 4 (`owise_renamed`, a
    kernel decision), and the two sentences are satisfied by the same interpretations
    (`sat_renamed`).
  - So Γ entails each of the 31 sentences, for every H (`fns_entailed`, E), and each of Γ's 31
    items is a consequence of its sentence (`fns_from_text`, the converse); for 30 by equality,
    for 212 by the renaming.
  - `account`: the class lists partition the 264 sentences of the user module; `account_absent`:
    the no-direction class holds exactly the sentences that apply a head name no symbol of Γ has.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEnsOwise

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens-owise.kompile.kore"
definition_of defn from "f2-examples/ens-owise.kompile.kore"
user_axioms U from "f2-examples/ens-owise.kompile.kore" module "ENS-OWISE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "ENS-OWISE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 264 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c

/-! ## The function equations (31 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The patterns of Γ's 31 equations, in `fnItems`'s order. -/
noncomputable def gammaPats : List P := (fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat

theorem gammaPats_eq : (fnItems c).map (·.pat) = gammaPats := by
  unfold gammaPats; rw [fnItems_eq, List.map_map]; rfl

/-- The text sentences of Γ's 31 equations, in `fnItems`'s order: `half`'s two (211, and 212 its
`[owise]` one), then the sort predicates' (`isX`'s plain equation, then its `[owise]` one). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax211, U.ax212, U.ax230, U.ax238, U.ax237, U.ax236, U.ax235, U.ax242, U.ax241, U.ax244, U.ax243, U.ax240,
   U.ax239, U.ax217, U.ax216, U.ax229, U.ax228, U.ax225, U.ax224, U.ax227, U.ax226, U.ax232, U.ax231, U.ax234,
   U.ax233, U.ax221, U.ax220, U.ax223, U.ax222, U.ax219, U.ax218]

/-- The translations of the text's sentences, in that order. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- Γ's item for `half`'s `[owise]` equation. -/
noncomputable def g212 : P := gammaPats.getD 1 ⊥

theorem gamma_1 : gammaPats[1]? = some g212 := by decide +kernel
theorem text_1 : fnText[1]? = some U.ax212 := rfl

/-- **Γ's equations are the text's sentences' translations, pattern for pattern, but the one at
index 1** (`half`'s `[owise]` equation). -/
theorem shape : gammaPats = textPats.set 1 g212 := by decide +kernel

/-- **`half`'s `[owise]` equation is not the translation of sentence 212.** -/
theorem owise_differs : g212 ≠ (trS U.ax212).pat := by decide +kernel

/-- The reason: the variable tables. Γ's sentence has one key for the exclusion's bound variable
and the equation's own variable; the text's has two. -/
theorem owise_tables :
    (fnAxioms c)[1]?.map (fun a => tableOf a.sortVars a.pattern) =
        some [.sortVar "R", .evar "VarV0" (KoreAML.srt "Int"), .evar "X0" (KoreAML.srt "Int")] ∧
      tableOf U.ax212.ax.sortVars U.ax212.ax.pattern =
        [.sortVar "R", .evar "Var'Unds'Gen1" (KoreAML.srt "Int"), .evar "X0" (KoreAML.srt "Int"),
         .evar "Var'Unds'Gen0" (KoreAML.srt "Int")] := by decide +kernel

/-- **Sentence 212's translation is Γ's item with its free variable 2 renamed to 4**: the
substitution captures nothing and 4 is not free in Γ's item. -/
theorem owise_renamed : (trS U.ax212).pat = g212.substEvar ⟨2⟩ (.evar ⟨4⟩) ∧
    renOK ⟨2⟩ ⟨4⟩ g212 = true ∧ g212.isFreeEvar ⟨4⟩ = false := by decide +kernel

/-- An interpretation satisfies sentence 212 exactly when it satisfies Γ's item. -/
theorem owise_iff {M : Type} {I : Interpretation KoreAML.Sym M} : (I ⊧ᴵ (trS U.ax212).pat) ↔ (I ⊧ᴵ g212) := by
  rw [owise_renamed.1]
  exact sat_renamed owise_renamed.2.1 owise_renamed.2.2

/-- **E for the 31 equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hΓ : ∀ p ∈ gammaPats, I ⊧ᴵ p := fun p hp => by
    rw [← gammaPats_eq] at hp
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hp
    exact hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, rfl⟩))))
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp had
  by_cases h1 : j = 1
  · subst h1
    rw [text_1] at hj
    cases hj
    exact owise_iff.mpr (hΓ _ (List.mem_of_getElem? gamma_1))
  · have ht : textPats[j]? = some (trS ad).pat := by
      unfold textPats; rw [List.getElem?_map, hj]; rfl
    have hg : gammaPats[j]? = some (trS ad).pat := by
      rw [shape, List.getElem?_set_ne (Ne.symm h1)]; exact ht
    exact hΓ _ (List.mem_of_getElem? hg)

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have h1 : gammaPats[j]? = some it.pat := by rw [← gammaPats_eq, List.getElem?_map, hj]; rfl
  by_cases hj1 : j = 1
  · subst hj1
    rw [gamma_1] at h1
    refine ⟨U.ax212, rfl, fun {M} _ {I} hI => ?_⟩
    rw [← Option.some.inj h1]
    exact owise_iff.mp (hI _ (Or.inl ⟨trS U.ax212, List.mem_singleton_self _, rfl⟩))
  · rw [shape, List.getElem?_set_ne (Ne.symm hj1)] at h1
    unfold textPats at h1
    rw [List.getElem?_map] at h1
    cases hf : fnText[j]? with
    | none => rw [hf] at h1; cases h1
    | some ad =>
      rw [hf] at h1
      refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩
      have he : (trS ad).pat = it.pat := Option.some.inj h1
      exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)

/-! ## The account -/

/-- Per class, the indices (`AxiomDecl.index`) of its sentences; the classes are those of the tie
of `f2-examples/ens.kompile.kore` (`tieClasses`), which this text's sentences follow with the one
`[owise]` equation more (212; the sentences after it one index later than ens's): the definedness
lemmas over set variables 126 to 130 and 267 (`#Ceil` of `%Int`, `/Int`, `<<Int`, `>>Int`, `modInt`
and of a map with one entry and a rest) are set-variable lemmas, and the shift equations 171, 172,
178, 179 library sentences, `<<Int` and `>>Int` being symbols of Γ. -/
def classes : List (String × List Nat) :=
  [("function equation", [211, 212, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231,
      232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]),
   ("rewrite rule", [155]),
   ("priority equation", []),
   ("constructor functional", [22, 24, 26, 28, 78, 103, 104, 108]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]),
   ("injectivity", [23, 25, 27, 29, 79, 109]),
   ("distinctness", [80]),
   ("no junk", [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125]),
   ("function functional", [84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]),
   ("hooked functional", [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51,
      52, 56, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 76, 77, 81, 83, 100, 101, 102, 105, 106, 107, 110, 111,
      112]),
   ("collection law", [53, 54, 55, 57, 58, 59, 60, 62, 63]),
   ("library", [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150,
      151, 152, 153, 154, 156, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
      174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195,
      196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 209, 247, 248, 249, 250, 265]),
   ("set idempotence", [61]),
   ("set-variable lemma", [126, 127, 128, 129, 130, 267]),
   ("no direction", [36, 40, 42, 73, 75, 82, 99, 113, 114, 157, 189, 208, 210, 213, 214, 215, 245, 246, 251, 252,
      253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 266])]

/-- **The account**: the class lists partition the user module's sentences, and the function
equations' list is `fnText`'s. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup ∧
    ((classes.filter (·.1 == "function equation")).flatMap (·.2)).isPerm (fnText.map (·.index)) = true := by
  rw [userAxioms_eq]; decide +kernel

/-- The class of each name. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. 99, 245 and 246 apply instances of `ite` (`ite{Sort}`, `ite{SortK}`): a symbol with sort
parameters is one symbol at each instance, and Γ applies its `ite`, the registry's `kIte` at KItem,
at no sort argument, so the three are of the no-direction class. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]; decide +kernel

end KCore.TieEnsOwise

#print axioms KCore.TieEnsOwise.shape
#print axioms KCore.TieEnsOwise.owise_differs
#print axioms KCore.TieEnsOwise.owise_renamed
#print axioms KCore.TieEnsOwise.fns_entailed
#print axioms KCore.TieEnsOwise.fns_from_text
#print axioms KCore.TieEnsOwise.account
#print axioms KCore.TieEnsOwise.account_classes
#print axioms KCore.TieEnsOwise.account_absent
