/-
  The seven `[owise]` function equations of kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`) that `test/TieKkFns.lean` leaves
  open, on the literals `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the
  package root: `lake env lean test/TieKkOwise.lean`.

  - `owAt`: the positions of the seven among Γ's function equations (`fnItems`, the order of
    `TieKkFns.fnText`) with their sentences: 30 `cmp` 502, 108 `hookOp` 563, 132 `isElem` 627,
    165 `match` 708, 171 `matchCol` 723, 184 `mkInj` 738, 224 `tag` 816. `ow_keys`: the clause at
    each position has priority 200 and the sentence is its function's equation of that priority.
  - `ow_same`: at each, Γ's item and the sentence's translation agree up to the order of the
    operands of their sorted disjunctions and the names of their variables (`TieAlpha.acEqB`), one
    kernel decision per position. The exclusion of each lists the other equations' conditions as a
    chain of disjunctions, in another order on the two sides (at 184 in the same order); the bound
    variables have other indices (the text's `_Gen` names against Γ's `VarV` names, each its own
    key of the variable table), and so do some free ones.
  - `ow_entailed` (E): Γ entails each of the seven sentences, for every H;
    `ow_from_text` (the converse): the item at each position is a consequence of its sentence.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The seven `[owise]` equations: the position of each among Γ's items, and its sentence. -/
noncomputable def owAt : List (Nat × AxiomDecl) :=
  [(30, U.ax502), (108, U.ax563), (132, U.ax627), (165, U.ax708), (171, U.ax723), (184, U.ax738),
   (224, U.ax816)]

/-- Each of the seven is the `[owise]` equation of the function at its position: the clause there
has priority 200, and the sentence is the first equation of the user module with that head symbol
and priority (`TiePair.findEqn`). -/
theorem ow_keys : owAt.all (fun p => ((TiePair.clauseKeys c)[p.1]?.map (·.2) == some 200) &&
    (((TiePair.clauseKeys c)[p.1]?.bind (TiePair.findEqn U.all)).map (·.index) == some p.2.index)) = true := by
  decide +kernel

/-- The item at the position and the sentence's translation agree up to the order of disjuncts
and the names of variables. -/
noncomputable def owSame (p : Nat × AxiomDecl) : Bool :=
  match (TiePair.gammaPats c)[p.1]? with
  | some g => TieAlpha.acEqB g (trS p.2).pat
  | none => false

theorem ow_30 : owSame (30, U.ax502) = true := by decide +kernel
theorem ow_108 : owSame (108, U.ax563) = true := by decide +kernel
theorem ow_132 : owSame (132, U.ax627) = true := by decide +kernel
theorem ow_165 : owSame (165, U.ax708) = true := by decide +kernel
theorem ow_171 : owSame (171, U.ax723) = true := by decide +kernel
theorem ow_184 : owSame (184, U.ax738) = true := by decide +kernel
theorem ow_224 : owSame (224, U.ax816) = true := by decide +kernel

theorem ow_same : ∀ p ∈ owAt, owSame p = true := by
  intro p hp
  simp only [owAt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ow_30
  · exact ow_108
  · exact ow_132
  · exact ow_165
  · exact ow_171
  · exact ow_184
  · exact ow_224

/-- At each of the seven the item and the sentence are satisfied by the same interpretations. -/
theorem ow_iff {p : Nat × AxiomDecl} (hp : p ∈ owAt) : ∃ g, (TiePair.gammaPats c)[p.1]? = some g ∧
    ∀ {M : Type} {I : Interpretation KoreAML.Sym M}, (I ⊧ᴵ (trS p.2).pat) ↔ (I ⊧ᴵ g) := by
  have h := ow_same p hp
  unfold owSame at h
  cases hg : (TiePair.gammaPats c)[p.1]? with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    exact ⟨g, rfl, fun {M I} => (TieAlpha.acEqB_sat h).symm⟩

/-- **E for the seven `[owise]` equations**: Γ entails each sentence, for every H. -/
theorem ow_entailed (H : HookParams) : ∀ p ∈ owAt, Γ (cH H) ⊧ (trS p.2).pat := by
  intro p hp M _ I hI
  obtain ⟨g, hg, hiff⟩ := ow_iff hp
  refine hiff.mpr ?_
  obtain ⟨it, hit, rfl⟩ : ∃ it ∈ fnItems c, it.pat = g := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[p.1]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  exact hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))))

/-- **The converse for the seven**: the item at each position is a consequence of its sentence,
for every H. -/
theorem ow_from_text (H : HookParams) : ∀ p ∈ owAt, ∀ it, (fnItems (cH H))[p.1]? = some it →
    (itemsPremises [trS p.2] ⊧ it.pat) := by
  intro p hp it hit
  rw [TiePair.fnItems_withHooks] at hit
  obtain ⟨g, hg, hiff⟩ := ow_iff hp
  have : g = it.pat := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map, hit] at hg
    exact (Option.some.inj hg).symm
  subst this
  exact fun {M} _ {I} hI => hiff.mp (hI _ (Or.inl ⟨trS p.2, List.mem_singleton_self _, rfl⟩))

end KCore.TieKk

#check @KCore.TieKk.ow_entailed
#check @KCore.TieKk.ow_from_text
#print axioms KCore.TieKk.ow_entailed
#print axioms KCore.TieKk.ow_from_text
