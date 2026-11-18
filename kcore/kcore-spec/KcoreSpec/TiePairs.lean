/-
  KCore, outside the cone: the tie of a text's function equations and the cut from Γ's theorems to
  a premise set of sentences as written, for any semantics. A tie file of one text instantiates
  these with kernel decisions on the literal definition; nothing here reads `Parse.parse` or
  `Definition.emit`.

  - `sameB g t`: the patterns are equal, or `t` is `g` with one free variable renamed, so that the
    same interpretations satisfy them (`sameB_iff`, from `Faithful.sat_renamed`). `shapeB G T`: the
    two lists agree so, position by position.
  - For a list `T` of patterns with `shapeB (gammaPats c) T` (`gammaPats c`: the patterns of
    `fnItems c`): Γ entails each member of `T` (`entailed`), each item of `fnItems c` is a
    consequence of the member at its index (`from_text`), every premise of Γ is a consequence of
    `Pre c T` (`T` with definedness, Γ's rule items, and the parts of Γ defined by predicates,
    `Families`: `gamma_from`), which has a model with the step's closure where Γ has one
    (`pre_model`); so what Γ entails `Pre c T` entails (`cut`), in particular a function's value
    or its having none at an argument list where `Eval` gives it (`value`, `noValue`).
  - `eval_withHooks`: a result the evaluator `Cert.evalFC` computes is `Eval`'s under every
    interpretation of the parameters, for a definition without an open generator.
  - `fnDet_withHooks`: one result at each argument list, from the agreement decider.
  - `fnModel_noTotal`: `FnDet` and `FnSolves` from the facts on termination, agreement and match
    independence the deciders leave; the totality of a `[total]` function is not read.
  - `not_total_of_none`: a function with the result none at an argument list of its sorts, where
    results are unique, is not `Total`.
-/
import KcoreSpec.TieCons
import KcoreSpec.TieRename
import KcoreSpec.TieDefs
import KcoreSpec.FnObligations
import KcoreSpec.StepCompleteAt
import KcoreSpec.ModelFunctional
import KcoreSpec.Cert

set_option autoImplicit false

namespace KCore

namespace TiePair

open ML Faithful KoreAML

/-! ## Patterns satisfied by the same interpretations -/

/-- One renaming step: the free variable `p.1` renamed to `p.2`, where `p.2` is not free and no
occurrence is captured. -/
def renStep (g : P) (p : Nat × Nat) : Option P :=
  if renOK ⟨p.1⟩ ⟨p.2⟩ g && !g.isFreeEvar ⟨p.2⟩ then some (g.substEvar ⟨p.1⟩ (.evar ⟨p.2⟩)) else none

/-- A sequence of renaming steps. -/
def renSeq (g : P) : List (Nat × Nat) → Option P
  | [] => some g
  | p :: ps => (renStep g p).bind fun g' => renSeq g' ps

theorem renSeq_iff {M : Type} {I : Interpretation KoreAML.Sym M} : ∀ {s : List (Nat × Nat)} {g t : P},
    renSeq g s = some t → ((I ⊧ᴵ t) ↔ (I ⊧ᴵ g))
  | [], g, t, h => by cases h; exact Iff.rfl
  | p :: ps, g, t, h => by
    unfold renSeq at h
    obtain ⟨g', hg', ht⟩ := Option.bind_eq_some_iff.mp h
    unfold renStep at hg'
    split at hg'
    next hc =>
      cases hg'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact (renSeq_iff ht).trans (sat_renamed hc.1 hc.2)
    next => cases hg'

/-- The index no sentence here uses, through which two variables are exchanged. -/
def renSpare : Nat := 63

/-- The renamings tried: one free variable renamed, or two exchanged. -/
def renCands : List (List (Nat × Nat)) :=
  ((List.range 10).flatMap fun x => (List.range 10).map fun y => [(x, y)]) ++
    (List.range 10).flatMap fun x => (List.range 10).map fun y => [(x, renSpare), (y, x), (renSpare, y)]

/-- `t` is `g`, or `g` under one of the renamings of `renCands`. -/
def sameB (g t : P) : Bool :=
  decide (g = t) || renCands.any fun s => decide (renSeq g s = some t)

/-- Patterns `sameB` accepts are satisfied by the same interpretations. -/
theorem sameB_iff {g t : P} (h : sameB g t = true) {M : Type} {I : Interpretation KoreAML.Sym M} :
    (I ⊧ᴵ t) ↔ (I ⊧ᴵ g) := by
  unfold sameB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [of_decide_eq_true h]
  · obtain ⟨s, -, hs⟩ := List.any_eq_true.mp h
    exact renSeq_iff (of_decide_eq_true hs)

/-- The lists have one length and `sameB` holds position by position. -/
def shapeB (G T : List P) : Bool := G.length == T.length && (G.zip T).all fun p => sameB p.1 p.2

theorem shape_at {G T : List P} (h : shapeB G T = true) {j : Nat} {g t : P} (hg : G[j]? = some g)
    (ht : T[j]? = some t) : sameB g t = true := by
  unfold shapeB at h
  have h2 := (Bool.and_eq_true_iff.mp h).2
  refine List.all_eq_true.mp h2 (g, t) ?_
  exact List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_zip_eq_some]; exact ⟨hg, ht⟩⟩

theorem shape_right {G T : List P} (h : shapeB G T = true) {j : Nat} {g : P} (hg : G[j]? = some g) :
    ∃ t, T[j]? = some t ∧ sameB g t = true := by
  have hl : G.length = T.length := by
    unfold shapeB at h; exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
  have hj : j < T.length := hl ▸ (List.getElem?_eq_some_iff.mp hg).1
  exact ⟨T[j], List.getElem?_eq_getElem hj, shape_at h hg (List.getElem?_eq_getElem hj)⟩

theorem shape_left {G T : List P} (h : shapeB G T = true) {j : Nat} {t : P} (ht : T[j]? = some t) :
    ∃ g, G[j]? = some g ∧ sameB g t = true := by
  have hl : G.length = T.length := by
    unfold shapeB at h; exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
  have hj : j < G.length := hl ▸ (List.getElem?_eq_some_iff.mp ht).1
  exact ⟨G[j], List.getElem?_eq_getElem hj, shape_at h (List.getElem?_eq_getElem hj) ht⟩

/-! ## The premise set -/

/-- The patterns of Γ's function equations, in `fnItems`'s order. -/
noncomputable def gammaPats (c : Semantics) : List P := (fnItems c).map (·.pat)

/-- The axioms of Γ's function equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

/-- A function's clauses in `fnItems`'s order, each as its function's name and its priority. -/
def clauseKeys (c : Semantics) : List (String × Nat) :=
  c.allFns.flatMap fun f => f.clauses.map fun cl => (c.symName f.label, cl.prio)

/-- The first of the axioms `us` that is an equation with the symbol named `k.1` at the head of its
left side, of the priority `k.2` by its attributes, and not a `simplification`. -/
def findEqn (us : List AxiomDecl) (k : String × Nat) : Option AxiomDecl :=
  us.find? fun ad => AttrsAgree.eqnHead ad.ax.pattern == some k.1 &&
    AttrsAgree.prioOf ad.ax.attributes == k.2 && !AttrsAgree.has ad.ax.attributes "simplification"

/-- `findEqn`'s test: `ad` is an equation with the symbol named `k.1` at the head of its left side,
of the priority `k.2`, and not a `simplification`. -/
def eqnKeyB (k : String × Nat) (ad : AxiomDecl) : Bool :=
  AttrsAgree.eqnHead ad.ax.pattern == some k.1 && AttrsAgree.prioOf ad.ax.attributes == k.2 &&
    !AttrsAgree.has ad.ax.attributes "simplification"

/-- The first of `us` that `eqnKeyB k` accepts, with the others in their order. -/
def takeEqn (k : String × Nat) : List AxiomDecl → Option (AxiomDecl × List AxiomDecl)
  | [] => none
  | ad :: us => if eqnKeyB k ad then some (ad, us) else (takeEqn k us).map fun p => (p.1, ad :: p.2)

/-- For each key in order, the first sentence of `us` of that key that no earlier key took. -/
def fnTextFrom : List (String × Nat) → List AxiomDecl → List AxiomDecl
  | [], _ => []
  | k :: ks, us => match takeEqn k us with
    | some (ad, rest) => ad :: fnTextFrom ks rest
    | none => fnTextFrom ks us

/-- The sentences among `us` of the clauses of `c`, in `fnItems`'s order, found by head symbol and
priority: each clause takes the first sentence of its function's symbol and its priority that no
earlier clause took (`fnTextFrom`), so two clauses of one function and one priority take two
sentences, in the text's order. Where no two clauses share a symbol and a priority, each takes the
first sentence of its key (`findEqn`). What the list is worth is its `shapeB` against
`gammaPats c`. -/
def fnTextOf (c : Semantics) (us : List AxiomDecl) : List AxiomDecl := fnTextFrom (clauseKeys c) us

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c
kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed

/-- Γ's equations' patterns are the translations of their axioms. -/
theorem gammaPats_eq (c : Semantics) :
    gammaPats c = (fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  have hk : ∀ ss : List Kore.Sentence, (kernelItems ss).map (·.pat) =
      (ss.filterMap fun | .axiom a => some a | _ => none).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
    intro ss
    induction ss with
    | nil => rfl
    | cons s ss ih =>
      cases s <;> simp only [kernelItems, List.filterMap_cons, List.map_cons] at ih ⊢ <;> first | exact ih | rw [ih]
  unfold gammaPats fnItems fnAxioms
  rw [List.map_flatMap, List.map_flatMap]
  congr 1
  funext f
  exact hk _

/-- The pattern of Γ's item at the index of an axiom of `fnAxioms`. -/
theorem gammaPats_at {c : Semantics} {j : Nat} {a : Kore.Axiom} (h : (fnAxioms c)[j]? = some a) :
    (gammaPats c)[j]? = some (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  rw [gammaPats_eq, List.getElem?_map, h]; rfl

theorem gammaPats_withHooks (c : Semantics) (H : HookParams) : gammaPats (c.withHooks H) = gammaPats c := by
  unfold gammaPats; rw [fnItems_withHooks]

/-- The patterns of `T`, with definedness. -/
def Texts (T : List P) : Premises KoreAML.Sym :=
  fun φ => φ ∈ T ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x

/-- The parts of Γ that are no sentence's translation. -/
def Families (c : Semantics) : Premises KoreAML.Sym :=
  ΓSig c ∪ ΓCons c ∪ ΓDomains c ∪ ΓColls c ∪ ΓFallback c

/-- The premises of a derivation: the patterns of `T`, Γ's rule items, and the families. -/
def Pre (c : Semantics) (T : List P) : Premises KoreAML.Sym := Texts T ∪ ΓRules c ∪ Families c

variable {c : Semantics} {T : List P}

theorem mem_Γ_fns {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-- **Γ entails each member of `T`.** -/
theorem entailed (h : shapeB (gammaPats c) T = true) : ∀ t ∈ T, Γ c ⊧ t := by
  intro t ht M _ I hI
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ht
  obtain ⟨g, hg, hs⟩ := shape_left h hj
  refine (sameB_iff hs).mpr ?_
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hg)
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, hit, rfl⟩))

/-- **Each item of `fnItems c` is a consequence of the member of `T` at its index.** -/
theorem from_text (h : shapeB (gammaPats c) T = true) :
    ∀ (j : Nat) (it : Item), (fnItems c)[j]? = some it → ∃ t, T[j]? = some t ∧ (Texts [t] ⊧ it.pat) := by
  intro j it hj
  have hg : (gammaPats c)[j]? = some it.pat := by unfold gammaPats; rw [List.getElem?_map, hj]; rfl
  obtain ⟨t, ht, hs⟩ := shape_right h hg
  exact ⟨t, ht, fun {M} _ {I} hI => (sameB_iff hs).mp (hI _ (Or.inl (List.mem_singleton_self _)))⟩

/-- Every premise of Γ is a consequence of `Pre c T`. -/
theorem gamma_from (h : shapeB (gammaPats c) T = true) : ∀ φ, Γ c φ → Pre c T ⊧ φ := by
  intro φ hφ M _ I hI
  rcases hφ with ((((((h1 | h1) | h1) | h1) | h1) | h1) | h1)
  · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h1)))))
  · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
  · exact hI _ (Or.inr (Or.inl (Or.inl (Or.inr h1))))
  · exact hI _ (Or.inr (Or.inl (Or.inr h1)))
  · rcases h1 with ⟨it, hit, rfl⟩ | hx
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hit
      obtain ⟨t, ht, hent⟩ := from_text h j it hj
      refine hent (I := I) fun ψ hψ => ?_
      rcases hψ with hψ | hψ
      · rw [List.mem_singleton.mp hψ]
        exact hI _ (Or.inl (Or.inl (Or.inl (List.mem_of_getElem? ht))))
      · exact hI _ (Or.inl (Or.inl (Or.inr hψ)))
    · exact hI _ (Or.inl (Or.inl (Or.inr hx)))
  · exact hI _ (Or.inl (Or.inr h1))
  · exact hI _ (Or.inr (Or.inr h1))

/-- **`Pre c T` with the step's closure has a model where Γ with it has one.** -/
theorem pre_model (h : shapeB (gammaPats c) T = true) (hc : Consistent c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre c T ∪ Γstep c) := by
  obtain ⟨M, hM, I, hI⟩ := hc
  have hΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  refine ⟨M, hM, I, fun φ hφ => ?_⟩
  rcases hφ with ((h1 | h1) | h1) | h1
  · rcases h1 with ht | ⟨x, rfl⟩
    · exact entailed h φ ht hΓ
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
  · exact hΓ _ (Or.inl (Or.inr h1))
  · rcases h1 with (((h1 | h1) | h1) | h1) | h1
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h1))))
    · exact hΓ _ (Or.inr h1)
  · exact hI _ (Or.inr h1)

/-- The cut: what Γ entails, `Pre c T` entails. -/
theorem cut (h : shapeB (gammaPats c) T = true) {ψ : P} (hψ : Γ c ⊧ ψ) : Pre c T ⊧ ψ :=
  fun hT => hψ fun φ hφ => gamma_from h φ hφ hT

/-- The cut with the step's closure on both sides. -/
theorem cutStep (h : shapeB (gammaPats c) T = true) {ψ : P} (hψ : (Γ c ∪ Γstep c) ⊧ ψ) :
    (Pre c T ∪ Γstep c) ⊧ ψ :=
  fun hT => hψ fun φ hφ => by
    rcases hφ with hφ | hφ
    · exact gamma_from h φ hφ (fun χ hχ => hT χ (Or.inl hχ))
    · exact hT φ (Or.inr hφ)

/-! ## A clause under the negation of the clauses of a smaller priority -/

/-- An equation `\implies{R}(\and{_}(\not{_}(n), prem), concl)`, read as its parts. -/
def negParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .implies R (.and _ [.not _ n, prem]) concl => some (R, n, prem, concl)
  | _ => none

theorem negParts_eq {p : Kore.Pattern} {R : Kore.KSort} {n prem concl : Kore.Pattern}
    (h : negParts p = some (R, n, prem, concl)) :
    ∃ R' R'', p = .implies R (.and R' [.not R'' n, prem]) concl := by
  unfold negParts at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

/-- **Γ's item of an equation without the negated conjunct of its premise**: the axiom
`¬ n ∧ prem → concl` read as `prem → concl`, under the variable table and the guards of the axiom
itself (so the variables keep their indices). An axiom of another form is its own item. -/
noncomputable def minusNeg (a : Kore.Axiom) : P :=
  match negParts a.pattern with
  | some (R, _, prem, concl) =>
    let t := tableOf a.sortVars a.pattern
    conjList (((a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups).map (guardOf t)) ⇒
      (tr ⟨t, []⟩ (.implies R prem concl) ≡ inhOf (trSort t R))
  | none => (trAxiom [] [] ⟨0, "kernel", a⟩).pat

/-- **W1 for a narrowed equation**: in a model of definedness, the item without the negated
conjunct entails Γ's item (a premise conjoined gives a consequence). -/
theorem item_of_minusNeg {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    {a : Kore.Axiom} (h : I ⊧ᴵ minusNeg a) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  unfold minusNeg at h
  cases hq : negParts a.pattern with
  | none => rw [hq] at h; exact h
  | some q =>
    obtain ⟨R, n, prem, concl⟩ := q
    rw [hq] at h
    dsimp only at h
    obtain ⟨R', R'', hp⟩ := negParts_eq hq
    intro e m
    have h1 := h e m
    unfold trAxiom
    dsimp only
    rw [hp] at h1 ⊢
    rw [interpret_impl] at h1 ⊢
    intro hg
    have h2 := h1 hg
    rw [interp_equal hD] at h2 ⊢
    intro b
    have h3 := h2 b
    simp only [sortOf, tr, trAndList, interp_sImp, interp_sAnd] at h3 ⊢
    exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 hl.2⟩⟩

/-- **W1 from a sentence**: a pattern that is the item without its negated conjunct, up to a
renaming (`sameB`), entails Γ's item, in a model of definedness. -/
theorem item_of_sentence {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    {a : Kore.Axiom} {t : P} (hs : sameB (minusNeg a) t = true) (h : I ⊧ᴵ t) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat :=
  item_of_minusNeg hD ((sameB_iff hs).mp h)

/-- A model of `Texts T` is a model of definedness. -/
theorem defOK_texts {M : Type} {I : Interpretation KoreAML.Sym M} {T : List P} (hI : I ⊧ᴵP Texts T) : DefOK I :=
  defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)

/-! ## Values -/

/-- **A defined result is a theorem of Γ**, for a semantics with `HypSoundCore`: where `f` has the
value `v` at `vs`, Γ entails `f(vs) = v`. -/
theorem eval_some_sound (c : Semantics) (hpreTop : c.clausesPreTop = true) (h : HypSoundCore c)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn}
    {vs : List GroundTerm} {v : GroundTerm} (hE : Eval c f vs (some v)) (hfn : c.lookupFn f = some fn)
    (hvs : c.sortsOf vs = some fn.args) :
    Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ den c v) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro M _ I hI e m
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hok hfn hcl) hp' hb'
        (collPats_of_sorted hph' hp') hws hkeys hXkeys hRkey hX hR hσR hfail m
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  rw [eval_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph (fun fn hfn cl hcl _ => hex fn hfn cl hcl) hE hfn hvs e a]
  rfl

/-- `⟦f(vs)⟧`. -/
noncomputable def app (c : Semantics) (f : Sym) (vs : List GroundTerm) : P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- **A value `Eval` gives is derived from `Pre c T`.** -/
theorem value (h : shapeB (gammaPats c) T = true) (hc : c.coreOK = true) (hok : c.ok = true) {f : Sym} {fn : Fn}
    {vs : List GroundTerm} {v : GroundTerm} (hE : Eval c f vs (some v)) (hfn : c.lookupFn f = some fn)
    (hvs : c.sortsOf vs = some fn.args) : Pre c T ⊧ (app c f vs ≡ den c v) :=
  have hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok)
  cut h (eval_some_sound (hpreTop := hpreTop) c (hypSound_of_core hc) (Semantics.ok_clauseBinds hok) hE hfn hvs)

/-- **That `Eval` gives no value is derived from `Pre c T`.** -/
theorem noValue (h : shapeB (gammaPats c) T = true) (hc : c.coreOK = true) (hok : c.ok = true) {f : Sym} {fn : Fn}
    {vs : List GroundTerm} (hE : Eval c f vs none) (hfn : c.lookupFn f = some fn)
    (hvs : c.sortsOf vs = some fn.args) : Pre c T ⊧ (app c f vs ≡ ⊥) :=
  have hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok)
  cut h (eval_none_sound_core (hpreTop := hpreTop) c (hypSound_of_core hc) (Semantics.ok_clauseBinds hok) hE hfn hvs)

/-! ## Evaluation under every interpretation -/

/-- **A result the evaluator computes is `Eval`'s under every interpretation**, for a definition
without an open generator. -/
theorem eval_withHooks (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams) {f : Sym} {fn : Fn} {vs : List GroundTerm} {n : Nat}
    {r : Option GroundTerm} (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args)
    (h : Cert.evalFC c n f vs = some r) : Eval (c.withHooks H) f vs r :=
  have hokH : (c.withHooks H).ok = true := (Semantics.ok_withHooks c H).trans hok
  have hsrH : (c.withHooks H).srReady = true := (Semantics.srReady_withHooks c H).trans hsr
  have hmrH : (c.withHooks H).matchReady = true := (Semantics.matchReady_withHooks c H).trans hmr
  Exec.evalF_sound (sortCtx_of hokH hsrH (Exec.ovlCase_of hmrH)) (Exec.clauseCtx_of hokH)
    (Exec.matchCtx_of hmrH) n (Cert.evalFC_sound n (by rw [Cert.evalFC_withHooks c H hr]; exact h))
    (by rw [Semantics.lookupFn_withHooks]; exact hfn)
    (by rw [Semantics.sortsOf_withHooks _ _ hr]; exact hvs)

/-- **One result at each argument list, under every interpretation**, where the agreement decider
names no function and every clause's matches are fixed. -/
theorem fnDet_withHooks (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hcf : c.clausesFixed = true) (hag : c.agreeObligations = []) (H : HookParams) : FnDet (c.withHooks H) :=
  fnDet_of_coherent (Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    ((clausesFixed_withHooks c H).trans hcf) ((Semantics.agreeObligations_withHooks c H).trans hag))

open Det in
/-- **`FnDet` and `FnSolves` without the totality facts**: from `coreOK`, the held variables' facts,
and the termination, agreement and match-independence facts the deciders leave. No fact on a
`[total]` function's values is read. -/
theorem fnModel_noTotal (hpreTop : c.clausesPreTop = true) {ord : List Sym} (h : c.coreOK = true)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f)
    (h1 : ∀ f ∈ c.rankObligations ord ++ c.decObligationsL, Terminates c f)
    (h3 : ∀ f ∈ c.agreeObligationsI, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn)
    (h4 : ∀ p ∈ c.matchObligationsL, ∀ fn, c.lookupFn p.1 = some fn → ∀ cl, fn.clauses[p.2]? = some cl →
      MatchIndependent c cl) : FnDet c ∧ FnSolves c := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hterm := terminates_of_rankLN (hpreTop := hpreTop) hok hsr (Semantics.ovlCase_of_core h) ord hheld h1
  have hmc : Exec.MatchCtxO c := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls h⟩
  have hag := clausesAgree_of_IO hok hsr hmc h3
  have hmi := matchIndependentAll_of_L hok hmc h4
  have hco : CoherentAll c := coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp
  have hd := fnDet_of_coherent hco
  exact ⟨hd, Faithful.Model.fnSolves_of_total (hypSound_of_core h) hd
    (fun fn hfn vs hvs => hterm fn.label fn (lookupFn_of_core h hfn) vs hvs)
    fun fn hfn cl hcl hne vs σ hdec =>
      (hmi fn.label fn (lookupFn_of_core h hfn) cl hcl).2 hne fn.label fn vs σ (lookupFn_of_core h hfn) hcl hdec⟩

/-- `fnModel_noTotal` under an interpretation of the parameters, where the deciders name no
function for termination, agreement or match independence. -/
theorem fnModel_noTotal_withHooks (hpreTop : c.clausesPreTop = true) {ord : List Sym} (h : c.coreOK = true) (hrh : c.RightHeld)
    (hr : ∀ k ∈ c.params, k.raw = false) (h1 : c.rankObligations ord ++ c.decObligationsL = [])
    (h3 : c.agreeObligationsI = []) (h4 : c.matchObligationsL = []) (H : HookParams) :
    FnDet (c.withHooks H) ∧ FnSolves (c.withHooks H) :=
  fnModel_noTotal (hpreTop := hpreTop) (ord := ord) ((Semantics.coreOK_withHooks c H).trans h)
    (fun f _ => (Semantics.rightHeld_withHooks hrh H hr).heldOwed f)
    (fun f hf => by
      rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, h1] at hf
      exact absurd hf List.not_mem_nil)
    (fun f hf => by
      rw [Det.Semantics.agreeObligationsI_withHooks, h3] at hf; exact absurd hf List.not_mem_nil)
    (fun p hp => by
      rw [Det.Semantics.matchObligationsL_withHooks, h4] at hp; exact absurd hp List.not_mem_nil)

/-- **A function with no value at an argument list of its sorts is not `Total`**, where results
are unique. -/
theorem not_total_of_none (hd : FnDet c) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) (hE : Eval c f vs none) :
    ¬ Total c f := fun ht => by
  obtain ⟨v, hv⟩ := ht fn hfn vs hvs
  exact absurd (hd f vs _ _ hE hv) (by simp)

/-- `FnHyp` fails where a `[total]` function of the definition has no value at an argument list of
its sorts. -/
theorem not_fnHyp_of_none (hd : FnDet c) {fn : Fn} {vs : List GroundTerm} (hfn : fn ∈ c.fns)
    (ht : fn.total = true) (hvs : c.sortsOf vs = some fn.args) (hE : Eval c fn.label vs none) :
    ¬ FnHyp c := fun hf => by
  obtain ⟨v, hv⟩ := hf.2.1 fn hfn ht vs hvs
  exact absurd (hd _ vs _ _ hE hv) (by simp)

/-! ## Reading a number off the kernel -/

/-- A list of numbers below 1000 as one number: `1` followed by each member in three decimal
digits. -/
def enc (l : List Nat) : Nat := l.foldl (fun a n => a * 1000 + n) 1

open Lean Elab Command Meta in
/-- `#kernel_nat t`: prints the numeral the kernel reduces the closed term `t : Nat` to. For
reading a fact off a literal definition (the indices of its sentences, a count) before stating it;
the statement is then a theorem the kernel checks. -/
elab "#kernel_nat " t:term : command => liftTermElabM do
  let e ← Term.elabTerm t (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let r ← ofExceptKernelException (Lean.Kernel.whnf (← getEnv) {} e)
  logInfo m!"{r}"

end TiePair

end KCore
