/-
  The fixture e2-clause-rhs-empty-peer: `rule f() => g(Y:Empty) [unboundVariables(Y)]` beside
  `rule f() => a`, of one priority (`syntax Empty`, no production; `T ::= "a" | g(Empty)`,
  `T ::= f() [function]`). The text is `f2-examples/rhsemptypeer.kompile.kore`, the kompiled text of
  `test/constructs/fixtures/e2-clause-rhs-empty-peer` (equal to it after `kfix.stripped`); its
  sentences 209 (`f() = a`) and 210 (`f() = g(Y)`, Y free, so universal over Empty). Run from the
  package root: `lake env lean -j1 test/TieClauseRhsPeer.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - Function equations (`fnText`: `f`'s two sentences, 209 and 210, in the order of `f`'s clauses,
    then the sort predicates'): each of Γ's items is the translation of its sentence (`shape`), so
    Γ entails each (`fns_entailed`) and each item is a consequence of its sentence
    (`fns_from_text`).
  - No value has sort Empty (`no_E`), so the clause `f() => g(Y)` applies under no substitution,
    under every H (`clY_not_applies`). The owed facts of `f` hold for every H: `f` is held-named
    and has a result at its one argument list, `f()` being `a` by the clause `f() => a` (`held`);
    `f`'s equations agree and the clause over Empty is match independent, as it applies nowhere
    (`agree`, `matchY`). So `FnHyp` holds for every H (`fnHypH`, the held-named form), and Γ with
    the step's closure has a model (`consistent`), so has `Pre` (`pre_model`).
  - The expectation (C7 form (a), from sentences; `Pre` holds every equation of `f` as written):
    `f_is_a`, `f()` is `a`, from sentence 209 as written in a model of `Pre`.
  The text's own sorted theory, in which every sort has an element, has no model (`g(e)` against
  `a`, by no confusion); Γ states no element of Empty, and has one.
  The clause over Empty leaves Y open, so the definition reads a confined sort and its theory is
  `Γc = Γ ∪ Γcl`; the statements here are over Γ and `Pre`, and what they entail `Γc` entails.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieClauseRhsPeer

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rhsemptypeer.kompile.kore"
definition_of defn from "f2-examples/rhsemptypeer.kompile.kore"
user_axioms U from "f2-examples/rhsemptypeer.kompile.kore" module "E2-CLAUSE-RHS-EMPTY-PEER"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## What the reader reads -/

def fS : Sym := 388
def aS : Sym := 386
def gS : Sym := 387
def emptyS : Srt := 33

/-- The symbols and the sort the clauses name. -/
theorem names : c.symName fS = "Lblf" ∧ c.symName aS = "Lbla" ∧ c.symName gS = "Lblg" ∧
    c.sortName emptyS = "Empty" := by
  decide +kernel

/-- A rank of the user's functions: `f` alone. -/
def ord : List Sym := [388]

/-- The semantics is `coreOK`, `rightValued` fails and `f` is the one held-named function; no
function named for termination or totality, `f` for agreement, its clause 1 for match
independence, no rule and no clause owing a condition. -/
theorem named : c.coreOK = true ∧ c.rightValued = false ∧ c.heldObligations = [388] ∧
    c.rankObligations ord ++ c.decObligationsL = [] ∧ c.totalObligationsRP ord [] = [] ∧
    c.agreeObligationsI = [388] ∧ c.matchObligationsL = [(388, 1)] ∧ c.owedRules = [] ∧
    c.owedClauses = [] := by
  decide_cheap

theorem coreOK : c.coreOK = true := named.1
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem sortOfH (H : HookParams) : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H noRaw
theorem sortsOfH (H : HookParams) : (cH H).sortsOf = c.sortsOf := Semantics.sortsOf_withHooks c H noRaw

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: `f`'s two (209, `f() => a`, and
210, `f() => g(Y)`, as `f`'s clauses), then the sort predicates' (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := [U.ax209, U.ax210] ++ (TiePair.fnTextOf c U.all).drop 2

theorem fnText_index : fnText.map (·.index) = [209, 210, 230, 238, 237, 236, 235, 242, 241, 244, 243, 240, 239,
    217, 216, 229, 228, 225, 224, 227, 226, 232, 231, 234, 233, 221, 220, 223, 222, 246, 245, 219, 218] := by
  decide +kernel

/-- The translations of the text's sentences, in that order. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, pattern for pattern or with
one variable renamed (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun ad had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-! ## No value of Empty -/

/-- **No value has the sort `e`** when no constructor, overload, open generator or subsort ends
there, no literal is of it and it is no collection sort. -/
theorem noValue {c : Semantics} {e : Srt} (hctor : c.ctorSigs.all (·.result != e) = true)
    (hovl : c.ovls = []) (hraw : ∀ k ∈ c.params, k.raw = false)
    (hsub : c.subsorts.all (fun p => p.2 != e) = true) (hcoll : c.collOf e = none)
    (hcarr : c.lib.carriers.all (·.1 != e) = true)
    (hlit : (e != Srt.int && e != Srt.bool && e != Srt.kconfigVar && e != Srt.string && e != Srt.bytes &&
      e != Srt.float && !c.lib.tokenSorts.contains e && !c.lib.byteSorts.contains e) = true)
    (v : GroundTerm) : c.sortOf v ≠ some e := by
  intro h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hlit
  obtain ⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hk⟩, hs⟩, hy⟩, hf⟩, ht⟩, hbs⟩ := hlit
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk' : lookupSig c.ctorSigs f with
    | none =>
      have : c.lookupOvl f = none := by simp [Semantics.lookupOvl, hovl]
      rw [hk', this, c.lookupOpen_of_noRaw hraw f] at h; cases h
    | some k =>
      rw [hk'] at h
      simp only at h
      split at h
      · have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk')
        have := List.all_eq_true.mp hctor k hm
        rw [Option.some.inj h] at this
        simp at this
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp hsub _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp h
    have hcs := Lib.carrier_of_not _ hcarr
    cases lit with
    | int _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact hi hd
    | bool _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact hb hd
    | float _ _ _ => simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hd; exact hf hd.1
    | tok t =>
      simp only [dvOK, hcs, ht, hbs, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true,
        beq_iff_eq] at hd
      rcases hd with (hd | hd) | ⟨hd, -⟩
      · exact hk hd
      · exact hs hd
      · exact hy hd
  | map s' es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [hcoll] at hco; cases hco
  | set s' es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [hcoll] at hco; cases hco
  | list s' es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp h
    rw [hcoll] at hco; cases hco

/-- What `noValue` asks of Empty (33). -/
theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.ovls = [] ∧
    c.subsorts.all (fun p => p.2 != 33) = true ∧ c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

/-- **No value has sort Empty**, under every H. -/
theorem no_E (H : HookParams) (v : GroundTerm) : (cH H).sortOf v ≠ some emptyS := by
  rw [sortOfH]
  exact noValue empty.1 empty.2.1 noRaw empty.2.2.1 empty.2.2.2.1 empty.2.2.2.2.1 empty.2.2.2.2.2 v

/-! ## `f`, for every H -/

theorem sortsOf_nil {c : Semantics} {vs : List GroundTerm} (h : c.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [Semantics.sortsOf] at h; split at h <;> cases h

/-- The reader's `f` and its two clauses. -/
noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clA : Clause := fF.clauses[0]'(by decide +kernel)
noncomputable def clY : Clause := fF.clauses[1]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f() => a` and `f() => g(Y:Empty)`, of one priority, neither `aside`; `f` is not `[total]`. -/
theorem fF_shape : fF.label = 388 ∧ fF.args = [] ∧ fF.total = false ∧ fF.clauses.length = 2 ∧
    clA.vars = [] ∧ clA.pats.isEmpty = true ∧ clA.req.isNone = true ∧ clA.ens.isNone = true ∧
    clY.vars = [33] ∧ clY.leftVars = [] ∧ clA.prio = clY.prio ∧ c.isCtor 386 = true ∧
    clY.exs = [] := by
  decide +kernel

theorem clA_rhs : clA.rhs = .app 386 [] := by rfl
theorem clY_vars : clY.vars = [33] := fF_shape.2.2.2.2.2.2.2.2.1
theorem clA_pre : clA.pre = .top := by rfl

theorem clauses_eq : fF.clauses = [clA, clY] := by
  apply List.ext_getElem (by rw [fF_shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 2 := fF_shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl
  | 1, _ => rfl

theorem lookupF : c.lookupFn 388 = some fF := fF_shape.1 ▸ lookupFn_of_core coreOK fF_mem
theorem lookupFH (H : HookParams) : (cH H).lookupFn 388 = some fF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

theorem lookupFH_eq {H : HookParams} {fn : Fn} (h : (cH H).lookupFn 388 = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans (lookupFH H))

/-- `f() => g(Y:Empty)` applies under no substitution, under every H: Y is of Empty. -/
theorem clY_not_applies (H : HookParams) (σ : Subst) (vs : List GroundTerm) : ¬ clY.AppliesAt (cH H) σ vs := by
  rintro ⟨h, -⟩
  obtain ⟨v, -, hv⟩ := h 0 33 (by rw [clY_vars]; rfl)
  exact no_E H v hv

/-- **`f()` is `a`** under every H, by `f() => a`; the other clause is of the same priority. -/
theorem evalF (H : HookParams) : Eval (cH H) 388 [] (some (.ctor 386 [])) := by
  obtain ⟨-, -, -, -, hva, hpa, hra, hea, -, -, hprio, hctor⟩ := fF_shape
  refine Eval.clause (cl := clA) (σ := []) (lookupFH H) (by rw [clauses_eq]; exact List.mem_cons_self)
    (fun i s h => by rw [hva] at h; cases h) (by rw [List.isEmpty_iff.mp hpa]; exact .nil)
    (fun t h => by rw [h] at hra; cases hra) (by rw [clA_pre]; exact .top) (fun cl' h _ hlt => ?_)
    (by rfl) (by rw [clA_rhs]; exact EvalTerm.ctor (rs := []) hctor.1 .nil) (fun t h => by rw [h] at hea; cases hea)
    (Clause.holds_postTop (by rfl) _)
  rw [clauses_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact absurd hlt (Nat.lt_irrefl _)
  · rw [hprio] at hlt; exact absurd hlt (Nat.lt_irrefl _)

/-- **`f` terminates** under every H: its one argument list is `[]`, where `f()` is `a`. -/
theorem terminatesF (H : HookParams) : Terminates (cH H) 388 := fun fn hfn vs hvs => by
  have e := lookupFH_eq hfn
  subst e
  rw [fF_shape.2.1] at hvs
  rw [sortsOf_nil hvs]
  exact ⟨_, evalF H⟩

/-- **What is owed of `f`, by the second fact**, under every H: `f()` is `a`, and `f` is not
`[total]`. The first fact is false: Y is of Empty. -/
theorem held (H : HookParams) : ∀ f ∈ c.heldObligations, HeldOwed (cH H) f := by
  intro f hf fn hfn
  rw [named.2.2.1, List.mem_singleton] at hf
  subst hf
  have e := lookupFH_eq hfn
  subst e
  exact .inr ⟨terminatesF H, fun ht => by rw [fF_shape.2.2.1] at ht; cases ht⟩

/-- **`f`'s equations agree** under every H: `f() => g(Y)` applies nowhere. -/
theorem agree (H : HookParams) : ClausesAgree (cH H) fF := by
  intro cl cl' hp _
  have hp' : (cl, cl') = (clA, clY) := by rw [clauses_eq] at hp; simpa [pairs] using hp
  cases hp'
  exact ⟨fun vs _ σ' _ ha => absurd ha (clY_not_applies H σ' vs),
    fun vs σ _ ha => absurd ha (clY_not_applies H σ vs)⟩

/-- **`f() => g(Y)` is match independent** under every H: it applies nowhere. -/
theorem matchY (H : HookParams) : MatchIndependent (cH H) clY :=
  (matchIndependent_iff_noExs fF_shape.2.2.2.2.2.2.2.2.2.2.2.2).mpr fun vs σ _ ha =>
    absurd ha (clY_not_applies H σ vs)

/-- **The facts the deciders leave of `FnHyp`**, under every H: the two named ones. -/
theorem obl (H : HookParams) : FnObligations (cH H) ord [] := by
  obtain ⟨-, -, -, hterm, htot, hagr, hmat, howR, howC⟩ := named
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf fn hfn => ?_, fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, howC]; intro p hp; cases hp)⟩,
    openLaws_of_plain noRaw⟩
  · rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, hterm] at hf; cases hf
  · rw [Semantics.totalObligationsRP_withHooks, htot] at hf; cases hf
  · rw [Det.Semantics.agreeObligationsI_withHooks, hagr, List.mem_singleton] at hf
    subst hf
    have e := lookupFH_eq hfn
    subst e
    exact agree H
  · rw [Det.Semantics.matchObligationsL_withHooks, hmat, List.mem_singleton] at hp
    subst hp
    have e := lookupFH_eq hfn
    subst e
    rw [clauses_eq] at hcl
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchY H

/-- **`FnHyp` for every H**, from the held-named form: `coreOK`, the owed fact of `f` and the
deciders. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooksN coreOK H (held H) ParamsTotal.nil (obl H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectation (C7 form (a)) -/

/-- The premises of the derivation: the function sentences as written (both of `f`'s), Γ's rule
items, and the families (the parts of Γ no sentence states). -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

/-- Sentence 209 is Γ's axiom of the clause `f() => a` (no clause of a smaller priority, so no
exclusion), pattern for pattern or with one variable renamed. -/
theorem written_clA : TiePair.sameB (trAxiom [] [] ⟨0, "kernel", clauseAxiom c fF clA⟩).pat (trS U.ax209).pat = true := by
  decide +kernel

kernel_rfl clauseAxiom_withHooks : ∀ (H : HookParams), clauseAxiom (cH H) fF clA = clauseAxiom c fF clA

-- The clause's right side `a`, as the translation writes it, is the value `a`'s pattern.
kernel_rfl rhs_kore : ∀ (H : HookParams) (vs : List KoreAML.Var),
  Term.kore (cH H) vs clA.rhs = GroundTerm.kore (cH H) (.ctor 386 [])

theorem clA_plain : plainPats c clA.pats = true := by decide +kernel
theorem clA_sorts : sortsOfTerms c.patCtxAll clA.vars clA.pats = some fF.args := by decide +kernel

/-- **`f()` is `a`, derived from `Pre`**, for every H: sentence 209 (`f() = a`) as written, in a
model of `Pre`, which is one of Γ. -/
theorem f_is_a (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) fS [] ≡ den (cH H) (.ctor aS [])) := by
  intro M _ I hI
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ hφ => TiePair.gamma_from (shapeH H) φ hφ hI
  obtain ⟨hsok, hsr', hnn, -, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hD := defOK hΓ
  have h209 : I ⊧ᴵ (trS U.ax209).pat :=
    hI _ (Or.inl (Or.inl (Or.inl (by
      unfold textPats; exact List.mem_map.mpr ⟨U.ax209, by simp [fnText], rfl⟩))))
  have hax : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", clauseAxiom (cH H) fF clA⟩).pat := by
    rw [clauseAxiom_withHooks]; exact (TiePair.sameB_iff written_clA).mp h209
  obtain ⟨-, -, -, -, hva, hpa, hra, hea, -, -, -, hctor⟩ := fF_shape
  have hsortA : (cH H).sortOf (.ctor 386 []) = some fF.result := by rw [sortOfH]; decide +kernel
  have key := PrioTextWitness.clause_eq_ax hΓ hnn htr (lookupFH H) (cl := clA) hax (ws := [])
    (by rw [sortsOfH, fF_shape.2.1]; rfl) (σ' := []) (fun i s h => by rw [hva] at h; cases h)
    (by rw [List.isEmpty_iff.mp hpa]; exact .nil) clA_plain clA_sorts
    (fun i hi => absurd hi (by rw [hva]; exact Nat.not_lt_zero _)) (fun t h => by rw [h] at hra; cases hra)
    (fun i hi => by rw [clA_rhs] at hi; simp [varOccs, varOccsList] at hi) (fun t h => by rw [h] at hea; cases hea)
    (r := some (.ctor 386 [])) (fun v hv => by cases hv; exact hsortA) (fun _ _ _ t h => by rw [h] at hra; cases hra)
    (fun tbl e _ => right_iff hΓ hnn (lookupFn_spec (lookupFH H)).1 (fun v hv => by cases hv; exact hsortA)
      (fun m => by rw [rhs_kore]; rfl)
      (fun t h => by rw [h] at hea; cases hea))
  intro e m
  rw [KoreAML.interp_equal hD]
  intro x
  exact key e x

end KCore.TieClauseRhsPeer

#check @KCore.TieClauseRhsPeer.f_is_a
#print axioms KCore.TieClauseRhsPeer.shape
#print axioms KCore.TieClauseRhsPeer.fns_entailed
#print axioms KCore.TieClauseRhsPeer.fns_from_text
#print axioms KCore.TieClauseRhsPeer.fnHypH
#print axioms KCore.TieClauseRhsPeer.consistent
#print axioms KCore.TieClauseRhsPeer.pre_model
#print axioms KCore.TieClauseRhsPeer.f_is_a
