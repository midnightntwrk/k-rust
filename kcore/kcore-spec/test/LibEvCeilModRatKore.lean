/-
  rat.md:109 on a text where `/Rat` has no equation: sentence 124 of
  `f2-examples/e6-mod-rat-kore.kompile.kore` (kompile 7.1.337's text of the construct fixture
  e6-mod-rat-kore, which imports RAT-COMMON, RAT-KORE, RAT-SYMBOLIC and FLOAT-SYNTAX and not RAT),

      #Ceil(@R1 /Rat @R2) => {(@R2 =/=Rat 0) #Equals true} #And #Ceil(@R1) #And #Ceil(@R2)

  The text holds no equation of `/Rat` and does not declare it total, so `/Rat` is a parameter
  symbol of the reading that no hook interprets (`div_param`): Γ states its graph at values from the
  interpretation H, a value of Rat or ⊥ (`ΓDomains`, `Semantics.paramVal`). `=/=Rat` is a function
  of Γ with RAT-KORE's equation (rat.md:127), which gives `1 =/=Rat 0 = true` and
  `0 =/=Rat 0 = false` under every H (`ne_1_0`, `ne_0_0`).

  The sentence has two free set variables and no free element variable (`s124_text`), so it is
  asked at every set of values of Rat. For every H and in every model of Γ (cH H):
  - where H gives `1 /Rat 1` a value of Rat, the sentence fails at `@R1 = {1}`, `@R2 = {1, 0}`: the
    left side holds, and `@R2 =/=Rat 0` holds the element of `false`;
  - where H gives it none, the sentence fails at `@R1 = @R2 = {1}`: Γ states `1 /Rat 1` to be ⊥, so
    the left side does not hold, and the right side does.
  So the sentence fails at a valuation at values whatever H is (`s124_at`, the instance of
  `LibEv.ceilParam_refuted_at`), and Γ (cH H) with the sentence has no model (`s124_refuted`).

  Γ (cH H) has a model for every H (`consistent`, `gamma_model`), so this is no vacuous statement:
  the sentence is entailed at values under no H (`s124_not_at_values`, `s124_not_at_set_values`),
  and no H is a witness of the class parameter lemma for it (`s124_no_witness`: the negation of the
  statement a tie of the text states as `ParamLemmaWitnessAtValues` where it lists 124 in that
  class). The sentence is of the class set-variable lemma, of direction refuted, for every H.

  At sets of at most one value the sentence is a condition on H: it fails there under every H that
  gives `1 /Rat 1` no value (`s124_one_at`), `HookParams.none` among them (`s124_one_none`).

  `rat2float_param`: RAT-SYNTAX's `Rat2Float` (rat.md:78), which the text declares a function
  without `total` and gives no equation, is likewise a parameter symbol of the reading without
  `impl`, and a symbol of Γ (`hasSym`), though no rule and no function clause applies it
  (`rat2float_unapplied`).

  Axioms guarded. Run from kcore-spec: `lake env lean -j1 test/LibEvCeilModRatKore.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvCeilModRatKore

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-mod-rat-kore.kompile.kore"
definition_of defn from "f2-examples/e6-mod-rat-kore.kompile.kore"
user_axioms U from "f2-examples/e6-mod-rat-kore.kompile.kore" module "E6-MOD-RAT-KORE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

def divRat : Sym := 400
def neRat : Sym := 392
def rat2Float : Sym := 399
def rat : Srt := 32
def ri (n : Int) : GroundTerm := .inj Srt.int rat (int n)

theorem names : c.symName divRat = "Lbl'UndsSlsh'Rat'Unds'" ∧
    c.symName neRat = "Lbl'UndsEqlsSlshEqls'Rat'Unds'" ∧
    c.symName rat2Float = "LblRat2Float'LParUndsCommUndsCommUndsRParUnds'RAT-SYNTAX'Unds'Float'Unds'Rat'Unds'Int'Unds'Int" ∧
    c.sortName rat = "Rat" ∧ (Srt.int, rat) ∈ c.subsorts := by decide +kernel

/-! ## `/Rat` is a parameter symbol, `=/=Rat` a function with an equation -/

theorem div_isParam : (c.lookupParam divRat).isSome = true := by decide +kernel

/-- `/Rat` as the reading holds it. -/
noncomputable def kDiv : ParamSig := (c.lookupParam divRat).get div_isParam

theorem kDiv_lookup : c.lookupParam divRat = some kDiv := (Option.some_get div_isParam).symm

/-- **`/Rat` is a parameter symbol no hook interprets**, from Rat × Rat to Rat, and no function of
the semantics: the text gives it no equation. -/
theorem div_param : kDiv.impl = none ∧ kDiv.raw = false ∧ kDiv.sig.args = [rat, rat] ∧ kDiv.sig.result = rat ∧
    (c.lookupFn divRat).isNone = true := by decide +kernel

/-- The function numbered `f`, as `lookupFn` finds it. -/
noncomputable def fnOf (f : Sym) : Fn := (c.lookupFn f).getD ⟨0, [], 0, [], false⟩

theorem hfn (f : Sym) (h : (c.lookupFn f).isSome = true) : c.lookupFn f = some (fnOf f) := by
  unfold fnOf; cases hl : c.lookupFn f with
  | none => rw [hl] at h; cases h
  | some fn => rfl
theorem hfnH (H : HookParams) (f : Sym) (h : (c.lookupFn f).isSome = true) :
    (cH H).lookupFn f = some (fnOf f) := by rw [Semantics.lookupFn_withHooks]; exact hfn f h

/-- `=/=Rat` has one equation. -/
theorem ne_fn : (c.lookupFn neRat).isSome = true ∧ (fnOf neRat).clauses.length = 1 := by decide +kernel

/-- What `Cert.evalFC` computes is `Eval`'s under every H. -/
theorem eval_of {f : Sym} {vs : List GroundTerm} {k : Nat} {r : Option GroundTerm}
    (hf : (c.lookupFn f).isSome = true) (hvs : c.sortsOf vs = some (fnOf f).args)
    (h : Cert.evalFC c k f vs = some r) (H : HookParams) : Eval (cH H) f vs r :=
  TiePair.eval_withHooks hok hsr hmr noRaw H (hfn f hf) hvs h

theorem sorts_args (H : HookParams) (f : Sym) {vs : List GroundTerm} (h : c.sortsOf vs = some (fnOf f).args) :
    (cH H).sortsOf vs = some (fnOf f).args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact h

theorem sort_ri : c.sortOf (ri 0) = some rat ∧ c.sortOf (ri 1) = some rat := by decide +kernel
theorem sort_riH (H : HookParams) (n : Int) (hn : n = 0 ∨ n = 1) : (cH H).sortOf (ri n) = some rat := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; rcases hn with rfl | rfl
  · exact sort_ri.1
  · exact sort_ri.2

/-- `1 =/=Rat 0` is `true`, under every H. -/
theorem ne_1_0 (H : HookParams) : Eval (cH H) neRat [ri 1, ri 0] (some (bool true)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H
/-- `0 =/=Rat 0` is `false`, under every H. -/
theorem ne_0_0 (H : HookParams) : Eval (cH H) neRat [ri 0, ri 0] (some (bool false)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-! ## The sentence -/

/-- The names the sentence's pattern reads do not read the interpretation of the hooks. -/
theorem srt_wh (c' : Semantics) (H : HookParams) (s : Srt) : srtOf (c'.withHooks H) s = srtOf c' s := rfl
theorem sym_wh (c' : Semantics) (H : HookParams) (f : Sym) : (c'.withHooks H).symName f = c'.symName f := rfl
theorem kore_wh (c' : Semantics) (H : HookParams) :
    (ri 0).kore (c'.withHooks H) = (ri 0).kore c' ∧ (bool true).kore (c'.withHooks H) = (bool true).kore c' :=
  ⟨rfl, rfl⟩
theorem pat_wh (H : HookParams) : LibEv.ceilFnPat (cH H) rat divRat neRat "VarR1" "VarR2" (ri 0) =
    LibEv.ceilFnPat c rat divRat neRat "VarR1" "VarR2" (ri 0) := by
  simp only [LibEv.ceilFnPat, LibEv.ceilFnVar, symApp, srt_wh, sym_wh, kore_wh]
theorem freeOK_wh (H : HookParams) (ks : List VarKey) :
    LibEv.ceilFnFreeOK (cH H) rat ks = LibEv.ceilFnFreeOK c rat ks := by
  unfold LibEv.ceilFnFreeOK; rw [srt_wh]

/-- Axiom 124 is the sentence `LibEv.ceilFnPat` writes at `/Rat`, `=/=Rat` and `inj{Int,Rat}(0)`;
its free variables are the two set variables of Rat and the sort variables, none an element
variable; and its item is the same under the text's declarations. -/
theorem s124_text : U.ax124.ax.pattern = LibEv.ceilFnPat c rat divRat neRat "VarR1" "VarR2" (ri 0) ∧
    U.ax124.ax.sortVars = [Rv, LibEv.Q0v] ∧ (trS U.ax124).pat = (trAxiom [] [] U.ax124).pat ∧
    LibEv.ceilFnFreeOK c rat (freeOf [] (LibEv.ceilFnPat c rat divRat neRat "VarR1" "VarR2" (ri 0))) = true := by
  decide +kernel

/-- The sentence carries `simplification` and rat.md's `Source`. -/
theorem s124_lemma : AttrsAgree.has U.ax124.ax.attributes "simplification" = true ∧
    Parse.isKBuiltin U.ax124.ax.attributes = true := by decide +kernel

theorem sorts_1_1 (H : HookParams) : (cH H).sortsOf [ri 1, ri 1] = some kDiv.sig.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel

/-- **rat.md:109 is refuted at sets of values, for every H**: in every model of Γ (cH H) it fails
at `@R1 = {1}`, `@R2 = {1, 0}` where H gives `1 /Rat 1` a value of Rat, and at `@R1 = @R2 = {1}`
where H gives it none. -/
theorem s124_at (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax124.ax ∧ SetVarsAtValues (cH H) I e U.ax124.ax ∧
      ¬ (trS U.ax124).pat.interpret I e default := by
  rw [s124_text.2.2.1]
  exact LibEv.ceilParam_refuted_at (coreOKH H) (hokH H) rat divRat neRat "VarR1" "VarR2" (ri 0)
    (by show rat < nRegSorts + c.sortNames.length; decide +kernel)
    (by rw [pat_wh, freeOK_wh]; exact s124_text.2.2.2)
    (k := kDiv) kDiv_lookup div_param.2.2.2.1 (hfnH H neRat ne_fn.1) (ri 1) (ri 0)
    (sort_riH H 1 (.inr rfl)) (sort_riH H 0 (.inl rfl)) (sorts_1_1 H)
    (sorts_args H neRat (by decide +kernel)) (ne_1_0 H)
    (sorts_args H neRat (by decide +kernel)) (ne_0_0 H)
    U.ax124 (by rw [pat_wh]; exact s124_text.1) s124_text.2.1 hI

/-- **Γ (cH H) with the sentence has no model, for every H.** -/
theorem s124_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax124).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, -, hn⟩ := s124_at H hI
  exact hn (hax e default)

/-- **At sets of at most one value the sentence fails under an H that gives `1 /Rat 1` no value**:
in every model of Γ (cH H), at `@R1 = @R2 = {1}`. -/
theorem s124_one_at (H : HookParams) (hnone : (cH H).paramVal divRat [ri 1, ri 1] = none)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    ∃ e : Valuation M, AtValues (cH H) I e U.ax124.ax ∧ SetVarsAtValues (cH H) I e U.ax124.ax ∧
      SetVarsAtMostOne e U.ax124.ax ∧ ¬ (trS U.ax124).pat.interpret I e default := by
  rw [s124_text.2.2.1]
  exact LibEv.ceilParam_refuted_one (coreOKH H) (hokH H) rat divRat neRat "VarR1" "VarR2" (ri 0)
    (by show rat < nRegSorts + c.sortNames.length; decide +kernel)
    (by rw [pat_wh, freeOK_wh]; exact s124_text.2.2.2)
    (k := kDiv) kDiv_lookup (hfnH H neRat ne_fn.1) (ri 1)
    (sort_riH H 1 (.inr rfl)) (sorts_1_1 H)
    (sorts_args H neRat (by decide +kernel)) (ne_1_0 H) hnone
    U.ax124 (by rw [pat_wh]; exact s124_text.1) s124_text.2.1 hI

/-- `HookParams.none` gives `1 /Rat 1` no value. -/
theorem div_none : (cH HookParams.none).paramVal divRat [ri 1, ri 1] = none := by
  have hn : kDiv.sig.name = divRat := by decide +kernel
  have h := ParamSchema.paramVal_implNone c noRaw HookParams.none (k := kDiv) (by rw [hn]; exact kDiv_lookup)
    div_param.1 [ri 1, ri 1]
  rw [hn] at h
  rw [h]; rfl

/-- **Under `HookParams.none` the sentence fails at sets of one value.** -/
theorem s124_one_none {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH HookParams.none)) :
    ∃ e : Valuation M, AtValues (cH HookParams.none) I e U.ax124.ax ∧
      SetVarsAtValues (cH HookParams.none) I e U.ax124.ax ∧
      SetVarsAtMostOne e U.ax124.ax ∧ ¬ (trS U.ax124).pat.interpret I e default :=
  s124_one_at HookParams.none div_none hI

/-! ## Γ has a model for every H -/

/- The ten `[total]` functions of RAT-SYNTAX have no equation in the text, and no other obligation
is named: no termination fact, no held variable, no agreement and no match independence is owed.
So every function has one result at each argument list and evaluation solves the equations, and Γ
with the step's closure has a model for every H; the model reads no totality. -/

def callOrder : List Nat := [387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem held_none : c.heldObligations = [] := by decide +kernel

theorem consistent (H : HookParams) : Consistent (cH H) := by
  have h := coreOKH H
  have hnoEx : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))
  have hpreTop : (cH H).clausesPreTop = true := by simp only [Semantics.clausesPreTop_withHooks]; decide +kernel
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hheld : ∀ f ∈ (cH H).heldObligations, HeldOwed (cH H) f := by
    rw [Semantics.heldObligations_withHooks, held_none]; intro f hf; cases hf
  have hterm := terminates_of_rankLN hpreTop hnoEx hok hsr (Semantics.ovlCase_of_core h) callOrder hheld
    (fun g hg => by
      rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg
      cases hg)
  have hmc : Exec.MatchCtxO (cH H) := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls h⟩
  have hag := Det.clausesAgree_of_IO hok hnoEx hsr hmc (fun g hg => by
    rw [Det.Semantics.agreeObligationsI_withHooks _ H, agree_named] at hg; cases hg)
  have hmi := Det.matchIndependentAll_of_L hok hnoEx hmc (fun p hp => by
    rw [Det.Semantics.matchObligationsL_withHooks _ H, match_named] at hp; cases hp)
  have hco : CoherentAll (cH H) := coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp
  have hd := fnDet_of_coherent hco
  have hft : FnTerminates (cH H) := fun fn hfn vs hvs => hterm fn.label fn (lookupFn_of_core h hfn) vs hvs
  exact consistent_of (cH H) h hd
    (Faithful.Model.fnSolves_of_total (hypSound_of_core h) hd hft
      fun fn hfn cl hcl hne vs σ hdec =>
        (hmi fn.label fn (lookupFn_of_core h hfn) cl hcl).2 hne fn.label fn vs σ (lookupFn_of_core h hfn) hcl hdec)
    (Faithful.Model.clausePreDecided_of_terminates (hypSound_of_core h) hft)
    (clausePostDecided_of_top fun _ hfn _ hcl =>
      (Semantics.sortedOK_clauseEx (Semantics.coreOK_parts h).1 hfn hcl).2 (hnoEx _ hfn _ hcl))
    (openLaws_of_plain fun k hk => noRaw k hk)

/-- **Γ (cH H) has a model, for every H.** -/
theorem gamma_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) := by
  obtain ⟨M, inst, I, hI⟩ := consistent H
  exact ⟨M, inst, I, fun φ hφ => hI φ (Or.inl (Or.inl hφ))⟩

/-! ## The class: no H meets the sentence -/

/-- **The sentence is entailed at values under no H** (`EntailsAtValues` as it is defined: it has
no free element variable, so that asks it at every valuation of its set variables). -/
theorem s124_not_at_values (H : HookParams) : ¬ EntailsAtValues (cH H) U.ax124 (trS U.ax124).pat := by
  intro h
  obtain ⟨M, inst, I, hI⟩ := gamma_model H
  obtain ⟨e, hav, -, hn⟩ := s124_at H hI
  exact hn (h M inst I hI e hav default)

/-- **Nor at set values** (`EntailsAtSetValues`): the valuation at which it fails is at values. -/
theorem s124_not_at_set_values (H : HookParams) :
    ¬ EntailsAtSetValues (cH H) U.ax124 (trS U.ax124).pat := by
  intro h
  obtain ⟨M, inst, I, hI⟩ := gamma_model H
  obtain ⟨e, hav, hsv, hn⟩ := s124_at H hI
  exact hn (h M inst I hI e hav hsv default)

/-- **No H is a witness of the class parameter lemma for the sentence**: there is no H at which
`FnHyp` holds and the sentence holds at values. -/
theorem s124_no_witness :
    ¬ ∃ H : HookParams, FnHyp (cH H) ∧ ∀ ad ∈ [U.ax124], EntailsAtValues (cH H) ad (trS ad).pat := by
  rintro ⟨H, -, hall⟩
  exact s124_not_at_values H (hall _ (List.mem_singleton.mpr rfl))

/-- **Nor at sets of at most one value under `HookParams.none`** (`LibEv.SvAtMostOne`): there the
sentence is a condition on H. -/
theorem s124_not_one_none :
    ¬ LibEv.SvAtMostOne (cH HookParams.none) U.ax124 (trS U.ax124).pat := by
  intro h
  obtain ⟨M, inst, I, hI⟩ := gamma_model HookParams.none
  obtain ⟨e, hav, hsv, hone, hn⟩ := s124_one_none hI
  exact hn (h M inst I hI e hav hsv hone default)

/-! ## `Rat2Float` -/

/-- A symbol of Γ by its name in the text. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

/-- **`Rat2Float` is a parameter symbol of the reading no hook interprets, and a symbol of Γ**: the
text declares it a function, not total, and gives it no equation, as it does `/Rat`. -/
theorem rat2float_param : ((c.lookupParam rat2Float).map fun k => (k.impl.isNone, k.raw)) = some (true, false) ∧
    (c.lookupFn rat2Float).isNone = true ∧
    hasSym "LblRat2Float'LParUndsCommUndsCommUndsRParUnds'RAT-SYNTAX'Unds'Float'Unds'Rat'Unds'Int'Unds'Int" = true ∧
    hasSym "Lbl'UndsSlsh'Rat'Unds'" = true := by decide +kernel

/-- No rule and no function clause of the reading applies `Rat2Float` or `/Rat`: being a symbol of
Γ does not rest on a use. -/
theorem rat2float_unapplied :
    (c.rules.all fun r => [rat2Float, divRat].all fun f =>
      !((Term.heads r.lhs ++ Term.heads r.rhs ++ (r.req.map Term.heads).getD [] ++
        (r.ens.map Term.heads).getD []).contains f)) = true ∧
    (c.allFns.all fun fn => fn.clauses.all fun cl => [rat2Float, divRat].all fun f =>
      !((Term.headsList cl.pats ++ (cl.req.map Term.heads).getD [] ++ Term.heads cl.rhs ++
        (cl.ens.map Term.heads).getD []).contains f)) = true := by decide +kernel

end KCore.LibEvCeilModRatKore

#check @KCore.LibEvCeilModRatKore.div_param
#check @KCore.LibEvCeilModRatKore.s124_text
#check @KCore.LibEvCeilModRatKore.s124_at
#check @KCore.LibEvCeilModRatKore.s124_refuted
#check @KCore.LibEvCeilModRatKore.s124_one_at
#check @KCore.LibEvCeilModRatKore.s124_one_none
#check @KCore.LibEvCeilModRatKore.consistent
#check @KCore.LibEvCeilModRatKore.gamma_model
#check @KCore.LibEvCeilModRatKore.s124_not_at_values
#check @KCore.LibEvCeilModRatKore.s124_not_at_set_values
#check @KCore.LibEvCeilModRatKore.s124_no_witness
#check @KCore.LibEvCeilModRatKore.s124_not_one_none
#check @KCore.LibEvCeilModRatKore.rat2float_param
#check @KCore.LibEvCeilModRatKore.rat2float_unapplied
/-- info: 'KCore.LibEvCeilModRatKore.s124_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.s124_at
/-- info: 'KCore.LibEvCeilModRatKore.s124_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.s124_refuted
/-- info: 'KCore.LibEvCeilModRatKore.s124_one_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.s124_one_none
/-- info: 'KCore.LibEvCeilModRatKore.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.consistent
/-- info: 'KCore.LibEvCeilModRatKore.s124_not_at_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.s124_not_at_values
/-- info: 'KCore.LibEvCeilModRatKore.s124_not_at_set_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.s124_not_at_set_values
/-- info: 'KCore.LibEvCeilModRatKore.s124_no_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.s124_no_witness
/-- info: 'KCore.LibEvCeilModRatKore.s124_not_one_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.s124_not_one_none
/-- info: 'KCore.LibEvCeilModRatKore.rat2float_param' depends on axioms: [propext] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.rat2float_param
/-- info: 'KCore.LibEvCeilModRatKore.rat2float_unapplied' depends on axioms: [propext] -/
#guard_msgs in #print axioms KCore.LibEvCeilModRatKore.rat2float_unapplied
