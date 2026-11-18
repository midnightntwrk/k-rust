/-
  Guards of the reading notes (findings/REVIEW-RN-reading-notes.md §3): for each note whose
  justification is about a value `Γ` gives, the statement of that justification for every
  interpretation H of the points the text leaves open, never only at the parsed semantics (whose
  interpretation, `HookParams.none`, gives nothing). Run from the package root:
  `lake env lean test/Guards.lean`.

  - G0, "where every clause fails, no value": false since the rest is the interpretation's
    (`Eval.rest`, `Semantics.fnRest`); `g0_refuted` is its refutation. No reading note rests on it:
    the one that did (`ensuresAsRequires`) is replaced by `Clause.ens`.
  - G1, a function equation's `ensures` (`Clause.ens`, in place of `ensuresAsRequires`): where a
    clause decides and its `ensures` has a result other than `true`, the function has no value
    (`eval_noValue_of_ens_fails`, every semantics). On `f2-examples/ens.kompile.kore`, for every H:
    `half(-4)` has no value and `Γ` entails `half(-4) = ⊥` (`Ens.half_neg4_gamma`).
  - G2, the same beside an `[owise]` equation (in place of the refusal `ensuresPriority`):
    `f2-examples/ens-owise.kompile.kore`, for every H (`EnsOwise.half_neg4_gamma`).
  - G3, `projectionDomainAsClause`: krust's texts hold, for every sort X, the selector-domain axiom
    of its projection, `⌈project:X(K)⌉ = ∃V. K = kseq(inj{X,KItem}(V), dotk)`; K 7.1.337's kompile
    writes none (`starinit.kompile.kore` names `project:Int` in its declaration, one use and its
    one equation only). On `f2-examples/projapp.kore`, krust's text of a rule applying
    `project:Int`, the axiom is read as a clause of `project:Int` with the `ensures` `false`: for every H, `project:Int(K)` has
    no value at every K of sort K that is not an injected Int (`ProjK.projInt_none_off`) and `Γ`
    entails `project:Int(K) = ⊥` there (`ProjK.projInt_off_gamma`), `.K` among them
    (`ProjK.dotk_off`). On `starinit.kompile.kore` the text is silent at `.K`: its value there is
    the interpretation's (`Proj.projInt_dotk_open`), as the text allows.
  - G4, the selector-inverse lemma `⌈project:Int(K)⌉ → kseq(inj(project:Int(K)), dotk) = K`, a
    `simplification` axiom of krust's text (kompile's has none): for every H, where `project:Int(K)`
    has a value v, K is `kseq(inj{Int,KItem}(v), dotk)` (`ProjK.inverse_holds`, at the values `Eval`
    gives; its statement in `Γ`'s models is not proved here).
  - G5, `total`: under `RestTotal`, a function declared total is total wherever, at each argument
    list, every clause fails or the function has a value (`total_of_restTotal`).
  - G6, a parameter symbol that is no open generator and a function with no clause have one value
    under every interpretation (`fnRest_nil_eq_paramVal`, in every semantics;
    `fnRest_nil_eq_paramVal_everyH`, at `c.withHooks H` for every H).
  - G7, `setIdempotence`: `_Set_` at a common member is no silent point, and `hook` gives it no value
    (`setIdem_bot`); in every semantics and under every H, `Γ` holds `_Set_(S₁, S₂) = ⊥` at sets
    where `hook` gives the concatenation no value (`setIdem_gamma`; at `{1} {1}`, `setIdem_everyH`).
    The point is reached (`setIdem_reached`): were `_Set_` a key of `silentTable`, which
    `silentKey_fixed` forbids, its value at a common member would be the interpretation's.
  - `rest_undetermined`, the statement of what replaced G0: at an argument list where every clause
    of a function fails, `Γ` holds the graph of the function's rest (`gamma_rest`), so over all
    interpretations it entails neither that the function has no value there nor that it has a
    given one (`rest_undetermined`, every semantics `coreOK` accepts, from two interpretations,
    one giving no rest and one giving the value; `RestOpen.F0_undetermined`, a function with no
    clause at 0). With G1 it says where the text speaks (an `ensures` that is not `true`: ⊥ under
    every H) and where it does not (every clause fails: the interpretation's).
  - G8, `ruleRightDefined`: for every semantics and every rule with no existential variables and
    whose predicates `pre` and `post` are `\top`, so under every interpretation, the rule's axiom
    without the premise `⌈rhs ∧ ens⌉` (`UndefRhsWitness.textRuleK`, the text's rewrite with the
    competitors' negation of the priority reading), with the definedness axioms, entails the axiom
    `Γ` reads (`prioRuleK`): `ruleRightDefined_weaker`.
  - G9, `existsDropped`: a rewrite axiom `\rewrites{C}(L, \exists Z:s. R)` whose binder binds
    nothing, with the definedness axioms, entails the axiom without the binder,
    `\rewrites{C}(L, R)`, in every interpretation and with no premise on the sort s
    (`existsDropped_weaker`): where s has an element the two right sides are equal; where it has
    none the text's right side is empty and so is its next, so the text says the left side has no
    instance. The statement has five premises on the two sentences' translations, each decided by
    computation on given sentences: the binder does not renumber the variables of C, L and R
    (the two tables give them one index each: so where the binder's variable is declared after
    every variable of R, or is a variable of L), the guards of the free variables are the same,
    and the binder's index is not free in the translated R. That they follow from "Z does not
    occur in R" for every sentence needs the translation's invariance under renumbering, which
    no theorem states. Instance at a sort the instance's signature gives no constructor:
    `existsDropped_empty`, `c(X:Int) => \exists Z:Empty. d(X:Int)`.
  - The reader's devices (`orSplit`, `topAsVariable`, `existsAsVariable`, `andAsEnsures`,
    `bottomAsEnsures`, `orBottom`, `predicateAtBool`, `andAtBool`, `requiresOrSplit`), each on the
    kompiled text of its construct fixture (namespaces `DevOr` to `DevOrBot`): the steps, or the
    values, the law of the note gives, stated for every H about `c.withHooks H`. The checks that
    decide them on the data read no interpretation (`Cert.checkStep_withHooks`,
    `Cert.stuckCheck_sound`, `Cert.evalFC_withHooks`), which is what carries them to every H; a
    function has no value under every H only where a clause decides and its `ensures` is not `true`
    (`Eval.ensFails`), so `Γ` entails ⊥ there. Each has its companion, the semantics of the same
    text read without the device (the sentence not read, or read by the law the note rejects),
    where the result differs: under every H where no function is at the point, and at a named H
    where the other reading makes the point one where every clause fails (the interpretation's:
    `DevAndEns.andEns_asRequires_H7`, `DevOrBot.orBot_unread_H7`).
  - `reflectionAsOwn` (`DevRefl`, e6-configuration's text): for every H the value of
    `#configuration` is H's answer, kept where it is of sort K (`conf_value`, with G6); the point
    is reached: under `Hk` `go` steps to `wrap(.K)` (`go_step_Hk`), under `HookParams.none` it has
    no successor (test/Configuration.lean). That `Γ` over all H entails neither is not stated in
    `Γ`'s models here.
  - `keyFunctionAsRequires` (`DevKey`, `keyfn-partial`'s text): for every H `look(1)` steps to the
    entry of `k(1)`, `kf(1)` being `k(1)` by its equation (`key_steps`); the point is reached:
    `kf(2)` is the interpretation's, and under `Hk` `look(2)` steps to that entry (`look2_Hk`). The
    bridge between the text's rule, whose left side applies the function, and the read one is not
    stated: the kernel has no pattern applying a function.
  - `equationPriority` (`DevPrio`, on `Faithful.PrioTextWitness.c`, two equations of priorities 50
    and 60 that both apply): for every H a model of the theory with each equation under its own
    premise is a model of `Γ` (`prio_gamma_of_text`); the point is reached: that theory has no
    model, `Γ` has one (`PrioTextWitness.not_model_text`, `has_model`). For one semantics: the
    entailment for every semantics is not stated.
  - `owiseAsPriority` (`DevOwise`, `owise2`'s text): for every H the `[owise]` equations give the
    values where no other equation applies and do not override one that applies (`owise_values`);
    the point is reached: with the `[owise]` equations not read, `f(1, 5)` is the interpretation's
    (`owise_unread_H9`).
  - `tokKItem` (a sort below KItem that KItem's no-junk sentence does not list; the reading adds the
    subsort): for every semantics with `coreOK` and every H, a no-junk sentence without a non-open
    injection from a sort with a value, its generators injections from sorts apart from that one,
    has no model with `Γ (c.withHooks H)` (`Faithful.noJunk_omitted_refuted`, the shape of TieEns'
    `idem_refuted`). On hashsort's text (`#Tok`), test/TokKItem.lean: the sentence entails `Γ`'s
    item (`text_entails_item`), is refuted for every H (`tok_refuted`), and `Γ` has a model
    (`consistent`), so `Γ` does not entail it (`text_not_entailed`).
  - G4 for the inert constructor classes (`distinctCtors`, `injectivity`, `noJunk`), for every
    semantics with `coreOK` and every H: a constructor sentence the check `Faithful.tieConsB`
    accepts on the data is entailed by `Γ (c.withHooks H)` (`inertCons_everyH`; the check reads no
    interpretation), and `Γ (c.withHooks H)` entails the no-junk item of every constructor sort
    with a generator (`inertNoJunk_everyH`). The fixture sentences are ens's, in test/TieEns.lean
    (`cons_entailed`, `nojunk_items`, `nojunk_trivial_entailed`, `nojunk_kitem_entailed`), which
    this file cannot import.
  - G4 for `collectionLaw`, `parametricFunctional` and `vacuousLeft`, for every H, each the
    library's statement of the class (KcoreSpec/InertEv.lean) at `c.withHooks H`: the associativity
    and the two unit sentences of `_List_` are entailed at values (`inertListLaw_everyH`); the
    `functional` sentence of `ite` at a sort the definition has is entailed at values
    (`inertIteFunctional_everyH`: at the instance, the text's sentence being over a sort variable,
    which no value has for its sort); a rewrite axiom whose left side is empty is entailed
    (`inertVacuousLeft_everyH`). The fixture sentences are in test/InertEvFixtures.lean.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.Guards

open KCore ML Faithful

def int (n : Int) : GroundTerm := .dv Srt.int (.int n)

kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed
/-- The matcher and `evalFC` read no interpretation where no parameter is raw. -/
theorem clauseMatches_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (cl : Clause)
    (vs : List GroundTerm) : Exec.clauseMatches (c.withHooks H) cl vs = Exec.clauseMatches c cl vs :=
  Cert.clauseMatches_withHooks_hr c H hr cl vs
theorem evalFC_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (n : Nat) (f : Sym)
    (vs : List GroundTerm) : Cert.evalFC (c.withHooks H) n f vs = Cert.evalFC c n f vs :=
  Cert.evalFC_withHooks c H hr n f vs

/-- A function's result that `evalFC` computes on the data, which reads no interpretation, is its
result under every interpretation. -/
theorem eval_everyH {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args)
    {n : Nat} {r : Option GroundTerm} (h : Cert.evalFC c n f vs = some r) (H : HookParams) :
    Eval (c.withHooks H) f vs r := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  exact Exec.evalF_sound (sortCtx_of hok' hsr' (Exec.ovlCase_of hmr')) (Exec.clauseCtx_of hok') (Exec.matchCtx_of hmr') n
    (Cert.evalFC_sound n (by rw [evalFC_withHooks c H hr]; exact h)) (by rw [Semantics.lookupFn_withHooks]; exact hfn)
    (by rw [Semantics.sortsOf_withHooks c H hr]; exact hvs)

/-! ## G0: where every clause fails, the value is the interpretation's -/

namespace NoClause

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def F : Sym := nRegSyms + 100
def fnF : Fn := ⟨F, [Srt.int], Srt.int, [], false⟩

def nc : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fnF]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- The interpretation that gives `F` the value 0 everywhere. -/
def Hc : HookParams := ⟨fun f _ => if f = F then some (int 0) else none⟩

end NoClause

open NoClause in
/-- **G0 is false**: a function with no clause has the interpretation's value at every argument
list of its sorts. -/
theorem g0_refuted : ¬ ∀ (c : Semantics) (f : Sym) (fn : Fn) (vs : List GroundTerm), c.lookupFn f = some fn →
    (∀ cl ∈ fn.clauses, Fails c vs cl) → ¬ ∃ v, Eval c f vs (some v) := by
  intro h
  have hl : (nc.withHooks Hc).lookupFn F = some fnF := by rw [Semantics.lookupFn_withHooks]; rfl
  have hr : (nc.withHooks Hc).fnRest fnF [int 0] = some (int 0) := by decide +kernel
  have hE := Eval.rest (c := nc.withHooks Hc) (vs := [int 0]) hl (fun cl hcl => by simp [fnF] at hcl)
  rw [hr] at hE
  exact h _ F fnF [int 0] hl (fun cl hcl => by simp [fnF] at hcl) ⟨_, hE⟩

/-! ## G1: an `ensures` that is not `true` where its clause decides gives no value -/

/-- **G1**, in every semantics whose clauses of one priority are coherent: a clause without
existential variables that decides at `vs` (it applies, every clause of a smaller priority fails)
and whose `ensures` has a result other than `true` leaves its function without a value there. -/
theorem eval_noValue_of_ens_fails {c : Semantics} {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
    {σ : Subst} {e : Term} {r : Option GroundTerm} (hco : CoherentAll c)
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses) (hσ : c.WellSorted cl.vars σ)
    (hmatch : PatVals c σ cl.pats vs) (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (hex : cl.exs = []) (he : cl.ens = some e) (hev : EvalTerm c σ e r) (hr : r ≠ some (bool true)) :
    ¬ ∃ v, Eval c f vs (some v) := fun ⟨_, h⟩ =>
  nomatch Eval.functional hco h (.ensFails hfn hmem hσ hmatch hreq hpre hprio hex he hev hr)

/-- `Γ` entails `f(vs) = ⊥` where `f` has no value, for every interpretation, from `coreOK` on the
data (`coreOK` does not read the interpretation). -/
theorem gamma_bot_everyH {c : Semantics} (hcore : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) (H : HookParams)
    (hE : Eval (c.withHooks H) f vs none) :
    Γ (c.withHooks H) ⊧ (KoreAML.den (symApp (c.withHooks H) f (GroundTerm.koreList (c.withHooks H) vs)) ≡ ⊥) :=
  eval_none_sound_core (hpreTop := by decide +kernel) _ (hypSound_of_core ((Semantics.coreOK_withHooks c H).trans hcore)) hbc hE
    (by rw [Semantics.lookupFn_withHooks]; exact hfn) (by rw [Semantics.sortsOf_withHooks _ _ hr]; exact hvs)

namespace Ens

definition_of defn from "f2-examples/ens.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def half : Sym := 387

theorem half_named : c.symName half = "Lblhalf" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn half = some (c.fns[0]'(by decide +kernel)) := rfl
theorem coreOK : c.coreOK = true := by decide_cheap

theorem half_neg4_none (H : HookParams) : Eval (c.withHooks H) half [int (-4)] none :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

/-- **G1 on `ens`**: under every interpretation, `Γ` entails `half(-4) = ⊥`. -/
theorem half_neg4_gamma (H : HookParams) :
    Γ (c.withHooks H) ⊧
      (KoreAML.den (symApp (c.withHooks H) half (GroundTerm.koreList (c.withHooks H) [int (-4)])) ≡ ⊥) :=
  gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by decide +kernel) H (half_neg4_none H)

end Ens

/-! ## G2: the same beside an `[owise]` equation -/

namespace EnsOwise

definition_of defn from "f2-examples/ens-owise.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def half : Sym := 387

theorem half_named : c.symName half = "Lblhalf" := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn half = some (c.fns[0]'(by decide +kernel)) := rfl
theorem coreOK : c.coreOK = true := by decide_cheap

theorem half_neg4_none (H : HookParams) : Eval (c.withHooks H) half [int (-4)] none :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

/-- **G2 on `ens-owise`**: under every interpretation, `Γ` entails `half(-4) = ⊥`; the `[owise]`
equation does not give it 0. -/
theorem half_neg4_gamma (H : HookParams) :
    Γ (c.withHooks H) ⊧
      (KoreAML.den (symApp (c.withHooks H) half (GroundTerm.koreList (c.withHooks H) [int (-4)])) ≡ ⊥) :=
  gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by decide +kernel) H (half_neg4_none H)

end EnsOwise

/-! ## G3, G4: the projection's domain and its selector-inverse lemma -/

-- K 7.1.337's text: no selector-domain axiom, so `project:Int` is the one clause of its equation.
namespace Proj

definition_of defn from "f2-examples/starinit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def projInt : Sym := 416

theorem projInt_named : c.symName projInt = "Lblproject'Coln'Int" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[4]'(by decide +kernel)

theorem fn_label : fn.label = projInt := by decide +kernel

/-- `project:Int`'s one clause, its equation `project:Int(kseq(inj{Int,KItem}(V), dotk)) = V`. -/
theorem fn_clauses : fn.clauses =
    [⟨[Srt.int], [.app kseq [.inj Srt.int Srt.kitem (.var 0), .app dotk []]], none, .var 0, none, 50, false, [], .top, .top⟩] := rfl

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn projInt = some fn := rfl

/-- The interpretation that gives `project:Int(.K)` the value 0 and nothing else. -/
def H0 : HookParams := ⟨fun f vs => if f = projInt ∧ vs = [.ctor dotk []] then some (int 0) else none⟩

/-- `project:Int`'s one clause, `project:Int(kseq(inj{Int,KItem}(V), dotk)) = V`, does not match `.K`. -/
theorem fails_dotk (H : HookParams) : ∀ cl ∈ fn.clauses, Fails (c.withHooks H) [.ctor dotk []] cl := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  have hfnH : (c.withHooks H).lookupFn projInt = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
  have hnil : ∀ cl ∈ fn.clauses, Exec.clauseMatches c cl [.ctor dotk []] = [] := by decide +kernel
  have hd : ∀ cl ∈ fn.clauses, ∀ σ ∈ Exec.clauseMatches (c.withHooks H) cl [.ctor dotk []],
      Exec.clauseReq (c.withHooks H) 10 cl σ = some false := by
    intro cl hcl σ hσ
    rw [clauseMatches_withHooks c H (by decide +kernel), hnil cl hcl] at hσ
    cases hσ
  intro cl hcl
  have hmem : fn ∈ (c.withHooks H).allFns := (lookupFn_spec hfnH).1
  obtain ⟨L, hL, hclk⟩ := Exec.clauseCtx_of hok' fn hmem
  obtain ⟨hpt, hmf, hlc, hreq, -⟩ := hclk cl hcl
  exact Exec.fails_of_false (Exec.matchCtx_of hmr') (n := 10) (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)
    hpt hmf hlc hreq
    (fun σ t r h hσ ht => Exec.evalT_sound (sortCtx_of hok' hsr' (Exec.ovlCase_of hmr')) (Exec.clauseCtx_of hok')
      (Exec.matchCtx_of hmr') 10 h hL hσ ht)
    (hd cl hcl)

/-- **The text is silent at `.K`**: the one equation does not apply there and no sentence speaks of
`project:Int(.K)`, so its value is the interpretation's rest: 0 under `H0`, none under
`HookParams.none`. -/
theorem projInt_dotk_open : Eval (c.withHooks H0) projInt [.ctor dotk []] (some (int 0)) ∧
    Eval (c.withHooks HookParams.none) projInt [.ctor dotk []] none := by
  have hl : ∀ H, (c.withHooks H).lookupFn projInt = some fn := fun H => by
    rw [Semantics.lookupFn_withHooks]; exact hfn
  have h0 : (c.withHooks H0).fnRest fn [.ctor dotk []] = some (int 0) := by decide +kernel
  have h1 : (c.withHooks HookParams.none).fnRest fn [.ctor dotk []] = none := by decide +kernel
  have e0 := Eval.rest (hl H0) (fails_dotk H0)
  have e1 := Eval.rest (hl HookParams.none) (fails_dotk HookParams.none)
  rw [h0] at e0; rw [h1] at e1
  exact ⟨e0, e1⟩

end Proj

-- krust's text of `projapp.k`, whose rule applies `project:Int`: it holds `project:Int`'s
-- selector-domain axiom (`\implies{R}(
-- \top{R}(), \equals{R,R}(\ceil{SortInt{},R}(Lblproject'Coln'Int{}(SelectorInput:SortK{})),
-- \exists{R}(VarK:SortInt{}, \equals{SortK{},R}(SelectorInput:SortK{}, kseq{}(inj{SortInt{},
-- SortKItem{}}(VarK:SortInt{}), dotk{}())))))`) and its selector-inverse lemma.
namespace ProjK

definition_of defn from "f2-examples/projapp.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def projInt : Sym := 387

theorem projInt_named : c.symName projInt = "Lblproject'Coln'Int" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem fn_label : fn.label = projInt := by decide +kernel

/-- The equation's clause and the clause read from the selector-domain axiom. -/
def eqnCl : Clause := ⟨[Srt.int], [.app kseq [.inj Srt.int Srt.kitem (.var 0), .app dotk []]], none, .var 0, none, 50, false, [], .top, .top⟩
def domCl : Clause := ⟨[Srt.k], [.var 0], none, .app projInt [.var 0], some (.dv Srt.bool (.bool false)), 200, false, [], .top, .top⟩

theorem fn_clauses : fn.clauses = [eqnCl, domCl] := rfl

private theorem hfn : c.lookupFn projInt = some fn := rfl
theorem coreOK : c.coreOK = true := by decide_cheap

kernel_rfl isCtor_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).isCtor = c.isCtor

theorem kseq_ctor : c.isCtor kseq = true := by decide +kernel
theorem dotk_ctor : c.isCtor dotk = true := by decide +kernel

/-- A value the equation's pattern matches is an injected Int in `kseq(…, dotk)`. -/
theorem eqn_match {H : HookParams} {σ : Subst} {K : GroundTerm}
    (h : PatVals (c.withHooks H) σ [.app kseq [.inj Srt.int Srt.kitem (.var 0), .app dotk []]] [K]) :
    ∃ w, σ.lookup 0 = some w ∧ K = .ctor kseq [injNormal Srt.int Srt.kitem w, .ctor dotk []] := by
  have hk := kseq_ctor; have hd := dotk_ctor
  rw [← isCtor_withHooks c H] at hk hd
  cases h with
  | cons h _ =>
    cases h with
    | ctor _ hs =>
      cases hs with
      | cons h1 hs =>
        cases hs with
        | cons h2 hs =>
          cases hs
          cases h1 with
          | inj h1 =>
            cases h1 with
            | var hw =>
              cases h2 with
              | ctor _ hn => cases hn; exact ⟨_, hw, rfl⟩
              | hook hp => exact absurd hp (by decide)
              | coll hc => rw [hd] at hc; cases hc
              | ovl hc => rw [hd] at hc; cases hc
    | hook hp => exact absurd hp (by decide)
    | coll hc => rw [hk] at hc; cases hc
    | ovl hc => rw [hk] at hc; cases hc

/-- **G3 on krust's text**: for every H, `project:Int(K)` has no value at every K of sort K that is
not an injected Int in `kseq(…, dotk)`: the equation fails there, and the clause read from the
selector-domain axiom decides with its `ensures` false. -/
theorem projInt_none_off (H : HookParams) (K : GroundTerm) (hK : c.sortOf K = some Srt.k)
    (hoff : ∀ v, K ≠ .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []]) :
    Eval (c.withHooks H) projInt [K] none := by
  have hfnH : (c.withHooks H).lookupFn projInt = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
  refine Eval.ensFails (cl := domCl) (σ := [(0, K)]) hfnH (by rw [fn_clauses]; simp) ?_ ?_
    (fun t ht => nomatch ht) .top ?_ rfl rfl .dv (by decide)
  · intro i s hs
    cases i with
    | zero => cases hs; exact ⟨K, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact hK⟩
    | succ i => simp [domCl] at hs
  · exact .cons (.var rfl) .nil
  · intro cl' hcl' _ hlt
    rw [fn_clauses] at hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · exact .intro fun σ _ hpv => by
        obtain ⟨w, -, rfl⟩ := eqn_match hpv
        exact absurd rfl (hoff w)
    · exact absurd hlt (by decide)

/-- `.K` is no injected Int. -/
theorem dotk_off : ∀ v, GroundTerm.ctor dotk [] ≠ .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []] :=
  fun v h => by cases h

/-- **G3 in `Γ`**: for every H, `Γ` entails `project:Int(K) = ⊥` at every such K. -/
theorem projInt_off_gamma (H : HookParams) (K : GroundTerm) (hK : c.sortOf K = some Srt.k)
    (hoff : ∀ v, K ≠ .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []]) :
    Γ (c.withHooks H) ⊧
      (KoreAML.den (symApp (c.withHooks H) projInt (GroundTerm.koreList (c.withHooks H) [K])) ≡ ⊥) :=
  gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by
    have ha : fn.args = [Srt.k] := by decide +kernel
    rw [ha]; exact OvlLaws.sortsOf_cons_iff.mpr ⟨hK, sortsOf_nil⟩) H (projInt_none_off H K hK hoff)

/-- **G4 on krust's text**: for every H, where `project:Int(K)` has a value v, K is
`kseq(inj{Int,KItem}(v), dotk)`, the selector-inverse lemma's statement at `Eval`'s values. -/
theorem inverse_holds (H : HookParams) (K v : GroundTerm) (hK : c.sortOf K = some Srt.k)
    (hE : Eval (c.withHooks H) projInt [K] (some v)) :
    K = .ctor kseq [injNormal Srt.int Srt.kitem v, .ctor dotk []] := by
  have hfnH : (c.withHooks H).lookupFn projInt = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
  generalize hr : (some v : Option GroundTerm) = r at hE
  cases hE with
  | clause hf hmem _ hmatch _ _ _ _ hrhs hens _ =>
    rw [hfnH] at hf; cases hf
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · obtain ⟨w, hw, rfl⟩ := eqn_match hmatch
      change EvalTerm _ _ (.var 0) _ at hrhs
      cases hrhs
      rw [hw] at hr; cases hr; rfl
    · have := hens _ rfl
      cases this
  | rest hf hnone =>
    rw [hfnH] at hf; cases hf
    cases hnone domCl (by rw [fn_clauses]; simp) with
    | intro h =>
      cases h [(0, K)] (fun i _ s hs => by
          cases i with
          | zero => cases hs; exact ⟨K, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact hK⟩
          | succ i => simp [domCl] at hs)
        (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre h => exact absurd (Holds.top_eq h) (by simp)
  | ensFails => cases hr
  | clauseEx hf hmem _ _ _ _ _ hne =>
    rw [hfnH] at hf; cases hf
    rw [fn_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> exact absurd rfl hne
  | exNone => cases hr

end ProjK

/-! ## G5: a function declared total, under `RestTotal` -/

/-- **G5**: under an interpretation that gives every function declared total a value where its
clauses give none (`RestTotal`), a function declared total is total wherever, at each argument list
of its sorts, every clause fails or it has a value. -/
theorem total_of_restTotal {c : Semantics} {H : HookParams} (h : RestTotal c H) {fn : Fn} (hfn : fn ∈ c.fns)
    (ht : fn.total = true) (hlook : c.lookupFn fn.label = some fn)
    (hcl : ∀ vs, c.sortsOf vs = some fn.args → (∀ cl ∈ fn.clauses, Fails (c.withHooks H) vs cl) ∨
      ∃ v, Eval (c.withHooks H) fn.label vs (some v)) (hr : ∀ k ∈ c.params, k.raw = false) :
    Total (c.withHooks H) fn.label := by
  intro fn' hlook' vs hvs
  rw [Semantics.lookupFn_withHooks, hlook] at hlook'
  cases hlook'
  rw [Semantics.sortsOf_withHooks c H hr] at hvs
  rcases hcl vs hvs with hnone | hv
  · exact eval_rest_of_restTotal h hfn ht hlook hvs hnone hr
  · exact hv

/-! ## G6: a parameter symbol and a function with no clause -/

/-- **G6**: a function with no clause and a parameter symbol of its signature with no registry
hook, no open generator, have one value at every argument list of its sorts, under every
interpretation: both are the interpretation's, kept where it has the result sort. (An open
generator's value where the interpretation gives none is its raw application, `paramVal`.) -/
theorem fnRest_nil_eq_paramVal (c : Semantics) (fn : Fn) (k : ParamSig) (hn : k.sig.name = fn.label)
    (ha : k.sig.args = fn.args) (hr : k.sig.result = fn.result) (hi : k.impl = none) (hraw : k.raw = false)
    (hk : c.lookupParam fn.label = some k) (vs : List GroundTerm) (hvs : c.sortsOf vs = some fn.args) :
    c.fnRest fn vs = c.paramVal fn.label vs := by
  unfold Semantics.fnRest Semantics.paramVal
  rw [hk]
  simp only [hi, hraw, Bool.false_eq_true, ↓reduceIte]
  cases hH : c.hooks.app fn.label vs with
  | none => rfl
  | some v => simp [Option.filter, hvs, hr, hn]

/-- **G6, for every interpretation**: under each H, a function with no clause and a parameter symbol
of its signature (no registry hook, no open generator) have one value at every argument list of
its sorts, H's where it has the result sort. -/
theorem fnRest_nil_eq_paramVal_everyH (c : Semantics) (H : HookParams) (fn : Fn) (k : ParamSig)
    (hn : k.sig.name = fn.label) (ha : k.sig.args = fn.args) (hr : k.sig.result = fn.result) (hi : k.impl = none)
    (hraw : k.raw = false) (hk : c.lookupParam fn.label = some k) (vs : List GroundTerm)
    (hvs : (c.withHooks H).sortsOf vs = some fn.args) :
    (c.withHooks H).fnRest fn vs = (c.withHooks H).paramVal fn.label vs :=
  fnRest_nil_eq_paramVal (c.withHooks H) fn k hn ha hr hi hraw hk vs hvs

/-! ## G7: `_Set_` at a common member -/

/-- **G7**: `_Set_` applied to two sets with a member in common is no silent point, and `hook` gives
it no value there, so `Γ` states ⊥ at it under every interpretation (`silentKey_fixed`). -/
theorem setIdem_bot :
    silent setConcat [.set Srt.set [int 1], .set Srt.set [int 1]] = false ∧
    hook setConcat [.set Srt.set [int 1], .set Srt.set [int 1]] = some none := by decide +kernel

/-! ## `rest_undetermined`: where every clause fails, `Γ` states the interpretation's value -/

namespace RestOpen
/-- A semantics with the configuration `<k> K </k>`, the generated counter and one function
`F : Int → Int` with no clause, not declared total. -/
def F : Sym := nRegSyms + 4
def fnF : Fn := ⟨F, [Srt.int], Srt.int, [], false⟩
def nc : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "LblF"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
    ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
      ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
    fns := [fnF]
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := [] }
def Hc : HookParams := ⟨fun f _ => if f = F then some (int 0) else none⟩
end RestOpen

/-- A function's application to values, as `Γ` writes it. -/
abbrev fnApp (c : Semantics) (f : Sym) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- At values where every clause of a function fails, `Γ` holds the graph of its rest. -/
theorem gamma_rest {c : Semantics} {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some fn.args) (hfail : ∀ cl ∈ fn.clauses, Fails c vs cl) :
    Γ c (fnApp c f vs ≡ (match c.fnRest fn vs with
      | some v => den c v
      | none => ⊥)) := by
  obtain ⟨hmem, hl⟩ := lookupFn_spec hfn
  subst hl
  exact Or.inr (Or.inr ⟨fn, vs, hmem, hvs, hfail, rfl⟩)

/-- **`rest_undetermined`: `Γ` does not determine a function where every clause fails.** At an
argument list where every clause of `f` fails under H₀ and under Hv, H₀ giving no rest and Hv the
rest `v`: over all interpretations `Γ` entails neither that `f(vs)` has no value nor that it is `v`.
Under H₀ it is ⊥ in every model, under Hv it is `v` in every model, and both theories have models
(`sound_hyp`). -/
theorem rest_undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args)
    {v : GroundTerm} (hv : c.sortOf v = some fn.result) {H₀ Hv : HookParams}
    (hfail₀ : ∀ cl ∈ fn.clauses, Fails (c.withHooks H₀) vs cl)
    (hfailv : ∀ cl ∈ fn.clauses, Fails (c.withHooks Hv) vs cl)
    (h0 : (c.withHooks H₀).fnRest fn vs = none) (h1 : (c.withHooks Hv).fnRest fn vs = some v)
    (hfn₀ : FnHyp (c.withHooks H₀)) (hfnv : FnHyp (c.withHooks Hv)) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (fnApp (c.withHooks H) f vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (fnApp (c.withHooks H) f vs ≡ den (c.withHooks H) v)) := by
  have hl : ∀ H, (c.withHooks H).lookupFn f = some fn := fun H => by rw [Semantics.lookupFn_withHooks]; exact hfn
  have hs : ∀ H, (c.withHooks H).sortsOf vs = some fn.args := fun H => by
    rw [Semantics.sortsOf_withHooks c H hr]; exact hvs
  constructor
  · intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks Hv) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks Hv) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_rest (hl Hv) (hs Hv) hfailv)
    rw [h1] at hfb
    have hbot := hall Hv hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks Hv)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have e1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have e2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((e2.mp (e1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks H₀) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks H₀) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_rest (hl H₀) (hs H₀) hfail₀)
    rw [h0] at hfb
    have hval := hall H₀ hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks H₀)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have e1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have e2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (e1.mp (e2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

namespace RestOpen

theorem nc_coreOK : nc.coreOK = true := by decide_cheap
theorem nc_noRaw : ∀ k ∈ nc.params, k.raw = false := by decide +kernel

/-- `F` has no clause, so `FnHyp` holds under every interpretation: `F`'s result everywhere is its
rest, and it is not declared total. -/
theorem nc_fnHyp (H : HookParams) : FnHyp (nc.withHooks H) := by
  have hlook : (nc.withHooks H).lookupFn fnF.label = some fnF := by rw [Semantics.lookupFn_withHooks]; rfl
  have hp : (nc.withHooks H).plain = true := (Semantics.plain_withHooks nc H).trans (by decide +kernel)
  have hfns : (nc.withHooks H).fns = [fnF] := rfl
  refine ⟨fun fn hfn vs _ => ?_, fun fn hfn ht => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_,
    openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts hp).1 r hr))
      (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts hp).2.1 fn hfn cl hcl)),
    openLaws_of_plain (Semantics.plain_parts hp).2.2⟩
  · rw [hfns] at hfn; rw [List.mem_singleton.mp hfn]
    exact ⟨_, .rest hlook fun cl hcl => by simp [fnF] at hcl⟩
  · rw [hfns] at hfn; rw [List.mem_singleton.mp hfn] at ht; cases ht
  · rw [hfns] at hfn; rw [List.mem_singleton.mp hfn]
    intro cl cl' h
    simp [fnF, pairs] at h
  · rw [hfns] at hfn; rw [List.mem_singleton.mp hfn] at hcl
    simp [fnF] at hcl

/-- **`rest_undetermined` at `F(0)`**: `F` has no clause, so over all interpretations `Γ` entails
neither `F(0) = ⊥` (under `Hc` it is 0) nor `F(0) = 0` (under `HookParams.none` it is ⊥). -/
theorem F0_undetermined :
    ¬ (∀ H : HookParams, Γ (nc.withHooks H) ⊧ (fnApp (nc.withHooks H) F [int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (nc.withHooks H) ⊧ (fnApp (nc.withHooks H) F [int 0] ≡ den (nc.withHooks H) (int 0))) :=
  rest_undetermined nc nc_coreOK nc_noRaw (f := F) (fn := fnF) rfl (by decide +kernel) (v := int 0) (by decide +kernel)
    (H₀ := HookParams.none) (Hv := Hc) (fun cl hcl => by simp [fnF] at hcl) (fun cl hcl => by simp [fnF] at hcl)
    (by decide +kernel) (by decide +kernel) (nc_fnHyp _) (nc_fnHyp _)

end RestOpen

/-! ## G7, for every interpretation -/

def ki (n : Int) : GroundTerm := .inj Srt.int Srt.kitem (int n)
def set1 : GroundTerm := .set Srt.set [ki 1]

/-- `_Set_`'s signature in the registry. -/
def setConcatSig : CtorSig := (lookupSig hookSigs setConcat).getD default

theorem setConcatSig_ok : lookupSig hookSigs setConcat = some setConcatSig ∧ setConcatSig.name = setConcat ∧
    setConcatSig.args = [Srt.set, Srt.set] := by decide +kernel

/-- `_Set_` is no key of `silentTable`: it has no silent point. -/
theorem setConcat_not_silent (vs : List GroundTerm) : silent setConcat vs = false := by
  cases h : silent setConcat vs with
  | false => rfl
  | true => exact absurd (silentKey_of_silent h) (by decide +kernel)

/-- **G7, for every interpretation**: in every semantics and under every H, `Γ` holds
`_Set_(S₁, S₂) = ⊥` at sets where `hook` gives the concatenation no value (a member in common). -/
theorem setIdem_gamma (c : Semantics) (H : HookParams) {vs : List GroundTerm}
    (hvs : (c.withHooks H).sortsOf vs = some [Srt.set, Srt.set]) (hh : hook setConcat vs = some none) :
    Γ (c.withHooks H) (fnApp (c.withHooks H) setConcat vs ≡ ⊥) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨setConcatSig, vs, none, (lookupSig_spec setConcatSig_ok.1).1,
    by rw [setConcatSig_ok.2.2]; exact hvs, hh, fun _ => setConcat_not_silent vs, rfl⟩)))))

open RestOpen in
/-- **G7 at `{1} {1}`**, on `RestOpen.nc`: under every interpretation `Γ` holds `_Set_({1}, {1}) = ⊥`. -/
theorem setIdem_everyH (H : HookParams) :
    Γ (nc.withHooks H) (fnApp (nc.withHooks H) setConcat [set1, set1] ≡ ⊥) :=
  setIdem_gamma nc H (by rw [Semantics.sortsOf_withHooks nc H nc_noRaw]; decide +kernel) (by decide +kernel)

/-- `silent` and `hookRes` over a table `T` in `silentTable`'s place. -/
def silentWith (T : List (Sym × (List GroundTerm → Bool))) (f : Sym) (vs : List GroundTerm) : Bool :=
  match T.find? (·.1 == f) with
  | some (_, p) => p vs
  | none => false
def hookResWith (T : List (Sym × (List GroundTerm → Bool))) (c : Semantics) (f : Sym)
    (vs : List GroundTerm) : Option (Option GroundTerm) :=
  if silentWith T f vs then (hook f vs).map fun r => r.or (c.fallback f vs) else hook f vs
theorem hookResWith_table (c : Semantics) (f : Sym) (vs : List GroundTerm) :
    c.hookRes f vs = hookResWith silentTable c f vs := rfl

/-- The interpretation that answers the empty set everywhere. -/
def Hempty : HookParams := ⟨fun _ _ => some (.set Srt.set [])⟩

open RestOpen in
/-- **The point is reached**: were `_Set_` a key of `silentTable` at a common member, its value
there would be the interpretation's: the empty set under `Hempty`, where `hookRes` gives none. -/
theorem setIdem_reached :
    hookResWith ((setConcat, fun _ => true) :: silentTable) (nc.withHooks Hempty) setConcat [set1, set1] =
      some (some (.set Srt.set [])) ∧
    (nc.withHooks Hempty).hookRes setConcat [set1, set1] = some none := by decide +kernel

/-! ## G8: `ruleRightDefined`, the text's rule axiom entails the read one -/

section RightDefined


theorem eraseDups_drop {α : Type} [DecidableEq α] {A X Y : List α} (hX : ∀ x ∈ X, x ∈ A) :
    (A ++ X ++ Y ++ Y).eraseDups = (A ++ Y).eraseDups := by
  have hsub : ∀ y ∈ Y, y ∈ A ++ X ++ Y := fun y hy => List.mem_append_right _ hy
  rw [List.eraseDups_append (as := A ++ X ++ Y), List.eraseDups_append (as := A ++ X),
    List.eraseDups_append (as := A)]
  rw [List.eraseDups_append (as := A)]
  have h1 : Y.removeAll (A ++ X ++ Y) = [] := by
    simp only [List.removeAll, List.filter_eq_nil_iff]
    intro y hy
    have h := hsub y hy
    simp only [List.mem_append] at h
    rcases h with (h | h) | h <;> simp [h]
  have h2 : X.removeAll A = [] := by
    simp only [List.removeAll, List.filter_eq_nil_iff]
    intro x hx
    simp [hX x hx]
  have h3 : Y.removeAll (A ++ X) = Y.removeAll A := by
    simp only [List.removeAll]
    refine List.filter_congr fun y _ => ?_
    by_cases hy : y ∈ A
    · simp [hy]
    · by_cases hy' : y ∈ X
      · exact absurd (hX y hy') hy
      · simp [hy, hy']
  rw [h1, h2, h3]
  simp

theorem varsOfList_append : ∀ (ps qs : List Kore.Pattern),
    KoreAML.varsOfList (ps ++ qs) = KoreAML.varsOfList ps ++ KoreAML.varsOfList qs
  | [], qs => by simp [KoreAML.varsOfList]
  | p :: ps, qs => by
    simp only [List.cons_append, KoreAML.varsOfList, varsOfList_append ps qs, List.append_assoc]

theorem freeOfList_append (b : List KoreAML.VarKey) : ∀ (ps qs : List Kore.Pattern),
    KoreAML.freeOfList b (ps ++ qs) = KoreAML.freeOfList b ps ++ KoreAML.freeOfList b qs
  | [], qs => by simp [KoreAML.freeOfList]
  | p :: ps, qs => by
    simp only [List.cons_append, KoreAML.freeOfList, freeOfList_append b ps qs, List.append_assoc]

/-- The premise `⌈R⌉` appended to a rewrite's left side changes neither the variable table nor the
guarded variables: its variables are the right side's, met later anyway. -/
theorem table_ceil (C : Kore.KSort) (ps : List Kore.Pattern) (R : Kore.Pattern) :
    KoreAML.tableOf [] (.rewrites C (.and C (ps ++ [.ceil C C R])) R) = KoreAML.tableOf [] (.rewrites C (.and C ps) R) := by
  simp only [KoreAML.tableOf, List.map_nil, List.nil_append, KoreAML.varsOf, varsOfList_append,
    KoreAML.varsOfList, List.append_nil]
  have := eraseDups_drop (A := KoreAML.sortVarsOf C ++ (KoreAML.sortVarsOf C ++ KoreAML.varsOfList ps))
    (X := KoreAML.sortVarsOf C ++ KoreAML.sortVarsOf C) (Y := KoreAML.varsOf R)
    (fun x hx => by simp only [List.mem_append] at hx ⊢; rcases hx with h | h <;> exact .inl h)
  simpa only [List.append_assoc] using this

theorem free_ceil (C : Kore.KSort) (ps : List Kore.Pattern) (R : Kore.Pattern) :
    (([] : List Kore.SortVar).map KoreAML.sortVarKey ++ KoreAML.freeOf [] (.rewrites C (.and C (ps ++ [.ceil C C R])) R)).eraseDups =
    (([] : List Kore.SortVar).map KoreAML.sortVarKey ++ KoreAML.freeOf [] (.rewrites C (.and C ps) R)).eraseDups := by
  simp only [List.map_nil, List.nil_append, KoreAML.freeOf, freeOfList_append, KoreAML.freeOfList, List.append_nil]
  have := eraseDups_drop (A := KoreAML.freeOfList [] ps) (X := []) (Y := KoreAML.freeOf [] R) (fun x hx => by cases hx)
  simpa only [List.append_nil, List.append_assoc] using this

/-- For a rule with no existential variables (`r.exs = []`) and whose predicates `pre` and `post` are
`\top`, in every semantics: `prioRuleK` is `UndefRhsWitness.textRuleK` with `⌈rhs ∧ ens⌉` appended to its
left side, whose conjuncts are the left side and the `requires`, and the competitors' negation where
there are competitors. -/
theorem prio_eq_text (c : Semantics) (r : Rule) (hex : r.exs = []) (hpre : r.pre = .top)
    (hpost : r.post = .top) : ∃ (C : Kore.KSort) (l q R : Kore.Pattern) (ps : List Kore.Pattern),
    (ps = [l, q] ∨ ∃ n, ps = [l, q, n]) ∧
    UndefRhsWitness.textRuleK c r = .rewrites C (.and C ps) R ∧ prioRuleK c r = .rewrites C (.and C (ps ++ [.ceil C C R])) R := by
  rw [prioRuleK_top hex hpre hpost]
  unfold UndefRhsWitness.textRuleK
  dsimp only
  by_cases hc : ((c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')).isEmpty = true
  · rw [if_pos hc, if_pos hc]; exact ⟨_, _, _, _, _, .inl rfl, rfl, rfl⟩
  · rw [if_neg hc, if_neg hc]; exact ⟨_, _, _, _, _, .inr ⟨_, rfl⟩, rfl, rfl⟩

/-- **G8** (`ReadingNote.ruleRightDefined`): for every semantics and every rule with no existential
variables (`r.exs = []`) and whose predicates `pre` and `post` are `\top`, so under every interpretation of
the points the text leaves open, the rule's axiom as the text writes it (`UndefRhsWitness.textRuleK`: no premise
`⌈rhs ∧ ens⌉`), with the definedness axioms, entails the axiom `Γ` reads (`prioRuleK`). The
competitors' negation, the priority reading, is in both. -/
theorem ruleRightDefined_weaker (c : Semantics) (r : Rule) (hex : r.exs = []) (hpre : r.pre = .top)
    (hpost : r.post = .top) :
    (fun φ => φ = (UndefRhsWitness.textRuleItem c r).pat ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ⊧
      (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat := by
  intro M _ I hI
  have hD : KoreAML.DefOK I := KoreAML.defOK_of fun x => hI _ (.inr ⟨x, rfl⟩)
  have h := hI _ (.inl rfl)
  obtain ⟨C, l, q, R, ps, hps, ht, hp⟩ := prio_eq_text c r hex hpre hpost
  intro e m
  have h1 := h e m
  unfold UndefRhsWitness.textRuleItem KoreAML.trAxiom at h1
  unfold KoreAML.trAxiom
  dsimp only at h1 ⊢
  rw [ht] at h1
  rw [hp, table_ceil, free_ceil]
  have hs : ∀ L, KoreAML.sortOf [] (.rewrites C L R) = some C := fun _ => rfl
  simp only [hs] at h1 ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [KoreAML.interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  generalize KoreAML.tableOf [] (.rewrites C (.and C ps) R) = tb at h3 ⊢
  rw [KoreAML.tr] at h3 ⊢
  unfold KoreAML.sRewrites at h3 ⊢
  rw [KoreAML.interp_sImp] at h3 ⊢
  refine ⟨fun h' => h'.1, fun ha => ⟨ha, fun hL => (h3.mpr ha).2 ?_⟩⟩
  rcases hps with rfl | ⟨n, rfl⟩
  · simp only [List.cons_append, List.nil_append] at hL
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at hL
    rw [tr_and2, KoreAML.interp_sAnd]
    exact ⟨hL.1, hL.2.1⟩
  · simp only [List.cons_append, List.nil_append] at hL
    rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at hL
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    exact ⟨hL.1, hL.2.1, hL.2.2.1⟩

end RightDefined

/-! ## G9: `existsDropped`, the text's rewrite axiom entails the one without the binder -/

section ExistsDropped

/-- The item of the rewrite axiom `\rewrites{C}(L, R)` with no sort variables (`trAxiom`). -/
def rwItem (C : Kore.KSort) (L R : Kore.Pattern) : KoreAML.Item :=
  KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := .rewrites C L R, attributes := [] }⟩

/-- The guards of that item: one for each free variable of the axiom, numbered by its table. -/
def rwGuards (C : Kore.KSort) (L R : Kore.Pattern) : List KoreAML.P :=
  ((([] : List Kore.SortVar).map KoreAML.sortVarKey ++ KoreAML.freeOf [] (.rewrites C L R)).eraseDups).map
    (KoreAML.guardOf (KoreAML.tableOf [] (.rewrites C L R)))

/-- The item's pattern: under the guards, the translated rewrite is all of the sort C. -/
theorem rwItem_pat (C : Kore.KSort) (L R : Kore.Pattern) :
    (rwItem C L R).pat = (KoreAML.conjList (rwGuards C L R) ⇒
      (KoreAML.sRewrites (KoreAML.trSort (KoreAML.tableOf [] (.rewrites C L R)) C)
          (KoreAML.tr ⟨KoreAML.tableOf [] (.rewrites C L R), []⟩ L)
          (KoreAML.tr ⟨KoreAML.tableOf [] (.rewrites C L R), []⟩ R) ≡
        KoreAML.inhOf (KoreAML.trSort (KoreAML.tableOf [] (.rewrites C L R)) C))) := by
  unfold rwItem rwGuards KoreAML.trAxiom
  have hs : KoreAML.sortOf [] (.rewrites C L R) = some C := rfl
  simp only [hs]
  rw [KoreAML.tr]

/-- **G9** (`ReadingNote.existsDropped`): the rewrite axiom `\rewrites{C}(L, \exists Z:s. R)` as
the text writes it, with the definedness axioms, entails `\rewrites{C}(L, R)`, the axiom the reader
reads where the binder binds nothing, in every interpretation: nothing is asked of the sort s of Z,
which may have no element. The premises are about the numbering of the two sentences' variables
(`tableOf` numbers a sentence's variables in the order it first holds them, the binder's among
them): `hC`, `hL`, `hR`, the sort C, the left side and R translate to one pattern under both
tables; `hG`, the free variables' guards are the same; `hZ`, the binder's index is not free in the
translated R (Z is not free in R). Each is an equation between computed values of the two
sentences. Where s has an element the text's right side is R's; where it has none it is empty,
and the text's sentence then states `L → ⊥`, of which `L → •R` is a consequence. -/
theorem existsDropped_weaker (C : Kore.KSort) (L R : Kore.Pattern) (Z : Kore.EVar)
    (hC : KoreAML.trSort (KoreAML.tableOf [] (.rewrites C L (.exist C Z R))) C =
      KoreAML.trSort (KoreAML.tableOf [] (.rewrites C L R)) C)
    (hL : KoreAML.tr ⟨KoreAML.tableOf [] (.rewrites C L (.exist C Z R)), []⟩ L =
      KoreAML.tr ⟨KoreAML.tableOf [] (.rewrites C L R), []⟩ L)
    (hR : KoreAML.tr ⟨KoreAML.tableOf [] (.rewrites C L (.exist C Z R)), []⟩ R =
      KoreAML.tr ⟨KoreAML.tableOf [] (.rewrites C L R), []⟩ R)
    (hG : rwGuards C L (.exist C Z R) = rwGuards C L R)
    (hZ : (KoreAML.tr ⟨KoreAML.tableOf [] (.rewrites C L R), []⟩ R).isFreeEvar
      ((KoreAML.tableOf [] (.rewrites C L (.exist C Z R))).ev (KoreAML.evarKey Z)) = false) :
    (fun φ => φ = (rwItem C L (.exist C Z R)).pat ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ⊧
      (rwItem C L R).pat := by
  intro M _ I hI
  have hD : KoreAML.DefOK I := KoreAML.defOK_of fun x => hI _ (.inr ⟨x, rfl⟩)
  have h := hI _ (.inl rfl)
  intro e m
  have h1 := h e m
  rw [rwItem_pat] at h1 ⊢
  rw [KoreAML.tr, hC, hL, hR, hG] at h1
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [KoreAML.interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  unfold KoreAML.sRewrites at h3 ⊢
  rw [KoreAML.interp_sImp] at h3 ⊢
  refine ⟨fun h' => h'.1, fun ha => ⟨ha, fun hLa => ?_⟩⟩
  have h4 := (h3.mpr ha).2 hLa
  unfold KoreAML.sNext at h4 ⊢
  rw [KoreAML.interp_app] at h4 ⊢
  obtain ⟨u, b, hu, hb, hab⟩ := h4
  refine ⟨u, b, hu, ?_, hab⟩
  rw [KoreAML.interp_sExists] at hb
  obtain ⟨v, _, hv⟩ := hb
  refine (only_free_var_relevant (I := I) _ _ _ _ (fun x hx => ?_) (fun _ _ => rfl) b).mp hv
  by_cases hxz : x = (KoreAML.tableOf [] (.rewrites C L (.exist C Z R))).ev (KoreAML.evarKey Z)
  · rw [hxz, hZ] at hx; cases hx
  · simp [Function.update, hxz]

/-! The instance: `c(X:Int) => \exists Z:Empty. d(X:Int)` entails `c(X:Int) => d(X:Int)`, Empty a
sort of which the two sentences state nothing (no constructor, no element): the shape of
test/ExReader.lean's site c at a sort without a constructor. -/

def exC : Kore.KSort := KoreAML.srt "GeneratedTopCell"
def exL : Kore.Pattern := .and exC [KoreAML.ap "Lblc" [KoreAML.ev "VarX" (KoreAML.srt "Int")], .top exC]
def exR : Kore.Pattern := .and exC [KoreAML.ap "Lbld" [KoreAML.ev "VarX" (KoreAML.srt "Int")], .top exC]
def exZ : Kore.EVar := KoreAML.evar "VarZ" (KoreAML.srt "Empty")

/-- G9 at `c(X:Int) => \exists Z:Empty. d(X:Int)`: the five premises by the kernel. -/
theorem existsDropped_empty :
    (fun φ => φ = (rwItem exC exL (.exist exC exZ exR)).pat ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ⊧
      (rwItem exC exL exR).pat :=
  existsDropped_weaker exC exL exR exZ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end ExistsDropped

/-! ## The reader's devices: what the checks on the data give under every interpretation -/

section EveryH
open KCore.Exec KCore.Cert
variable {c : Semantics}

/-- A configuration of the data is one under every interpretation, where no parameter is an open
generator. -/
def cfgH (hr : ∀ k ∈ c.params, k.raw = false) (x : Config c) (H : HookParams) : Config (c.withHooks H) :=
  ⟨x.val, by rw [Semantics.sortOf_withHooks _ _ hr]; exact x.property⟩

/-- A step some rule's check accepts on the data, which reads no interpretation
(`Cert.checkStep_withHooks`), is a step under every interpretation. -/
theorem step_everyH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) {x y : Config c} {n : Nat}
    (hc : c.rules.any (fun r => checkStep c n r x.val y.val) = true) (H : HookParams) :
    Step (c.withHooks H) (cfgH hr x H) (cfgH hr y H) := by
  obtain ⟨r, hmem, hc⟩ := List.any_eq_true.mp hc
  obtain ⟨_, hstep⟩ := step_of_listed ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    (x := cfgH hr x H)
    (listed_of_checkStep (c := c.withHooks H) (r := r) hmem ((checkStep_withHooks c H hr n r _ _).trans hc))
  exact hstep

/-- A configuration `stuckCheck` accepts on the data has no successor under any interpretation. -/
theorem stuck_everyH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) (hcf : c.clausesFixed = true) (hag : c.agreeObligations = [])
    (hna : c.asideFree = true) {x : Config c} {n : Nat} (h : stuckCheck c n x.val = true) (H : HookParams) :
    ∀ y, ¬ Step (c.withHooks H) (cfgH hr x H) y :=
  stuckCheck_sound hok hsr hmr H
    (Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
      ((Semantics.matchReady_withHooks c H).trans hmr) ((Semantics.clausesFixed_withHooks c H).trans hcf)
      ((Semantics.agreeObligations_withHooks c H).trans hag))
    (x := cfgH hr x H) h hna hr

/-- A successor the executable step lists under the interpretation H is a step under H. -/
theorem step_atH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) {x y : Config c} (H : HookParams) {n : Nat}
    (h : (successorsN (c.withHooks H) n x.val).any (same · y.val) = true) :
    Step (c.withHooks H) (cfgH hr x H) (cfgH hr y H) := by
  obtain ⟨_, hstep⟩ := step_of_listed ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    (x := cfgH hr x H) h
  exact hstep

/-- A function's result the executable evaluation finds under the interpretation H is its result
under H. -/
theorem eval_atH (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    (hr : ∀ k ∈ c.params, k.raw = false) {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args) (H : HookParams) {n : Nat} {r : Option GroundTerm}
    (h : evalF (c.withHooks H) n f vs = some r) : Eval (c.withHooks H) f vs r := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  exact evalF_sound (sortCtx_of hok' hsr' (ovlCase_of hmr')) (clauseCtx_of hok') (matchCtx_of hmr') n h
    (by rw [Semantics.lookupFn_withHooks]; exact hfn) (by rw [Semantics.sortsOf_withHooks c H hr]; exact hvs)

end EveryH

/-- The configuration with `it` in the k cell `kCell` and the counter at 0. -/
def cfgOf (kCell : Sym) (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

/-! ### `orSplit`: one rule per disjunct of a left side -/

-- `c(a() #Or b()) => a()` (the construct fixture e7-guardors).
namespace DevOr

definition_of defn from "f2-examples/mlor.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def a : Sym := 385
def b : Sym := 386
def cc : Sym := 387
def exp : Srt := 32
theorem names_ok : c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧ c.symName cc = "Lblc" ∧
    c.sortName exp = "Exp" := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def CA : Config c := ⟨cfg (.ctor cc [.ctor a []]), by decide +kernel⟩
def CB : Config c := ⟨cfg (.ctor cc [.ctor b []]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor a []), by decide +kernel⟩

/-- **`orSplit`, for every interpretation**: `c(a)` and `c(b)` each step to `a`, as the axiom
`c(a ∨ b) → •a` says of each disjunct. -/
theorem or_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw CA H) (cfgH noRaw A H) ∧ Step (c.withHooks H) (cfgH noRaw CB H) (cfgH noRaw A H) :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H⟩

/-- The axiom read as its first disjunct's rule alone. -/
noncomputable def c1 : Semantics := { c with rules := c.rules.take 1 }
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
def CA1 : Config c1 := ⟨CA.val, by decide +kernel⟩
def CB1 : Config c1 := ⟨CB.val, by decide +kernel⟩

/-- **The point is reached**: read as one disjunct's rule, the other disjunct's configuration has
no successor, under every interpretation. -/
theorem or_one_stuck (H : HookParams) :
    (∀ y, ¬ Step (c1.withHooks H) (cfgH noRaw1 CA1 H) y) ∨ (∀ y, ¬ Step (c1.withHooks H) (cfgH noRaw1 CB1 H) y) :=
  .inr (stuck_everyH hok1 hsr1 hmr1 noRaw1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 50)
    (by decide +kernel) H)

end DevOr

/-! ### `topAsVariable`: `\top` in a left side is a variable of the rule -/

-- `c(#Top) => a()` (the construct fixture e3-ml-rule-lhs-top).
namespace DevTop

definition_of defn from "f2-examples/mltop.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def a : Sym := 385
def b : Sym := 386
def cc : Sym := 387
def d : Sym := 388
def exp : Srt := 32
theorem names_ok : c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧ c.symName cc = "Lblc" ∧ c.symName d = "Lbld" ∧
    c.sortName exp = "Exp" := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def CB : Config c := ⟨cfg (.ctor cc [.ctor b []]), by decide +kernel⟩
def CD : Config c := ⟨cfg (.ctor cc [.ctor d [.ctor a [], .ctor b []]]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor a []), by decide +kernel⟩

/-- **`topAsVariable`, for every interpretation**: `c(b)` and `c(d(a, b))` each step to `a`:
`c(⊤)` holds `c(v)` for every value `v` of Exp. -/
theorem top_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw CB H) (cfgH noRaw A H) ∧ Step (c.withHooks H) (cfgH noRaw CD H) (cfgH noRaw A H) :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H⟩

/-- The text with the axiom not read: no rule. -/
noncomputable def c0 : Semantics := { c with rules := [] }
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel
private theorem hok0 : c0.ok = true := by decide +kernel
private theorem hsr0 : c0.srReady = true := by decide +kernel
private theorem hmr0 : c0.matchReady = true := by decide +kernel
def CB0 : Config c0 := ⟨CB.val, by decide +kernel⟩

/-- **The point is reached**: without the rule `c(b)` has no successor, under every interpretation. -/
theorem top_unread_stuck (H : HookParams) : ∀ y, ¬ Step (c0.withHooks H) (cfgH noRaw0 CB0 H) y :=
  stuck_everyH hok0 hsr0 hmr0 noRaw0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 50)
    (by decide +kernel) H

end DevTop

/-! ### `existsAsVariable`: `\exists` in a left side binds a variable of the rule -/

-- `c(#Exists Y:Exp. d(Y, b())) => a()` (the construct fixture e3-ml-rule-lhs-exists).
namespace DevEx

definition_of defn from "f2-examples/mlex.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def a : Sym := 385
def b : Sym := 386
def cc : Sym := 387
def d : Sym := 388
def exp : Srt := 32
theorem names_ok : c.symName a = "Lbla" ∧ c.symName b = "Lblb" ∧ c.symName cc = "Lblc" ∧ c.symName d = "Lbld" ∧
    c.sortName exp = "Exp" := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def CDA : Config c := ⟨cfg (.ctor cc [.ctor d [.ctor a [], .ctor b []]]), by decide +kernel⟩
def CDB : Config c := ⟨cfg (.ctor cc [.ctor d [.ctor b [], .ctor b []]]), by decide +kernel⟩
def CDX : Config c := ⟨cfg (.ctor cc [.ctor d [.ctor b [], .ctor a []]]), by decide +kernel⟩
def A : Config c := ⟨cfg (.ctor a []), by decide +kernel⟩

/-- **`existsAsVariable`, for every interpretation**: `c(d(a, b))` and `c(d(b, b))` each step to
`a` (Y is `a`, then `b`), and `c(d(b, a))`, which no Y makes an instance of the left side, has no
successor. -/
theorem ex_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw CDA H) (cfgH noRaw A H) ∧ Step (c.withHooks H) (cfgH noRaw CDB H) (cfgH noRaw A H) ∧
    ∀ y, ¬ Step (c.withHooks H) (cfgH noRaw CDX H) y :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 50)
    (by decide +kernel) H⟩

/-- The text with the axiom not read: no rule. -/
noncomputable def c0 : Semantics := { c with rules := [] }
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel
private theorem hok0 : c0.ok = true := by decide +kernel
private theorem hsr0 : c0.srReady = true := by decide +kernel
private theorem hmr0 : c0.matchReady = true := by decide +kernel
def CDB0 : Config c0 := ⟨CDB.val, by decide +kernel⟩

/-- **The point is reached**: without the rule `c(d(b, b))` has no successor, under every
interpretation. -/
theorem ex_unread_stuck (H : HookParams) : ∀ y, ¬ Step (c0.withHooks H) (cfgH noRaw0 CDB0 H) y :=
  stuck_everyH hok0 hsr0 hmr0 noRaw0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 50)
    (by decide +kernel) H

end DevEx

/-! ### `predicateAtBool`: a predicate at sort Bool is never `true` -/

-- `go(X) => done requires #Ceil(1 /Int X)` beside `go(_) => other [priority(60)]` (the construct
-- fixture e3-ml-req-ceil).
namespace DevCeil

definition_of defn from "f2-examples/mlceil.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def done : Sym := 385
def go : Sym := 386
def other : Sym := 387
def exp : Srt := 32
theorem names_ok : c.symName done = "Lbldone" ∧ c.symName go = "Lblgo" ∧ c.symName other = "Lblother" ∧
    c.sortName exp = "Exp" := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def Go1 : Config c := ⟨cfg (.ctor go [int 1]), by decide +kernel⟩
def Other : Config c := ⟨cfg (.ctor other []), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor done []), by decide +kernel⟩

/-- **`predicateAtBool`, for every interpretation**: `go(1)` steps to `other`, by the rule of
priority 60: the first rule's `requires`, a predicate at Bool equated with `true`, holds nowhere, so
it neither steps nor blocks. -/
theorem ceil_steps (H : HookParams) : Step (c.withHooks H) (cfgH noRaw Go1 H) (cfgH noRaw Other H) :=
  step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H

/-- The first rule read with the predicate as holding where `1 /Int X` has a value: no `requires`
at `X = 1`. -/
noncomputable def c1 : Semantics :=
  { c with rules := c.rules.map fun r => if r.prio = 50 then { r with req := none } else r }
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
def Go11 : Config c1 := ⟨Go1.val, by decide +kernel⟩
def Done1 : Config c1 := ⟨Done.val, by decide +kernel⟩

/-- **The point is reached**: read so, `go(1)` steps to `done` under every interpretation. -/
theorem ceil_defined_steps (H : HookParams) : Step (c1.withHooks H) (cfgH noRaw1 Go11 H) (cfgH noRaw1 Done1 H) :=
  step_everyH hok1 hsr1 hmr1 noRaw1 (n := 50) (by decide +kernel) H

end DevCeil

/-! ### `andAtBool`: `\and{SortBool{}}` of terms is their strict conjunction -/

-- `go(B) => done requires true #And B` (the construct fixture e3-ml-req-and-var).
namespace DevAndBool

definition_of defn from "f2-examples/mlreqv.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def done : Sym := 385
def go : Sym := 386
def exp : Srt := 32
theorem names_ok : c.symName done = "Lbldone" ∧ c.symName go = "Lblgo" ∧ c.sortName exp = "Exp" := by
  decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def GoT : Config c := ⟨cfg (.ctor go [.dv Srt.bool (.bool true)]), by decide +kernel⟩
def GoF : Config c := ⟨cfg (.ctor go [.dv Srt.bool (.bool false)]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor done []), by decide +kernel⟩

/-- **`andAtBool`, for every interpretation**: `go(true)` steps to `done` and `go(false)` has no
successor: `{true} ∩ {B}` is `{true}` exactly where B is `true`. -/
theorem and_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw GoT H) (cfgH noRaw Done H) ∧ ∀ y, ¬ Step (c.withHooks H) (cfgH noRaw GoF H) y :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 50)
    (by decide +kernel) H⟩

/-- The `requires` read as its first conjunct alone, `true`: no `requires`. -/
noncomputable def c1 : Semantics := { c with rules := c.rules.map fun r => { r with req := none } }
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
def GoF1 : Config c1 := ⟨GoF.val, by decide +kernel⟩
def Done1 : Config c1 := ⟨Done.val, by decide +kernel⟩

/-- **The point is reached**: read so, `go(false)` steps to `done` under every interpretation. -/
theorem and_first_steps (H : HookParams) : Step (c1.withHooks H) (cfgH noRaw1 GoF1 H) (cfgH noRaw1 Done1 H) :=
  step_everyH hok1 hsr1 hmr1 noRaw1 (n := 50) (by decide +kernel) H

end DevAndBool

/-! ### `requiresOrSplit`: one rule per disjunct of a `requires` -/

-- `go(X) => done requires X >=Int 0 #Or 10 /Int X >Int 0` (the construct fixture
-- e3-ml-req-or-undef).
namespace DevReqOr

definition_of defn from "f2-examples/mlreqor.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def done : Sym := 385
def go : Sym := 386
def exp : Srt := 32
theorem names_ok : c.symName done = "Lbldone" ∧ c.symName go = "Lblgo" ∧ c.sortName exp = "Exp" := by
  decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj exp Srt.kitem e)
def Go0 : Config c := ⟨cfg (.ctor go [int 0]), by decide +kernel⟩
def GoM1 : Config c := ⟨cfg (.ctor go [int (-1)]), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor done []), by decide +kernel⟩

/-- **`requiresOrSplit`, for every interpretation**: `go(0)` steps to `done` (`0 >=Int 0` is
`true`; `10 /Int 0` has no value, and the union of the two disjuncts still holds `true`), and
`go(-1)` has no successor (both disjuncts are `false`). -/
theorem reqOr_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw Go0 H) (cfgH noRaw Done H) ∧ ∀ y, ¬ Step (c.withHooks H) (cfgH noRaw GoM1 H) y :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 50)
    (by decide +kernel) H⟩

/-- The two disjuncts read as one `requires`, `A₁ orBool A₂`. -/
noncomputable def c1 : Semantics :=
  { c with rules := match c.rules with
      | [r₁, r₂] => [{ r₁ with req := match r₁.req, r₂.req with
          | some t₁, some t₂ => some (.app boolOr [t₁, t₂])
          | _, _ => none }]
      | rs => rs }
theorem one_rule : c1.rules.map (fun r => r.req.map Term.heads) = [some [boolOr, intGe, intGt, intTDiv]] := by
  decide +kernel
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
def Go01 : Config c1 := ⟨Go0.val, by decide +kernel⟩

/-- **The point is reached**: read as `orBool`, which has no value where one argument has none,
`go(0)` has no successor under every interpretation. -/
theorem reqOr_orBool_stuck (H : HookParams) : ∀ y, ¬ Step (c1.withHooks H) (cfgH noRaw1 Go01 H) y :=
  stuck_everyH hok1 hsr1 hmr1 noRaw1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (n := 50)
    (by decide +kernel) H

end DevReqOr

/-! ### `andAsEnsures`: `t ∧ ⌈B = true⌉` in an equation's right side is t with the `ensures` B -/

-- `f(X) => X #And {(X >Int 0) #Equals true}` (the construct fixture e3-ml-eq-rhs-and-pred).
namespace DevAndEns

definition_of defn from "f2-examples/mleqand.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def f : Sym := 384
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl
theorem coreOK : c.coreOK = true := by decide_cheap

/-- **`andAsEnsures`, for every interpretation**: `f(1)` is 1, and `f(0)` has no value: the right
side `X ∧ ⌈X >Int 0 = true⌉` is empty at 0, so `Γ` entails `f(0) = ⊥`. -/
theorem andEns_values (H : HookParams) :
    Eval (c.withHooks H) f [int 1] (some (int 1)) ∧ Eval (c.withHooks H) f [int 0] none ∧
    (Γ (c.withHooks H) ⊧ (KoreAML.den (symApp (c.withHooks H) f (GroundTerm.koreList (c.withHooks H) [int 0])) ≡ ⊥)) :=
  have h0 := eval_everyH hok hsr hmr noRaw hfn (vs := [int 0]) (r := none) (by decide +kernel) (n := 10) (by decide +kernel) H
  ⟨eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H, h0,
   gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by decide +kernel) H h0⟩

/-- The predicate read as a `requires` of the equation: the clause fails where it is not `true`. -/
noncomputable def c1 : Semantics :=
  { c with fns := c.fns.map fun g => if g.label = f then
      { g with clauses := g.clauses.map fun cl => { cl with req := cl.ens, ens := none } } else g }
noncomputable abbrev fn1 : Fn := c1.fns[0]'(by decide +kernel)
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
private theorem hfn1 : c1.lookupFn f = some fn1 := rfl

/-- The interpretation that gives `f(0)` the value 7 and nothing else. -/
def H7 : HookParams := ⟨fun g vs => if g = f ∧ vs = [int 0] then some (int 7) else none⟩

/-- **The point is reached**: read so, `f(0)` is a point where every clause fails, and under `H7`
it is 7. -/
theorem andEns_asRequires_H7 : Eval (c1.withHooks H7) f [int 0] (some (int 7)) :=
  eval_atH hok1 hsr1 hmr1 noRaw1 hfn1 (by decide +kernel) H7 (n := 10) (by decide +kernel)

end DevAndEns

/-! ### `bottomAsEnsures`: `\bottom` in an equation's right side is the `ensures` false -/

-- `f(X) => #Bottom requires X <Int 0` beside `f(X) => X [owise]` (the construct fixture
-- e3-ml-eq-rhs-bottom).
namespace DevBot

definition_of defn from "f2-examples/mleqbot.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def f : Sym := 384
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl
theorem coreOK : c.coreOK = true := by decide_cheap

/-- **`bottomAsEnsures`, for every interpretation**: `f(2)` is 2 (the `[owise]` equation), and
`f(-1)` has no value: the first equation applies there, its right side is empty, and it blocks the
`[owise]` one; `Γ` entails `f(-1) = ⊥`. -/
theorem bot_values (H : HookParams) :
    Eval (c.withHooks H) f [int 2] (some (int 2)) ∧ Eval (c.withHooks H) f [int (-1)] none ∧
    (Γ (c.withHooks H) ⊧ (KoreAML.den (symApp (c.withHooks H) f (GroundTerm.koreList (c.withHooks H) [int (-1)])) ≡ ⊥)) :=
  have h0 := eval_everyH hok hsr hmr noRaw hfn (vs := [int (-1)]) (r := none) (by decide +kernel) (n := 10) (by decide +kernel) H
  ⟨eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H, h0,
   gamma_bot_everyH coreOK noRaw (by decide +kernel) hfn (by decide +kernel) H h0⟩

/-- The equation with the empty right side not read: `f` has the `[owise]` clause alone. -/
noncomputable def c1 : Semantics :=
  { c with fns := c.fns.map fun g => if g.label = f then
      { g with clauses := g.clauses.filter fun cl => cl.ens.isNone } else g }
noncomputable abbrev fn1 : Fn := c1.fns[0]'(by decide +kernel)
theorem one_clause : fn1.clauses.map (·.prio) = [200] := by decide +kernel
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
private theorem hfn1 : c1.lookupFn f = some fn1 := rfl

/-- **The point is reached**: read so, `f(-1)` is -1 under every interpretation. -/
theorem bot_unread_value (H : HookParams) : Eval (c1.withHooks H) f [int (-1)] (some (int (-1))) :=
  eval_everyH hok1 hsr1 hmr1 noRaw1 hfn1 (by decide +kernel) (n := 10) (by decide +kernel) H

end DevBot

/-! ### `orBottom`: `t ∨ ⊥` in a right side is t -/

-- `f(X) => X #Or #Bottom` (the construct fixture e3-ml-eq-rhs-or-bottom).
namespace DevOrBot

definition_of defn from "f2-examples/mleqorb.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def f : Sym := 384
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl

/-- **`orBottom`, for every interpretation**: `f(3)` is 3. -/
theorem orBot_value (H : HookParams) : Eval (c.withHooks H) f [int 3] (some (int 3)) :=
  eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H

/-- The equation not read: `f` has no clause. -/
noncomputable def c1 : Semantics :=
  { c with fns := c.fns.map fun g => if g.label = f then { g with clauses := [] } else g }
noncomputable abbrev fn1 : Fn := c1.fns[0]'(by decide +kernel)
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
private theorem hfn1 : c1.lookupFn f = some fn1 := rfl

/-- The interpretation that gives `f(3)` the value 7 and nothing else. -/
def H7 : HookParams := ⟨fun g vs => if g = f ∧ vs = [int 3] then some (int 7) else none⟩

/-- **The point is reached**: read so, `f(3)` is the interpretation's, 7 under `H7`. -/
theorem orBot_unread_H7 : Eval (c1.withHooks H7) f [int 3] (some (int 7)) :=
  eval_atH hok1 hsr1 hmr1 noRaw1 hfn1 (by decide +kernel) H7 (n := 10) (by decide +kernel)

end DevOrBot

/-! ## The other notes: `reflectionAsOwn`, `keyFunctionAsRequires`, `equationPriority`, `owiseAsPriority` -/

/-! ### `reflectionAsOwn`: a K-REFLECTION symbol is a parameter symbol -/

-- `<k> go => wrap(#configuration) ... </k>` with K-REFLECTION imported (the construct fixture
-- e6-configuration).
namespace DevRefl

definition_of defn from "f2-examples/e6cfg.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def cfgSym : Sym := 389
def go : Sym := 386
def wrap : Sym := 387
def expS : Srt := 32
theorem names_ok : c.symName cfgSym = "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K" ∧
    c.symName go = "Lblgo" ∧ c.symName wrap = "Lblwrap" ∧ c.sortName expS = "Exp" := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 (.inj expS Srt.kitem e)
def Go : Config c := ⟨cfg (.ctor go []), by decide +kernel⟩
def WrapK : Config c := ⟨cfg (.ctor wrap [.ctor dotk []]), by decide +kernel⟩

/-- `#configuration` is a parameter symbol with no registry hook, no open generator, of result
sort K. -/
theorem conf_param : (c.lookupParam cfgSym).map (fun k => (k.impl, k.raw, k.sig.result)) =
    some (none, false, Srt.k) := by decide +kernel

/-- **`reflectionAsOwn`, for every interpretation**: the value of `#configuration` is the
interpretation's answer, kept where it is of sort K: the text states nothing else of it. -/
theorem conf_value (H : HookParams) :
    (c.withHooks H).paramVal cfgSym [] =
      (H.app cfgSym []).filter fun v => (c.withHooks H).sortOf v == some Srt.k := by
  have hl : (c.withHooks H).lookupParam cfgSym = c.lookupParam cfgSym := rfl
  have hp := conf_param
  unfold Semantics.paramVal
  rw [hl]
  cases hk : c.lookupParam cfgSym with
  | none => rw [hk] at hp; cases hp
  | some k =>
    rw [hk] at hp
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨hi, hraw, hres⟩ := hp
    simp only [hi, hraw, hres, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The interpretation that gives `#configuration` the empty K sequence. -/
def Hk : HookParams := ⟨fun f _ => if f = cfgSym then some (.ctor dotk []) else none⟩

/-- **The point is reached**: under `Hk`, `go` steps to `wrap(.K)`; under `HookParams.none` it has
no successor (test/Configuration.lean, `stuck_go`). Over all interpretations the text fixes
neither. -/
theorem go_step_Hk : Step (c.withHooks Hk) (cfgH noRaw Go Hk) (cfgH noRaw WrapK Hk) :=
  step_atH hok hsr hmr noRaw Hk (n := 50) (by decide +kernel)

end DevRefl

/-! ### `keyFunctionAsRequires`: a function applied as a map key in a left side -/

-- `<k> look(I) => V ... </k> <tab> kf(I) |-> V ... </tab>`, `kf(1) => k(1)` its one equation
-- (`f2-examples/keyfn-partial.k`).
namespace DevKey

definition_of defn from "f2-examples/keyfn-partial.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def kCell : Sym := 389
def baseCell : Sym := 391
def memCell : Sym := 393
def tabCell : Sym := 395
def kk : Sym := 398
def look : Sym := 399
def kf : Sym := 402
def key : Srt := 38
theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName baseCell = "Lbl'-LT-'base'-GT-'" ∧
    c.symName memCell = "Lbl'-LT-'mem'-GT-'" ∧ c.symName tabCell = "Lbl'-LT-'tab'-GT-'" ∧ c.symName kk = "Lblk" ∧
    c.symName look = "Lbllook" ∧ c.symName kf = "Lblkf" ∧ c.sortName key = "Key" := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
/-- The table `k(1) |-> 3`. -/
def tab : GroundTerm := .map Srt.map [(.inj key Srt.kitem (.ctor kk [int 1]), .inj Srt.int Srt.kitem (int 3))]
def cfg (pgm : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [pgm, .ctor dotk []]], .ctor baseCell [int 0],
    .ctor memCell [.map Srt.map []], .ctor tabCell [tab], .ctor counterLabel [int 0]]
def Look1 : Config c := ⟨cfg (.ctor look [int 1]), by decide +kernel⟩
def Look2 : Config c := ⟨cfg (.ctor look [int 2]), by decide +kernel⟩
def Three : Config c := ⟨cfg (.inj Srt.int Srt.kitem (int 3)), by decide +kernel⟩

/-- **`keyFunctionAsRequires`, for every interpretation**: with the table `k(1) |-> 3`, `look(1)`
steps to 3: `kf(1)` is `k(1)` by its equation, a key of the table. -/
theorem key_steps (H : HookParams) : Step (c.withHooks H) (cfgH noRaw Look1 H) (cfgH noRaw Three H) :=
  step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H

/-- The interpretation that gives `kf(2)` the value `k(1)` and nothing else. -/
def Hk : HookParams := ⟨fun f vs => if f = kf ∧ vs = [int 2] then some (.ctor kk [int 1]) else none⟩

/-- **The point is reached**: no equation of `kf` applies at 2, so `kf(2)` is the interpretation's.
Under `Hk` it is `k(1)`, a key of the table, and `look(2)` steps to 3; under `HookParams.none` it
has no value and `look(2)` has no successor (test/KeyFunction.lean, the compiled step). -/
theorem look2_Hk : Step (c.withHooks Hk) (cfgH noRaw Look2 Hk) (cfgH noRaw Three Hk) :=
  step_atH hok hsr hmr noRaw Hk (n := 50) (by decide +kernel)

end DevKey

/-! ### `equationPriority`: an equation is read under the negation of the smaller priorities -/

-- `Faithful.PrioTextWitness.c`: `f() = 1` of priority 50 and `f() = 2` of priority 60.
namespace DevPrio

open Faithful.PrioTextWitness

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl fnItemsText_withHooks : ∀ (c : Semantics) (H : HookParams),
  fnItemsText (c.withHooks H) = fnItemsText c

/-- **`equationPriority`, for every interpretation**: a model of the theory with each equation
under its own premise, as the text writes it (`ΓFnText`), is a model of `Γ`, whose second equation
is under the negation of the first: the text entails what is read. -/
theorem prio_gamma_of_text (H : HookParams) {M : Type} {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP ΓFnText (c.withHooks H)) : I ⊧ᴵP Γ (c.withHooks H) := by
  have hD : KoreAML.DefOK I :=
    KoreAML.defOK_of fun x => hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
  have htext : ∀ {it : KoreAML.Item}, it ∈ fnItemsText c → I ⊧ᴵ it.pat := fun {it} h =>
    hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, by rw [fnItemsText_withHooks]; exact h, rfl⟩))))
  intro φ hφ
  rcases hφ with ((((((h | h) | h) | h) | h) | h) | h)
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · rw [fnItems_withHooks, fnItems_eq] at hit
      rcases List.mem_append.mp hit with hit | hit
      · rcases List.mem_cons.mp hit with rfl | hit
        · exact htext (by rw [fnItemsText_eq]; exact List.mem_cons_self ..)
        rcases List.mem_cons.mp hit with rfl | hit
        · exact item2C_of hD (htext (by rw [fnItemsText_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        · cases hit
      · exact htext (by rw [fnItemsText_eq]; exact List.mem_append_right _ hit)
    · exact hI _ (Or.inl (Or.inl (Or.inr (Or.inr ⟨x, rfl⟩))))
  · exact hI φ (Or.inl (Or.inr h))
  · exact hI φ (Or.inr h)

end DevPrio

/-! ### `owiseAsPriority`: an `[owise]` equation is the clause of priority 200 -/

-- `f(0, _) => 0`, `f(_, 0) => 1`, `f(1, Y) => Y [owise]`, `f(X, 1) => X [owise]`
-- (`f2-examples/owise2.k`).
namespace DevOwise

definition_of defn from "f2-examples/owise2.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
def f : Sym := 387
theorem names_ok : c.symName f = "Lblf" := by decide +kernel
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)
theorem prios : fn.clauses.map (·.prio) = [50, 50, 200, 200] := by decide +kernel
private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl

/-- **`owiseAsPriority`, for every interpretation**: `f(1, 5)` is 5 and `f(7, 1)` is 7, by the
`[owise]` equations, where neither other equation applies; `f(1, 0)` is 1, by `f(_, 0) => 1`, which
the `[owise]` equation `f(1, Y) => Y` (it would give 0) does not override. -/
theorem owise_values (H : HookParams) :
    Eval (c.withHooks H) f [int 1, int 5] (some (int 5)) ∧ Eval (c.withHooks H) f [int 7, int 1] (some (int 7)) ∧
    Eval (c.withHooks H) f [int 1, int 0] (some (int 1)) :=
  ⟨eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H,
   eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H,
   eval_everyH hok hsr hmr noRaw hfn (by decide +kernel) (n := 10) (by decide +kernel) H⟩

/-- The `[owise]` equations not read: `f` has its two other clauses alone. -/
noncomputable def c1 : Semantics :=
  { c with fns := c.fns.map fun g => if g.label = f then
      { g with clauses := g.clauses.filter fun cl => cl.prio != 200 } else g }
noncomputable abbrev fn1 : Fn := c1.fns[0]'(by decide +kernel)
theorem noRaw1 : ∀ k ∈ c1.params, k.raw = false := by decide +kernel
private theorem hok1 : c1.ok = true := by decide +kernel
private theorem hsr1 : c1.srReady = true := by decide +kernel
private theorem hmr1 : c1.matchReady = true := by decide +kernel
private theorem hfn1 : c1.lookupFn f = some fn1 := rfl

/-- The interpretation that gives `f(1, 5)` the value 9 and nothing else. -/
def H9 : HookParams := ⟨fun g vs => if g = f ∧ vs = [int 1, int 5] then some (int 9) else none⟩

/-- **The point is reached**: read so, `f(1, 5)` is a point where every clause fails, the
interpretation's: 9 under `H9`. -/
theorem owise_unread_H9 : Eval (c1.withHooks H9) f [int 1, int 5] (some (int 9)) :=
  eval_atH hok1 hsr1 hmr1 noRaw1 hfn1 (by decide +kernel) H9 (n := 10) (by decide +kernel)

end DevOwise


/-! ## G4: the inert constructor classes, for every interpretation -/

/-- **A constructor sentence the data accepts is entailed, for every interpretation**: the text's
`functional` or subsort sentence of a generator, its no-confusion sentence (`injectivity`) and the
no-confusion sentence of two generators (`distinctCtors`), where `tieConsB` finds the constructor
items `Γ` holds for them. `tieConsB` reads no interpretation. -/
theorem inertCons_everyH (c : Semantics) (hcore : c.coreOK = true) (H : HookParams) {a : Kore.Axiom}
    (h : tieConsB c a = true) (i : Nat) (mod : String) :
    Γ (c.withHooks H) ⊧ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  intro M _ I hI
  haveI : OvlOK (c.withHooks H) := ovlOK_of_core ((Semantics.coreOK_withHooks c H).trans hcore)
  exact tieCons_entailed (c := c.withHooks H) ((tieConsB_withHooks c H a).trans h) i mod hI

/-- **No junk, for every interpretation**: `Γ` entails the no-junk item of every constructor sort
that has a generator, over the sort's generators. -/
theorem inertNoJunk_everyH (c : Semantics) (H : HookParams) {N : Srt} (hN : N ∈ consSorts (c.withHooks H))
    (hg : ((c.withHooks H).gens N).isEmpty = false) :
    Γ (c.withHooks H) ⊧ (KoreAML.Cons.noJunkItem ((c.withHooks H).sortName N)
      (((c.withHooks H).gens N).map (Gen.toK (c.withHooks H)))).pat := by
  intro M _ I hI
  exact sat_cons (c := c.withHooks H) hI (Or.inl ⟨_, noJunkItem_mem (c := c.withHooks H) hN hg, rfl⟩)

/-! ## G4: the inert classes `collectionLaw`, `parametricFunctional`, `vacuousLeft` -/

/-- **The laws of `_List_` are entailed at values, for every interpretation**: an axiom declaration
whose pattern is the associativity, the right unit or the left unit of `_List_`. `_List_` is total
on lists and has no silent point: the value of each side is `hook`'s, whatever H. -/
theorem inertListLaw_everyH (c : Semantics) (hcore : c.coreOK = true) (hs : c.shapesOK = true) (H : HookParams)
    {E : InertEv.LawEqn} (hE : E = InertEv.listAssoc ∨ E = InertEv.listUnitRight ∨ E = InertEv.listUnitLeft)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues (c.withHooks H) ad (KoreAML.trAxiom [] [] ad).pat :=
  InertEv.listLaw_ev (c := c.withHooks H) ((Semantics.coreOK_withHooks c H).trans hcore) hs hE ad hp hsv

/-- **`ite` at a sort is total at values, for every interpretation**: for a parameter symbol
`f : Bool × S × S → S` implemented by the registry's `kIte`, an axiom declaration whose pattern is
the `functional` sentence of `f` (`InertEv.iteFunPat`). The sentence is the instance at the sort S
of the text's sentence over a sort variable. `kIte` has no silent point: the value is that of the
second or of the third argument, whatever H. -/
theorem inertIteFunctional_everyH (c : Semantics) (hcore : c.coreOK = true) (hs : c.shapesOK = true)
    (H : HookParams) {k : ParamSig} (hk : c.lookupParam k.sig.name = some k) (himpl : k.impl = some kIte)
    {S : Srt} (hargs : k.sig.args = [Srt.bool, S, S]) (hres : k.sig.result = S)
    (hS : S < nRegSorts + c.sortNames.length) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = InertEv.iteFunPat c k.sig.name S) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues (c.withHooks H) ad (KoreAML.trAxiom [] [] ad).pat :=
  InertEv.iteFun_entailed (c := c.withHooks H) ((Semantics.coreOK_withHooks c H).trans hcore) hs hk himpl hargs
    hres hS ad hp hsv

/-- **A rewrite axiom with an empty left side is entailed, for every interpretation**: where the
left side is one `Parse.vacuous` accepts (the condition of `Parse.classifyAxiom`), with any
declarations and no alias. The proof reads definedness alone, and so no interpretation. -/
theorem inertVacuousLeft_everyH (c : Semantics) (H : HookParams) {a : Kore.Axiom}
    (hv : (match a.pattern with
      | .rewrites _ (.and _ [l, _]) _ => Parse.vacuous l
      | _ => false) = true)
    (decls : List KoreAML.SymbolDecl) (i : Nat) (mod : String) :
    Γ (c.withHooks H) ⊧ (KoreAML.trAxiom decls [] ⟨i, mod, a⟩).pat :=
  InertEv.vacuousLeft_entailed (c.withHooks H) hv decls i mod

end KCore.Guards

#print axioms KCore.Guards.g0_refuted
#print axioms KCore.Guards.eval_noValue_of_ens_fails
#print axioms KCore.Guards.Ens.half_neg4_gamma
#print axioms KCore.Guards.EnsOwise.half_neg4_gamma
#print axioms KCore.Guards.Proj.projInt_dotk_open
#print axioms KCore.Guards.ProjK.projInt_none_off
#print axioms KCore.Guards.ProjK.projInt_off_gamma
#print axioms KCore.Guards.ProjK.inverse_holds
#print axioms KCore.Guards.total_of_restTotal
#print axioms KCore.Guards.fnRest_nil_eq_paramVal
#print axioms KCore.Guards.setIdem_bot
#print axioms KCore.Guards.fnRest_nil_eq_paramVal_everyH
#print axioms KCore.Guards.rest_undetermined
#print axioms KCore.Guards.RestOpen.F0_undetermined
#print axioms KCore.Guards.setIdem_gamma
#print axioms KCore.Guards.setIdem_everyH
#print axioms KCore.Guards.setIdem_reached
#print axioms KCore.Guards.ruleRightDefined_weaker
#print axioms KCore.Guards.existsDropped_weaker
#print axioms KCore.Guards.existsDropped_empty
#print axioms KCore.Guards.inertCons_everyH
#print axioms KCore.Guards.inertNoJunk_everyH
#print axioms KCore.Guards.inertListLaw_everyH
#print axioms KCore.Guards.inertIteFunctional_everyH
#print axioms KCore.Guards.inertVacuousLeft_everyH
#print axioms KCore.Guards.DevOr.or_steps
#print axioms KCore.Guards.DevOr.or_one_stuck
#print axioms KCore.Guards.DevTop.top_steps
#print axioms KCore.Guards.DevTop.top_unread_stuck
#print axioms KCore.Guards.DevEx.ex_steps
#print axioms KCore.Guards.DevEx.ex_unread_stuck
#print axioms KCore.Guards.DevCeil.ceil_steps
#print axioms KCore.Guards.DevCeil.ceil_defined_steps
#print axioms KCore.Guards.DevAndBool.and_steps
#print axioms KCore.Guards.DevAndBool.and_first_steps
#print axioms KCore.Guards.DevReqOr.reqOr_steps
#print axioms KCore.Guards.DevReqOr.reqOr_orBool_stuck
#print axioms KCore.Guards.DevAndEns.andEns_values
#print axioms KCore.Guards.DevAndEns.andEns_asRequires_H7
#print axioms KCore.Guards.DevBot.bot_values
#print axioms KCore.Guards.DevBot.bot_unread_value
#print axioms KCore.Guards.DevOrBot.orBot_value
#print axioms KCore.Guards.DevOrBot.orBot_unread_H7
#print axioms KCore.Guards.DevRefl.conf_value
#print axioms KCore.Guards.DevRefl.go_step_Hk
#print axioms KCore.Guards.DevKey.key_steps
#print axioms KCore.Guards.DevKey.look2_Hk
#print axioms KCore.Guards.DevPrio.prio_gamma_of_text
#print axioms KCore.Guards.DevOwise.owise_values
#print axioms KCore.Guards.DevOwise.owise_unread_H9

/-! ## The table of readings (DONE-0 C6)

One entry for every constructor of `Parse.ReadingNote`, `Parse.InertReason` and
`Parse.UnreadReason`: its guard theorem, its "point is reached" companion (an H, or a semantics, at
which the reading without its guard differs), the invariants it cites, or the reader test that
guards it where no value is at stake; otherwise `pending`, with the ticket that owes the entry and
what exists so far. Each table is a `match` with no wildcard arm, so a constructor added to
`Parse.lean` without an entry fails this file ("missing cases"); `test/guards.sh` checks that no
wildcard arm is between the `table:begin` and `table:end` lines, checks each pointer into another
test file, and prints the pending entries.

A pointer to a declaration of this file or of the library is a name literal (``n``), resolved when
the file is elaborated: a guard renamed or deleted fails the file. The other test files are not
modules this file can import, so a pointer into one is the file and a text it holds (a theorem's
name, or the `#guard_msgs` of its verdict test), checked by `test/guards.sh`.

The four readings REVIEW-RN finding 7 found without a note each have a `ReadingNote` constructor
now (`unnoted` below lists them), so they are entries of the first table.
-/

namespace KCore.Guards.Table

open Lean KCore.Parse

/-- Where a guard, a companion or a reader test is. -/
inductive GuardRef where
  /-- A declaration of this file or of the library, by a name literal. -/
  | decl (n : Name)
  /-- Another test file (relative to the package root) and a text it holds. -/
  | test (file needle : String)

/-- How far an entry is. -/
inductive GuardStatus where
  /-- The guard, its companion and its invariant are named, and a guard is a declaration stated about
  `c.withHooks H` for every `H : HookParams` (C6's form; the `run_cmd` after the lists checks it). -/
  | guarded
  /-- No value is at stake: the reading decides which sentences are part of the definition, and the
  reader test that fixes its verdict is named. -/
  | readerTest
  /-- Not yet: the ticket that owes the entry. -/
  | pending (ticket : String)

structure GuardEntry where
  status : GuardStatus
  guard : List GuardRef := []
  companion : List GuardRef := []
  invariant : List Name := []
  note : String

def GuardRef.show : GuardRef → String
  | .decl n => n.toString
  | .test f n => s!"{f}#{n}"

def GuardStatus.show : GuardStatus → String
  | .guarded => "guarded"
  | .readerTest => "reader-test"
  | .pending t => s!"pending {t}"

def GuardEntry.line (ctor : String) (e : GuardEntry) : String :=
  let refs := fun (rs : List GuardRef) => ";".intercalate (rs.map GuardRef.show)
  s!"GUARD|{ctor}|{e.status.show}|{refs e.guard}|{refs e.companion}|{";".intercalate (e.invariant.map toString)}|{e.note}"

-- table:begin
def readingNote : ReadingNote → GuardEntry
  | .reflectionAsOwn =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevRefl.conf_value, .decl ``KCore.Guards.fnRest_nil_eq_paramVal_everyH],
      companion := [.decl ``KCore.Guards.DevRefl.go_step_Hk, .test "test/Configuration.lean" "stuck_go"],
      invariant := [``KCore.Semantics.paramVal],
      note := "on e6-configuration's text, every H: #configuration's value is H's answer, kept where it is of sort K (conf_value), as a function with no clause (G6); the point is reached: under Hk go steps to wrap(.K), under HookParams.none it has no successor (stuck_go), so the text fixes neither; the statement in Γ's models (param_undetermined, REVIEW-RN section 3: over all H, Γ entails neither ⊥ nor a value) is not written" }
  | .streamRule =>
    { status := .readerTest,
      guard := [.test "test/StreamIO.lean" "#guard_msgs"],
      note := "the sentence is a rule of the definition read as written, its hooks parameter symbols (REVIEW-RN RN7): no value-level claim" }
  | .ruleRightDefined =>
    { status := .pending "GUARD.final",
      guard := [.decl ``KCore.Guards.ruleRightDefined_weaker],
      companion := [.decl ``KCore.Faithful.UndefRhsWitness.not_model_text,
        .decl ``KCore.Faithful.UndefRhsWitness.gamma_of_text],
      invariant := [``KCore.Faithful.prioRuleK],
      note := "G8 names no H and covers only rules with exs = [] and pre and post top; owed: a statement about c.withHooks H for every H, and the rules with existential variables, pre or post once R3.flip lands; the companion is a semantics whose text reading has no model while Γ's does" }
  | .projectionDomainAsClause =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.ProjK.projInt_none_off, .decl ``KCore.Guards.ProjK.projInt_off_gamma,
        .decl ``KCore.Guards.ProjK.dotk_off],
      companion := [.decl ``KCore.Guards.Proj.projInt_dotk_open],
      invariant := [``KCore.Semantics.coreOK, ``KCore.Eval.ensFails, ``KCore.Semantics.fnRest],
      note := "G3 on krust's projapp text, every H; the companion is K 7.1.337's starinit text, which states no domain axiom, where H0 gives project:Int(.K) a value" }
  | .orSplit =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevOr.or_steps, .test "test/Connectives.lean" "orSplit"],
      companion := [.decl ``KCore.Guards.DevOr.or_one_stuck],
      invariant := [``KCore.Cert.checkStep_withHooks, ``KCore.Cert.stuckCheck_sound],
      note := "on e7-guardors' text (c(a ∨ b) => a), every H: c(a) and c(b) each step to a; the companion is the text read as its first disjunct's rule alone, where c(b) has no successor under every H (no function is at the point, so no H separates the two readings: the semantics does)" }
  | .topAsVariable =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevTop.top_steps, .test "test/Connectives.lean" "topAsVariable"],
      companion := [.decl ``KCore.Guards.DevTop.top_unread_stuck],
      invariant := [``KCore.Cert.checkStep_withHooks, ``KCore.Cert.stuckCheck_sound],
      note := "on e3-ml-rule-lhs-top's text (c(⊤) => a), every H: c(b) and c(d(a, b)) each step to a; the companion is the text with the axiom not read, where c(b) has no successor under every H (no function is at the point)" }
  | .existsAsVariable =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevEx.ex_steps, .test "test/Connectives.lean" "existsAsVariable"],
      companion := [.decl ``KCore.Guards.DevEx.ex_unread_stuck],
      invariant := [``KCore.Cert.checkStep_withHooks, ``KCore.Cert.stuckCheck_sound],
      note := "on e3-ml-rule-lhs-exists' text (c(∃Y. d(Y, b)) => a), every H: c(d(a, b)) and c(d(b, b)) each step to a and c(d(b, a)) has no successor; the companion is the text with the axiom not read, where c(d(b, b)) has no successor under every H (no function is at the point)" }
  | .andAsEnsures =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevAndEns.andEns_values, .test "test/Connectives.lean" "andAsEnsures"],
      companion := [.decl ``KCore.Guards.DevAndEns.andEns_asRequires_H7],
      invariant := [``KCore.Eval.ensFails, ``KCore.Semantics.fnRest, ``KCore.Cert.evalFC_withHooks],
      note := "on e3-ml-eq-rhs-and-pred's text (f(X) = X ∧ ⌈X >Int 0 = true⌉), every H: f(1) = 1, f(0) has no value and Γ entails f(0) = ⊥; the companion is the predicate read as a requires, where f(0) is a point every clause fails at, 7 under H7" }
  | .andTermsWeaker =>
    { status := .pending "GUARD.final",
      guard := [.test "test/Connectives.lean" "andTermsWeaker"],
      note := "a CE reader device (CE.note-rule-and-weaker); reader tests at the parsed semantics only; the entailment of the read rule by the text's sentence (its docstring) is stated by no theorem, no statement over c.withHooks H, no companion" }
  | .bottomAsEnsures =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevBot.bot_values, .test "test/Connectives.lean" "bottomAsEnsures"],
      companion := [.decl ``KCore.Guards.DevBot.bot_unread_value],
      invariant := [``KCore.Eval.ensFails, ``KCore.Cert.evalFC_withHooks],
      note := "on e3-ml-eq-rhs-bottom's text (f(X) = ⊥ requires X <Int 0 beside f(X) = X [owise]), every H: f(2) = 2, f(-1) has no value and Γ entails f(-1) = ⊥; the companion is the equation with the empty right side not read, where the [owise] clause gives f(-1) = -1 under every H" }
  | .orBottom =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevOrBot.orBot_value, .test "test/Connectives.lean" "orBottom"],
      companion := [.decl ``KCore.Guards.DevOrBot.orBot_unread_H7],
      invariant := [``KCore.Semantics.fnRest, ``KCore.Cert.evalFC_withHooks],
      note := "on e3-ml-eq-rhs-or-bottom's text (f(X) = X ∨ ⊥), every H: f(3) = 3; the companion is the equation not read, where f has no clause and f(3) is the interpretation's, 7 under H7" }
  | .predicateAtBool =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevCeil.ceil_steps, .test "test/Connectives.lean" "predicateAtBool"],
      companion := [.decl ``KCore.Guards.DevCeil.ceil_defined_steps],
      invariant := [``KCore.Cert.checkStep_withHooks, ``KCore.Cert.stuckCheck_sound],
      note := "on e3-ml-req-ceil's text (go(X) => done requires ⌈1 /Int X⌉ beside go(_) => other of priority 60), every H: go(1) steps to other; the companion is the predicate read as holding where 1 /Int X has a value, where go(1) steps to done under every H (no function is at the point)" }
  | .andAtBool =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevAndBool.and_steps, .test "test/Connectives.lean" "andAtBool",
        .test "test/AndBoolSingle.lean" "#guard_msgs"],
      companion := [.decl ``KCore.Guards.DevAndBool.and_first_steps, .test "test/AndBoolNotStrict.lean" "not_strict"],
      invariant := [``KCore.Cert.checkStep_withHooks, ``KCore.Cert.stuckCheck_sound],
      note := "on e3-ml-req-and-var's text (go(B) => done requires true ∧ B), every H: go(true) steps to done and go(false) has no successor; the companions are the requires read as its first conjunct alone, where go(false) steps to done under every H, and an interpretation where the strict conjunction under an [owise] negation is not the text's intersection (not_strict), which is why an equation reads the note only at single-valued conjuncts" }
  | .requiresOrSplit =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevReqOr.reqOr_steps, .test "test/Connectives.lean" "requiresOrSplit"],
      companion := [.decl ``KCore.Guards.DevReqOr.reqOr_orBool_stuck],
      invariant := [``KCore.Cert.checkStep_withHooks, ``KCore.Cert.stuckCheck_sound],
      note := "on e3-ml-req-or-undef's text (go(X) => done requires X >=Int 0 ∨ 10 /Int X >Int 0), every H: go(0) steps to done and go(-1) has no successor; the companion is the two disjuncts read as one requires A1 orBool A2, which has no value at 0 (10 /Int 0 has none), where go(0) has no successor under every H" }
  | .setVarInDropped =>
    { status := .pending "GUARD.final",
      guard := [.decl ``KCore.setvar_in_drop, .test "test/SetVarOwise.lean" "f_one"],
      note := "setvar_in_drop is the entailment on the translated sentence, f_one an evaluation at the parsed semantics; no statement over c.withHooks H, no companion; no GUARD ticket names this constructor" }
  | .keyFunctionAsRequires =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevKey.key_steps, .test "test/KeyFunction.lean" "#guard_msgs"],
      companion := [.decl ``KCore.Guards.DevKey.look2_Hk, .test "test/KeyFunction.lean" "look(2): []"],
      invariant := [``KCore.Cert.checkStep_withHooks, ``KCore.Semantics.fnRest],
      note := "on keyfn-partial's text, every H: look(1) steps to the entry of k(1), kf(1) being k(1) by its equation; the point is reached: kf(2) is a point where no equation applies, under Hk it is k(1) and look(2) steps to that entry, under HookParams.none look(2) has no successor (the compiled step, AtNone.steps); the bridge between the text's rule and the read one (REVIEW-RN RN12) is not written: the kernel has no pattern applying a function (functionInPattern)" }
  | .equationPriority =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevPrio.prio_gamma_of_text, .decl ``KCore.Faithful.PrioTextWitness.gamma_of_text],
      companion := [.decl ``KCore.Faithful.PrioTextWitness.not_model_text, .decl ``KCore.Faithful.PrioTextWitness.has_model],
      invariant := [``KCore.Faithful.prioEquation, ``KCore.Faithful.lowerClauses],
      note := "on PrioTextWitness.c (f() = 1 of priority 50, f() = 2 of priority 60), every H: a model of the theory with each equation under its own premise, as the text writes it, is a model of Γ (c.withHooks H), whose second equation is under the negation of the first; the point is reached: the text's theory has no model there and Γ has one; one hand-built semantics: the entailment for every semantics (as G8 for rules) is not written, the competitors' bound variables changing the translated sentence's variable table" }
  | .owiseAsPriority =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.DevOwise.owise_values, .test "test/OwisePriority.lean" "#guard_msgs",
        .test "test/OwiseSeveral.lean" "f_prios"],
      companion := [.decl ``KCore.Guards.DevOwise.owise_unread_H9],
      invariant := [``KCore.Faithful.prioEquation, ``KCore.Cert.evalFC_withHooks, ``KCore.Semantics.fnRest],
      note := "on owise2's text (two equations and two [owise] equations), every H: f(1, 5) = 5 and f(7, 1) = 7 by the [owise] equations, f(1, 0) = 1 by the equation the [owise] one does not override; the companion is the [owise] equations not read, where f(1, 5) is a point every clause fails at, 9 under H9; that the text's premise (one negated disjunct per other equation) and Γ's (the clauses of a smaller priority) are one is the reader's check (fnFrom, fnPairs, excludes), stated by no theorem" }
  | .owiseDisjunctNarrower =>
    { status := .pending "GUARD.final",
      guard := [.decl ``KCore.owise_disjunct_narrower],
      companion := [.decl ``KCore.owise_diag_svin],
      note := "both are stated on translated sentences, not over c.withHooks H; no GUARD ticket names this constructor" }
  | .identityAlias =>
    { status := .pending "GUARD.final",
      guard := [.test "test/AliasRhs.lean" "Semantics equal: true"],
      note := "reader tests only: the alias sentence decided the identity on the sentence (aliasIsIdentity), and hw-allpath-alias's Semantics equal to that of its text with the alias removed; no statement over c.withHooks H, no companion; no GUARD ticket names this constructor (added by FIX-core.allpath-alias-read)" }

  | .existsRenamedApart =>
    { status := .pending "GUARD.final",
      guard := [.test "test/ExReader.lean" "exApart_shadow"],
      note := "reader tests only (test/ExReader.lean, site a: the rule read is the rule of the text with the binder spelled with another name; exApart in the kernel); that the axiom and its α-variant denote the same is argued (C3-existentialRhs-decision L1) and stated by no theorem, as for the left side's lhsBind; no statement over c.withHooks H, no companion; no GUARD ticket names this constructor (added by C3.reader-exists-binders)" }
  | .existsDropped =>
    { status := .pending "GUARD.final",
      guard := [.decl ``KCore.Guards.existsDropped_weaker, .decl ``KCore.Guards.existsDropped_empty,
        .test "test/ExReader.lean" "exKept_drop"],
      note := "G9 is stated on translated sentences, not over c.withHooks H, with no premise on the binder's sort and five premises on the numbering of the two sentences' variables, decided by computation at the instance (a sort without a constructor); no companion (the read sentence is the weaker: nothing is refuted); no GUARD ticket names this constructor (added by C3.reader-exists-binders)" }
  | .overloadFunction =>
    { status := .pending "GUARD.final",
      guard := [.decl ``KCore.Faithful.funUncItem_of_funItem, .decl ``KCore.Faithful.injUncItem_of_injItem,
        .test "test/Overloads.lean" "overloadFunction", .test "test/OvlFun.lean" "cons_items"],
      note := "each sentence entails the item read of it (the item is the sentence at fewer arguments), in every interpretation; that the functional, injectivity and distinctness items of a function-overloaded symbol are the uncovered ones is kernel-checked on two hand-built semantics; no statement over c.withHooks H: coreOK admits no function overload yet" }
  | .tokKItem =>
    { status := .guarded,
      guard := [.decl ``KCore.Faithful.noJunk_omitted_refuted, .test "test/TokKItem.lean" "tok_refuted",
        .test "test/TokKItem.lean" "text_entails_item", .test "test/HashSort.lean" "tokKItem"],
      companion := [.test "test/TokKItem.lean" "consistent", .test "test/TokKItem.lean" "text_not_entailed"],
      invariant := [``KCore.Semantics.sortsBelowKItem, ``KCore.Faithful.consItemsK, ``KCore.Semantics.gens],
      note := "for every semantics with coreOK and every H, a no-junk sentence of a constructor sort that leaves out a non-open injection inj{a, N} from a sort with a value, its generators injections from sorts incomparable with a and sharing no lower bound with it, has no model with Γ (c.withHooks H) (noJunk_omitted_refuted: Cons-Fun and Cons-Dist); on hashsort's text (syntax #Tok [token]; KItem's no-junk sentence, axiom 125, lists 13 injections and not inj{#Tok, KItem}; no subsort axiom states #Tok < KItem; the equations of is#Tok apply inj{#Tok, KItem}), where the reading adds the subsort #Tok < KItem: the sentence entails Γ's no-junk item of KItem in every interpretation with definedness (text_entails_item), Γ with it has no model for every H (tok_refuted), and Γ has one (consistent), so Γ does not entail it (text_not_entailed)" }

def inertReason : InertReason → GuardEntry
  | .import =>
    { status := .readerTest,
      guard := [.test "test/imp-account.expected" "import"],
      note := "no value is at stake: an import states no axiom; kompile writes the sentences of the imported modules into the user module, where each is classified by its own form, and K's prelude is read as a whole (the account's first line says whether it agrees); imp's account counts the import apart" }
  | .claim =>
    { status := .readerTest,
      guard := [.test "test/constructs/rows.toml" "Sentence:kw:claim"],
      note := "C1's class use (R-1): a claim is a statement to prove, a use of the definition and no axiom of its theory, so Γ holds nothing for it; kompile refuses a claim in a definition (fixture e1-claim), so no kompiled text holds one" }
  | .simplification =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.ProjK.inverse_holds, .test "test/TieEns.lean" "lib166"],
      invariant := [``KCore.Semantics.coreOK, ``KCore.Faithful.ΓDomains],
      note := "at values, for every H, on two texts: the selector-inverse lemma of krust's projapp text holds at Eval's values (G4, inverse_holds); ens's sentence 166, I -Int 0 = I, is satisfied at every value of Int in every model of Γ (lib166). One lemma per text, not every simplification of the library: the class's claim (a lemma follows from the other sentences) is checked where a row lists the sentence" }
  | .distinctCtors =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.inertCons_everyH, .test "test/TieEns.lean" "cons_entailed"],
      invariant := [``KCore.Faithful.consItemsK, ``KCore.Faithful.tieConsB],
      note := "for every semantics with coreOK and every H, Γ entails a no-confusion sentence of two generators that tieConsB accepts (the items Cons-Fun of both and Cons-Dist); the fixture sentences are ens's distinctness sentences among the 30 of TieEns.cons_entailed, each accepted by decision (cons_checked) and translated without its declarations (cons_trS)" }
  | .injectivity =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.inertCons_everyH, .test "test/TieEns.lean" "cons_entailed"],
      invariant := [``KCore.Faithful.consItemsK, ``KCore.Faithful.tieConsB],
      note := "as distinctCtors, for the no-confusion sentence of one generator (the items Cons-Fun and Cons-Inj); the fixture sentences are ens's injectivity sentences among the 30 of TieEns.cons_entailed" }
  | .noJunk =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.inertNoJunk_everyH, .test "test/TieEns.lean" "nojunk_items",
        .test "test/TieEns.lean" "nojunk_trivial_entailed", .test "test/TieEns.lean" "nojunk_kitem_entailed"],
      invariant := [``KCore.Faithful.consItemsK, ``KCore.Semantics.gens],
      note := "for every semantics and every H, Γ entails the no-junk item of a constructor sort over its generators; on ens the sentences of the sorts with generators are those items (116 to 120, 122, 123: nojunk_items), KItem's is the item with its disjuncts in the text's order and is entailed (125), and those of the sorts without a generator are valid (115, 121, 124)" }
  | .collectionLaw =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.inertListLaw_everyH, .test "test/InertEvFixtures.lean" "list_laws_ens"],
      invariant := [``KCore.Semantics.coreOK, ``KCore.Faithful.ΓDomains],
      note := "at values, for every semantics with coreOK and shapesOK and every H: the associativity and the two unit sentences of _List_ hold in every model of Γ at the valuations sending their variables to values, each side's value being hook's (_List_ is total on lists and has no silent point); the fixture sentences are ens's 53, 54, 55 (list_laws_ens). Not stated: the laws of _Map_ and _Set_ (ens 57 to 60, 62, 63), whose concatenation has no value at a common key or member, and those of a cell collection's or a range map's concatenation" }
  | .parametricFunctional =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.inertIteFunctional_everyH, .test "test/InertEvFixtures.lean" "ite_int_lazy"],
      invariant := [``KCore.Semantics.coreOK, ``KCore.Faithful.ΓDomains],
      note := "at values and at an instance, for every semantics with coreOK and shapesOK and every H: the functional sentence of a parameter ite{S} implemented by kIte holds in every model of Γ at the valuations sending its variables to values, from the graph ΓDomains states of the parameter. The text's sentence is over a sort variable, which no value has for its sort, so it is not stated at values; the fixture is lazy's sentence 39 at SortInt{} (ax39_text, ite_instance, ite_int_lazy). Not stated: an instance of a symbol of the library's parametric sorts, or of a user's sort-parametric function declared total, whose totality where it has no equation is a condition on H (ParamPres.total)" }
  | .vacuousLeft =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.inertVacuousLeft_everyH, .test "test/InertEvFixtures.lean" "vacuous_lhs_bottom",
        .test "test/Connectives.lean" "vacuousLeft"],
      invariant := [``KCore.Parse.vacuous],
      note := "for every semantics and every H, Γ entails a rewrite axiom whose left side Parse.vacuous accepts: the left side's translation holds of no element (InertEv.vacuous_none, by recursion on the pattern), so the axiom holds in every interpretation with definedness; the proof reads no hook. Translated without aliases: an alias application is not expanded, and a text with an alias declaration is refused (aliasDeclaration). The fixture is the rule of e3-ml-rule-lhs-bottom (vacuous_lhs_bottom)" }

def unreadReason : UnreadReason → GuardEntry
  | .cellCollectionInjection =>
    { status := .readerTest,
      guard := [.test "test/CellCollection.lean" "#guard_msgs"],
      note := "which sentences are part of the reading; a read sentence applying the injection is refused (REVIEW-RN RN9)" }
  | .macroUnused =>
    { status := .readerTest,
      guard := [.test "test/MacroUnused.lean" "#guard_msgs"],
      note := "which sentences are part of the reading: the four macro and alias declarations of e2-macro's text, which applies none of them (kompile has expanded them), are not read, and the text is read with nothing unaccounted; an application would be refused at the applying sentence (macroSymbol)" }
  | .parametricUnused =>
    { status := .readerTest,
      guard := [.test "test/ParametricUnused.lean" "#guard_msgs"],
      note := "the declaration is read only through the instances a sentence applies (REVIEW-RN RN9)" }
  | .setIdempotence =>
    { status := .guarded,
      guard := [.decl ``KCore.Guards.setIdem_gamma, .decl ``KCore.Guards.setIdem_everyH,
        .decl ``KCore.Guards.setIdem_bot],
      companion := [.test "test/TieEns.lean" "idem_refuted", .decl ``KCore.Guards.setIdem_reached],
      invariant := [``KCore.silentKey_fixed, ``KCore.Faithful.ΓDomains],
      note := "G7: in every semantics and under every H, Γ holds _Set_(S1, S2) = ⊥ where hook gives the concatenation no value (setIdem_gamma; at {1} {1}, setIdem_everyH), so the idempotence axiom, which gives _Set_(K, K) the value K, is no part of the reading: Γ with it has no model, for every H (idem_refuted, on ens's sentence 61); the point is reached (setIdem_reached): were _Set_ a key of silentTable, its value at a common member would be the interpretation's" }
  | .overloadConfusion =>
    { status := .readerTest,
      guard := [.test "test/Overloads.lean" "overloadConfusion"],
      note := "the kernel states the distinctness at uncovered arguments only (KoreAML.Cons.distUncItem); the account lists the axioms not read" }
  | .noSortPredicate =>
    { status := .readerTest,
      guard := [.test "test/RangeMap.lean" "isNoPredName"],
      note := "the theory has no symbol isX for a sort the registry gives no predicate; the sixth of the six UnreadReason constructors GUARD.unread counts" }
-- table:end

def readingNotes : List ReadingNote :=
  [.reflectionAsOwn, .streamRule, .ruleRightDefined, .projectionDomainAsClause, .orSplit, .topAsVariable,
   .existsAsVariable, .andAsEnsures, .andTermsWeaker, .bottomAsEnsures, .orBottom, .predicateAtBool, .andAtBool,
   .requiresOrSplit, .setVarInDropped, .keyFunctionAsRequires, .equationPriority, .owiseAsPriority,
   .owiseDisjunctNarrower, .identityAlias, .existsRenamedApart, .existsDropped,
   .overloadFunction, .tokKItem]

def inertReasons : List InertReason :=
  [.import, .claim, .simplification, .distinctCtors, .injectivity, .noJunk, .collectionLaw,
   .parametricFunctional, .vacuousLeft]

def unreadReasons : List UnreadReason :=
  [.cellCollectionInjection, .macroUnused, .parametricUnused, .setIdempotence, .overloadConfusion,
   .noSortPredicate]

/-- REVIEW-RN finding 7's readings without a note, and the constructor each has now. -/
def unnoted : List (String × ReadingNote) :=
  [("the rule axiom's premise ⌈rhs ∧ ens⌉", .ruleRightDefined),
   ("a key function read as a requires", .keyFunctionAsRequires),
   ("the priority form of a function's equations", .equationPriority),
   ("[owise] as priority 200", .owiseAsPriority)]

example : readingNotes.Nodup ∧ inertReasons.Nodup ∧ unreadReasons.Nodup := by decide

-- The three lists hold every constructor (with `Nodup`, each once), so the printed table is the
-- whole of each `match`.
run_cmd do
  let env ← getEnv
  for (ind, n) in [(``ReadingNote, readingNotes.length), (``InertReason, inertReasons.length),
      (``UnreadReason, unreadReasons.length)] do
    let some (.inductInfo i) := env.find? ind | throwError "guards: no inductive {ind}"
    unless i.ctors.length == n do
      throwError "guards: {ind} has {i.ctors.length} constructors, its list {n}"

/-- A type with a binder of type `HookParams` (an `∀ H`, possibly after other binders). -/
def hasHookBinder : Expr → Bool
  | .forallE _ t b _ => t.isConstOf ``KCore.HookParams || hasHookBinder b
  | _ => false

-- C6's literal form: an entry is `guarded` only where one of its guards is a declaration whose type
-- quantifies over `H : HookParams` and states something about `Semantics.withHooks` (a statement
-- about `c.withHooks H` for every H). A pointer into another test file is not checked here, so it
-- never makes an entry guarded alone.
run_cmd do
  let env ← getEnv
  let everyH := fun (n : Name) => match env.find? n with
    | some ci => hasHookBinder ci.type && (ci.type.find? (·.isConstOf ``KCore.Semantics.withHooks)).isSome
    | none => false
  let entries : List (String × GuardEntry) :=
    readingNotes.map (fun r => (reprStr r, readingNote r)) ++
    inertReasons.map (fun r => (reprStr r, inertReason r)) ++
    unreadReasons.map (fun r => (reprStr r, unreadReason r))
  for (ctor, e) in entries do
    if let .guarded := e.status then
      unless e.guard.any (fun | .decl n => everyH n | .test _ _ => false) do
        throwError "guards: {ctor} is marked guarded, but no guard of it is a declaration stated about c.withHooks H for every H : HookParams"

/-- REVIEW-RN section 3's minimum (DONE-0 C6, "Minimum content"), each with its guards: declarations
of this file stated about `c.withHooks H` for every `H : HookParams` (the `run_cmd` below checks each
one's form). G3 is not void: krust's text holds the selector-domain axiom (`ProjK`), K 7.1.337's
does not (`Proj.projInt_dotk_open`). G4 is per inert class (`inertReason`). -/
def minimum : List (String × List Name) :=
  [("G1", [``KCore.Guards.Ens.half_neg4_none, ``KCore.Guards.Ens.half_neg4_gamma]),
   ("G2", [``KCore.Guards.EnsOwise.half_neg4_none, ``KCore.Guards.EnsOwise.half_neg4_gamma]),
   ("G3", [``KCore.Guards.ProjK.projInt_none_off, ``KCore.Guards.ProjK.projInt_off_gamma]),
   ("G5", [``KCore.Guards.total_of_restTotal]),
   ("G6", [``KCore.Guards.fnRest_nil_eq_paramVal_everyH]),
   ("G7", [``KCore.Guards.setIdem_gamma, ``KCore.Guards.setIdem_everyH]),
   ("rest_undetermined", [``KCore.Guards.rest_undetermined])]

run_cmd do
  let env ← getEnv
  for (g, ns) in minimum do
    for n in ns do
      let some ci := env.find? n | throwError "guards: minimum {g}: no declaration {n}"
      unless hasHookBinder ci.type && (ci.type.find? (·.isConstOf ``KCore.Semantics.withHooks)).isSome do
        throwError "guards: minimum {g}: {n} is not stated about c.withHooks H for every H : HookParams"

#eval show IO Unit from do
  for (g, ns) in minimum do IO.println s!"GUARD-MINIMUM|{g}|{";".intercalate (ns.map toString)}"

#eval show IO Unit from do
  let short := fun (s : String) => (s.splitOn "Parse.").getLast!
  for r in readingNotes do IO.println ((readingNote r).line (short (reprStr r)))
  for r in inertReasons do IO.println ((inertReason r).line (short (reprStr r)))
  for r in unreadReasons do IO.println ((unreadReason r).line (short (reprStr r)))
  for (w, r) in unnoted do IO.println s!"GUARD-UNNOTED|{w}|{short (reprStr r)}"

end KCore.Guards.Table
