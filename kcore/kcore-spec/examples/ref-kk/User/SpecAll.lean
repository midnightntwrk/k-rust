/-
  `Spec` holds of every evaluation of kore.k at `K₀ sig`, for `d` that `execReady` accepts with
  the kore.k definition `E` (`spec_all`): the thirteen step cases are those of the terms
  (User.SpecCb's `stepCases_terms_c13`: `eval`, `evalTs`, `ensure`, `strictHook`) and those of the
  walk of the clauses (User.SpecClauses' `stepCases_clauses_ksc`), each with no hypothesis, and
  `spec_of_steps` (User.SpecMotive) is the induction.

  What it gives at three calls, with `hr`, `hE` the only hypotheses on `d` and the premises the
  call's clause of `Spec` asks of the call:

  - `eval_spec`: `eval(D, T)` at the instance `t` of a term `tm` under `σ`, where the term is well
    sorted and `σ` gives its variables values of their sorts with kore.k literals (`TermOK_ksm`):
    the encoding of a result `EvalTerm (d₀ d) σ tm` has. `eval_spec_en`: the same of a right side
    with its ensures.
  - `apply_spec`: `apply(D, F, As)` at the encodings of values `ws` of the argument sorts of the
    function `f` of `d₀ d`: the encoding of a result `Eval (d₀ d) f ws` has. The sorts are needed:
    kore.k's `match` of a variable reads no sort, so `f(X:Int) => X` gives kore.k a value at a
    `Bool` argument where no clause of `f` matches in `d₀ d`. `apply_ctor_spec`: where `f` is no
    function, the constructor application.
  - `tryCl_none`: `tryCl` at a clause of the function `f` at values of its argument sorts with
    the result `none`: the clause fails.

  The literals of values of a function's argument sorts have a kore.k form
  (`litsVL_of_sorts_ksa`): no argument sort is `Float` under `encodable`.
-/
import User.SpecCb
import User.SpecClauses

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The step cases and the induction -/

/-- **The thirteen step cases**, with no hypothesis. -/
theorem stepCases_all_ksa (d : Semantics) (E : D) : ∀ f ∈ specFns, StepCase d E f := by
  intro f hf
  obtain ⟨h464, h467, h463, h508⟩ := stepCases_terms_c13 d E
  have hcl := stepCases_clauses_ksc d E
  rcases hf with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, hf⟩⟩⟩⟩
  · exact h464
  · exact h467
  · exact h463
  · exact h508
  · exact hcl f hf

/-- **`Spec` holds of every evaluation of kore.k.** -/
theorem spec_all {d : Semantics} {E : D} (hr : CExec.execReady d = true) (hE : encDef d = some E)
    {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval (K₀ sig) f vs r) :
    Spec d E f vs r :=
  spec_of_steps hr hE (stepCases_all_ksa d E) h

/-! ## The literals of values of a function's argument sorts -/

/-- Each member of values with the sorts `ss` has one of them. -/
theorem sortOf_mem_ksa {c : Semantics} : ∀ {ws : List GroundTerm} {ss : List Srt},
    c.sortsOf ws = some ss → ∀ v ∈ ws, ∃ s ∈ ss, c.sortOf v = some s
  | [], _, _, v, hv => nomatch hv
  | w :: ws, ss, h, v, hv => by
    simp only [Semantics.sortsOf] at h
    split at h
    · next s ss' hw hws =>
      cases h
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨s, List.mem_cons_self .., hw⟩
      · obtain ⟨s', hm, hs'⟩ := sortOf_mem_ksa hws v hv
        exact ⟨s', List.mem_cons_of_mem _ hm, hs'⟩
    · cases h

/-- **Values of a function's argument sorts have kore.k literals**: no argument sort of a
function is `Float` under `encodable`. -/
theorem litsVL_of_sorts_ksa {d : Semantics} (hr : CExec.execReady d = true)
    (hc : encodable d = true) {fn : Fn} (hfn : fn ∈ (d₀ d).allFns) {ws : List GroundTerm}
    (hs : (d₀ d).sortsOf ws = some fn.args) : litsVL ws = true :=
  litsVL_iff.mpr fun v hv => by
    obtain ⟨s, hm, hv'⟩ := sortOf_mem_ksa hs v hv
    exact litsV_kst hr hc hv' fun e => (encodable_facts hc).2.2 (e ▸ sigSorts_fnArg_kst hfn hm)

/-! ## What `Spec` gives at `eval`, `apply` and `tryCl` -/

section
variable {d : Semantics} {E : D}

/-- **`eval` at a term's instance**: the encoding of a result of the term. -/
theorem eval_spec (hr : CExec.execReady d = true) (hE : encDef d = some E) {σ : Subst}
    {tm : Term} {t : T} {r : Option GroundTerm} (hok : TermOK_ksm d σ tm) (ht : Inst d σ tm t)
    (h : Eval (K₀ sig) 464 [embD E, emb t] r) :
    ∃ o, r = some (emb (encR o)) ∧ EvalTerm (d₀ d) σ tm o :=
  (spec_all hr hE h).eval_term hok ht

/-- `eval` at a right side with its ensures: the right side's result where the ensures has the
result `true`, `bot` otherwise. -/
theorem eval_spec_en (hr : CExec.execReady d = true) (hE : encDef d = some E) {σ : Subst}
    {rhs e : Term} {p q : T} {r : Option GroundTerm} (hrhs : TermOK_ksm d σ rhs)
    (he : TermOK_ksm d σ e) (hp : Inst d σ rhs p) (hq : Inst d σ e q)
    (h : Eval (K₀ sig) 464 [embD E, emb (.en p q)] r) :
    ∃ o w, r = some (emb (ensureF (encR w) (encR o))) ∧ EvalTerm (d₀ d) σ rhs o ∧
      EvalTerm (d₀ d) σ e w :=
  (spec_all hr hE h).eval_en hrhs he hp hq

/-- `apply` at the encodings of values, as `CallIs_ksm`. -/
theorem apply_callIs_ksa (hr : CExec.execReady d = true) (hE : encDef d = some E) {f : Sym}
    {ws : List GroundTerm} {r : Option GroundTerm} (lv : litsVL ws = true)
    (h : Eval (K₀ sig) 448 [embD E, .dv 3 (.int (f : Int)), embTs (encTs ws)] r) :
    CallIs_ksm d f ws r := by
  have he : (ws.map some).map encR = encTs ws := by rw [List.map_map, encTs_eq_map]; rfl
  have hS := spec_all hr hE h
  rw [← he] at hS
  have hlv : ∀ v, some v ∈ ws.map some → litsV v = true := fun v hv => by
    obtain ⟨w, hw, e⟩ := List.mem_map.mp hv
    have e' : w = v := Option.some.inj e
    subst e'
    exact litsVL_iff.mp lv w hw
  have hall : allSome (ws.map some) = some ws := _root_.KCore.allSome_map_some ws
  exact ((Spec_apply d E _ _).mp hS f (ws.map some) rfl hlv).2 ws hall

/-- **`apply` at a function**: at the encodings of values of its argument sorts, the encoding of a
result of the function. -/
theorem apply_spec (hr : CExec.execReady d = true) (hE : encDef d = some E) {f : Sym} {fn : Fn}
    {ws : List GroundTerm} {r : Option GroundTerm} (hf : (d₀ d).lookupFn f = some fn)
    (hs : (d₀ d).sortsOf ws = some fn.args)
    (h : Eval (K₀ sig) 448 [embD E, .dv 3 (.int (f : Int)), embTs (encTs ws)] r) :
    ∃ o, r = some (emb (encR o)) ∧ Eval (d₀ d) f ws o :=
  (apply_callIs_ksa hr hE (litsVL_of_sorts_ksa hr (encodable_of_encDef_ksc hE)
    (lookupFn_spec hf).1 hs) h).2 fn hf hs

/-- `apply` at a symbol that is no function: the constructor application. -/
theorem apply_ctor_spec (hr : CExec.execReady d = true) (hE : encDef d = some E) {f : Sym}
    {ws : List GroundTerm} {r : Option GroundTerm} (hf : (d₀ d).lookupFn f = none)
    (lv : litsVL ws = true)
    (h : Eval (K₀ sig) 448 [embD E, .dv 3 (.int (f : Int)), embTs (encTs ws)] r) :
    r = some (emb (.ap (f : Int) (encTs ws))) :=
  (apply_callIs_ksa hr hE lv h).1 hf

/-- **`tryCl` with the result `none`**: the clause fails. -/
theorem tryCl_none (hr : CExec.execReady d = true) (hE : encDef d = some E) {f : Sym} {fn : Fn}
    {ws : List GroundTerm} {cl : Clause} (hw : WalkAt_ksm d f fn ws) (hcl : cl ∈ fn.clauses)
    (h : Eval (K₀ sig) 513 [embD E, embTs (encCl d cl).pats, emb (encCl d cl).req,
      emb (encCl d cl).rhs, embTs (encTs ws)] (some (embRes none))) : Fails (d₀ d) ws cl :=
  (spec_all hr hE h).tryCl_none hw hcl

end

/-! ## Checks -/

#check @stepCases_all_ksa
#check @spec_all
#check @litsVL_of_sorts_ksa
#check @eval_spec
#check @eval_spec_en
#check @apply_spec
#check @apply_ctor_spec
#check @tryCl_none

open Lean in
#eval show CoreM Unit from do
  for n in [``stepCases_all_ksa, ``spec_all, ``sortOf_mem_ksa, ``litsVL_of_sorts_ksa, ``eval_spec,
      ``eval_spec_en, ``apply_callIs_ksa, ``apply_spec, ``apply_ctor_spec, ``tryCl_none] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
