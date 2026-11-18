/-
  KCore. What the statements assume of the functions of a semantics (`FnHyp`) and the facts `coreOK`
  does not decide (`CoreObligations`, `Obligations`, with `of_nil` where none is named). Two of
  `FnHyp`'s conjuncts are about the theory, not evaluation: the closed conditions over variables the
  patterns do not bind are decided by the text (`OpenDecided`), and the interpretation satisfies the
  laws the text writes for its open generators (`OpenLaws`). Both hold where nothing beyond the
  plain shapes is used (`openDecided_of_plain`, `openLaws_of_plain`); `OpenLaws` holds for every
  semantics without an open generator (`openLaws_of_plain`), and `OpenDecided` for every one that
  reads no confined sort (`openDecided_of_readsConfined`).
-/
import KcoreSpec.Faithful
import KcoreSpec.OpenValues

set_option autoImplicit false

namespace KCore

open Faithful

/-- **What the statements assume of the functions of a semantics**: each function has a result at
every argument list of its sorts, each `[total]` one a value there, any two equations of one
priority of a function are coherent where both apply (`ClausesAgree`), and any two matches of a
clause at one argument list give one result, a clause with existential variables having a result
at each match where it decides (`MatchIndependent`); every closed condition over
variables the patterns do not bind is decided by the text (`OpenDecided`), and the interpretation
satisfies the laws the text writes for its open generators (`OpenLaws`). -/
def FnHyp (c : Semantics) : Prop :=
  (∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c fn.label vs r) ∧
  (∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) ∧
  (∀ fn ∈ c.fns, ClausesAgree c fn) ∧
  (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) ∧
  OpenDecided c ∧ OpenLaws c

/-! ## The new conjuncts where nothing new is used -/

/-- A rule whose left side binds every variable has no open variable. -/
theorem Rule.opens_of_binds {r : Rule} (h : binds r.vars.length (varOccs r.lhs) = true) : r.opens = [] := by
  simp only [Rule.opens, List.filter_eq_nil_iff, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.not_eq_false]
  intro i hi
  simpa using List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- A clause whose patterns bind every variable has no open variable. -/
theorem Clause.opens_of_binds {cl : Clause} (h : binds cl.vars.length (varOccsList cl.pats) = true) :
    cl.opens = [] := by
  simp only [Clause.opens, List.filter_eq_nil_iff, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.not_eq_false]
  intro i hi
  simpa using List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- The new conjuncts of `FnHyp` are true where nothing new is used. -/
theorem needsWitness_of_binds {c : Semantics} {r : Rule}
    (h : binds r.vars.length (varOccs r.lhs) = true) : r.needsWitness c = false := by
  simp [Rule.needsWitness, Rule.reqOpen, Rule.openCondVars, Rule.opens_of_binds h]

theorem Clause.needsWitness_of_binds {c : Semantics} {cl : Clause}
    (h : binds cl.vars.length (varOccsList cl.pats) = true) : cl.needsWitness c = false := by
  simp [Clause.needsWitness, Clause.reqOpen, Clause.openCondVars, Clause.opens_of_binds h]

theorem openDecided_of_plain {c : Semantics}
    (hr : ∀ r ∈ c.rules, r.needsWitness c = false)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false) : OpenDecided c :=
  ⟨fun r hr' h => absurd h (by rw [hr r hr']; decide),
   fun fn hfn cl hcl h => absurd h (by rw [hc fn hfn cl hcl]; decide)⟩

theorem openLaws_of_plain {c : Semantics} (h : ∀ k ∈ c.params, k.raw = false) : OpenLaws c :=
  fun k hk hraw => absurd hraw (by rw [h k hk]; decide)

theorem openTotal_of_plain {c : Semantics} (h : ∀ k ∈ c.params, k.raw = false) : OpenTotal c :=
  fun k hk hraw => absurd hraw (by rw [h k hk]; decide)

/-- What `plain` says of the rules, the clauses and the parameters. -/
theorem Semantics.plain_parts {c : Semantics} (h : c.plain = true) :
    (∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) ∧
    (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) ∧
    (∀ k ∈ c.params, k.raw = false) := by
  simp only [Semantics.plain, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hr, hf⟩, hk⟩, -⟩, -⟩ := h
  exact ⟨fun r hr' => (hr r hr').2, fun fn hfn cl hcl => (hf fn hfn cl hcl).2,
    fun k hk' => by simpa using hk k hk'⟩

/-- `plain` does not read the interpretation of the parameters. -/
theorem Semantics.plain_withHooks (c : Semantics) (H : HookParams) : (c.withHooks H).plain = c.plain := rfl

/-! ## The same under `coreOK`

`coreOK`'s `sortedOK` holds the plain shapes of the rules, clauses and parameters (`rulesPlain`,
`clausesPlain`, `paramsPlain`), the binding of every variable of a rule by its left side where the
values do not decide it otherwise (`rulesPlain`), and the occurrence of every variable of a clause
in it (`clauseSorted`). -/

/-- A clause of a semantics `sortedOK` accepts has a `\top` predicate on its right side. -/
theorem Semantics.sortedOK_clausePost {c : Semantics} (h : c.sortedOK = true) {fn : Fn} (hfn : fn ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) : cl.post = .top := by
  simp only [Semantics.sortedOK, Semantics.clausesPlain, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨-, hpost⟩, -⟩ := h.1.2 fn hfn cl hcl
  exact Cond.eq_top_of_isTop hpost

/-- What `paramsPlain` asks of an open generator (its `raw` branch): no registry hook,
two arguments of its result sort where it has a law, a number outside the registry, no name
like an `ite`'s, and `shapesOK` of the semantics. -/
theorem Semantics.raw_of_paramsPlain {c : Semantics} (h : c.paramsPlain = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    k.impl = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result]) ∧
    nRegSyms ≤ k.sig.name ∧ iteSort? (c.symName k.sig.name) = none ∧
    c.shapesOK = true := by
  simp only [Semantics.paramsPlain, Bool.and_eq_true, List.all_eq_true] at h
  have hp := h.1 k hk
  simp only [hr, ↓reduceIte, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
    Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩ := hp
  refine ⟨h1, fun hl => ?_, h4, h5, h6⟩
  rcases h3 with h3 | h3
  · rw [hl] at h3; cases h3
  · exact h3

/-- What `sortedOK` asks of an open generator (`paramsPlain`'s raw branch). -/
theorem Semantics.raw_of_sortedOK {c : Semantics} (h : c.sortedOK = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    k.impl = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result]) ∧
    nRegSyms ≤ k.sig.name ∧ iteSort? (c.symName k.sig.name) = none ∧
    c.shapesOK = true := by
  simp only [Semantics.sortedOK, Bool.and_eq_true] at h
  exact Semantics.raw_of_paramsPlain h.2 hk hr

/-- What `coreOK` asks of an open generator (`paramsPlain`'s raw branch). -/
theorem Semantics.raw_of_core {c : Semantics} (h : c.coreOK = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    k.impl = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result]) ∧
    nRegSyms ≤ k.sig.name ∧ iteSort? (c.symName k.sig.name) = none ∧
    c.shapesOK = true :=
  Semantics.raw_of_sortedOK (Semantics.coreOK_parts h).1 hk hr

/-- `idsOK` numbers each parameter outside the registry once: their names are without repetition. -/
theorem Semantics.paramsOnce_of_ids {c : Semantics} (h : c.idsOK = true) :
    ((c.params.filter fun k => decide (nRegSyms ≤ k.sig.name)).map (·.sig.name)).Nodup := by
  unfold Semantics.idsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have he : c.ownSyms = _ := h.1.1.2
  have hnd : c.ownSyms.Nodup := by rw [he]; exact List.nodup_range' ..
  unfold Semantics.ownSyms at hnd
  exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1

/-- **The lookups find a raw parameter itself**, where it is numbered outside the registry and
`idsOK` holds: no other parameter bears its number (`paramsOnce_of_ids`), so `lookupParam` and
`lookupOpen` at its name answer it, not another parameter of the same name. -/
theorem Semantics.raw_lookup {c : Semantics} (hids : c.idsOK = true) {k : ParamSig} (hk : k ∈ c.params)
    (hr : k.raw = true) (hreg : nRegSyms ≤ k.sig.name) :
    c.lookupParam k.sig.name = some k ∧ c.lookupOpen k.sig.name = some k := by
  have hnd := Semantics.paramsOnce_of_ids hids
  have huniq : ∀ kp ∈ c.params, kp.sig.name = k.sig.name → kp = k := fun kp hkp he =>
    Faithful.Model.inj_of_nodup_map hnd kp (List.mem_filter.mpr ⟨hkp, by simpa [he] using hreg⟩) k
      (List.mem_filter.mpr ⟨hk, by simpa using hreg⟩) he
  constructor
  · rw [Semantics.lookupParam_eq]
    cases hf : c.params.find? (·.sig.name == k.sig.name) with
    | none => exact absurd (List.find?_eq_none.mp hf k hk) (by simp)
    | some kp =>
      rw [huniq kp (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)]
  · unfold Semantics.lookupOpen
    simp only [hreg, ↓reduceIte]
    cases hf : c.params.find? (fun k' => k'.raw && k'.sig.name == k.sig.name) with
    | none => exact absurd (List.find?_eq_none.mp hf k hk) (by simp [hr])
    | some kp =>
      have h2 := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      rw [huniq kp (List.mem_of_find?_eq_some hf) h2.2]

/-- No constructor and no overloading symbol bears an open generator's name (`genWf`'s flat
conjunct), so neither lookup answers at it. -/
theorem Semantics.raw_noCtor {c : Semantics} (hg : Faithful.genWf c = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    lookupSig c.ctorSigs k.sig.name = none ∧ c.lookupOvl k.sig.name = none := by
  simp only [Faithful.genWf, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.2 k hk
  simp only [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨hc, ho⟩, -⟩ := this
  constructor
  · rw [lookupSig_eq, List.find?_eq_none]
    intro g hgm
    simpa using (hc g hgm).1
  · unfold Semantics.lookupOvl
    rw [List.find?_eq_none]
    intro o ho'
    simpa using (ho o.sig (List.mem_map_of_mem (f := (·.sig)) ho')).1

/-- **`OpenTotal` where the interpretation answers nothing**: each open generator's application to
values of its argument sorts is then its raw application, a value of its result sort
(`paramVal_raw_keep`). From, for each raw parameter, the parameter its name finds (`lookupParam`),
the open generator it is (`lookupOpen`), of its signature, with no registry hook, and its name no
constructor's and no overloading symbol's. -/
theorem openTotal_of_noAnswer {c : Semantics} (hn : ∀ f vs, c.hooks.app f vs = none)
    (h : ∀ k ∈ c.params, k.raw = true → ∃ kp, c.lookupParam k.sig.name = some kp ∧
      c.lookupOpen k.sig.name = some kp ∧ kp.sig = k.sig ∧ kp.impl = none ∧
      lookupSig c.ctorSigs k.sig.name = none ∧ c.lookupOvl k.sig.name = none) : OpenTotal c := by
  intro k hk hr vs hvs
  obtain ⟨kp, hlp, hko, hsig, hi, hc, ho⟩ := h k hk hr
  rw [← hsig] at hvs
  rw [paramVal_raw_keep hlp hi hko hc ho (hn _ _) hvs]
  rfl

/-- What `coreOK` gives of each raw parameter for `openTotal_of_noAnswer`: the parameter and the
open generator its name finds are the raw parameter itself (`raw_lookup`: `paramsPlain`'s raw
branch numbers it outside the registry and `idsOK` numbers it once), with no registry hook
(`raw_of_core`), its name no constructor's and no overloading symbol's (`raw_noCtor`, from
`genWf`'s flat conjunct). -/
theorem Semantics.raw_open_core {c : Semantics} (h : c.coreOK = true) :
    ∀ k ∈ c.params, k.raw = true → ∃ kp, c.lookupParam k.sig.name = some kp ∧
      c.lookupOpen k.sig.name = some kp ∧ kp.sig = k.sig ∧ kp.impl = none ∧
      lookupSig c.ctorSigs k.sig.name = none ∧ c.lookupOvl k.sig.name = none := by
  intro k hk hr
  obtain ⟨hi, -, hreg, -, -⟩ := Semantics.raw_of_core h hk hr
  obtain ⟨hlp, hlo⟩ := Semantics.raw_lookup (Semantics.coreOK_parts h).2.2.2.2 hk hr hreg
  have hfa := (Semantics.coreOK_parts h).2.1
  simp only [Semantics.faithCoreOK, Bool.and_eq_true] at hfa
  obtain ⟨hc, ho⟩ := Semantics.raw_noCtor hfa.1.1.1.1.1.1.1.1.1.1.2 hk hr
  exact ⟨k, hlp, hlo, rfl, hi, hc, ho⟩

/-- **`OpenTotal` at `HookParams.none`** (CN-4 §3.4 V1): where the interpretation answers nothing,
every open generator has a value, its raw application, at every argument list of its sorts. -/
theorem openTotal_none (c : Semantics) (h : c.coreOK = true) : OpenTotal (c.withHooks HookParams.none) :=
  -- the parameters, the lookups and the constructors do not read the interpretation
  openTotal_of_noAnswer (c := c.withHooks HookParams.none) (fun _ _ => rfl) (fun k hk hr => Semantics.raw_open_core (c := c) h k hk hr)

/-- A semantics that reads no confined sort has no rule or clause with an open variable. -/
theorem Semantics.opens_of_readsConfined {c : Semantics} (hrc : c.readsConfined = false) :
    (∀ r ∈ c.rules, r.opens = []) ∧ (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.opens = []) := by
  simp only [Semantics.readsConfined, Bool.or_eq_false_iff, List.any_eq_false] at hrc
  refine ⟨fun r hr => ?_, fun fn hfn cl hcl => ?_⟩
  · have h1 := hrc.1 r hr
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, List.isEmpty_iff] at h1
    exact h1.1.1
  · have h1 := hrc.2 fn hfn
    simp only [List.any_eq_true, not_exists, not_and] at h1
    have h2 := h1 cl hcl
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, List.isEmpty_iff] at h2
    exact h2.1.1

/-- `OpenDecided` of a semantics that reads no confined sort: no rule or clause has an open variable. -/
theorem openDecided_of_readsConfined {c : Semantics} (hrc : c.readsConfined = false) : OpenDecided c :=
  openDecided_of_plain
    (fun r hr => by
      simp [Rule.needsWitness, Rule.reqOpen, Rule.openCondVars, (Semantics.opens_of_readsConfined hrc).1 r hr])
    (fun fn hfn cl hcl => by
      simp [Clause.needsWitness, Clause.reqOpen, Clause.openCondVars,
        (Semantics.opens_of_readsConfined hrc).2 fn hfn cl hcl])

/-- `readsConfined` does not read the interpretation of the parameters. -/
theorem Semantics.readsConfined_withHooks (c : Semantics) (H : HookParams) :
    (c.withHooks H).readsConfined = c.readsConfined := rfl

/-- **The facts `coreOK` does not decide**, for a semantics `c` and a termination certificate `t`:
the functions whose termination neither declaration order nor a decreasing self call at `t`'s
argument shows (`orderObligations`, `Certificates.obligations`) have a result at every argument
list of their sorts, the `[total]` functions `totalOK` does not confirm have a value there
(`totalObligations`), each two equations of one priority of a function `fnExclusiveOK` does not
confirm are coherent (`agreeObligations`, `ClausesAgree`), each clause `clauseFixed` does not show
to fix its variables gives one result at one argument list (`matchObligations`, each a function and
the index of its clause, `MatchIndependent`), and each argument a short-circuiting evaluation may
skip whose value `definedArg` does not show has one wherever it is skipped (`lazyObligations`,
`LazyOcc.Holds`). Each of these conjuncts is over a list of named functions, clauses or
occurrences, all empty in a semantics the deciders confirm (`CoreObligations.of_nil`). The last two
are `FnHyp`'s: the closed conditions over unbound variables are decided (`OpenDecided`), and the
interpretation satisfies the open generators' laws (`OpenLaws`); both hold where the definition is
plain (`openDecided_of_plain`, `openLaws_of_plain`). -/
def CoreObligations (c : Semantics) (t : Certificates) : Prop :=
  (∀ f ∈ c.orderObligations ++ t.obligations c, ∀ fn, c.lookupFn f = some fn →
    ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c f vs r) ∧
  (∀ f ∈ c.totalObligations, ∀ fn, c.lookupFn f = some fn →
    ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c f vs (some v)) ∧
  (∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) ∧
  (∀ p ∈ c.matchObligations, ∀ fn, c.lookupFn p.1 = some fn →
    ∀ cl, fn.clauses[p.2]? = some cl → MatchIndependent c cl) ∧
  (∀ o ∈ c.lazyObligations, o.Holds c) ∧ OpenDecided c ∧ OpenLaws c

theorem CoreObligations.of_nil {c : Semantics} {t : Certificates}
    (h1 : c.orderObligations ++ t.obligations c = [])
    (h2 : c.totalObligations = []) (h3 : c.agreeObligations = [])
    (h4 : c.matchObligations = []) (h5 : c.lazyObligations = [])
    (h6 : c.plain = true := by decide +kernel) : CoreObligations c t :=
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf (List.not_mem_nil),
   fun f hf => by rw [h2] at hf; exact absurd hf (List.not_mem_nil),
   fun f hf => by rw [h3] at hf; exact absurd hf (List.not_mem_nil),
   fun p hp => by rw [h4] at hp; exact absurd hp (List.not_mem_nil),
   fun o ho => by rw [h5] at ho; exact absurd ho (List.not_mem_nil),
   openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts h6).1 r hr))
     (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts h6).2.1 fn hfn cl hcl)),
   openLaws_of_plain (Semantics.plain_parts h6).2.2⟩

/-- The named obligations of a definition: `CoreObligations` of its semantics, with its
certificate as the termination certificate. `Obligations.of_nil`: they hold when none is named
(a generated package then states `obligations_nil`; where some are named, its `sound` and
`complete` take them as a premise). -/
def Obligations (d : Definition) : Prop := CoreObligations d.sem d.cert

theorem Obligations.of_nil {d : Definition} (h1 : d.sem.orderObligations ++ d.cert.obligations d.sem = [])
    (h2 : d.sem.totalObligations = []) (h3 : d.sem.agreeObligations = [])
    (h4 : d.sem.matchObligations = []) (h5 : d.sem.lazyObligations = [])
    (h6 : d.sem.plain = true := by decide +kernel) : Obligations d :=
  CoreObligations.of_nil h1 h2 h3 h4 h5 h6


end KCore
