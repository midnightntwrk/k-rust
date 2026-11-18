/-
  KCore. Termination and totality of the functions (checked layer).

  - `Terminates c f`: at every argument list of its argument sorts, the function `f` has a result
    (an `Eval` derivation, the result possibly `none`); `Total c f`: a value there.
  - A term has a result when each call in it does (`evalTerm_result`): variables, domain values,
    injections and constructors build one; an interpreted hook has one at every argument list
    (`hook` is `some` on every interpreted symbol, possibly `some none`); a parameter symbol has
    `paramVal`'s; an undefined argument makes a call undefined (`EvalTerm.callUndef`). A `#as` has
    no result; no right-hand side holds one (`rhsCtx` does not admit it).
  - A function has a result where the `requires` of its clauses and the right-hand sides of the
    clauses that apply have one (`eval_result`): each clause either applies or fails, by excluded
    middle on its matches, the `requires` evaluated at each.
  - So a function whose callees terminate terminates (`terminates_of_callees`); the generated sort
    predicates call nothing (`sortPreds_terminate`). The well-sortedness that carries the
    hypothesis to the argument lists of the calls is subject reduction (`EvalTerms.sorted`).
  - A function whose self calls decrease (`decreasingOK`) and whose other callees terminate
    terminates (`terminates_of_decreasing`), by induction on the size (`GroundTerm.size`) of the
    argument at the decreasing position: a variable strictly inside a pattern (`strictlyIn`) has a
    strictly smaller value (`strictlyIn_size`).
  - `terminates_of_order`: every function terminates, given the termination of the named ones; by
    induction on the position in the declaration order (a function the order check accepts calls
    only itself, the functions before it and the sort predicates). `CoreObligations.terminates`:
    for a semantics, under `coreOK` and `CoreObligations`; `Obligations.terminates`: for a
    definition, under `wf` and `Obligations`.
  - Totality, from termination: Totals.lean.
-/
import KcoreSpec.SubjectReduction
import KcoreSpec.NamesApart
import KcoreSpec.Params
import KcoreSpec.Statements
import KcoreSpec.Obligations
import KcoreSpec.RightHeldExtend
import KcoreSpec.HoldsCongr
import KcoreSpec.RightHeldHooks

set_option autoImplicit false

namespace KCore

/-- At every argument list of its argument sorts, the function `f` has a result. -/
def Terminates (c : Semantics) (f : Sym) : Prop :=
  ∀ fn, c.lookupFn f = some fn → ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c f vs r

/-- At every argument list of its argument sorts, the function `f` has a value. -/
def Total (c : Semantics) (f : Sym) : Prop :=
  ∀ fn, c.lookupFn f = some fn → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c f vs (some v)

variable {c : Semantics}

/-! ## The calls of a term -/

mutual
  theorem mem_heads_of_callsOf {g : Sym} {us : List Term} :
      ∀ (t : Term), us ∈ callsOf g t → g ∈ Term.heads t
    | .app f ts, h => by
      simp only [callsOf, List.mem_append] at h
      simp only [Term.heads, List.mem_cons]
      rcases h with h | h
      · by_cases hf : (f == g) = true
        · exact Or.inl (beq_iff_eq.mp hf).symm
        · simp [hf] at h
      · exact Or.inr (mem_headsList_of_callsOfList ts h)
    | .inj _ _ t, h => by
      simp only [callsOf] at h
      simp only [Term.heads]
      exact mem_heads_of_callsOf t h
    | .as t _, h => by
      simp only [callsOf] at h
      simp only [Term.heads]
      exact mem_heads_of_callsOf t h
    | .var _, h => by simp [callsOf] at h
    | .dv _ _, h => by simp [callsOf] at h
  theorem mem_headsList_of_callsOfList {g : Sym} {us : List Term} :
      ∀ (ts : List Term), us ∈ callsOfList g ts → g ∈ Term.headsList ts
    | [], h => by simp [callsOfList] at h
    | t :: ts, h => by
      simp only [callsOfList, List.mem_append] at h
      simp only [Term.headsList, List.mem_append]
      exact h.imp (mem_heads_of_callsOf t) (mem_headsList_of_callsOfList ts)
end

/-- A call `g(ts)` under σ has a result: where the arguments have values `vs` of the argument
sorts of the function `g`, `g` has a result at `vs`. -/
def CallOK (c : Semantics) (σ : Subst) (g : Sym) (ts : List Term) : Prop :=
  ∀ gfn, c.lookupFn g = some gfn → ∀ rs vs, EvalTerms c σ ts rs → allSome rs = some vs →
    c.sortsOf vs = some gfn.args → ∃ r, Eval c g vs r

/-- Each function among the symbols `f` overloads has a result at every argument list of its
sorts: so an application of `f` has one at arguments such a function covers (`EvalTerm.ovlFn`).
True of a symbol that is not function-overloaded. -/
def OvlTerminates (c : Semantics) (f : Sym) : Prop :=
  ∀ o, c.lookupOvl f = some o → ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true → Terminates c kg.name

theorem ovlTerminates_of_not_fnOvl {f : Sym} (h : f ∉ c.fnOvlSyms) : OvlTerminates c f :=
  fun o ho kg hkg hb => by
    rw [OvlLaws.noFnOver_of_not_fnOvl h o ho kg hkg] at hb
    cases hb

/-- A callee of a function `fnOvlCallers` does not name is not function-overloaded. -/
theorem Semantics.not_fnOvl_of_not_caller {fn : Fn} (hfn : fn ∈ c.fns) (hn : fn.label ∉ c.fnOvlCallers)
    {g : Sym} (hg : g ∈ fn.callees) : g ∉ c.fnOvlSyms := fun hm =>
  hn (List.mem_map.mpr ⟨fn, List.mem_filter.mpr ⟨hfn, List.any_eq_true.mpr ⟨g, hg, List.contains_iff_mem.mpr hm⟩⟩, rfl⟩)

/-! ## A term has a result when its calls do -/

mutual
  /-- A right-hand side well sorted over the heads `L`, under a well-sorted σ, has a result when
  each of its calls does, and each function among the symbols a head overloads has one
  (`OvlTerminates`). -/
  theorem evalTerm_result (hc : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L) {vars : List Srt}
      {σ : Subst} (hσ : c.WellSorted vars σ) :
      ∀ (t : Term) {s : Srt}, sortOfTerm (c.rhsCtx L) vars t = some s →
        (∀ f ∈ Term.heads t, OvlTerminates c f) →
        (∀ g ts, ts ∈ callsOf g t → CallOK c σ g ts) → ∃ r, EvalTerm c σ t r
    | .var _, _, _, _, _ => ⟨_, EvalTerm.var⟩
    | .dv _ _, _, _, _, _ => ⟨_, EvalTerm.dv⟩
    | .inj _ _ t, _, ht, hovl, hcall => by
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      obtain ⟨r, hr⟩ := evalTerm_result hc hL hσ t ht' (fun g hg => hovl g (by rw [Term.heads]; exact hg))
        (fun g ts h => hcall g ts (by simpa [callsOf] using h))
      exact ⟨_, EvalTerm.inj hr⟩
    | .as _ _, _, ht, _, _ => by simp [sortOfTerm, Semantics.rhsCtx] at ht
    | .app f ts, _, ht, hovl, hcall => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨rs, hts⟩ := evalTerms_result hc hL hσ ts hargs
        (fun g hg => hovl g (by rw [Term.heads]; exact List.mem_cons_of_mem _ hg)) (fun g us h =>
        hcall g us (by simp only [callsOf, List.mem_append]; exact Or.inr h))
      cases hct : c.isCtor f
      · cases hhk : isHook f
        · cases hpar : c.isParam f
          · cases hov : c.isOvl f with
            | true =>
              obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hc hL hk' hov
              exact EvalTerm.ovl_result (hc.ovl.fnFacts hc.trans) hct hov hts hlo
                (fun ws has => EvalTerms.sorted hc hts hL hσ hargs has)
                (fun kg hkg hb fn _ hlook _ vs hvs =>
                  hovl f (by rw [Term.heads]; exact List.mem_cons_self ..) o hlo kg hkg hb fn hlook vs hvs)
            | false =>
            cases hvs : allSome rs with
            | none => exact ⟨none, EvalTerm.callUndef hct hhk hts hvs hpar⟩
            | some vs =>
              have hnc : lookupSig c.ctorSigs f = none :=
                Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hct)
              simp only [Semantics.rhsCtx, List.append_assoc] at hk'
              rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
                lookupSig_append_of_none (c.lookupSig_params_of_not hpar)] at hk'
              obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (lookupOvl_none_of hc hov) hk')
              obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
              have hlook : c.lookupFn f = some fn := by
                rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn
              obtain ⟨r, hr⟩ := hcall f ts (by simp [callsOf]) fn hlook rs vs hts hvs
                (EvalTerms.sorted hc hts hL hσ hargs hvs)
              exact ⟨r, EvalTerm.call hct hhk hts hvs hr hpar⟩
          · exact ⟨_, EvalTerm.param hct hhk hpar hts rfl⟩
        · refine ⟨(allSome rs).bind fun vs => (c.hookRes f vs).join,
            EvalTerm.hook hct hhk hts (fun vs h => ?_) (fun h => by rw [h]; rfl)⟩
          obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhk vs
          simp [h, ho]
      · exact ⟨_, EvalTerm.ctor hct hts⟩
  theorem evalTerms_result (hc : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L) {vars : List Srt}
      {σ : Subst} (hσ : c.WellSorted vars σ) :
      ∀ (ts : List Term) {ss : List Srt}, sortsOfTerms (c.rhsCtx L) vars ts = some ss →
        (∀ f ∈ Term.headsList ts, OvlTerminates c f) →
        (∀ g us, us ∈ callsOfList g ts → CallOK c σ g us) → ∃ rs, EvalTerms c σ ts rs
    | [], _, _, _, _ => ⟨[], EvalTerms.nil⟩
    | t :: ts, _, hts, hovl, hcall => by
      obtain ⟨_, _, ht, hts', rfl⟩ := sortsOfTerms_cons.mp hts
      obtain ⟨r, hr⟩ := evalTerm_result hc hL hσ t ht
        (fun g hg => hovl g (by rw [Term.headsList]; exact List.mem_append_left _ hg)) (fun g us h =>
        hcall g us (by simp only [callsOfList, List.mem_append]; exact Or.inl h))
      obtain ⟨rs, hrs⟩ := evalTerms_result hc hL hσ ts hts'
        (fun g hg => hovl g (by rw [Term.headsList]; exact List.mem_append_right _ hg)) (fun g us h =>
        hcall g us (by simp only [callsOfList, List.mem_append]; exact Or.inr h))
      exact ⟨r :: rs, EvalTerms.cons hr hrs⟩
end

/-! ## A function has a result when its clauses' terms do -/

/-- Each clause applies or fails at `vs` (excluded middle on its matches), where its `requires`
has a result and its predicate a truth value at each match and each variable outside its patterns and conditions is of a sort with
a value (a match on those extends to every variable, `Clause.fails_of_not_appliesRH`), no clause
with an existential variable or a right side's predicate other than `\top`; a clause
that applies, of the smallest priority among those that do, gives the result where its `ensures`
and right-hand side have results (none where the `ensures` is not `true`), and the rest where none
applies. -/
theorem eval_resultRH {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm}
    (hx : ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top)
    (hbd : ∀ cl ∈ fn.clauses, c.HeldAt cl.vars cl.leftVars)
    (hreq : ∀ cl ∈ fn.clauses, ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs →
      (∀ t, cl.req = some t → ∃ r, EvalTerm c σ t r) ∧ ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hrhs : ∀ cl ∈ fn.clauses, ∀ σ, cl.AppliesAt c σ vs → ∃ r, EvalTerm c σ cl.rhs r)
    (hens : ∀ cl ∈ fn.clauses, ∀ σ, cl.AppliesAt c σ vs → ∀ t, cl.ens = some t → ∃ r, EvalTerm c σ t r) :
    ∃ r, Eval c f vs r := by
  have hfail : ∀ cl ∈ fn.clauses, (¬ ∃ σ, cl.AppliesAt c σ vs) → Fails c vs cl := fun cl hcl hna =>
    Clause.fails_of_not_appliesRH (hbd cl hcl) (hreq cl hcl) hna
  have key : ∀ n p, p < n → (∃ cl ∈ fn.clauses, cl.prio = p ∧ ∃ σ, cl.AppliesAt c σ vs) →
      ∃ r, Eval c f vs r := by
    intro n
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      intro p hp ⟨cl, hcl, hpr, σ, hσ, hm, hq, hp'⟩
      by_cases hlow : ∃ cl' ∈ fn.clauses, cl'.prio < p ∧ ∃ σ', cl'.AppliesAt c σ' vs
      · obtain ⟨cl', hcl', hlt, ha⟩ := hlow
        exact ih cl'.prio (by omega) ⟨cl', hcl', rfl, ha⟩
      · have hlowF : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails c vs cl' := fun cl' hcl' hlt =>
          hfail cl' hcl' fun ha => hlow ⟨cl', hcl', by omega, ha⟩
        cases he : cl.ens with
        | none =>
          obtain ⟨r, hr⟩ := hrhs cl hcl σ ⟨hσ, hm, hq, hp'⟩
          exact ⟨r, Eval.clause hfn hcl hσ hm hq hp' (fun cl' h _ hlt => hlowF cl' h hlt) (hx cl hcl).1 hr
            (fun t ht => by rw [he] at ht; cases ht) (Clause.holds_postTop (hx cl hcl).2 σ)⟩
        | some t =>
          obtain ⟨w, hw⟩ := hens cl hcl σ ⟨hσ, hm, hq, hp'⟩ t he
          by_cases hb : w = some (bool true)
          · subst hb
            obtain ⟨r, hr⟩ := hrhs cl hcl σ ⟨hσ, hm, hq, hp'⟩
            exact ⟨r, Eval.clause hfn hcl hσ hm hq hp' (fun cl' h _ hlt => hlowF cl' h hlt) (hx cl hcl).1 hr
              (fun t' ht' => by rw [he] at ht'; cases ht'; exact hw) (Clause.holds_postTop (hx cl hcl).2 σ)⟩
          · exact ⟨none, Eval.ensFails hfn hcl hσ hm hq hp' (fun cl' h _ hlt => hlowF cl' h hlt) (hx cl hcl).1 he hw hb⟩
  by_cases hany : ∃ cl ∈ fn.clauses, ∃ σ, cl.AppliesAt c σ vs
  · obtain ⟨cl, hcl, ha⟩ := hany
    exact key (cl.prio + 1) cl.prio (by omega) ⟨cl, hcl, rfl, ha⟩
  · exact ⟨_, Eval.rest hfn fun cl hcl => hfail cl hcl fun ha => hany ⟨cl, hcl, ha⟩⟩

/-- `eval_resultRH` where each clause's patterns bind every variable. -/
theorem eval_result {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm}
    (hx : ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top)
    (hbd : ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true)
    (hreq : ∀ cl ∈ fn.clauses, ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs →
      (∀ t, cl.req = some t → ∃ r, EvalTerm c σ t r) ∧ ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hrhs : ∀ cl ∈ fn.clauses, ∀ σ, cl.AppliesAt c σ vs → ∃ r, EvalTerm c σ cl.rhs r)
    (hens : ∀ cl ∈ fn.clauses, ∀ σ, cl.AppliesAt c σ vs → ∀ t, cl.ens = some t → ∃ r, EvalTerm c σ t r) :
    ∃ r, Eval c f vs r :=
  eval_resultRH hfn hx (fun cl hcl => Semantics.heldAt_of_bindsRH (hbd cl hcl)) hreq hrhs hens

/-! ## A function whose callees terminate terminates -/

/-- What termination reads of a core besides subject reduction (`SortCtx`): the `requires` and the
`ensures` of each function's clauses are Bool terms over some function heads, each clause's
predicate is `\top` (so it has a truth value at every substitution), no clause has an existential
variable or a right side's predicate other than `\top`, and each variable of each clause is in its
patterns or conditions or of a sort with a value. -/
structure EvalCtx (c : Semantics) : Prop where
  sort : SortCtx c
  reqs : ∀ fn ∈ c.allFns, ∃ L, HeadsOK c L ∧ ∀ cl ∈ fn.clauses, reqOK (c.rhsCtx L) cl.vars cl.req = true
  enss : ∀ fn ∈ c.allFns, ∃ L, HeadsOK c L ∧ ∀ cl ∈ fn.clauses, reqOK (c.rhsCtx L) cl.vars cl.ens = true
  pres : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top
  plain : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top
  /-- each variable of each clause is in `leftVars` or of a sort with a value -/
  binds : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, c.HeldAt cl.vars cl.leftVars

/-- `EvalCtx` less `binds`: what termination reads of a core where the held variables are asked of
one function at a time (`Semantics.HeldFn`), not of every function. -/
structure EvalCtxN (c : Semantics) : Prop where
  sort : SortCtx c
  reqs : ∀ fn ∈ c.allFns, ∃ L, HeadsOK c L ∧ ∀ cl ∈ fn.clauses, reqOK (c.rhsCtx L) cl.vars cl.req = true
  enss : ∀ fn ∈ c.allFns, ∃ L, HeadsOK c L ∧ ∀ cl ∈ fn.clauses, reqOK (c.rhsCtx L) cl.vars cl.ens = true
  pres : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top
  plain : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top

theorem EvalCtx.toN (hc : EvalCtx c) : EvalCtxN c := ⟨hc.sort, hc.reqs, hc.enss, hc.pres, hc.plain⟩

/-- `EvalCtxN` of a semantics `sortedOK` and `srReady` accept: nothing is asked of the clauses'
variables. -/
theorem evalCtxN_of_all (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase) : EvalCtxN c := by
  refine ⟨sortCtx_of_all hok hsr hov, fun fn hfn' => ?_, fun fn hfn' => ?_, Semantics.sortedOK_preTop hok,
    Semantics.sortedOK_plainCl hok⟩
  · rcases List.mem_append.mp hfn' with hfn | hfn
    · replace hok := Semantics.sortedOK_sorted hok
      simp only [Bool.and_eq_true, List.all_eq_true] at hok
      refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
        exact ⟨g, List.mem_append_left _ hg, rfl⟩
      · have := hok.1.2 fn hfn cl hcl
        simp only [Semantics.clauseSorted, Bool.and_eq_true] at this
        replace this := this.1
        exact this.1.1.1.2
    · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl => (sortPreds_ctx hfn cl hcl).2.2.2.1⟩
  · rcases List.mem_append.mp hfn' with hfn | hfn
    · replace hok := Semantics.sortedOK_sorted hok
      simp only [Bool.and_eq_true, List.all_eq_true] at hok
      refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
        exact ⟨g, List.mem_append_left _ hg, rfl⟩
      · have := hok.1.2 fn hfn cl hcl
        simp only [Semantics.clauseSorted, Bool.and_eq_true] at this
        replace this := this.1
        exact this.1.2
    · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl => (sortPreds_ctx hfn cl hcl).2.2.2.2.2⟩

/-- `EvalCtx` of a semantics `sortedOK` and `srReady` accept, whose clauses' variables are held
(`RightHeld`; the sort predicates' patterns bind their one variable). -/
theorem evalCtx_of_all (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hrh : c.RightHeld) : EvalCtx c := by
  have hN := evalCtxN_of_all hok hsr hov
  refine ⟨hN.sort, hN.reqs, hN.enss, hN.pres, hN.plain, fun fn hfn' => ?_⟩
  · rcases List.mem_append.mp hfn' with hfn | hfn
    · exact fun cl hcl => hrh.heldAt hfn hcl
    · exact fun cl hcl => Semantics.heldAt_of_bindsRH (Semantics.sortPreds_binds hfn cl hcl)

theorem heads_rhs_callees {fn : Fn} {cl : Clause} (hcl : cl ∈ fn.clauses) {g : Sym}
    (hg : g ∈ Term.heads cl.rhs) : g ∈ fn.callees := by
  simp only [Fn.callees, List.mem_append, List.mem_flatMap]
  exact ⟨cl, hcl, Or.inl (Or.inl hg)⟩

theorem heads_req_callees {fn : Fn} {cl : Clause} (hcl : cl ∈ fn.clauses) {t : Term}
    (ht : cl.req = some t) {g : Sym} (hg : g ∈ Term.heads t) : g ∈ fn.callees := by
  simp only [Fn.callees, List.mem_append, List.mem_flatMap]
  exact ⟨cl, hcl, Or.inl (Or.inr (by rw [ht]; exact hg))⟩

theorem heads_ens_callees {fn : Fn} {cl : Clause} (hcl : cl ∈ fn.clauses) {t : Term}
    (ht : cl.ens = some t) {g : Sym} (hg : g ∈ Term.heads t) : g ∈ fn.callees := by
  simp only [Fn.callees, List.mem_append, List.mem_flatMap]
  exact ⟨cl, hcl, Or.inr (by rw [ht]; exact hg)⟩

theorem lookupFn_of_memN (hc : EvalCtxN c) {fn : Fn} (hfn : fn ∈ c.allFns) :
    c.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]; exact find?_label hc.sort.nodupFns hfn

theorem lookupFn_of_mem (hc : EvalCtx c) {fn : Fn} (hfn : fn ∈ c.allFns) :
    c.lookupFn fn.label = some fn :=
  lookupFn_of_memN hc.toN hfn

/-- A function whose clauses' variables are held (`hb`) has a result at an argument list of its
argument sorts where each call in its clauses (under a match of the clause's patterns at the
arguments) has one. The held variables are read of this function alone. -/
theorem eval_of_callsN (hc : EvalCtxN c) {fn : Fn} (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some fn.args) (hovl : ∀ g ∈ fn.callees, OvlTerminates c g)
    (hcl : ∀ cl ∈ fn.clauses, ∀ σ, PatVals c σ cl.pats vs → ∀ t, (t = cl.rhs ∨ cl.req = some t ∨ cl.ens = some t) →
      ∀ g ts, ts ∈ callsOf g t → CallOK c σ g ts) :
    ∃ r, Eval c fn.label vs r := by
  obtain ⟨L, hL, hrs⟩ := hc.sort.fns fn hfn
  obtain ⟨L', hL', hreqs⟩ := hc.reqs fn hfn
  obtain ⟨L'', hL'', hens⟩ := hc.enss fn hfn
  refine eval_resultRH (lookupFn_of_memN hc hfn) (hc.plain fn hfn) hb
    (fun cl hcl' σ hσ hm => ⟨fun t ht => ?_, true, Clause.holds_preTop (hc.pres fn hfn cl hcl') σ⟩)
    (fun cl hcl' σ ha => ?_) (fun cl hcl' σ ha t ht => ?_)
  · have hq := hreqs cl hcl'
    rw [ht] at hq
    simp only [reqOK, beq_iff_eq] at hq
    exact evalTerm_result hc.sort hL' hσ t hq (fun g hg => hovl g (heads_req_callees hcl' ht hg))
      (hcl cl hcl' σ hm t (Or.inr (Or.inl ht)))
  · exact evalTerm_result hc.sort hL ha.1 cl.rhs (hrs cl hcl') (fun g hg => hovl g (heads_rhs_callees hcl' hg))
      (hcl cl hcl' σ ha.2.1 _ (Or.inl rfl))
  · have hq := hens cl hcl'
    rw [ht] at hq
    simp only [reqOK, beq_iff_eq] at hq
    exact evalTerm_result hc.sort hL'' ha.1 t hq (fun g hg => hovl g (heads_ens_callees hcl' ht hg))
      (hcl cl hcl' σ ha.2.1 t (Or.inr (Or.inr ht)))

/-- A function has a result at an argument list of its argument sorts where each call in its
clauses (under a match of the clause's patterns at the arguments) has one. -/
theorem eval_of_calls (hc : EvalCtx c) {fn : Fn} (hfn : fn ∈ c.allFns) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some fn.args) (hovl : ∀ g ∈ fn.callees, OvlTerminates c g)
    (hcl : ∀ cl ∈ fn.clauses, ∀ σ, PatVals c σ cl.pats vs → ∀ t, (t = cl.rhs ∨ cl.req = some t ∨ cl.ens = some t) →
      ∀ g ts, ts ∈ callsOf g t → CallOK c σ g ts) :
    ∃ r, Eval c fn.label vs r :=
  eval_of_callsN hc.toN hfn (hc.binds fn hfn) hvs hovl hcl

theorem heads_callees {fn : Fn} {cl : Clause} (hcl : cl ∈ fn.clauses) {t : Term}
    (ht : t = cl.rhs ∨ cl.req = some t ∨ cl.ens = some t) {g : Sym} (hg : g ∈ Term.heads t) : g ∈ fn.callees := by
  rcases ht with rfl | ht | ht
  · exact heads_rhs_callees hcl hg
  · exact heads_req_callees hcl ht hg
  · exact heads_ens_callees hcl ht hg

/-- `terminates_of_callees` with the held variables read of the one function (`hb`). -/
theorem terminates_of_calleesN (hc : EvalCtxN c) {fn : Fn} (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn)
    (hcall : ∀ g ∈ fn.callees, Terminates c g) (hovl : ∀ g ∈ fn.callees, OvlTerminates c g) :
    Terminates c fn.label := by
  intro fn' hfn' vs hvs
  rw [lookupFn_of_memN hc hfn] at hfn'
  cases hfn'
  exact eval_of_callsN hc hfn hb hvs hovl
    (fun cl hcl _ _ t ht g ts hts gfn hg _ vs' _ _ hsrt =>
      hcall g (heads_callees hcl ht (mem_heads_of_callsOf t hts)) gfn hg vs' hsrt)

/-- **A function whose callees terminate terminates**: each call in its clauses reaches a function of the definition at argument values of its argument sorts (subject
reduction), where the callee has a result; an application of an overloading symbol reaches, at
arguments a function it overloads covers, that function (`hovl`). -/
theorem terminates_of_callees (hc : EvalCtx c) {fn : Fn} (hfn : fn ∈ c.allFns)
    (hcall : ∀ g ∈ fn.callees, Terminates c g) (hovl : ∀ g ∈ fn.callees, OvlTerminates c g) :
    Terminates c fn.label :=
  terminates_of_calleesN hc.toN hfn (hc.binds fn hfn) hcall hovl

/-- The generated sort predicates call nothing: their right-hand sides are Bool literals. -/
theorem sortPreds_callees {fn : Fn} (hfn : fn ∈ c.sortPreds) : fn.callees = [] := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩ <;> rfl

/-- The sort predicates terminate: their patterns bind their one variable, and they call nothing. -/
theorem sortPreds_terminateN (hc : EvalCtxN c) {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    Terminates c fn.label :=
  terminates_of_calleesN hc (List.mem_append_right _ hfn)
    (fun cl hcl => Semantics.heldAt_of_bindsRH (Semantics.sortPreds_binds hfn cl hcl))
    (by rw [sortPreds_callees hfn]; intro g hg; nomatch hg)
    (by rw [sortPreds_callees hfn]; intro g hg; nomatch hg)

theorem sortPreds_terminate (hc : EvalCtx c) {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    Terminates c fn.label :=
  sortPreds_terminateN hc.toN hfn

/-! ## What is owed of a held-named function -/

/-- **What is owed of a held-named function `f`** (`Semantics.heldObligations`), one of two facts,
the choice the prover's: the variables of its clauses are held (`HeldFn`: each variable outside a
clause's patterns and conditions is of a sort with a value; shown by exhibiting the values), or `f`
has a result at every argument list of its sorts (`Terminates`), a value where it is `[total]`
(`Total`). At a sort without a value the first is false, and the second holds where another clause
decides or the clause is never matched. -/
def HeldOwed (c : Semantics) (f : Sym) : Prop :=
  ∀ fn, c.lookupFn f = some fn → c.HeldFn fn ∨ (Terminates c f ∧ (fn.total = true → Total c f))

/-- `RightHeld` gives the first fact of every function. -/
theorem Semantics.RightHeld.heldOwed (hrh : c.RightHeld) (f : Sym) : HeldOwed c f := fun fn hfn => by
  obtain ⟨hm, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hm with hu | hp
  · exact .inl (hrh.heldFn hu)
  · exact .inl fun cl hcl => Semantics.heldAt_of_bindsRH (Semantics.sortPreds_binds hp cl hcl)

/-- **Each function's variables are held, or it has the results owed**, from the owed facts of the
held-named ones: a function not named has `HeldFn` on the data (`Semantics.heldFn_of_not_named`). -/
theorem heldOr_of_owed (hc : EvalCtxN c) (h : ∀ f ∈ c.heldObligations, HeldOwed c f) {fn : Fn} (hfn : fn ∈ c.fns) :
    c.HeldFn fn ∨ (Terminates c fn.label ∧ (fn.total = true → Total c fn.label)) := by
  by_cases hn : fn.label ∈ c.heldObligations
  · exact h _ hn fn (lookupFn_of_memN hc (List.mem_append_left _ hfn))
  · exact .inl (Semantics.heldFn_of_not_named hfn hn)

/-! ## Declaration order -/

/-- The order check passes for each function `orderObligations` does not name: each of its callees
is itself, a function declared before it, or no function of the user's. -/
theorem order_go (labels : List Sym) : ∀ (fs : List Fn) (earlier : List Sym) (n : Nat) (fn : Fn),
    fs[n]? = some fn → fn.label ∉ Semantics.orderObligations.go labels earlier fs →
    ∀ g ∈ fn.callees, g = fn.label ∨ g ∈ earlier ++ (fs.take n).map (·.label) ∨ g ∉ labels
  | [], _, _, _, h, _ => by simp at h
  | f :: fs, earlier, n, fn, h, hn => by
    simp only [Semantics.orderObligations.go, List.mem_append] at hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      intro g hg
      have hok : (f.callees.all fun g => g == f.label || earlier.contains g || !labels.contains g) = true := by
        cases hk : (f.callees.all fun g => g == f.label || earlier.contains g || !labels.contains g)
        · rw [hk] at hn
          exact absurd (Or.inl (List.mem_singleton_self _)) hn
        · rfl
      have := List.all_eq_true.mp hok g hg
      simp only [List.take_zero, List.map_nil, List.append_nil]
      cases h1 : (g == f.label) <;> cases h2 : earlier.contains g <;> cases h3 : labels.contains g <;>
        simp only [h1, h2, h3, Bool.or_self, Bool.or_true, Bool.true_or, Bool.not_false,
          Bool.not_true] at this
      all_goals first
        | exact absurd this (by decide)
        | exact Or.inl (beq_iff_eq.mp h1)
        | exact Or.inr (Or.inl (List.contains_iff_mem.mp h2))
        | exact Or.inr (Or.inr fun hm => absurd (List.contains_iff_mem.mpr hm) (by rw [h3]; decide))
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      intro g hg
      rcases order_go labels fs (earlier ++ [f.label]) n fn h (fun h' => hn (Or.inr h')) g hg with
        h | h | h
      · exact Or.inl h
      · refine Or.inr (Or.inl ?_)
        simp only [List.take_succ_cons, List.map_cons, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at h ⊢
        rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inr h)

/-! ## Decreasing self calls -/

mutual
  /-- The size of a value: its constructor and injection nodes; a domain value or a collection
  counts one. -/
  def GroundTerm.size : GroundTerm → Nat
    | .ctor _ ts => GroundTerm.sizeList ts + 1
    | .inj _ _ t => GroundTerm.size t + 1
    | .dv _ _ => 1
    | .map _ _ => 1
    | .set _ _ => 1
    | .list _ _ => 1
    termination_by structural t => t
  def GroundTerm.sizeList : List GroundTerm → Nat
    | [] => 0
    | t :: ts => GroundTerm.size t + GroundTerm.sizeList ts
    termination_by structural ts => ts
end

/-- An injection does not shrink a value: `injNormal` drops a nested injection for its own. -/
theorem size_injNormal (a b : Srt) (w : GroundTerm) : w.size ≤ (injNormal a b w).size := by
  cases w <;> simp [injNormal, GroundTerm.size]

theorem isCtor_of_ctorPat {g : Sym} (h : c.ctorPat g = true) : c.isCtor g = true := by
  simp only [Semantics.ctorPat, Bool.and_eq_true] at h
  exact h.1

theorem not_patternHook_of_ctorPat {g : Sym} (h : c.ctorPat g = true) :
    patternHooks.contains g = false := by
  simp only [Semantics.ctorPat, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

mutual
  /-- On a path of constructor applications, injections and aliases, a variable's value is no
  larger than the value the pattern denotes. -/
  theorem ctorPath_size {σ : Subst} {j : Nat} : ∀ (p : Term) {v : GroundTerm}, PatVal c σ p v →
      ctorPathIn c.ctorPat j p = true → ∃ w, σ.lookup j = some w ∧ w.size ≤ v.size
    | .var i, v, h, hp => by
      cases h with
      | var hl =>
        simp only [ctorPathIn, beq_iff_eq] at hp
        subst hp
        exact ⟨v, hl, Nat.le_refl _⟩
    | .dv _ _, _, _, hp => by simp [ctorPathIn] at hp
    | .inj a b t, _, h, hp => by
      cases h with
      | inj h' =>
        obtain ⟨w, hw, hle⟩ := ctorPath_size t h' (by simpa [ctorPathIn] using hp)
        exact ⟨w, hw, Nat.le_trans hle (size_injNormal a b _)⟩
    | .as t _, _, h, hp => by
      cases h with
      | as h' _ => exact ctorPath_size t h' (by simpa [ctorPathIn] using hp)
    | .app g ts, _, h, hp => by
      simp only [ctorPathIn, Bool.and_eq_true] at hp
      cases h with
      | ctor _ hs =>
        obtain ⟨w, hw, hle⟩ := ctorPathList_size ts hs hp.2
        exact ⟨w, hw, by simp only [GroundTerm.size]; omega⟩
      | hook hph _ _ => rw [not_patternHook_of_ctorPat hp.1] at hph; cases hph
      | coll hc _ _ _ => rw [isCtor_of_ctorPat hp.1] at hc; cases hc
      | ovl hc _ _ _ => rw [isCtor_of_ctorPat hp.1] at hc; cases hc
  theorem ctorPathList_size {σ : Subst} {j : Nat} : ∀ (ts : List Term) {vs : List GroundTerm},
      PatVals c σ ts vs → ctorPathInList c.ctorPat j ts = true →
        ∃ w, σ.lookup j = some w ∧ w.size ≤ GroundTerm.sizeList vs
    | [], _, _, hp => by simp [ctorPathInList] at hp
    | t :: ts, _, h, hp => by
      cases h with
      | cons h1 h2 =>
        simp only [ctorPathInList, Bool.or_eq_true] at hp
        rcases hp with hp | hp
        · obtain ⟨w, hw, hle⟩ := ctorPath_size t h1 hp
          exact ⟨w, hw, by simp only [GroundTerm.sizeList]; omega⟩
        · obtain ⟨w, hw, hle⟩ := ctorPathList_size ts h2 hp
          exact ⟨w, hw, by simp only [GroundTerm.sizeList]; omega⟩
end

/-- **A variable strictly inside a pattern** (`strictlyIn`) has a value strictly smaller than the
value the pattern denotes. -/
theorem strictlyIn_size {σ : Subst} {j : Nat} : ∀ (p : Term) {v : GroundTerm}, PatVal c σ p v →
    strictlyIn c.ctorPat j p = true → ∃ w, σ.lookup j = some w ∧ w.size < v.size
  | .var _, _, _, hp => by simp [strictlyIn] at hp
  | .dv _ _, _, _, hp => by simp [strictlyIn] at hp
  | .inj a b t, _, h, hp => by
    cases h with
    | inj h' =>
      obtain ⟨w, hw, hlt⟩ := strictlyIn_size t h' (by simpa [strictlyIn] using hp)
      exact ⟨w, hw, Nat.lt_of_lt_of_le hlt (size_injNormal a b _)⟩
  | .as t _, _, h, hp => by
    cases h with
    | as h' _ => exact strictlyIn_size t h' (by simpa [strictlyIn] using hp)
  | .app g ts, _, h, hp => by
    simp only [strictlyIn, Bool.and_eq_true] at hp
    cases h with
    | ctor _ hs =>
      obtain ⟨w, hw, hle⟩ := ctorPathList_size ts hs hp.2
      exact ⟨w, hw, by simp only [GroundTerm.size]; omega⟩
    | hook hph _ _ => rw [not_patternHook_of_ctorPat hp.1] at hph; cases hph
    | coll hc _ _ _ => rw [isCtor_of_ctorPat hp.1] at hc; cases hc
    | ovl hc _ _ _ => rw [isCtor_of_ctorPat hp.1] at hc; cases hc

/-- A self call in a clause of a function whose self calls decrease at `dec`: its argument there is
a variable strictly inside the clause's pattern there. -/
theorem decreasingOK_clause {f : Fn} {dec : Option Nat} (h : decreasingOK c f dec = true)
    {cl : Clause} (hcl : cl ∈ f.clauses) {t : Term} (ht : t = cl.rhs ∨ cl.req = some t ∨ cl.ens = some t)
    {ts : List Term} (hts : ts ∈ callsOf f.label t) :
    ∃ i j p, dec = some i ∧ ts[i]? = some (.var j) ∧ cl.pats[i]? = some p ∧ strictlyIn c.ctorPat j p = true := by
  have hmem : (cl.pats, ts) ∈ selfCalls f := by
    simp only [selfCalls, List.mem_append, List.mem_flatMap, List.mem_map]
    refine ⟨cl, hcl, ts, ?_, rfl⟩
    rcases ht with rfl | ht | ht
    · exact Or.inl (Or.inl hts)
    · rw [ht]; exact Or.inl (Or.inr hts)
    · rw [ht]; exact Or.inr hts
  unfold decreasingOK at h
  have hne : (selfCalls f).isEmpty = false := by
    cases hs : selfCalls f with
    | nil => rw [hs] at hmem; cases hmem
    | cons _ _ => rfl
  simp only [hne, Bool.false_or] at h
  cases dec with
  | none => cases h
  | some i =>
    have := List.all_eq_true.mp h _ hmem
    simp only at this
    split at this
    · rename_i j p hj hp
      exact ⟨i, j, p, rfl, hj, hp, this⟩
    · cases this

/-- The value of an argument that is a variable is the variable's. -/
theorem evalTerms_var {σ : Subst} : ∀ {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {i j : Nat}, EvalTerms c σ ts rs → ts[i]? = some (.var j) →
    allSome rs = some vs → vs[i]? = σ.lookup j
  | _, _, _, i, j, .cons (t := t) (ts := ts) (r := r) (rs := rs) h hs, hti, hall => by
    simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hall
    obtain ⟨w, hw, ws, hws, rfl⟩ := hall
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hti
      subst hti
      cases h
      simpa using hw.symm
    | succ i =>
      simp only [List.getElem?_cons_succ] at hti ⊢
      exact evalTerms_var hs hti hws
  | _, _, _, _, _, .nil, hti, _ => by simp at hti

theorem patVals_get {σ : Subst} : ∀ {ps : List Term} {vs : List GroundTerm} {i : Nat} {p : Term},
    PatVals c σ ps vs → ps[i]? = some p → ∃ v, vs[i]? = some v ∧ PatVal c σ p v
  | _, _, _, _, .nil, hp => by simp at hp
  | _, _, i, _, .cons h hs, hp => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      exact ⟨_, rfl, h⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hp ⊢
      exact patVals_get hs hp

/-- The measure of a self call: the size of the argument at the decreasing position. -/
def decMeasure (dec : Option Nat) (vs : List GroundTerm) : Nat :=
  ((vs[dec.getD 0]?).map GroundTerm.size).getD 0

/-- **A function whose self calls decrease, and whose other callees terminate, terminates**: by
induction on the size of the argument at the decreasing position. A self call is at a variable
strictly inside the clause's pattern there, whose value is strictly smaller (`strictlyIn_size`). -/
theorem terminates_of_decreasing (hc : EvalCtx c) {fn : Fn} (hfn : fn ∈ c.allFns) {dec : Option Nat}
    (hdec : decreasingOK c fn dec = true)
    (hcall : ∀ g ∈ fn.callees, g ≠ fn.label → Terminates c g)
    (hovl : ∀ g ∈ fn.callees, OvlTerminates c g) : Terminates c fn.label := by
  have hlook := lookupFn_of_mem hc hfn
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  suffices h : ∀ n vs, c.sortsOf vs = some fn.args → decMeasure dec vs < n →
      ∃ r, Eval c fn.label vs r from h _ vs hvs (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro vs hvs hlt
    refine eval_of_calls hc hfn hvs hovl (fun cl hcl σ hm t ht g ts hts gfn hg rs vs' hrs hall hsrt => ?_)
    by_cases hgl : g = fn.label
    · subst hgl
      rw [hlook] at hg
      cases hg
      obtain ⟨i, j, p, rfl, hti, hpi, hsi⟩ := decreasingOK_clause hdec hcl ht hts
      obtain ⟨v, hvi, hpv⟩ := patVals_get hm hpi
      obtain ⟨w, hw, hwv⟩ := strictlyIn_size p hpv hsi
      have hvi' : vs'[i]? = some w := (evalTerms_var hrs hti hall).trans hw
      refine ih vs' hsrt ?_
      have h1 : decMeasure (some i) vs' = w.size := by simp [decMeasure, hvi']
      have h2 : decMeasure (some i) vs = v.size := by simp [decMeasure, hvi]
      omega
    · exact hcall g (heads_callees hcl ht (mem_heads_of_callsOf t hts)) hgl gfn hg vs' hsrt

theorem mem_withPres {α β : Type} [Inhabited β] : ∀ (as : List α) (bs : List β) {a : α}, a ∈ as →
    ∃ b, (a, b) ∈ withPres as bs
  | [], _, _, h => nomatch h
  | x :: as, bs, a, h => by
    simp only [withPres, List.mem_cons, Prod.mk.injEq]
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨b, hb⟩ := mem_withPres as bs.tail h
      exact ⟨b, Or.inr hb⟩

/-- A function the certificate does not name has self calls that decrease at its argument. -/
theorem decreasing_of_not_named {z : Certificates} {fn : Fn} (hfn : fn ∈ c.fns)
    (hn : fn.label ∉ z.obligations c) : ∃ dec, decreasingOK c fn dec = true := by
  obtain ⟨dec, hd⟩ := mem_withPres c.fns z.decreasing hfn
  refine ⟨dec, ?_⟩
  cases h : decreasingOK c fn dec
  · exact absurd (List.mem_map.mpr ⟨(fn, dec), List.mem_filter.mpr ⟨hd, by simp [h]⟩, rfl⟩) hn
  · rfl

/-- **Declaration order and decreasing self calls give termination**: in a core that `sortedOK`
and `srReady` accept, every function terminates, given the termination of the named ones
(`orderObligations`, the certificate's `obligations`: the first conjunct of `Obligations`). By
induction on the position in the declaration order: a function not named calls only itself, the
functions before it, which terminate, and the sort predicates, which call nothing; its self calls
decrease (`terminates_of_decreasing`). Stated for every function `lookupFn` finds, the sort
predicates among them. -/
theorem terminates_of_order_core (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hrh : c.RightHeld)
    (z : Certificates) (hnamed : ∀ g ∈ c.orderObligations ++ z.obligations c, Terminates c g) :
    ∀ f, Terminates c f := by
  have hc := evalCtx_of_all hok hsr hov hrh
  have pos : ∀ (n : Nat) (fn : Fn), c.fns[n]? = some fn → Terminates c fn.label := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro fn hn
      have hmem : fn ∈ c.fns := List.mem_of_getElem? hn
      by_cases hN : fn.label ∈ c.orderObligations ++ z.obligations c
      · exact hnamed _ hN
      have hord : fn.label ∉ Semantics.orderObligations.go (c.fns.map (·.label)) [] c.fns :=
        fun h => hN (List.mem_append_left _ (show fn.label ∈ c.orderObligations from List.mem_append_left _ h))
      have hovl : ∀ g ∈ fn.callees, OvlTerminates c g := fun g hg =>
        ovlTerminates_of_not_fnOvl (Semantics.not_fnOvl_of_not_caller hmem
          (fun h => hN (List.mem_append_left _ (show fn.label ∈ c.orderObligations from List.mem_append_right _ h))) hg)
      obtain ⟨dec, hdec⟩ := decreasing_of_not_named (z := z) hmem (fun h => hN (List.mem_append_right _ h))
      refine terminates_of_decreasing hc (List.mem_append_left _ hmem) hdec (fun g hg hgl => ?_) hovl
      rcases order_go _ c.fns [] n fn hn hord g hg with h | h | h
      · exact absurd h hgl
      · simp only [List.nil_append, List.mem_map] at h
        obtain ⟨fm, hfm, rfl⟩ := h
        obtain ⟨m, hm, hfmm⟩ := List.getElem_of_mem hfm
        rw [List.length_take] at hm
        have hlt : m < n := by omega
        refine ih m hlt fm ?_
        rw [← hfmm, List.getElem_take]
        exact List.getElem?_eq_getElem _
      · intro gfn hgfn
        obtain ⟨hgm, hlab⟩ := lookupFn_spec hgfn
        rcases List.mem_append.mp hgm with hu | hp
        · exact absurd (hlab ▸ List.mem_map_of_mem hu) h
        · exact hlab ▸ sortPreds_terminate hc hp gfn (hlab ▸ hgfn)
  intro f fn hfn
  obtain ⟨hgm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  rcases List.mem_append.mp hgm with hu | hp
  · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hu
    exact pos n _ (List.getElem?_eq_getElem hn) _ hfn
  · exact sortPreds_terminate hc hp fn hfn

/-- `terminates_of_order_core` in a core that `okAll` accepts. -/
theorem terminates_of_order (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase) (z : Certificates)
    (hnamed : ∀ g ∈ c.orderObligations ++ z.obligations c, Terminates c g)
    (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel)) : ∀ f, Terminates c f :=
  terminates_of_order_core (Semantics.sortedOK_of_okAll hok) hsr hov hrh z hnamed

/-- With no function named, every function terminates. -/
theorem terminates_of_nil (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase) (z : Certificates)
    (h : c.orderObligations ++ z.obligations c = []) (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel)) : ∀ f, Terminates c f :=
  terminates_of_order hok hsr hov z (fun g hg => by rw [h] at hg; exact absurd hg List.not_mem_nil) hrh

theorem orderObligations_withHooks (H : HookParams) :
    (c.withHooks H).orderObligations = c.orderObligations := rfl

theorem ctorPat_withHooks (H : HookParams) : (c.withHooks H).ctorPat = c.ctorPat := rfl

theorem certObligations_withHooks (z : Certificates) (H : HookParams) :
    z.obligations (c.withHooks H) = z.obligations c := by
  simp only [Certificates.obligations, decreasingOK, ctorPat_withHooks]
  rfl

/-- `terminates_of_order` for every interpretation of the parameters: the conditions decided once
on the data, the named functions' termination under `H`. For a semantics without an open generator
(`hr`). -/
theorem terminates_of_order_withHooks (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (z : Certificates) (H : HookParams)
    (hnamed : ∀ g ∈ c.orderObligations ++ z.obligations c, Terminates (c.withHooks H) g)
    (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel))
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) :
    ∀ f, Terminates (c.withHooks H) f :=
  terminates_of_order ((Semantics.okAll_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) (Semantics.ovlCase_withHooks hov H) z
    (by rw [orderObligations_withHooks, certObligations_withHooks]; exact hnamed)
    (Semantics.rightHeld_withHooks hrh H hr)

/-- `terminates_of_nil` for every interpretation of the parameters, of a semantics without an open
generator (`hr`). -/
theorem terminates_of_nil_withHooks (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (z : Certificates) (h : c.orderObligations ++ z.obligations c = []) (H : HookParams)
    (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel))
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) :
    ∀ f, Terminates (c.withHooks H) f :=
  terminates_of_nil ((Semantics.okAll_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) (Semantics.ovlCase_withHooks hov H) z
    (by rw [orderObligations_withHooks, certObligations_withHooks]; exact h)
    (Semantics.rightHeld_withHooks hrh H hr)

/-- What subject reduction reads of the overloading symbols, from `coreOK`. -/
theorem Semantics.ovlCase_of_core {c : Semantics} (h : c.coreOK = true) : c.OvlCase := by
  obtain ⟨hok, -, -, -, hids⟩ := Semantics.coreOK_parts h
  exact .inr ⟨Semantics.coreOK_ovls h, NamesApart.subsorts_irrefl_of hids hok⟩

/-- Every Range value is a KItem, decided, from `coreOK` (`genWf` and `overloadsOK` are among its
conjuncts). -/
theorem rangeKeysOK_of_core {c : Semantics} (h : c.coreOK = true) : c.rangeKeysOK = true :=
  rangeKeysOK_of_genWf (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1)
    (Semantics.coreOK_ovls h)

/-- **Every function of a semantics terminates**, under `coreOK` and `CoreObligations` (its first
conjunct: the named functions terminate). -/
theorem CoreObligations.terminates {c : Semantics} {t : Certificates} (h : c.coreOK = true)
    (hrh : c.RightHeld) (hob : CoreObligations c t) : ∀ f, Terminates c f := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  exact KCore.terminates_of_order_core hok (NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)) (Semantics.ovlCase_of_core h) hrh
    t hob.1

/-- **Every function of a definition terminates**, under `wf` and `Obligations` (its first
conjunct: the named functions terminate). -/
theorem Obligations.terminates {d : Definition} (hwf : wf d = true) (hrh : d.sem.RightHeld)
    (hob : Obligations d) : ∀ f, Terminates d.sem f :=
  CoreObligations.terminates (Definition.coreOK_of_wf hwf) hrh hob

end KCore
