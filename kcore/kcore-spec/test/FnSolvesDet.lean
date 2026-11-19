/-
  `FnDet` beside `coreOK` and `FnSolves`. A witness for `FnDet` is a semantics with `coreOK` and
  `FnSolves`, without `FnDet`, whose `Γ` has no model.
  - Among the semantics whose clauses' predicates are all `\top` (`clausesPreTop`) and whose
    clauses bind no variable by `\exists` (`FnsNoExs`) there is none: there, under `coreOK`,
    `FnSolves` gives `FnDet` (`fnDet_of_fnSolves`), kernel-checked here.
  - `coreOK` also admits a clause whose predicate is not `\top` where its conditions need no
    witness, and there `FnSolves` does not give `FnDet` (`not_fnDet_of_fnSolves`): the semantics of
    KcoreSpec/ModelFnDetWitness.lean meets `coreOK`, `FnSolves`, `ClausePreDecided`,
    `ClausePostDecided` and `OpenLaws`, one of its functions has two results at 0, and its `Γ` has
    no model. So `fnDet_of_fnSolves` cannot lose `clausesPreTop`, and `consistent_of` cannot lose
    `FnDet` (`consistent_needs_fnDet`).
  - Whether `fnDet_of_fnSolves` can lose `FnsNoExs` is open: `coreOK` admits a clause with
    existential variables, each of a confined sort or fixed by the clause's right-side predicate,
    and `Eval.clauseEx` and `Eval.exNone` read that predicate by `Holds`, which has `ceil` and
    `not`.
  Run from the package root: `lake env lean -j1 test/FnSolvesDet.lean`.

  Why the proof below stops at a predicate. It shows, by induction over one derivation, that every
  value of the function is that derivation's result; it never shows that a derivation of a value
  excludes a derivation of none. Reading a clause's failure (`Fails`, a derivation that its
  `requires` is not `true`) as "the clause does not apply" needs only the first. A predicate adds
  `ReqFails.pre`, a derivation that the predicate is false, and `Holds.not` over `Holds.ceil` makes
  a predicate false from a derivation of a value and true from a derivation of none: reading that
  failure as "does not apply" needs that a value excludes none, which is `FnDet` itself. `FnSolves`
  speaks of values only, so it does not give it. The witness: `a(X) => 1`,
  `a(X) => 1 ensures u(X)` and `u(X) => true` where `¬⌈a(X)⌉`. `a` is 1 by its first clause; so the
  predicate is false, `u`'s clause fails and `u` is undefined; so `a` has no value by its second
  clause (`Eval.ensFails`); so the predicate is also true and `u` is `true`. The values of `a` are 1
  alone and those of `u` `true` alone, and each clause gives them: `FnSolves` holds.

  Scope. The proof reads the block as it is here: every term is strict (undefined where an argument
  is), no clause has an existential variable (`FnsNoExs`, a hypothesis), so `coreOK` makes every
  clause's `post` `\top` (`sortedOK_plainCl_of_noExs`), and `clausesPreTop` makes every clause's
  `pre` `\top` (`allFns_preTop`). So `Eval.clauseEx` and `Eval.exNone` do
  not occur, `FnSolves` is read as the value of the deciding clause's right-hand side where its
  `ensures` is `true` (`Clause.gives_iff_noExs`), the premise on `Clause.pre` (of `clause` and
  `ensFails`) holds and the failure `ReqFails.pre` does not occur. Existential variables (which
  `coreOK` admits, so `FnsNoExs` is a hypothesis here) or another `pre` (a `Cond` whose `Holds` has
  `ceil` and `not`, so that a premise can hold because a term is undefined) can make a witness
  possible; the recursor call below
  stops elaborating when the block changes, which is the signal to decide the question again on the
  new block.

  The argument, by one induction over the evaluation block (`Eval.rec`), shows of every result `r`
  of a function at `vs` that any value `some w` there is `r` (`V1`), and of every term's result
  under σ that any value of the term is it (`V4`): the side that has a value has every subterm
  defined, since a term with an undefined argument is undefined.
  - `Eval.clause` of a user function: the clause decides as the model reads it (`DecidesAt`): it
    applies, and no clause of a smaller priority that is not `aside` applies, which is the
    induction's reading of their failures (`V2`). Its arguments are of the function's sorts
    (`clauseSorted`, `patVals_sortedAll`), so `FnSolves` makes every value there a value of its
    right-hand side under σ, which the induction equates with `r`.
  - `Eval.ensFails`: `FnSolves` makes the `ensures` evaluate to `true` wherever there is a value,
    and the induction equates that with its result here, which is not `true`.
  - `Eval.rest`: a clause giving a value would apply, against every clause's failure (`V2`).
  - A sort predicate (not in `c.fns`, so not read by `FnSolves`): its clauses have no `requires`
    and no `ensures`, their right sides are literals, and two of its clauses differ in priority,
    so the one of the smaller priority blocks the other wherever it matches (`sortPred_shape`).
  - The terms: as `EvalTerm.functional_hdet_of_fnDet` (EvalFunctional.lean), on the value side only.
  `FnDet` follows: two results that are both `none` are equal, and otherwise one is a value.

  The instance `instance_c0` checks the hypotheses are met by a definition (non-vacuity).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace FnSolvesDet

open Det

variable {c : Semantics}

/-- A value of `f` at `vs` is the result `r`. -/
abbrev V1 (c : Semantics) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ r', Eval c f vs r' → r'.isSome = true → r = r'
/-- The clause's patterns and `requires` hold under no σ, where its predicate is `\top`. -/
abbrev V2 (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs →
    (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → cl.pre = .top → False
abbrev V3 (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → cl.pre = .top → False
/-- A value of the term under σ is the result `r`. -/
abbrev V4 (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  ∀ r', EvalTerm c σ t r' → r'.isSome = true → r = r'
abbrev V5 (c : Semantics) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  ∀ rs', EvalTerms c σ ts rs' → (∀ x ∈ rs', x.isSome = true) → rs = rs'

theorem allSome_isSome : ∀ {rs : List (Option GroundTerm)}, (allSome rs).isSome = true → ∀ x ∈ rs, x.isSome = true
  | [], _, x, hx => nomatch hx
  | r :: rs, h, x, hx => by
    cases r with
    | none => simp [allSome] at h
    | some v =>
      cases hr : allSome rs with
      | none => simp [allSome, hr] at h
      | some ws =>
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact allSome_isSome (by rw [hr]; rfl) x hx

theorem isSome_of_bind {o : Option (List GroundTerm)} {g : List GroundTerm → Option GroundTerm}
    (h : (o.bind g).isSome = true) : o.isSome = true := by cases o <;> simp_all

theorem isSome_of_map {o : Option (List GroundTerm)} {g : List GroundTerm → GroundTerm}
    (h : (o.map g).isSome = true) : o.isSome = true := by cases o <;> simp_all

theorem isSome_of_eq {o : Option (List GroundTerm)} {vs : List GroundTerm} (h : o = some vs) : o.isSome = true := by
  rw [h]; rfl

/-! ## The terms -/

theorem case_inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm}
    (ih : V4 c σ t r) : V4 c σ (.inj a b t) (r.map (injNormal a b)) := fun r' h' hs => by
  cases h' with
  | inj h'' =>
    rename_i r''
    cases r'' with
    | none => simp at hs
    | some w => rw [ih _ h'' rfl]

theorem case_ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = true) (ihts : V5 c σ ts rs) : V4 c σ (.app f ts) ((allSome rs).map (.ctor f)) :=
  fun r' h' hs => by
    cases h' with
    | ctor _ hts' => rw [ihts _ hts' (allSome_isSome (isSome_of_map hs))]
    | hook h => rw [hk] at h; cases h
    | param h => rw [hk] at h; cases h
    | call h => rw [hk] at h; cases h
    | callUndef h => rw [hk] at h; cases h
    | ovl h => rw [hk] at h; cases h
    | ovlFn h => rw [hk] at h; cases h

theorem case_hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = true)
    (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r)
    (ihts : V5 c σ ts rs) : V4 c σ (.app f ts) r := fun r' h' hs => by
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | @hook _ _ _ rs' _ _ _ hts' hh' hund' =>
    cases hall : allSome rs' with
    | none => rw [hund' hall] at hs; cases hs
    | some vs =>
      have := ihts _ hts' (allSome_isSome (isSome_of_eq hall)); subst this
      exact Option.some.inj ((hh vs hall).symm.trans (hh' vs hall))
  | param _ h => rw [hhk] at h; cases h
  | call _ h => rw [hhk] at h; cases h
  | callUndef _ h => rw [hhk] at h; cases h
  | ovl _ ho => rw [(c.isOvl_parts ho).2.1] at hhk; cases hhk
  | ovlFn _ ho => rw [(c.isOvl_parts ho).2.1] at hhk; cases hhk

theorem case_param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = false)
    (hp : c.isParam f = true) (hr : r = (allSome rs).bind (c.paramVal f))
    (ihts : V5 c σ ts rs) : V4 c σ (.app f ts) r := fun r' h' hs => by
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ h => rw [hhk] at h; cases h
  | param _ _ _ hts' hr' =>
    have := ihts _ hts' (allSome_isSome (isSome_of_bind (hr' ▸ hs))); subst this; rw [hr, hr']
  | call _ _ _ _ _ h => rw [hp] at h; cases h
  | callUndef _ _ _ _ h => rw [hp] at h; cases h
  | ovl _ ho => rw [(c.isOvl_parts ho).2.2.1] at hp; cases hp
  | ovlFn _ ho => rw [(c.isOvl_parts ho).2.2.1] at hp; cases hp

theorem case_call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {r : Option GroundTerm} (hk : c.isCtor f = false)
    (hhk : isHook f = false) (hvs : allSome rs = some vs) (hp : c.isParam f = false)
    (hno : c.isOvl f = false) (ihts : V5 c σ ts rs) (ihf : V1 c f vs r) : V4 c σ (.app f ts) r :=
  fun r' h' hs => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hhk] at h; cases h
    | param _ _ h => rw [hp] at h; cases h
    | call _ _ hts' hvs' hf' _ =>
      have := ihts _ hts' (allSome_isSome (isSome_of_eq hvs')); subst this
      rw [hvs] at hvs'; cases hvs'
      exact ihf _ hf' hs
    | callUndef => cases hs
    | ovl _ ho => rw [hno] at ho; cases ho
    | ovlFn _ ho => rw [hno] at ho; cases ho

theorem case_callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (hhk : isHook f = false) (hvs : allSome rs = none)
    (hp : c.isParam f = false) (ihts : V5 c σ ts rs) : V4 c σ (.app f ts) none := fun r' h' hs => by
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ h => rw [hhk] at h; cases h
  | param _ _ h => rw [hp] at h; cases h
  | call _ _ hts' hvs' _ _ =>
    have := ihts _ hts' (allSome_isSome (isSome_of_eq hvs')); subst this
    rw [hvs] at hvs'; cases hvs'
  | callUndef => cases hs
  | ovl _ _ hts' =>
    have hsm := isSome_of_map hs
    have := ihts _ hts' (allSome_isSome hsm); subst this
    rw [hvs] at hsm; cases hsm
  | ovlFn _ _ hts' hvs' =>
    have := ihts _ hts' (allSome_isSome (isSome_of_eq hvs')); subst this
    rw [hvs] at hvs'; cases hvs'

theorem case_ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (ho : c.isOvl f = true)
    (hnf : ∀ vs, allSome rs = some vs → c.fnCover f vs = none) (ihts : V5 c σ ts rs) :
    V4 c σ (.app f ts) ((allSome rs).map (c.norm f)) := fun r' h' hs => by
  have hp := c.isOvl_parts ho
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ h => rw [hp.2.1] at h; cases h
  | param _ _ h => rw [hp.2.2.1] at h; cases h
  | call _ _ _ _ hf' _ => rw [hf'.isOvl_false] at ho; cases ho
  | callUndef => cases hs
  | ovl _ _ hts' =>
    have := ihts _ hts' (allSome_isSome (isSome_of_map hs)); subst this; rfl
  | ovlFn _ _ hts' hvs' _ hcov' =>
    have := ihts _ hts' (allSome_isSome (isSome_of_eq hvs')); subst this
    rw [hnf _ hvs'] at hcov'; cases hcov'

theorem case_ovlFn {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {o : OvlSig} {kg : CtorSig} {r : Option GroundTerm}
    (hk : c.isCtor f = false) (ho : c.isOvl f = true) (hvs : allSome rs = some vs)
    (hlo : c.lookupOvl f = some o) (hcov : c.fnCover f vs = some kg) (ihts : V5 c σ ts rs)
    (ihf : V1 c kg.name (stripAll kg.args o.sig.args vs) r) :
    V4 c σ (.app f ts) (r.map (lift kg.result o.sig.result)) := fun r' h' hs => by
  have hp := c.isOvl_parts ho
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ h => rw [hp.2.1] at h; cases h
  | param _ _ h => rw [hp.2.2.1] at h; cases h
  | call _ _ _ _ hf' _ => rw [hf'.isOvl_false] at ho; cases ho
  | callUndef => cases hs
  | ovl _ _ hts' hnf' =>
    have := ihts _ hts' (allSome_isSome (isSome_of_map hs)); subst this
    rw [hnf' _ hvs] at hcov; cases hcov
  | @ovlFn _ _ _ _ _ _ _ r₂ _ _ hts' hvs' hlo' hcov' hf' =>
    have := ihts _ hts' (allSome_isSome (isSome_of_eq hvs')); subst this
    rw [hvs] at hvs'; cases hvs'
    rw [hlo] at hlo'; cases hlo'
    rw [hcov] at hcov'; cases hcov'
    have h2 : r₂.isSome = true := by
      cases r₂ with
      | none => cases hs
      | some _ => rfl
    rw [ihf _ hf' h2]

theorem case_cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} (ih1 : V4 c σ t r) (ih2 : V5 c σ ts rs) :
    V5 c σ (t :: ts) (r :: rs) := fun rs' h' hs => by
  cases h' with
  | cons h1 h2 =>
    rw [ih1 _ h1 (hs _ (List.mem_cons_self ..)), ih2 _ h2 (fun x hx => hs x (List.mem_cons_of_mem _ hx))]

/-! ## The sort predicates -/

/-- The clauses of a sort predicate: no `requires`, no `ensures`, not `aside`, a literal on the
right; two distinct ones differ in priority. -/
theorem sortPred_shape {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    (∀ cl ∈ fn.clauses, cl.req = none ∧ cl.ens = none ∧ cl.aside = false ∧ ∃ b, cl.rhs = .dv Srt.bool (.bool b)) ∧
    (∀ cl ∈ fn.clauses, ∀ cl' ∈ fn.clauses, cl.prio = cl'.prio → cl = cl') := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, -, _, _, rfl⟩
  · refine ⟨fun cl hcl => ?_, fun cl hcl cl' hcl' _ => ?_⟩
    · rw [List.mem_singleton] at hcl; subst hcl; exact ⟨rfl, rfl, rfl, _, rfl⟩
    · rw [List.mem_singleton] at hcl hcl'; rw [hcl, hcl']
  all_goals
    refine ⟨fun cl hcl => ?_, fun cl hcl cl' hcl' hp => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> exact ⟨rfl, rfl, rfl, _, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl hcl'
      rcases hcl with rfl | rfl <;> rcases hcl' with rfl | rfl <;>
        first | rfl | exact absurd hp (by simp)

/-! ## The functions -/

theorem matchCtxO (h : c.coreOK = true) : Exec.MatchCtxO c := by
  obtain ⟨hok, -, hha, -, hids⟩ := Semantics.coreOK_parts h
  exact ⟨NamesApart.subsorts_trans_of hids hok, NamesApart.subsorts_irrefl_of hids hok,
    NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls h⟩

section Fns

variable (h : c.coreOK = true) (hpreTop : c.clausesPreTop = true) (hs : FnSolves c) (hnoEx : c.FnsNoExs)
include h hs

omit h hs in
include hnoEx in
/-- No clause of a function has an existential variable. -/
theorem exs_nil {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause} (hmem : cl ∈ fn.clauses) :
    cl.exs = [] :=
  hnoEx.allFns fn (lookupFn_spec hfn).1 cl hmem

omit hs in
/-- A clause of a user function whose patterns denote `vs` under a well-sorted σ: `vs` is of the
function's sorts. -/
theorem sortsOf_of_match {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    {σ : Subst} {vs : List GroundTerm} (hσ : c.WellSorted cl.vars σ) (hm : PatVals c σ cl.pats vs) :
    c.sortsOf vs = some fn.args := by
  obtain ⟨hok, -⟩ := Semantics.coreOK_parts h
  have hf := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  have hcs := hf.1.2 fn hfn cl hcl
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hcs
  exact Det.patVals_sortedAll (matchCtxO h) hσ hm hcs.1.1.1.1.1.1

include hpreTop hnoEx in
theorem case_clause {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
    {σ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses) (hσ : c.WellSorted cl.vars σ)
    (hmatch : PatVals c σ cl.pats vs) (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → V2 c vs cl')
    (ihrhs : V4 c σ cl.rhs r) : V1 c f vs r := fun r' h' hsm => by
  obtain ⟨hall, hlab⟩ := lookupFn_spec hfn
  have hT := Semantics.allFns_preTop hpreTop fn hall
  rcases List.mem_append.mp hall with hu | hp
  · -- a user function: the clause decides as the model reads it, and `FnSolves` applies
    have hdec : cl.DecidesAt c fn σ vs :=
      ⟨⟨hσ.at _, hmatch, hreq, hpre⟩,
        fun cl' h1 h2 h3 σ' hw hp' hq => ihprio cl' h1 h2 h3 σ' hw hp' hq.1 (hT cl' h1)⟩
    cases r' with
    | none => cases hsm
    | some w =>
      have hpl := Semantics.sortedOK_plainCl_of_noExs (Semantics.coreOK_parts h).1 hnoEx fn hall cl hmem
      have hw := (Clause.gives_iff_noExs hpl.1 hpl.2 hσ w).mp
        ((hs fn hu vs (sortsOf_of_match h hu hmem hσ hmatch) cl hmem σ hdec w).mp
          (by rw [hlab]; exact h'))
      exact ihrhs _ hw.1 rfl
  · -- a sort predicate
    obtain ⟨hsh, hpr⟩ := sortPred_shape hp
    obtain ⟨hq, he, ha, b, hb⟩ := hsh cl hmem
    have hr : r = some (.dv Srt.bool (.bool b)) := ihrhs _ (by rw [hb]; exact .dv) rfl
    -- the clause matches, so it does not fail: it has no `requires` and its predicate is `\top`
    have nf : ¬ Fails c vs cl := fun hf => by
      cases hf with
      | intro hf' =>
        cases hf' σ (hσ.at _) hmatch with
        | intro ht _ _ => rw [hq] at ht; cases ht
        | pre hh => rw [hT cl hmem] at hh; exact absurd (Holds.top_eq hh) (by simp)
    cases h' with
    | @clause _ _ _ cl' σ' _ hfn' hmem' hσ' hmatch' hreq' _ hprio' _ hrhs' hens' _ =>
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hq', -, ha', b', hb'⟩ := hsh cl' hmem'
      rcases Nat.lt_trichotomy cl'.prio cl.prio with hlt | heq | hgt
      · exact (ihprio cl' hmem' ha' hlt _ (hσ'.at _) hmatch' hreq' (hT cl' hmem')).elim
      · have := hpr cl hmem cl' hmem' heq.symm; subst this
        have hd : EvalTerm c σ' (.dv Srt.bool (.bool b)) r' := hb ▸ hrhs'
        cases hd; exact hr
      · exact absurd (hprio' cl hmem ha hgt) nf
    | rest hfn' hnone =>
      rw [hfn] at hfn'; cases hfn'
      exact absurd (hnone cl hmem) nf
    | ensFails => cases hsm
    | clauseEx hfn' hmem' _ _ _ _ _ hne' => exact absurd (exs_nil hnoEx hfn' hmem') hne'
    | exNone => cases hsm

include hpreTop hnoEx in
theorem case_ensFails {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
    {σ : Subst} {t : Term} {w : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses) (hσ : c.WellSorted cl.vars σ)
    (hmatch : PatVals c σ cl.pats vs) (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) (ht : cl.ens = some t) (hw : w ≠ some (bool true))
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → V2 c vs cl')
    (ihe : V4 c σ t w) : V1 c f vs none := fun r' h' hsm => by
  obtain ⟨hall, hlab⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hall with hu | hp
  · have hdec : cl.DecidesAt c fn σ vs :=
      ⟨⟨hσ.at _, hmatch, hreq, hpre⟩, fun cl' h1 h2 h3 σ' hw' hp' hq =>
        ihprio cl' h1 h2 h3 σ' hw' hp' hq.1
          (Semantics.allFns_preTop hpreTop fn hall cl' h1)⟩
    cases r' with
    | none => cases hsm
    | some v =>
      have hpl := Semantics.sortedOK_plainCl_of_noExs (Semantics.coreOK_parts h).1 hnoEx fn hall cl hmem
      have hv := (Clause.gives_iff_noExs hpl.1 hpl.2 hσ v).mp
        ((hs fn hu vs (sortsOf_of_match h hu hmem hσ hmatch) cl hmem σ hdec v).mp
          (by rw [hlab]; exact h'))
      exact absurd (ihe _ (hv.2 t ht) rfl) hw
  · rw [((sortPred_shape hp).1 cl hmem).2.1] at ht; cases ht

omit hs in
include hpreTop hnoEx in
theorem case_rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn) (ihnone : ∀ cl ∈ fn.clauses, V2 c vs cl) : V1 c f vs (c.fnRest fn vs) :=
  fun r' h' hsm => by
    cases h' with
    | clause hfn' hmem' hσ' hmatch' hreq' _ _ _ =>
      rw [hfn] at hfn'; cases hfn'
      exact (ihnone _ hmem' _ (hσ'.at _) hmatch' hreq'
        (Semantics.allFns_preTop hpreTop _ (lookupFn_spec hfn).1 _ hmem')).elim
    | rest hfn' _ => rw [hfn] at hfn'; cases hfn'; rfl
    | ensFails => cases hsm
    | clauseEx hfn' hmem' _ _ _ _ _ hne' => exact absurd (exs_nil hnoEx hfn' hmem') hne'
    | exNone => cases hsm

include hpreTop hnoEx in
/-- **A value of a function is each of its results there**, under `coreOK`, `clausesPreTop`,
`FnSolves` and no clause with an existential variable. -/
theorem eval_value {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (he : Eval c f vs r) :
    V1 c f vs r :=
  Eval.rec (motive_1 := fun f vs r _ => V1 c f vs r) (motive_2 := fun vs cl _ => V2 c vs cl)
    (motive_3 := fun σ cl _ => V3 c σ cl) (motive_4 := fun σ t r _ => V4 c σ t r)
    (motive_5 := fun σ ts rs _ => V5 c σ ts rs)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre _ _ _ _ _ _ _ ihprio ihrhs _ _ =>
      case_clause h hpreTop hs hnoEx hfn hmem hσ hmatch hreq hpre ihprio ihrhs)
    (fun hfn _ ihnone => case_rest h hpreTop hnoEx hfn ihnone)
    (fun hfn hmem hσ hmatch hreq hpre _ _ ht _ hw _ _ ihprio ihe =>
      case_ensFails h hpreTop hs hnoEx hfn hmem hσ hmatch hreq hpre ht hw ihprio ihe)
    (fun hfn hmem _ _ _ _ _ hne => by intros; exact absurd (exs_nil hnoEx hfn hmem) hne)
    (fun hfn hmem hne => by intros; exact absurd (exs_nil hnoEx hfn hmem) hne)
    (fun _ ih => fun σ hw hp hq hT => ih σ hw hp hq hT)
    (fun ht _ hr ih => fun hq _ => hr (ih _ (hq _ ht) rfl))
    (fun hh _ => fun _ hT => by rw [hT] at hh; exact absurd (Holds.top_eq hh) (by simp))
    (fun r' h' _ => by cases h'; rfl)
    (fun r' h' _ => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh _ ihts => case_hook hk hhk hh ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ hnf ihts => case_ovl hk ho hnf ihts)
    (fun hk ho _ hvs hlo hcov _ ihts ihf => case_ovlFn hk ho hvs hlo hcov ihts ihf)
    (fun rs' h' _ => by cases h'; rfl)
    (fun _ _ ih1 ih2 => case_cons ih1 ih2)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    he

end Fns

/-- **Under `coreOK`, `clausesPreTop` and no clause with an existential variable, `FnSolves` gives
`FnDet`**: no semantics whose clauses' predicates are all `\top` and whose clauses bind no
variable by `\exists` meets `coreOK` and `FnSolves` without `FnDet`. -/
theorem fnDet_of_fnSolves (h : c.coreOK = true) (hpreTop : c.clausesPreTop = true) (hs : FnSolves c)
    (hnoEx : c.FnsNoExs) : FnDet c := by
  intro f vs r r' h1 h2
  cases r' with
  | some w => exact eval_value h hpreTop hs hnoEx h1 _ h2 rfl
  | none =>
    cases r with
    | none => rfl
    | some w => exact (eval_value h hpreTop hs hnoEx h2 _ h1 rfl).symm

/-! ## The statements that read `FnDet` beside `FnSolves` -/

/-- `consistent_of` (pinned, test/Pins.lean) with its `FnDet` from its other hypotheses. -/
example (c : Semantics) (h : c.coreOK = true) (hpreTop : c.clausesPreTop = true) (hs : FnSolves c)
    (hnoEx : c.FnsNoExs) (hp : ClausePreDecided c) (hl : OpenLaws c) : Consistent c :=
  consistent_of c h (fnDet_of_fnSolves h hpreTop hs hnoEx) hs hp
    (clausePostDecided_of_top fun fn hfn cl hcl =>
      (Semantics.sortedOK_plainCl_of_noExs (Semantics.coreOK_parts h).1 hnoEx fn (List.mem_append_left _ hfn) cl hcl).2) hl

/-! ## Without `clausesPreTop` -/

/-- **`coreOK` and `FnSolves` do not give `FnDet`** where a clause has a predicate that is not
`\top`: `FnDetWitness.c` meets both and not `FnDet`. -/
theorem not_fnDet_of_fnSolves : ¬ ∀ c : Semantics, c.coreOK = true → FnSolves c → FnDet c :=
  fun h => FnDetWitness.not_fnDet (h _ FnDetWitness.coreOK FnDetWitness.fnSolves)

/-- The semantics that shows it is outside `fnDet_of_fnSolves`: a clause of it has a predicate
that is not `\top`. -/
example : FnDetWitness.c.clausesPreTop = false := FnDetWitness.not_preTop

/-- **`consistent_of` cannot lose `FnDet`**: its other hypotheses do not give `Consistent`. -/
theorem consistent_needs_fnDet :
    ¬ ∀ c : Semantics, c.coreOK = true → FnSolves c → ClausePreDecided c → ClausePostDecided c → OpenLaws c →
      Consistent c :=
  fun h => FnDetWitness.not_consistent
    (h _ FnDetWitness.coreOK FnDetWitness.fnSolves FnDetWitness.clausePreDecided
      FnDetWitness.clausePostDecided FnDetWitness.openLaws)

/-! ## An instance: a definition meeting both hypotheses -/

/-- The configuration `<k> K </k>` with the counter and no function: `FnSolves` holds, there being
no function. -/
def c0 : Semantics :=
  { lib := { ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
    ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
      ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
    fns := []
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := [] }

theorem instance_c0 : FnDet c0 :=
  fnDet_of_fnSolves (by decide +kernel) rfl (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)

end FnSolvesDet

end KCore

/-- info: 'KCore.FnSolvesDet.fnDet_of_fnSolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnSolvesDet.fnDet_of_fnSolves
/-- info: 'KCore.FnSolvesDet.instance_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnSolvesDet.instance_c0
/-- info: 'KCore.FnSolvesDet.not_fnDet_of_fnSolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnSolvesDet.not_fnDet_of_fnSolves
/-- info: 'KCore.FnSolvesDet.consistent_needs_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnSolvesDet.consistent_needs_fnDet
