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
  - `coreOK` also admits a clause with existential variables, each of a confined sort or fixed by
    the clause's right-side predicate, and `Eval.clauseEx` and `Eval.exNone` read that predicate by
    `Holds`, which has `ceil` and `not`. There too `FnSolves` does not give `FnDet`, every clause's
    predicate being `\top` (`not_fnDet_of_fnSolves_preTop`): `FnDetExsWit.c` below, the same
    definition with `¬⌈a(X)⌉` in the right-side predicate of `u`'s clause beside an existential
    variable it fixes, meets `coreOK`, `clausesPreTop`, `FnSolves`, `ClausePreDecided`,
    `ClausePostDecided` and `OpenLaws`, `a` has two results at 0, and its `Γc` has no model. So
    `fnDet_of_fnSolves` cannot lose `FnsNoExs`, and `consistent_of` cannot lose `FnDet` where every
    clause's predicate is `\top` (`consistent_needs_fnDet_preTop`). The existential variable has one
    value there: what the right-side predicate adds is a reading that is true from a derivation of
    none, as a premise's predicate does.
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
  `ensFails`) holds and the failure `ReqFails.pre` does not occur. A right-side predicate beside
  existential variables (which `coreOK` admits, so `FnsNoExs` is a hypothesis here) or another
  `pre` (each a `Cond` whose `Holds` has `ceil` and `not`, so that it can hold because a term is
  undefined) gives a witness; the recursor call below stops elaborating when the block changes,
  which is the signal to decide the question again on the new block.

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

/-! ## With `clausesPreTop`, a clause with an existential variable

`FnDetExsWit.c`: two functions over Int, every clause's predicate `\top`:
- `a(X) => 1` (`aCl1`) and `a(X) => 1 ensures u(X)` (`aCl2`), of one priority;
- `u(X) => true` with the existential variable `Z : Int` and the right-side predicate
  `Z = 0 ∧ ¬⌈a(X)⌉` (`uCl`), which fixes `Z`.
At an Int `w`:
- `a(w)` is 1 by `aCl1` (`a_one`);
- so the right-side predicate is false at every instance, an instance exists, and `u(w)` has no
  value by `Eval.exNone` (`u_none`);
- so `aCl2`'s `ensures` is not `true`, and `a(w)` has no value by `Eval.ensFails` (`a_none`);
- so the right-side predicate is also true at `Z = 0`, every instance gives `true` or is read as
  giving nothing, and `u(w)` is `true` by `Eval.clauseEx` (`u_true`).
The existential variable has one value; what has two results is `a`, a value and none, through
`Holds.not` over `Holds.ceil` in a right-side predicate, which `coreOK` admits only on a clause
with an existential variable. `FnSolves` holds: it speaks of values only.

In a model of `Γc`, `a(0)` would denote the element of 1 and nothing (`no_model_c`): `aCl1`'s
sentence states `a(x) = 1`; then `¬⌈a(x)⌉` is nothing, so is `u(x)`, and `aCl2`'s states
`a(x) = 1 ∧ ⌈u(x) = true⌉`, nothing. The definition reads a confined sort (its clause has a
variable its patterns do not bind), so its theory is `Γc`, and `Consistent` is about `Γc`. -/

namespace FnDetExsWit

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def A : Sym := nRegSyms + 4
def Uu : Sym := nRegSyms + 5

def one : GroundTerm := .dv Srt.int (.int 1)
def zero : GroundTerm := .dv Srt.int (.int 0)
def tt : GroundTerm := .dv Srt.bool (.bool true)

/-- `a(X) => 1`. -/
def aCl1 : Clause := ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 1), none, 50, false, [], .top, .top⟩
/-- `a(X) => 1 ensures u(X)`. -/
def aCl2 : Clause :=
  ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 1), some (.app Uu [.var 0]), 50, false, [], .top, .top⟩
def aFn : Fn := ⟨A, [Srt.int], Srt.int, [aCl1, aCl2], false⟩

/-- `Z = 0 ∧ ¬⌈a(X)⌉`. -/
def postU : Cond :=
  .and (.equals Srt.int (.var 1) (.dv Srt.int (.int 0))) (.not (.ceil Srt.int (.app A [.var 0])))

/-- `u(X) => true` with `Z` existential and the right-side predicate `Z = 0 ∧ ¬⌈a(X)⌉`. -/
def uCl : Clause :=
  ⟨[Srt.int, Srt.int], [.var 0], none, .dv Srt.bool (.bool true), none, 50, false, [1], .top, postU⟩
def uFn : Fn := ⟨Uu, [Srt.int], Srt.bool, [uCl], false⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbla", "Lblu"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [aFn, uFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- `coreOK` accepts `c`. -/
theorem coreOK : c.coreOK = true := by decide +kernel

/-- Every clause's predicate is `\top`. -/
theorem preTop : c.clausesPreTop = true := by decide +kernel

/-- A clause of `c` has an existential variable. -/
theorem not_noExs : ¬ c.FnsNoExs := fun h => by
  have := h uFn (by simp [c]) uCl (by simp [uFn])
  cases this

theorem lookups : c.lookupFn A = some aFn ∧ c.lookupFn Uu = some uFn := ⟨rfl, rfl⟩

theorem kinds : c.isCtor A = false ∧ isHook A = false ∧ c.isParam A = false ∧ c.isOvl A = false ∧
    c.isCtor Uu = false ∧ isHook Uu = false ∧ c.isParam Uu = false ∧ c.isOvl Uu = false := by decide +kernel

theorem aCl_of {cl : Clause} (h : cl ∈ aFn.clauses) : cl = aCl1 ∨ cl = aCl2 := by simpa [aFn] using h
theorem uCl_of {cl : Clause} (h : cl ∈ uFn.clauses) : cl = uCl := by simpa [uFn] using h
theorem mem_fns {fn : Fn} (h : fn ∈ c.fns) : fn = aFn ∨ fn = uFn := by simpa [c] using h

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals c σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- A substitution that gives X the Int `w` and Z an Int is well sorted for `[Int, Int]`, and
for `[Int]`. -/
theorem sorted2 {σ : Subst} {w z : GroundTerm} (h0 : σ.lookup 0 = some w) (hw : c.sortOf w = some Srt.int)
    (h1 : σ.lookup 1 = some z) (hz : c.sortOf z = some Srt.int) : c.WellSorted [Srt.int, Srt.int] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨w, h0, hw⟩
  | 1, hs => cases hs; exact ⟨z, h1, hz⟩
  | i + 2, hs => simp at hs

theorem sorted1 {σ : Subst} {w : GroundTerm} (h0 : σ.lookup 0 = some w) (hw : c.sortOf w = some Srt.int) :
    c.WellSorted [Srt.int] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨w, h0, hw⟩
  | i + 1, hs => simp at hs

/-- X is `w` and Z is 0. -/
def sg (w : GroundTerm) : Subst := [(0, w), (1, zero)]

theorem zero_int : c.sortOf zero = some Srt.int := by decide +kernel

theorem sg_match (w : GroundTerm) : PatVals c (sg w) [.var 0] [w] := .cons (.var rfl) .nil

/-- A call of `f` at the variable X, where X is `w`, has `f`'s result at `w`. -/
theorem call_mk {f : Sym} (hk : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = false)
    {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) {r : Option GroundTerm} (h : Eval c f [w] r) :
    EvalTerm c σ (.app f [.var 0]) r :=
  .call (vs := [w]) hk hh (.cons .var .nil) (by rw [hl]; rfl) h hp

section Results

variable {w : GroundTerm} (hw : c.sortOf w = some Srt.int)
include hw

omit hw in
/-- No clause of `a` is of a smaller priority than another. -/
theorem a_prio {cl : Clause} (hcl : cl ∈ aFn.clauses) :
    ∀ cl' ∈ aFn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c [w] cl' := by
  intro cl' hcl' _ hlt
  rcases aCl_of hcl with rfl | rfl <;> rcases aCl_of hcl' with rfl | rfl <;> exact absurd hlt (Nat.lt_irrefl _)

omit hw in
theorem u_prio : ∀ cl' ∈ uFn.clauses, cl'.aside = false → cl'.prio < uCl.prio → Fails c [w] cl' :=
  fun cl' hcl' _ hlt => by rw [uCl_of hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _)

/-- **`a(w)` is 1**, by its first clause. -/
theorem a_one : Eval c A [w] (some one) :=
  .clause (fn := aFn) (cl := aCl1) (σ := sg w) lookups.1 (List.mem_cons_self ..) (sorted1 rfl hw) (sg_match _)
    (fun _ ht => nomatch ht) .top (a_prio (List.mem_cons_self ..)) rfl .dv (fun _ ht => nomatch ht) .top

/-- `Z = 0 ∧ ¬⌈a(X)⌉` is false where X is `w`: `a(w)` has a value. -/
theorem post_false {σ : Subst} (hl : σ.lookup 0 = some w) : Holds c 2 σ postU false := by
  have h : Holds c 2 σ postU (sameResult (σ.lookup 1) (some zero) && !(some one).isSome) :=
    .and (.equals .var .dv) (.not (.ceil (call_mk kinds.1 kinds.2.1 kinds.2.2.1 hl (a_one hw))))
  simpa using h

omit hw in
/-- X is `w` at an instance of `u`'s clause at a match where X is `w`. -/
theorem inst_x {σ σ' : Subst} (hl : σ.lookup 0 = some w) (ha : AgreeOff uCl.exsFree σ σ') :
    σ'.lookup 0 = some w := (ha 0 (by decide)).trans hl

/-- **`u(w)` has no value**: every instance of its clause's right side gives nothing. -/
theorem u_none : Eval c Uu [w] none :=
  .exNone (fn := uFn) (cl := uCl) (σ := sg w) lookups.2 (List.mem_singleton_self _) (by decide)
    ((sorted2 rfl hw rfl zero_int).at _) (sg_match _) (fun _ ht => nomatch ht) .top u_prio
    ⟨sg w, AgreeOff.refl _ _, sorted2 rfl hw rfl zero_int⟩
    (fun _ ha _ => .fails (post_false hw (inst_x rfl ha)) (.post (post_false hw (inst_x rfl ha))))

/-- **`a(w)` has no value**, by its second clause, whose `ensures` `u(X)` is not `true`. -/
theorem a_none : Eval c A [w] none :=
  .ensFails (fn := aFn) (cl := aCl2) (σ := sg w) (w := none) lookups.1
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (sorted1 rfl hw) (sg_match _)
    (fun _ ht => nomatch ht) .top (a_prio (List.mem_cons_of_mem _ (List.mem_singleton_self _))) rfl rfl
    (call_mk kinds.2.2.2.2.1 kinds.2.2.2.2.2.1 kinds.2.2.2.2.2.2.1 rfl (u_none hw)) (by intro h; cases h)

/-- `Z = 0 ∧ ¬⌈a(X)⌉` is true where X is `w` and Z is 0: `a(w)` has the result none. -/
theorem post_true {σ : Subst} (hl : σ.lookup 0 = some w) (hz : σ.lookup 1 = some zero) :
    Holds c 2 σ postU true := by
  have h : Holds c 2 σ postU (sameResult (σ.lookup 1) (some zero) && !(none : Option GroundTerm).isSome) :=
    .and (.equals .var .dv) (.not (.ceil (call_mk kinds.1 kinds.2.1 kinds.2.2.1 hl (a_none hw))))
  rw [hz] at h
  exact h

/-- **`u(w)` is `true`**: the instance at `Z = 0` gives it, and every instance is read as giving
nothing. -/
theorem u_true : Eval c Uu [w] (some tt) :=
  .clauseEx (fn := uFn) (cl := uCl) (σ := sg w) lookups.2 (List.mem_singleton_self _)
    (sorted2 rfl hw rfl zero_int) (sg_match _) (fun _ ht => nomatch ht) .top u_prio (by decide) .dv
    (fun _ ht => nomatch ht) (post_true hw rfl rfl)
    (fun _ ha _ => .fails (post_false hw (inst_x rfl ha)) (.post (post_false hw (inst_x rfl ha))))

end Results

/-- `a` has no result but 1 and none. -/
theorem a_res {w : GroundTerm} {r : Option GroundTerm} (h : Eval c A [w] r) :
    r = some one ∨ r = none := by
  cases h with
  | clause hfn hcl _ _ _ _ _ _ hrhs _ _ =>
    obtain rfl := Option.some.inj (lookups.1.symm.trans hfn)
    rcases aCl_of hcl with rfl | rfl <;> exact .inl (EvalTerm.dv_inv hrhs)
  | rest hfn hnone =>
    obtain rfl := Option.some.inj (lookups.1.symm.trans hfn)
    exact .inr rfl
  | ensFails => exact .inr rfl
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj (lookups.1.symm.trans hfn)
    rcases aCl_of hcl with rfl | rfl <;> exact absurd rfl hne
  | exNone => exact .inr rfl

/-- `u` has no result but `true` and none. -/
theorem u_res {w : GroundTerm} {r : Option GroundTerm} (h : Eval c Uu [w] r) : r = some tt ∨ r = none := by
  cases h with
  | clause hfn hcl _ _ _ _ _ hex _ _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    obtain rfl := uCl_of hcl
    cases hex
  | rest hfn hnone =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    exact .inr rfl
  | ensFails => exact .inr rfl
  | clauseEx hfn hcl _ _ _ _ _ _ hrhs _ _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    obtain rfl := uCl_of hcl
    exact .inl (EvalTerm.dv_inv hrhs)
  | exNone => exact .inr rfl

/-! ### The hypotheses -/

theorem i0_int : c.sortOf (.dv Srt.int (.int 0)) = some Srt.int := by decide +kernel

/-- **Not `FnDet`**: `a(0)` has the results 1 and none. -/
theorem not_fnDet : ¬ FnDet c := fun hd => by
  have := hd _ _ _ _ (a_one i0_int) (a_none i0_int)
  cases this

/-- What a clause of `a` that applies gives: X is an Int `w`, and the argument list is `[w]`. -/
theorem applies_a {cl : Clause} (hv : cl.vars = [Srt.int]) (hp : cl.pats = [.var 0]) (hex : cl.exs = [])
    {σ : Subst} {vs : List GroundTerm} (ha : cl.AppliesAt c σ vs) :
    ∃ w, σ.lookup 0 = some w ∧ c.sortOf w = some Srt.int ∧ vs = [w] ∧ c.WellSorted cl.vars σ := by
  have hσ := (wellSortedAt_univ hex).mp ha.1
  have hm := ha.2.1
  rw [hp] at hm
  obtain ⟨w', rfl, hl'⟩ := match0 hm
  obtain ⟨w, hl, hw⟩ := hσ 0 Srt.int (by rw [hv]; rfl)
  rw [hl] at hl'; cases hl'
  exact ⟨_, hl, hw, rfl, hσ⟩

/-- **Evaluation solves the equations of `c`**: the values of `a` at an Int are 1 alone, which each
of its clauses gives at its match, `u(X)` having the value `true`; the values of `u` are `true`
alone, which the instance of its clause at `Z = 0` gives. -/
theorem fnSolves : FnSolves c := by
  intro fn hfn vs _ cl hcl σ hdec v
  rcases mem_fns hfn with rfl | rfl
  · rcases aCl_of hcl with rfl | rfl
    · obtain ⟨w, hl, hw, rfl, hσ⟩ := applies_a rfl rfl rfl hdec.1
      refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := aCl1) rfl rfl hσ v).symm
      constructor
      · intro h
        rcases a_res h with h1 | h1
        · cases h1; exact ⟨.dv, fun _ ht => nomatch ht⟩
        · cases h1
      · rintro ⟨hr, -⟩
        cases (EvalTerm.dv_inv hr : some v = some one)
        exact a_one hw
    · obtain ⟨w, hl, hw, rfl, hσ⟩ := applies_a rfl rfl rfl hdec.1
      refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := aCl2) rfl rfl hσ v).symm
      constructor
      · intro h
        rcases a_res h with h1 | h1
        · cases h1
          exact ⟨.dv, fun t ht => by
            cases ht
            exact call_mk kinds.2.2.2.2.1 kinds.2.2.2.2.2.1 kinds.2.2.2.2.2.2.1 hl (u_true hw)⟩
        · cases h1
      · rintro ⟨hr, -⟩
        cases (EvalTerm.dv_inv hr : some v = some one)
        exact a_one hw
  · obtain rfl := uCl_of hcl
    obtain ⟨w, rfl, hl⟩ := match0 hdec.1.2.1
    have hw : c.sortOf w = some Srt.int := by
      obtain ⟨w', hl', hw'⟩ := hdec.1.1 0 (by decide) Srt.int rfl
      rw [hl] at hl'; cases hl'; exact hw'
    constructor
    · intro h
      rcases u_res h with h1 | h1
      · cases h1
        have h0 : ((1, zero) :: σ).lookup 0 = some w := by simpa [List.lookup] using hl
        have h1 : ((1, zero) :: σ).lookup 1 = some zero := by first | rfl | simp [List.lookup]
        refine ⟨(1, zero) :: σ, fun i hi => ?_, sorted2 h0 hw h1 zero_int,
          ⟨.dv, (fun _ ht => nomatch ht), post_true hw h0 h1⟩⟩
        have hi1 : (i == 1) = false := by
          cases hb : i == 1
          · rfl
          · exact absurd (by rw [beq_iff_eq.mp hb]; decide) hi
        simp [List.lookup, hi1]
      · cases h1
    · rintro ⟨σ', -, -, hr, -, -⟩
      cases (EvalTerm.dv_inv hr : some v = some tt)
      exact u_true hw

theorem clausePreDecided : ClausePreDecided c := clausePreDecided_of_isTop (by decide +kernel)

theorem openLaws : OpenLaws c := openLaws_of_plain (by decide +kernel)

/-- **Each clause's right-side predicate has a truth value at each well-sorted instance**:
`Z = 0 ∧ ¬⌈a(X)⌉` is false there (and, at `Z = 0`, true). -/
theorem clausePostDecided : ClausePostDecided c := by
  intro fn hfn cl hcl σ hσ
  rcases mem_fns hfn with rfl | rfl
  · rcases aCl_of hcl with rfl | rfl <;> exact ⟨true, .top⟩
  · obtain rfl := uCl_of hcl
    obtain ⟨w, hl, hw⟩ := hσ 0 Srt.int rfl
    exact ⟨false, post_false hw hl⟩

/-! ### `Γc` has no model -/

section NoModel

open ML Faithful HoldsShape

/-- No clause of `c` has conditions that need a witness. -/
theorem noWitness : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
  intro fn hfn cl hcl h
  have h0 : c.fns.all (fun f => f.clauses.all fun cl => !cl.needsWitness c) = true := by decide +kernel
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h0 fn hfn) cl hcl
  rw [h] at h1; cases h1

/-- **`Γc` has no model**: `a(0)` would denote the element of 1, its result by the first clause,
and nothing, its result by the second. -/
theorem no_model_c : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γc c) := by
  intro M _ I hIc
  have h := Semantics.coreOK_iff_ex.mp coreOK
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hneg := neg_of_coreClEx hIc (Semantics.sortedOKClEx_of_sortedOKEx hok) hsr (Semantics.coreOKEx_parts h).2.1
    hph noWitness (preReadAll_of_coreEx h hIc)
  have hden := fun (r : Option GroundTerm) (hev : Eval c A [.dv Srt.int (.int 0)] r) (e : Valuation M) (m : M) =>
    eval_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) hneg (preReadAll_of_coreEx h hIc)
      (clauseExRead_all_of_coreEx h hIc) hev lookups.1 (by decide +kernel) e m
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  obtain ⟨hone, -⟩ := elemOf_spec hI (v := one) (s := Srt.int) (by decide +kernel) e
  have h1 := (hden _ (a_one i0_int) e (elemOf c I one)).mpr ((hone _).mpr rfl)
  exact (hden _ (a_none i0_int) e (elemOf c I one)).mp h1

/-- **Not `Consistent`**: `Γc` is part of `Γc ∪ Γstep`. -/
theorem not_consistent : ¬ Consistent c := fun ⟨M, hM, I, hI⟩ =>
  no_model_c M hM I (fun φ hφ => hI φ (Or.inl hφ))

end NoModel

end FnDetExsWit

namespace FnSolvesDet

/-- **`coreOK`, `clausesPreTop` and `FnSolves` do not give `FnDet`** where a clause has an
existential variable: `FnDetExsWit.c` meets the three and not `FnDet`. So `fnDet_of_fnSolves`
cannot lose `FnsNoExs`. -/
theorem not_fnDet_of_fnSolves_preTop :
    ¬ ∀ c : Semantics, c.coreOK = true → c.clausesPreTop = true → FnSolves c → FnDet c :=
  fun h => FnDetExsWit.not_fnDet (h _ FnDetExsWit.coreOK FnDetExsWit.preTop FnDetExsWit.fnSolves)

/-- **`consistent_of` cannot lose `FnDet` where every clause's predicate is `\top`**: its other
hypotheses and `clausesPreTop` do not give `Consistent`. -/
theorem consistent_needs_fnDet_preTop :
    ¬ ∀ c : Semantics, c.coreOK = true → c.clausesPreTop = true → FnSolves c → ClausePreDecided c →
      ClausePostDecided c → OpenLaws c → Consistent c :=
  fun h => FnDetExsWit.not_consistent
    (h _ FnDetExsWit.coreOK FnDetExsWit.preTop FnDetExsWit.fnSolves FnDetExsWit.clausePreDecided
      FnDetExsWit.clausePostDecided FnDetExsWit.openLaws)

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
/-- info: 'KCore.FnSolvesDet.not_fnDet_of_fnSolves_preTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnSolvesDet.not_fnDet_of_fnSolves_preTop
/-- info: 'KCore.FnSolvesDet.consistent_needs_fnDet_preTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnSolvesDet.consistent_needs_fnDet_preTop
