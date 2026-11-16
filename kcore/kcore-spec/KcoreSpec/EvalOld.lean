/-
  KCore. The evaluation of a plain definition, kept under its own names: `Eval₀`, `Fails₀`,
  `ReqFails₀`, `EvalTerm₀`, `EvalTerms₀` are the mutual block of Evaluation.lean, constructor for
  constructor, over the same matching (`PatVal`), well-sortedness, hooks, parameters, overloads and
  rest. `Step₀` and `NotApplies₀` (StepOld.lean) read them. Where the definition is plain the two
  blocks have the same derivations (`eval_plain`, `evalTerm_plain`, `fails_plain`).
-/
import KcoreSpec.Statements

set_option autoImplicit false

namespace KCore

mutual
  /-- `Eval₀ c f vs r`: the function `f` of `c` at `vs` has the result `r` (`none`: undefined). -/
  inductive Eval₀ (c : Semantics) : Sym → List GroundTerm → Option GroundTerm → Prop where
    /-- A clause that applies decides, when no clause of a smaller priority applies: its
    patterns denote `vs` under a well-sorted σ, its `requires` evaluates to `true` under σ, and
    every clause of a smaller priority fails. Where its `ensures` evaluates to `true` (or it has
    none), the result is its right-hand side's. -/
    | clause {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
        {σ : Subst} {r : Option GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hmem : cl ∈ fn.clauses)
        (hσ : c.WellSorted cl.vars σ)
        (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm₀ c σ t (some (bool true)))
        (hprio : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails₀ c vs cl')
        (hrhs : EvalTerm₀ c σ cl.rhs r)
        (hens : ∀ t, cl.ens = some t → EvalTerm₀ c σ t (some (bool true))) : Eval₀ c f vs r
    /-- Where every clause fails, `f` has its rest (`fnRest`). -/
    | rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hnone : ∀ cl ∈ fn.clauses, Fails₀ c vs cl) : Eval₀ c f vs (c.fnRest fn vs)
    /-- A clause that decides (as in `clause`) whose `ensures` evaluates to something other than
    `true` (`false`, or undefined): `f` has no value there, `rhs ∧ ⊥` being empty whatever the
    right-hand side is. The rest is not read. -/
    | ensFails {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
        {σ : Subst} {t : Term} {w : Option GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hmem : cl ∈ fn.clauses)
        (hσ : c.WellSorted cl.vars σ)
        (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm₀ c σ t (some (bool true)))
        (hprio : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails₀ c vs cl')
        (ht : cl.ens = some t) (he : EvalTerm₀ c σ t w) (hw : w ≠ some (bool true)) :
        Eval₀ c f vs none
  /-- `Fails₀ c vs cl`: the clause does not apply at `vs`: for every well-sorted σ under which its
  patterns denote `vs`, it has a `requires` that evaluates to something other than `true`
  (`false`, or undefined). With no `requires`, no σ may match. -/
  inductive Fails₀ (c : Semantics) : List GroundTerm → Clause → Prop where
    | intro {vs : List GroundTerm} {cl : Clause}
        (h : ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs → ReqFails₀ c σ cl) :
        Fails₀ c vs cl
  /-- `ReqFails₀ c σ cl`: the clause has a `requires` whose result under σ is not `true`. -/
  inductive ReqFails₀ (c : Semantics) : Subst → Clause → Prop where
    | intro {σ : Subst} {cl : Clause} {t : Term} {r : Option GroundTerm}
        (ht : cl.req = some t) (he : EvalTerm₀ c σ t r) (hr : r ≠ some (bool true)) :
        ReqFails₀ c σ cl
  /-- `EvalTerm₀ c σ t r`: the right-hand side (or `requires`) `t` has the result `r` under σ. -/
  inductive EvalTerm₀ (c : Semantics) : Subst → Term → Option GroundTerm → Prop where
    | var {σ : Subst} {i : Nat} : EvalTerm₀ c σ (.var i) (σ.lookup i)
    | dv {σ : Subst} {s : Srt} {lit : Lit} : EvalTerm₀ c σ (.dv s lit) (some (.dv s lit))
    | inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (h : EvalTerm₀ c σ t r) :
        EvalTerm₀ c σ (.inj a b t) (r.map (injNormal a b))
    /-- A constructor of `c` builds the constructor term (undefined if an argument is). -/
    | ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = true) (hts : EvalTerms₀ c σ ts rs) :
        EvalTerm₀ c σ (.app f ts) ((allSome rs).map (.ctor f))
    /-- An interpreted hooked symbol has its meaning (Hooks.lean), and at a silent point the
    interpretation's value (`hookRes`). -/
    | hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = true) (hts : EvalTerms₀ c σ ts rs)
        (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r)
        (hund : allSome rs = none → r = none) : EvalTerm₀ c σ (.app f ts) r
    /-- A parameter symbol has the value `paramVal` gives it, on defined arguments;
    undefined if an argument is. -/
    | param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true)
        (hts : EvalTerms₀ c σ ts rs) (hr : r = (allSome rs).bind (c.paramVal f)) :
        EvalTerm₀ c σ (.app f ts) r
    /-- A function of `c` is called on defined arguments. -/
    | call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {vs : List GroundTerm} {r : Option GroundTerm}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms₀ c σ ts rs)
        (hvs : allSome rs = some vs) (hf : Eval₀ c f vs r) (hp : c.isParam f = false) :
        EvalTerm₀ c σ (.app f ts) r
    /-- A call with an undefined argument is undefined. -/
    | callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms₀ c σ ts rs)
        (hvs : allSome rs = none) (hp : c.isParam f = false) : EvalTerm₀ c σ (.app f ts) none
    /-- An overloading symbol builds the normal form (`norm`; undefined if an argument is). -/
    | ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTerms₀ c σ ts rs) :
        EvalTerm₀ c σ (.app f ts) ((allSome rs).map (c.norm f))
  inductive EvalTerms₀ (c : Semantics) : Subst → List Term → List (Option GroundTerm) → Prop where
    | nil {σ : Subst} : EvalTerms₀ c σ [] []
    | cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
        {rs : List (Option GroundTerm)}
        (h : EvalTerm₀ c σ t r) (hs : EvalTerms₀ c σ ts rs) : EvalTerms₀ c σ (t :: ts) (r :: rs)
end

/-! ## The two blocks have the same derivations

`Fails` ranges over the substitutions well sorted on the variables of the patterns and conditions,
`Fails₀` over those well sorted on every variable; `Eval` reads only the smaller-priority clauses
that are not `aside`, `Eval₀` all of them. A derivation of `Eval` is one of `Eval₀` wherever no
clause evaluation reaches is `aside` (`Semantics.aside_of_plain`); a derivation of `Eval₀` is one of
`Eval` wherever the patterns of every clause that evaluation reaches
bind every variable: in a plain definition (`Semantics.binds_of_plain`). -/

/-- The patterns of every clause of a function of a plain definition bind each of its variables:
the user's by `plain`, the generated sort predicates' by their text. -/
theorem Semantics.binds_of_plain_mem {c : Semantics} (hp : c.plain = true) {fn : Fn}
    (hfn : fn ∈ c.allFns) : ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true := by
  simp only [Semantics.allFns, List.mem_append] at hfn
  rcases hfn with hfn | hfn
  · simp only [Semantics.plain, Bool.and_eq_true, List.all_eq_true] at hp
    intro cl hcl
    exact (hp.1.1.1.2 fn hfn cl hcl).2
  · exact Semantics.sortPreds_binds hfn

theorem Semantics.binds_of_plain {c : Semantics} (hp : c.plain = true) {f : Sym} {fn : Fn}
    (hfn : c.lookupFn f = some fn) : ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true := by
  rw [Semantics.lookupFn_eq] at hfn
  exact Semantics.binds_of_plain_mem hp (List.mem_of_find?_eq_some hfn)

/-- No clause of a function of a plain definition is `aside`: the user's by `plain`, the generated
sort predicates' by their text. -/
theorem Semantics.aside_of_plain_mem {c : Semantics} (hp : c.plain = true) {fn : Fn}
    (hfn : fn ∈ c.allFns) : ∀ cl ∈ fn.clauses, cl.aside = false := by
  simp only [Semantics.allFns, List.mem_append] at hfn
  rcases hfn with hfn | hfn
  · simp only [Semantics.plain, Bool.and_eq_true, List.all_eq_true] at hp
    intro cl hcl
    simpa using (hp.1.1.1.2 fn hfn cl hcl).1.1.1.1
  · simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_filterMap, Option.map_eq_some_iff] at hfn
    rcases hfn with rfl | rfl | ⟨X, -, _, _, rfl⟩ <;> intro cl hcl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl <;>
      rcases hcl with rfl | rfl <;> rfl

theorem Semantics.aside_of_plain {c : Semantics} (hp : c.plain = true) {f : Sym} {fn : Fn}
    (hfn : c.lookupFn f = some fn) : ∀ cl ∈ fn.clauses, cl.aside = false := by
  rw [Semantics.lookupFn_eq] at hfn
  exact Semantics.aside_of_plain_mem hp (List.mem_of_find?_eq_some hfn)

mutual
  theorem Eval.to_old {c : Semantics}
      (hA : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, cl.aside = false) : ∀ {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm},
      Eval c f vs r → Eval₀ c f vs r
    | _, _, _, .clause hfn hmem hσ hmatch hreq hprio hrhs hens =>
        .clause hfn hmem hσ hmatch (fun t ht => EvalTerm.to_old hA (hreq t ht))
          (fun cl' h1 h2 => Fails.to_old hA (hprio cl' h1 (hA hfn cl' h1) h2))
          (EvalTerm.to_old hA hrhs) (fun t ht => EvalTerm.to_old hA (hens t ht))
    | _, _, _, .rest hfn hnone => .rest hfn (fun cl h => Fails.to_old hA (hnone cl h))
    | _, _, _, .ensFails hfn hmem hσ hmatch hreq hprio ht he hw =>
        .ensFails hfn hmem hσ hmatch (fun t ht => EvalTerm.to_old hA (hreq t ht))
          (fun cl' h1 h2 => Fails.to_old hA (hprio cl' h1 (hA hfn cl' h1) h2))
          ht (EvalTerm.to_old hA he) hw
  theorem Fails.to_old {c : Semantics}
      (hA : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, cl.aside = false) : ∀ {vs : List GroundTerm} {cl : Clause}, Fails c vs cl → Fails₀ c vs cl
    | _, _, .intro h => .intro fun σ hσ hp => ReqFails.to_old hA (h σ (hσ.at _) hp)
  theorem ReqFails.to_old {c : Semantics}
      (hA : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, cl.aside = false) : ∀ {σ : Subst} {cl : Clause}, ReqFails c σ cl → ReqFails₀ c σ cl
    | _, _, .intro ht he hr => .intro ht (EvalTerm.to_old hA he) hr
  theorem EvalTerm.to_old {c : Semantics}
      (hA : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, cl.aside = false) : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm},
      EvalTerm c σ t r → EvalTerm₀ c σ t r
    | _, _, _, .var => .var
    | _, _, _, .dv => .dv
    | _, _, _, .inj h => .inj (EvalTerm.to_old hA h)
    | _, _, _, .ctor h hts => .ctor h (EvalTerms.to_old hA hts)
    | _, _, _, .hook h hhk hts hh hund => .hook h hhk (EvalTerms.to_old hA hts) hh hund
    | _, _, _, .param h hhk hp hts hr => .param h hhk hp (EvalTerms.to_old hA hts) hr
    | _, _, _, .call h hh hts hvs hf hp => .call h hh (EvalTerms.to_old hA hts) hvs (Eval.to_old hA hf) hp
    | _, _, _, .callUndef h hh hts hvs hp => .callUndef h hh (EvalTerms.to_old hA hts) hvs hp
    | _, _, _, .ovl h ho hts => .ovl h ho (EvalTerms.to_old hA hts)
  theorem EvalTerms.to_old {c : Semantics}
      (hA : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, cl.aside = false) : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)},
      EvalTerms c σ ts rs → EvalTerms₀ c σ ts rs
    | _, _, _, .nil => .nil
    | _, _, _, .cons h hs => .cons (EvalTerm.to_old hA h) (EvalTerms.to_old hA hs)
end


mutual
  theorem Eval₀.to_new {c : Semantics}
      (hB : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) : ∀ {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm},
      Eval₀ c f vs r → Eval c f vs r
    | _, _, _, .clause hfn hmem hσ hmatch hreq hprio hrhs hens =>
        .clause hfn hmem hσ hmatch (fun t ht => EvalTerm₀.to_new hB (hreq t ht))
          (fun cl' h1 _ h2 => Fails₀.to_new hB (hB hfn cl' h1) (hprio cl' h1 h2))
          (EvalTerm₀.to_new hB hrhs) (fun t ht => EvalTerm₀.to_new hB (hens t ht))
    | _, _, _, .rest hfn hnone => .rest hfn (fun cl h => Fails₀.to_new hB (hB hfn cl h) (hnone cl h))
    | _, _, _, .ensFails hfn hmem hσ hmatch hreq hprio ht he hw =>
        .ensFails hfn hmem hσ hmatch (fun t ht => EvalTerm₀.to_new hB (hreq t ht))
          (fun cl' h1 _ h2 => Fails₀.to_new hB (hB hfn cl' h1) (hprio cl' h1 h2))
          ht (EvalTerm₀.to_new hB he) hw
  theorem Fails₀.to_new {c : Semantics}
      (hB : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) : ∀ {vs : List GroundTerm} {cl : Clause}, binds cl.vars.length (varOccsList cl.pats) = true →
      Fails₀ c vs cl → Fails c vs cl
    | _, _, hb, .intro h => .intro fun σ hσ hp => ReqFails₀.to_new hB (h σ (Clause.wellSorted_of_at hb hσ) hp)
  theorem ReqFails₀.to_new {c : Semantics}
      (hB : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) : ∀ {σ : Subst} {cl : Clause}, ReqFails₀ c σ cl → ReqFails c σ cl
    | _, _, .intro ht he hr => .intro ht (EvalTerm₀.to_new hB he) hr
  theorem EvalTerm₀.to_new {c : Semantics}
      (hB : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm},
      EvalTerm₀ c σ t r → EvalTerm c σ t r
    | _, _, _, .var => .var
    | _, _, _, .dv => .dv
    | _, _, _, .inj h => .inj (EvalTerm₀.to_new hB h)
    | _, _, _, .ctor h hts => .ctor h (EvalTerms₀.to_new hB hts)
    | _, _, _, .hook h hhk hts hh hund => .hook h hhk (EvalTerms₀.to_new hB hts) hh hund
    | _, _, _, .param h hhk hp hts hr => .param h hhk hp (EvalTerms₀.to_new hB hts) hr
    | _, _, _, .call h hh hts hvs hf hp => .call h hh (EvalTerms₀.to_new hB hts) hvs (Eval₀.to_new hB hf) hp
    | _, _, _, .callUndef h hh hts hvs hp => .callUndef h hh (EvalTerms₀.to_new hB hts) hvs hp
    | _, _, _, .ovl h ho hts => .ovl h ho (EvalTerms₀.to_new hB hts)
  theorem EvalTerms₀.to_new {c : Semantics}
      (hB : ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)},
      EvalTerms₀ c σ ts rs → EvalTerms c σ ts rs
    | _, _, _, .nil => .nil
    | _, _, _, .cons h hs => .cons (EvalTerm₀.to_new hB h) (EvalTerms₀.to_new hB hs)
end


/-- **Evaluation is the old evaluation** where the definition is plain. -/
theorem eval_plain {c : Semantics} (hp : c.plain = true) (f : Sym) (vs : List GroundTerm)
    (r : Option GroundTerm) : Eval c f vs r ↔ Eval₀ c f vs r :=
  ⟨Eval.to_old (Semantics.aside_of_plain hp), Eval₀.to_new (Semantics.binds_of_plain hp)⟩

theorem evalTerm_plain {c : Semantics} (hp : c.plain = true) (σ : Subst) (t : Term)
    (r : Option GroundTerm) : EvalTerm c σ t r ↔ EvalTerm₀ c σ t r :=
  ⟨EvalTerm.to_old (Semantics.aside_of_plain hp), EvalTerm₀.to_new (Semantics.binds_of_plain hp)⟩

/-- A clause whose patterns bind every variable fails where it failed before, where the definition is
plain. -/
theorem fails_plain {c : Semantics} (hp : c.plain = true) (vs : List GroundTerm) (cl : Clause)
    (h : (cl.pre.isTop && binds cl.vars.length (varOccsList cl.pats)) = true) :
    Fails c vs cl ↔ Fails₀ c vs cl := by
  simp only [Bool.and_eq_true] at h
  exact ⟨Fails.to_old (Semantics.aside_of_plain hp), Fails₀.to_new (Semantics.binds_of_plain hp) h.2⟩

end KCore
