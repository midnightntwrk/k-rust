/-
  e3.positivity-probe (CN-4 §4.9, first Lean block and stop rule "positivity fails"). A copy of the
  `Eval` block of KcoreSpec/Evaluation.lean in the namespace `KCore.E3Probe`, with:
  - `Holds` joined to the block, its twelve constructors as landed (Evaluation.lean, `inductive
    Holds`), each line indented and nothing else changed;
  - `PatVal`, `PatVals` outside the block (the library's: `Holds.exSome`'s `hr` holds `PatVal`
    under `↔`), as `Extends`, `sameResult`, `allSome`;
  - `hpre : Holds c cl.vars.length σ cl.pre true` after `hreq` in `Eval.clause` and `Eval.ensFails`;
  - `ReqFails.pre (h : Holds c cl.vars.length σ cl.pre false)`.
  The block is generated from Evaluation.lean's lines (the three insertions and the indentation of
  `Holds` are the only differences), so it is the landed block with CN-4 §4.9's three edits.

  What the file checks: the kernel accepts the six mutually inductive types (strict positivity:
  `Holds` occurs in `Eval.clause`, `Eval.ensFails`, `ReqFails.pre` as a premise, and in its own
  `exSome`, `ex`, `all` under `∀ σ', … →`; `EvalTerm` occurs in `Holds.ceil`, `equals`, `mem`,
  `exNone`, `exSome`), the recursors have six motives, and the new premises are usable (a clause
  with `pre = .top` applies by `Holds.top`; `ReqFails.pre` from `Holds.bot`; no `Holds … .top false`).
  Nothing here is imported by KcoreSpec; no library declaration is edited.
  Run from the package root: `lake env lean -j1 test/EvalBlockPositivity.lean`.
-/
import KcoreSpec.Evaluation

set_option autoImplicit false

namespace KCore.E3Probe

open KCore

mutual
  /-- `Eval c f vs r`: the function `f` of `c` at `vs` has the result `r` (`none`: undefined). -/
  inductive Eval (c : Semantics) : Sym → List GroundTerm → Option GroundTerm → Prop where
    /-- A clause that applies decides, when no clause of a smaller priority that is not `aside`
    applies: its patterns denote `vs` under a well-sorted σ, its `requires` evaluates to `true`
    under σ, and every clause of a smaller priority that is not `aside` fails. Where its `ensures`
    evaluates to `true` (or it has none), the result is its right-hand side's. -/
    | clause {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
        {σ : Subst} {r : Option GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hmem : cl ∈ fn.clauses)
        (hσ : c.WellSorted cl.vars σ)
        (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
        (hpre : Holds c cl.vars.length σ cl.pre true)
        (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
        (hrhs : EvalTerm c σ cl.rhs r)
        (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) : Eval c f vs r
    /-- Where every clause fails, `f` has its rest (`fnRest`). -/
    | rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) : Eval c f vs (c.fnRest fn vs)
    /-- A clause that decides (as in `clause`) whose `ensures` evaluates to something other than
    `true` (`false`, or undefined): `f` has no value there, `rhs ∧ ⊥` being empty whatever the
    right-hand side is. The rest is not read. -/
    | ensFails {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
        {σ : Subst} {t : Term} {w : Option GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hmem : cl ∈ fn.clauses)
        (hσ : c.WellSorted cl.vars σ)
        (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
        (hpre : Holds c cl.vars.length σ cl.pre true)
        (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
        (ht : cl.ens = some t) (he : EvalTerm c σ t w) (hw : w ≠ some (bool true)) :
        Eval c f vs none
  /-- `Fails c vs cl`: the clause does not apply at `vs`: for every σ that gives the variables of
  its patterns and conditions values of their sorts and under which its patterns denote `vs`, it
  has a `requires` that evaluates to something other than `true` (`false`, or undefined). With no
  `requires`, no σ may match. A variable outside the patterns and conditions does not bear on
  whether the clause applies. -/
  inductive Fails (c : Semantics) : List GroundTerm → Clause → Prop where
    | intro {vs : List GroundTerm} {cl : Clause}
        (h : ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs → ReqFails c σ cl) :
        Fails c vs cl
  /-- `ReqFails c σ cl`: the clause has a `requires` whose result under σ is not `true`. -/
  inductive ReqFails (c : Semantics) : Subst → Clause → Prop where
    | intro {σ : Subst} {cl : Clause} {t : Term} {r : Option GroundTerm}
        (ht : cl.req = some t) (he : EvalTerm c σ t r) (hr : r ≠ some (bool true)) :
        ReqFails c σ cl
    | pre {σ : Subst} {cl : Clause} (h : Holds c cl.vars.length σ cl.pre false) : ReqFails c σ cl
  /-- `EvalTerm c σ t r`: the right-hand side (or `requires`) `t` has the result `r` under σ. -/
  inductive EvalTerm (c : Semantics) : Subst → Term → Option GroundTerm → Prop where
    | var {σ : Subst} {i : Nat} : EvalTerm c σ (.var i) (σ.lookup i)
    | dv {σ : Subst} {s : Srt} {lit : Lit} : EvalTerm c σ (.dv s lit) (some (.dv s lit))
    | inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r) :
        EvalTerm c σ (.inj a b t) (r.map (injNormal a b))
    /-- A constructor of `c` builds the constructor term (undefined if an argument is). -/
    | ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = true) (hts : EvalTerms c σ ts rs) :
        EvalTerm c σ (.app f ts) ((allSome rs).map (.ctor f))
    /-- An interpreted hooked symbol has its meaning (Hooks.lean), and at a silent point the
    interpretation's value (`hookRes`). -/
    | hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = true) (hts : EvalTerms c σ ts rs)
        (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r)
        (hund : allSome rs = none → r = none) : EvalTerm c σ (.app f ts) r
    /-- A parameter symbol has the value `paramVal` gives it, on defined arguments;
    undefined if an argument is. -/
    | param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true)
        (hts : EvalTerms c σ ts rs) (hr : r = (allSome rs).bind (c.paramVal f)) :
        EvalTerm c σ (.app f ts) r
    /-- A function of `c` is called on defined arguments. -/
    | call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {vs : List GroundTerm} {r : Option GroundTerm}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms c σ ts rs)
        (hvs : allSome rs = some vs) (hf : Eval c f vs r) (hp : c.isParam f = false) :
        EvalTerm c σ (.app f ts) r
    /-- A call with an undefined argument is undefined. -/
    | callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms c σ ts rs)
        (hvs : allSome rs = none) (hp : c.isParam f = false) : EvalTerm c σ (.app f ts) none
    /-- An overloading symbol builds the normal form (`norm`; undefined if an argument is), where
    no function it overloads covers the arguments (`fnCover`). -/
    | ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTerms c σ ts rs)
        (hnf : ∀ vs, allSome rs = some vs → c.fnCover f vs = none) :
        EvalTerm c σ (.app f ts) ((allSome rs).map (c.norm f))
    /-- An overloading symbol at values a function it overloads covers (`fnCover`) has that
    function's result at the stripped arguments, lifted to the symbol's result sort; undefined
    where the function is. -/
    | ovlFn {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {vs : List GroundTerm} {o : OvlSig} {kg : CtorSig} {r : Option GroundTerm}
        (h : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTerms c σ ts rs)
        (hvs : allSome rs = some vs) (hlo : c.lookupOvl f = some o) (hcov : c.fnCover f vs = some kg)
        (hf : Eval c kg.name (stripAll kg.args o.sig.args vs) r) :
        EvalTerm c σ (.app f ts) (r.map (lift kg.result o.sig.result))
  inductive EvalTerms (c : Semantics) : Subst → List Term → List (Option GroundTerm) → Prop where
    | nil {σ : Subst} : EvalTerms c σ [] []
    | cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
        {rs : List (Option GroundTerm)}
        (h : EvalTerm c σ t r) (hs : EvalTerms c σ ts rs) : EvalTerms c σ (t :: ts) (r :: rs)
  /-- `Holds c n σ p b`: the condition p, with n variables in scope, has the truth value b under σ.
  A negation is the result `false`, never a `¬`. -/
  inductive Holds (c : Semantics) : Nat → Subst → Cond → Bool → Prop where
    | top {n σ} : Holds c n σ .top true
    | bot {n σ} : Holds c n σ .bot false
    | not {n σ p b} (h : Holds c n σ p b) : Holds c n σ (.not p) (!b)
    | and {n σ p q b b'} (h : Holds c n σ p b) (h' : Holds c n σ q b') : Holds c n σ (.and p q) (b && b')
    | or {n σ p q b b'} (h : Holds c n σ p b) (h' : Holds c n σ q b') : Holds c n σ (.or p q) (b || b')
    | implies {n σ p q b b'} (h : Holds c n σ p b) (h' : Holds c n σ q b') :
        Holds c n σ (.implies p q) (!b || b')
    | ceil {n σ s t r} (h : EvalTerm c σ t r) : Holds c n σ (.ceil s t) r.isSome
    | equals {n σ s t u r r'} (h : EvalTerm c σ t r) (h' : EvalTerm c σ u r') :
        Holds c n σ (.equals s t u) (sameResult r r')
    | mem {n σ s t u r r'} (h : EvalTerm c σ t r) (h' : EvalTerm c σ u r') :
        Holds c n σ (.mem s t u) (r.isSome && sameResult r r')
    | exNone {n σ ys s p t body} (h : EvalTerm c σ t none) : Holds c n σ (.exMatch ys s p t body) false
    | exSome {n σ ys s p t body v b} (g : Subst → Bool) (h : EvalTerm c σ t (some v))
        (hb : ∀ σ', Extends c n ys σ σ' → PatVal c σ' p v → Holds c (n + ys.length) σ' body (g σ'))
        (hr : b = true ↔ ∃ σ', Extends c n ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true) :
        Holds c n σ (.exMatch ys s p t body) b
    | ex {n σ s body b} (g : Subst → Bool)
        (hb : ∀ σ', Extends c n [s] σ σ' → Holds c (n + 1) σ' body (g σ'))
        (hr : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) : Holds c n σ (.ex s body) b
    | all {n σ s body b} (g : Subst → Bool)
        (hb : ∀ σ', Extends c n [s] σ σ' → Holds c (n + 1) σ' body (g σ'))
        (hr : b = true ↔ ∀ σ', Extends c n [s] σ σ' → g σ' = true) : Holds c n σ (.all s body) b
end


/-! ## The block is accepted: its recursors, with one motive for each of the six types -/

/-- `Holds.rec` takes six motives, in the block's order: `Eval`, `Fails`, `ReqFails`, `EvalTerm`,
`EvalTerms`, `Holds`. -/
example (c : Semantics) : True := by
  have _h := @Holds.rec c
    (motive_1 := fun _ _ _ (_ : Eval c _ _ _) => True) (motive_2 := fun _ _ (_ : Fails c _ _) => True)
    (motive_3 := fun _ _ (_ : ReqFails c _ _) => True) (motive_4 := fun _ _ _ (_ : EvalTerm c _ _ _) => True)
    (motive_5 := fun _ _ _ (_ : EvalTerms c _ _ _) => True) (motive_6 := fun _ _ _ _ (_ : Holds c _ _ _ _) => True)
  trivial

/-! ## The block's names are the copy's, not the library's

Each name of the block is also the library's (`KCore.Eval`, …, `KCore.Holds`). The premises below
are written with the copy's full names, so each constructor applies only if its premise is the
copy's type: `Holds` in `Eval.clause`, `Eval.ensFails` and `ReqFails.pre`; `EvalTerm` in
`Holds.ceil`; `Eval` in `EvalTerm.call`. -/

example {c : Semantics} {σ : Subst} {cl : Clause}
    (h : _root_.KCore.E3Probe.Holds c cl.vars.length σ cl.pre false) :
    _root_.KCore.E3Probe.ReqFails c σ cl := .pre h

example {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t : Term} {r : Option GroundTerm}
    (h : _root_.KCore.E3Probe.EvalTerm c σ t r) :
    _root_.KCore.E3Probe.Holds c n σ (.ceil s t) r.isSome := .ceil h

example {c : Semantics} {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    {r : Option GroundTerm} (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : _root_.KCore.PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → _root_.KCore.E3Probe.EvalTerm c σ t (some (bool true)))
    (hpre : _root_.KCore.E3Probe.Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → _root_.KCore.E3Probe.Fails c vs cl')
    (hrhs : _root_.KCore.E3Probe.EvalTerm c σ cl.rhs r)
    (hens : ∀ t, cl.ens = some t → _root_.KCore.E3Probe.EvalTerm c σ t (some (bool true))) :
    _root_.KCore.E3Probe.Eval c f vs r := .clause hfn hmem hσ hmatch hreq hpre hprio hrhs hens

example {c : Semantics} {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    {t : Term} {w : Option GroundTerm} (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : _root_.KCore.PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → _root_.KCore.E3Probe.EvalTerm c σ t (some (bool true)))
    (hpre : _root_.KCore.E3Probe.Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → _root_.KCore.E3Probe.Fails c vs cl')
    (ht : cl.ens = some t) (he : _root_.KCore.E3Probe.EvalTerm c σ t w) (hw : w ≠ some (bool true)) :
    _root_.KCore.E3Probe.Eval c f vs none := .ensFails hfn hmem hσ hmatch hreq hpre hprio ht he hw

/-- Both `Holds` stand side by side: the library's, outside its block, and the copy's, which the
unqualified name means in this namespace. -/
example {c : Semantics} {n : Nat} {σ : Subst} : _root_.KCore.Holds c n σ .top true := _root_.KCore.Holds.top
example {c : Semantics} {n : Nat} {σ : Subst} : _root_.KCore.E3Probe.Holds c n σ .top true := Holds.top

/-- `Holds` has its twelve constructors, `ReqFails` two. -/
example : True := by
  have _h1 := @Holds.top; have _h2 := @Holds.bot; have _h3 := @Holds.not; have _h4 := @Holds.and
  have _h5 := @Holds.or; have _h6 := @Holds.implies; have _h7 := @Holds.ceil; have _h8 := @Holds.equals
  have _h9 := @Holds.mem; have _h10 := @Holds.exNone; have _h11 := @Holds.exSome; have _h12 := @Holds.ex
  have _h13 := @Holds.all; have _h14 := @ReqFails.intro; have _h15 := @ReqFails.pre
  trivial

/-! ## The new premises are usable -/

/-- `Holds … .top false` has no derivation (what `fails_plain` needs of `ReqFails.pre` at
`pre = .top`, e3-statements §5). -/
theorem not_holds_top_false {c : Semantics} {n : Nat} {σ : Subst} : ¬ Holds c n σ .top false := by
  intro h; cases h

/-- A clause whose `pre` is `\top` meets `hpre` by `Holds.top`. -/
theorem hpre_of_top {c : Semantics} {cl : Clause} {σ : Subst} (h : cl.pre = .top) :
    Holds c cl.vars.length σ cl.pre true := by
  rw [h]; exact .top

/-- A clause whose `pre` is `\bot` fails at every substitution, by `ReqFails.pre`, and so at every
argument list, with no `requires`. -/
theorem fails_of_bot {c : Semantics} {cl : Clause} {vs : List GroundTerm} (h : cl.pre = .bot) :
    Fails c vs cl :=
  .intro fun σ _ _ => .pre (by rw [h]; exact .bot)

/-- info: 'KCore.E3Probe.fails_of_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fails_of_bot

end KCore.E3Probe
