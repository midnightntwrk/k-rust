/-
  The motive of the induction on an evaluation of kore.k, one call at a time
  (`Eval.calls_induct` at `K₀ sig`), for kore.k's evaluation functions.

  `Spec d E f vs r` says, of a call of kore.k's function `f` at `vs` with the result `r`, what the
  object semantics `d₀ d` holds of it, where `E` is the kore.k definition of `d`. It has a clause
  for each of the thirteen functions through which `eval` calls itself, and is `True` at every
  other function (a helper's result is read from its own evaluation):

  - `eval`, `evalTs` (`SpecEval`, `SpecEvalTs`): at the instance of a term under `σ`, the result
    is the encoding of a result `EvalTerm (d₀ d) σ` has. `eval` is also asked for an element of a
    collection construction and for a right side with its ensures, which are no terms of the
    object semantics: `EvalForm` names the four forms, `EvalForm.Is` what kore.k is given and
    `EvalForm.Gives` what it returns.
  - `ensure`, `strictHook`, `result` (`SpecEnsure`, `SpecStrictHook`, `SpecResult`): the value,
    without a call of `eval`.
  - `apply`, `applyL` (`SpecApply`, `SpecApplyL`): `bot` at an undefined argument, the constructor
    application where `f` is no function, and the encoding of a result `Eval (d₀ d) f` has where
    it is one (`CallIs_ksm`).
  - `evalAt`, `evalIf`, `tryAt`, `orElse`, `tryCl`, `tryM` (the walk of the clauses): `some u`
    where `u` is the encoding of a result `Eval (d₀ d) f` has, `none` where the clauses the call
    walks `Fails`. Each takes what the walk has shown before the call: every clause of a smaller
    priority fails (`Below_ksm`).

  `StepCase d E f` is the step of the induction at `f`; `stepCase_iff_ksm` and the examples after
  it give its statement at each function with `Spec` unfolded there. `spec_of_steps` is the
  induction: from the thirteen step cases, `Spec` holds of every evaluation. `stepCase_ensure` is
  the step at `ensure`.
-/
import User.HelpWalk
import User.Inst
import KcoreSpec.EvalCallsInduct
import KcoreSpec.KKMatchFSpec
import KcoreSpec.KKLitsVEval

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The symbols -/

/-- Each symbol number `Spec` has a clause for has the KORE name of the function. -/
theorem spec_names_ksm :
    RefKk.defn.sem.symName 464 = "Lbleval'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Def'Unds'Term" ∧
    RefKk.defn.sem.symName 467 = "LblevalTs'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Def'Unds'Ts" ∧
    RefKk.defn.sem.symName 463 = "Lblensure'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 508 = "LblstrictHook'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 448 = "Lblapply'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Def'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 449 = "LblapplyL'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Def'Unds'Int'Unds'Ts'Unds'Look" ∧
    RefKk.defn.sem.symName 502 = "Lblresult'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Int'Unds'Ts'Unds'Res" ∧
    RefKk.defn.sem.symName 465 = "LblevalAt'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Res'Unds'Def'Unds'Ts'Unds'Clauses'Unds'Prio" ∧
    RefKk.defn.sem.symName 466 = "LblevalIf'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Res'Unds'Def'Unds'Ts'Unds'Clauses'Unds'Int'Unds'Res" ∧
    RefKk.defn.sem.symName 512 = "LbltryAt'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Res'Unds'Def'Unds'Ts'Unds'Clauses'Unds'Int" ∧
    RefKk.defn.sem.symName 497 = "LblorElse'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Res'Unds'Res'Unds'Def'Unds'Ts'Unds'Clauses'Unds'Int" ∧
    RefKk.defn.sem.symName 513 = "LbltryCl'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Res'Unds'Def'Unds'Ts'Unds'Term'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 514 = "LbltryM'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Res'Unds'Def'Unds'Term'Unds'Term'Unds'Ms" := by
  decide +kernel

/-- The functions `Spec` has a clause for: `eval`, `evalTs`, `ensure`, `strictHook`, `apply`,
`applyL`, `result`, `evalAt`, `evalIf`, `tryAt`, `orElse`, `tryCl`, `tryM`. -/
def specFns : List Sym := [464, 467, 463, 508, 448, 449, 502, 465, 466, 512, 497, 513, 514]

/-! ## What `eval` is asked for -/

/-- A term of the object semantics that `σ` gives a meaning: the term is well sorted over some
function signatures of `d₀ d`, `σ` gives each of its variables a value of the variable's sort, and
the literals of these values have a kore.k form. -/
def TermOK_ksm (d : Semantics) (σ : Subst) (tm : Term) : Prop :=
  ∃ (L : List CtorSig) (vars : List Srt) (s : Srt), HeadsOK (d₀ d) L ∧
    sortOfTerm ((d₀ d).rhsCtx L) vars tm = some s ∧ (d₀ d).WellSortedAt vars (varOccs tm) σ ∧
    ∀ i ∈ varOccs tm, ∀ v, σ.lookup i = some v → litsV v = true

/-- The forms kore.k's `eval` is asked for: a term's instance; an element `el(X)` or `kv(A, V)`
of a collection construction, over the instances of the terms it holds; a right side with its
ensures, `en(T, E)`. -/
inductive EvalForm where
  | term (tm : Term)
  | el (x : Term)
  | kv (a v : Term)
  | en (rhs e : Term)

/-- kore.k's `mkEl`: an element, undefined where its term is. -/
def mkElV_ksm : T → T
  | .bot => .bot
  | x => .el x

/-- kore.k's `mkKv`: an entry, undefined where its key or its value is. -/
def mkKvV_ksm (a v : T) : T := if hasBotF [a, v] then .bot else .kv a v

/-- `t` is the form `q` under `σ`: what `eval` is given. -/
def EvalForm.Is (d : Semantics) (σ : Subst) : EvalForm → T → Prop
  | .term tm, t => TermOK_ksm d σ tm ∧ Inst d σ tm t
  | .el x, t => TermOK_ksm d σ x ∧ ∃ p, Inst d σ x p ∧ t = .el p
  | .kv a v, t => TermOK_ksm d σ a ∧ TermOK_ksm d σ v ∧ ∃ p q, Inst d σ a p ∧ Inst d σ v q ∧ t = .kv p q
  | .en rhs e, t =>
      TermOK_ksm d σ rhs ∧ TermOK_ksm d σ e ∧ ∃ p q, Inst d σ rhs p ∧ Inst d σ e q ∧ t = .en p q

/-- `u` is what the object semantics gives the form `q` under `σ`: the encoding of a result of
the term; the element or entry of the results of its terms; the right side's result where the
ensures has the result `true`, and `bot` otherwise. -/
def EvalForm.Gives (d : Semantics) (σ : Subst) : EvalForm → T → Prop
  | .term tm, u => ∃ o, u = encR o ∧ EvalTerm (d₀ d) σ tm o
  | .el x, u => ∃ o, u = mkElV_ksm (encR o) ∧ EvalTerm (d₀ d) σ x o
  | .kv a v, u => ∃ oa ov, u = mkKvV_ksm (encR oa) (encR ov) ∧ EvalTerm (d₀ d) σ a oa ∧
      EvalTerm (d₀ d) σ v ov
  | .en rhs e, u => ∃ o w, u = ensureF (encR w) (encR o) ∧ EvalTerm (d₀ d) σ rhs o ∧
      EvalTerm (d₀ d) σ e w

/-! ## The terms -/

/-- `R` relates two lists element by element. -/
inductive Each₂_ksm {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Each₂_ksm R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} (h : R a b) (hs : Each₂_ksm R as bs) :
      Each₂_ksm R (a :: as) (b :: bs)

/-- `eval(D, T)`: at a form under `σ`, what the object semantics gives the form. -/
def SpecEval (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (σ : Subst) (q : EvalForm) (t : T), vs = [embD E, emb t] → q.Is d σ t →
    ∃ u, r = some (emb u) ∧ q.Gives d σ u

/-- `evalTs(D, Ts)`: at forms under one `σ`, what the object semantics gives each, in order. -/
def SpecEvalTs (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (σ : Subst) (qs : List EvalForm) (ts : List T), vs = [embD E, embTs ts] →
    Each₂_ksm (fun q t => q.Is d σ t) qs ts →
    ∃ us, r = some (embTs us) ∧ Each₂_ksm (fun q u => q.Gives d σ u) qs us

/-- `ensure(E, T)`: `T` where `E` is `bv(true)`, else `bot`. -/
def SpecEnsure (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ e t : T, vs = [emb e, emb t] → r = some (emb (ensureF e t))

/-- `strictHook(O, As)` at the code of the interpreted symbol `f` and the encodings of the results
`os` of its arguments: where each has a value, of `f`'s argument sorts together, the encoding of
what `d₀ d` gives `f` there; `bot` where one has none. -/
def SpecStrictHook (d : Semantics) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (o : Int) (os : List (Option GroundTerm)), opOf f = some o →
    vs = [.dv 3 (.int o), embTs (os.map encR)] →
    (∀ v, some v ∈ os → litsV v = true) →
    (∀ ws, allSome os = some ws →
      ∃ k, lookupSig hookSigs f = some k ∧ (d₀ d).sortsOf ws = some k.args) →
    r = some (emb (encR ((allSome os).bind fun ws => ((d₀ d).hookRes f ws).join)))

/-! ## A call -/

/-- The result `r` of kore.k's application of `f` to the encodings of `ws`: the constructor
application where `f` is no function of `d₀ d`; where it is one and `ws` has its argument sorts,
the encoding of a result `Eval (d₀ d) f ws` has. -/
def CallIs_ksm (d : Semantics) (f : Sym) (ws : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ((d₀ d).lookupFn f = none → r = some (emb (.ap (f : Int) (encTs ws)))) ∧
  ∀ fn, (d₀ d).lookupFn f = some fn → (d₀ d).sortsOf ws = some fn.args →
    ∃ o, r = some (emb (encR o)) ∧ Eval (d₀ d) f ws o

/-- `apply(D, F, As)` at the encodings of the results `os` of the arguments: `bot` where one has
no value, else the application at their values. -/
def SpecApply (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (os : List (Option GroundTerm)),
    vs = [embD E, .dv 3 (.int (f : Int)), embTs (os.map encR)] →
    (∀ v, some v ∈ os → litsV v = true) →
    (allSome os = none → r = some (emb .bot)) ∧ ∀ ws, allSome os = some ws → CallIs_ksm d f ws r

/-- `applyL(D, F, As, L)` at the encodings of values and what `lookup` gives `F`: the clauses of
`f` where it is a function of `d₀ d`, `nofn` otherwise. -/
def SpecApplyL (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (ws : List GroundTerm) (l : Option (List Cl)),
    vs = [embD E, .dv 3 (.int (f : Int)), embTs (encTs ws), embLook l] → litsVL ws = true →
    l = ((d₀ d).lookupFn f).map (fun fn => fn.clauses.map (encCl d)) → CallIs_ksm d f ws r

/-- `result(F, As, R)`: the term `R` holds, `bot` at `none`. -/
def SpecResult (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f as : GroundTerm) (x : Option T), vs = [f, as, embRes x] → r = some (emb (x.getD .bot))

/-! ## The walk of the clauses -/

/-- The call the walk is in: `f` is the function `fn` of `d₀ d`, at values `ws` of its argument
sorts whose literals have a kore.k form. -/
def WalkAt_ksm (d : Semantics) (f : Sym) (fn : Fn) (ws : List GroundTerm) : Prop :=
  (d₀ d).lookupFn f = some fn ∧ (d₀ d).sortsOf ws = some fn.args ∧ litsVL ws = true

/-- What the walk has shown when it is at the priority `p`: every clause of a smaller priority
fails at `ws`; at `noP`, every clause. -/
def Below_ksm (d : Semantics) (fn : Fn) (ws : List GroundTerm) (p : Option Int) : Prop :=
  ∀ cl ∈ fn.clauses, (∀ P, p = some P → (cl.prio : Int) < P) → Fails (d₀ d) ws cl

/-- `u` is the encoding of a result `f` has at `ws` in `d₀ d`. -/
def Found_ksm (d : Semantics) (f : Sym) (ws : List GroundTerm) (u : T) : Prop :=
  ∃ o, u = encR o ∧ Eval (d₀ d) f ws o

/-- `evalAt(D, As, Cs, P)` at `fn`'s clauses and a priority below which every clause fails:
`some u` with `u` a result of `f`, or `none` where every clause of `fn` fails. -/
def SpecEvalAt (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (fn : Fn) (ws : List GroundTerm) (p : Option Int),
    vs = [embD E, embTs (encTs ws), embCls (fn.clauses.map (encCl d)), embPrio p] →
    WalkAt_ksm d f fn ws → Below_ksm d fn ws p →
    ∃ x, r = some (embRes x) ∧ (∀ u, x = some u → Found_ksm d f ws u) ∧
      (x = none → ∀ cl ∈ fn.clauses, Fails (d₀ d) ws cl)

/-- `evalIf(D, As, Cs, P, R)` at what `tryAt` gave at `P` (`x`: a result of `f`, or `none` where
every clause of priority `P` fails): as `evalAt`. -/
def SpecEvalIf (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (fn : Fn) (ws : List GroundTerm) (P : Int) (x : Option T),
    vs = [embD E, embTs (encTs ws), embCls (fn.clauses.map (encCl d)), .dv 3 (.int P), embRes x] →
    WalkAt_ksm d f fn ws → Below_ksm d fn ws (some P) →
    (∀ u, x = some u → Found_ksm d f ws u) →
    (x = none → ∀ cl ∈ fn.clauses, (cl.prio : Int) = P → Fails (d₀ d) ws cl) →
    ∃ y, r = some (embRes y) ∧ (∀ u, y = some u → Found_ksm d f ws u) ∧
      (y = none → ∀ cl ∈ fn.clauses, Fails (d₀ d) ws cl)

/-- `tryAt(D, As, Cs, P)` at clauses `suf` of `fn` (the rest of its clauses, in the order of the
text): `some u` with `u` a result of `f`, or `none` where every clause of `suf` of priority `P`
fails. -/
def SpecTryAt (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (fn : Fn) (ws : List GroundTerm) (suf : List Clause) (P : Int),
    vs = [embD E, embTs (encTs ws), embCls (suf.map (encCl d)), .dv 3 (.int P)] →
    WalkAt_ksm d f fn ws → (∀ cl ∈ suf, cl ∈ fn.clauses) → Below_ksm d fn ws (some P) →
    ∃ x, r = some (embRes x) ∧ (∀ u, x = some u → Found_ksm d f ws u) ∧
      (x = none → ∀ cl ∈ suf, (cl.prio : Int) = P → Fails (d₀ d) ws cl)

/-- `orElse(R, D, As, Cs, P)` at what `tryCl` gave a clause (`x`: a result of `f`, or `none`) and
the clauses `suf` after it: `x` where it is a result, else as `tryAt` at `suf`. -/
def SpecOrElse (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (fn : Fn) (ws : List GroundTerm) (suf : List Clause) (P : Int) (x : Option T),
    vs = [embRes x, embD E, embTs (encTs ws), embCls (suf.map (encCl d)), .dv 3 (.int P)] →
    WalkAt_ksm d f fn ws → (∀ cl ∈ suf, cl ∈ fn.clauses) → Below_ksm d fn ws (some P) →
    (∀ u, x = some u → Found_ksm d f ws u) →
    ∃ y, r = some (embRes y) ∧ (∀ u, y = some u → Found_ksm d f ws u) ∧
      (y = none → x = none ∧ ∀ cl ∈ suf, (cl.prio : Int) = P → Fails (d₀ d) ws cl)

/-- `tryCl(D, Ps, Req, Rhs, As)` at a clause `cl` of `fn` below whose priority every clause
fails: `some u` with `u` a result of `f`, or `none` where `cl` fails. -/
def SpecTryCl (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (fn : Fn) (ws : List GroundTerm) (cl : Clause),
    vs = [embD E, embTs (encCl d cl).pats, emb (encCl d cl).req, emb (encCl d cl).rhs,
      embTs (encTs ws)] →
    WalkAt_ksm d f fn ws → cl ∈ fn.clauses → Below_ksm d fn ws (some (cl.prio : Int)) →
    ∃ x, r = some (embRes x) ∧ (∀ u, x = some u → Found_ksm d f ws u) ∧
      (x = none → Fails (d₀ d) ws cl)

/-- `tryM(D, Req, Rhs, Ms)` at matches `ms` of `cl`'s patterns at `ws`, each the binding of a
substitution under which the patterns denote `ws`: `some u` with `u` a result of `f`, or `none`
where the `requires` fails under every substitution a binding of `ms` represents. -/
def SpecTryM (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (f : Sym) (fn : Fn) (ws : List GroundTerm) (cl : Clause) (ms : Ms),
    vs = [embD E, emb (encCl d cl).req, emb (encCl d cl).rhs, embMs ms] →
    WalkAt_ksm d f fn ws → cl ∈ fn.clauses → Below_ksm d fn ws (some (cl.prio : Int)) →
    (∀ B ∈ ms, ∃ σ, BindRep (d₀ d) cl.vars B σ ∧ (d₀ d).WellSorted cl.vars σ ∧
      PatVals (d₀ d) σ cl.pats ws) →
    ∃ x, r = some (embRes x) ∧ (∀ u, x = some u → Found_ksm d f ws u) ∧
      (x = none → ∀ B ∈ ms, ∀ σ, BindRep (d₀ d) cl.vars B σ → (d₀ d).WellSorted cl.vars σ →
        PatVals (d₀ d) σ cl.pats ws → ReqFails (d₀ d) σ cl)

/-! ## The motive -/

/-- **The motive.** What the object semantics `d₀ d` holds of a call of kore.k's `f` at `vs` with
the result `r`, where `E` is the kore.k definition of `d`: the clause of `f` among the thirteen
evaluation functions, `True` at any other function. -/
def Spec (d : Semantics) (E : D) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  if f = 464 then SpecEval d E vs r
  else if f = 467 then SpecEvalTs d E vs r
  else if f = 463 then SpecEnsure vs r
  else if f = 508 then SpecStrictHook d vs r
  else if f = 448 then SpecApply d E vs r
  else if f = 449 then SpecApplyL d E vs r
  else if f = 502 then SpecResult vs r
  else if f = 465 then SpecEvalAt d E vs r
  else if f = 466 then SpecEvalIf d E vs r
  else if f = 512 then SpecTryAt d E vs r
  else if f = 497 then SpecOrElse d E vs r
  else if f = 513 then SpecTryCl d E vs r
  else if f = 514 then SpecTryM d E vs r
  else True

section
variable (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm)

theorem Spec_eval : Spec d E 464 vs r ↔ SpecEval d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_evalTs : Spec d E 467 vs r ↔ SpecEvalTs d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_ensure : Spec d E 463 vs r ↔ SpecEnsure vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_strictHook : Spec d E 508 vs r ↔ SpecStrictHook d vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_apply : Spec d E 448 vs r ↔ SpecApply d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_applyL : Spec d E 449 vs r ↔ SpecApplyL d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_result : Spec d E 502 vs r ↔ SpecResult vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_evalAt : Spec d E 465 vs r ↔ SpecEvalAt d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_evalIf : Spec d E 466 vs r ↔ SpecEvalIf d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_tryAt : Spec d E 512 vs r ↔ SpecTryAt d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_orElse : Spec d E 497 vs r ↔ SpecOrElse d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_tryCl : Spec d E 513 vs r ↔ SpecTryCl d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)
theorem Spec_tryM : Spec d E 514 vs r ↔ SpecTryM d E vs r := by
  first | simp [Spec] | (unfold Spec; exact Iff.rfl)

end

/-- A conditional proposition whose condition fails is its second branch. -/
theorem ite_of_not_ksm {c : Prop} [Decidable c] {P Q : Prop} (h : ¬ c) (hq : Q) :
    if c then P else Q := by
  split
  next hc => exact absurd hc h
  next => exact hq

/-- A function outside `specFns` is none of its thirteen. -/
theorem ne_of_not_specFns_ksm {f : Sym} (hf : f ∉ specFns) {n : Sym} (hn : n ∈ specFns) : ¬ f = n :=
  fun he => hf (he ▸ hn)

/-- `Spec` asks nothing of a function outside `specFns`. -/
theorem Spec_else_ksm (d : Semantics) (E : D) {f : Sym} (hf : f ∉ specFns) (vs : List GroundTerm)
    (r : Option GroundTerm) : Spec d E f vs r := by
  have hne : ∀ n : Sym, n ∈ specFns → ¬ f = n := fun n hn => ne_of_not_specFns_ksm hf hn
  unfold Spec
  exact
    ite_of_not_ksm (hne 464 (.head _)) <|
    ite_of_not_ksm (hne 467 (.tail _ (.head _))) <|
    ite_of_not_ksm (hne 463 (.tail _ (.tail _ (.head _)))) <|
    ite_of_not_ksm (hne 508 (.tail _ (.tail _ (.tail _ (.head _))))) <|
    ite_of_not_ksm (hne 448 (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) <|
    ite_of_not_ksm (hne 449 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) <|
    ite_of_not_ksm (hne 502 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) <|
    ite_of_not_ksm (hne 465 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) <|
    ite_of_not_ksm (hne 466 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) <|
    ite_of_not_ksm (hne 512 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))) <|
    ite_of_not_ksm (hne 497 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))) <|
    ite_of_not_ksm (hne 513 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))) <|
    ite_of_not_ksm (hne 514 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))) <|
    trivial

/-! ## The step cases -/

/-- What a step of the induction knows of each call the evaluation makes: it is an evaluation of
kore.k, and `Spec` holds of it. -/
abbrev Called (d : Semantics) (E : D) : CallRel :=
  fun g ws q => Eval (K₀ sig) g ws q ∧ Spec d E g ws q

/-- **The step case at `f`**, for `d` that `execReady` accepts with the kore.k definition `E`:
where `f` has the result `r` at `vs` by a constructor of `Eval` whose calls each are evaluations of
kore.k of which `Spec` holds, `Spec` holds of `f`, `vs` and `r`. -/
def StepCase (d : Semantics) (E : D) (f : Sym) : Prop :=
  CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) f vs r → Spec d E f vs r

/-- The step case at `f`, with `Spec` at `f` written as its clause `S`. -/
theorem stepCase_iff_ksm {d : Semantics} {E : D} {f : Sym}
    {S : List GroundTerm → Option GroundTerm → Prop} (h : ∀ vs r, Spec d E f vs r ↔ S vs r) :
    StepCase d E f ↔ (CExec.execReady d = true → encDef d = some E →
      ∀ vs r, ByClause (K₀ sig) (Called d E) f vs r → S vs r) :=
  ⟨fun H hr hE vs r hb => (h vs r).mp (H hr hE vs r hb),
   fun H hr hE vs r hb => (h vs r).mpr (H hr hE vs r hb)⟩

section
variable (d : Semantics) (E : D)

/-- The step cases to prove, one for each function of `specFns`: the terms (`eval`, `evalTs`,
`ensure`, `strictHook`) and the clauses (`apply`, `applyL`, `result`, `evalAt`, `evalIf`, `tryAt`,
`orElse`, `tryCl`, `tryM`). -/
example : StepCase d E 464 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 464 vs r → SpecEval d E vs r) :=
  stepCase_iff_ksm (Spec_eval d E)
example : StepCase d E 467 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 467 vs r → SpecEvalTs d E vs r) :=
  stepCase_iff_ksm (Spec_evalTs d E)
example : StepCase d E 463 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 463 vs r → SpecEnsure vs r) :=
  stepCase_iff_ksm (Spec_ensure d E)
example : StepCase d E 508 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 508 vs r → SpecStrictHook d vs r) :=
  stepCase_iff_ksm (Spec_strictHook d E)
example : StepCase d E 448 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 448 vs r → SpecApply d E vs r) :=
  stepCase_iff_ksm (Spec_apply d E)
example : StepCase d E 449 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 449 vs r → SpecApplyL d E vs r) :=
  stepCase_iff_ksm (Spec_applyL d E)
example : StepCase d E 502 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 502 vs r → SpecResult vs r) :=
  stepCase_iff_ksm (Spec_result d E)
example : StepCase d E 465 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 465 vs r → SpecEvalAt d E vs r) :=
  stepCase_iff_ksm (Spec_evalAt d E)
example : StepCase d E 466 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 466 vs r → SpecEvalIf d E vs r) :=
  stepCase_iff_ksm (Spec_evalIf d E)
example : StepCase d E 512 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 512 vs r → SpecTryAt d E vs r) :=
  stepCase_iff_ksm (Spec_tryAt d E)
example : StepCase d E 497 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 497 vs r → SpecOrElse d E vs r) :=
  stepCase_iff_ksm (Spec_orElse d E)
example : StepCase d E 513 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 513 vs r → SpecTryCl d E vs r) :=
  stepCase_iff_ksm (Spec_tryCl d E)
example : StepCase d E 514 ↔ (CExec.execReady d = true → encDef d = some E →
    ∀ vs r, ByClause (K₀ sig) (Called d E) 514 vs r → SpecTryM d E vs r) :=
  stepCase_iff_ksm (Spec_tryM d E)

/-- A step case holds an evaluation of `f` at `vs` itself, and one of each call. -/
example {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
    (hb : ByClause (K₀ sig) (Called d E) f vs r) : Eval (K₀ sig) f vs r :=
  hb.eval_of_and

/-- The step case at `ensure`: it makes no call, and its evaluation is `ensureF`'s. -/
theorem stepCase_ensure : StepCase d E 463 := fun _ _ vs r hb =>
  (Spec_ensure d E vs r).mpr fun e t hvs => by
    have he : Eval (K₀ sig) 463 vs r := hb.eval_of_and
    rw [hvs] at he
    exact (ensureF.eval_iff e t).mp he

end

/-! ## The induction -/

/-- **`Spec` holds of every evaluation of kore.k**, given the thirteen step cases: the instance of
`Eval.calls_induct` at `K₀ sig` and `Spec d E`. -/
theorem spec_of_steps {d : Semantics} {E : D} (hr : CExec.execReady d = true)
    (hE : encDef d = some E) (hs : ∀ f ∈ specFns, StepCase d E f) {f : Sym}
    {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval (K₀ sig) f vs r) : Spec d E f vs r :=
  Eval.calls_induct (c := K₀ sig) (P := Spec d E) (fun f vs r hb =>
    if hf : f ∈ specFns then hs f hf hr hE vs r hb else Spec_else_ksm d E hf vs r) h

/-! ## What `Spec` gives at `eval` and at `tryCl` -/

/-- `Spec` at `eval` of a term's instance: the result is the encoding of a result of the term. -/
theorem Spec.eval_term {d : Semantics} {E : D} {σ : Subst} {tm : Term} {t : T}
    {r : Option GroundTerm} (h : Spec d E 464 [embD E, emb t] r) (hok : TermOK_ksm d σ tm)
    (ht : Inst d σ tm t) : ∃ o, r = some (emb (encR o)) ∧ EvalTerm (d₀ d) σ tm o := by
  obtain ⟨u, hu, hg⟩ := (Spec_eval d E _ r).mp h σ (.term tm) t rfl
    (show TermOK_ksm d σ tm ∧ Inst d σ tm t from ⟨hok, ht⟩)
  obtain ⟨o, ho, he⟩ : ∃ o, u = encR o ∧ EvalTerm (d₀ d) σ tm o := hg
  exact ⟨o, ho ▸ hu, he⟩

/-- `Spec` at `eval` of a right side with its ensures: the right side's result where the ensures
has the result `true`, `bot` otherwise. -/
theorem Spec.eval_en {d : Semantics} {E : D} {σ : Subst} {rhs e : Term} {p q : T}
    {r : Option GroundTerm} (h : Spec d E 464 [embD E, emb (.en p q)] r)
    (hrhs : TermOK_ksm d σ rhs) (he : TermOK_ksm d σ e) (hp : Inst d σ rhs p) (hq : Inst d σ e q) :
    ∃ o w, r = some (emb (ensureF (encR w) (encR o))) ∧ EvalTerm (d₀ d) σ rhs o ∧
      EvalTerm (d₀ d) σ e w := by
  obtain ⟨u, hu, hg⟩ := (Spec_eval d E _ r).mp h σ (.en rhs e) (.en p q) rfl
    (show TermOK_ksm d σ rhs ∧ TermOK_ksm d σ e ∧
      ∃ p' q', Inst d σ rhs p' ∧ Inst d σ e q' ∧ T.en p q = .en p' q' from
      ⟨hrhs, he, p, q, hp, hq, rfl⟩)
  obtain ⟨o, w, ho, h1, h2⟩ : ∃ o w, u = ensureF (encR w) (encR o) ∧ EvalTerm (d₀ d) σ rhs o ∧
    EvalTerm (d₀ d) σ e w := hg
  exact ⟨o, w, ho ▸ hu, h1, h2⟩

/-- `Spec` at `tryCl` with the result `none`: the clause fails. -/
theorem Spec.tryCl_none {d : Semantics} {E : D} {f : Sym} {fn : Fn} {ws : List GroundTerm}
    {cl : Clause}
    (h : Spec d E 513 [embD E, embTs (encCl d cl).pats, emb (encCl d cl).req,
      emb (encCl d cl).rhs, embTs (encTs ws)] (some (embRes none)))
    (hw : WalkAt_ksm d f fn ws) (hcl : cl ∈ fn.clauses)
    (hb : Below_ksm d fn ws (some (cl.prio : Int))) : Fails (d₀ d) ws cl := by
  obtain ⟨x, hx, -, hn⟩ := (Spec_tryCl d E _ _).mp h f fn ws cl rfl hw hcl hb
  cases x with
  | none => exact hn rfl
  | some u => simp [embRes] at hx

/-! ## Checks -/

#check @Spec
#check @specFns
#check @StepCase
#check @stepCase_iff_ksm
#check @stepCase_ensure
#check @spec_of_steps
#check @Spec_else_ksm
#check @Spec.eval_term
#check @Spec.eval_en
#check @Spec.tryCl_none

open Lean in
#eval show CoreM Unit from do
  for n in [``spec_names_ksm, ``Spec_eval, ``Spec_evalTs, ``Spec_ensure, ``Spec_strictHook,
      ``Spec_apply, ``Spec_applyL, ``Spec_result, ``Spec_evalAt, ``Spec_evalIf, ``Spec_tryAt,
      ``Spec_orElse, ``Spec_tryCl, ``Spec_tryM, ``Spec_else_ksm, ``stepCase_iff_ksm,
      ``stepCase_ensure, ``spec_of_steps, ``Spec.eval_term, ``Spec.eval_en, ``Spec.tryCl_none] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
