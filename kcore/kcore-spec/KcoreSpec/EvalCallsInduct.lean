/-
  KCore. Induction on an evaluation, one function call at a time.

  `Eval` is defined together with `Fails`, `ReqFails`, `EvalTerm`, `EvalTerms`, `Holds`,
  `InstFails` and `InstIs`, so its recursor asks one motive for each. A property of the calls
  alone (`P f vs r` for every `Eval c f vs r`) needs none of the other seven: what it needs of a
  derivation is the constructor of `Eval` at its root, with `P` known at each call the
  constructor's premises make.

  `EvalTermR c R`, `FailsR c R`, `HoldsR c R`, … are the seven relations with `R g ws q` read at
  each call in place of `Eval c g ws q` (the two constructors `EvalTerm.call` and `EvalTerm.ovlFn`;
  every other constructor is the original's). `ByClause c R f vs r` is the five constructors of
  `Eval` over them: `f` has the result `r` at `vs` by one of `Eval`'s constructors, each call
  inside it related by `R`.

  - `Eval.calls_induct`: `P` holds of every evaluation, if it holds of `f vs r` wherever
    `ByClause c (fun g ws q => Eval c g ws q ∧ P g ws q) f vs r`.
  - The relations are monotone in `R` (`ByClause.mono`), and at an `R` that implies `Eval c` they
    give the originals (`ByClause.eval`, `EvalTermR.toEval`, …), so no premise of a constructor is
    lost: `Eval c f vs r ↔ ByClause c (Eval c) f vs r` (`Eval.byClause_iff`).

  No definition of the semantics is changed and none is read by a statement of the library.
-/
import KcoreSpec.EvalLemmas

set_option autoImplicit false

namespace KCore

/-- A relation in the place of `Eval c`: function, arguments, result. -/
abbrev CallRel : Type := Sym → List GroundTerm → Option GroundTerm → Prop

mutual
  /-- `Fails` with `R` read at each call. -/
  inductive FailsR (c : Semantics) (R : CallRel) : List GroundTerm → Clause → Prop where
    | intro {vs : List GroundTerm} {cl : Clause}
        (h : ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs → ReqFailsR c R σ cl) :
        FailsR c R vs cl
  /-- `ReqFails` with `R` read at each call. -/
  inductive ReqFailsR (c : Semantics) (R : CallRel) : Subst → Clause → Prop where
    | intro {σ : Subst} {cl : Clause} {t : Term} {r : Option GroundTerm}
        (ht : cl.req = some t) (he : EvalTermR c R σ t r) (hr : r ≠ some (bool true)) :
        ReqFailsR c R σ cl
    | pre {σ : Subst} {cl : Clause} (h : HoldsR c R cl.vars.length σ cl.pre false) : ReqFailsR c R σ cl
  /-- `EvalTerm` with `R f vs r` read at each call (`call`, `ovlFn`) in place of `Eval c f vs r`. -/
  inductive EvalTermR (c : Semantics) (R : CallRel) : Subst → Term → Option GroundTerm → Prop where
    | var {σ : Subst} {i : Nat} : EvalTermR c R σ (.var i) (σ.lookup i)
    | dv {σ : Subst} {s : Srt} {lit : Lit} : EvalTermR c R σ (.dv s lit) (some (.dv s lit))
    | inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (h : EvalTermR c R σ t r) :
        EvalTermR c R σ (.inj a b t) (r.map (injNormal a b))
    | ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = true) (hts : EvalTermsR c R σ ts rs) :
        EvalTermR c R σ (.app f ts) ((allSome rs).map (.ctor f))
    | hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = true) (hts : EvalTermsR c R σ ts rs)
        (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r)
        (hund : allSome rs = none → r = none) : EvalTermR c R σ (.app f ts) r
    | param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true)
        (hts : EvalTermsR c R σ ts rs) (hr : r = (allSome rs).bind (c.paramVal f)) :
        EvalTermR c R σ (.app f ts) r
    | call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {vs : List GroundTerm} {r : Option GroundTerm}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTermsR c R σ ts rs)
        (hvs : allSome rs = some vs) (hf : R f vs r) (hp : c.isParam f = false) :
        EvalTermR c R σ (.app f ts) r
    | callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTermsR c R σ ts rs)
        (hvs : allSome rs = none) (hp : c.isParam f = false) : EvalTermR c R σ (.app f ts) none
    | ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTermsR c R σ ts rs)
        (hnf : ∀ vs, allSome rs = some vs → c.fnCover f vs = none) :
        EvalTermR c R σ (.app f ts) ((allSome rs).map (c.norm f))
    | ovlFn {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {vs : List GroundTerm} {o : OvlSig} {kg : CtorSig} {r : Option GroundTerm}
        (h : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTermsR c R σ ts rs)
        (hvs : allSome rs = some vs) (hlo : c.lookupOvl f = some o) (hcov : c.fnCover f vs = some kg)
        (hf : R kg.name (stripAll kg.args o.sig.args vs) r) :
        EvalTermR c R σ (.app f ts) (r.map (lift kg.result o.sig.result))
  /-- `EvalTerms` with `R` read at each call. -/
  inductive EvalTermsR (c : Semantics) (R : CallRel) : Subst → List Term → List (Option GroundTerm) → Prop where
    | nil {σ : Subst} : EvalTermsR c R σ [] []
    | cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
        {rs : List (Option GroundTerm)}
        (h : EvalTermR c R σ t r) (hs : EvalTermsR c R σ ts rs) : EvalTermsR c R σ (t :: ts) (r :: rs)
  /-- `Holds` with `R` read at each call. -/
  inductive HoldsR (c : Semantics) (R : CallRel) : Nat → Subst → Cond → Bool → Prop where
    | top {n σ} : HoldsR c R n σ .top true
    | bot {n σ} : HoldsR c R n σ .bot false
    | not {n σ p b} (h : HoldsR c R n σ p b) : HoldsR c R n σ (.not p) (!b)
    | and {n σ p q b b'} (h : HoldsR c R n σ p b) (h' : HoldsR c R n σ q b') :
        HoldsR c R n σ (.and p q) (b && b')
    | or {n σ p q b b'} (h : HoldsR c R n σ p b) (h' : HoldsR c R n σ q b') :
        HoldsR c R n σ (.or p q) (b || b')
    | implies {n σ p q b b'} (h : HoldsR c R n σ p b) (h' : HoldsR c R n σ q b') :
        HoldsR c R n σ (.implies p q) (!b || b')
    | ceil {n σ s t r} (h : EvalTermR c R σ t r) : HoldsR c R n σ (.ceil s t) r.isSome
    | equals {n σ s t u r r'} (h : EvalTermR c R σ t r) (h' : EvalTermR c R σ u r') :
        HoldsR c R n σ (.equals s t u) (sameResult r r')
    | mem {n σ s t u r r'} (h : EvalTermR c R σ t r) (h' : EvalTermR c R σ u r') :
        HoldsR c R n σ (.mem s t u) (r.isSome && sameResult r r')
    | exNone {n σ ys s p t body} (h : EvalTermR c R σ t none) :
        HoldsR c R n σ (.exMatch ys s p t body) false
    | exSome {n σ ys s p t body v b} (g : Subst → Bool) (h : EvalTermR c R σ t (some v))
        (hb : ∀ σ', Extends c n ys σ σ' → PatVal c σ' p v → HoldsR c R (n + ys.length) σ' body (g σ'))
        (hr : b = true ↔ ∃ σ', Extends c n ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true) :
        HoldsR c R n σ (.exMatch ys s p t body) b
    | ex {n σ s body b} (g : Subst → Bool)
        (hb : ∀ σ', Extends c n [s] σ σ' → HoldsR c R (n + 1) σ' body (g σ'))
        (hr : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) : HoldsR c R n σ (.ex s body) b
    | all {n σ s body b} (g : Subst → Bool)
        (hb : ∀ σ', Extends c n [s] σ σ' → HoldsR c R (n + 1) σ' body (g σ'))
        (hr : b = true ↔ ∀ σ', Extends c n [s] σ σ' → g σ' = true) : HoldsR c R n σ (.all s body) b
  /-- `InstFails` with `R` read at each call. -/
  inductive InstFailsR (c : Semantics) (R : CallRel) : Subst → Clause → Prop where
    | ens {σ : Subst} {cl : Clause} {t : Term} {w : Option GroundTerm}
        (ht : cl.ens = some t) (he : EvalTermR c R σ t w) (hw : w ≠ some (bool true)) : InstFailsR c R σ cl
    | post {σ : Subst} {cl : Clause} (h : HoldsR c R cl.vars.length σ cl.post false) : InstFailsR c R σ cl
    | rhs {σ : Subst} {cl : Clause} (h : EvalTermR c R σ cl.rhs none) : InstFailsR c R σ cl
  /-- `InstIs` with `R` read at each call. -/
  inductive InstIsR (c : Semantics) (R : CallRel) : Subst → Clause → Option GroundTerm → Prop where
    | fails {σ : Subst} {cl : Clause} {r : Option GroundTerm} {b : Bool}
        (hp : HoldsR c R cl.vars.length σ cl.post b) (h : InstFailsR c R σ cl) : InstIsR c R σ cl r
    | gives {σ : Subst} {cl : Clause} {v : GroundTerm} (hrhs : EvalTermR c R σ cl.rhs (some v))
        (hens : ∀ t, cl.ens = some t → EvalTermR c R σ t (some (bool true)))
        (hpost : HoldsR c R cl.vars.length σ cl.post true) : InstIsR c R σ cl (some v)
end

/-- `ByClause c R f vs r`: `f` has the result `r` at `vs` by one of `Eval`'s constructors
(`clause`, `rest`, `ensFails`, `clauseEx`, `exNone`, each with the original's premises), where each
call its premises make is related by `R` in place of `Eval c`. -/
inductive ByClause (c : Semantics) (R : CallRel) : Sym → List GroundTerm → Option GroundTerm → Prop where
  | clause {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
      {σ : Subst} {r : Option GroundTerm}
      (hfn : c.lookupFn f = some fn)
      (hmem : cl ∈ fn.clauses)
      (hσ : c.WellSorted cl.vars σ)
      (hmatch : PatVals c σ cl.pats vs)
      (hreq : ∀ t, cl.req = some t → EvalTermR c R σ t (some (bool true)))
      (hpre : HoldsR c R cl.vars.length σ cl.pre true)
      (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → FailsR c R vs cl')
      (hex : cl.exs = [])
      (hrhs : EvalTermR c R σ cl.rhs r)
      (hens : ∀ t, cl.ens = some t → EvalTermR c R σ t (some (bool true)))
      (hpost : HoldsR c R cl.vars.length σ cl.post true) : ByClause c R f vs r
  | rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
      (hfn : c.lookupFn f = some fn)
      (hnone : ∀ cl ∈ fn.clauses, FailsR c R vs cl) : ByClause c R f vs (c.fnRest fn vs)
  | ensFails {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
      {σ : Subst} {t : Term} {w : Option GroundTerm}
      (hfn : c.lookupFn f = some fn)
      (hmem : cl ∈ fn.clauses)
      (hσ : c.WellSorted cl.vars σ)
      (hmatch : PatVals c σ cl.pats vs)
      (hreq : ∀ t, cl.req = some t → EvalTermR c R σ t (some (bool true)))
      (hpre : HoldsR c R cl.vars.length σ cl.pre true)
      (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → FailsR c R vs cl')
      (hex : cl.exs = [])
      (ht : cl.ens = some t) (he : EvalTermR c R σ t w) (hw : w ≠ some (bool true)) :
      ByClause c R f vs none
  | clauseEx {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
      {σ : Subst} {v : GroundTerm}
      (hfn : c.lookupFn f = some fn)
      (hmem : cl ∈ fn.clauses)
      (hσ : c.WellSorted cl.vars σ)
      (hmatch : PatVals c σ cl.pats vs)
      (hreq : ∀ t, cl.req = some t → EvalTermR c R σ t (some (bool true)))
      (hpre : HoldsR c R cl.vars.length σ cl.pre true)
      (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → FailsR c R vs cl')
      (hne : cl.exs ≠ [])
      (hrhs : EvalTermR c R σ cl.rhs (some v))
      (hens : ∀ t, cl.ens = some t → EvalTermR c R σ t (some (bool true)))
      (hpost : HoldsR c R cl.vars.length σ cl.post true)
      (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIsR c R σ' cl (some v)) :
      ByClause c R f vs (some v)
  | exNone {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
      (hfn : c.lookupFn f = some fn)
      (hmem : cl ∈ fn.clauses)
      (hne : cl.exs ≠ [])
      (hσ : c.WellSortedAt cl.vars cl.univ σ)
      (hmatch : PatVals c σ cl.pats vs)
      (hreq : ∀ t, cl.req = some t → EvalTermR c R σ t (some (bool true)))
      (hpre : HoldsR c R cl.vars.length σ cl.pre true)
      (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → FailsR c R vs cl')
      (hsome : ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ')
      (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIsR c R σ' cl none) :
      ByClause c R f vs none

variable {c : Semantics} {R R' : CallRel}

/-! ## The induction principle -/

/-- **Induction on an evaluation by its calls.** A property `P` of function, arguments and result
holds of every evaluation, if it holds of `f vs r` wherever `f` has the result `r` at `vs` by a
constructor of `Eval` whose calls each are evaluations of which `P` holds. -/
theorem Eval.calls_induct {c : Semantics} {P : Sym → List GroundTerm → Option GroundTerm → Prop}
    (step : ∀ f vs r, ByClause c (fun g ws q => Eval c g ws q ∧ P g ws q) f vs r → P f vs r)
    {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval c f vs r) : P f vs r :=
  Eval.rec (motive_1 := fun f vs r _ => P f vs r)
    (motive_2 := fun vs cl _ => FailsR c (fun g ws q => Eval c g ws q ∧ P g ws q) vs cl)
    (motive_3 := fun σ cl _ => ReqFailsR c (fun g ws q => Eval c g ws q ∧ P g ws q) σ cl)
    (motive_4 := fun σ t r _ => EvalTermR c (fun g ws q => Eval c g ws q ∧ P g ws q) σ t r)
    (motive_5 := fun σ ts rs _ => EvalTermsR c (fun g ws q => Eval c g ws q ∧ P g ws q) σ ts rs)
    (motive_6 := fun n σ p b _ => HoldsR c (fun g ws q => Eval c g ws q ∧ P g ws q) n σ p b)
    (motive_7 := fun σ cl _ => InstFailsR c (fun g ws q => Eval c g ws q ∧ P g ws q) σ cl)
    (motive_8 := fun σ cl r _ => InstIsR c (fun g ws q => Eval c g ws q ∧ P g ws q) σ cl r)
    -- Eval
    (fun hfn hmem hσ hmatch _ _ _ hex _ _ _ ihreq ihpre ihprio ihrhs ihens ihpost =>
      step _ _ _ (.clause hfn hmem hσ hmatch ihreq ihpre ihprio hex ihrhs ihens ihpost))
    (fun hfn _ ihnone => step _ _ _ (.rest hfn ihnone))
    (fun hfn hmem hσ hmatch _ _ _ hex ht _ hw ihreq ihpre ihprio ihe =>
      step _ _ _ (.ensFails hfn hmem hσ hmatch ihreq ihpre ihprio hex ht ihe hw))
    (fun hfn hmem hσ hmatch _ _ _ hne _ _ _ _ ihreq ihpre ihprio ihrhs ihens ihpost ihall =>
      step _ _ _ (.clauseEx hfn hmem hσ hmatch ihreq ihpre ihprio hne ihrhs ihens ihpost ihall))
    (fun hfn hmem hne hσ hmatch _ _ _ hsome _ ihreq ihpre ihprio ihall =>
      step _ _ _ (.exNone hfn hmem hne hσ hmatch ihreq ihpre ihprio hsome ihall))
    -- Fails, ReqFails
    (fun _ ih => .intro ih)
    (fun ht _ hr ihe => .intro ht ihe hr)
    (fun _ ih => .pre ih)
    -- EvalTerm
    .var
    .dv
    (fun _ ih => .inj ih)
    (fun h _ ihts => .ctor h ihts)
    (fun h hhk _ hh hund ihts => .hook h hhk ihts hh hund)
    (fun h hhk hp _ hr ihts => .param h hhk hp ihts hr)
    (fun h hh _ hvs hf hp ihts ihf => .call h hh ihts hvs ⟨hf, ihf⟩ hp)
    (fun h hh _ hvs hp ihts => .callUndef h hh ihts hvs hp)
    (fun h ho _ hnf ihts => .ovl h ho ihts hnf)
    (fun h ho _ hvs hlo hcov hf ihts ihf => .ovlFn h ho ihts hvs hlo hcov ⟨hf, ihf⟩)
    -- EvalTerms
    .nil
    (fun _ _ ih ihs => .cons ih ihs)
    -- Holds
    .top
    .bot
    (fun _ ih => .not ih)
    (fun _ _ ih ih' => .and ih ih')
    (fun _ _ ih ih' => .or ih ih')
    (fun _ _ ih ih' => .implies ih ih')
    (fun _ ih => .ceil ih)
    (fun _ _ ih ih' => .equals ih ih')
    (fun _ _ ih ih' => .mem ih ih')
    (fun _ ih => .exNone ih)
    (fun g _ _ hr ih ihb => .exSome g ih ihb hr)
    (fun g _ hr ihb => .ex g ihb hr)
    (fun g _ hr ihb => .all g ihb hr)
    -- InstFails, InstIs
    (fun ht _ hw ihe => .ens ht ihe hw)
    (fun _ ih => .post ih)
    (fun _ ih => .rhs ih)
    (fun _ _ ihp ih => .fails ihp ih)
    (fun _ _ _ ihrhs ihens ihpost => .gives ihrhs ihens ihpost)
    h

/-! ## Monotone in the relation -/

mutual
  theorem FailsR.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {vs : List GroundTerm} {cl : Clause} :
      FailsR c R vs cl → FailsR c R' vs cl
    | .intro h => .intro fun σ hw hm => (h σ hw hm).mono hR
  theorem ReqFailsR.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {σ : Subst} {cl : Clause} :
      ReqFailsR c R σ cl → ReqFailsR c R' σ cl
    | .intro ht he hr => .intro ht (he.mono hR) hr
    | .pre h => .pre (h.mono hR)
  theorem EvalTermR.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {σ : Subst} {t : Term}
      {r : Option GroundTerm} : EvalTermR c R σ t r → EvalTermR c R' σ t r
    | .var => .var
    | .dv => .dv
    | .inj h => .inj (h.mono hR)
    | .ctor h hts => .ctor h (hts.mono hR)
    | .hook h hhk hts hh hund => .hook h hhk (hts.mono hR) hh hund
    | .param h hhk hp hts hr => .param h hhk hp (hts.mono hR) hr
    | .call h hh hts hvs hf hp => .call h hh (hts.mono hR) hvs (hR _ _ _ hf) hp
    | .callUndef h hh hts hvs hp => .callUndef h hh (hts.mono hR) hvs hp
    | .ovl h ho hts hnf => .ovl h ho (hts.mono hR) hnf
    | .ovlFn h ho hts hvs hlo hcov hf => .ovlFn h ho (hts.mono hR) hvs hlo hcov (hR _ _ _ hf)
  theorem EvalTermsR.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {σ : Subst} {ts : List Term}
      {rs : List (Option GroundTerm)} : EvalTermsR c R σ ts rs → EvalTermsR c R' σ ts rs
    | .nil => .nil
    | .cons h hs => .cons (h.mono hR) (hs.mono hR)
  theorem HoldsR.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {n : Nat} {σ : Subst} {p : Cond} {b : Bool} :
      HoldsR c R n σ p b → HoldsR c R' n σ p b
    | .top => .top
    | .bot => .bot
    | .not h => .not (h.mono hR)
    | .and h h' => .and (h.mono hR) (h'.mono hR)
    | .or h h' => .or (h.mono hR) (h'.mono hR)
    | .implies h h' => .implies (h.mono hR) (h'.mono hR)
    | .ceil h => .ceil (h.mono hR)
    | .equals h h' => .equals (h.mono hR) (h'.mono hR)
    | .mem h h' => .mem (h.mono hR) (h'.mono hR)
    | .exNone h => .exNone (h.mono hR)
    | .exSome g h hb hr => .exSome g (h.mono hR) (fun σ' he hp => (hb σ' he hp).mono hR) hr
    | .ex g hb hr => .ex g (fun σ' he => (hb σ' he).mono hR) hr
    | .all g hb hr => .all g (fun σ' he => (hb σ' he).mono hR) hr
  theorem InstFailsR.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {σ : Subst} {cl : Clause} :
      InstFailsR c R σ cl → InstFailsR c R' σ cl
    | .ens ht he hw => .ens ht (he.mono hR) hw
    | .post h => .post (h.mono hR)
    | .rhs h => .rhs (h.mono hR)
  theorem InstIsR.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {σ : Subst} {cl : Clause}
      {r : Option GroundTerm} : InstIsR c R σ cl r → InstIsR c R' σ cl r
    | .fails hp h => .fails (hp.mono hR) (h.mono hR)
    | .gives hrhs hens hpost => .gives (hrhs.mono hR) (fun t ht => (hens t ht).mono hR) (hpost.mono hR)
end

/-- `ByClause` is monotone in the relation read at the calls. -/
theorem ByClause.mono (hR : ∀ g ws q, R g ws q → R' g ws q) {f : Sym} {vs : List GroundTerm}
    {r : Option GroundTerm} : ByClause c R f vs r → ByClause c R' f vs r
  | .clause hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost =>
    .clause hfn hmem hσ hmatch (fun t ht => (hreq t ht).mono hR) (hpre.mono hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).mono hR) hex (hrhs.mono hR)
      (fun t ht => (hens t ht).mono hR) (hpost.mono hR)
  | .rest hfn hnone => .rest hfn fun cl hm => (hnone cl hm).mono hR
  | .ensFails hfn hmem hσ hmatch hreq hpre hprio hex ht he hw =>
    .ensFails hfn hmem hσ hmatch (fun t ht => (hreq t ht).mono hR) (hpre.mono hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).mono hR) hex ht (he.mono hR) hw
  | .clauseEx hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall =>
    .clauseEx hfn hmem hσ hmatch (fun t ht => (hreq t ht).mono hR) (hpre.mono hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).mono hR) hne (hrhs.mono hR)
      (fun t ht => (hens t ht).mono hR) (hpost.mono hR) (fun σ' ha hw => (hall σ' ha hw).mono hR)
  | .exNone hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    .exNone hfn hmem hne hσ hmatch (fun t ht => (hreq t ht).mono hR) (hpre.mono hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).mono hR) hsome (fun σ' ha hw => (hall σ' ha hw).mono hR)

/-! ## At a relation that implies `Eval c`: the originals -/

mutual
  theorem FailsR.toEval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {vs : List GroundTerm} {cl : Clause} :
      FailsR c R vs cl → Fails c vs cl
    | .intro h => .intro fun σ hw hm => (h σ hw hm).toEval hR
  theorem ReqFailsR.toEval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {σ : Subst} {cl : Clause} :
      ReqFailsR c R σ cl → ReqFails c σ cl
    | .intro ht he hr => .intro ht (he.toEval hR) hr
    | .pre h => .pre (h.toEval hR)
  theorem EvalTermR.toEval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {σ : Subst} {t : Term}
      {r : Option GroundTerm} : EvalTermR c R σ t r → EvalTerm c σ t r
    | .var => .var
    | .dv => .dv
    | .inj h => .inj (h.toEval hR)
    | .ctor h hts => .ctor h (hts.toEval hR)
    | .hook h hhk hts hh hund => .hook h hhk (hts.toEval hR) hh hund
    | .param h hhk hp hts hr => .param h hhk hp (hts.toEval hR) hr
    | .call h hh hts hvs hf hp => .call h hh (hts.toEval hR) hvs (hR _ _ _ hf) hp
    | .callUndef h hh hts hvs hp => .callUndef h hh (hts.toEval hR) hvs hp
    | .ovl h ho hts hnf => .ovl h ho (hts.toEval hR) hnf
    | .ovlFn h ho hts hvs hlo hcov hf => .ovlFn h ho (hts.toEval hR) hvs hlo hcov (hR _ _ _ hf)
  theorem EvalTermsR.toEval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {σ : Subst} {ts : List Term}
      {rs : List (Option GroundTerm)} : EvalTermsR c R σ ts rs → EvalTerms c σ ts rs
    | .nil => .nil
    | .cons h hs => .cons (h.toEval hR) (hs.toEval hR)
  theorem HoldsR.toEval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {n : Nat} {σ : Subst} {p : Cond}
      {b : Bool} : HoldsR c R n σ p b → Holds c n σ p b
    | .top => .top
    | .bot => .bot
    | .not h => .not (h.toEval hR)
    | .and h h' => .and (h.toEval hR) (h'.toEval hR)
    | .or h h' => .or (h.toEval hR) (h'.toEval hR)
    | .implies h h' => .implies (h.toEval hR) (h'.toEval hR)
    | .ceil h => .ceil (h.toEval hR)
    | .equals h h' => .equals (h.toEval hR) (h'.toEval hR)
    | .mem h h' => .mem (h.toEval hR) (h'.toEval hR)
    | .exNone h => .exNone (h.toEval hR)
    | .exSome g h hb hr => .exSome g (h.toEval hR) (fun σ' he hp => (hb σ' he hp).toEval hR) hr
    | .ex g hb hr => .ex g (fun σ' he => (hb σ' he).toEval hR) hr
    | .all g hb hr => .all g (fun σ' he => (hb σ' he).toEval hR) hr
  theorem InstFailsR.toEval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {σ : Subst} {cl : Clause} :
      InstFailsR c R σ cl → InstFails c σ cl
    | .ens ht he hw => .ens ht (he.toEval hR) hw
    | .post h => .post (h.toEval hR)
    | .rhs h => .rhs (h.toEval hR)
  theorem InstIsR.toEval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {σ : Subst} {cl : Clause}
      {r : Option GroundTerm} : InstIsR c R σ cl r → InstIs c σ cl r
    | .fails hp h => .fails (hp.toEval hR) (h.toEval hR)
    | .gives hrhs hens hpost =>
      .gives (hrhs.toEval hR) (fun t ht => (hens t ht).toEval hR) (hpost.toEval hR)
end

/-- At a relation that implies `Eval c`, a result by a constructor is a result. -/
theorem ByClause.eval (hR : ∀ g ws q, R g ws q → Eval c g ws q) {f : Sym} {vs : List GroundTerm}
    {r : Option GroundTerm} : ByClause c R f vs r → Eval c f vs r
  | .clause hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost =>
    .clause hfn hmem hσ hmatch (fun t ht => (hreq t ht).toEval hR) (hpre.toEval hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).toEval hR) hex (hrhs.toEval hR)
      (fun t ht => (hens t ht).toEval hR) (hpost.toEval hR)
  | .rest hfn hnone => .rest hfn fun cl hm => (hnone cl hm).toEval hR
  | .ensFails hfn hmem hσ hmatch hreq hpre hprio hex ht he hw =>
    .ensFails hfn hmem hσ hmatch (fun t ht => (hreq t ht).toEval hR) (hpre.toEval hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).toEval hR) hex ht (he.toEval hR) hw
  | .clauseEx hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall =>
    .clauseEx hfn hmem hσ hmatch (fun t ht => (hreq t ht).toEval hR) (hpre.toEval hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).toEval hR) hne (hrhs.toEval hR)
      (fun t ht => (hens t ht).toEval hR) (hpost.toEval hR) (fun σ' ha hw => (hall σ' ha hw).toEval hR)
  | .exNone hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    .exNone hfn hmem hne hσ hmatch (fun t ht => (hreq t ht).toEval hR) (hpre.toEval hR)
      (fun cl' hm ha hp => (hprio cl' hm ha hp).toEval hR) hsome (fun σ' ha hw => (hall σ' ha hw).toEval hR)

/-- The step of `Eval.calls_induct` holds an evaluation of `f` at `vs` itself. -/
theorem ByClause.eval_of_and {P : CallRel} {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
    (h : ByClause c (fun g ws q => Eval c g ws q ∧ P g ws q) f vs r) : Eval c f vs r :=
  h.eval fun _ _ _ hq => hq.1

/-- **An evaluation is a constructor of `Eval` over evaluations**: the instance of
`Eval.calls_induct` at `P := ByClause c (Eval c)`, with the converse. The seven mirrored relations
therefore hold every premise of the originals. -/
theorem Eval.byClause_iff {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} :
    Eval c f vs r ↔ ByClause c (Eval c) f vs r :=
  ⟨Eval.calls_induct (P := ByClause c (Eval c)) fun _ _ _ h => h.mono fun _ _ _ hq => hq.1,
   ByClause.eval fun _ _ _ hq => hq⟩

end KCore
