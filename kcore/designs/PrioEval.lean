/-
  Prototype for KN-0: evaluation with clause priorities and without clause order, and the proof
  that it is functional when clauses of equal priority are coherent. `prio` stands for the field
  `Clause.prio` that KN-2 adds; the catch-all clause is an ordinary clause of priority 200.
-/
import KcoreSpec.EvalSound

set_option autoImplicit false

namespace KCore.Proto

open KCore

variable (prio : Clause → Nat)

mutual
  inductive Eval (c : Semantics) : Sym → List GroundTerm → Option GroundTerm → Prop where
    /-- A clause that applies decides, when no clause of a smaller priority applies. -/
    | clause {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
        {σ : Subst} {r : Option GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hmem : cl ∈ fn.clauses)
        (hσ : c.WellSorted cl.vars σ)
        (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
        (hprio : ∀ cl' ∈ fn.clauses, prio cl' < prio cl → Fails c vs cl')
        (hrhs : EvalTerm c σ cl.rhs r) : Eval c f vs r
    /-- Where no clause applies, `f` is undefined. -/
    | undef {f : Sym} {fn : Fn} {vs : List GroundTerm}
        (hfn : c.lookupFn f = some fn)
        (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) : Eval c f vs none
  inductive Fails (c : Semantics) : List GroundTerm → Clause → Prop where
    | intro {vs : List GroundTerm} {cl : Clause}
        (h : ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs → ReqFails c σ cl) :
        Fails c vs cl
  inductive ReqFails (c : Semantics) : Subst → Clause → Prop where
    | intro {σ : Subst} {cl : Clause} {t : Term} {r : Option GroundTerm}
        (ht : cl.req = some t) (he : EvalTerm c σ t r) (hr : r ≠ some (bool true)) :
        ReqFails c σ cl
  inductive EvalTerm (c : Semantics) : Subst → Term → Option GroundTerm → Prop where
    | var {σ : Subst} {i : Nat} : EvalTerm c σ (.var i) (σ.lookup i)
    | dv {σ : Subst} {s : Srt} {lit : Lit} : EvalTerm c σ (.dv s lit) (some (.dv s lit))
    | inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r) :
        EvalTerm c σ (.inj a b t) (r.map (injNormal a b))
    | ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = true) (hts : EvalTerms c σ ts rs) :
        EvalTerm c σ (.app f ts) ((allSome rs).map (.ctor f))
    | hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = true) (hts : EvalTerms c σ ts rs)
        (hh : ∀ vs, allSome rs = some vs → hook f vs = some r)
        (hund : allSome rs = none → r = none) : EvalTerm c σ (.app f ts) r
    | param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {r : Option GroundTerm}
        (h : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true)
        (hts : EvalTerms c σ ts rs) (hr : r = (allSome rs).bind (c.paramVal f)) :
        EvalTerm c σ (.app f ts) r
    | call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        {vs : List GroundTerm} {r : Option GroundTerm}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms c σ ts rs)
        (hvs : allSome rs = some vs) (hf : Eval c f vs r) (hp : c.isParam f = false) :
        EvalTerm c σ (.app f ts) r
    | callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
        (h : c.isCtor f = false) (hh : isHook f = false) (hts : EvalTerms c σ ts rs)
        (hvs : allSome rs = none) (hp : c.isParam f = false) : EvalTerm c σ (.app f ts) none
  inductive EvalTerms (c : Semantics) : Subst → List Term → List (Option GroundTerm) → Prop where
    | nil {σ : Subst} : EvalTerms c σ [] []
    | cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
        {rs : List (Option GroundTerm)}
        (h : EvalTerm c σ t r) (hs : EvalTerms c σ ts rs) : EvalTerms c σ (t :: ts) (r :: rs)
end

variable {prio} {c : Semantics}

mutual
  theorem EvalTerm.congr {σ σ' : Subst} : ∀ {t : Term} {r : Option GroundTerm},
      EvalTerm prio c σ t r → (∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) → EvalTerm prio c σ' t r
    | .var i, r, h, ha => by
      cases h
      rw [ha i (by simp [varOccs])]
      exact .var
    | .dv s l, r, h, _ => by cases h; exact .dv
    | .inj a b t, r, h, ha => by
      cases h with
      | inj h' => exact .inj (EvalTerm.congr h' (fun i hi => ha i (by simpa [varOccs] using hi)))
    | .as t i, r, h, _ => by cases h
    | .app f ts, r, h, ha => by
      have ha' : ∀ i ∈ varOccsList ts, σ.lookup i = σ'.lookup i :=
        fun i hi => ha i (by simpa [varOccs] using hi)
      cases h with
      | ctor hk hts => exact .ctor hk (EvalTerms.congr hts ha')
      | hook hk hhk hts hh hund => exact .hook hk hhk (EvalTerms.congr hts ha') hh hund
      | param hk hhk hp hts hr => exact .param hk hhk hp (EvalTerms.congr hts ha') hr
      | call hk hhk hts hvs hf hp => exact .call hk hhk (EvalTerms.congr hts ha') hvs hf hp
      | callUndef hk hhk hts hvs hp => exact .callUndef hk hhk (EvalTerms.congr hts ha') hvs hp
  termination_by structural t => t
  theorem EvalTerms.congr {σ σ' : Subst} : ∀ {ts : List Term} {rs : List (Option GroundTerm)},
      EvalTerms prio c σ ts rs → (∀ i ∈ varOccsList ts, σ.lookup i = σ'.lookup i) →
        EvalTerms prio c σ' ts rs
    | [], rs, h, _ => by cases h; exact .nil
    | t :: ts, rs, h, ha => by
      cases h with
      | cons h1 h2 =>
        exact .cons (EvalTerm.congr h1 (fun i hi => ha i (by simp [varOccsList, hi])))
          (EvalTerms.congr h2 (fun i hi => ha i (by simp [varOccsList, hi])))
  termination_by structural ts => ts
end

mutual
  /-- A term and the terms inside it. Evaluation is strict, so a derivation for a term holds one
  for each of them. -/
  def subterms : Term → List Term
    | .var i => [.var i]
    | .dv s l => [.dv s l]
    | .inj a b t => .inj a b t :: subterms t
    | .as t i => .as t i :: subterms t
    | .app f ts => .app f ts :: subtermsList ts
    termination_by structural t => t
  def subtermsList : List Term → List Term
    | [] => []
    | t :: ts => subterms t ++ subtermsList ts
    termination_by structural ts => ts
end

variable (prio c) in
/-- `u` has one result under σ. -/
def Fun (σ : Subst) (u : Term) : Prop :=
  ∀ r r', EvalTerm prio c σ u r → EvalTerm prio c σ u r' → r = r'

variable (prio c) in
/-- Every term inside `t` has one result under σ. -/
def HDet (σ : Subst) (t : Term) : Prop := ∀ u ∈ subterms t, Fun prio c σ u

variable (prio c) in
def AppliesAt (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  c.WellSorted cl.vars σ ∧ PatVals c σ cl.pats vs ∧
    ∀ t, cl.req = some t → EvalTerm prio c σ t (some (bool true))

variable (prio c) in
/-- Two clauses (or one clause twice) are coherent: where both apply at one argument list, they
are the same instance of one right-hand side, or their right-hand sides have the same result.
The one who shows it may use that the terms of the first clause's `requires` and right-hand side
each have one result under its match: that is what the functionality proof has in hand at that
point, and what a check that two `requires` exclude each other reads. -/
def Coherent (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', AppliesAt prio c cl σ vs → AppliesAt prio c cl' σ' vs →
    (∀ t, cl.req = some t → HDet prio c σ t) → HDet prio c σ cl.rhs →
    (cl.rhs = cl'.rhs ∧ ∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∨
    ∀ r r', EvalTerm prio c σ cl.rhs r → EvalTerm prio c σ' cl'.rhs r' → r = r'

variable (prio c) in
def CoherentAll : Prop :=
  ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, ∀ cl' ∈ fn.clauses, prio cl = prio cl' →
    Coherent prio c cl cl'

abbrev M1 (prio : Clause → Nat) (c : Semantics) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ r', Eval prio c f vs r' → r = r'
abbrev M2 (prio : Clause → Nat) (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∀ σ, AppliesAt prio c cl σ vs → False
abbrev M3 (prio : Clause → Nat) (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  (∀ t, cl.req = some t → EvalTerm prio c σ t (some (bool true))) → False
abbrev M4 (prio : Clause → Nat) (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  (∀ r', EvalTerm prio c σ t r' → r = r') ∧ HDet prio c σ t
abbrev M5 (prio : Clause → Nat) (c : Semantics) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  (∀ rs', EvalTerms prio c σ ts rs' → rs = rs') ∧ ∀ u ∈ subtermsList ts, Fun prio c σ u

theorem mk4 {σ : Subst} {t : Term} {r : Option GroundTerm}
    (top : ∀ r', EvalTerm prio c σ t r' → r = r')
    (sub : ∀ u ∈ subterms t, u = t ∨ Fun prio c σ u) : M4 prio c σ t r :=
  ⟨top, fun u hu => (sub u hu).elim (fun h => h ▸ fun _ _ h1 h2 => (top _ h1).symm.trans (top _ h2)) id⟩

theorem not_fails {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (ihreq : ∀ t, cl.req = some t → M4 prio c σ t (some (bool true))) (hf : Fails prio c vs cl) :
    False := by
  cases hf with
  | intro h =>
    cases h σ hσ hmatch with
    | intro ht he hr => exact hr ((ihreq _ ht).1 _ he).symm

theorem case_clause (hco : CoherentAll prio c) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {cl : Clause} {σ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm prio c σ t (some (bool true)))
    (hrhs : EvalTerm prio c σ cl.rhs r)
    (ihreq : ∀ t, cl.req = some t → M4 prio c σ t (some (bool true)))
    (ihprio : ∀ cl' ∈ fn.clauses, prio cl' < prio cl → M2 prio c vs cl')
    (ihrhs : M4 prio c σ cl.rhs r) : M1 prio c f vs r := by
  intro r' h'
  cases h' with
  | @clause _ _ _ cl' σ' _ hfn' hmem' hσ' hmatch' hreq' hprio' hrhs' =>
    rw [hfn] at hfn'; cases hfn'
    rcases Nat.lt_trichotomy (prio cl) (prio cl') with hlt | heq | hgt
    · exact (not_fails hσ hmatch ihreq (hprio' _ hmem hlt)).elim
    · rcases hco f fn hfn cl hmem cl' hmem' heq vs σ σ' ⟨hσ, hmatch, hreq⟩ ⟨hσ', hmatch', hreq'⟩
          (fun t ht => (ihreq t ht).2) ihrhs.2 with ⟨he, hv⟩ | hr
      · rw [← he] at hrhs'
        exact ihrhs.1 r' (EvalTerm.congr hrhs' fun i hi => (hv i hi).symm)
      · exact hr _ _ hrhs hrhs'
    · exact (ihprio _ hmem' hgt _ ⟨hσ', hmatch', hreq'⟩).elim
  | undef hfn' hnone' =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails hσ hmatch ihreq (hnone' _ hmem)).elim

theorem case_undef {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn)
    (ihnone : ∀ cl ∈ fn.clauses, M2 prio c vs cl) : M1 prio c f vs none := by
  intro r' h'
  cases h' with
  | clause hfn' hmem' hσ' hmatch' hreq' _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ hmem' _ ⟨hσ', hmatch', hreq'⟩).elim
  | undef => rfl

theorem case_inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm}
    (ih : M4 prio c σ t r) : M4 prio c σ (.inj a b t) (r.map (injNormal a b)) :=
  mk4 (fun r' h' => by cases h' with | inj h'' => rw [ih.1 _ h''])
    (fun u hu => by
      simp only [subterms, List.mem_cons] at hu
      exact hu.imp id (ih.2 u))

theorem sub_app {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (ihts : M5 prio c σ ts rs) : ∀ u ∈ subterms (.app f ts), u = .app f ts ∨ Fun prio c σ u :=
  fun u hu => by
    simp only [subterms, List.mem_cons] at hu
    exact hu.imp id (ihts.2 u)

theorem case_ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = true) (ihts : M5 prio c σ ts rs) :
    M4 prio c σ (.app f ts) ((allSome rs).map (.ctor f)) :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor _ hts' => rw [ihts.1 _ hts']
    | hook h => rw [hk] at h; cases h
    | param h => rw [hk] at h; cases h
    | call h => rw [hk] at h; cases h
    | callUndef h => rw [hk] at h; cases h) (sub_app ihts)

theorem case_hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = true)
    (hh : ∀ vs, allSome rs = some vs → hook f vs = some r) (hund : allSome rs = none → r = none)
    (ihts : M5 prio c σ ts rs) : M4 prio c σ (.app f ts) r :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ _ hts' hh' hund' =>
      have := ihts.1 _ hts'; subst this
      cases hall : allSome rs with
      | none => rw [hund hall, hund' hall]
      | some vs => exact Option.some.inj ((hh vs hall).symm.trans (hh' vs hall))
    | param _ h => rw [hhk] at h; cases h
    | call _ h => rw [hhk] at h; cases h
    | callUndef _ h => rw [hhk] at h; cases h) (sub_app ihts)

theorem case_param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = false)
    (hp : c.isParam f = true) (hr : r = (allSome rs).bind (c.paramVal f))
    (ihts : M5 prio c σ ts rs) : M4 prio c σ (.app f ts) r :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hhk] at h; cases h
    | param _ _ _ hts' hr' => have := ihts.1 _ hts'; subst this; rw [hr, hr']
    | call _ _ _ _ _ h => rw [hp] at h; cases h
    | callUndef _ _ _ _ h => rw [hp] at h; cases h) (sub_app ihts)

theorem case_call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {r : Option GroundTerm} (hk : c.isCtor f = false)
    (hhk : isHook f = false) (hvs : allSome rs = some vs) (hp : c.isParam f = false)
    (ihts : M5 prio c σ ts rs) (ihf : M1 prio c f vs r) : M4 prio c σ (.app f ts) r :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hhk] at h; cases h
    | param _ _ h => rw [hp] at h; cases h
    | call _ _ hts' hvs' hf' _ =>
      have := ihts.1 _ hts'; subst this
      rw [hvs] at hvs'; cases hvs'
      exact ihf _ hf'
    | callUndef _ _ hts' hvs' _ =>
      have := ihts.1 _ hts'; subst this
      rw [hvs] at hvs'; cases hvs') (sub_app ihts)

theorem case_callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (hhk : isHook f = false) (hvs : allSome rs = none)
    (hp : c.isParam f = false) (ihts : M5 prio c σ ts rs) : M4 prio c σ (.app f ts) none :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hhk] at h; cases h
    | param _ _ h => rw [hp] at h; cases h
    | call _ _ hts' hvs' _ _ =>
      have := ihts.1 _ hts'; subst this
      rw [hvs] at hvs'; cases hvs'
    | callUndef => rfl) (sub_app ihts)

theorem case_cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} (ih1 : M4 prio c σ t r) (ih2 : M5 prio c σ ts rs) :
    M5 prio c σ (t :: ts) (r :: rs) :=
  ⟨fun rs' h' => by cases h' with | cons h1 h2 => rw [ih1.1 _ h1, ih2.1 _ h2],
   fun u hu => by
    simp only [subtermsList, List.mem_append] at hu
    exact hu.elim (ih1.2 u) (ih2.2 u)⟩

/-- Evaluation by priorities has one result when clauses of equal priority are coherent. -/
theorem Eval.functional (hco : CoherentAll prio c) {f : Sym}
    {vs : List GroundTerm} {r r' : Option GroundTerm} (h : Eval prio c f vs r)
    (h' : Eval prio c f vs r') : r = r' :=
  Eval.rec (motive_1 := fun f vs r _ => M1 prio c f vs r) (motive_2 := fun vs cl _ => M2 prio c vs cl)
    (motive_3 := fun σ cl _ => M3 prio c σ cl) (motive_4 := fun σ t r _ => M4 prio c σ t r)
    (motive_5 := fun σ ts rs _ => M5 prio c σ ts rs)
    (fun hfn hmem hσ hmatch hreq _ hrhs ihreq ihprio ihrhs =>
      case_clause hco hfn hmem hσ hmatch hreq hrhs ihreq ihprio ihrhs)
    (fun hfn _ ihnone => case_undef hfn ihnone)
    (fun _ ih => fun σ ha => ih σ ha.1 ha.2.1 ha.2.2)
    (fun ht _ hr ihe => fun hall => hr (ihe.1 _ (hall _ ht)))
    (mk4 (fun r' h' => by cases h'; rfl) (fun u hu => by simp only [subterms, List.mem_singleton] at hu; exact .inl hu))
    (mk4 (fun r' h' => by cases h'; rfl) (fun u hu => by simp only [subterms, List.mem_singleton] at hu; exact .inl hu))
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs _ hp ihts ihf => case_call hk hhk hvs hp ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    ⟨fun rs' h' => by cases h'; rfl, fun u hu => by simp [subtermsList] at hu⟩
    (fun _ _ ih1 ih2 => case_cons ih1 ih2)
    h r' h'

end KCore.Proto

#print axioms KCore.Proto.Eval.functional
