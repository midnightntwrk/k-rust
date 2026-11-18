/-
  The heads of the KORE patterns the semantics writes for its functions and rules: every head
  (`appHeadsOf`) of a clause's equation and of a rule's axiom is one of Γ's heads (`gammaHeads`).

  - **A context's heads are Γ's (`CtxG`).** A term well sorted in a context (`sortOfTerm`) applies
    only the context's symbols, each at the head `Term.kore` writes for it (`gammaHead`), and `inj`
    only at the context's subsort pairs. Where every symbol the context gives a signature is one of
    Γ's (`kernelSyms`) and every pair is one of `c.subsorts`, the term's translation applies Γ's
    heads only (`term`). This holds of the right-hand sides' context and of the left-hand sides'
    (`ctxG_rhsCtx`, `ctxG_patCtxAll`), so of every condition `condOK` accepts (`cond`).
  - **The builders (`premise`, ..., `prioRuleK`).** Each pattern a clause's equation or a rule's
    axiom is made of applies the heads of its parts and, in an equation, the function's own head
    `gammaHead c f.label`.
  - **Under `coreOK` (`prioEquation_coreOK`, `prioRuleK_coreOK`).** The parts of the user's
    clauses and rules are well sorted (`clauseSorted`, `ruleSorted`) and the user's clauses bind no
    existential variable, so their right side's predicate, which `clauseSorted` does not check, is
    not written; the sort predicates' clauses apply `kseq`, `dotk` and `inj` at a pair
    `(X, KItem)` of `c.subsorts`; and a function's equations apply it at the head its
    applications are written at (`symApp`), which is one of Γ's.
-/
import KcoreSpec.TieHeadsWalk

set_option autoImplicit false

namespace KCore

open Faithful

namespace GHKore

/-- Every head of the KORE pattern is one of Γ's. -/
def HIn (c : Semantics) (p : Kore.Pattern) : Prop := appHeadsOf p ⊆ gammaHeads c

/-- Every head of the KORE patterns is one of Γ's. -/
def HInL (c : Semantics) (ps : List Kore.Pattern) : Prop := appHeadsOfList ps ⊆ gammaHeads c

/-- Every head of the axiom's pattern is one of Γ's; a sentence that is no axiom has none. -/
def SentHIn (c : Semantics) : Kore.Sentence → Prop
  | .axiom a => HIn c a.pattern
  | _ => True

variable {c : Semantics}

theorem hinL_iff : ∀ (ps : List Kore.Pattern), HInL c ps ↔ ∀ p ∈ ps, HIn c p
  | [] => by simp [HInL, appHeadsOfList]
  | p :: ps => by
    simp only [HInL, appHeadsOfList, List.append_subset, List.mem_cons, forall_eq_or_imp]
    exact and_congr Iff.rfl (hinL_iff ps)

theorem hinL_nil : HInL c [] := by simp [HInL, appHeadsOfList]

theorem hinL_cons {p : Kore.Pattern} {ps : List Kore.Pattern} :
    HInL c (p :: ps) ↔ HIn c p ∧ HInL c ps := by
  simp only [HInL, HIn, appHeadsOfList, List.append_subset]

theorem hinL_append {ps qs : List Kore.Pattern} : HInL c (ps ++ qs) ↔ HInL c ps ∧ HInL c qs := by
  simp only [hinL_iff, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (.inl hp), fun p hp => h p (.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

/-! ## The connectives -/

section Conn

variable {S S' : Kore.KSort} {p q : Kore.Pattern} {ps : List Kore.Pattern}

@[simp] theorem hin_var (x : Kore.VarPattern) : HIn c (.var x) := by simp [HIn, appHeadsOf]
@[simp] theorem hin_top : HIn c (.top S) := by simp [HIn, appHeadsOf]
@[simp] theorem hin_bottom : HIn c (.bottom S) := by simp [HIn, appHeadsOf]
@[simp] theorem hin_dv (l : String) : HIn c (.dv S l) := by simp [HIn, appHeadsOf]
@[simp] theorem hin_not : HIn c (.not S p) ↔ HIn c p := by simp [HIn, appHeadsOf]
@[simp] theorem hin_exist (x : Kore.EVar) : HIn c (.exist S x p) ↔ HIn c p := by simp [HIn, appHeadsOf]
@[simp] theorem hin_ceil : HIn c (.ceil S S' p) ↔ HIn c p := by simp [HIn, appHeadsOf]
@[simp] theorem hin_and : HIn c (.and S ps) ↔ HInL c ps := by simp [HIn, HInL, appHeadsOf]
@[simp] theorem hin_or : HIn c (.or S ps) ↔ HInL c ps := by simp [HIn, HInL, appHeadsOf]
@[simp] theorem hin_implies : HIn c (.implies S p q) ↔ HIn c p ∧ HIn c q := by
  simp [HIn, appHeadsOf, List.append_subset]
@[simp] theorem hin_rewrites : HIn c (.rewrites S p q) ↔ HIn c p ∧ HIn c q := by
  simp [HIn, appHeadsOf, List.append_subset]
@[simp] theorem hin_equals : HIn c (.equals S S' p q) ↔ HIn c p ∧ HIn c q := by
  simp [HIn, appHeadsOf, List.append_subset]
@[simp] theorem hin_in : HIn c (.in S S' p q) ↔ HIn c p ∧ HIn c q := by
  simp [HIn, appHeadsOf, List.append_subset]

theorem hin_forall (x : Kore.EVar) : HIn c (.forall S x p) ↔ HIn c p := by simp [HIn, appHeadsOf]

theorem hin_foldr_exist {α : Type} (s : Kore.KSort) (g : α → Kore.EVar) (body : Kore.Pattern) :
    ∀ (l : List α), HIn c (l.foldr (fun v p => .exist s (g v) p) body) ↔ HIn c body
  | [] => Iff.rfl
  | _ :: l => by rw [List.foldr_cons, hin_exist]; exact hin_foldr_exist s g body l

theorem hin_existsAll (s : Kore.KSort) (bs : List Kore.EVar) (body : Kore.Pattern) :
    HIn c (KoreAML.existsAll s bs body) ↔ HIn c body :=
  hin_foldr_exist s (fun b => b) body bs

theorem hin_anyOf : ∀ (l : List Kore.Pattern), (∀ p ∈ l, HIn c p) → HIn c (KoreAML.anyOf l)
  | [], _ => by simp [KoreAML.anyOf]
  | p :: l, h => by
    simp only [KoreAML.anyOf, hin_or, hinL_cons, hinL_nil, and_true]
    exact ⟨h p (List.mem_cons_self ..), hin_anyOf l fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem hin_anyOfC (S : Kore.KSort) : ∀ (l : List Kore.Pattern), (∀ p ∈ l, HIn c p) → HIn c (anyOfC S l)
  | [], _ => by simp [anyOfC]
  | p :: l, h => by
    simp only [anyOfC, hin_or, hinL_cons, hinL_nil, and_true]
    exact ⟨h p (List.mem_cons_self ..), hin_anyOfC S l fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem hin_argsConj : ∀ (i : Nat) (l : List (String × Kore.Pattern)), (∀ x ∈ l, HIn c x.2) →
    HIn c (KoreAML.argsConj i l)
  | _, [], _ => by simp [KoreAML.argsConj]
  | i, (s, p) :: rest, h => by
    simp only [KoreAML.argsConj, hin_and, hinL_cons, hinL_nil, hin_in, and_true, KoreAML.ev, hin_var,
      true_and]
    exact ⟨h (s, p) (List.mem_cons_self ..),
      hin_argsConj (i + 1) rest fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

end Conn

/-! ## Γ's heads -/

/-- The head at which `Term.kore` applies a symbol of Γ is one of Γ's. -/
theorem gammaHead_mem {k : CtorSig} (hk : k ∈ kernelSyms c) : gammaHead c k.name ∈ gammaHeads c := by
  unfold gammaHeads
  exact List.mem_append_left _ (List.mem_map_of_mem hk)

/-- `inj` at a pair of `subsorts` is one of Γ's heads. -/
theorem inj_mem {a b : Srt} (h : (a, b) ∈ c.subsorts) :
    ("inj", [KoreAML.srt (c.sortName a), KoreAML.srt (c.sortName b)]) ∈ gammaHeads c := by
  unfold gammaHeads
  exact List.mem_append_right _ (List.mem_map.mpr ⟨(a, b), h, rfl⟩)

/-- The head at which Γ applies a function is one of Γ's, where the function is one of Γ's. -/
theorem fnHead_mem {f : Fn} (hf : f ∈ c.allFns) : gammaHead c f.label ∈ gammaHeads c :=
  gammaHead_mem (c := c) (k := f.sig) (by
    unfold kernelSyms
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map_of_mem hf)))))

/-- `Term.kore` applies a symbol at its head `gammaHead`. -/
theorem kore_app_ghk (vs : List KoreAML.Var) (f : Sym) (ts : List Term) :
    Term.kore c vs (.app f ts) = .app ⟨⟨(gammaHead c f).1⟩⟩ (gammaHead c f).2 (Term.koreList c vs ts) := by
  rw [← symApp_gammaHead]; rw [Term.kore]; unfold symApp; rfl

theorem hin_app_gamma {f : Sym} {vs : List KoreAML.Var} {ts : List Term} (hf : gammaHead c f ∈ gammaHeads c)
    (hts : HInL c (Term.koreList c vs ts)) : HIn c (Term.kore c vs (.app f ts)) := by
  rw [kore_app_ghk]
  simp only [HIn, appHeadsOf, List.cons_subset]
  exact ⟨hf, hts⟩

theorem hin_inj_gamma {a b : Srt} {vs : List KoreAML.Var} {t : Term} (hab : (a, b) ∈ c.subsorts)
    (ht : HIn c (Term.kore c vs t)) : HIn c (Term.kore c vs (.inj a b t)) := by
  rw [Term.kore]
  simp only [KoreAML.injP, HIn, appHeadsOf, appHeadsOfList, List.cons_subset, List.append_nil]
  exact ⟨inj_mem hab, ht⟩

/-! ## Terms well sorted in a context of Γ's symbols -/

/-- **The context's heads are Γ's**: every symbol the context gives a signature is one of Γ's
(`kernelSyms`), and every subsort pair it admits is one of `c.subsorts`. -/
structure CtxG (c : Semantics) (x : TermCtx) : Prop where
  heads : ∀ k ∈ x.heads, k ∈ kernelSyms c
  subs : ∀ p ∈ x.subs, p ∈ c.subsorts

theorem lookupSig_mem_ghk {heads : List CtorSig} {f : Sym} {k : CtorSig} (h : lookupSig heads f = some k) :
    k ∈ heads ∧ k.name = f := by
  rw [lookupSig_eq] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

mutual
/-- **A term well sorted in a context of Γ's symbols applies Γ's heads only**, at whatever
variables it is written. -/
theorem term {x : TermCtx} (hx : CtxG c x) (vs : List Srt) (vs' : List KoreAML.Var) :
    ∀ (t : Term) {s : Srt}, sortOfTerm x vs t = some s → HIn c (Term.kore c vs' t)
  | .var _, _, _ => by rw [Term.kore]; simp [KoreAML.varAt]
  | .dv _ _, _, _ => by rw [Term.kore]; exact hin_dv _
  | .app f ts, s, h => by
    simp only [sortOfTerm] at h
    cases hk : lookupSig x.heads f with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      by_cases he : (sortsOfTerms x vs ts == some k.args) = true
      · have hm := lookupSig_mem_ghk hk
        have hg : gammaHead c f ∈ gammaHeads c := hm.2 ▸ gammaHead_mem (hx.heads k hm.1)
        exact hin_app_gamma hg (terms hx vs vs' ts (beq_iff_eq.mp he))
      · simp [he] at h
  | .inj a b t, s, h => by
    simp only [sortOfTerm] at h
    by_cases hc : (x.subs.contains (a, b) && sortOfTerm x vs t == some a) = true
    · simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
      exact hin_inj_gamma (hx.subs _ hc.1) (term hx vs vs' t hc.2)
    · rw [if_neg hc] at h; cases h
  | .as t i, s, h => by
    rw [Term.kore, hin_and, hinL_cons, hinL_cons]
    refine ⟨?_, hin_var _, hinL_nil⟩
    simp only [sortOfTerm] at h
    split at h
    · rename_i hu
      exact term hx vs vs' t hu
    · cases h
theorem terms {x : TermCtx} (hx : CtxG c x) (vs : List Srt) (vs' : List KoreAML.Var) :
    ∀ (ts : List Term) {ss : List Srt}, sortsOfTerms x vs ts = some ss → HInL c (Term.koreList c vs' ts)
  | [], _, _ => by rw [Term.koreList]; exact hinL_nil
  | t :: ts, ss, h => by
    simp only [sortsOfTerms] at h
    rw [Term.koreList, hinL_cons]
    cases h1 : sortOfTerm x vs t with
    | none => rw [h1] at h; cases h
    | some a =>
      cases h2 : sortsOfTerms x vs ts with
      | none => rw [h1, h2] at h; cases h
      | some bs => exact ⟨term hx vs vs' t h1, terms hx vs vs' ts h2⟩
end

section Kernel
variable {k : CtorSig}
theorem ks_ctor (h : k ∈ c.ctorSigs) : k ∈ kernelSyms c := by
  unfold kernelSyms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
theorem ks_fn (h : k ∈ c.allFns.map Fn.sig) : k ∈ kernelSyms c := by
  unfold kernelSyms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
theorem ks_param (h : k ∈ c.params.map (·.sig)) : k ∈ kernelSyms c := by
  unfold kernelSyms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
theorem ks_hook (h : k ∈ hookSigs) : k ∈ kernelSyms c := by
  unfold kernelSyms
  exact List.mem_append_left _ (List.mem_append_right _ h)
theorem ks_ovl (h : k ∈ c.ovlSigs) : k ∈ kernelSyms c := by
  unfold kernelSyms
  exact List.mem_append_right _ h
end Kernel

/-- The right-hand sides' context over function signatures of Γ has Γ's heads. -/
theorem ctxG_rhsCtx {fns : List CtorSig} (hf : ∀ k ∈ fns, k ∈ kernelSyms c) : CtxG c (c.rhsCtx fns) where
  heads k hk := by
    simp only [Semantics.rhsCtx, List.mem_append] at hk
    rcases hk with ((((h | h) | h) | h) | h) | h
    · exact ks_ctor h
    · exact ks_hook h
    · exact ks_param h
    · exact ks_fn (by rw [Semantics.allFns, List.map_append]; exact List.mem_append_right _ h)
    · exact hf k h
    · exact ks_ovl h
  subs _ h := h

/-- The right-hand sides' context over the user's functions has Γ's heads. -/
theorem ctxG_rhsCtx_fns : CtxG c (c.rhsCtx (c.fns.map Fn.sig)) :=
  ctxG_rhsCtx fun _ hk => ks_fn (by rw [Semantics.allFns, List.map_append]; exact List.mem_append_left _ hk)

/-- The left-hand sides' context has Γ's heads. -/
theorem ctxG_patCtxAll : CtxG c c.patCtxAll where
  heads k hk := by
    simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs, List.mem_append] at hk
    rcases hk with (h | h) | ((h | h) | h)
    · exact ks_ctor h
    · exact ks_hook (List.mem_filter.mp h).1
    · exact ks_hook (List.mem_filter.mp h).1
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      exact ks_param (List.mem_map_of_mem (List.mem_filter.mp hp).1)
    · exact ks_ovl h
  subs _ h := h

/-! ## Conditions -/

/-- **A condition `condOK` accepts applies Γ's heads only**, at whatever variables and sort it is
written. -/
theorem cond (S : Kore.KSort) :
    ∀ (p : Cond) (vars : List Srt) (vs : List KoreAML.Var), c.condOK vars p = true → HIn c (Cond.kore c vs S p)
  | .top, _, _, _ => by rw [Cond.kore]; exact hin_top
  | .bot, _, _, _ => by rw [Cond.kore]; exact hin_bottom
  | .not p, vars, vs, h => by
    rw [Cond.kore, hin_not]; exact cond S p vars vs h
  | .and p q, vars, vs, h => by
    simp only [Semantics.condOK, Bool.and_eq_true] at h
    simp only [Cond.kore, hin_and, hinL_cons, hinL_nil, and_true]
    exact ⟨cond S p vars vs h.1, cond S q vars vs h.2⟩
  | .or p q, vars, vs, h => by
    simp only [Semantics.condOK, Bool.and_eq_true] at h
    simp only [Cond.kore, hin_or, hinL_cons, hinL_nil, and_true]
    exact ⟨cond S p vars vs h.1, cond S q vars vs h.2⟩
  | .implies p q, vars, vs, h => by
    simp only [Semantics.condOK, Bool.and_eq_true] at h
    simp only [Cond.kore, hin_implies]
    exact ⟨cond S p vars vs h.1, cond S q vars vs h.2⟩
  | .ceil s t, vars, vs, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Cond.kore, hin_ceil]
    exact term ctxG_rhsCtx_fns vars vs t h.1
  | .equals s t u, vars, vs, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Cond.kore, hin_equals]
    exact ⟨term ctxG_rhsCtx_fns vars vs t h.1.1, term ctxG_rhsCtx_fns vars vs u h.1.2⟩
  | .mem s t u, vars, vs, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Cond.kore, hin_in]
    exact ⟨term ctxG_rhsCtx_fns vars vs t h.1.1, term ctxG_rhsCtx_fns vars vs u h.1.2⟩
  | .exMatch ys s p t body, vars, vs, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Cond.kore, hin_existsAll, hin_and, hinL_cons, hinL_nil, and_true, hin_in]
    exact ⟨⟨term ctxG_rhsCtx_fns vars vs t h.1.1.2, term ctxG_patCtxAll (vars ++ ys) _ p (sortOfTerm_all_of_nf h.1.1.1)⟩,
      cond S body (vars ++ ys) _ h.1.2⟩
  | .ex s body, vars, vs, h => by
    simp only [Semantics.condOK] at h
    simp only [Cond.kore, hin_exist]
    exact cond S body (vars ++ [s]) _ h
  | .all s body, vars, vs, h => by
    simp only [Semantics.condOK] at h
    simp only [Cond.kore, hin_forall]
    exact cond S body (vars ++ [s]) _ h

theorem condConj {vs : List KoreAML.Var} {S : Kore.KSort} {p : Cond} (h : HIn c (Cond.kore c vs S p)) :
    HInL c (Cond.conj c vs S p) := by
  unfold Cond.conj
  split
  · exact hinL_nil
  · exact hinL_cons.mpr ⟨h, hinL_nil⟩

/-! ## The parts of clauses and rules -/

/-- **A clause's parts apply Γ's heads only**, at whatever variables they are written: its
patterns, its `requires`, its right-hand side, its `ensures`, its premise's predicate, and its
right side's predicate where the clause binds an existential variable (only then is it written,
`clauseRhs`). -/
structure ClauseG (c : Semantics) (cl : Clause) : Prop where
  pats : ∀ vs, HInL c (Term.koreList c vs cl.pats)
  req : ∀ vs t, cl.req = some t → HIn c (Term.kore c vs t)
  rhs : ∀ vs, HIn c (Term.kore c vs cl.rhs)
  ens : ∀ vs t, cl.ens = some t → HIn c (Term.kore c vs t)
  pre : ∀ vs S, HIn c (Cond.kore c vs S cl.pre)
  post : cl.exs ≠ [] → ∀ vs S, HIn c (Cond.kore c vs S cl.post)

/-- **A rule's parts apply Γ's heads only**, at whatever variables they are written. -/
structure RuleG (c : Semantics) (r : Rule) : Prop where
  lhs : ∀ vs, HIn c (Term.kore c vs r.lhs)
  req : ∀ vs t, r.req = some t → HIn c (Term.kore c vs t)
  rhs : ∀ vs, HIn c (Term.kore c vs r.rhs)
  ens : ∀ vs t, r.ens = some t → HIn c (Term.kore c vs t)
  pre : ∀ vs S, HIn c (Cond.kore c vs S r.pre)
  post : ∀ vs S, HIn c (Cond.kore c vs S r.post)

theorem reqOK_some_ghk {x : TermCtx} {vs : List Srt} {r : Option Term} (h : reqOK x vs r = true) :
    ∀ t, r = some t → sortOfTerm x vs t = some Srt.bool := by
  rintro t rfl
  simp only [reqOK, beq_iff_eq] at h
  exact h

/-- A clause well sorted over function signatures of Γ (`clauseSorted`) has parts that apply Γ's
heads only, where it binds no existential variable or its right side's predicate is well sorted:
`clauseSorted` does not check that predicate. -/
theorem clauseG_of_sorted {f : Fn} {rhsHeads : List CtorSig} {cl : Clause}
    (hf : ∀ k ∈ rhsHeads, k ∈ kernelSyms c) (h : c.clauseSorted f rhsHeads cl = true)
    (hpost : cl.exs = [] ∨ c.condOK cl.vars cl.post = true) : ClauseG c cl := by
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hpats, -⟩, hreq⟩, hrhs⟩, hens⟩, -⟩, hpre⟩ := h
  have hx := ctxG_rhsCtx hf
  refine ⟨fun vs => terms ctxG_patCtxAll cl.vars vs cl.pats (sortsOfTerms_all_of_nf hpats),
    fun vs t ht => term hx cl.vars vs t (reqOK_some_ghk hreq t ht),
    fun vs => term hx cl.vars vs cl.rhs hrhs,
    fun vs t ht => term hx cl.vars vs t (reqOK_some_ghk hens t ht),
    fun vs S => cond S cl.pre cl.vars vs hpre, fun hne vs S => ?_⟩
  rcases hpost with hp | hp
  · exact absurd hp hne
  · exact cond S cl.post cl.vars vs hp

/-- A rule well sorted (`ruleSorted`) has parts that apply Γ's heads only. -/
theorem ruleG_of_sorted {r : Rule} (h : c.ruleSorted r = true) : RuleG c r := by
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlhs, -⟩, -⟩, -⟩, hreq⟩, hpre⟩, hens⟩, hpost⟩, -⟩, -⟩, hrhs⟩ := h
  replace hlhs := sortOfTerm_all_of_nf hlhs
  exact ⟨fun vs => term ctxG_patCtxAll r.vars vs r.lhs hlhs,
    fun vs t ht => term ctxG_rhsCtx_fns r.vars vs t (reqOK_some_ghk hreq t ht),
    fun vs => term ctxG_rhsCtx_fns r.vars vs r.rhs hrhs,
    fun vs t ht => term ctxG_rhsCtx_fns r.vars vs t (reqOK_some_ghk hens t ht),
    fun vs S => cond S r.pre r.vars vs hpre, fun vs S => cond S r.post r.vars vs hpost⟩

/-! ## The builders -/

theorem reqPat_ghk {S : Kore.KSort} {r : Option Term} {vs : List KoreAML.Var}
    (h : ∀ t, r = some t → HIn c (Term.kore c vs t)) : HIn c (reqPat S (r.map (Term.kore c vs))) := by
  cases r with
  | none => exact hin_top
  | some t => simp only [Option.map_some, reqPat, hin_equals, hin_dv, and_true]; exact h t rfl

theorem premise_ghk {vs : List KoreAML.Var} {args : List String} {req : Option Term} {pats : List Term}
    (hr : ∀ t, req = some t → HIn c (Term.kore c vs t)) (hp : HInL c (Term.koreList c vs pats)) :
    HIn c (premise args (req.map (Term.kore c vs)) (Term.koreList c vs pats)) := by
  simp only [premise, hin_and, hinL_cons, hinL_nil, and_true]
  refine ⟨reqPat_ghk hr, hin_argsConj 0 _ fun x hx => ?_⟩
  exact (hinL_iff _).mp hp x.2 (List.of_mem_zip hx).2

theorem withPre_ghk {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern} (hp : HIn c prem)
    (hpre : HIn c (Cond.kore c vs KoreAML.R cl.pre)) : HIn c (withPre c vs cl prem) := by
  unfold withPre
  split
  · exact hp
  · exact hin_and.mpr (hinL_cons.mpr ⟨hp, hinL_cons.mpr ⟨hpre, hinL_nil⟩⟩)

/-- A clause's premise with its predicate applies Γ's heads only. -/
theorem clausePremise_ghk {f : Fn} {cl : Clause} (hcl : ClauseG c cl) (vs : List KoreAML.Var) :
    HIn c (withPre c vs cl (premise (f.args.map c.sortName) (cl.req.map (Term.kore c vs))
      (Term.koreList c vs cl.pats))) :=
  withPre_ghk (premise_ghk (hcl.req vs) (hcl.pats vs)) (hcl.pre vs KoreAML.R)

theorem exclusion_ghk {f : Fn} {cl : Clause} (hcl : ClauseG c cl) (cp : ClausePres) :
    HIn c (exclusion c f cl cp) := by
  unfold exclusion
  rw [hin_existsAll]
  exact clausePremise_ghk hcl _

theorem clauseRhs_ghk {f : Fn} {cl : Clause} (hcl : ClauseG c cl) :
    HIn c (clauseRhs c f cl).1 ∧ HIn c (clauseRhs c f cl).2 := by
  unfold clauseRhs
  split
  · exact ⟨hcl.rhs _, reqPat_ghk (hcl.ens _)⟩
  · rename_i hne
    refine ⟨?_, hin_top⟩
    rw [hin_foldr_exist, hin_and, hinL_append, hinL_cons, hinL_cons]
    refine ⟨⟨hcl.rhs _, reqPat_ghk (hcl.ens _), hinL_nil⟩, condConj ?_⟩
    exact hcl.post (fun he => hne (by rw [he]; rfl)) _ _

/-- An equation of `f` applies the heads of its premise, its right side and its `ensures` part, and
`f`'s own head. -/
theorem eqnSentence_ghk {f : Fn} {prem rhs ens : Kore.Pattern} (hf : gammaHead c f.label ∈ gammaHeads c)
    (h1 : HIn c prem) (h2 : HIn c rhs) (h3 : HIn c ens) : SentHIn c (eqnSentence c f prem rhs ens) := by
  simp only [eqnSentence, KoreAML.equationAt, KoreAML.axiomR, SentHIn, hin_implies, hin_equals, hin_and,
    hinL_cons, hinL_nil, and_true]
  refine ⟨h1, ?_, h2, h3⟩
  rw [symApp_gammaHead]
  simp only [HIn, appHeadsOf, List.cons_subset]
  refine ⟨hf, ?_⟩
  have : HInL c (KoreAML.vars (KoreAML.numbered "X" 0 (f.args.map c.sortName))) :=
    (hinL_iff _).mpr fun p hp => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
      exact hin_var (.evar x)
  exact this

/-- **A clause's equation applies Γ's heads only**, where `f`'s head is Γ's and every clause of `f`
(the competitors among them) has parts that apply Γ's heads only. -/
theorem prioEquation_ghk {f : Fn} {cl : Clause} (hf : gammaHead c f.label ∈ gammaHeads c)
    (hcls : ∀ cl' ∈ f.clauses, ClauseG c cl') (hcl : ClauseG c cl) : SentHIn c (prioEquation c f cl) := by
  have hr := clauseRhs_ghk (f := f) hcl
  unfold prioEquation clauseEquation competingEquation
  split
  · exact eqnSentence_ghk hf (clausePremise_ghk hcl _) hr.1 hr.2
  · refine eqnSentence_ghk hf ?_ hr.1 hr.2
    refine hin_and.mpr (hinL_cons.mpr ⟨hin_not.mpr ?_, hinL_cons.mpr ⟨clausePremise_ghk hcl _, hinL_nil⟩⟩)
    exact hin_anyOf _ fun p hp => by
      obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hp
      exact exclusion_ghk (hcls cl' (List.mem_filter.mp hcl').1) _

theorem applies_ghk {r : Rule} (hr : RuleG c r) (rp : RulePres) : HIn c (applies c r rp) := by
  unfold applies
  rw [hin_existsAll, hin_and, hinL_append, hinL_cons, hinL_cons]
  exact ⟨⟨hr.lhs _, reqPat_ghk (hr.req _), hinL_nil⟩, condConj (hr.pre _ _)⟩

theorem ruleRight_ghk {r : Rule} (hr : RuleG c r) : HIn c (ruleRight c r) := by
  unfold ruleRight
  rw [hin_foldr_exist, hin_and, hinL_append, hinL_cons, hinL_cons]
  exact ⟨⟨hr.rhs _, reqPat_ghk (hr.ens _), hinL_nil⟩, condConj (hr.post _ _)⟩

/-- **A rule's axiom applies Γ's heads only**, where every rule (the competitors among them) has
parts that apply Γ's heads only. -/
theorem prioRuleK_ghk {r : Rule} (hrs : ∀ r' ∈ c.rules, RuleG c r') (hr : RuleG c r) :
    HIn c (prioRuleK c r) := by
  have hR := ruleRight_ghk hr
  have hleft : HInL c ([Term.kore c (canonVars c r.vars) r.lhs,
      reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
      Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre) :=
    hinL_append.mpr ⟨hinL_cons.mpr ⟨hr.lhs _, hinL_cons.mpr ⟨reqPat_ghk (hr.req _), hinL_nil⟩⟩,
      condConj (hr.pre _ _)⟩
  unfold prioRuleK
  dsimp only
  split
  · rw [hin_rewrites, hin_and, hinL_append]
    exact ⟨⟨hleft, hinL_cons.mpr ⟨hin_ceil.mpr hR, hinL_nil⟩⟩, hR⟩
  · rw [hin_rewrites, hin_and, hinL_append]
    refine ⟨⟨hleft, hinL_cons.mpr ⟨hin_not.mpr ?_, hinL_cons.mpr ⟨hin_ceil.mpr hR, hinL_nil⟩⟩⟩, hR⟩
    exact hin_anyOfC _ _ fun p hp => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hp
      exact applies_ghk (hrs r' (List.mem_filter.mp hr').1) _

/-! ## The sort predicates -/

theorem kseq_mem : gammaHead c kseq ∈ gammaHeads c :=
  gammaHead_mem (k := ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩)
    (ks_ctor (by simp [Semantics.ctorSigs, fixedCtors]))

theorem dotk_mem : gammaHead c dotk ∈ gammaHeads c :=
  gammaHead_mem (k := ⟨dotk, [], Srt.k⟩) (ks_ctor (by simp [Semantics.ctorSigs, fixedCtors]))

theorem hin_kseqPat {X : Srt} (hX : (X, Srt.kitem) ∈ c.subsorts) (vs : List KoreAML.Var) :
    HInL c (Term.koreList c vs [.app kseq [.inj X Srt.kitem (.var 0), .app dotk []]]) := by
  rw [Term.koreList, Term.koreList, hinL_cons]
  refine ⟨hin_app_gamma kseq_mem ?_, hinL_nil⟩
  rw [Term.koreList, Term.koreList, Term.koreList, hinL_cons, hinL_cons]
  refine ⟨hin_inj_gamma hX (by rw [Term.kore]; exact hin_var _),
    hin_app_gamma dotk_mem (by rw [Term.koreList]; exact hinL_nil), hinL_nil⟩

/-- The sort predicates' clauses apply `kseq`, `dotk` and `inj` at a pair `(X, KItem)` of
`c.subsorts` only. -/
theorem clauseG_sortPreds {fn : Fn} (hfn : fn ∈ c.sortPreds) : ∀ cl ∈ fn.clauses, ClauseG c cl := by
  have hdv : ∀ (vs : List KoreAML.Var) (b : Bool), HIn c (Term.kore c vs (.dv Srt.bool (.bool b))) := by
    intro vs b; rw [Term.kore]; exact hin_dv _
  have hvar : ∀ (vs : List KoreAML.Var), HInL c (Term.koreList c vs [.var 0]) := by
    intro vs; rw [Term.koreList, Term.koreList, hinL_cons, Term.kore]; exact ⟨hin_var _, hinL_nil⟩
  have hcl : ∀ (b : Bool) (vars : List Srt) (pats : List Term) (prio : Nat),
      (∀ vs, HInL c (Term.koreList c vs pats)) →
      ClauseG c { vars := vars, pats := pats, req := none, prio := prio
                  rhs := .dv Srt.bool (.bool b), ens := none } := by
    intro b vars pats prio hp
    refine ⟨hp, fun _ _ h => (nomatch h), fun vs => hdv vs b, fun _ _ h => (nomatch h),
      fun _ _ => (by exact hin_top), fun h => absurd rfl h⟩
  simp only [Semantics.sortPreds, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with (rfl | rfl) | ⟨X, hX, p, -, rfl⟩
  · intro cl hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    subst hcl'
    exact hcl true _ _ _ hvar
  · intro cl hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · refine hcl true _ _ _ fun vs => ?_
      rw [Term.koreList, Term.koreList, hinL_cons]
      refine ⟨hin_app_gamma kseq_mem ?_, hinL_nil⟩
      rw [Term.koreList, Term.koreList, Term.koreList, hinL_cons, hinL_cons]
      exact ⟨by rw [Term.kore]; exact hin_var _, hin_app_gamma dotk_mem (by rw [Term.koreList]; exact hinL_nil),
        hinL_nil⟩
    · exact hcl false _ _ _ hvar
  · have hX' : (X, Srt.kitem) ∈ c.subsorts := by
      unfold Semantics.subsorts
      exact List.mem_append_right _ (List.mem_map_of_mem (f := (·, Srt.kitem)) hX)
    intro cl hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · exact hcl true _ _ _ (hin_kseqPat hX')
    · exact hcl false _ _ _ hvar

/-! ## Under `coreOK` -/

/-- Under `coreOK`, every function's head is Γ's, and every clause of it has parts that apply Γ's
heads only. -/
theorem fnG_coreOK (h : c.coreOK = true) {f : Fn} (hf : f ∈ c.allFns) :
    gammaHead c f.label ∈ gammaHeads c ∧ ∀ cl ∈ f.clauses, ClauseG c cl := by
  obtain ⟨hs, hfa, -⟩ := Semantics.coreOK_parts h
  refine ⟨fnHead_mem hf, ?_⟩
  have hf' := hf
  simp only [Semantics.allFns, List.mem_append] at hf'
  rcases hf' with hu | hp
  · intro cl hcl
    have hsorted := Semantics.sortedOK_sorted hs
    simp only [Bool.and_eq_true, List.all_eq_true] at hsorted
    exact clauseG_of_sorted
      (fun _ hk => ks_fn (by rw [Semantics.allFns, List.map_append]; exact List.mem_append_left _ hk))
      (hsorted.1.2 f hu cl hcl) (.inl (Semantics.fnsNoExs_of_coreOK h f hu cl hcl))
  · exact clauseG_sortPreds hp

/-- **Under `coreOK`, every equation of every function applies Γ's heads only.** -/
theorem prioEquation_coreOK (h : c.coreOK = true) {f : Fn} (hf : f ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ f.clauses) : SentHIn c (prioEquation c f cl) :=
  have hg := fnG_coreOK h hf
  prioEquation_ghk hg.1 hg.2 (hg.2 cl hcl)

/-- Under `coreOK`, every rule has parts that apply Γ's heads only. -/
theorem ruleG_coreOK (h : c.coreOK = true) {r : Rule} (hr : r ∈ c.rules) : RuleG c r := by
  have hsorted := Semantics.sortedOK_sorted (Semantics.coreOK_parts h).1
  simp only [Bool.and_eq_true, List.all_eq_true] at hsorted
  exact ruleG_of_sorted (hsorted.2 r hr)

/-- **Under `coreOK`, every rule's axiom applies Γ's heads only.** -/
theorem prioRuleK_coreOK (h : c.coreOK = true) {r : Rule} (hr : r ∈ c.rules) : HIn c (prioRuleK c r) :=
  prioRuleK_ghk (fun _ hr' => ruleG_coreOK h hr') (ruleG_coreOK h hr)

end GHKore

end KCore
