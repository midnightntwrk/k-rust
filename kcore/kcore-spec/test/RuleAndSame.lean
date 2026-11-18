/-
  `t #And u` on a rule's right side: the reading with the ensures `t == u` and the exact reading
  give the same steps. Run from the package root: `lake env lean -j1 test/RuleAndSame.lean`.
  Kernel-checked (`decide +kernel`).

  The text's rule `L => C[t #And u]` is read as `rhs := C[t]` with `ens := t ==Int u` (off Int,
  `==K` of the two one-item K sequences). The exact reading is, in the fresh form, the rule with
  one more variable Z of the conjuncts' sort in `exs`, `rhs := C[Z]`, no `ensures` and
  `post := Z ∈ t ∧ Z ∈ u`; in the variable form (t a variable V of the rule), `rhs := C[V]`, no
  `ensures` and `post := V ∈ u`.

  - `step_fresh_int`: for a semantics whose one rule has the ensures `t ==Int u` and `\top`
    predicates, with coherent functions, `Step c x y ↔ Step cIn x y` for all configurations x, y,
    `cIn` the semantics with the rule in the fresh form (`zForm`). From `Holds.mem` and
    `sameResult` on one side and the hook of `==Int` on the other: both say that t and u evaluate
    to one Int.
  - `MlAndT.step_and_same`: the instance at the semantics for `f2-examples/mlandt.kompile.kore`
    (fixture e3-ml-rule-rhs-and-term, `go(X) => f(X) #And g(X)`) with its rule read without the
    cut (`Parse.ruleOfUncut`, `andTermsWeaker`: the reading the reader takes where its test at
    reading time fails; at this text the reader takes the cut, `andTermsCut`).
  - `step_var_k`, `MlAndC.step_and_same`: the same for the variable form and `==K`, at
    `f2-examples/mlandc.kompile.kore` (fixture e3-ml-rule-rhs-and-ctor, `c(X) => X #And a()`), its
    rule read without the cut.
-/
import KcoreSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000

open KCore

namespace RuleAndSame

open Lean Elab Command in
/-- `definition_uncut NAME from "file.kore"`: `def NAME : Definition`, the definition
`Parse.parseWith Parse.ruleOfUncut` builds from the file (a conjunction of terms on a rule's right
side read with the `ensures` of the conjuncts' equality), added as a term (not compiled). -/
elab "definition_uncut " id:ident " from " path:str : command => do
  let input ← IO.FS.readFile path.getString
  let k ← match Kore.parseDefinition input with
    | .error e => throwError "definition_uncut: {path.getString}: KORE read error {e}"
    | .ok k => pure k
  let d ← match Parse.parseWith Parse.ruleOfUncut k with
    | .ok d => pure d
    | .error r => throwError "definition_uncut: {path.getString}: refused: {r.toText}"
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDecl <| .defnDecl {
    name, levelParams := [], type := mkConst ``Definition, value := definitionExpr d,
    hints := .regular 0, safety := .safe }

/-! ## The evaluation and matching of a semantics do not read its rules -/

/-- `c` with the rules `rs`. -/
abbrev withRules (c : Semantics) (rs : List Rule) : Semantics := { c with rules := rs }

kernel_rfl sortOf_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).sortOf = c.sortOf
kernel_rfl collVal_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).collVal = c.collVal
kernel_rfl norm_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).norm = c.norm
kernel_rfl fnCover_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).fnCover = c.fnCover
kernel_rfl paramVal_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).paramVal = c.paramVal
kernel_rfl hookRes_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).hookRes = c.hookRes
kernel_rfl fnRest_withRules : ∀ (c : Semantics) (rs : List Rule), (withRules c rs).fnRest = c.fnRest

theorem wellSorted_rules {c : Semantics} {rs : List Rule} {vars : List Srt} {σ : Subst} :
    (withRules c rs).WellSorted vars σ ↔ c.WellSorted vars σ := by
  unfold Semantics.WellSorted; rw [sortOf_withRules]

/-- A configuration of `c` is one of `c` with any rules. -/
def Config.toRules {c : Semantics} (rs : List Rule) (x : Config c) : Config (withRules c rs) :=
  ⟨x.val, by rw [sortOf_withRules]; exact x.2⟩

section Transfer
variable {c : Semantics} (rs : List Rule) {σ : Subst}

theorem patVals_rules {ps : List Term} {vs : List GroundTerm} (h : PatVals c σ ps vs) :
    PatVals (withRules c rs) σ ps vs :=
  PatVals.rec (c := c) (σ := σ) (motive_1 := fun p v _ => PatVal (withRules c rs) σ p v)
    (motive_2 := fun ps vs _ => PatVals (withRules c rs) σ ps vs)
    (fun h => .var h) .dv (fun h _ ih => .ctor h ih) (fun hp _ hv ih => .hook hp ih hv)
    (fun _ ih => .inj ih) (fun hc hp _ hv ih => .coll hc hp ih (by rw [collVal_withRules]; exact hv))
    (fun _ hi ih => .as ih hi) (fun hc ho _ hv ih => .ovl hc ho ih (by rw [norm_withRules]; exact hv)) .nil (fun _ _ ih ihs => .cons ih ihs) h

theorem patVal_rules {p : Term} {v : GroundTerm} (h : PatVal c σ p v) : PatVal (withRules c rs) σ p v :=
  PatVal.rec (c := c) (σ := σ) (motive_1 := fun p v _ => PatVal (withRules c rs) σ p v)
    (motive_2 := fun ps vs _ => PatVals (withRules c rs) σ ps vs)
    (fun h => .var h) .dv (fun h _ ih => .ctor h ih) (fun hp _ hv ih => .hook hp ih hv)
    (fun _ ih => .inj ih) (fun hc hp _ hv ih => .coll hc hp ih (by rw [collVal_withRules]; exact hv))
    (fun _ hi ih => .as ih hi) (fun hc ho _ hv ih => .ovl hc ho ih (by rw [norm_withRules]; exact hv)) .nil (fun _ _ ih ihs => .cons ih ihs) h

/-- A pattern's values with the rules `rs` are those of `c`. -/
theorem patVals_rules_back {ps : List Term} {vs : List GroundTerm} (h : PatVals (withRules c rs) σ ps vs) :
    PatVals c σ ps vs :=
  patVals_rules (c := withRules c rs) c.rules h

theorem patVal_rules_back {p : Term} {v : GroundTerm} (h : PatVal (withRules c rs) σ p v) : PatVal c σ p v :=
  patVal_rules (c := withRules c rs) c.rules h

omit σ in
/-- The extensions of a substitution with the rules `rs` are those of `c`. -/
theorem extends_rules {n : Nat} {ys : List Srt} {σ σ' : Subst} :
    Extends (withRules c rs) n ys σ σ' ↔ Extends c n ys σ σ' := by
  unfold Extends; rw [sortOf_withRules]

theorem evalTerm_rules {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r) :
    EvalTerm (withRules c rs) σ t r :=
  EvalTerm.rec (c := c) (motive_1 := fun f vs r _ => Eval (withRules c rs) f vs r)
    (motive_2 := fun vs cl _ => Fails (withRules c rs) vs cl)
    (motive_3 := fun σ cl _ => ReqFails (withRules c rs) σ cl)
    (motive_4 := fun σ t r _ => EvalTerm (withRules c rs) σ t r)
    (motive_5 := fun σ ts rs' _ => EvalTerms (withRules c rs) σ ts rs')
    (motive_6 := fun n σ p b _ => Holds (withRules c rs) n σ p b)
    (motive_7 := fun σ cl _ => InstFails (withRules c rs) σ cl)
    (motive_8 := fun σ cl r _ => InstIs (withRules c rs) σ cl r)
    (fun hfn hmem hσ hmatch _ _ _ hex _ _ _ ihreq ihpre ihprio ihrhs ihens ihpost =>
      .clause hfn hmem (wellSorted_rules.mpr hσ) (patVals_rules rs hmatch) ihreq ihpre ihprio hex ihrhs ihens ihpost)
    (fun hfn _ ihnone => by
      have := Eval.rest (c := withRules c rs) hfn ihnone
      rwa [fnRest_withRules] at this)
    (fun hfn hmem hσ hmatch _ _ _ hex ht _ hw ihreq ihpre ihprio ihe =>
      .ensFails hfn hmem (wellSorted_rules.mpr hσ) (patVals_rules rs hmatch) ihreq ihpre ihprio hex ht ihe hw)
    (fun hfn hmem hσ hmatch _ _ _ hne _ _ _ _ ihreq ihpre ihprio ihrhs ihens ihpost ihall =>
      .clauseEx hfn hmem (wellSorted_rules.mpr hσ) (patVals_rules rs hmatch) ihreq ihpre ihprio hne ihrhs ihens
        ihpost (fun σ' ha hw => ihall σ' ha (wellSorted_rules.mp hw)))
    (fun hfn hmem hne hσ hmatch _ _ _ hsome _ ihreq ihpre ihprio ihall =>
      .exNone hfn hmem hne (by unfold Semantics.WellSortedAt at hσ ⊢; rw [sortOf_withRules]; exact hσ)
        (patVals_rules rs hmatch) ihreq ihpre ihprio
        (let ⟨σ', ha, hw⟩ := hsome; ⟨σ', ha, wellSorted_rules.mpr hw⟩)
        (fun σ' ha hw => ihall σ' ha (wellSorted_rules.mp hw)))
    (fun _ ih => .intro fun σ hσ hp => ih σ (by unfold Semantics.WellSortedAt at hσ ⊢; rwa [sortOf_withRules] at hσ) (patVals_rules_back rs hp))
    (fun ht _ hr ihe => .intro ht ihe hr)
    (fun _ ih => .pre ih)
    .var .dv (fun _ ih => .inj ih) (fun hk _ ih => .ctor hk ih)
    (fun hk hhk _ hh hund ih => .hook hk hhk ih (by rw [hookRes_withRules]; exact hh) hund)
    (fun hk hhk hp _ hr ih => .param hk hhk hp ih (by rw [paramVal_withRules]; exact hr))
    (fun hk hhk _ hvs _ hp ihts ihf => .call hk hhk ihts hvs ihf hp)
    (fun hk hhk _ hvs hp ih => .callUndef hk hhk ih hvs hp)
    (fun hk ho _ hnf ih => by
      have := EvalTerm.ovl (c := withRules c rs) hk ho ih (fun vs hv => by rw [fnCover_withRules]; exact hnf vs hv)
      rwa [norm_withRules] at this)
    (fun hk ho _ hvs hlo hcov _ ihts ihf => .ovlFn hk ho ihts hvs hlo (by rw [fnCover_withRules]; exact hcov) ihf)
    .nil (fun _ _ ih1 ih2 => .cons ih1 ih2)
    .top .bot (fun _ ih => .not ih) (fun _ _ ih ih' => .and ih ih') (fun _ _ ih ih' => .or ih ih')
    (fun _ _ ih ih' => .implies ih ih') (fun _ ih => .ceil ih) (fun _ _ ih ih' => .equals ih ih')
    (fun _ _ ih ih' => .mem ih ih') (fun _ ih => .exNone ih)
    (fun g _ _ hr ih ihb =>
      .exSome g ih (fun σ' he hp => ihb σ' ((extends_rules rs).mp he) (patVal_rules_back rs hp))
        (hr.trans ⟨fun ⟨σ', he, hp, hg⟩ => ⟨σ', (extends_rules rs).mpr he, patVal_rules rs hp, hg⟩,
          fun ⟨σ', he, hp, hg⟩ => ⟨σ', (extends_rules rs).mp he, patVal_rules_back rs hp, hg⟩⟩))
    (fun g _ hr ihb =>
      .ex g (fun σ' he => ihb σ' ((extends_rules rs).mp he))
        (hr.trans ⟨fun ⟨σ', he, hg⟩ => ⟨σ', (extends_rules rs).mpr he, hg⟩,
          fun ⟨σ', he, hg⟩ => ⟨σ', (extends_rules rs).mp he, hg⟩⟩))
    (fun g _ hr ihb =>
      .all g (fun σ' he => ihb σ' ((extends_rules rs).mp he))
        (hr.trans ⟨fun H σ' he => H σ' ((extends_rules rs).mp he),
          fun H σ' he => H σ' ((extends_rules rs).mpr he)⟩))
    (fun ht _ hw ihe => .ens ht ihe hw) (fun _ ih => .post ih) (fun _ ih => .rhs ih)
    (fun _ _ ihp ih => .fails ihp ih) (fun _ _ _ ihr ihe ihp => .gives ihr ihe ihp)
    h

theorem evalTerm_rules_back {t : Term} {r : Option GroundTerm} (h : EvalTerm (withRules c rs) σ t r) :
    EvalTerm c σ t r :=
  evalTerm_rules (c := withRules c rs) c.rules h


end Transfer

/-! ## A rule's shape as a decided test -/

/-- The optional term is T. -/
def optIs (o : Option Term) (T : Term) : Bool :=
  match o with
  | some e => Term.beq e T
  | none => false

theorem optIs_eq {o : Option Term} {T : Term} (h : optIs o T = true) : o = some T := by
  cases o with
  | none => cases h
  | some e => rw [Det.Term.beq_sound (show Term.beq e T = true from h)]

theorem isNone_eq {o : Option Term} (h : o.isNone = true) : o = none := by
  cases o with
  | none => rfl
  | some e => cases h

/-- A list of one rule is the list of its first. -/
theorem rules_single : ∀ {l : List Rule} (h : 0 < l.length), l.length = 1 → l = [l[0]]
  | [_], _, _ => rfl
  | [], h, _ => absurd h (by decide)
  | _ :: _ :: _, _, h1 => by simp at h1

/-! ## Replacing a subterm by a term with its results -/

mutual
  /-- T with each subterm equal to `a` replaced by `b`. -/
  def repl (a b : Term) : Term → Term
    | .app g ts => if Term.beq (.app g ts) a then b else .app g (replList a b ts)
    | .inj x y t => if Term.beq (.inj x y t) a then b else .inj x y (repl a b t)
    | .as t i => .as (repl a b t) i
    | .var i => if Term.beq (.var i) a then b else .var i
    | .dv s l => if Term.beq (.dv s l) a then b else .dv s l
    termination_by structural t => t
  def replList (a b : Term) : List Term → List Term
    | [] => []
    | t :: ts => repl a b t :: replList a b ts
    termination_by structural ts => ts
end

mutual
  /-- Where b has every result of a under σ, the term with a replaced by b has every result of
  the term. -/
  theorem evalTerm_repl {c : Semantics} {σ : Subst} {a b : Term}
      (hab : ∀ r, EvalTerm c σ a r → EvalTerm c σ b r) :
      ∀ {T : Term} {r : Option GroundTerm}, EvalTerm c σ T r → EvalTerm c σ (repl a b T) r
    | .var i, r, h => by
      rw [repl]; split
      · next hb => exact hab r (Det.Term.beq_sound hb ▸ h)
      · exact h
    | .dv s l, r, h => by
      rw [repl]; split
      · next hb => exact hab r (Det.Term.beq_sound hb ▸ h)
      · exact h
    | .inj x y t, r, h => by
      rw [repl]; split
      · next hb => exact hab r (Det.Term.beq_sound hb ▸ h)
      · cases h with
        | inj h' => exact .inj (evalTerm_repl hab h')
    | .as t i, r, h => by cases h
    | .app f ts, r, h => by
      rw [repl]; split
      · next hb => exact hab r (Det.Term.beq_sound hb ▸ h)
      · cases h with
        | ctor hk hts => exact .ctor hk (evalTerms_repl hab hts)
        | hook hk hhk hts hh hund => exact .hook hk hhk (evalTerms_repl hab hts) hh hund
        | param hk hhk hp hts hr => exact .param hk hhk hp (evalTerms_repl hab hts) hr
        | call hk hhk hts hvs hf hp => exact .call hk hhk (evalTerms_repl hab hts) hvs hf hp
        | callUndef hk hhk hts hvs hp => exact .callUndef hk hhk (evalTerms_repl hab hts) hvs hp
        | ovl hk ho hts hnf => exact .ovl hk ho (evalTerms_repl hab hts) hnf
        | ovlFn hk ho hts hvs hlo hcov hf => exact .ovlFn hk ho (evalTerms_repl hab hts) hvs hlo hcov hf
  termination_by structural T => T
  theorem evalTerms_repl {c : Semantics} {σ : Subst} {a b : Term}
      (hab : ∀ r, EvalTerm c σ a r → EvalTerm c σ b r) :
      ∀ {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
        EvalTerms c σ (replList a b ts) rs
    | [], rs, h => by cases h; exact .nil
    | t :: ts, rs, h => by
      cases h with
      | cons h1 h2 => exact .cons (evalTerm_repl hab h1) (evalTerms_repl hab h2)
  termination_by structural ts => ts
end

/-! ## `Holds` at a conjunction and at a membership of a variable -/

theorem holds_and_true {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} (h : Holds c n σ (.and p q) true) :
    Holds c n σ p true ∧ Holds c n σ q true := by
  generalize hp : Cond.and p q = P at h
  generalize hb : true = B at h
  cases h with
  | and h1 h2 =>
    cases hp
    rename_i b b'
    cases b <;> cases b' <;> first | exact ⟨h1, h2⟩ | cases hb
  | _ => cases hp

/-- A membership of a variable holds exactly where the term has the variable's value. -/
theorem holds_mem_var_true {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {i : Nat} {t : Term}
    (h : Holds c n σ (.mem s (.var i) t) true) : ∃ v, σ.lookup i = some v ∧ EvalTerm c σ t (some v) := by
  generalize hp : Cond.mem s (.var i) t = P at h
  generalize hb : true = B at h
  cases h with
  | mem h1 h2 =>
    cases hp
    rename_i r r'
    have hr := h1.var_inv
    subst hr
    cases hl : σ.lookup i with
    | none => rw [hl] at hb; cases hb
    | some v =>
      rw [hl] at hb
      cases r' with
      | none => cases hb
      | some w =>
        have he : GroundTerm.cmp v w = .eq := by simpa [sameResult] using hb.symm
        rw [GroundTerm.cmp_eq v w he]
        exact ⟨w, rfl, h2⟩
  | _ => cases hp

theorem holds_mem_var {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {i : Nat} {t : Term} {v : GroundTerm}
    (hl : σ.lookup i = some v) (ht : EvalTerm c σ t (some v)) : Holds c n σ (.mem s (.var i) t) true := by
  have h := Holds.mem (c := c) (n := n) (s := s) (EvalTerm.var (c := c) (σ := σ) (i := i)) ht
  rw [hl] at h
  have hb : ((some v).isSome && sameResult (some v) (some v)) = true := by
    simp [sameResult, GroundTerm.cmp_refl]
  exact hb ▸ h

/-! ## The hook of `==Int` -/

theorem hookRes_intEq (c : Semantics) (vs : List GroundTerm) :
    c.hookRes intEq vs = some (int2 vs fun x y => some (KCore.bool (decide (x = y)))) := by
  rw [Semantics.hookRes_of_not_silent (c := c) (f := intEq) (vs := vs) rfl, Det.hook_intEq]

/-- `t ==Int u` evaluates to `true` exactly where t and u evaluate to one Int. -/
theorem intEq_true_iff {c : Semantics} (hic : c.isCtor intEq = false) (hio : c.isOvl intEq = false)
    {σ : Subst} {t u : Term} :
    EvalTerm c σ (.app intEq [t, u]) (some (KCore.bool true)) ↔
      ∃ a : Int, EvalTerm c σ t (some (int a)) ∧ EvalTerm c σ u (some (int a)) := by
  constructor
  · intro h
    generalize hT : Term.app intEq [t, u] = T at h
    generalize hR : some (KCore.bool true) = R at h
    cases h with
    | ctor hk _ => cases hT; rw [hic] at hk; cases hk
    | hook hk hhk hts hh hund =>
      cases hT
      obtain ⟨rt, rs1, rfl, ht, hts⟩ := hts.cons_inv
      obtain ⟨ru, rs2, rfl, hu, hts⟩ := hts.cons_inv
      have := hts.nil_inv; subst this
      cases rt with
      | none => have := hund rfl; subst this; cases hR
      | some vt =>
        cases ru with
        | none => have := hund rfl; subst this; cases hR
        | some vu =>
          have hres := hh [vt, vu] rfl
          rw [hookRes_intEq] at hres
          have hres' := Option.some.inj hres
          rw [← hR] at hres'
          simp only [int2] at hres'
          cases hx : asInt vt with
          | none => rw [hx] at hres'; cases hres'
          | some x =>
            cases hy : asInt vu with
            | none => rw [hx, hy] at hres'; cases hres'
            | some y =>
              rw [hx, hy] at hres'
              have hxy : x = y := by
                have h1 : KCore.bool (decide (x = y)) = KCore.bool true := Option.some.inj hres'
                have h2 : decide (x = y) = true := by simpa [KCore.bool] using h1
                exact of_decide_eq_true h2
              subst hxy
              rw [asInt_int_inv hx] at ht
              rw [asInt_int_inv hy] at hu
              exact ⟨x, ht, hu⟩
    | param hk hhk _ _ _ => cases hT; exact absurd hhk (by decide)
    | call hk hhk _ _ _ _ => cases hT; exact absurd hhk (by decide)
    | callUndef hk hhk _ _ _ => cases hT; exact absurd hhk (by decide)
    | ovl hk ho _ => cases hT; rw [hio] at ho; cases ho
    | ovlFn hk ho => cases hT; rw [hio] at ho; cases ho
    | var => cases hT
    | dv => cases hT
    | inj _ => cases hT
  · rintro ⟨a, ht, hu⟩
    refine .hook hic (by decide) (.cons ht (.cons hu .nil)) (fun vs hvs => ?_) (fun hn => by cases hn)
    have : vs = [int a, int a] := (Option.some.inj hvs).symm
    subst this
    rw [hookRes_intEq]
    simp [int2, asInt, int, KCore.bool]

/-! ## The fresh form gives the same steps (`==Int`) -/

/-- The fresh form: Z, the variable after the rule's, in `exs`; the right side with t replaced by
Z; no `ensures`; `post := Z ∈ t ∧ Z ∈ u`. -/
def zForm (r : Rule) (t u : Term) (s : Srt) : Rule :=
  { r with vars := r.vars ++ [s], rhs := repl t (.var r.vars.length) r.rhs, ens := none,
           exs := r.exs ++ [r.vars.length],
           post := .and (.mem s (.var r.vars.length) t) (.mem s (.var r.vars.length) u) }

theorem lookup_cons_self (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lookup_cons_ne {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

section Fresh
variable {c : Semantics} (hco : CoherentAll c) (hsh : c.shapesOK = true)
  (hic : c.isCtor intEq = false) (hio : c.isOvl intEq = false)
  {r : Rule} (hrules : c.rules = [r]) {t u : Term}
  (hens : r.ens = some (.app intEq [t, u])) (hreq : r.req = none)
  (hpre : r.pre = .top) (hpost : r.post = .top)
  (hvl : ∀ i ∈ varOccs r.lhs, i < r.vars.length) (hvr : ∀ i ∈ varOccs r.rhs, i < r.vars.length)
  (hvt : ∀ i ∈ varOccs t, i < r.vars.length) (hvu : ∀ i ∈ varOccs u, i < r.vars.length)
  (hback : repl (.var r.vars.length) t (repl t (.var r.vars.length) r.rhs) = r.rhs)
include hco hsh hic hio hrules hens hreq hpre hpost hvl hvr hvt hvu hback

/-- **The reading with the ensures `t ==Int u` and the fresh form give the same steps.** -/
theorem step_fresh_int (x y : Config c) :
    Step c x y ↔ Step (withRules c [zForm r t u Srt.int]) (Config.toRules _ x) (Config.toRules _ y) := by
  constructor
  · intro h
    cases h with
    | rule r' hr' σ hσ hmatch hreq' _ heval hens' _ hprio =>
      rw [hrules, List.mem_singleton] at hr'
      subst hr'
      obtain ⟨a, hta, hua⟩ := (intEq_true_iff hic hio).mp (hens' _ hens)
      let n := r'.vars.length
      let σ' : Subst := (n, int a) :: σ
      have hl : σ'.lookup n = some (int a) := lookup_cons_self _ _ _
      have hoff : ∀ i, i < n → σ'.lookup i = σ.lookup i := fun i hi => lookup_cons_ne _ _ (by omega)
      have hagree : ∀ {T : Term}, (∀ i ∈ varOccs T, i < n) → ∀ {res}, EvalTerm c σ T res → EvalTerm c σ' T res :=
        fun hT _ he => Exec.EvalTerm.congr he (fun i hi => (hoff i (hT i hi)).symm)
      have hta' := hagree hvt hta
      have hua' := hagree hvu hua
      have hvar : EvalTerm c σ' (.var n) (some (int a)) := by
        have h := EvalTerm.var (c := c) (σ := σ') (i := n); rwa [hl] at h
      refine .rule (zForm r' t u Srt.int) (List.mem_singleton.mpr rfl) σ' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine wellSorted_rules.mpr fun i s hi => ?_
        change (r'.vars ++ [Srt.int])[i]? = some s at hi
        by_cases hlt : i < n
        · rw [List.getElem?_append_left hlt] at hi
          obtain ⟨v, hv, hs⟩ := hσ i s hi
          exact ⟨v, (hoff i hlt).trans hv, hs⟩
        · have hin : i = n := by
            have := (List.getElem?_eq_some_iff.mp hi).1
            simp at this; omega
          subst hin
          have hi' : (r'.vars ++ [Srt.int])[r'.vars.length]? = some s := hi
          have : s = Srt.int := by simp at hi'; first | exact hi'.symm | exact hi'
          subst this
          exact ⟨int a, hl, sortOf_int a⟩
      · exact patVal_rules _ (PatVal.congr_varsRH hmatch (fun j hj => hoff j (hvl j hj)))
      · intro q hq; rw [show (zForm r' t u Srt.int).req = r'.req from rfl, hreq] at hq; cases hq
      · rw [show (zForm r' t u Srt.int).pre = r'.pre from rfl, hpre]; exact .top
      · exact evalTerm_rules _ (evalTerm_repl (fun res he => by
          have := Det.evalTerm_det hco he hta'; subst this; exact hvar) (hagree hvr heval))
      · intro q hq; cases hq
      · exact Holds.and (b := true) (b' := true) (holds_mem_var hl (evalTerm_rules _ hta'))
          (holds_mem_var hl (evalTerm_rules _ hua'))
      · intro r'' hr'' hlt
        have : r'' = zForm r' t u Srt.int := List.mem_singleton.mp hr''
        subst this
        exact absurd hlt (Nat.lt_irrefl _)
  · intro h
    cases h with
    | rule r' hr' σ hσ hmatch hreq' _ heval _ hpost' hprio =>
      have hr'' : r' = zForm r t u Srt.int := List.mem_singleton.mp hr'
      subst hr''
      let n := r.vars.length
      obtain ⟨h1, h2⟩ := holds_and_true hpost'
      obtain ⟨v, hv, htv⟩ := holds_mem_var_true h1
      obtain ⟨w, hw, huw⟩ := holds_mem_var_true h2
      rw [hv] at hw; cases hw
      have hσ0 := wellSorted_rules.mp hσ
      obtain ⟨v', hv', hsv⟩ := hσ0 n Srt.int (by
        show (r.vars ++ [Srt.int])[r.vars.length]? = some Srt.int
        simp)
      rw [hv] at hv'; cases hv'
      obtain ⟨a, rfl⟩ := shape_int hsh hsv
      have htv' := evalTerm_rules_back _ htv
      have huw' := evalTerm_rules_back _ huw
      refine .rule r (by rw [hrules]; exact List.mem_singleton.mpr rfl) σ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro i s hi
        have hlt : i < r.vars.length := (List.getElem?_eq_some_iff.mp hi).1
        exact hσ0 i s (by show (r.vars ++ [Srt.int])[i]? = some s; rw [List.getElem?_append_left hlt]; exact hi)
      · exact patVal_rules_back _ hmatch
      · intro q hq; rw [hreq] at hq; cases hq
      · rw [hpre]; exact .top
      · have := evalTerm_repl (a := .var n) (b := t) (fun res he => by
          have := he.var_inv; rw [hv] at this; subst this; exact htv') (evalTerm_rules_back _ heval)
        rw [show (zForm r t u Srt.int).rhs = repl t (.var n) r.rhs from rfl, hback] at this
        exact this
      · intro q hq
        rw [hens] at hq; cases hq
        exact (intEq_true_iff hic hio).mpr ⟨a, htv', huw'⟩
      · rw [hpost]; exact .top
      · intro r'' hr'' hlt
        rw [hrules, List.mem_singleton] at hr''
        subst hr''
        exact absurd hlt (Nat.lt_irrefl _)

end Fresh

/-! ## The instance: `go(X) => f(X) #And g(X)` -/

namespace MlAndT

definition_uncut defn from "f2-examples/mlandt.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

/-- The text's one rule, read without the cut. -/
noncomputable abbrev r : Rule := c.rules[0]'(by decide +kernel)
def t : Term := .app 388 [.var 0]
def u : Term := .app 389 [.var 0]

theorem names_ok : c.symName 388 = "Lblf" ∧ c.symName 389 = "Lblg" := by decide +kernel

/-- The rule read without the cut: three variables, the ensures `f(X) ==Int g(X)`, `\top` predicates, no
existential variable, and `f(X)` on its right side. -/
theorem rule_shape_dec : c.rules.length = 1 ∧ r.vars = [Srt.int, Srt.k, Srt.counter] ∧
    optIs r.ens (.app intEq [t, u]) = true ∧ r.req.isNone = true ∧ r.pre.isTop = true ∧
    r.post.isTop = true ∧ r.exs = [] ∧
    (varOccs r.lhs).all (· < 3) = true ∧ (varOccs r.rhs).all (· < 3) = true ∧
    Term.beq (repl (.var 3) t (repl t (.var 3) r.rhs)) r.rhs = true ∧
    Term.beq (repl t (.var 3) r.rhs) r.rhs = false := by
  decide +kernel

theorem rule_shape : c.rules = [r] ∧ r.vars = [Srt.int, Srt.k, Srt.counter] ∧
    r.ens = some (.app intEq [t, u]) ∧ r.req = none ∧ r.pre = .top ∧ r.post = .top ∧ r.exs = [] ∧
    (varOccs r.lhs).all (· < 3) = true ∧ (varOccs r.rhs).all (· < 3) = true ∧
    repl (.var 3) t (repl t (.var 3) r.rhs) = r.rhs ∧ Term.beq (repl t (.var 3) r.rhs) r.rhs = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := rule_shape_dec
  exact ⟨rules_single _ h1, h2, optIs_eq h3, isNone_eq h4, Cond.eq_top_of_isTop h5, Cond.eq_top_of_isTop h6,
    h7, h8, h9, Det.Term.beq_sound h10, h11⟩

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)
theorem shapes : c.shapesOK = true := by decide +kernel

/-- The definition with the rule in the fresh form. -/
noncomputable abbrev cIn : Semantics := withRules c [zForm r t u Srt.int]

/-- **The weakening and the exact reading give the same steps** at e3-ml-rule-rhs-and-term. -/
theorem step_and_same (x y : Config c) :
    Step c x y ↔ Step cIn (Config.toRules _ x) (Config.toRules _ y) := by
  obtain ⟨hrules, hvars, hens, hreq, hpre, hpost, -, hvl, hvr, hback, -⟩ := rule_shape
  have hn : r.vars.length = 3 := by rw [hvars]; rfl
  exact step_fresh_int coherent shapes (by decide +kernel) (by decide +kernel) hrules hens hreq hpre hpost
    (fun i hi => by rw [hn]; simpa using List.all_eq_true.mp hvl i hi)
    (fun i hi => by rw [hn]; simpa using List.all_eq_true.mp hvr i hi)
    (fun i hi => by rw [hn]; simp [t, varOccs, varOccsList] at hi; omega)
    (fun i hi => by rw [hn]; simp [u, varOccs, varOccsList] at hi; omega)
    (by rw [hn]; exact hback) x y

end MlAndT

/-! ## The variable form gives the same steps (`==K`) -/

theorem hookRes_kEq (c : Semantics) (v w : GroundTerm) :
    c.hookRes kEq [v, w] = some (some (KCore.bool (GroundTerm.cmp v w == .eq))) := by
  rw [Semantics.hookRes_of_not_silent (c := c) (f := kEq) (vs := [v, w]) rfl, Det.hook_kEq]

/-- `A ==K B` evaluates to `true` exactly where A and B evaluate to one value. -/
theorem kEq_true_iff {c : Semantics} (hic : c.isCtor kEq = false) (hio : c.isOvl kEq = false)
    {σ : Subst} {A B : Term} :
    EvalTerm c σ (.app kEq [A, B]) (some (KCore.bool true)) ↔
      ∃ v, EvalTerm c σ A (some v) ∧ EvalTerm c σ B (some v) := by
  constructor
  · intro h
    generalize hT : Term.app kEq [A, B] = T at h
    generalize hR : some (KCore.bool true) = R at h
    cases h with
    | ctor hk _ => cases hT; rw [hic] at hk; cases hk
    | hook hk hhk hts hh hund =>
      cases hT
      obtain ⟨rt, rs1, rfl, ht, hts⟩ := hts.cons_inv
      obtain ⟨ru, rs2, rfl, hu, hts⟩ := hts.cons_inv
      have := hts.nil_inv; subst this
      cases rt with
      | none => have := hund rfl; subst this; cases hR
      | some vt =>
        cases ru with
        | none => have := hund rfl; subst this; cases hR
        | some vu =>
          have hres := hh [vt, vu] rfl
          rw [hookRes_kEq, ← hR] at hres
          have h1 : KCore.bool (GroundTerm.cmp vt vu == .eq) = KCore.bool true :=
            Option.some.inj (Option.some.inj hres)
          have h2 : (GroundTerm.cmp vt vu == .eq) = true := by simpa [KCore.bool] using h1
          have h3 : GroundTerm.cmp vt vu = .eq := by simpa using h2
          rw [GroundTerm.cmp_eq vt vu h3] at ht
          exact ⟨vu, ht, hu⟩
    | param hk hhk _ _ _ => cases hT; exact absurd hhk (by decide)
    | call hk hhk _ _ _ _ => cases hT; exact absurd hhk (by decide)
    | callUndef hk hhk _ _ _ => cases hT; exact absurd hhk (by decide)
    | ovl hk ho _ => cases hT; rw [hio] at ho; cases ho
    | ovlFn hk ho => cases hT; rw [hio] at ho; cases ho
    | var => cases hT
    | dv => cases hT
    | inj _ => cases hT
  · rintro ⟨v, hA, hB⟩
    refine .hook hic (by decide) (.cons hA (.cons hB .nil)) (fun vs hvs => ?_) (fun hn => by cases hn)
    have : vs = [v, v] := (Option.some.inj hvs).symm
    subst this
    rw [hookRes_kEq, GroundTerm.cmp_refl]
    rfl

/-- The one-item K sequence of a term of sort s: `kseq(inj{s,KItem}(T), dotk)`. -/
def wrapK (s : Srt) (T : Term) : Term := .app kseq [.inj s Srt.kitem T, .app dotk []]

/-- The one-item K sequence of T evaluates to the sequence of T's value injected. -/
theorem wrapK_eval {c : Semantics} {σ : Subst} {s : Srt} {T : Term} {W : GroundTerm} :
    EvalTerm c σ (wrapK s T) (some W) ↔
      ∃ v, EvalTerm c σ T (some v) ∧ W = .ctor kseq [injNormal s Srt.kitem v, .ctor dotk []] := by
  constructor
  · intro h
    obtain ⟨rs, hts, hr⟩ := EvalTerm.ctor_inv Det.isCtor_kseq h
    obtain ⟨r1, rs1, rfl, h1, hts⟩ := hts.cons_inv
    obtain ⟨r2, rs2, rfl, h2, hts⟩ := hts.cons_inv
    have := hts.nil_inv; subst this
    obtain ⟨r', hT, rfl⟩ := h1.inj_inv
    obtain ⟨rs0, hts0, rfl⟩ := EvalTerm.ctor_inv Det.isCtor_dotk h2
    have := hts0.nil_inv; subst this
    cases r' with
    | none => cases hr
    | some v => exact ⟨v, hT, Option.some.inj hr⟩
  · rintro ⟨v, hT, rfl⟩
    exact EvalTerm.ctor Det.isCtor_kseq (.cons (.inj hT) (.cons (.ctor Det.isCtor_dotk .nil) .nil))

/-- The variable form: the right side as it is (it holds the variable V at the position), no
`ensures`, `post := V ∈ U`. -/
def vForm (r : Rule) (v0 : Nat) (U : Term) (s : Srt) : Rule :=
  { r with ens := none, post := .mem s (.var v0) U }

section VarForm
variable {c : Semantics} (hg : Faithful.genWf c = true) [OvlOK c]
  (hic : c.isCtor kEq = false) (hio : c.isOvl kEq = false)
  {r : Rule} (hrules : c.rules = [r]) {v0 : Nat} {U : Term} {s : Srt}
  (hens : r.ens = some (.app kEq [wrapK s (.var v0), wrapK s U])) (hreq : r.req = none)
  (hpre : r.pre = .top) (hpost : r.post = .top) (hv0 : r.vars[v0]? = some s)
  (hU : ∀ (σ : Subst) (w : GroundTerm), EvalTerm c σ U (some w) → c.sortOf w = some s)
include hg hic hio hrules hens hreq hpre hpost hv0 hU

/-- **The reading with the ensures `V ==K U` (of one-item K sequences) and the variable form give
the same steps.** -/
theorem step_var_k (x y : Config c) :
    Step c x y ↔ Step (withRules c [vForm r v0 U s]) (Config.toRules _ x) (Config.toRules _ y) := by
  constructor
  · intro h
    cases h with
    | rule r' hr' σ hσ hmatch hreq' _ heval hens' _ hprio =>
      rw [hrules, List.mem_singleton] at hr'
      subst hr'
      obtain ⟨W, hA, hB⟩ := (kEq_true_iff hic hio).mp (hens' _ hens)
      obtain ⟨a, ha, rfl⟩ := wrapK_eval.mp hA
      obtain ⟨b, hb, hab⟩ := wrapK_eval.mp hB
      have hla := ha.var_inv
      obtain ⟨a', hla', hsa⟩ := hσ v0 s hv0
      rw [hla'] at hla; cases hla
      have hinj : injNormal s Srt.kitem a = injNormal s Srt.kitem b := by
        injection hab with _ h; injection h with h1 _ <;> first | exact h1 | done
      have : a = b := Faithful.injNormal_inj hg hsa (hU σ b hb) hinj
      subst this
      refine .rule (vForm r' v0 U s) (List.mem_singleton.mpr rfl) σ (wellSorted_rules.mpr hσ)
        (patVal_rules _ hmatch) ?_ ?_ (evalTerm_rules _ heval) (fun q hq => by cases hq)
        (holds_mem_var hla' (evalTerm_rules _ hb)) ?_
      · intro q hq; rw [show (vForm r' v0 U s).req = r'.req from rfl, hreq] at hq; cases hq
      · rw [show (vForm r' v0 U s).pre = r'.pre from rfl, hpre]; exact .top
      · intro r'' hr'' hlt
        have : r'' = vForm r' v0 U s := List.mem_singleton.mp hr''
        subst this
        exact absurd hlt (Nat.lt_irrefl _)
  · intro h
    cases h with
    | rule r' hr' σ hσ hmatch hreq' _ heval _ hpost' hprio =>
      have hr'' : r' = vForm r v0 U s := List.mem_singleton.mp hr'
      subst hr''
      obtain ⟨v, hv, hUv⟩ := holds_mem_var_true hpost'
      have hUv' := evalTerm_rules_back _ hUv
      have hvar : EvalTerm c σ (.var v0) (some v) := by
        have h := EvalTerm.var (c := c) (σ := σ) (i := v0); rwa [hv] at h
      refine .rule r (by rw [hrules]; exact List.mem_singleton.mpr rfl) σ (wellSorted_rules.mp hσ)
        (patVal_rules_back _ hmatch) ?_ ?_ (evalTerm_rules_back _ heval) ?_ ?_ ?_
      · intro q hq; rw [hreq] at hq; cases hq
      · rw [hpre]; exact .top
      · intro q hq
        rw [hens] at hq; cases hq
        exact (kEq_true_iff hic hio).mpr ⟨_, wrapK_eval.mpr ⟨v, hvar, rfl⟩, wrapK_eval.mpr ⟨v, hUv', rfl⟩⟩
      · rw [hpost]; exact .top
      · intro r'' hr'' hlt
        rw [hrules, List.mem_singleton] at hr''
        subst hr''
        exact absurd hlt (Nat.lt_irrefl _)

end VarForm

/-! ## The instance: `c(X) => X #And a()` -/

namespace MlAndC

definition_uncut defn from "f2-examples/mlandc.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

/-- The text's one rule, read without the cut. -/
noncomputable abbrev r : Rule := c.rules[0]'(by decide +kernel)
def exp : Srt := 32
def a : Sym := 385

theorem names_ok : c.symName a = "Lbla" ∧ c.sortName exp = "Exp" := by decide +kernel

/-- The rule read without the cut: X of Exp its first variable, the ensures `X ==K a()` of one-item K
sequences, `\top` predicates, no existential variable. -/
theorem rule_shape_dec : c.rules.length = 1 ∧ r.vars[0]? = some exp ∧
    optIs r.ens (.app kEq [wrapK exp (.var 0), wrapK exp (.app a [])]) = true ∧ r.req.isNone = true ∧
    r.pre.isTop = true ∧ r.post.isTop = true ∧ r.exs = [] := by
  decide +kernel

theorem rule_shape : c.rules = [r] ∧ r.vars[0]? = some exp ∧
    r.ens = some (.app kEq [wrapK exp (.var 0), wrapK exp (.app a [])]) ∧ r.req = none ∧
    r.pre = .top ∧ r.post = .top ∧ r.exs = [] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rule_shape_dec
  exact ⟨rules_single _ h1, h2, optIs_eq h3, isNone_eq h4, Cond.eq_top_of_isTop h5, Cond.eq_top_of_isTop h6, h7⟩

theorem coreOK : c.coreOK = true := by decide_cheap

/-- `a()` evaluates to the value `a` of Exp. -/
theorem a_sort (σ : Subst) (w : GroundTerm) (h : EvalTerm c σ (.app a []) (some w)) : c.sortOf w = some exp := by
  obtain ⟨rs, hts, hr⟩ := EvalTerm.ctor_inv (by decide +kernel) h
  have := hts.nil_inv; subst this
  have : w = .ctor a [] := (Option.some.inj hr)
  subst this
  decide +kernel

/-- The definition with the rule in the variable form. -/
noncomputable abbrev cIn : Semantics := withRules c [vForm r 0 (.app a []) exp]

/-- **The weakening and the exact reading give the same steps** at e3-ml-rule-rhs-and-ctor. -/
theorem step_and_same (x y : Config c) :
    Step c x y ↔ Step cIn (Config.toRules _ x) (Config.toRules _ y) := by
  obtain ⟨hrules, hv0, hens, hreq, hpre, hpost, -⟩ := rule_shape
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  exact step_var_k hg (by decide +kernel) (by decide +kernel) hrules hens hreq hpre hpost hv0 a_sort x y

end MlAndC

end RuleAndSame

#print axioms RuleAndSame.step_fresh_int
#print axioms RuleAndSame.MlAndT.step_and_same
#print axioms RuleAndSame.step_var_k
#print axioms RuleAndSame.MlAndC.step_and_same
