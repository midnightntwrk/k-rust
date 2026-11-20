/-
  The statements beside the pinned theorems for a semantics whose clauses are asked CN-4's bodies
  (`sortedOKCl`), at a function with a clause whose variable is of a sort without a value and held
  by the `ensures` only. Run from the package root: `lake env lean test/OpenClausePins.lean`.
  Kernel-checked (`decide +kernel`).

  The semantics `c3` is test/RightHeldStep.lean's: the reader's for `f2-examples/opencl.kompile.kore`
  (`opencl.k`: Int, Bool, a sort S with the generators `a` and `c(Empty)`, Empty without a
  generator, the total predicate `isC`, the function `g(Int)` with `g(_) => 0 [owise]`, the rule
  `<k> go => g(f()) </k>`), with `f` made a function of the clauses
  - `clYE`, `f() => 0 ensures isC(c(Y:Empty))`: Y is of Empty, which no constructor has as its
    result, and neither the patterns nor the conditions hold it (`rightValued` fails);
  - `clOne`, `f() => 1`, at the same priority.
  `c3` is `coreOK` (`clauseSorted` asks of Y only that it occur in the clause), and `sortedOKCl`. No clause of `c3` has `needsWitness`, so the hypotheses on the
  conditions (`CondDecided`) hold with nothing assumed.

  The rule steps `<k> go </k>` to `<k> 0 </k>` (`f()` is `1` by `clOne`, `g(1)` is `0`): `stepGo`.
  - `famEx_closedCl` at `stepGo`: in every model of `Γc c3`, the step's instances are `<k> 0 </k>`.
  - `fnModel_ofCl` at `c3` (`FnTerminates`, `ClausesAgree`, `MatchIndependent` shown by hand: `clYE`
    applies under no substitution, no value having sort Empty), and `FnHyp c3` by hand, though
    `rightValued` fails, with `fnModel_of_fnHypCl` at it.
  - `complete_atCl` at `<k> go </k>`: with the step's closure, in every model of `Γc c3`, every
    successor is `<k> 0 </k>`.
  - The pinned statements at `c3`, which meets `coreOK`: `famEx_closed` and `sound_at` at `stepGo`,
    `stepDecided_of_fnHyp` and `complete_at` at `<k> go </k>`, `fnModel_of_fnHyp`, `consistent_of`,
    `sound_hyp` and `exact_hyp`.
  - `c3W`, `c3` with a third clause `f() => 1 requires H ==Int 0` that needs a witness and has one
    (H := 0): `coreOK`, and the pinned `sound_at`, `famEx_closed`, `complete_at` with the clauses'
    hypothesis `hc` proved from the witness, not from the absence of such clauses.
  - `c5`, `c3` with `clOne` of a larger priority than `clYE`: `clYE` is among `lowerClauses`, `f()`
    has no result, the value model is a model (`hypModel_ofCl`), and `exclusion_iffCl` is
    instantiated at `clYE`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenClausePinsTest

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the clauses and the rule name. -/
example : c.symName 391 = "Lblf" ∧ c.symName 389 = "Lblg" ∧ c.symName 390 = "LblisC" ∧
    c.symName 387 = "Lblc" ∧ c.symName 388 = "Lblgo" ∧ c.symName 384 = "Lbl'-LT-'k'-GT-'" ∧
    c.sortName 32 = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-- `f() => 0 ensures isC(c(Y:Empty))` -/
def clYE : Clause :=
  { vars := [33], pats := [], req := none, rhs := .dv Srt.int (.int 0),
    ens := some (.app 390 [.app 387 [.var 0]]) }
/-- `f() => 1` -/
def clOne : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.int (.int 1), ens := none }

/-- `f` with the clauses `clYE` and `clOne`. -/
def fF : Fn := { label := 391, args := [], result := Srt.int, clauses := [clYE, clOne] }

/-- `c` with `f` a function of the clauses `clYE` and `clOne`. -/
noncomputable def c3 : Semantics := { c with fns := c.fns ++ [fF], params := c.params.filter (·.sig.name != 391) }

/-- Empty is the result of no constructor and not `valued`; `clYE`'s variable is outside its
patterns and conditions, so `rightValued` fails; `sortedOK` and `coreOK` hold at `c3`. -/
theorem shape : c3.ctorSigs.all (·.result != 33) = true ∧ c3.valued 33 = false ∧ clYE.leftVars = [] ∧
    c3.rightValued = false ∧ c3.sortedOK = true ∧ c3.coreOK = true := by
  decide_cheap

/-- No clause of a function of `c3` has an existential variable or a right side's predicate other
than `\top`. -/
theorem plain3 : ∀ fn ∈ c3.fns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top :=
  fun fn hfn => Semantics.sortedOK_plainCl_of_noExs shape.2.2.2.2.1 (Semantics.fnsNoExs_of_all (by decide +kernel)) fn (List.mem_append_left _ hfn)

/-- What the lemmas ask of `c3`, decided, and no clause of `c3` needs a witness. -/
theorem decided : c3.sortedOKCl = true ∧ c3.srReady = true ∧ c3.ovls = [] ∧
    c3.subsorts.all (fun p => p.1 != p.2) = true ∧ c3.faithCoreOK = true ∧ Faithful.patHooksApart c3 = true ∧
    c3.overloadsOK = true ∧ (∀ fn ∈ c3.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c3 = false) := by
  decide_cheap

/-- `coreOK`'s conjuncts other than `sortedOK` hold at `c3`. -/
example : c3.faithCoreOK = true ∧ c3.predsApart = true ∧ c3.idsOK = true ∧
    c3.overloadsOK = true := by
  decide_cheap

instance ovl3 : OvlOK c3 := OvlOK.of_nil decided.2.2.1 decided.2.2.2.1

/-- `c3`'s rules bind their variables in their left sides. -/
theorem rulesBind3 : ∀ r ∈ c3.rules, binds r.vars.length (varOccs r.lhs) = true := by
  decide +kernel

theorem noWit {fn : Fn} (hfn : fn ∈ c3.fns) {cl : Clause} (hcl : cl ∈ fn.clauses) (hw : cl.needsWitness c3 = true) :
    False := by
  rw [decided.2.2.2.2.2.2.2 fn hfn cl hcl] at hw; cases hw

/-- Each function of `c3` is the one `lookupFn` finds under its label. -/
theorem lookup3 {fn : Fn} (hfn : fn ∈ c3.fns) : c3.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label (sortCtx_of_allCl decided.1 decided.2.1 (OvlOK.ovlCase ovl3)).nodupFns (List.mem_append_left _ hfn)

/-! ## The step `<k> go </k>` to `<k> 0 </k>` -/

/-- `g`, the text's function, with its one clause `g(_) => 0`. -/
noncomputable def gF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clG : Clause := gF.clauses[0]'(by decide +kernel)

theorem gF_mem : gF ∈ c3.fns := List.mem_append_left _ (List.getElem_mem _)
theorem gF_shape : gF.label = 389 ∧ gF.clauses.length = 1 ∧ clG.vars = [Srt.int] := by decide +kernel
theorem clG_pats : clG.pats = [.var 0] := by rfl
theorem clG_req : clG.req = none := by rfl
theorem clG_rhs : clG.rhs = .dv Srt.int (.int 0) := by rfl
theorem clG_ens : clG.ens = none := by rfl
theorem clG_mem : clG ∈ gF.clauses := List.getElem_mem _

theorem fF_mem : fF ∈ c3.fns := List.mem_append_right _ (List.mem_singleton_self _)

/-- `f()` is `1`: `clOne` applies, `clYE` is of the same priority. -/
theorem evalF : Eval c3 391 [] (some (.dv Srt.int (.int 1))) :=
  Eval.clause (cl := clOne) (σ := []) (lookup3 fF_mem) (List.Mem.tail _ (List.Mem.head _))
    (fun i s h => by simp [clOne] at h) .nil (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [clYE, clOne] at hlt)
    rfl .dv (fun t h => by cases h) .top

/-- `g(1)` is `0`: its one clause applies. -/
theorem evalG : Eval c3 389 [.dv Srt.int (.int 1)] (some (.dv Srt.int (.int 0))) := by
  have hfn : c3.lookupFn 389 = some gF := gF_shape.1 ▸ lookup3 gF_mem
  refine Eval.clause (σ := [(0, .dv Srt.int (.int 1))]) hfn clG_mem (fun i s hs => ?_) ?_
    (fun t ht => by rw [clG_req] at ht; cases ht) (Clause.holds_preTop (by rfl) _) (fun cl' hcl' _ hlt => ?_)
    (plain3 gF gF_mem _ clG_mem).1 ?_
    (fun t ht => by rw [clG_ens] at ht; cases ht) (Clause.holds_postTop (plain3 gF gF_mem _ clG_mem).2 _)
  · rw [gF_shape.2.2] at hs
    cases i with
    | zero => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | succ i => simp at hs
  · rw [clG_pats]; exact .cons (.var rfl) .nil
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcl'
    have hj0 : j = 0 := by have := gF_shape.2.1; omega
    subst hj0
    exact absurd hlt (Nat.lt_irrefl _)
  · rw [clG_rhs]; exact .dv

/-- The rule `<k> go => g(f()) </k>`, with its one variable, the counter cell. -/
noncomputable def r3 : Rule := c3.rules[0]'(by decide +kernel)

theorem r3_mem : r3 ∈ c3.rules := List.getElem_mem _
theorem r3_shape : c3.rules.length = 1 ∧ r3.vars = [19] ∧ r3.req = none ∧ r3.ens = none ∧ r3.exs = [] := by
  decide +kernel
theorem r3_lhs : r3.lhs = .app topLabel [.app 384 [.app kseq [.app 388 [], .app dotk []]], .var 0] := by rfl
theorem r3_rhs : r3.rhs =
    .app topLabel [.app 384 [.app kseq [.inj Srt.int Srt.kitem (.app 389 [.app 391 []]), .app dotk []]], .var 0] := by
  rfl
theorem r3_pre : r3.pre = .top := by rfl
theorem r3_post : r3.post = .top := by rfl

def counter : GroundTerm := .ctor counterLabel [.dv Srt.int (.int 0)]
def cfg (k : GroundTerm) : GroundTerm := .ctor topLabel [.ctor 384 [.ctor kseq [k, .ctor dotk []]], counter]

/-- `<k> go </k>` -/
noncomputable def Go : Config c3 := ⟨cfg (.ctor 388 []), by decide +kernel⟩
/-- `<k> 0 </k>` -/
noncomputable def Zero : Config c3 := ⟨cfg (injNormal Srt.int Srt.kitem (.dv Srt.int (.int 0))), by decide +kernel⟩

def σ3 : Subst := [(0, counter)]

theorem allSome_some : ∀ vs : List GroundTerm, allSome (vs.map some) = some vs
  | [] => rfl
  | v :: vs => by simp only [List.map_cons, allSome, Option.bind_some, allSome_some vs, Option.map_some]

/-- A constructor applied to terms with results has the constructor term as its result. -/
theorem evalCtor {σ : Subst} {f : Sym} {ts : List Term} {vs : List GroundTerm} (h : c3.isCtor f = true)
    (hts : EvalTerms c3 σ ts (vs.map some)) : EvalTerm c3 σ (.app f ts) (some (.ctor f vs)) := by
  have := EvalTerm.ctor h hts
  rwa [allSome_some, Option.map_some] at this

theorem isCtors : c3.isCtor topLabel = true ∧ c3.isCtor 384 = true ∧ c3.isCtor kseq = true ∧
    c3.isCtor dotk = true ∧ c3.isCtor 388 = true := by decide +kernel

theorem isFns : c3.isCtor 389 = false ∧ isHook 389 = false ∧ c3.isParam 389 = false ∧
    c3.isCtor 391 = false ∧ isHook 391 = false ∧ c3.isParam 391 = false := by decide +kernel

theorem patGo : PatVal c3 σ3 r3.lhs Go.val := by
  obtain ⟨h71, h380, hks, hdk, h384⟩ := isCtors
  rw [r3_lhs]
  exact .ctor h71 (.cons (.ctor h380 (.cons (.ctor hks (.cons (.ctor h384 .nil) (.cons (.ctor hdk .nil) .nil))) .nil))
    (.cons (.var rfl) .nil))

theorem evalRhs : EvalTerm c3 σ3 r3.rhs (some Zero.val) := by
  obtain ⟨h71, h380, hks, hdk, -⟩ := isCtors
  obtain ⟨hcg, hhg, hpg, hcf, hhf, hpf⟩ := isFns
  have hf : EvalTerm c3 σ3 (.app 391 []) (some (.dv Srt.int (.int 1))) :=
    .call hcf hhf .nil rfl evalF hpf
  have hg : EvalTerm c3 σ3 (.app 389 [.app 391 []]) (some (.dv Srt.int (.int 0))) :=
    .call hcg hhg (.cons hf .nil) rfl evalG hpg
  have hi : EvalTerm c3 σ3 (.inj Srt.int Srt.kitem (.app 389 [.app 391 []]))
      (some (injNormal Srt.int Srt.kitem (.dv Srt.int (.int 0)))) := .inj hg
  have hd : EvalTerm c3 σ3 (.app dotk []) (some (.ctor dotk [])) := evalCtor (vs := []) hdk .nil
  have hk := evalCtor (vs := [_, _]) hks (.cons hi (.cons hd .nil))
  have hc := evalCtor (vs := [_]) h380 (.cons hk .nil)
  have hv : EvalTerm c3 σ3 (.var 0) (some counter) := .var
  rw [r3_rhs]
  exact evalCtor (vs := [_, _]) h71 (.cons hc (.cons hv .nil))

/-- **The rule steps `<k> go </k>` to `<k> 0 </k>`.** -/
theorem stepGo : StepBy c3 r3 σ3 Go Zero := by
  obtain ⟨hlen, hvars, hreq, hens, -⟩ := r3_shape
  refine ⟨r3_mem, fun i s hs => ?_, patGo, fun t ht => (by rw [hreq] at ht; cases ht), (by rw [r3_pre]; exact .top),
    evalRhs, fun t ht => (by rw [hens] at ht; cases ht), (by rw [r3_post]; exact .top), fun r' hr' hlt => ?_⟩
  · rw [hvars] at hs
    cases i with
    | zero => cases hs; exact ⟨counter, rfl, by decide +kernel⟩
    | succ i => simp at hs
  · have : r' = r3 := by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr'
      have hj0 : j = 0 := by omega
      subst hj0
      rfl
    subst this
    exact absurd hlt (Nat.lt_irrefl _)

/-! ## `famEx_closed` -/

/-- **`famEx_closedCl` at `stepGo`**: in every model of `Γc c3`, the instances of the step are
`<k> 0 </k>`, nothing assumed (no clause needs a witness). -/
example : Faithful.Γc c3 ⊧ (Faithful.famEx c3 r3 σ3 ≡ den c3 Zero.val) :=
  Faithful.famEx_closedCl (hpreTop := by decide +kernel) c3 decided.1 decided.2.1 decided.2.2.2.2.1 decided.2.2.2.2.2.1 decided.2.2.2.2.2.2.1
    stepGo r3_shape.2.2.2.2 (Cond.eq_top_of_isTop (by decide +kernel)) (fun _ hfn _ hcl hw => (noWit hfn hcl hw).elim)

/-- info: 'KCore.Faithful.famEx_closedCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Faithful.famEx_closedCl

/-! ## `fnModel_of_fnHyp` -/

/-- The text's functions (`g`, `isC`): each clause's patterns bind its variables, it has no
`requires` and no `ensures`, and its right side is a literal; two of their clauses are of different
priorities, neither `aside`. -/
theorem textFns : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true ∧
    cl.req = none ∧ cl.ens = none ∧ (match cl.rhs with | .dv _ _ => true | _ => false) = true := by
  decide +kernel

/-- Each clause of the text's functions has the precondition `.top`. -/
theorem textPre : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.pre = .top :=
  fun fn hfn cl hcl =>
    Cond.eq_top_of_isTop ((by decide +kernel : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.pre.isTop = true) fn hfn cl hcl)

theorem textPairs : ∀ fn ∈ c.fns,
    (pairs fn.clauses).all (fun p => p.1.prio != p.2.prio && !p.1.aside && !p.2.aside) = true := by
  decide +kernel

theorem sortsOf_nil3 {vs : List GroundTerm} (h : c3.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [Semantics.sortsOf] at h; split at h <;> cases h

/-- **The functions of `c3` terminate**: `g` and `isC` by `eval_result` (each clause applies or
fails); `f()` is `1` by `clOne`. -/
theorem fnTerminates3 : FnTerminates c3 := by
  intro fn hfn vs hvs
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF] from hfn) with hfn' | hfn'
  · refine eval_result (lookup3 hfn) (plain3 fn hfn) (fun cl hcl => (textFns fn hfn' cl hcl).1)
      (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(textFns fn hfn' cl hcl).2.1] at ht; cases ht), true,
        Clause.holds_preTop (textPre fn hfn' cl hcl) σ⟩) (fun cl hcl _ _ => ?_)
      (fun cl hcl _ _ t ht => by rw [(textFns fn hfn' cl hcl).2.2.1] at ht; cases ht)
    have h4 := (textFns fn hfn' cl hcl).2.2.2
    cases hr : cl.rhs with
    | dv s l => exact ⟨_, .dv⟩
    | _ => rw [hr] at h4; cases h4
  · rw [List.mem_singleton] at hfn'
    subst hfn'
    rw [sortsOf_nil3 hvs]
    exact ⟨_, evalF⟩

theorem subs_E : c3.subsorts.all (fun p => p.2 != 33) = true := by decide +kernel
theorem coll_E : c3.collOf 33 = none := by decide +kernel
theorem lib_E : c3.lib.carriers.all (·.1 != 33) = true := by decide +kernel

/-- **No value has sort Empty**: no constructor and no subsort pair ends there, no literal is of
it, and it is no collection sort. -/
theorem no_E (v : GroundTerm) : c3.sortOf v ≠ some 33 := by
  intro h
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk : lookupSig c3.ctorSigs f with
    | none =>
      have : c3.lookupOvl f = none := by simp [Semantics.lookupOvl, decided.2.2.1]
      rw [hk, this, c3.lookupOpen_of_noRaw (by decide +kernel) f] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      split at h
      · have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
        have := List.all_eq_true.mp shape.1 k hm
        rw [Option.some.inj h] at this
        simp at this
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp subs_E _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp h
    have hcs := Lib.carrier_of_not _ lib_E
    cases lit with
    | int _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | bool _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | float _ _ _ => simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hd; exact absurd hd.1 (by decide)
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hd
      rcases hd with ((hd | hd) | hd) | ⟨hd | hd, -⟩
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
  | map s' es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [coll_E] at hco; cases hco
  | set s' es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [coll_E] at hco; cases hco
  | list s' es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp h
    rw [coll_E] at hco; cases hco

/-- `clYE` applies under no substitution: Y is of Empty. -/
theorem clYE_not_applies (σ : Subst) (vs : List GroundTerm) : ¬ clYE.AppliesAt c3 σ vs := by
  rintro ⟨h, -⟩
  obtain ⟨v, -, hv⟩ := (wellSortedAt_univ rfl).mp h 0 33 rfl
  exact no_E v hv

/-- A clause without `ensures` whose right side is a literal is coherent with itself. -/
theorem coherent_dv {cl : Clause} (hx : cl.exs = []) (hn : cl.ens = none) {s : Srt} {l : Lit}
    (hr : cl.rhs = .dv s l) : MatchIndependent c3 cl :=
  (matchIndependent_iff_noExs hx).mpr <| Coherent.of_rhs hn hn (fun _ _ _ _ _ _ _ _ => .inr fun r r' h h' => by
    rw [hr] at h h'; cases h; cases h'; rfl) hx hx

/-- **The equations of `c3`'s functions agree**: the text's clauses of one function are of
different priorities; `clYE` and `clOne` are of one priority, and `clYE` applies nowhere. -/
theorem agree3 : ∀ fn ∈ c3.fns, ClausesAgree c3 fn := by
  intro fn hfn
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF] from hfn) with hu | hf
  · intro cl cl' hp hcomp
    exact absurd hcomp (not_compete (List.all_eq_true.mp (textPairs fn hu) _ hp))
  · rw [List.mem_singleton] at hf
    subst hf
    intro cl cl' hp _
    have hp' : (cl, cl') = (clYE, clOne) := by simpa [fF, pairs] using hp
    cases hp'
    exact ⟨fun vs σ _ ha => absurd ha (clYE_not_applies σ vs), fun vs _ σ' _ ha => absurd ha (clYE_not_applies σ' vs)⟩

/-- **The clauses of `c3`'s functions are match independent**: the text's and `clOne` have literal
right sides and no `ensures`; `clYE` applies nowhere. -/
theorem matchInd3 : ∀ fn ∈ c3.fns, ∀ cl ∈ fn.clauses, MatchIndependent c3 cl := by
  intro fn hfn cl hcl
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF] from hfn) with hu | hf
  · have h4 := (textFns fn hu cl hcl).2.2.2
    cases hr : cl.rhs with
    | dv s l => exact coherent_dv (plain3 fn hfn cl hcl).1 (textFns fn hu cl hcl).2.2.1 hr
    | _ => rw [hr] at h4; cases h4
  · rw [List.mem_singleton] at hf
    subst hf
    simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · exact (matchIndependent_iff_noExs rfl).mpr fun vs σ _ ha => absurd ha (clYE_not_applies σ vs)
    · exact coherent_dv rfl rfl rfl

/-- **`fnModel_ofCl` at `c3`**: `c3`'s functions have one result at each argument list and its
evaluation solves the equations, nothing assumed. -/
theorem fnModel3 : FnDet c3 ∧ FnSolves c3 :=
  Faithful.fnModel_ofCl (hpreTop := by decide +kernel) decided.1 decided.2.1 ovl3 fnTerminates3 agree3 matchInd3

/-- What `FnHyp` asks beyond: `isC`, the total function, has a value at each argument; no clause and
no rule needs a witness; no parameter is an open generator. -/
theorem rest3 : c3.fns.all (fun fn => !fn.total || fn.label == 390) = true ∧
    c3.rules.all (fun r => !r.needsWitness c3) = true ∧ c3.params.all (fun k => !k.raw) = true := by
  decide +kernel

/-- `isC`, the total function, has an `[owise]` clause `isC(X) => false` without a `requires`. -/
theorem owise3 : ∀ fn ∈ c.fns, fn.total = true → ∃ cl ∈ fn.clauses, cl.vars = fn.args ∧ fn.args.length = 1 ∧
    cl.req = none ∧ (match cl.pats with | [.var 0] => true | _ => false) = true := by
  decide +kernel

/-- **`isC` has a value at each argument**: its result is a literal, and it cannot have its rest,
its `[owise]` clause applying everywhere. -/
theorem totals3 : ∀ fn ∈ c3.fns, fn.total = true → ∀ vs, c3.sortsOf vs = some fn.args →
    ∃ v, Eval c3 fn.label vs (some v) := by
  intro fn hfn ht vs hvs
  have hu : fn ∈ c.fns := by
    rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF] from hfn) with hu | hf
    · exact hu
    · rw [List.mem_singleton] at hf; subst hf; cases ht
  obtain ⟨r, hr⟩ := fnTerminates3 fn hfn vs hvs
  have hfl := lookup3 hfn
  suffices key : ∃ v, r = some v by obtain ⟨v, rfl⟩ := key; exact ⟨v, hr⟩
  cases hr with
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [hfl] at hfn'; cases hfn'
    exact absurd (plain3 fn hfn _ hmem).1 hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ =>
    rw [hfl] at hfn'; cases hfn'
    exact absurd (plain3 fn hfn _ hmem).1 hne
  | clause hfn' hmem _ _ _ _ _ _ hrhs _ _ =>
    rw [hfl] at hfn'; cases hfn'
    have h4 := (textFns fn hu _ hmem).2.2.2
    revert hrhs h4
    cases _ : Clause.rhs _ with
    | dv s l => intro hrhs _; cases hrhs; exact ⟨_, rfl⟩
    | _ => intro _ h4; cases h4
  | ensFails hfn' hmem _ _ _ _ _ _ hte _ _ =>
    rw [hfl] at hfn'; cases hfn'
    rw [(textFns fn hu _ hmem).2.2.1] at hte; cases hte
  | rest hfn' hnone =>
    rw [hfl] at hfn'; cases hfn'
    exfalso
    obtain ⟨cl, hcl, hvars, hlen, hreq, hpat⟩ := owise3 fn hu ht
    obtain ⟨s0, hs0⟩ : ∃ s0, fn.args = [s0] := by
      match h : fn.args, hlen with
      | [s0], _ => exact ⟨s0, rfl⟩
    rw [hs0] at hvs
    obtain ⟨v, hv, rfl⟩ : ∃ v, c3.sortOf v = some s0 ∧ vs = [v] := by
      match vs, hvs with
      | [v], h => exact ⟨v, (OvlLaws.sortsOf_cons_iff.mp h).1, rfl⟩
      | [], h => cases h
      | v :: w :: ws, h => exact absurd (sortsOf_nil3 (OvlLaws.sortsOf_cons_iff.mp h).2) (List.cons_ne_nil _ _)
    have hpats : cl.pats = [.var 0] := by
      revert hpat
      split
      · intro _; assumption
      · intro h; cases h
    cases hnone cl hcl with
    | intro h =>
      have hσ : c3.WellSortedAt cl.vars cl.leftVars [(0, v)] := by
        intro i _ s hs
        rw [hvars, hs0] at hs
        cases i with
        | zero => cases hs; exact ⟨v, rfl, hv⟩
        | succ i => simp at hs
      cases h [(0, v)] hσ (by rw [hpats]; exact .cons (.var rfl) .nil) with
      | intro hq _ _ => rw [hreq] at hq; cases hq
      | pre h => rw [textPre fn hu cl hcl] at h; exact absurd (Holds.top_eq h) (by simp)

/-- **`FnHyp` holds at `c3`**, though `rightValued` fails there (`clYE`): no decider derives it,
the conjuncts are shown by hand. -/
theorem fnHyp3 : FnHyp c3 :=
  ⟨fnTerminates3, totals3, agree3, matchInd3,
    ⟨fun r hr hw => (by have := List.all_eq_true.mp rest3.2.1 r hr; simp [hw] at this),
     fun _ hfn _ hcl hw => (noWit hfn hcl hw).elim⟩,
    fun k hk hraw => (by have := List.all_eq_true.mp rest3.2.2 k hk; simp [hraw] at this)⟩

/-- **`fnModel_of_fnHypCl` at `c3`.** -/
example : FnDet c3 ∧ FnSolves c3 := fnModel_of_fnHypCl (hpreTop := by decide +kernel) decided.1 decided.2.1 ovl3 fnHyp3

/-- info: 'KCore.fnModel_of_fnHypCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnModel_of_fnHypCl

/-- **`fnDet_of_agree` at `c3`**: one result for every function from the agreement of the equations
and the match independence of the clauses, nothing else of `c3` read. -/
example : FnDet c3 := Faithful.fnDet_of_agree agree3 matchInd3

/-- `_(1) => 1 requires H ==Int 0`, H:Int open (a clause, not one of `c3`'s). -/
def clR : Clause :=
  { vars := [Srt.int], pats := [.dv Srt.int (.int 1)], req := some (.app intEq [.var 0, .dv Srt.int (.int 0)]),
    rhs := .dv Srt.int (.int 1), ens := none }

/-- **`Clause.witnessedDet_of_fnHyp` at `clR`**: H := 0 makes its `requires` `true`, and with
`FnHyp c3` that is its only result, so `clR` is `Witnessed` in `c3`. -/
example : clR.Witnessed c3 :=
  Clause.witnessedDet_of_fnHyp fnHyp3
    ⟨[(0, .dv Srt.int (.int 0))], (fun j _ s hs => by
      cases j with
      | zero => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 0⟩
      | succ j => cases (show (none : Option Srt) = some s from hs)),
     (fun t ht => by
      cases ht
      exact .hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
        (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)), .top⟩

/-- info: 'KCore.Faithful.fnDet_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Faithful.fnDet_of_agree
/-- info: 'KCore.Clause.witnessedDet_of_fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Clause.witnessedDet_of_fnHyp

/-! ## `complete_at` -/

theorem r3_opens : r3.opens = [] := by decide +kernel

/-- **The one successor of `<k> go </k>` is `<k> 0 </k>`**: a step is by `r3`, whose left side fixes
the counter cell to `σ3`'s, and the right side has one result (`CoherentAll`, `coherentAll_ofCl`). -/
theorem succ_go {r : Rule} {σ : Subst} {y : Config c3} (hs : StepBy c3 r σ Go y) : y.val = Zero.val := by
  have hr : r = r3 := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs.mem
    have hj0 : j = 0 := by have := r3_shape.1; omega
    subst hj0
    rfl
  subst hr
  have hm := hs.hmatch
  rw [r3_lhs] at hm
  have h0 : σ.lookup 0 = some counter := by
    cases hm with
    | ctor _ hs' =>
      cases hs' with
      | cons _ hs'' =>
        cases hs'' with
        | cons hv _ => cases hv with | var h => exact h
    | hook hp _ _ => exact absurd hp (by decide +kernel)
    | coll hc _ _ _ => exact absurd (isCtors.1.symm.trans hc) (by decide)
    | ovl hc _ _ _ => exact absurd (isCtors.1.symm.trans hc) (by decide)
  have hev : EvalTerm c3 σ r3.rhs (some Zero.val) := by
    refine Exec.EvalTerm.congr evalRhs fun i hi => ?_
    rw [r3_rhs] at hi
    simp [varOccs, varOccsList] at hi
    subst hi
    rw [h0]; rfl
  have := EvalTerm.functional (Faithful.coherentAll_ofCl agree3 matchInd3) hs.heval hev
  exact Option.some.inj this

/-- **`complete_atCl` at `<k> go </k>`**: with the step's closure, in every model of `Γc c3`, every
successor of `<k> go </k>` is `<k> 0 </k>`, the evaluation at `go` decided by `stepDecided_of_coreCl`
(`f()` is `1`, by `clOne`; `clYE` at the same priority), nothing assumed (no clause needs a
witness, no rule leaves a variable open). -/
example : (Faithful.Γc c3 ∪ Faithful.Γstep c3) ⊧
    (den c3 Go.val ⇒ KoreAML.allNext (KoreAML.disjList ([Outcome.val Zero.val].map (Outcome.pat c3)))) :=
  complete_atCl (hpreTop := by decide +kernel) c3 decided.1 rulesBind3 (Semantics.rulesTop_of_isTop (by decide +kernel)) decided.2.1 decided.2.2.2.2.1 decided.2.2.2.2.2.1 Go
    (Faithful.stepDecided_of_coreCl decided.1 rulesBind3 (Semantics.rulesTop_of_isTop (by decide +kernel)) decided.2.1 ovl3 fnTerminates3 Go.val) _
    (fun y r σ _ hs => by rw [succ_go hs]; exact List.mem_singleton_self _)
    (fun r hr hop => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
      have hj0 : j = 0 := by have := r3_shape.1; omega
      subst hj0
      exact absurd r3_opens hop)
    (fun _ hfn _ hcl hw => (noWit hfn hcl hw).elim)

/-- info: 'KCore.complete_atCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_atCl

/-! ## The pinned theorems at `c3`

`c3` meets `coreOK`: `clauseSorted` asks of `clYE`'s Y only that it occur in the clause, and no
clause of `c3` has an open condition variable. The pinned statements are instantiated at it with
their pinned types; `fnHyp3` is `FnHyp c3`, shown by hand though `rightValued` fails. -/

theorem core3 : c3.coreOK = true := shape.2.2.2.2.2

/-- **`famEx_closed` at `stepGo`.** -/
example : Faithful.Γc c3 ⊧ (Faithful.famEx c3 r3 σ3 ≡ den c3 Zero.val) :=
  famEx_closed c3 core3 stepGo r3_shape.2.2.2.2 (fun _ hfn _ hcl hw => (noWit hfn hcl hw).elim)

/-- **`sound_at` at `stepGo`**: in every model of `Γc c3`, `<k> go </k>` has a successor among the
step's instances, and `<k> 0 </k>` is one of them; `r3` has no competitor. -/
example : (Faithful.Γc c3 ⊧ (den c3 Go.val ⇒ KoreAML.sNext (Faithful.famEx c3 r3 σ3))) ∧
    (Faithful.Γc c3 ⊧ (den c3 Zero.val ⇒ Faithful.famEx c3 r3 σ3)) :=
  sound_at c3 core3 Go Zero r3 σ3 stepGo
    (fun r' hr' hlt _ _ => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr'
      have hj0 : j = 0 := by have := r3_shape.1; omega
      subst hj0
      exact absurd hlt (Nat.lt_irrefl _))
    (fun _ hfn _ hcl hw => (noWit hfn hcl hw).elim)

/-- **`stepDecided_of_fnHyp` at `<k> go </k>`.** -/
theorem decidedGo : StepDecided c3 Go.val := stepDecided_of_fnHyp core3 fnHyp3 Go

/-- **`complete_at` at `<k> go </k>`**: with the step's closure, in every model of `Γc c3`, every
successor of `<k> go </k>` is `<k> 0 </k>`. -/
example : (Faithful.Γc c3 ∪ Faithful.Γstep c3) ⊧
    (den c3 Go.val ⇒ KoreAML.allNext (KoreAML.disjList ([Outcome.val Zero.val].map (Outcome.pat c3)))) :=
  complete_at c3 core3 Go decidedGo _
    (fun y r σ _ hs => by rw [succ_go hs]; exact List.mem_singleton_self _)
    (fun r hr hop => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
      have hj0 : j = 0 := by have := r3_shape.1; omega
      subst hj0
      exact absurd r3_opens hop)
    (fun _ hfn _ hcl hw => (noWit hfn hcl hw).elim)

/-- **`fnModel_of_fnHyp` and `consistent_of` at `c3`**: the theory of `c3` with the step's closure
has a model. -/
example : FnDet c3 ∧ FnSolves c3 := fnModel_of_fnHyp core3 fnHyp3
example : Consistent c3 := consistent_of c3 core3 fnModel3.1 fnModel3.2 (clausePreDecided_of_fnHyp core3 fnHyp3)
  (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp core3) fnHyp3) (openLaws_of_plain (by decide +kernel))

/-- **`Clause.witnessed_of_coherent` at `clR`**: `FnHyp c3` with `coreOK` makes the clauses of `c3`
coherent, so the result `true` of `clR`'s `requires` at H := 0 is its only one. -/
example : clR.Witnessed c3 :=
  have hco : CoherentAll c3 := Faithful.CoherentAll_of (hyp_of_fnHyp core3 fnHyp3)
  have he : EvalTerm c3 [(0, .dv Srt.int (.int 0))] (.app intEq [.var 0, .dv Srt.int (.int 0)])
      (some (bool true)) :=
    .hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)
  Clause.witnessed_of_coherent hco (σ := [(0, .dv Srt.int (.int 0))])
    (fun j _ s hs => by
      cases j with
      | zero => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 0⟩
      | succ j => cases (show (none : Option Srt) = some s from hs))
    (fun t ht => by cases ht; exact ⟨he, fun r hr => EvalTerm.functional hco hr he⟩) .top

/-- **`Clause.pre_not_false_of_only_true` at `\top`**: true is its only truth value under the empty
substitution, and it reads no variable, so it is false under no substitution. -/
example (σ' : Subst) : ¬ Holds c3 1 σ' .top false :=
  Clause.pre_not_false_of_only_true (σ := []) (fun _ hb => hb.top_eq) (fun j hj => by simp [varOccsCond] at hj)

/-- **The headline statements at `c3`.** -/
example : SoundC c3 := sound_hyp c3 core3 fnHyp3
example : ExactC c3 := exact_hyp c3 core3 fnHyp3

/-! ## `FnHyp c3` through the held-named form (`fnHyp_of_fnObligationsN`)

`f` is the one held-named function of `c3` (`Semantics.heldObligations`). Of the two facts
`HeldOwed` offers, the first is false (`clYE`'s variable is of Empty, which has no value); the
second holds: `f()` is `1` by `clOne`, and `f` is not `[total]`. The rank `ord3` and the totality
decider name no function; agreement and match independence are named for `f` and `clYE` and shown
by hand (`agree3`, `matchInd3`); no condition is owed. `FnHyp c3` then comes from the deciders and
the owed fact, not from the six conjuncts shown by hand (`fnHyp3`). -/

/-- A rank of `c3`'s functions: `isC`, `g`, `f`. -/
def ord3 : List Sym := [390, 389, 391]

/-- The lists the package would state: `f` is held-named; no function is named for termination or
totality; `f`'s equations and `clYE` are named for agreement and match independence; no rule and no
clause owes a condition. -/
theorem named3 : c3.heldObligations = [391] ∧ c3.rankObligations ord3 ++ c3.decObligationsL = [] ∧
    c3.totalObligationsRP ord3 [] = [] ∧ c3.agreeObligationsI = [391] ∧
    c3.matchObligationsL = [(391, 0)] ∧ c3.owedRules = [] ∧ c3.owedClauses = [] := by
  decide +kernel

/-- The list is the data's under every interpretation, and is empty exactly where `rightValued`
holds: not at `c3`. -/
example (H : HookParams) : (c3.withHooks H).heldObligations = [391] :=
  (Semantics.heldObligations_withHooks c3 H).trans named3.1
example : c3.heldObligations ≠ [] := fun h => by
  have := Semantics.heldObligations_eq_nil.mp h; rw [shape.2.2.2.1] at this; cases this

theorem lookupF3 {fn : Fn} (h : c3.lookupFn 391 = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans (lookup3 fF_mem))

/-- The first fact is false at `f`: `clYE`'s variable is outside its patterns and conditions and no
value has sort Empty. -/
theorem not_heldFn3 : ¬ c3.HeldFn fF := fun h => by
  rcases h clYE (List.mem_cons_self) 0 33 rfl with h | ⟨v, hv⟩
  · rw [shape.2.2.1] at h; cases h
  · exact no_E v hv

/-- **What is owed of `f`, by the second fact**: `f()` is `1` (`evalF`, by `clOne`), and `f` is
not `[total]`. -/
theorem held3 : ∀ f ∈ c3.heldObligations, HeldOwed c3 f := by
  intro f hf fn hfn
  rw [named3.1, List.mem_singleton] at hf
  subst hf
  have e := lookupF3 hfn
  subst e
  refine .inr ⟨fun fn' hfn' vs hvs => ?_, fun ht => by cases ht⟩
  have e := lookupF3 hfn'
  subst e
  rw [sortsOf_nil3 hvs]
  exact ⟨_, evalF⟩

/-- **The facts the deciders leave of `FnHyp` at `c3`**: the two named ones by hand. -/
theorem obl3 : FnObligations c3 ord3 [] := by
  obtain ⟨-, hterm, htot, hagr, hmat, howR, howC⟩ := named3
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf fn hfn => ?_, fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩,
    openLaws_of_plain (by decide +kernel)⟩
  · rw [hagr, List.mem_singleton] at hf
    subst hf
    have e := lookupF3 hfn
    subst e
    exact agree3 fF fF_mem
  · rw [hmat, List.mem_singleton] at hp
    subst hp
    have e := lookupF3 hfn
    subst e
    exact matchInd3 fF fF_mem cl (List.mem_of_getElem? hcl)

/-- **`FnHyp c3` from the held-named form**: `coreOK`, the owed fact of `f` and the deciders. -/
theorem fnHyp3N : FnHyp c3 := fnHyp_of_fnObligationsN core3 held3 ParamsTotal.nil obl3

/-- The forms a package's statements instantiate, at `c3`: soundness, completeness, the functions'
model and consistency, and each for an interpretation H of the parameters, the owed facts and the
named ones stated for H. -/
example : SoundC c3 := sound_fnN c3 ord3 [] core3 held3 ParamsTotal.nil obl3
example (ref : OutFn) : CompleteC c3 ref := complete_fnN c3 ord3 [] ref core3 held3 ParamsTotal.nil obl3
theorem facts3 : FnFacts c3 ord3 [] := ⟨obl3.1, obl3.2.1, obl3.2.2.1, obl3.2.2.2.1, obl3.2.2.2.2.2⟩
example : FnDet c3 ∧ FnSolves c3 := fnModel_of_fnFactsN core3 held3 facts3
example : Consistent c3 := consistent_of_fnFactsN core3 held3 facts3
example (H : HookParams) (hheld : ∀ f ∈ c3.heldObligations, HeldOwed (c3.withHooks H) f)
    (hob : FnObligations (c3.withHooks H) ord3 []) : FnHyp (c3.withHooks H) :=
  fnHyp_withHooksN core3 H hheld ParamsTotal.nil hob
example (H : HookParams) (hheld : ∀ f ∈ c3.heldObligations, HeldOwed (c3.withHooks H) f)
    (hob : FnObligations (c3.withHooks H) ord3 []) : SoundC (c3.withHooks H) :=
  sound_fn_withHooksN c3 ord3 [] core3 H hheld ParamsTotal.nil hob
example (ref : OutFn) (H : HookParams) (hheld : ∀ f ∈ c3.heldObligations, HeldOwed (c3.withHooks H) f)
    (hob : FnObligations (c3.withHooks H) ord3 []) : CompleteC (c3.withHooks H) ref :=
  complete_fn_withHooksN c3 ord3 [] ref core3 H hheld ParamsTotal.nil hob
example (H : HookParams) (hheld : ∀ f ∈ c3.heldObligations, HeldOwed (c3.withHooks H) f)
    (hob : FnFacts (c3.withHooks H) ord3 []) : (FnDet (c3.withHooks H) ∧ FnSolves (c3.withHooks H)) ∧
      Consistent (c3.withHooks H) :=
  ⟨fnModel_of_fnFacts_withHooksN core3 H hheld hob, consistent_of_fnFacts_withHooksN core3 H hheld hob⟩

/-- The two lemmas under the form, at `c3`: every function terminates, `f` among them, by the rank
and the owed fact. -/
example : ∀ f, Terminates c3 f :=
  terminates_of_rankLN (hpreTop := by decide +kernel) (hnoEx := Semantics.fnsNoExs_of_all (by decide +kernel)) shape.2.2.2.2.1 decided.2.1 (Semantics.ovlCase_of_core core3) ord3 held3 obl3.1

/--
info: 'OpenClausePinsTest.fnHyp3N' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fnHyp3N

/-! ## The clauses' hypothesis on the conditions discharged by a witness: `c3W`

`c3W` is `c3` with a third clause of `f`, `clW0` (`f() => 1 requires H ==Int 0`, H:Int, its closed
condition over an unconfined sort): `c3W` meets `coreOK`, `clW0` needs a witness and is
`Witnessed` at H := 0, and no other clause needs one, so the pinned statements' hypothesis `hc` is
proved from the witness (`hcW3`). -/

/-- `f() => 1 requires H ==Int 0` -/
def clW0 : Clause :=
  { vars := [Srt.int], pats := [], req := some (.app intEq [.var 0, .dv Srt.int (.int 0)]),
    rhs := .dv Srt.int (.int 1), ens := none }
def fFW : Fn := { fF with clauses := [clYE, clOne, clW0] }
noncomputable def c3W : Semantics := { c3 with fns := c.fns ++ [fFW] }

theorem shapeW : c3W.coreOK = true ∧ clW0.needsWitness c3W = true ∧ clW0.condVars = [0] ∧
    c.fns.all (fun fn => fn.clauses.all fun cl => !cl.needsWitness c3W) = true ∧
    [clYE, clOne].all (fun cl => !cl.needsWitness c3W) = true ∧
    c3W.rules.all (fun r => !r.needsWitness c3W) = true := by
  decide_cheap

/-- **`clW0` is `Witnessed`** at H := 0: `0 ==Int 0` is `true`, and by inversion of the hook nothing else. -/
theorem witW0 : clW0.Witnessed c3W := by
  refine Clause.witnessed_of_top rfl (σ := [(0, .dv Srt.int (.int 0))]) (fun j hj s hs => ?_) (fun t ht => ?_)
  · rw [shapeW.2.2.1] at hj
    cases List.mem_singleton.mp hj
    cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 0⟩
  · cases ht
    refine ⟨.hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h), fun r hr => ?_⟩
    cases hr with
    | ctor h _ => exact absurd h (by decide +kernel)
    | hook h hhk hts hh hund =>
      cases hts with
      | cons h1 hs1 =>
        cases h1
        cases hs1 with
        | cons h2 hs2 =>
          cases h2
          cases hs2
          have h3 := hh _ rfl
          have h4 : c3W.hookRes intEq [.dv Srt.int (.int 0), .dv Srt.int (.int 0)] =
              some (some (.dv Srt.bool (.bool true))) := by rfl
          exact Option.some.inj (h3.symm.trans h4)
    | param h hhk hp _ _ => exact absurd hhk (by decide +kernel)
    | call _ hh _ _ _ _ => exact absurd hh (by decide +kernel)
    | callUndef _ hh _ _ _ => exact absurd hh (by decide +kernel)
    | ovl _ ho _ => exact absurd ho (by decide +kernel)
    | ovlFn _ ho => exact absurd ho (by decide +kernel)

/-- **`hc` at `c3W`, from the witness**: `clW0` is `Witnessed`; no other clause needs a witness. -/
theorem hcW3 : ∀ fn ∈ c3W.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c3W = true → cl.CondDecided c3W := by
  intro fn hfn cl hcl hw
  rcases List.mem_append.mp hfn with hfn' | hfn'
  · have := List.all_eq_true.mp (List.all_eq_true.mp shapeW.2.2.2.1 fn hfn') cl hcl
    simp [hw] at this
  · cases List.mem_singleton.mp hfn'
    rcases List.mem_cons.mp hcl with rfl | hcl
    · have := List.all_eq_true.mp shapeW.2.2.2.2.1 clYE (List.mem_cons_self ..); simp [hw] at this
    rcases List.mem_cons.mp hcl with rfl | hcl
    · have := List.all_eq_true.mp shapeW.2.2.2.2.1 clOne (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp [hw] at this
    · cases List.mem_singleton.mp hcl
      exact Or.inl witW0

/-- No rule of `c3W` needs a witness. -/
theorem hwW3 {x : Config c3W} (r : Rule) : ∀ r' ∈ c3W.rules, r'.prio < r.prio → r'.needsWitness c3W = true →
    (∃ σ', PatVal c3W σ' r'.lhs x.val) → r'.CondDecided c3W := by
  intro r' hr' _ hw _
  have := List.all_eq_true.mp shapeW.2.2.2.2.2 r' hr'
  simp [hw] at this

/-- **`sound_at`, `famEx_closed` and `complete_at` at `c3W`**, `hc` from the witness. -/
example (x y : Config c3W) (r : Rule) (σ : Subst) (hs : StepBy c3W r σ x y) :
    (Faithful.Γc c3W ⊧ (den c3W x.val ⇒ KoreAML.sNext (Faithful.famEx c3W r σ))) ∧
      (Faithful.Γc c3W ⊧ (den c3W y.val ⇒ Faithful.famEx c3W r σ)) :=
  sound_at c3W shapeW.1 x y r σ hs (hwW3 (x := x) r) hcW3

example {x y : Config c3W} {r : Rule} {σ : Subst} (hs : StepBy c3W r σ x y) (hex : r.exs = []) :
    Faithful.Γc c3W ⊧ (Faithful.famEx c3W r σ ≡ den c3W y.val) :=
  famEx_closed c3W shapeW.1 hs hex hcW3

example (x : Config c3W) (hd : StepDecided c3W x.val) (os : List Outcome)
    (hval : ∀ (y : Config c3W) (r : Rule) (σ : Subst), r.opens = [] → StepBy c3W r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c3W.rules, r.opens ≠ [] → ∀ σ, Unblocked c3W r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os) :
    (Faithful.Γc c3W ∪ Faithful.Γstep c3W) ⊧
      (den c3W x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c3W)))) :=
  complete_at c3W shapeW.1 x hd os hval hfam hcW3

/-- info: 'OpenClausePinsTest.hcW3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcW3

/-! ## A clause with a variable only the `ensures` holds, among another clause's `lowerClauses`

`c5` is `c3` with `clOne` given a larger priority than `clYE` (`clOne5`): `clYE` is then among
`clOne5`'s `lowerClauses`, with its one variable Y outside its patterns and conditions (`leftVars`
is empty) and of Empty. `clYE` neither applies nor fails, so `f()` has no result; the value model is
a model of the theory (`hypModel_ofCl`), and `exclusion_iffCl` reads `clYE`'s exclusion there. -/

/-- `f() => 1`, of a larger priority than `clYE`. -/
def clOne5 : Clause := { clOne with prio := clYE.prio + 1 }

/-- `f` with the clauses `clYE` and `clOne5`. -/
def fF5 : Fn := { fF with clauses := [clYE, clOne5] }

/-- `c` with `f` a function of the clauses `clYE` and `clOne5`. -/
noncomputable def c5 : Semantics := { c with fns := c.fns ++ [fF5], params := c.params.filter (·.sig.name != 391) }

theorem shape5 : clYE.leftVars = [] ∧ clYE.vars = [33] ∧ c5.coreOK = true ∧ c5.rightValued = false ∧
    c5.ctorSigs.all (·.result != 33) = true := by
  decide_cheap

/-- `clYE` is among `clOne5`'s `lowerClauses`: not `aside`, of a smaller priority. -/
theorem clYE_low : clYE ∈ Faithful.lowerClauses fF5 clOne5 :=
  List.mem_filter.mpr ⟨List.mem_cons_self .., by decide +kernel⟩

theorem decided5 : c5.sortedOKCl = true ∧ c5.srReady = true ∧ c5.ovls = [] ∧
    c5.subsorts.all (fun p => p.1 != p.2) = true ∧ c5.faithCoreOK = true ∧ Faithful.patHooksApart c5 = true ∧
    c5.idsOK = true := by
  decide_cheap

instance ovl5 : OvlOK c5 := OvlOK.of_nil decided5.2.2.1 decided5.2.2.2.1

theorem lookup5 {fn : Fn} (hfn : fn ∈ c5.fns) : c5.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label (sortCtx_of_allCl decided5.1 decided5.2.1 (OvlOK.ovlCase ovl5)).nodupFns (List.mem_append_left _ hfn)

theorem subs_E5 : c5.subsorts.all (fun p => p.2 != 33) = true := by decide +kernel
theorem coll_E5 : c5.collOf 33 = none := by decide +kernel
theorem lib_E5 : c5.lib.carriers.all (·.1 != 33) = true := by decide +kernel

/-- No value has sort Empty in `c5`, as in `c3`. -/
theorem no_E5 (v : GroundTerm) : c5.sortOf v ≠ some 33 := by
  intro h
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk : lookupSig c5.ctorSigs f with
    | none =>
      have : c5.lookupOvl f = none := by simp [Semantics.lookupOvl, decided5.2.2.1]
      rw [hk, this, c5.lookupOpen_of_noRaw (by decide +kernel) f] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      split at h
      · have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
        have := List.all_eq_true.mp shape5.2.2.2.2 k hm
        rw [Option.some.inj h] at this
        simp at this
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp subs_E5 _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp h
    have hcs := Lib.carrier_of_not _ lib_E5
    cases lit with
    | int _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | bool _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | float _ _ _ => simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hd; exact absurd hd.1 (by decide)
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hd
      rcases hd with ((hd | hd) | hd) | ⟨hd | hd, -⟩
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
  | map s' es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [coll_E5] at hco; cases hco
  | set s' es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [coll_E5] at hco; cases hco
  | list s' es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp h
    rw [coll_E5] at hco; cases hco

theorem clYE_not_applies5 (σ : Subst) (vs : List GroundTerm) : ¬ clYE.AppliesAt c5 σ vs := by
  rintro ⟨h, -⟩
  obtain ⟨v, -, hv⟩ := (wellSortedAt_univ rfl).mp h 0 33 rfl
  exact no_E5 v hv

theorem coherent_dv5 {cl : Clause} (hx : cl.exs = []) (hn : cl.ens = none) {s : Srt} {l : Lit}
    (hr : cl.rhs = .dv s l) : MatchIndependent c5 cl :=
  (matchIndependent_iff_noExs hx).mpr <| Coherent.of_rhs hn hn (fun _ _ _ _ _ _ _ _ => .inr fun r r' h h' => by
    rw [hr] at h h'; cases h; cases h'; rfl) hx hx

/-- No clause of a function of `c5` has an existential variable or a right side's predicate other
than `\top`. -/
theorem plain5 : ∀ fn ∈ c5.fns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top :=
  fun fn hfn => Semantics.sortedOK_plainCl_of_noExs (Semantics.coreOK_parts shape5.2.2.1).1 (Semantics.fnsNoExs_of_all (by decide +kernel)) fn (List.mem_append_left _ hfn)

theorem agree5 : ∀ fn ∈ c5.fns, ClausesAgree c5 fn := by
  intro fn hfn
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF5] from hfn) with hu | hf
  · intro cl cl' hp hcomp
    exact absurd hcomp (not_compete (List.all_eq_true.mp (textPairs fn hu) _ hp))
  · rw [List.mem_singleton] at hf
    subst hf
    intro cl cl' hp _
    have hp' : (cl, cl') = (clYE, clOne5) := by simpa [fF5, pairs] using hp
    cases hp'
    exact ⟨fun vs σ _ ha => absurd ha (clYE_not_applies5 σ vs), fun vs _ σ' _ ha => absurd ha (clYE_not_applies5 σ' vs)⟩

theorem matchInd5 : ∀ fn ∈ c5.fns, ∀ cl ∈ fn.clauses, MatchIndependent c5 cl := by
  intro fn hfn cl hcl
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF5] from hfn) with hu | hf
  · have h4 := (textFns fn hu cl hcl).2.2.2
    cases hr : cl.rhs with
    | dv s l => exact coherent_dv5 (plain5 fn hfn cl hcl).1 (textFns fn hu cl hcl).2.2.1 hr
    | _ => rw [hr] at h4; cases h4
  · rw [List.mem_singleton] at hf
    subst hf
    simp only [fF5, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · exact (matchIndependent_iff_noExs rfl).mpr fun vs σ _ ha => absurd ha (clYE_not_applies5 σ vs)
    · exact coherent_dv5 rfl rfl rfl

theorem reqNone5 : ∀ fn ∈ c5.fns, ∀ cl ∈ fn.clauses, cl.req = none := by decide +kernel

/-- Each clause of `c5` has the precondition `.top`. -/
theorem preTop5 : ∀ fn ∈ c5.fns, ∀ cl ∈ fn.clauses, cl.pre = .top :=
  fun fn hfn cl hcl =>
    Cond.eq_top_of_isTop ((by decide +kernel : ∀ fn ∈ c5.fns, ∀ cl ∈ fn.clauses, cl.pre.isTop = true) fn hfn cl hcl)

theorem fnDet5 : FnDet c5 := Faithful.fnDet_of_agree agree5 matchInd5

/-- **Evaluation solves `c5`'s equations**: a clause instance that decides is one of the text's or
`clOne5`, whose right sides are literals; `clYE` decides nowhere. -/
theorem fnSolves5 : FnSolves c5 := by
  refine fnSolves_of_parts_lookup (fun _ hfn => lookup5 hfn) fnDet5 plain5 ?_ ?_
  · intro fn hfn _ _ _ _ _ cl' hcl' _ _ σ' _ _
    exact ⟨(fun t ht => by rw [reqNone5 fn hfn cl' hcl'] at ht; cases ht), true,
      Clause.holds_preTop (preTop5 fn hfn cl' hcl') σ'⟩
  · intro fn hfn vs cl σ cl' σ' hcl hcl' hdec hdec' _
    rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF5] from hfn) with hu | hf
    · have h4 := (textFns fn hu cl' hcl').2.2.2
      cases hr : cl'.rhs with
      | dv s l =>
        refine ⟨some (.dv s l), Or.inl ⟨fun t ht => ?_, ?_⟩⟩
        · rw [(textFns fn hu cl' hcl').2.2.1] at ht; cases ht
        · rw [hr]; exact .dv
      | _ => rw [hr] at h4; cases h4
    · rw [List.mem_singleton] at hf
      subst hf
      simp only [fF5, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hdec'.1 (clYE_not_applies5 σ' vs)
      · refine ⟨some (.dv Srt.int (.int 1)), Or.inl ⟨fun t ht => ?_, ?_⟩⟩
        · cases ht
        · exact .dv

/-- The value model is a model of `c5`'s theory. -/
theorem hypModel5 : Faithful.Model.HypModelCore c5 :=
  hypModel_ofCl decided5.1 decided5.2.1 ovl5 decided5.2.2.2.2.1 decided5.2.2.2.2.2.1 decided5.2.2.2.2.2.2
    fnDet5

/-- **`exclusion_iffCl` at `clYE`, a clause of `clOne5`'s `lowerClauses` with a variable outside
its patterns and conditions**: in the value model, `clYE`'s exclusion holds exactly where its
(empty) patterns match and its (absent) `requires` holds under a substitution well sorted on
`leftVars`, which is empty; Y is not asked a value. -/
example := @Faithful.Model.exclusion_iffCl c5 (by decide +kernel) hypModel5 fF5
  (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))) clYE (List.mem_cons_self ..) rfl

/-- info: 'KCore.Faithful.Model.exclusion_iffCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Faithful.Model.exclusion_iffCl

end OpenClausePinsTest
