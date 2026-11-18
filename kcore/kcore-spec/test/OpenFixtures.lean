/-
  The fixtures of rules whose left side leaves a variable open, read from K 7.1.337 kompile's KORE
  (test/constructs/fixtures, their kompiled texts copied to f2-examples). Run from the package root:
  `lake env lean -j1 test/OpenFixtures.lean`. Kernel-checked (`decide +kernel`).

  - `Genless` (e2-open-genless, `f2-examples/opengenless.kompile.kore`): `syntax Empty` (no
    production), `S ::= mk(Empty) | k()`, `isMk(S)` with `isMk(mk(_)) => true` and
    `isMk(k()) => false`, the rule 0 `<k> a() => b() ... </k> requires isMk(X:S)` (X bound by no
    side) and the rule 1 `<k> a() => c() ... </k> [owise]`.
    - `coreOK` holds. S is not confined (`confined S = false`): its generator `mk` takes Empty, a
      sort without a generator, of which the text states no elements.
    - The rule 0 is read by arm C of `rulesPlain`: X is under no constructor of the right side
      (arm A) and of no confined sort (arm B), and the condition is closed and holds no variable
      the rest of the rule holds; `rulePlainOpen` holds and `openRefusal` gives none. It
      `needsWitness`, and its `CondDecided` is the owed fact the account lists (`owedCondDecided`:
      rule 0, over X).
    - Every value of S is `k()` (`valS`: no value has sort Empty), and `isMk(k())` has the one
      result `false` (`isMk_k_only`), so the rule 0 is not `Witnessed` (`not_witnessed0`) and does
      not apply at `<k> a() </k>` (`notApplies0`). Whether it is `Refuted` (`Γc` excludes an element
      of S where `isMk` is true) is neither shown nor excluded here.
    - `Step a() c()` holds at values, by the rule 1 (`step_a_c`).
    - Soundness at that step is stated under the owed fact as a hypothesis, named with its rule
      (`sound_at_a_c_of_owed0`, the pinned `sound_at` with `hw` from `owed0 : r0.CondDecided c`).
  - `Unbound` (e2-unbound, `f2-examples/unbound.kompile.kore`): the one rule
    `<k> a() => b(X) ... </k>` (X:Int bound by no side), `b(Int)` a constructor of Exp.
    - `coreOK` holds. The rule is read by arm A (`arm_A`: X is under the constructor b of the right
      side; `rulePlainOpen`, `openRefusal` none, no witness needed); the definition reads a confined
      sort, so its theory is `Γc`.
    - `<k> b(i) </k>` is a configuration for every Int i (`sortOf_cfgB`), and `<k> a() </k>` steps
      to it under X := i (`stepBy`, `step`).
    - `sound_b`: `Γc ⊧ den a() ⇒ •den b(i)` for every i: in every model each `b(i)` is a successor.
    - `step_inv`: every `Step` successor of `<k> a() </k>` is some `<k> b(i) </k>`.
    - `outIs`: `refU` (the family of r0 at an unblocked match, none elsewhere) meets `OutIs`; at
      `<k> a() </k>` it lists one family (`refU_A`), and `complete_A` is `complete_hyp` there.
    - `exact_b`: under `FnHyp c`, by `ExactC` (`exact_hyp`), y is a successor of `<k> a() </k>` in
      some model of `Γc` with the step's closure exactly where y is some `<k> b(i) </k>`: no other
      value is a successor in any model. `FnHyp c` is a hypothesis here, not shown.
  - `Linked` (e2-open-linked and e2-open-linked-bool, `f2-examples/openlinked.kompile.kore` and
    `openlinkedbool.kompile.kore`): `a() => b(X) requires X ==Int 2 *Int H` and
    `a() => b(#if B #then 1 #else 0 #fi) requires B ==Bool (2 *Int H ==Int 1)`. H, of the
    unconfined sort Int, is bound by no side and passes no arm: it is under no constructor of the
    right side, and its closed condition shares a variable with the right side. Each text has the
    one refusal `openRequires`, naming H and the shared variable (X:Int; B:Bool).
  - `Cool` (e2-rule, `f2-examples/rulecool.kompile.kore`): nine rules over `a(Int)`, `b(Int)`,
    `c(Int)`, among them `<k> c(1) => b(1) ... </k> [cool]` and `<k> c(2) => b(2) ... </k> [heat]`,
    which kompile writes with the `requires` `true andBool isKResult(HOLE)` and
    `true andBool notBool isKResult(HOLE)`, HOLE:K bound by no side.
    - `coreOK` holds, and no rule is refused `openRequires` (`arms`): HOLE, of the unconfined sort K,
      is held by the `requires` alone, a closed condition no variable of which the rest of the rule
      holds; each of the two rules owes its `CondDecided` (`Parse.owedCondDecided`: rules 6 and 7,
      over HOLE).
    - Both are `Witnessed` (`witnessed6`, `witnessed7`), so the owed facts hold (`condDecided`): the
      `[cool]` condition at HOLE := `kseq(inj{Int,KItem}(0), dotk)`, the `[heat]` one at HOLE := `dotk`.
      The `requires` is evaluated by `Exec.evalT_sound`, its `ClauseCtx` from the sort predicates
      (`fns` is empty), since `ok` is false with an open rule variable.
    - At `<k> c(1) </k>` the successor `<k> b(1) </k>`, by the `[cool]` rule (`stepBy6`, by hand;
      the rule 1 of priority 10 does not apply there, `notApplies1`), and in every model of `Γc`
      (`sound_c_b`, the pinned `sound_at` and `famEx_closed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace OpenFixtures

namespace Genless

definition_of defn from "f2-examples/opengenless.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sS : Srt := 32
def sE : Srt := 34
def sExp : Srt := 33
def kCell : Sym := 385
def symA : Sym := 387
def symB : Sym := 388
def symC : Sym := 389
def symK : Sym := 390
def symMk : Sym := 391
def isMk : Sym := 392

theorem names_ok : c.sortName sS = "S" ∧ c.sortName sE = "Empty" ∧ c.sortName sExp = "Exp" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" ∧ c.symName symK = "Lblk" ∧ c.symName symMk = "Lblmk" ∧
    c.symName isMk = "LblisMk" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- S is not confined: its generator `mk` takes Empty, which has no generator. -/
theorem not_confined : c.confined sS = false ∧ c.confined sE = false := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)

theorem rules_eq : c.rules = [r0, r1] := rfl
theorem r0_req : r0.req = some (.app isMk [.var 2]) := rfl
theorem r0_vars : r0.vars = [Srt.k, 19, sS] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symA []), .var 0]], .var 1] := rfl
theorem r0_pre : r0.pre = .top := rfl
theorem r1_vars : r1.vars = [Srt.k, 19] := rfl
theorem r1_lhs : r1.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symA []), .var 0]], .var 1] := rfl
theorem r1_rhs : r1.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC []), .var 0]], .var 1] := rfl
theorem r1_req : r1.req = none := rfl
theorem r1_ens : r1.ens = none := rfl
theorem r1_pre : r1.pre = .top := rfl
theorem r1_post : r1.post = .top := rfl
theorem prios : r0.prio = 50 ∧ r1.prio = 200 := ⟨rfl, rfl⟩

/-- **The rule 0 is read by arm C**: its open variable X (variable 2) is under no constructor of
the right side and of no confined sort, and is held by the `requires`, a closed condition no
variable of which the right side, the `ensures` or `post` holds. -/
theorem arm_C :
    r0.opens = [2] ∧
    (ctorOccs c r0.rhs).contains 2 = false ∧
    ((r0.vars[2]?.map c.confined).getD false) = false ∧
    (r0.condVars.contains 2 && r0.reqClosed &&
      r0.condVars.all (fun j => !(varOccs r0.rhs ++ (r0.ens.map varOccs).getD [] ++
        varOccsCond r0.vars.length r0.post).contains j)) = true ∧
    c.rulePlainOpen r0 = true ∧ (Parse.openRefusal c r0 []).isNone = true ∧
    r0.needsWitness c = true ∧ r1.needsWitness c = false := by
  decide +kernel

/-- The owed fact the account lists: rule 0's `CondDecided`, over its variable 2 (X:S). -/
theorem owed : Parse.owedCondDecided c = [(0, [2])] := by decide +kernel

/-- No clause needs a witness. -/
theorem no_clause_owed : c.fns.all (fun fn => fn.clauses.all fun cl => !cl.needsWitness c) = true := by
  decide +kernel

/-! ## The values of S -/

theorem ctorSigs_E : c.ctorSigs.all (fun k => k.result != sE) = true := by decide +kernel
theorem ctorSigs_S : c.ctorSigs.all (fun k => k.result != sS ||
    (k.name == symK && k.args == []) || (k.name == symMk && k.args == [sE])) = true := by decide +kernel
theorem subsorts_SE : c.subsorts.all (fun p => p.2 != sS && p.2 != sE) = true := by decide +kernel
theorem ovls_nil : c.ovls = [] := by decide +kernel
theorem lits_SE : c.lib.carrier sS = sS ∧ c.lib.carrier sE = sE ∧
    c.lib.tokenSorts.contains sS = false ∧ c.lib.tokenSorts.contains sE = false ∧
    c.lib.byteSorts.contains sS = false ∧ c.lib.byteSorts.contains sE = false := by decide +kernel
theorem colls_SE : c.collOf sS = none ∧ c.collOf sE = none := by decide +kernel

/-- A sort that is its own carrier, no literal sort, token sort or byte sort, has no literal. -/
theorem dvOK_false {l : Lib} {s : Srt} (hc : l.carrier s = s) (ht : l.tokenSorts.contains s = false)
    (hb : l.byteSorts.contains s = false) (h1 : s ≠ Srt.int) (h2 : s ≠ Srt.bool)
    (h3 : s ≠ Srt.kconfigVar) (h4 : s ≠ Srt.string) (h5 : s ≠ Srt.bytes) (h6 : s ≠ Srt.float)
    (lit : Lit) : dvOK l s lit = false := by
  have ht' : s ∉ l.tokenSorts := by simpa using ht
  have hb' : s ∉ l.byteSorts := by simpa using hb
  cases lit <;> simp [dvOK, hc, h1, h2, h3, h4, h5, h6, ht', hb']

theorem dvOK_S (lit : Lit) : dvOK c.lib sS lit = false :=
  dvOK_false lits_SE.1 lits_SE.2.2.1 lits_SE.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) lit
theorem dvOK_E (lit : Lit) : dvOK c.lib sE lit = false :=
  dvOK_false lits_SE.2.1 lits_SE.2.2.2.1 lits_SE.2.2.2.2.2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) lit

/-- No parameter is raw (`sortOf`'s open-generator arm reads none, `ctor_sig`). -/
theorem noRaw_intA1 : (c.params.all fun k => !k.raw) = true := by
  decide +kernel

/-- A constructor application of sort s is an application of a constructor whose result is s. -/
theorem ctor_sig {f : Sym} {ts : List GroundTerm} {s : Srt} (h : c.sortOf (.ctor f ts) = some s) :
    ∃ k ∈ c.ctorSigs, k.name = f ∧ c.sortsOf ts = some k.args ∧ k.result = s := by
  rcases (Semantics.sortOf_ctor_iff c).mp h with ⟨k, hk, hts, hr⟩ | ⟨-, o, ho, -⟩ | ⟨-, -, kp, hko, -⟩
  · rw [lookupSig_eq] at hk
    exact ⟨k, List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk, hts, hr.symm⟩
  · simp [Semantics.lookupOvl, ovls_nil] at ho
  · rw [c.lookupOpen_of_noRaw (fun k hk => by simpa using List.all_eq_true.mp noRaw_intA1 k hk) f] at hko
    cases hko

/-- A value of a sort that is no injection's target, has no literal and is no collection sort is a
constructor application. -/
theorem ctor_of_sort {v : GroundTerm} {s : Srt} (h : c.sortOf v = some s)
    (hsub : ∀ p ∈ c.subsorts, p.2 ≠ s) (hlit : ∀ lit, dvOK c.lib s lit = false) (hcoll : c.collOf s = none) :
    ∃ f ts, v = .ctor f ts := by
  cases v with
  | ctor f ts => exact ⟨f, ts, rfl⟩
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hcond
      exact absurd rfl (hsub _ hcond.1.1)
    · cases h
  | dv s' lit =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i hok
      cases h
      rw [hlit] at hok
      cases hok
    · cases h
  | map s' es =>
    obtain ⟨rfl, hco⟩ := sortOf_map_sort h
    rw [hcoll] at hco; cases hco
  | set s' es =>
    obtain ⟨rfl, k, hco, -⟩ := Faithful.Model.sortOf_set_some h
    rw [hcoll] at hco; cases hco
  | list s' es =>
    obtain ⟨rfl, k, hco, -⟩ := Faithful.Model.sortOf_list_some h
    rw [hcoll] at hco; cases hco

theorem subsorts_S : ∀ p ∈ c.subsorts, p.2 ≠ sS := fun p hp => by
  have := List.all_eq_true.mp subsorts_SE p hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.1
theorem subsorts_E : ∀ p ∈ c.subsorts, p.2 ≠ sE := fun p hp => by
  have := List.all_eq_true.mp subsorts_SE p hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.2

/-- No value has sort Empty: no constructor, injection, literal or collection has it. -/
theorem noEmpty (v : GroundTerm) : c.sortOf v ≠ some sE := by
  intro h
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_E dvOK_E colls_SE.2
  obtain ⟨k, hk, -, -, hr⟩ := ctor_sig h
  have := List.all_eq_true.mp ctorSigs_E k hk
  simp [hr] at this

/-- **Every value of S is `k()`**: S's constructors are `k()` and `mk(Empty)`, and Empty has no
value. -/
theorem valS {v : GroundTerm} (h : c.sortOf v = some sS) : v = .ctor symK [] := by
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_S dvOK_S colls_SE.1
  obtain ⟨k, hk, hname, hts, hr⟩ := ctor_sig h
  have := List.all_eq_true.mp ctorSigs_S k hk
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with ⟨hn, ha⟩ | ⟨hn, ha⟩
  · rw [ha] at hts
    cases ts with
    | nil => rw [← hname, hn]
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts <;> cases hts
  · rw [ha] at hts
    cases ts with
    | nil => simp [Semantics.sortsOf] at hts
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts
      · rename_i s ss hs _
        cases hts
        exact absurd hs (noEmpty t)
      · cases hts

/-! ## `isMk` at `k()` -/

noncomputable def fnIsMk : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clK : Clause := fnIsMk.clauses[0]'(by decide +kernel)
noncomputable def clMk : Clause := fnIsMk.clauses[1]'(by decide +kernel)

theorem lookup_isMk : c.lookupFn isMk = some fnIsMk := rfl
theorem isMk_clauses : fnIsMk.clauses = [clK, clMk] := rfl
theorem clK_shape : clK.vars = [] ∧ clK.pats = [.app symK []] ∧ clK.req = none ∧
    clK.rhs = .dv Srt.bool (.bool false) ∧ clK.ens = none ∧ clK.prio = 50 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem clMk_shape : clMk.pats = [.app symMk [.var 0]] ∧ clMk.ens = none ∧ clMk.prio = 50 :=
  ⟨rfl, rfl, rfl⟩
theorem isMk_syms : c.isCtor isMk = false ∧ isHook isMk = false ∧ c.isParam isMk = false ∧
    c.isCtor symK = true ∧ patternHooks.contains symMk = false ∧ c.isCollPat symMk = false ∧
    c.isOvl symMk = false := by
  decide +kernel

/-- `isMk(k())` is `false`, by its clause `isMk(k()) => false`. -/
theorem eval_isMk_k : Eval c isMk [.ctor symK []] (some (bool false)) := by
  refine Eval.clause (cl := clK) (σ := []) lookup_isMk (by rw [isMk_clauses]; simp)
    (fun j s hs => ?_) ?_ (fun t ht => ?_) (Clause.holds_preTop (by rfl) _) (fun cl' hcl' _ hlt => ?_) (by rfl) ?_
    (fun t ht => ?_) (Clause.holds_postTop (by rfl) _)
  · rw [clK_shape.1] at hs; cases hs
  · rw [clK_shape.2.1]; exact .cons (.ctor isMk_syms.2.2.2.1 .nil) .nil
  · rw [clK_shape.2.2.1] at ht; cases ht
  · rw [isMk_clauses] at hcl'
    rw [clK_shape.2.2.2.2.2] at hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · rw [clK_shape.2.2.2.2.2] at hlt; omega
    · rw [clMk_shape.2.2] at hlt; omega
  · rw [clK_shape.2.2.2.1]; exact .dv
  · rw [clK_shape.2.2.2.2.1] at ht; cases ht

/-- **`isMk(k())` has no result but `false`**: `isMk(mk(_))`'s pattern does not denote `k()`, and
the clause `isMk(k()) => false` applies, with no `requires` and no `ensures`. -/
theorem isMk_k_only {r : Option GroundTerm} (h : Eval c isMk [.ctor symK []] r) : r = some (bool false) := by
  cases h with
  | clause hfn hmem hσ hmatch hreq _ hprio _ hrhs hens _ =>
    rw [lookup_isMk] at hfn
    cases hfn
    rw [isMk_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [clK_shape.2.2.2.1] at hrhs
      cases hrhs
      rfl
    · rw [clMk_shape.1] at hmatch
      cases hmatch with
      | cons h _ =>
        cases h with
        | hook hp _ _ => exact absurd hp (by rw [isMk_syms.2.2.2.2.1]; decide)
        | coll _ hp _ _ => exact absurd hp (by rw [isMk_syms.2.2.2.2.2.1]; decide)
        | ovl _ ho _ _ => exact absurd ho (by rw [isMk_syms.2.2.2.2.2.2]; decide)
  | rest hfn hnone =>
    rw [lookup_isMk] at hfn
    cases hfn
    have hf := hnone clK (by rw [isMk_clauses]; simp)
    cases hf with
    | intro hall =>
      have hreq := hall [] (fun i _ s hs => by rw [clK_shape.1] at hs; cases hs)
        (by rw [clK_shape.2.1]; exact .cons (.ctor isMk_syms.2.2.2.1 .nil) .nil)
      cases hreq with
      | intro ht _ _ => rw [clK_shape.2.2.1] at ht; cases ht
      | pre h => rw [show clK.pre = .top by rfl] at h; exact absurd (Holds.top_eq h) (by simp)
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookup_isMk] at hfn
    cases hfn
    rw [isMk_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [clK_shape.2.2.2.2.1] at ht; cases ht
    · rw [clMk_shape.2.1] at ht; cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [lookup_isMk] at hfn
    cases hfn
    rw [isMk_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> exact absurd (by rfl) hne
  | exNone hfn hmem hne =>
    rw [lookup_isMk] at hfn
    cases hfn
    rw [isMk_clauses] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> exact absurd (by rfl) hne

/-- Where X is `k()`, the `requires` `isMk(X)` evaluates to `false`. -/
theorem req_false {σ : Subst} (hl : σ.lookup 2 = some (.ctor symK [])) :
    EvalTerm c σ (.app isMk [.var 2]) (some (bool false)) :=
  .call isMk_syms.1 isMk_syms.2.1 (.cons .var .nil) (by rw [hl]; rfl) eval_isMk_k isMk_syms.2.2.1

/-- There it has no other result. -/
theorem req_only {σ : Subst} (hl : σ.lookup 2 = some (.ctor symK [])) {r : Option GroundTerm}
    (h : EvalTerm c σ (.app isMk [.var 2]) r) : r = some (bool false) := by
  cases h with
  | ctor h _ => exact absurd h (by rw [isMk_syms.1]; decide)
  | hook h hhk _ _ _ => exact absurd hhk (by rw [isMk_syms.2.1]; decide)
  | param h hhk hp _ _ => exact absurd hp (by rw [isMk_syms.2.2.1]; decide)
  | call h hh hts hvs hf hp =>
    cases hts with
    | cons h1 hs1 =>
      cases h1
      cases hs1
      rw [hl] at hvs
      cases hvs
      exact isMk_k_only hf
  | callUndef h hh hts hvs hp =>
    cases hts with
    | cons h1 hs1 =>
      cases h1
      cases hs1
      rw [hl] at hvs
      cases hvs
  | ovl h ho _ => exact absurd ho (by decide +kernel)
  | ovlFn h ho => exact absurd ho (by decide +kernel)

/-! ## The rule 0 is not witnessed and does not apply at `a()` -/

/-- **The rule 0 is not `Witnessed`**: X is `k()` at every value, where `isMk(X)` is `false` only. -/
theorem not_witnessed0 : ¬ r0.Witnessed c := by
  rintro ⟨σ, hσ, hreq, -⟩
  obtain ⟨v, hl, hv⟩ := hσ 2 (by decide +kernel) sS (by rw [r0_vars]; rfl)
  rw [valS hv] at hl
  have := req_only hl (hreq _ r0_req)
  cases this

/-- The configuration `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def A : Config c := ⟨cfg (.ctor symA []), by decide +kernel⟩
def C : Config c := ⟨cfg (.ctor symC []), by decide +kernel⟩

/-- **The rule 0 does not apply at `<k> a() </k>`**: under every σ giving X a value of S, its
`requires` is `false`. -/
theorem notApplies0 : NotApplies c r0 A.val := by
  intro σ hσ _
  obtain ⟨v, hl, hv⟩ := hσ 2 (by decide +kernel) sS (by rw [r0_vars]; rfl)
  rw [valS hv] at hl
  exact .intro r0_req (req_false hl) (by decide)

/-! ## `Step a() c()`, and soundness under the owed fact -/

def σ1 : Subst := [(0, .ctor dotk []), (1, .ctor counterLabel [.dv Srt.int (.int 0)])]

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symA = true ∧ c.isCtor symC = true ∧ c.isCtor dotk = true ∧ c.isCtor counterLabel = true := by
  decide +kernel

/-- **`Step a() c()`** by the `[owise]` rule 1: the rule 0, of a smaller priority number, does not
apply. -/
theorem stepBy1 : StepBy c r1 σ1 A C where
  mem := by rw [rules_eq]; simp
  hσ := fun i s hs => by
    rw [r1_vars] at hs
    match i, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  hmatch := by
    rw [r1_lhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.1 .nil)) (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r1_req] at ht; cases ht
  hpre := by rw [r1_pre]; exact .top
  heval := by
    rw [r1_rhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.2.1 .nil)) (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r1_ens] at ht; cases ht
  hpost := by rw [r1_post]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact notApplies0
    · exact absurd hlt (Nat.lt_irrefl _)

theorem step_a_c : Step c A C := step_iff_by.mpr ⟨r1, σ1, stepBy1⟩

/-- **Soundness at `a() ⇒ c()` under the owed fact of rule 0** (`owed0`: its condition is decided,
`Witnessed` or `Refuted`): the pinned `sound_at`, its `hw` from `owed0`, its `hc` from no clause
needing a witness. -/
theorem sound_at_a_c_of_owed0 (owed0 : r0.CondDecided c) :
    (Γc c ⊧ (den c A.val ⇒ KoreAML.sNext (famEx c r1 σ1))) ∧ (Γc c ⊧ (den c C.val ⇒ famEx c r1 σ1)) :=
  sound_at c coreOK A C r1 σ1 stepBy1
    (fun r' hr' hlt _ _ => by
      rw [rules_eq] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact owed0
      · exact absurd hlt (Nat.lt_irrefl _))
    (fun fn hfn cl hcl hw => by
      have := List.all_eq_true.mp (List.all_eq_true.mp no_clause_owed fn hfn) cl hcl
      rw [hw] at this
      cases this)

/-- info: 'OpenFixtures.Genless.arm_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arm_C
/-- info: 'OpenFixtures.Genless.not_witnessed0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_witnessed0
/-- info: 'OpenFixtures.Genless.step_a_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_a_c
/--
info: 'OpenFixtures.Genless.sound_at_a_c_of_owed0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms sound_at_a_c_of_owed0

end Genless

namespace Unbound

definition_of defn from "f2-examples/unbound.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem rules_eq : c.rules = [r0] := by
  have h : c.rules.length = 1 := by decide +kernel
  match hr : c.rules, h with
  | [r], _ => simp only [r0, hr, List.getElem_cons_zero]
theorem r0_vars : r0.vars = [Srt.k, 19, Srt.int] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symA []), .var 0]], .var 1] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symB [.var 2]), .var 0]], .var 1] := rfl
theorem r0_req : r0.req = none := rfl
theorem r0_ens : r0.ens = none := rfl
theorem r0_pre : r0.pre = .top := rfl
theorem r0_post : r0.post = .top := rfl
theorem r0_exs : r0.exs = [] := rfl

/-- **The rule is read by arm A**: its open variable X (variable 2) is under the constructor b of
the right side; `rulePlainOpen` holds, `openRefusal` gives none, and it needs no witness. The
definition reads a confined sort (Int), so its theory is `Γc`. -/
theorem arm_A :
    r0.opens = [2] ∧ (ctorOccs c r0.rhs).contains 2 = true ∧ c.rulePlainOpen r0 = true ∧
    (Parse.openRefusal c r0 []).isNone = true ∧ r0.needsWitness c = false ∧
    c.readsConfined = true ∧ c.fns = [] := by
  decide +kernel

theorem shapesOK : c.shapesOK = true := by decide +kernel
theorem varOccs_lhs : varOccs r0.lhs = [0, 1] := by decide +kernel

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symA = true ∧ c.isCtor symB = true ∧ c.isCtor dotk = true ∧ c.isCtor counterLabel = true := by
  decide +kernel
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symA = false := by
  decide +kernel

/-! ## The configurations -/

/-- The configuration `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- A constructor application has the sort of another of the same constructor whose arguments have
the same sorts. -/
theorem sortOf_ctor_congr {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr {t t0 : GroundTerm} {ts : List GroundTerm} (h : c.sortOf t = c.sortOf t0) :
    c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congr {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symB).isSome = true := by
  decide +kernel

/-- `<k> b(v) </k>` is a configuration for every v of sort Int: its sort is that of `<k> b(0) </k>`,
layer by layer. -/
theorem sortOf_cfgB {v : GroundTerm} (hv : c.sortOf v = some Srt.int) :
    c.sortOf (cfg (.ctor symB [v])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symB [int 0])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congr lookups_ok.1 (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.1
    (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2.2.1 (sortsOf_head_congr (sortOf_inj_congr
      (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hv, sortOf_int]))) rfl))))))

def A : Config c := ⟨cfg (.ctor symA []), by decide +kernel⟩
/-- `<k> b(i) </k>`. -/
def B (i : Int) : Config c := ⟨cfg (.ctor symB [int i]), sortOf_cfgB (sortOf_int i)⟩

/-! ## The left side -/

/-- **What the left side denotes**: `<k> a() ~> w </k>` with the counter cell u, w and u the values
σ gives the variables 0 and 1. -/
theorem lhs_inv {σ : Subst} {x : GroundTerm} (h : PatVal c σ r0.lhs x) :
    ∃ w u, x = .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symA []), w]], u] ∧
      σ.lookup 0 = some w ∧ σ.lookup 1 = some u := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h syms_ok.1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨u, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  cases hvs2.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 syms_ok.2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 syms_ok.2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hooks_ok.2.2.2 ha syms_ok.2.2.2.1
  cases has.nil_inv
  exact ⟨w, u, rfl, PatVal.var_inv hz2, PatVal.var_inv h2⟩

/-! ## `Step` from `a()` to `b(i)`, for every Int i -/

def σA : Subst := [(0, .ctor dotk []), (1, .ctor counterLabel [.dv Srt.int (.int 0)])]
def σ (i : Int) : Subst := σA ++ [(2, int i)]

theorem hmatchA (τ : Subst) (h0 : τ.lookup 0 = some (.ctor dotk []))
    (h1 : τ.lookup 1 = some (.ctor counterLabel [.dv Srt.int (.int 0)])) : PatVal c τ r0.lhs A.val := by
  rw [r0_lhs]
  exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
    (.cons (.inj (.ctor syms_ok.2.2.2.1 .nil)) (.cons (.var h0) .nil))) .nil)) (.cons (.var h1) .nil))

/-- **`a()` steps to `b(i)`**, X := i. -/
theorem stepBy (i : Int) : StepBy c r0 (σ i) A (B i) where
  mem := by rw [rules_eq]; simp
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, sortOf_int i⟩
  hmatch := hmatchA _ rfl rfl
  hreq := fun t ht => by rw [r0_req] at ht; cases ht
  hpre := by rw [r0_pre]; exact .top
  heval := by
    rw [r0_rhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.2.1 (.cons .var .nil))) (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_ens] at ht; cases ht
  hpost := by rw [r0_post]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

theorem step (i : Int) : Step c A (B i) := step_iff_by.mpr ⟨r0, σ i, stepBy i⟩

/-- **In every model of `Γc`, `<k> a() </k>` has `<k> b(i) </k>` as a successor**, for every Int i. -/
theorem sound_b (i : Int) : Γc c ⊧ (den c A.val ⇒ KoreAML.sNext (den c (B i).val)) := by
  have hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
    intro fn hfn; rw [arm_A.2.2.2.2.2.2] at hfn; cases hfn
  obtain ⟨h1, -⟩ := sound_at c coreOK A (B i) r0 (σ i) (stepBy i)
    (fun r' hr' hlt _ _ => by
      rw [rules_eq] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact absurd hlt (Nat.lt_irrefl _)) hc
  have hcl : Γc c ⊧ (famEx c r0 (σ i) ≡ den c (B i).val) := famEx_closed c coreOK (stepBy i) r0_exs hc
  intro M _ I hI e m
  have hst := h1 hI e m
  rw [interpret_impl] at hst ⊢
  intro hx
  exact sNext_congr ((KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))).mp (hcl hI e m)) (hst hx)

/-! ## No other successor -/

/-- **Every `Step` successor of `<k> a() </k>` is a `<k> b(i) </k>`.** -/
theorem step_inv {y : Config c} (hs : Step c A y) : ∃ i : Int, y = B i := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hr := hb.mem
  rw [rules_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  obtain ⟨w, u, hx, h0, h1⟩ := lhs_inv hb.hmatch
  simp only [A, cfg, GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨v, h2, hv⟩ := hb.hσ 2 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨i, rfl⟩ := shape_int shapesOK hv
  refine ⟨i, Subtype.ext ?_⟩
  have h := hb.heval
  rw [r0_rhs] at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv syms_ok.1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  cases hrs2.nil_inv
  rw [hq2.var_inv, h1] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv syms_ok.2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  obtain ⟨ks, hks, rfl⟩ := EvalTerm.ctor_inv syms_ok.2.2.1 hp1
  obtain ⟨k1, ks1, rfl, hk1, hks1⟩ := hks.cons_inv
  obtain ⟨k2, ks2, rfl, hk2, hks2⟩ := hks1.cons_inv
  cases hks2.nil_inv
  rw [hk2.var_inv, h0] at he
  obtain ⟨b1, hb1, rfl⟩ := EvalTerm.inj_inv hk1
  obtain ⟨bs, hbs, rfl⟩ := EvalTerm.ctor_inv syms_ok.2.2.2.2.1 hb1
  obtain ⟨d1, ds1, rfl, hd1, hds1⟩ := hbs.cons_inv
  cases hds1.nil_inv
  rw [hd1.var_inv, h2] at he
  simp only [allSome, Option.bind, Option.map, injNormal, Option.some.injEq] at he
  exact he

/-! ## The outcomes: one family at `a()` -/

open Classical in
/-- The outcomes at x: the family of r0 at a match no rule blocks, where there is one; none
otherwise (the rule leaves X open, and no rule binds every variable). -/
noncomputable def refU (x : GroundTerm) : List Outcome :=
  if h : ∃ τ, Unblocked c r0 τ x then [.fam r0 h.choose] else []

theorem unblockedA : Unblocked c r0 σA A.val :=
  ⟨fun j hj s hs => by
    rw [varOccs_lhs] at hj
    rw [r0_vars] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · cases hs; exact ⟨_, rfl, by decide +kernel⟩
    · cases hs; exact ⟨_, rfl, by decide +kernel⟩,
   hmatchA _ rfl rfl,
   fun r' hr' hlt => by
     rw [rules_eq] at hr'
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
     subst hr'
     exact absurd hlt (Nat.lt_irrefl _)⟩

/-- **`refU` lists the outcomes** (`OutIs`): no value (the one rule leaves X open), and the family
of each unblocked match up to the values of the left side's variables 0 and 1. -/
theorem outIs : OutIs c refU := by
  intro x
  refine ⟨fun y => ?_, fun r τ hm => ?_, fun r hr _ τ hu => ?_⟩
  · constructor
    · intro hm
      unfold refU at hm
      split at hm <;> simp at hm
    · rintro ⟨hy, r, τ, hop, hb⟩
      have hr := hb.mem
      rw [rules_eq] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [arm_A.1] at hop
      cases hop
  · unfold refU at hm
    split at hm
    · rename_i h
      simp only [List.mem_cons, Outcome.fam.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨by rw [rules_eq]; simp, by rw [arm_A.1]; simp, h.choose_spec⟩
    · simp at hm
  · rw [rules_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have h : ∃ τ, Unblocked c r0 τ x.val := ⟨τ, hu⟩
    refine ⟨h.choose, fun j hj => ?_, by simp only [refU, h, ↓reduceDIte, List.mem_singleton]⟩
    obtain ⟨w, u, hx, h0, h1⟩ := lhs_inv hu.2.1
    obtain ⟨w', u', hx', h0', h1'⟩ := lhs_inv h.choose_spec.2.1
    rw [hx] at hx'
    simp only [GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    rw [varOccs_lhs] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [h0, h0']
    · rw [h1, h1']

/-- At `<k> a() </k>`, `refU` lists one family. -/
theorem refU_A : ∃ τ, refU A.val = [.fam r0 τ] :=
  ⟨_, by simp only [refU, (⟨σA, unblockedA⟩ : ∃ τ, Unblocked c r0 τ A.val), ↓reduceDIte]; rfl⟩

/-- **Completeness at `<k> a() </k>`** under `FnHyp`: with the step's closure, every successor is in
the one family. -/
theorem complete_A (hf : FnHyp c) :
    (Γc c ∪ Γstep c) ⊧ (den c A.val ⇒ KoreAML.allNext (KoreAML.disjList ((refU A.val).map (Outcome.pat c)))) :=
  complete_hyp c refU coreOK hf outIs A

/-- **By `ExactC`** (under `FnHyp`): a configuration y is a successor of `<k> a() </k>` in some model
of `Γc` with the step's closure exactly where y is some `<k> b(i) </k>`; so in no model is a value
other than a `b(i)` a successor. -/
theorem exact_b (hf : FnHyp c) (y : Config c) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧ ¬ (I ⊧ᴵ (den c A.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ↔
    ∃ i : Int, y = B i := by
  rw [← exact_hyp c coreOK hf A y]
  exact ⟨step_inv, fun ⟨i, hi⟩ => hi ▸ step i⟩

/-- info: 'OpenFixtures.Unbound.arm_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arm_A
/--
info: 'OpenFixtures.Unbound.stepBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms stepBy
/--
info: 'OpenFixtures.Unbound.sound_b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms sound_b
/--
info: 'OpenFixtures.Unbound.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms step_inv
/-- info: 'OpenFixtures.Unbound.outIs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outIs
/--
info: 'OpenFixtures.Unbound.exact_b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms exact_b

/-- **The Holds lemma at a condition with a binder**, `∃ B:Bool. ⊤`, in any model of `Γc`: the
definition reads a confined sort, so `holds_entails` reads the binders' facts (`binderFacts_of_core`);
the clause hypothesis is empty, the definition having no function. -/
theorem entails_ex {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hIc : I ⊧ᴵP Γc c) :
    HoldsShape.HoldsDen' c I (.ex Srt.bool .top) :=
  HoldsShape.holds_entails coreOK hIc
    (fun fn hfn => absurd hfn (by rw [arm_A.2.2.2.2.2.2]; exact List.not_mem_nil)) _
    fun _ => arm_A.2.2.2.2.2.1

/--
info: 'OpenFixtures.Unbound.entails_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms entails_ex

end Unbound

namespace Linked

/-- The refusals of the text at `path` (`Parse.refusals`), each with its reason and detail, or
"read". -/
def refusalsOf (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.refusals k with
    | [] => "read"
    | rs => String.intercalate "; " (rs.map fun r => s!"{r.reason.name} {r.detail}")

/--
info: openlinked: openRequires VarH:Int: in a closed condition that holds VarX:Int, which the right side, the ensures or post holds; of a sort the text leaves unconfined
openlinkedbool: openRequires VarH:Int: in a closed condition that holds VarB:Bool, which the right side, the ensures or post holds; of a sort the text leaves unconfined
-/
#guard_msgs in
#eval show IO Unit from do
  for n in ["openlinked", "openlinkedbool"] do
    IO.println s!"{n}: {← refusalsOf s!"f2-examples/{n}.kompile.kore"}"

end Linked

namespace Cool

definition_of defn from "f2-examples/rulecool.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 32
def isKResult : Sym := 383
def kCell : Sym := 384
def symA : Sym := 386
def symB : Sym := 387
def symC : Sym := 388
def andBool : Sym := 4
def notBool : Sym := 3

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName isKResult = "LblisKResult" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
noncomputable def r6 : Rule := c.rules[6]'(by decide +kernel)
noncomputable def r7 : Rule := c.rules[7]'(by decide +kernel)

theorem rules_len : c.rules.length = 9 := by decide +kernel

/-- The left side of the `[cool]` rule at 1 and of the `[heat]` rule at 2: `<k> c(n #as X) ~> R </k>`
with the counter cell. -/
def lhsAt (n : Int) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symC [.as (.dv Srt.int (.int n)) 0]), .var 1]], .var 2]

theorem r6_vars : r6.vars = [Srt.int, Srt.k, 19, Srt.k] := rfl
theorem r6_lhs : r6.lhs = lhsAt 1 := rfl
theorem r6_rhs : r6.rhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symB [.var 0]), .var 1]], .var 2] := rfl
theorem r6_req : r6.req = some (.app andBool [.dv Srt.bool (.bool true), .app isKResult [.var 3]]) := rfl
theorem r6_ens : r6.ens = none := rfl
theorem r6_pre : r6.pre = .top := rfl
theorem r6_post : r6.post = .top := rfl
theorem r7_vars : r7.vars = [Srt.int, Srt.k, 19, Srt.k] := rfl
theorem r7_lhs : r7.lhs = lhsAt 2 := rfl
theorem r7_req : r7.req = some (.app andBool [.dv Srt.bool (.bool true), .app notBool [.app isKResult [.var 3]]]) := rfl
theorem r7_pre : r7.pre = .top := rfl
theorem r1_lhs : r1.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symA [.var 0]), .var 1]], .var 2] := rfl

/-- **The `[cool]` and `[heat]` rules are read, and no rule is refused `openRequires`**: HOLE
(variable 3, of the unconfined sort K) is the one open variable of each, held by the `requires`
alone, a closed condition no variable of which the rest of the rule holds (arm C); each owes its
`CondDecided`, the account's two owed facts. -/
theorem arms :
    r6.opens = [3] ∧ r7.opens = [3] ∧ r6.condVars = [3] ∧ r7.condVars = [3] ∧
    c.rulePlainOpen r6 = true ∧ c.rulePlainOpen r7 = true ∧
    (c.rules.all fun r => (Parse.openRefusal c r []).isNone) = true ∧
    r6.needsWitness c = true ∧ r7.needsWitness c = true ∧
    Parse.owedCondDecided c = [(6, [3]), (7, [3])] := by
  decide +kernel

/-! ## The two conditions are witnessed -/

/-- `kseq(inj{Int,KItem}(0), dotk)`: a K whose one item is a `KResult`. -/
def holeCool : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem (int 0), .ctor dotk []]
/-- `dotk`: the empty K, not a `KResult`. -/
def holeHeat : GroundTerm := .ctor dotk []

theorem hole_sorts : c.sortOf holeCool = some Srt.k ∧ c.sortOf holeHeat = some Srt.k := by decide +kernel

/-- The configuration `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- The substitution of the `[cool]` and `[heat]` rules at `<k> c(n) </k>`, HOLE := h. -/
def σAt (n : Int) (h : GroundTerm) : Subst :=
  [(0, int n), (1, .ctor dotk []), (2, .ctor counterLabel [.dv Srt.int (.int 0)]), (3, h)]

theorem σAt_sorted {n : Int} {h : GroundTerm} (hh : c.sortOf h = some Srt.k) :
    c.WellSorted [Srt.int, Srt.k, 19, Srt.k] (σAt n h) := fun j s hs => by
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int n⟩
  | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 3, hs => cases hs; exact ⟨_, rfl, hh⟩

/-- The functions are the generated sort predicates (`fns` is empty), whose clauses `sortPreds_ctx`
reads: the executable evaluation is sound here although `ok` is false (an open rule variable). -/
theorem clauseCtx : Exec.ClauseCtx c := by
  have hf : c.fns = [] := by decide +kernel
  intro fn hfn'
  rcases List.mem_append.mp hfn' with hfn | hfn
  · rw [hf] at hfn; cases hfn
  · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl =>
      ⟨(sortPreds_ctx hfn cl hcl).1, (sortPreds_ctx hfn cl hcl).2.1, (sortPreds_ctx hfn cl hcl).2.2.1,
        (sortPreds_ctx hfn cl hcl).2.2.2.1, (sortPreds_ctx hfn cl hcl).2.2.2.2.1,
        (sortPreds_ctx hfn cl hcl).2.2.2.2.2, Semantics.sortPreds_pre hfn cl hcl,
        Semantics.sortPreds_exs hfn cl hcl, Semantics.sortPreds_post hfn cl hcl⟩⟩

theorem sortCtx : SortCtx c := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  exact sortCtx_of_all hok hsr (OvlOK.ovlCase hno)

theorem matchCtx : Exec.MatchCtx c := Exec.matchCtx_of (by decide +kernel)

/-- `true andBool isKResult(HOLE)` is `true` where HOLE is `holeCool`. -/
theorem reqCool : EvalTerm c (σAt 1 holeCool)
    (.app andBool [.dv Srt.bool (.bool true), .app isKResult [.var 3]]) (some (bool true)) :=
  Exec.evalT_sound sortCtx clauseCtx matchCtx 10 (by decide +kernel) (headsOK_fns c)
    (σAt_sorted hole_sorts.1) (s := Srt.bool) (by decide +kernel)

/-- `true andBool notBool isKResult(HOLE)` is `true` where HOLE is `holeHeat`. -/
theorem reqHeat : EvalTerm c (σAt 2 holeHeat)
    (.app andBool [.dv Srt.bool (.bool true), .app notBool [.app isKResult [.var 3]]]) (some (bool true)) :=
  Exec.evalT_sound sortCtx clauseCtx matchCtx 10 (by decide +kernel) (headsOK_fns c)
    (σAt_sorted hole_sorts.2) (s := Srt.bool) (by decide +kernel)

/-- **The `[cool]` rule is `Witnessed`**, HOLE := `kseq(inj{Int,KItem}(0), dotk)`. -/
theorem witnessed6 : r6.Witnessed c :=
  ⟨σAt 1 holeCool, fun i _ s hs => σAt_sorted hole_sorts.1 i s (by rw [← r6_vars]; exact hs),
   fun t ht => by rw [r6_req] at ht; cases ht; exact reqCool,
   by rw [r6_pre]; exact .top⟩

/-- **The `[heat]` rule is `Witnessed`**, HOLE := `dotk`. -/
theorem witnessed7 : r7.Witnessed c :=
  ⟨σAt 2 holeHeat, fun i _ s hs => σAt_sorted hole_sorts.2 i s (by rw [← r7_vars]; exact hs),
   fun t ht => by rw [r7_req] at ht; cases ht; exact reqHeat,
   by rw [r7_pre]; exact .top⟩

/-- The two owed facts the account lists hold. -/
theorem condDecided : r6.CondDecided c ∧ r7.CondDecided c := ⟨.inl witnessed6, .inl witnessed7⟩

/-! ## At `c(1)` the successor `b(1)`, by the `[cool]` rule -/

/-- The one rule of a priority number below the `[cool]` rule's (50) is the rule 1, `a(X) => c(X)`
at priority 10, and it needs no witness. -/
theorem prio_lt : ∀ i (hi : i < c.rules.length), c.rules[i].prio < 50 → i = 1 := by decide +kernel
theorem prio6 : r6.prio = 50 := by decide +kernel
theorem r1_noWitness : r1.needsWitness c = false := by decide +kernel

def C1 : Config c := ⟨cfg (.ctor symC [int 1]), by decide +kernel⟩
def B1 : Config c := ⟨cfg (.ctor symB [int 1]), by decide +kernel⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symB = true ∧ c.isCtor symC = true ∧ c.isCtor symA = true := by
  decide +kernel
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symA = false := by
  decide +kernel

/-- The rule of priority 10, `a(X) => c(X)`, does not apply at `<k> c(1) </k>`: its left side holds `a`. -/
theorem notApplies1 : NotApplies c r1 C1.val := by
  intro σ _ hm
  exfalso
  rw [r1_lhs] at hm
  obtain ⟨-, vs, hv, hvs⟩ := PatVal.app_inv hooks_ok.1 hm syms_ok.1
  obtain ⟨v1, vs1, rfl, h1, -⟩ := hvs.cons_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 syms_ok.2.1
  obtain ⟨w1, ws1, rfl, h11, -⟩ := hws.cons_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 syms_ok.2.2.1
  obtain ⟨z1, zs1, rfl, hz1, -⟩ := hzs.cons_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, -⟩ := PatVal.app_inv hooks_ok.2.2.2 ha syms_ok.2.2.2.2.2
  simp only [C1, cfg, GroundTerm.ctor.injEq, List.cons.injEq] at hv
  obtain ⟨-, ⟨-, ⟨-, hi, -⟩, -⟩, -⟩ := hv
  simp [injNormal, symA, symC] at hi

/-- **`c(1)` steps to `b(1)` by the `[cool]` rule**, HOLE := `holeCool`: the `StepBy`, by hand. -/
theorem stepBy6 : StepBy c r6 (σAt 1 holeCool) C1 B1 where
  mem := List.getElem_mem _
  hσ := fun j s hs => σAt_sorted hole_sorts.1 j s (by rw [← r6_vars]; exact hs)
  hmatch := by
    rw [r6_lhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.2.1 (.cons (.as .dv rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r6_req] at ht; cases ht; exact reqCool
  hpre := by rw [r6_pre]; exact .top
  heval := by
    rw [r6_rhs]
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (.inj (.ctor syms_ok.2.2.2.1 (.cons .var .nil))) (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r6_ens] at ht; cases ht
  hpost := by rw [r6_post]; exact .top
  hprio := fun r' hr' hlt => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr'
    obtain rfl := prio_lt i hi (prio6 ▸ hlt)
    exact notApplies1

theorem step_c_b : Step c C1 B1 := step_iff_by.mpr ⟨r6, σAt 1 holeCool, stepBy6⟩

/-- **In every model of `Γc`, `<k> c(1) </k>` has `<k> b(1) </k>` as a successor**: the pinned
`sound_at` at the `[cool]` step (no rule of a smaller priority number needs a witness, and there is
no clause), and `famEx_closed`. -/
theorem sound_c_b : Γc c ⊧ (den c C1.val ⇒ KoreAML.sNext (den c B1.val)) := by
  have hf : c.fns = [] := by decide +kernel
  have hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
    intro fn hfn; rw [hf] at hfn; cases hfn
  obtain ⟨h1, -⟩ := sound_at c coreOK C1 B1 r6 _ stepBy6
    (fun r' hr' hlt hw _ => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr'
      obtain rfl := prio_lt i hi (prio6 ▸ hlt)
      exact absurd hw (by rw [show c.rules[1] = r1 from rfl, r1_noWitness]; decide)) hc
  have hcl : Γc c ⊧ (famEx c r6 (σAt 1 holeCool) ≡ den c B1.val) :=
    famEx_closed c coreOK stepBy6 (by decide +kernel) hc
  intro M _ I hI e m
  have hst := h1 hI e m
  rw [interpret_impl] at hst ⊢
  intro hx
  exact sNext_congr ((KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))).mp (hcl hI e m)) (hst hx)

/-- info: 'OpenFixtures.Cool.arms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arms
/--
info: 'OpenFixtures.Cool.condDecided' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms condDecided
/-- info: 'OpenFixtures.Cool.step_c_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_c_b
/--
info: 'OpenFixtures.Cool.sound_c_b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms sound_c_b

end Cool

end OpenFixtures
