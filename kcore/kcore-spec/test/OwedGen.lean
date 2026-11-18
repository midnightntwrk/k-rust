/-
  What `kcore gen --core` states for a text that owes a `CondDecided`, applied on the reader's
  semantics of two fixtures (their kompiled texts in f2-examples; the generated packages' text is
  checked by `test/owed-gen.sh`). Run from the package root:
  `lake env lean -j1 test/OwedGen.lean`. Kernel-checked (`decide +kernel`).

  The generated package of such a text states `owed_rules`, `owed_clauses`, `Obl := FnFacts …` with
  `obl_nil`, `Owed := OpenDecided defn.sem`, `sound_defn (how : Owed) : SoundC defn.sem :=
  sound_fn … (obl_nil.obligations how)` and `consistent := consistent_of_fnFacts …`. Here the same
  terms are built at the two texts, at the call order the generator computes (`[]` for e2-rule,
  which has no function with equations; `[isMk]` for e2-open-genless); neither has a parameter
  symbol.

  - `Cool` (e2-rule, `f2-examples/rulecool.kompile.kore`): `owedRules = [6, 7]`, the `[cool]` and
    `[heat]` rules, whose `requires` is closed over HOLE:K; no clause is owed. Both rules are
    `Witnessed` (HOLE := `kseq(inj{Int,KItem}(0), dotk)` and HOLE := `dotk`), so `Owed` holds
    (`owed`, by `openRules_of_owed` and `openClauses_of_owed` from the two lists), and with it
    `sound_fn` gives `SoundC c` (`sound`) and `FnHyp c` (`fnHyp`): the hypothesis set the generator
    states is discharged at a text with rules that need a witness.
  - `Genless` (e2-open-genless, `f2-examples/opengenless.kompile.kore`): `owedRules = [0]`, the
    rule `a() => b() requires isMk(X:S)`, S a sort of which every value is `k()`. `Consistent c`
    holds with no owed condition read (`consistent`, by `consistent_of_fnFacts`). The rule 0 is not
    `Witnessed` (`not_witnessed0`: at the one value of S, `isMk` is `false` only), so `Owed` holds
    exactly where the theory refutes the condition (`owed_iff_refuted`). Neither `Owed` nor its
    negation is shown: no model of `Γc` with an element of S at which `isMk` is true is built.
  The witnesses and the values of S are those of `test/OpenFixtures.lean` (sections `Cool`,
  `Genless`), repeated here since a test file imports the library only.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace OwedGen

namespace Cool

definition_of defn from "f2-examples/rulecool.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def sExp : Srt := 32
def isKResult : Sym := 383
def kCell : Sym := 384
def andBool : Sym := 4
def notBool : Sym := 3

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName isKResult = "LblisKResult" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

noncomputable def r6 : Rule := c.rules[6]'(by decide +kernel)
noncomputable def r7 : Rule := c.rules[7]'(by decide +kernel)

theorem r6_vars : r6.vars = [Srt.int, Srt.k, 19, Srt.k] := rfl
theorem r6_req : r6.req = some (.app andBool [.dv Srt.bool (.bool true), .app isKResult [.var 3]]) := rfl
theorem r6_pre : r6.pre = .top := rfl
theorem r7_vars : r7.vars = [Srt.int, Srt.k, 19, Srt.k] := rfl
theorem r7_req : r7.req = some (.app andBool [.dv Srt.bool (.bool true), .app notBool [.app isKResult [.var 3]]]) := rfl
theorem r7_pre : r7.pre = .top := rfl

/-- **The owed conditions**, as the generated `owed_rules` and `owed_clauses` state them: the
`[cool]` and `[heat]` rules, and no clause. The text is not `plain`. -/
theorem owed_rules : c.owedRules = [6, 7] := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel
theorem not_plain : c.plain = false := by decide +kernel

/-! ## The two conditions are witnessed -/

/-- `kseq(inj{Int,KItem}(0), dotk)`: a K whose one item is a `KResult`. -/
def holeCool : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem (int 0), .ctor dotk []]
/-- `dotk`: the empty K, not a `KResult`. -/
def holeHeat : GroundTerm := .ctor dotk []

theorem hole_sorts : c.sortOf holeCool = some Srt.k ∧ c.sortOf holeHeat = some Srt.k := by decide +kernel

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
      let ⟨h1, h2, h3, h4, h5, h6⟩ := sortPreds_ctx hfn cl hcl
      ⟨h1, h2, h3, h4, h5, h6, Semantics.sortPreds_pre hfn cl hcl, Semantics.sortPreds_exs hfn cl hcl,
        Semantics.sortPreds_post hfn cl hcl⟩⟩

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

/-! ## The generated hypothesis set, discharged -/

/-- The generated `Obl` and `Owed` at this text. -/
abbrev Obl : Prop := FnFacts c [] []
abbrev Owed : Prop := OpenDecided c

/-- The generated `obl_nil`: no fact about a function or the interpretation is named. -/
theorem obl_nil : Obl :=
  FnFacts.of_nil (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **`Owed` holds at e2-rule**: the two owed rules, one by one, from their witnesses
(`openRules_of_owed` at `owed_rules`), and no owed clause (`openClauses_of_owed` at
`owed_clauses`). -/
theorem owed : Owed :=
  ⟨openRules_of_owed (by
      rw [owed_rules]
      intro j hj r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · cases (show some r6 = some r from (rfl : c.rules[6]? = some r6).symm.trans hr)
        exact Or.inl witnessed6
      · cases (show some r7 = some r from (rfl : c.rules[7]? = some r7).symm.trans hr)
        exact Or.inl witnessed7),
   openClauses_of_owed (by rw [owed_clauses]; intro p hp; cases hp)⟩

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)

/-- **Soundness of e2-rule's semantics**: the generated `sound_defn (how : Owed)`, its term
(`sound_fn` at `obl_nil.obligations how`) applied at `owed`. -/
theorem sound : SoundC c := sound_fn c [] [] coreOK rightHeld ParamsTotal.nil (obl_nil.obligations owed)

/-- **`FnHyp` of e2-rule's semantics**: the generated `fnHyp_defn (how : Owed)` at `owed`. -/
theorem fnHyp : FnHyp c := fnHyp_of_fnObligations coreOK rightHeld ParamsTotal.nil (obl_nil.obligations owed)

/-- The generated `consistent`: no owed condition is read. -/
theorem consistent : Consistent c := consistent_of_fnFacts coreOK rightHeld obl_nil

/-- info: 'OwedGen.Cool.owed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms owed
/-- info: 'OwedGen.Cool.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound
/-- info: 'OwedGen.Cool.fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnHyp

end Cool

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

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_req : r0.req = some (.app isMk [.var 2]) := rfl
theorem r0_vars : r0.vars = [Srt.k, 19, sS] := rfl

/-- **The owed conditions**, as the generated `owed_rules` and `owed_clauses` state them: the rule
0, and no clause. The text is not `plain`. -/
theorem owed_rules : c.owedRules = [0] := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel
theorem not_plain : c.plain = false := by decide +kernel

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
    (fun j s hs => ?_) ?_ (fun t ht => ?_) .top (fun cl' hcl' _ hlt => ?_) (by rfl) ?_ (fun t ht => ?_)
    (Clause.holds_postTop (by rfl) _)
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
      | pre h => rw [show clK.pre = .top from rfl] at h; cases h
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

/-! ## The rule 0 is not witnessed -/

/-- **The rule 0 is not `Witnessed`**: X is `k()` at every value, where `isMk(X)` is `false` only. -/
theorem not_witnessed0 : ¬ r0.Witnessed c := by
  rintro ⟨σ, hσ, hreq, -⟩
  obtain ⟨v, hl, hv⟩ := hσ 2 (by decide +kernel) sS (by rw [r0_vars]; rfl)
  rw [valS hv] at hl
  have := req_only hl (hreq _ r0_req)
  cases this


/-! ## The generated hypothesis set -/

/-- The generated `Obl` and `Owed` at this text; `[isMk]` is the generated `callOrder`. -/
abbrev Obl : Prop := FnFacts c [isMk] []
abbrev Owed : Prop := OpenDecided c

/-- The generated `obl_nil`: no fact about a function or the interpretation is named. -/
theorem obl_nil : Obl :=
  FnFacts.of_nil (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)

/-- **The theory of e2-open-genless has a model**: the generated `consistent`, which reads no owed
condition, at a text whose owed condition is not witnessed. -/
theorem consistent : Consistent c := consistent_of_fnFacts coreOK rightHeld obl_nil

/-- **`Owed` holds at e2-open-genless exactly where the theory refutes the rule 0's condition**:
the one owed rule is not `Witnessed`, and no clause is owed. So the generated `sound_defn`,
`complete_defn` and `fnHyp_defn` state something of this text only if `Γc` excludes an element of
S at which `isMk` is true. -/
theorem owed_iff_refuted : Owed ↔ r0.Refuted c := by
  constructor
  · intro h
    have hmem : r0 ∈ c.rules := by unfold r0; exact List.getElem_mem _
    have hn : r0.needsWitness c = true := by decide +kernel
    have h0 : r0.CondDecided c := h.1 r0 hmem hn
    exact @Or.resolve_left (r0.Witnessed c) (r0.Refuted c) h0 not_witnessed0
  · intro h
    exact ⟨openRules_of_owed (by
        rw [owed_rules]
        intro j hj r hr
        cases List.mem_singleton.mp hj
        cases (show some r0 = some r from (rfl : c.rules[0]? = some r0).symm.trans hr)
        exact Or.inr h),
      openClauses_of_owed (by rw [owed_clauses]; intro p hp; cases hp)⟩

/-- info: 'OwedGen.Genless.not_witnessed0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_witnessed0
/-- info: 'OwedGen.Genless.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistent
/-- info: 'OwedGen.Genless.owed_iff_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms owed_iff_refuted

end Genless

end OwedGen
