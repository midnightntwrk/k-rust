/-
  The fixture e3-eq-exists-bool (an equation with an existential variable of Bool, f not `total`): the
  clause the reader gives for its text and the results of `f`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxBool.lean`.

  `rule f(X) => ?B ensures ?B ==Bool notBool X`, f not `total`. kompile rejects `?B` on an equation
  (fixture `e3-eq-exists-bool-partial`), so the text exists in the `#Exists` spelling
  (`e3-eq-exists-partial-ml`): `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`, its axiom 131.

  From the sentence: `f(x)` is the set of the elements b of Bool with `b = notBool x`, so
  `f(true) = false` and `f(false) = true`, and nothing else.

  The statements are on `defn`, the definition the reader gives for the text
  (`f2-examples/e3-eq-exists-partial-ml.kompile.kore`), each for every hook interpretation H:
  - The clause read is `clF` (`read`): `[X:Bool, B:Bool]`, `exs [1]`, `rhs B`, `post B = notBool X`;
    `f` has no other clause and is not `total`.
  - `f_value`: `f(b)` has the result `notBool b`, by `Eval.clauseEx` at B := `notBool b`. The
    instance at the other value of Bool has `post` false: it gives nothing, and it is an instance
    that agrees with the result, not a result none (`inst_all`).
  - `f_alone`: `f(b)` has no other result. `f_true`, `f_true_alone`: the two at `true`.
  - `fnHyp`: `FnHyp` holds: `f` has a result at every argument of Bool, the clause has one result
    at each match where it decides (`res_eq`, `res_some`), and no condition is open.

  `ExClauseFixtures.CeFx` holds the facts the proofs share with the other fixtures of an equation
  read as one clause with existential variables (test/ExClauseFxBool.lean, test/ExClauseFxCtor.lean,
  test/ExClauseFxSuper.lean; a test file imports no test file, so each repeats them).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.CeFx

open GroundTerm

/-- What a semantics reads of its symbols and sorts does not depend on the hook interpretation. -/
theorem isCtor_wh (d : Semantics) (H : HookParams) (f : Sym) : (d.withHooks H).isCtor f = d.isCtor f := rfl
theorem shapesOK_wh (d : Semantics) (H : HookParams) : (d.withHooks H).shapesOK = d.shapesOK := rfl
theorem fns_wh (d : Semantics) (H : HookParams) : (d.withHooks H).fns = d.fns := rfl
theorem params_wh (d : Semantics) (H : HookParams) : (d.withHooks H).params = d.params := rfl
theorem rules_wh (d : Semantics) (H : HookParams) : (d.withHooks H).rules = d.rules := rfl

variable {d : Semantics} {σ : Subst}

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem sameResult_self (v : GroundTerm) : sameResult (some v) (some v) = true := sameResult_some.mpr rfl

theorem sameResult_eq_some {r : Option GroundTerm} {v : GroundTerm} (h : sameResult r (some v) = true) :
    r = some v := by
  cases r with
  | none => cases h
  | some w => rw [sameResult_some.mp h]

theorem holds_cast {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' :=
  e ▸ h

/-- The instances of a clause whose one existential variable is the variable 1: σ with it set. -/
theorem agree_set1 (σ : Subst) (w : GroundTerm) : AgreeOff [1] σ ((1, w) :: σ) := fun i hi =>
  lkNe w σ (fun h => hi (by rw [h]; exact List.mem_singleton_self _))

/-- A substitution giving the variables 0 and 1 values of the two sorts is well sorted. -/
theorem sorted2 {a b : Srt} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some b) : d.WellSorted [a, b] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | i + 2, hs => simp at hs

/-- An application of an interpreted hooked symbol has the value `hookRes` gives at its arguments'
results, and none where an argument has none. -/
theorem hook_inv {f : Sym} {ts : List Term} {r : Option GroundTerm} (hc : d.isCtor f = false)
    (hk : isHook f = true) (h : EvalTerm d σ (.app f ts) r) :
    ∃ rs, EvalTerms d σ ts rs ∧ (∀ vs, allSome rs = some vs → d.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | hook _ _ hts hh hund => cases ht; exact ⟨_, hts, hh, hund⟩
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | param _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hk] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | ovl _ ho _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | _ => cases ht

/-- The results of two terms. -/
theorem terms2_inv {t u : Term} {rs : List (Option GroundTerm)} (h : EvalTerms d σ [t, u] rs) :
    ∃ r r', rs = [r, r'] ∧ EvalTerm d σ t r ∧ EvalTerm d σ u r' := by
  obtain ⟨r, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv h
  obtain ⟨r', rs'', rfl, h2, hs'⟩ := EvalTerms.cons_inv hs
  obtain rfl := EvalTerms.nil_inv hs'
  exact ⟨r, r', rfl, h1, h2⟩

/-- A function with one clause has no pair of clauses to agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

end ExClauseFixtures.CeFx

namespace ExClauseFixtures.ExBool

open GroundTerm ExClauseFixtures.CeFx

definition_of defn from "f2-examples/e3-eq-exists-partial-ml.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384

/-- `f(X) => B` with `exs = [B]` and `post := B = notBool X`, X and B of Bool. -/
def clF : Clause :=
  { vars := [Srt.bool, Srt.bool], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.bool (.var 1) (.app boolNot [.var 0]) }

def fnF : Fn := { label := fF, args := [Srt.bool], result := Srt.bool, clauses := [clF] }

/-- **The reading**: the text's one function is `f`, with the one clause `clF`. -/
theorem read : c.fns = [fnF] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName boolNot = "LblnotBool'Unds'" ∧
    c.sortName Srt.bool = "Bool" := by decide +kernel

/-- B is of the confined sort Bool: the clause is one `clausePlainEx` admits. -/
theorem plainEx : c.confined Srt.bool = true ∧ c.clausePlainEx clF = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noRules : c.rules = [] := by decide +kernel
theorem shapes : c.shapesOK = true := by decide +kernel

/-! ### The clause in a semantics that reads it -/

section Clause

variable {d : Semantics} {σ : Subst}

theorem notHook : isHook boolNot = true := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation (domains.md 1138, 1139). -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

theorem evalNot (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    EvalTerm d σ (.app boolNot [.var 0]) (some (bool (!b))) :=
  .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalNot_inv (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    {r : Option GroundTerm} (h : EvalTerm d σ (.app boolNot [.var 0]) r) : r = some (bool (!b)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  have := hh [bool b] (by rw [h0]; rfl)
  rw [hookNot] at this
  exact (Option.some.inj this).symm

/-- The clause's `post` at a match giving X the value b: whether B's value is `notBool b`. -/
theorem post_holds (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    Holds d 2 σ clF.post (sameResult (σ.lookup 1) (some (bool (!b)))) :=
  Holds.equals .var (evalNot hc h0)

theorem post_inv (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) {t : Bool}
    (h : Holds d 2 σ clF.post t) : t = sameResult (σ.lookup 1) (some (bool (!b))) := by
  cases h with
  | equals h1 h2 =>
    obtain rfl := EvalTerm.var_inv h1
    obtain rfl := evalNot_inv hc h0 h2
    rfl

/-- **Every instance is decided and gives `notBool b` or nothing**: at B := `notBool b` it gives
it, at the other value of Bool its `post` is false. -/
theorem inst_all (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (hw : d.WellSorted clF.vars σ) : InstIs d σ clF (some (bool (!b))) := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.bool rfl
  cases hb : sameResult (some w) (some (bool (!b))) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds hc h0) (by rw [hw1, hb]))
  | false => exact .fails (post_holds hc h0) (.post (holds_cast (post_holds hc h0) (by rw [hw1, hb])))

/-- The instance at B := `notBool b` does not give nothing. -/
theorem inst_not_none (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (h1 : σ.lookup 1 = some (bool (!b))) : ¬ InstIs d σ clF none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := post_inv hc h0 hp
      rw [h1, sameResult_self] at e
      cases e
    | rhs h => have := EvalTerm.var_inv h; rw [h1] at this; cases this

/-- σ with B := `notBool b` is an instance of the clause at σ, well sorted where σ gives X the
value b. -/
theorem ext_sorted {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    d.WellSorted clF.vars ((1, bool (!b)) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) (rmS_sortOf_bool d b) (lkSelf _ _ _) (rmS_sortOf_bool d (!b))

theorem ext_agree (σ : Subst) (w : GroundTerm) : AgreeOff clF.exsFree σ ((1, w) :: σ) := agree_set1 σ w

/-- An instance at σ gives X the value σ gives it. -/
theorem agree_x {σ' : Subst} (h : AgreeOff clF.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by decide)

/-- **The clause has the one result `notBool b` at a match giving X the value b.** -/
theorem res_eq (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    {r : Option GroundTerm} (h : Clause.Res d clF σ r) : r = some (bool (!b)) := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, ha, -, ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex (by decide)
  · have h0' := (agree_x ha).trans h0
    have e := post_inv hc h0' hpost
    rw [← EvalTerm.var_inv hrhs] at e
    rw [sameResult_some.mp e.symm]
  · exact absurd (hall _ (ext_agree σ _) (ext_sorted h0))
      (inst_not_none hc ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

theorem res_some (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    Clause.Res d clF σ (some (bool (!b))) :=
  have h0' : ((1, bool (!b)) :: σ : Subst).lookup 0 = some (bool b) := (lkNe _ _ (by decide)).trans h0
  .inr ⟨by decide, .inl ⟨(1, bool (!b)) :: σ, bool (!b), ext_agree σ _, ext_sorted h0,
    ⟨(lkSelf 1 (bool (!b)) σ) ▸ .var, (fun t ht => nomatch ht),
      holds_cast (post_holds hc h0') (by rw [lkSelf, sameResult_self])⟩,
    fun σ'' ha hw => inst_all hc ((agree_x ha).trans h0) hw, rfl⟩⟩

/-- **`f(b)` is `notBool b`**, by `Eval.clauseEx` at B := `notBool b`. -/
theorem value (hc : d.isCtor boolNot = false) (hfn : d.lookupFn fF = some fnF) (b : Bool) :
    Eval d fF [bool b] (some (bool (!b))) :=
  have h0 : ([(1, bool (!b)), (0, bool b)] : Subst).lookup 0 = some (bool b) := rfl
  .clauseEx (fn := fnF) (cl := clF) (σ := [(1, bool (!b)), (0, bool b)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d (!b))) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (post_holds hc h0) (sameResult_self _))
    (fun σ' ha hw => inst_all hc ((agree_x ha).trans h0) hw)

/-- **`f(b)` has no other result.** -/
theorem alone (hc : d.isCtor boolNot = false) (hfn : d.lookupFn fF = some fnF) {b : Bool}
    {r : Option GroundTerm} (h : Eval d fF [bool b] r) : r = some (bool (!b)) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnF] using h2
  have hx : ∀ {σ : Subst}, PatVals d σ clF.pats [bool b] → σ.lookup 0 = some (bool b) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clF.vars [(1, bool b), (0, bool b)] :=
        sorted2 rfl (rmS_sortOf_bool d b) rfl (rmS_sortOf_bool d b)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have e := post_inv hc (hx hmatch) hpost
    rw [← EvalTerm.var_inv hrhs] at e
    rw [sameResult_some.mp e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx hmatch
    exact absurd (hall _ (ext_agree σ _) (ext_sorted h0))
      (inst_not_none hc ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

/-- The value a match of the clause gives X is a value of Bool, in a semantics where the values of
Bool are its literals. -/
theorem applies_x (hs : d.shapesOK = true) {vs : List GroundTerm} (h : clF.AppliesAt d σ vs) :
    ∃ b, σ.lookup 0 = some (bool b) := by
  obtain ⟨w, hw, hws⟩ := h.1 0 (by decide) Srt.bool rfl
  obtain ⟨b, rfl⟩ := shape_bool hs hws
  exact ⟨b, hw⟩

/-- **`FnHyp`** of a semantics whose one function is `f` with the clause `clF`, without rules and
open generators, where the values of Bool are its literals. -/
theorem fnHyp_of (hc : d.isCtor boolNot = false) (hfns : d.fns = [fnF]) (hfn : d.lookupFn fF = some fnF)
    (hs : d.shapesOK = true) (hrules : d.rules = []) (hraw : ∀ k ∈ d.params, k.raw = false) : FnHyp d := by
  have hmem : ∀ {fn}, fn ∈ d.fns → fn = fnF := fun h => by rw [hfns] at h; simpa using h
  refine ⟨fun fn hf vs hvs => ?_, fun fn hf ht => ?_, fun fn hf => ?_, fun fn hf cl hcl => ?_,
    openDecided_of_plain (fun r hr => by rw [hrules] at hr; cases hr) (fun fn hf cl hcl => ?_),
    openLaws_of_plain hraw⟩
  · obtain rfl := hmem hf
    obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
    obtain ⟨b, rfl⟩ := shape_bool hs hw
    exact ⟨_, value hc hfn b⟩
  · obtain rfl := hmem hf; cases ht
  · obtain rfl := hmem hf; exact agree_one rfl
  · obtain rfl := hmem hf
    obtain rfl : cl = clF := by simpa [fnF] using hcl
    refine ⟨fun vs σ σ' ha ha' _ _ _ _ _ => .inr fun r r' hr hr' => ?_, fun _ _ _ _ σ _ _ hdec => ?_⟩
    · obtain ⟨b, hb⟩ := applies_x hs ha
      obtain ⟨b', hb'⟩ := applies_x hs ha'
      obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv ha.2.1
      obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv ha'.2.1
      cases hvs
      have e : bool b = bool b' := Option.some.inj
        (hb.symm.trans ((PatVal.var_inv hv).trans ((PatVal.var_inv hv').symm.trans hb')))
      obtain rfl : b = b' := by simpa [KCore.bool] using e
      rw [res_eq hc hb hr, res_eq hc hb' hr']
    · obtain ⟨b, hb⟩ := applies_x hs hdec.1
      exact ⟨_, res_some hc hb⟩
  · obtain rfl := hmem hf
    obtain rfl : cl = clF := by simpa [fnF] using hcl
    rfl

end Clause

/-! ### The expectations, for every H -/

theorem notCtorH (H : HookParams) : (cH H).isCtor boolNot = false := (isCtor_wh c H _).trans notCtor
theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some fnF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

/-- **`f(b) = notBool b`, for every H.** -/
theorem f_value (H : HookParams) (b : Bool) : Eval (cH H) fF [bool b] (some (bool (!b))) :=
  value (notCtorH H) (lookupFH H) b

/-- **`f(b)` has no other result, for every H.** -/
theorem f_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) fF [bool b] r) :
    r = some (bool (!b)) :=
  alone (notCtorH H) (lookupFH H) h

/-- **`f(true) = false`, for every H.** -/
theorem f_true (H : HookParams) : Eval (cH H) fF [bool true] (some (bool false)) := f_value H true

/-- **`f(true)` has no result but `false`, for every H**: not `true`, and not none. -/
theorem f_true_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fF [bool true] r) :
    r = some (bool false) := f_alone H h

/-- **`FnHyp` holds, for every H.** -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of (notCtorH H) ((fns_wh c H).trans read) (lookupFH H) ((shapesOK_wh c H).trans shapes)
    ((rules_wh c H).trans noRules) (fun k hk => noRaw k ((params_wh c H) ▸ hk))

end ExClauseFixtures.ExBool

/-- info: 'ExClauseFixtures.ExBool.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.ExBool.read
/-- info: 'ExClauseFixtures.ExBool.f_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExBool.f_value
/-- info: 'ExClauseFixtures.ExBool.f_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExBool.f_alone
/-- info: 'ExClauseFixtures.ExBool.f_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExBool.f_true
/-- info: 'ExClauseFixtures.ExBool.f_true_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExBool.f_true_alone
/-- info: 'ExClauseFixtures.ExBool.fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExBool.fnHyp
