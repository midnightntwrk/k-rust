/-
  The fixture e3-eq-exists-ml-and-right
  (`rule f(X) => (notBool X) #And (#Exists B:Bool. (B #And {B #Equals X}))`, f `[function]`, not
  `total`): the clause the reader gives for its text and the results of f, for every hook
  interpretation. Run from the package root: `lake env lean -j1 test/ExClauseFxAndRight.lean`.

  The text is `f2-examples/e3-eq-exists-ml-and-right.kompile.kore`; sentence 131 (`AxiomDecl.index`)
  is f's equation.

  From the sentence: f(x) is the intersection of {notBool x} and {B of Bool | B = x}, which is
  empty at every x: the conjuncts differ everywhere.

  The statements are on `defn`, the definition the reader gives for the text, each for every H:
  - The clause read is `clF` (`read`): the binder hoisted over the conjunction, B holding the
    position: `[X:Bool, B:Bool]`, `exs [1]`, `rhs B`, `post (B = X) ∧ (B ∈ notBool(X))`.
  - `f_none`, `f_none_alone`: `f(b)` has the result none, by `Eval.exNone` (every instance has
    `post` false: no value of Bool is both b and `notBool b`), and no other result; `f_true_none`,
    `f_true_none_alone` at true.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

namespace ExClauseFixtures.AndRight

open GroundTerm

definition_of defn from "f2-examples/e3-eq-exists-ml-and-right.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384

/-- `f(X) => B` with `exs = [B]` and `post := (B = X) ∧ (B ∈ notBool X)`, X and B of Bool. -/
def clF : Clause :=
  { vars := [Srt.bool, Srt.bool], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .and (.equals Srt.bool (.var 1) (.var 0)) (.mem Srt.bool (.var 1) (.app boolNot [.var 0])) }

def fnF : Fn := { label := fF, args := [Srt.bool], result := Srt.bool, clauses := [clF] }

/-- **The reading**: the text's one function is `f`, with the one clause `clF`. -/
theorem read : c.fns = [fnF] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName boolNot = "LblnotBool'Unds'" := by decide +kernel

/-- B is of the confined Bool: `clausePlainEx` admits the clause. -/
theorem plainEx : c.confined Srt.bool = true ∧ c.clausePlainEx clF = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false := by decide +kernel

section Clause

variable {d : Semantics} {σ : Subst}

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem holds_cast {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' :=
  e ▸ h

theorem agree_set1 (σ : Subst) (w : GroundTerm) : AgreeOff [1] σ ((1, w) :: σ) := fun i hi =>
  lkNe w σ (fun h => hi (by rw [h]; exact List.mem_singleton_self _))

theorem notHook : isHook boolNot = true := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation. -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

theorem evalNot (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b)) :
    EvalTerm d σ (.app boolNot [.var 0]) (some (bool (!b))) :=
  .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)

/-- The truth value of the clause's `post` where X is b and B is w. -/
def postVal (b : Bool) (w : GroundTerm) : Bool :=
  sameResult (some w) (some (bool b)) && sameResult (some w) (some (bool (!b)))

/-- No value of Bool is both b and `notBool b`. -/
theorem postVal_false (b : Bool) (w : GroundTerm) : postVal b w = false := by
  cases h : postVal b w with
  | false => rfl
  | true =>
    simp only [postVal, Bool.and_eq_true] at h
    have e := (sameResult_some.mp h.1).symm.trans (sameResult_some.mp h.2)
    cases b <;> simp [KCore.bool] at e

theorem post_holds (hc : d.isCtor boolNot = false) {b : Bool} {w : GroundTerm}
    (h0 : σ.lookup 0 = some (bool b)) (h1 : σ.lookup 1 = some w) : Holds d 2 σ clF.post (postVal b w) := by
  refine holds_cast (Holds.and (Holds.equals .var .var) (Holds.mem .var (evalNot hc h0))) ?_
  rw [h0, h1]; rfl

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

theorem evalNot_inv (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    {r : Option GroundTerm} (h : EvalTerm d σ (.app boolNot [.var 0]) r) : r = some (bool (!b)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain rfl := EvalTerms.nil_inv hs
  obtain rfl := EvalTerm.var_inv h1
  have := hh [bool b] (by rw [h0]; rfl)
  rw [hookNot] at this
  exact (Option.some.inj this).symm

theorem post_inv (hc : d.isCtor boolNot = false) {b : Bool} {w : GroundTerm}
    (h0 : σ.lookup 0 = some (bool b)) (h1 : σ.lookup 1 = some w) {t : Bool}
    (h : Holds d 2 σ clF.post t) : t = postVal b w := by
  cases h with
  | and ha hb =>
    cases ha with
    | equals ha1 ha2 =>
      cases hb with
      | mem hb1 hb2 =>
        obtain rfl := EvalTerm.var_inv ha1
        obtain rfl := EvalTerm.var_inv ha2
        obtain rfl := EvalTerm.var_inv hb1
        obtain rfl := evalNot_inv hc h0 hb2
        rw [h0, h1]; rfl

/-- `post` holds at no instance. -/
theorem post_not_true (hc : d.isCtor boolNot = false) {b : Bool} {w : GroundTerm}
    (h0 : σ.lookup 0 = some (bool b)) (h1 : σ.lookup 1 = some w) : ¬ Holds d 2 σ clF.post true := by
  intro h
  have e := post_inv hc h0 h1 h
  rw [postVal_false] at e; cases e

/-- **Every instance is decided and gives nothing.** -/
theorem inst_all (hc : d.isCtor boolNot = false) {b : Bool} (h0 : σ.lookup 0 = some (bool b))
    (hw : d.WellSorted clF.vars σ) (r : Option GroundTerm) : InstIs d σ clF r := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.bool rfl
  exact .fails (post_holds hc h0 hw1) (.post (holds_cast (post_holds hc h0 hw1) (postVal_false b w)))

theorem agree_x {σ' : Subst} (h : AgreeOff clF.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

/-- **`f(b)` has the result none**, by `Eval.exNone`. -/
theorem none_at (hc : d.isCtor boolNot = false) (hfn : d.lookupFn fF = some fnF) (b : Bool) :
    Eval d fF [bool b] none :=
  .exNone (fn := fnF) (cl := clF) (σ := [(0, bool b)]) hfn (List.mem_singleton_self _) (by decide)
    (fun i hi s hs => by
      have : i = 0 := by simp [Clause.univ, clF] at hi; omega
      subst this; cases hs; exact ⟨bool b, rfl, rmS_sortOf_bool d b⟩)
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    ⟨[(1, bool b), (0, bool b)], agree_set1 _ _, fun i s hs => by
      match i, hs with
      | 0, hs => cases hs; exact ⟨bool b, rfl, rmS_sortOf_bool d b⟩
      | 1, hs => cases hs; exact ⟨bool b, rfl, rmS_sortOf_bool d b⟩
      | i + 2, hs => simp [clF] at hs⟩
    (fun σ' ha hw => inst_all hc ((agree_x ha).trans rfl) hw none)

/-- **`f(b)` has no other result**: no instance gives a value, and the clause applies. -/
theorem alone (hc : d.isCtor boolNot = false) (hfn : d.lookupFn fF = some fnF) {b : Bool}
    {r : Option GroundTerm} (h : Eval d fF [bool b] r) : r = none := by
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
      have hs : d.WellSorted clF.vars [(1, bool b), (0, bool b)] := fun i s hs => by
        match i, hs with
        | 0, hs => cases hs; exact ⟨bool b, rfl, rmS_sortOf_bool d b⟩
        | 1, hs => cases hs; exact ⟨bool b, rfl, rmS_sortOf_bool d b⟩
        | i + 2, hs => simp [clF] at hs
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | @clauseEx _ _ _ _ σ v hfn' hmem hσ hmatch _ _ _ _ _ _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨w, hw1, -⟩ := hσ 1 Srt.bool rfl
    exact absurd hpost (post_not_true hc (hx hmatch) hw1)
  | exNone => rfl

end Clause

/-! ### The expectations, for every H -/

theorem notCtorH (H : HookParams) : (cH H).isCtor boolNot = false := notCtor
theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some fnF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

/-- **`f(b)` has the result none, for every H**: the conjuncts `notBool b` and b differ. -/
theorem f_none (H : HookParams) (b : Bool) : Eval (cH H) fF [bool b] none := none_at (notCtorH H) (lookupFH H) b

/-- **`f(b)` has no other result, for every H**: no value. -/
theorem f_none_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) fF [bool b] r) :
    r = none := alone (notCtorH H) (lookupFH H) h

/-- **`f(true)` has the result none, for every H.** -/
theorem f_true_none (H : HookParams) : Eval (cH H) fF [bool true] none := f_none H true

/-- **`f(true)` has no value, for every H.** -/
theorem f_true_none_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fF [bool true] r) :
    r = none := f_none_alone H h

end ExClauseFixtures.AndRight

/-- info: 'ExClauseFixtures.AndRight.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.AndRight.read
#print axioms ExClauseFixtures.AndRight.f_none
#print axioms ExClauseFixtures.AndRight.f_none_alone
#print axioms ExClauseFixtures.AndRight.f_true_none
#print axioms ExClauseFixtures.AndRight.f_true_none_alone
