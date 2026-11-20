/-
  The fixture e3-eq-exists-ml-and-terms (`rule f(X) => #Exists B:Bool. (B #And (notBool X))` and
  `rule k(X) => #Exists Z:Int. (Z #And (X +Int 1))`, f and k `[function]`, neither `total`): the
  clauses the reader gives for its text and the results of f and k, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxAndTerms.lean`.

  The text is `f2-examples/e3-eq-exists-ml-and-terms.kompile.kore`; sentence numbers are
  `AxiomDecl.index`: 200 is f's equation, 235 k's.

  From the sentences: f(x) is the set of the elements B of Bool that are `notBool x`, {notBool x};
  k(x) is {x +Int 1}.

  The statements are on `defn`, the definition the reader gives for the text, each for every H:
  - The clauses read (`read`): each binder's variable holds the position and is in the other
    conjunct: f's `[X:Bool, B:Bool]`, `exs [1]`, `rhs B`, `post B ∈ notBool(X)`; k's `[X:Int, Z:Int]`,
    `exs [1]`, `rhs Z`, `post Z ∈ X +Int 1`.
  - `f_value`, `f_alone`: `f(b)` is `notBool b`, by `Eval.clauseEx` at B := `notBool b` (the instance
    where the conjuncts agree; at the other value of Bool they differ and the instance has `post`
    false: it gives nothing, not a result none), and has no other result; `f_true`, `f_true_alone`.
  - `k_value`, `k_alone`: `k(n)` is `n +Int 1`, by `Eval.clauseEx` at Z := n +Int 1 (every other
    instance has `post` false), and has no other result; `k_2`, `k_2_alone`.
  The two clauses have one shape, `clM s t` (a binder of sort s holding the position, `post` its
  membership in the term t over X); the facts on that shape are stated once, from what the term t
  evaluates to (`TermOK`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.AndTermsFx

open GroundTerm

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

/-- `f(X) => V` with `exs = [V]` and `post := V ∈ t`, X and V of the sort s. -/
def clM (s : Srt) (t : Term) : Clause :=
  { vars := [s, s], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .mem s (.var 1) t }

def fnM (f : Sym) (s : Srt) (t : Term) : Fn := { label := f, args := [s], result := s, clauses := [clM s t] }

/-- The term t at a σ giving X the value `emb a` has the one result `F a`. -/
structure TermOK (d : Semantics) (t : Term) {α : Type} (emb F : α → GroundTerm) : Prop where
  ev : ∀ (σ : Subst) a, σ.lookup 0 = some (emb a) → EvalTerm d σ t (some (F a))
  inv : ∀ (σ : Subst) a r, σ.lookup 0 = some (emb a) → EvalTerm d σ t r → r = some (F a)

section Shape

variable {s : Srt} {t : Term} {α : Type} {emb F : α → GroundTerm} {f : Sym}

theorem post_holds (ht : TermOK d t emb F) {a : α} {w : GroundTerm} (h0 : σ.lookup 0 = some (emb a))
    (h1 : σ.lookup 1 = some w) : Holds d 2 σ (clM s t).post (sameResult (some w) (some (F a))) :=
  holds_cast (Holds.mem .var (ht.ev σ a h0)) (by rw [h1]; rfl)

theorem post_inv (ht : TermOK d t emb F) {a : α} {w : GroundTerm} (h0 : σ.lookup 0 = some (emb a))
    (h1 : σ.lookup 1 = some w) {b : Bool} (h : Holds d 2 σ (clM s t).post b) :
    b = sameResult (some w) (some (F a)) := by
  cases h with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := ht.inv σ a _ h0 h'
    rw [h1]; rfl

theorem exsFree_clM : (clM s t).exsFree = [1] := rfl
theorem exs_clM : (clM s t).exs ≠ [] := List.cons_ne_nil 1 []

theorem agree_x {σ' : Subst} (h : AgreeOff (clM s t).exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by rw [exsFree_clM]; decide)

/-- **Every instance is decided and gives `F a` or nothing.** -/
theorem inst_all (ht : TermOK d t emb F) {a : α} (h0 : σ.lookup 0 = some (emb a))
    (hw : d.WellSorted (clM s t).vars σ) : InstIs d σ (clM s t) (some (F a)) := by
  obtain ⟨w, hw1, -⟩ := hw 1 s rfl
  cases hb : sameResult (some w) (some (F a)) with
  | true =>
    obtain rfl := sameResult_some.mp hb
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds ht h0 hw1) hb)
  | false => exact .fails (post_holds ht h0 hw1) (.post (holds_cast (post_holds ht h0 hw1) hb))

/-- The instance at V := `F a` does not give nothing. -/
theorem inst_not_none (ht : TermOK d t emb F) {a : α} (h0 : σ.lookup 0 = some (emb a))
    (h1 : σ.lookup 1 = some (F a)) : ¬ InstIs d σ (clM s t) none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht' _ _ => cases ht'
    | post hp =>
      have e := post_inv ht h0 h1 hp
      rw [sameResult_self] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e

/-- **`f(emb a)` is `F a`**, by `Eval.clauseEx` at V := `F a`. -/
theorem value (ht : TermOK d t emb F) (hfn : d.lookupFn f = some (fnM f s t)) {a : α}
    (hx : d.sortOf (emb a) = some s) (hy : d.sortOf (F a) = some s) :
    Eval d f [emb a] (some (F a)) :=
  have h0 : ([(1, F a), (0, emb a)] : Subst).lookup 0 = some (emb a) := rfl
  .clauseEx (fn := fnM f s t) (cl := clM s t) (σ := [(1, F a), (0, emb a)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl hx rfl hy) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnM, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    exs_clM .var (fun t ht => nomatch ht)
    (holds_cast (post_holds ht h0 rfl) (sameResult_self _))
    (fun σ' ha hw => inst_all ht ((agree_x ha).trans h0) hw)

/-- **`f(emb a)` has no other result.** -/
theorem alone (ht : TermOK d t emb F) (hfn : d.lookupFn f = some (fnM f s t)) {a : α}
    (hx : d.sortOf (emb a) = some s) (hy : d.sortOf (F a) = some s) {r : Option GroundTerm}
    (h : Eval d f [emb a] r) : r = some (F a) := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clM s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnM] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ (clM s t).pats [emb a] → σ.lookup 0 = some (emb a) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clM
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone (clM s t) (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted (clM s t).vars [(1, emb a), (0, emb a)] := sorted2 rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clM
  | clauseEx hfn' hmem _ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have h1 := (EvalTerm.var_inv hrhs).symm
    have e := post_inv ht (hx0 hmatch) h1 hpost
    rw [sameResult_some.mp e.symm]
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx0 hmatch
    exact absurd (hall _ (agree_set1 σ _) (sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) hy))
      (inst_not_none ht ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

end Shape

end ExClauseFixtures.AndTermsFx

namespace ExClauseFixtures.AndTerms

open GroundTerm ExClauseFixtures.AndTermsFx

definition_of defn from "f2-examples/e3-eq-exists-ml-and-terms.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def fK : Sym := 385

/-- f's right side's other conjunct, `notBool X`. -/
def tF : Term := .app boolNot [.var 0]
/-- k's right side's other conjunct, `X +Int 1`. -/
def tK : Term := .app intAdd [.var 0, .dv Srt.int (.int 1)]

/-- **The reading**: the text's functions are f, with the clause `[X:Bool, B:Bool]`, `exs [1]`,
`rhs B`, `post B ∈ notBool(X)`, and k, with `[X:Int, Z:Int]`, `exs [1]`, `rhs Z`,
`post Z ∈ X +Int 1`. -/
theorem read : c.fns = [fnM fF Srt.bool tF, fnM fK Srt.int tK] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName fK = "Lblk" ∧ c.symName boolNot = "LblnotBool'Unds'" := by
  decide +kernel

/-- B is of the confined Bool, Z of the unconfined Int and fixed by its membership: `clausePlainEx`
admits both clauses. -/
theorem plainEx : c.clausePlainEx (clM Srt.bool tF) = true ∧ c.confined Srt.int = false ∧
    c.clausePlainEx (clM Srt.int tK) = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some (fnM fF Srt.bool tF) := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupK : c.lookupFn fK = some (fnM fK Srt.int tK) := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor boolNot = false ∧ c.isCtor intAdd = false := by decide +kernel

section Terms

variable {d : Semantics}

theorem notHook : isHook boolNot = true := by decide +kernel
theorem addHook : isHook intAdd = true := by decide +kernel

/-- `notBool` at a value of Bool, under every interpretation. -/
theorem hookNot (b : Bool) : d.hookRes boolNot [bool b] = some (some (bool (!b))) :=
  Semantics.hookRes_of_value (by cases b <;> decide +kernel)

/-- `_+Int_` at two values of Int, under every interpretation (the sum of the two integers). -/
theorem hookAdd (n : Int) : d.hookRes intAdd [int n, int 1] = some (some (int (n + 1))) :=
  Semantics.hookRes_of_value rfl

theorem tF_ok (hc : d.isCtor boolNot = false) : TermOK d tF bool (fun b => bool (!b)) where
  ev σ b h0 := .hook hc notHook (rs := [σ.lookup 0]) (.cons .var .nil)
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookNot b)
    (fun hn => by rw [h0] at hn; cases hn)
  inv σ b r h0 h := by
    obtain ⟨rs, hts, hh, -⟩ := hook_inv hc notHook h
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    have := hh [bool b] (by rw [h0]; rfl)
    rw [hookNot] at this
    exact (Option.some.inj this).symm

theorem tK_ok (hc : d.isCtor intAdd = false) : TermOK d tK int (fun n => int (n + 1)) where
  ev σ n h0 := .hook hc addHook (rs := [σ.lookup 0, some (int 1)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookAdd n)
    (fun hn => by rw [h0] at hn; cases hn)
  inv σ n r h0 h := by
    obtain ⟨rs, hts, hh, -⟩ := hook_inv hc addHook h
    obtain ⟨r1, rs1, rfl, h1, hs1⟩ := EvalTerms.cons_inv hts
    obtain ⟨r2, rs2, rfl, h2, hs2⟩ := EvalTerms.cons_inv hs1
    obtain rfl := EvalTerms.nil_inv hs2
    obtain rfl := EvalTerm.var_inv h1
    obtain rfl := EvalTerm.dv_inv h2
    have := hh [int n, int 1] (by rw [h0]; rfl)
    rw [hookAdd] at this
    exact (Option.some.inj this).symm

end Terms

/-! ### The expectations, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some (fnM fF Srt.bool tF) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF
theorem lookupKH (H : HookParams) : (cH H).lookupFn fK = some (fnM fK Srt.int tK) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupK
theorem tF_okH (H : HookParams) : TermOK (cH H) tF bool (fun b => bool (!b)) := tF_ok notCtor.1
theorem tK_okH (H : HookParams) : TermOK (cH H) tK int (fun n => int (n + 1)) := tK_ok notCtor.2

/-- **`f(b) = notBool b`, for every H.** -/
theorem f_value (H : HookParams) (b : Bool) : Eval (cH H) fF [bool b] (some (bool (!b))) :=
  value (tF_okH H) (lookupFH H) (rmS_sortOf_bool _ b) (rmS_sortOf_bool _ (!b))

/-- **`f(b)` has no other result, for every H.** -/
theorem f_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) fF [bool b] r) :
    r = some (bool (!b)) :=
  alone (tF_okH H) (lookupFH H) (rmS_sortOf_bool _ b) (rmS_sortOf_bool _ (!b)) h

/-- **`f(true) = false`, for every H.** -/
theorem f_true (H : HookParams) : Eval (cH H) fF [bool true] (some (bool false)) := f_value H true

/-- **`f(true)` has no result but `false`, for every H**: not `true`, and not none. -/
theorem f_true_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fF [bool true] r) :
    r = some (bool false) := f_alone H h

/-- **`k(n) = n +Int 1`, for every H.** -/
theorem k_value (H : HookParams) (n : Int) : Eval (cH H) fK [int n] (some (int (n + 1))) :=
  value (tK_okH H) (lookupKH H) (rmS_sortOf_int _ n) (rmS_sortOf_int _ (n + 1))

/-- **`k(n)` has no other result, for every H.** -/
theorem k_alone (H : HookParams) {n : Int} {r : Option GroundTerm} (h : Eval (cH H) fK [int n] r) :
    r = some (int (n + 1)) :=
  alone (tK_okH H) (lookupKH H) (rmS_sortOf_int _ n) (rmS_sortOf_int _ (n + 1)) h

/-- **`k(2) = 3`, for every H.** -/
theorem k_2 (H : HookParams) : Eval (cH H) fK [int 2] (some (int 3)) := k_value H 2

/-- **`k(2)` has no result but 3, for every H.** -/
theorem k_2_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fK [int 2] r) :
    r = some (int 3) := k_alone H h

end ExClauseFixtures.AndTerms

/-- info: 'ExClauseFixtures.AndTerms.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.AndTerms.read
#print axioms ExClauseFixtures.AndTerms.f_value
#print axioms ExClauseFixtures.AndTerms.f_alone
#print axioms ExClauseFixtures.AndTerms.f_true
#print axioms ExClauseFixtures.AndTerms.f_true_alone
#print axioms ExClauseFixtures.AndTerms.k_value
#print axioms ExClauseFixtures.AndTerms.k_alone
#print axioms ExClauseFixtures.AndTerms.k_2
#print axioms ExClauseFixtures.AndTerms.k_2_alone
