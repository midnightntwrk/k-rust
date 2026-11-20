/-
  `Faithful.Model.consistent_of_fnMany_agree` on the fixture e3-eq-exists-ml-in-or-int, at its
  function f, for every interpretation of the hooks: the theory has a model for every H
  (`consistent`). Run from the package root: `lake env lean -j1 test/FnManyOverInOrInt.lean`.

  The text is `f2-examples/e3-eq-exists-ml-in-or-int.kompile.kore`
  (`rule f(X) => X #Or (#Exists B:Int. (B #And {B #Equals X +Int 1}))`, over Int, not `total`). The
  reading and the facts on the clause's shape `clO s t` are test/ExClauseFxInOrInt.lean's, repeated
  (a test file imports no test file). f(x) is the set {x, x +Int 1}; evaluation gives f no result.
  - Decided on the text: f's name `Lblf` is read as no instance and is no constant; the theory's
    lists hold `Lblf` in f's own items only, the values and the heads applied at values but f's are
    of other names; f's clause's premise and right side apply no symbol named `Lblf`; `coreOKEx`.
  - For every H: `avoidsOffH` (f's clause applies at every argument of Int, so no rest of f),
    `agreeH` (two matches agree on X), `fnDetH` (`fnDet_of_coherent`: f's clause has no result at
    any match, `two_insts`; sort predicates as in `Faithful.fnDet_of_agree`), `postDecH` (the
    `post` is decided where X is a value of Int: its binder's alternative is decided at each value
    of the binder, `X +Int 1` having one value). f is the text's only function.
-/
import KcoreSpec
import KcoreSpec.ModelFnMany
import KcoreSpec.ModelFnOverHooks

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace FnManyOverInOrInt.Fx

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

/-- `f(X) => Z` with `exs = [Z]` and `post := (Z ∈ X) ∨ ∃B:s. ((Z ∈ B) ∧ (B = t))`, X and Z of the
sort s; the binder B is the index 2, bound in its alternative. -/
def clO (s : Srt) (t : Term) : Clause :=
  { vars := [s, s], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .or (.mem s (.var 1) (.var 0))
      (.ex s (.and (.mem s (.var 1) (.var 2)) (.equals s (.var 2) t))) }

def fnO (f : Sym) (s : Srt) (t : Term) : Fn := { label := f, args := [s], result := s, clauses := [clO s t] }

/-- Under every σ giving X the value x, the term t has no result but the value y. -/
def TermAt (d : Semantics) (t : Term) (x y : GroundTerm) : Prop :=
  ∀ (σ : Subst) (r : Option GroundTerm), σ.lookup 0 = some x → EvalTerm d σ t r → r = some y

section Shape

variable {s : Srt} {t : Term} {x y : GroundTerm} {f : Sym}

/-- Where Z is X's value, `post` has no truth value but true: its first alternative holds. -/
theorem post_at_x (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some x) {b : Bool}
    (h : Holds d 2 σ (clO s t).post b) : b = true := by
  cases h with
  | or h h' =>
    cases h with
    | mem a1 a0 =>
      obtain rfl := EvalTerm.var_inv a1
      obtain rfl := EvalTerm.var_inv a0
      rw [h0, h1]; simp [sameResult_self]

/-- σ with the binder's index given the value y of the sort s. -/
theorem extends_y (σ : Subst) (hy : d.sortOf y = some s) : Extends d 2 [s] σ ((2, y) :: σ) :=
  ⟨fun _ hi => lkNe y σ (Nat.ne_of_lt hi), fun j s' hj => by
    match j, hj with
    | 0, hj => cases hj; exact ⟨y, lkSelf _ _ _, hy⟩
    | j + 1, hj => simp at hj⟩

/-- Where Z is t's value y, `post` has no truth value but true: the second alternative holds, at
the binder's value y. -/
theorem post_at_y (ht : TermAt d t x y) (hy : d.sortOf y = some s) (h0 : σ.lookup 0 = some x)
    (h1 : σ.lookup 1 = some y) {b : Bool} (h : Holds d 2 σ (clO s t).post b) : b = true := by
  cases h with
  | @or _ _ _ _ b1 b2 h h' =>
    cases h' with
    | ex g hb hr =>
      have l1 : ((2, y) :: σ : Subst).lookup 1 = some y := (lkNe y σ (by decide)).trans h1
      have l2 : ((2, y) :: σ : Subst).lookup 2 = some y := lkSelf _ _ _
      have hg : g ((2, y) :: σ) = true := by
        have hb' := hb _ (extends_y σ hy)
        generalize g ((2, y) :: σ) = gb at hb'
        cases hb' with
        | and hm he =>
          cases hm with
          | mem a1 a2 =>
            cases he with
            | equals e1 e2 =>
              obtain rfl := EvalTerm.var_inv a1
              obtain rfl := EvalTerm.var_inv a2
              obtain rfl := EvalTerm.var_inv e1
              obtain rfl := ht _ _ ((lkNe y σ (by decide)).trans h0) e2
              rw [l1, l2]; simp [sameResult_self]
      have e2 : b2 = true := hr.mpr ⟨_, extends_y σ hy, hg⟩
      rw [e2]; simp

theorem exsFree_clO : (clO s t).exsFree = [1] := rfl
theorem exs_clO : (clO s t).exs ≠ [] := List.cons_ne_nil 1 []

/-- An instance at which Z has the value w and `post` has no truth value but true gives w. -/
theorem inst_eq {σ' : Subst} {w : GroundTerm} {r : Option GroundTerm} (h1 : σ'.lookup 1 = some w)
    (hp : ∀ b, Holds d 2 σ' (clO s t).post b → b = true) (h : InstIs d σ' (clO s t) r) : r = some w := by
  cases h with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp' => cases hp _ hp'
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- **The instances at Z := x and Z := y do not agree on one result**, where y is not x: no r is
the result of every instance of the clause at a match giving X the value x. -/
theorem two_insts (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (h0 : σ.lookup 0 = some x) {r : Option GroundTerm}
    (hall : ∀ σ', AgreeOff (clO s t).exsFree σ σ' → d.WellSorted (clO s t).vars σ' → InstIs d σ' (clO s t) r) :
    False := by
  have h0' : ∀ w, ((1, w) :: σ : Subst).lookup 0 = some x := fun w => (lkNe _ _ (by decide)).trans h0
  have hw : ∀ w, d.sortOf w = some s → d.WellSorted (clO s t).vars ((1, w) :: σ) := fun w hw =>
    sorted2 (h0' w) hx (lkSelf _ _ _) hw
  have e1 := inst_eq (lkSelf 1 x σ) (fun _ hb => post_at_x (h0' x) (lkSelf _ _ _) hb)
    (hall _ (agree_set1 σ _) (hw x hx))
  have e2 := inst_eq (lkSelf 1 y σ) (fun _ hb => post_at_y ht hy (h0' y) (lkSelf _ _ _) hb)
    (hall _ (agree_set1 σ _) (hw y hy))
  rw [e1] at e2
  exact hne (Option.some.inj e2).symm

theorem pat_x {σ : Subst} (hm : PatVals d σ (clO s t).pats [x]) : σ.lookup 0 = some x := by
  obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
  cases hvs
  exact PatVal.var_inv hv

/-- **`f(x)` has no result**, where t's value y at x is not x. -/
theorem no_res (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnO f s t)) {r : Option GroundTerm} (h : Eval d f [x] r) : False := by
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clO s t := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnO] using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clO
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone (clO s t) (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted (clO s t).vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex exs_clO
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall
  | exNone hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts ht hne hx hy (pat_x hmatch) hall

/-- **The clause is not match independent**: it decides at `[x]` and has no result there. -/
theorem not_mi (ht : TermAt d t x y) (hne : y ≠ x) (hx : d.sortOf x = some s) (hy : d.sortOf y = some s)
    (hfn : d.lookupFn f = some (fnO f s t)) : ¬ MatchIndependent d (clO s t) := by
  intro hm
  have hs : d.WellSorted (clO s t).vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
  have hdec : (clO s t).Decides d (fnO f s t) [(1, x), (0, x)] [x] :=
    ⟨⟨hs.at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnO, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 exs_clO f (fnO f s t) [x] _ hfn (List.mem_singleton_self _) hdec
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex exs_clO
  · exact two_insts (σ := [(1, x), (0, x)]) ht hne hx hy rfl hall
  · exact two_insts (σ := [(1, x), (0, x)]) ht hne hx hy rfl hall

end Shape

end FnManyOverInOrInt.Fx

namespace FnManyOverInOrInt

open GroundTerm FnManyOverInOrInt.Fx

definition_of defn from "f2-examples/e3-eq-exists-ml-in-or-int.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384

/-- The term the binder is equated with, `X +Int 1`. -/
def tAdd : Term := .app intAdd [.var 0, .dv Srt.int (.int 1)]

/-- **The reading**: the text's one function is f, not `total`, with the one clause
`[X:Int, #Or0:Int]`, `exs [1]`, `rhs #Or0`, `post (#Or0 ∈ X) ∨ ∃B:Int. ((#Or0 ∈ B) ∧ (B = X +Int 1))`:
the binder kept in its alternative. -/
theorem read : c.fns = [fnO fF Srt.int tAdd] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName intAdd = "Lbl'UndsPlus'Int'Unds'" ∧
    c.sortName Srt.int = "Int" := by decide +kernel

/-- Int is not confined; each alternative fixes #Or0 (the second by the binder, which its body
equates with a term over X): `clausePlainEx` admits the clause. -/
theorem plainEx : c.confined Srt.int = false ∧ c.clausePlainEx (clO Srt.int tAdd) = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some (fnO fF Srt.int tAdd) := by rw [Semantics.lookupFn_eq]; rfl
theorem notCtor : c.isCtor intAdd = false := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

section Terms

variable {d : Semantics}

theorem addHook : isHook intAdd = true := by decide +kernel

/-- `_+Int_` at two values of Int, under every interpretation (the sum of the two integers). -/
theorem hookAdd (n : Int) : d.hookRes intAdd [int n, int 1] = some (some (int (n + 1))) :=
  Semantics.hookRes_of_value rfl

/-- `X +Int 1` where X is n: n + 1, and no other result. -/
theorem tAdd_at (hc : d.isCtor intAdd = false) (n : Int) : TermAt d tAdd (int n) (int (n + 1)) := by
  intro σ r h0 h
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc addHook h
  obtain ⟨r1, rs1, rfl, h1, hs1⟩ := EvalTerms.cons_inv hts
  obtain ⟨r2, rs2, rfl, h2, hs2⟩ := EvalTerms.cons_inv hs1
  obtain rfl := EvalTerms.nil_inv hs2
  obtain rfl := EvalTerm.var_inv h1
  obtain rfl := EvalTerm.dv_inv h2
  have := hh [int n, int 1] (by rw [h0]; rfl)
  rw [hookAdd] at this
  exact (Option.some.inj this).symm

theorem succ_ne (n : Int) : int (n + 1) ≠ int n := by
  intro h
  have : n + 1 = n := by simpa [int] using h
  omega

end Terms

/-! ### The expectations, for every H -/

theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some (fnO fF Srt.int tAdd) := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

theorem tAdd_atH (H : HookParams) (n : Int) : TermAt (cH H) tAdd (int n) (int (n + 1)) := tAdd_at (d := cH H) notCtor n

/-- **`f(n)` has no result, for every H and every n**: neither a value nor none. Its instances at
#Or0 := n and at #Or0 := n +Int 1 give n and n +Int 1. -/
theorem no_result (H : HookParams) (n : Int) (r : Option GroundTerm) : ¬ Eval (cH H) fF [int n] r :=
  fun h => no_res (tAdd_atH H n) (succ_ne n) (rmS_sortOf_int _ n) (rmS_sortOf_int _ (n + 1)) (lookupFH H) h

/-- **The owed fact the package names for f's clause, `MatchIndependent`, is false, for every H.** -/
theorem not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) (clO Srt.int tAdd) :=
  not_mi (tAdd_atH H 0) (succ_ne 0) (rmS_sortOf_int _ 0) (rmS_sortOf_int _ (0 + 1)) (lookupFH H)

/-- **`FnHyp` is false, for every H**: f has no result at 0. -/
theorem not_fnHyp (H : HookParams) : ¬ FnHyp (cH H) := by
  intro hf
  have hso : (cH H).sortsOf [int 0] = some (fnO fF Srt.int tAdd).args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl
  obtain ⟨r, hr⟩ := hf.1 (fnO fF Srt.int tAdd)
    (by rw [show (cH H).fns = c.fns from rfl, read]; exact List.mem_singleton_self _) [int 0] hso
  exact no_result H 0 r hr


/-! ## The model with f read as its instances' values, for every H -/

section Model

open KCore.Faithful KCore.Faithful.Model

def nF : String := "Lblf"
def fnF : Fn := fnO fF Srt.int tAdd
def clF : Clause := clO Srt.int tAdd

theorem name_f : c.symName fF = nF := by decide +kernel
theorem plain_f : instDecode? nF = none := by decide +kernel
theorem spare_f : GenEqs.spareSymB c nF = true := by decide +kernel
theorem values_f : GenEqs.NameFree.valuesN c [nF] = true := by rw [GenEqs.NameFree.valuesN]; decide_cheap 40
theorem hooks_f : hookSigs.all (fun k => GenEqs.NameFree.appOKN c [nF] k.name) = true := by decide_cheap 40
theorem params_f : c.params.all (fun k => GenEqs.NameFree.appOKN c [nF] k.sig.name) = true := by decide_cheap 40
theorem fns_f : c.allFns.all (fun g => decide (g.label = fF) || GenEqs.NameFree.appOKN c [nF] g.label) = true := by
  decide_cheap 40
theorem lists_f : listsOffB c fF nF = true := by rw [listsOffB]; decide_cheap 40
theorem kok_f : ownKokB c fnF clF = true := by decide +kernel
theorem coreEx : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem shapes : c.shapesOK = true := by decide_cheap
theorem preTop : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel
theorem f_one : (c.allFns.filter (fun g => decide (g.label = fF))).length = 1 := by decide +kernel

theorem shapesH (H : HookParams) : (cH H).shapesOK = true := shapes

theorem rangeBelowH (H : HookParams) : RangeBelow (cH H) :=
  have h := hypSoundEx_of_coreEx (c := cH H) ((coreOKEx_withHooks_fm c H).trans coreEx)
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- f's clause applies at every argument of Int. -/
theorem not_fails_f {d : Semantics} {x : GroundTerm} (hx : d.sortOf x = some Srt.int) : ¬ Fails d [x] clF := by
  intro hF
  cases hF with
  | intro hF =>
    have hs : d.WellSorted clF.vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
    cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **Every premise but f's own items avoids `Lblf`, for every H.** -/
theorem avoidsOffH (H : HookParams) : AvoidsOff (cH H) fF ((cH H).symName fF) := by
  have hn : (cH H).symName fF = nF := name_f
  rw [hn]
  refine avoidsOff_of_lists (rangeBelowH H) (listsOff_withHooks H lists_f) values_f
    (List.all_eq_true.mp hooks_f) (List.all_eq_true.mp params_f)
    (fun g hg hl => by
      have h1 : GenEqs.NameFree.appOKN c [nF] g.label = true := by
        have := List.all_eq_true.mp fns_f g hg
        simpa [hl] using this
      exact h1)
    (fun fn hfn hl vs hvs => ?_)
  have hfn' : fn ∈ c.allFns.filter (fun g => decide (g.label = fF)) := List.mem_filter.mpr ⟨hfn, by simpa using hl⟩
  have hH : fnF ∈ c.allFns.filter (fun g => decide (g.label = fF)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (by rw [read]; simp [fnF]), by simp [fnF, fnO]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp f_one
  rw [hx, List.mem_singleton] at hfn' hH
  obtain rfl : fn = fnF := hfn'.trans hH.symm
  match vs, hvs with
  | [x], hvs =>
    have hx : (cH H).sortOf x = some Srt.int := by
      simp only [Semantics.sortsOf] at hvs
      cases h1 : (cH H).sortOf x with
      | none => rw [h1] at hvs; cases hvs
      | some s => rw [h1] at hvs; cases hvs; rfl
    exact fun hall => not_fails_f hx (hall clF (List.mem_singleton_self _))
  | [], hvs => cases hvs
  | _ :: _ :: _, hvs => exact absurd (sortsOf_len hvs) (by simp [fnF, fnO])

/-- The value of X at a match of a clause whose pattern is X and whose X is of the sort s. -/
theorem match0 {d : Semantics} {cl : Clause} {s : Srt} (hp : cl.pats = [.var 0]) (hu : 0 ∈ cl.univ)
    (hv : cl.vars[0]? = some s) {σ : Subst} {vs : List GroundTerm} (ha : cl.AppliesAt d σ vs) :
    ∃ x, vs = [x] ∧ σ.lookup 0 = some x ∧ d.sortOf x = some s := by
  have hm : PatVals d σ [.var 0] vs := hp ▸ ha.2.1
  obtain ⟨x, vs', rfl, hx, hs⟩ := PatVals.cons_inv hm
  obtain rfl : vs' = [] := by cases hs; rfl
  obtain ⟨v, hv0, hvs⟩ := ha.1 0 hu s hv
  have e : some v = some x := hv0.symm.trans (PatVal.var_inv hx)
  obtain rfl := Option.some.inj e
  exact ⟨v, rfl, hv0, hvs⟩

/-- **Two matches of f's clause at one argument agree on X, for every H.** -/
theorem agreeH (H : HookParams) : ∀ ws σ₁ σ₂, clF.AppliesAt (cH H) σ₁ ws → clF.AppliesAt (cH H) σ₂ ws →
    ∀ i < clF.vars.length, i ∉ clF.exsFree → σ₁.lookup i = σ₂.lookup i := by
  intro ws σ₁ σ₂ h1 h2 i hi hx
  rw [show clF.exsFree = [1] from rfl] at hx
  have hi0 : i = 0 := by
    have hl : clF.vars.length = 2 := rfl
    simp only [List.mem_singleton] at hx
    omega
  subst hi0
  obtain ⟨x, rfl, h0, -⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl h1
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) (cl := clF) rfl (by decide) rfl h2
  cases hx'
  rw [h0, h0']

/-- f's clause has no result at a match giving X a value of Int, for every H. -/
theorem no_resEx (H : HookParams) {σ : Subst} {x : GroundTerm} {r : Option GroundTerm}
    (h0 : σ.lookup 0 = some x) (hx : (cH H).sortOf x = some Srt.int) (h : clF.Res (cH H) σ r) : False := by
  obtain ⟨n, rfl⟩ := shape_int (shapesH H) hx
  rcases h with ⟨he, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact exs_clO he
  · exact two_insts (tAdd_atH H n) (succ_ne n) hx (rmS_sortOf_int _ (n + 1)) h0 hall
  · exact two_insts (tAdd_atH H n) (succ_ne n) hx (rmS_sortOf_int _ (n + 1)) h0 hall

/-- **Every function has at most one result, for every H**: f's clause has no result at any
match; sort predicates as in `Faithful.fnDet_of_agree`. -/
theorem fnDetH (H : HookParams) : FnDet (cH H) := by
  refine fnDet_of_coherent fun f fn hfn cl hcl cl' hcl' hprio => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · have hfns : (cH H).fns = [fnO fF Srt.int tAdd] := read
    rw [hfns, List.mem_singleton] at hu
    subst hu
    simp only [fnO, List.mem_singleton] at hcl hcl'; subst hcl hcl'
    intro vs σ σ' ha _ _ _ _ _ _
    obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) (cl := clF) rfl
      (by decide) rfl ha
    exact .inr fun r _ hr _ => (no_resEx H h0 hx hr).elim
  · by_cases he : cl = cl'
    · subst he
      intro vs σ σ' _ _ _ _ _ _ _
      refine Or.inl ⟨Semantics.sortPreds_exs hp cl hcl, Semantics.sortPreds_exs hp cl hcl, rfl, rfl,
        fun i hi => absurd hi ?_, fun t ht => ?_⟩
      · obtain ⟨s', lit, hr⟩ := sortPreds_rhs hp cl hcl
        rw [hr, varOccs]
        exact List.not_mem_nil
      · rw [sortPreds_ens hp cl hcl] at ht; cases ht
    · rcases mem_pairs_of_ne hcl hcl' he with hpr | hpr
      · exact (sortPreds_agree hp cl cl' hpr hprio).1
      · refine (sortPreds_agree hp cl' cl hpr ?_).2
        rcases hprio with h | h | h
        · exact .inl h.symm
        · exact .inr (.inr h)
        · exact .inr (.inl h)

/-- `X +Int 1` where X is n: n + 1. -/
theorem tAdd_ev (H : HookParams) {σ : Subst} {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm (cH H) σ tAdd (some (int (n + 1))) :=
  .hook notCtor addHook (rs := [σ.lookup 0, some (int 1)]) (.cons .var (.cons .dv .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookAdd n)
    (fun hn => by rw [h0] at hn; cases hn)

/-- **f's right-side predicate has a truth value, for every H**, where X is a value of Int: its
binder's alternative is decided at each value of the binder. -/
theorem postDecH (H : HookParams) : ClausePostDecided (cH H) := by
  classical
  intro fn hfn cl hcl σ hσ
  have hfns : (cH H).fns = [fnO fF Srt.int tAdd] := read
  rw [hfns, List.mem_singleton] at hfn
  subst hfn
  simp only [fnO, List.mem_singleton] at hcl; subst hcl
  obtain ⟨x, h0, hx⟩ := hσ 0 Srt.int rfl
  obtain ⟨n, rfl⟩ := shape_int (shapesH H) hx
  let g : Subst → Bool := fun σ' =>
    (σ'.lookup 1).isSome && sameResult (σ'.lookup 1) (σ'.lookup 2) &&
      sameResult (σ'.lookup 2) (some (int (n + 1)))
  have hb : ∀ σ', Extends (cH H) 2 [Srt.int] σ σ' →
      Holds (cH H) (2 + 1) σ' (.and (.mem Srt.int (.var 1) (.var 2)) (.equals Srt.int (.var 2) tAdd)) (g σ') :=
    fun σ' hext => Holds.and (Holds.mem .var .var)
      (Holds.equals .var (tAdd_ev H ((hext.1 0 (by decide)).trans h0)))
  exact ⟨_, Holds.or (Holds.mem .var .var)
    (Holds.ex (b := decide (∃ σ', Extends (cH H) 2 [Srt.int] σ σ' ∧ g σ' = true))
      g hb decide_eq_true_iff)⟩

/-- **The theory has a model, for every H** (`consistent_of_fnMany_agree` at f). -/
theorem consistent (H : HookParams) : Consistent (cH H) := by
  have hfns : (cH H).fns = [fnO fF Srt.int tAdd] := read
  refine consistent_of_fnMany_agree (f := fF) (fn := fnF) (cl := clF) (a := Srt.int)
    ((coreOKEx_withHooks_fm c H).trans coreEx) (by rw [hfns]; simp [fnF]) rfl rfl rfl exs_clO
    (by rw [show (cH H).symName fF = nF from name_f]; exact plain_f)
    (by rw [show (cH H).symName fF = nF from name_f, spareSymB_withHooks_fm]; exact spare_f)
    (avoidsOffH H) (by rw [ownKokB_withHooks]; exact kok_f) (fnDetH H) (fun g hg' hl => ?_) (agreeH H)
    (clausePreDecided_of_isTop (c := cH H) preTop) (postDecH H) (openLaws_of_plain noRaw)
  rw [hfns, List.mem_singleton] at hg'
  subst hg'
  exact absurd rfl hl

end Model

end FnManyOverInOrInt

/-- info: 'FnManyOverInOrInt.lists_f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverInOrInt.lists_f
/-- info: 'FnManyOverInOrInt.fnDetH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverInOrInt.fnDetH
/-- info: 'FnManyOverInOrInt.postDecH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverInOrInt.postDecH
/-- info: 'FnManyOverInOrInt.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverInOrInt.consistent
