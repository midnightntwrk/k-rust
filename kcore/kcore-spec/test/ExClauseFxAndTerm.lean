/-
  The fixture e3-ml-eq-rhs-and-term (`rule f(X) => X`, `rule g(X) => 0 -Int X`,
  `rule h(X) => f(X) #And g(X)`, f, g and h `[function]` over Int, none `total`): the clauses the
  reader gives for its text and the results of `h`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxAndTerm.lean`.

  The text is `f2-examples/e3-ml-eq-rhs-and-term.kompile.kore`; sentence numbers are
  `AxiomDecl.index`: 200 is f's equation, 202 g's, 204 h's `h(X0) = (f(X) ∧ g(X)) ∧ \top`.

  From the sentences: h(x) is the intersection of f(x) = {x} and g(x) = {0 -Int x}: {0} at 0, and
  empty at every other x.

  The statements are on `defn`, the definition the reader gives for the text, each for every H:
  - The clauses read (`read`): f's `f(X) => X`, g's `g(X) => 0 -Int X`, and h's one clause
    `[X:Int, #Cut0:Int]`, `exs [1]`, `rhs #Cut0`, `post (#Cut0 ∈ f(X)) ∧ (#Cut0 ∈ g(X))`: the
    conjunction at a term position is a fresh variable that is in both conjuncts.
  - `h_zero`, `h_zero_alone`: where the conjuncts agree, at 0, `h(0)` is 0 (`Eval.clauseEx` at
    #Cut0 := 0; every other instance has `post` false) and has no other result.
  - `h_ne`, `h_ne_alone`: where they differ, at n ≠ 0, `h(n)` has the result none (`Eval.exNone`:
    every instance has `post` false, since no value is both n and 0 -Int n) and no other result.
  - `f_value`, `g_value` and their `_alone` forms: the results of the two conjuncts.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.AndTermFx

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

/-- A substitution giving the variable 0 a value of the sort is well sorted. -/
theorem sorted1 {a : Srt} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a) :
    d.WellSorted [a] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp at hs

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

/-- A call of a function of the semantics at the value of the variable 0: the function's result. -/
theorem call_inv {f : Sym} {fn : Fn} {x : GroundTerm} {r : Option GroundTerm} (hc : d.isCtor f = false)
    (hk : isHook f = false) (hpf : d.isParam f = false) (hfn : d.lookupFn f = some fn) (h0 : σ.lookup 0 = some x)
    (h : EvalTerm d σ (.app f [.var 0]) r) : Eval d f [x] r := by
  generalize ht : Term.app f [.var 0] = t at h
  cases h with
  | call _ _ hts hvs hf _ =>
    cases ht
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    rw [h0] at hvs; cases hvs; exact hf
  | callUndef _ _ hts hvs _ =>
    cases ht
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    rw [h0] at hvs; cases hvs
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | hook _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | param _ _ hp _ _ => cases ht; rw [hpf] at hp; cases hp
  | ovl _ ho _ _ => cases ht; rw [d.isOvl_of_lookupFn hfn] at ho; cases ho
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [d.isOvl_of_lookupFn hfn] at ho; cases ho
  | _ => cases ht

theorem call_of {f : Sym} {x : GroundTerm} {r : Option GroundTerm} (hc : d.isCtor f = false)
    (hk : isHook f = false) (hpf : d.isParam f = false) (h0 : σ.lookup 0 = some x) (hf : Eval d f [x] r) :
    EvalTerm d σ (.app f [.var 0]) r :=
  .call hc hk (rs := [σ.lookup 0]) (.cons .var .nil) (by rw [h0]; rfl) hf hpf

end ExClauseFixtures.AndTermFx

namespace ExClauseFixtures.AndTerm

open GroundTerm ExClauseFixtures.AndTermFx

definition_of defn from "f2-examples/e3-ml-eq-rhs-and-term.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def fG : Sym := 385
def fH : Sym := 386

/-- `f(X) => X`. -/
def clF : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }
/-- `g(X) => 0 -Int X`. -/
def clG : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app intSub [.dv Srt.int (.int 0), .var 0], ens := none }
/-- `h(X) => #Cut0` with `exs = [#Cut0]` and `post := (#Cut0 ∈ f(X)) ∧ (#Cut0 ∈ g(X))`. -/
def clH : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .and (.mem Srt.int (.var 1) (.app fF [.var 0])) (.mem Srt.int (.var 1) (.app fG [.var 0])) }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clF] }
def fnG : Fn := { label := fG, args := [Srt.int], result := Srt.int, clauses := [clG] }
def fnH : Fn := { label := fH, args := [Srt.int], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are f, g and h, each with the one clause above. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem names : c.symName fF = "Lblf" ∧ c.symName fG = "Lblg" ∧ c.symName fH = "Lblh" ∧
    c.symName intSub = "Lbl'Unds'-Int'Unds'" := by decide +kernel

/-- #Cut0 is of the unconfined Int and fixed by `post`: `clausePlainEx` admits h's clause. -/
theorem plainEx : c.confined Srt.int = false ∧ c.clausePlainEx clH = true := by decide +kernel

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn fG = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn fH = some fnH := by rw [Semantics.lookupFn_eq]; rfl

/-- What a semantics must give for the three clauses to be read in it. -/
structure Reads (d : Semantics) : Prop where
  lf : d.lookupFn fF = some fnF
  lg : d.lookupFn fG = some fnG
  lh : d.lookupFn fH = some fnH
  cf : d.isCtor fF = false
  cg : d.isCtor fG = false
  sub : d.isCtor intSub = false
  pf : d.isParam fF = false
  pg : d.isParam fG = false

theorem reads : Reads c :=
  ⟨lookupF, lookupG, lookupH, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel⟩

theorem readsH (H : HookParams) : Reads (cH H) :=
  ⟨by rw [Semantics.lookupFn_withHooks]; exact lookupF, by rw [Semantics.lookupFn_withHooks]; exact lookupG,
   by rw [Semantics.lookupFn_withHooks]; exact lookupH, reads.cf, reads.cg, reads.sub, reads.pf, reads.pg⟩

section Clauses

variable {d : Semantics} {σ : Subst}

theorem fHook : isHook fF = false := by decide +kernel
theorem gHook : isHook fG = false := by decide +kernel
theorem subHook : isHook intSub = true := by decide +kernel

/-- `_-Int_` at two values of Int, under every interpretation (domains.md, `hook(INT.sub)`: the
difference of the two integers). -/
theorem hookSub (n : Int) : d.hookRes intSub [int 0, int n] = some (some (int (0 - n))) :=
  Semantics.hookRes_of_value rfl

/-- A clause of one variable, of a function whose one clause it is, matched at a value. -/
theorem fails_one {cl : Clause} {x : GroundTerm} (hx : d.sortOf x = some Srt.int)
    (hv : cl.vars = [Srt.int]) (hp : cl.pats = [.var 0]) (hr : cl.req = none) (hpre : cl.pre = .top)
    (h : Fails d [x] cl) : False := by
  cases h with
  | intro hF =>
    have hs : d.WellSorted cl.vars [(0, x)] := hv ▸ sorted1 rfl hx
    have hm : PatVals d [(0, x)] cl.pats [x] := hp ▸ .cons (.var rfl) .nil
    cases hF _ (hs.at _) hm with
    | intro ht => rw [hr] at ht; cases ht
    | pre hq => rw [hpre] at hq; cases hq

/-! ### f and g -/

theorem f_val (hd : Reads d) (x : GroundTerm) (hx : d.sortOf x = some Srt.int) : Eval d fF [x] (some x) :=
  .clause (fn := fnF) (cl := clF) (σ := [(0, x)]) hd.lf (List.mem_singleton_self _) (sorted1 rfl hx)
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => nomatch ht) .top

theorem f_inv (hd : Reads d) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) {r : Option GroundTerm}
    (h : Eval d fF [x] r) : r = some x := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hd.lf] at h1; cases h1; simpa [fnF] using h2
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hmatch
    cases hvs
    rw [EvalTerm.var_inv hrhs, PatVal.var_inv hv]
  | rest hfn' hnone =>
    rw [hd.lf] at hfn'; cases hfn'
    exact (fails_one hx rfl rfl rfl rfl (hnone clF (List.mem_singleton_self _))).elim
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

theorem evalSub (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ clG.rhs (some (int (0 - n))) :=
  .hook hd.sub subHook (rs := [some (int 0), σ.lookup 0]) (.cons .dv (.cons .var .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookSub n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalSub_inv (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) {r : Option GroundTerm}
    (h : EvalTerm d σ clG.rhs r) : r = some (int (0 - n)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.sub subHook h
  obtain ⟨r1, rs1, rfl, h1, hs1⟩ := EvalTerms.cons_inv hts
  obtain ⟨r2, rs2, rfl, h2, hs2⟩ := EvalTerms.cons_inv hs1
  obtain rfl := EvalTerms.nil_inv hs2
  obtain rfl := EvalTerm.dv_inv h1
  obtain rfl := EvalTerm.var_inv h2
  have := hh [int 0, int n] (by rw [h0]; rfl)
  rw [hookSub] at this
  exact (Option.some.inj this).symm

theorem g_val (hd : Reads d) (n : Int) : Eval d fG [int n] (some (int (0 - n))) :=
  .clause (fn := fnG) (cl := clG) (σ := [(0, int n)]) hd.lg (List.mem_singleton_self _)
    (sorted1 rfl (rmS_sortOf_int d n)) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evalSub hd rfl) (fun t ht => nomatch ht) .top

theorem g_inv (hd : Reads d) {n : Int} {r : Option GroundTerm} (h : Eval d fG [int n] r) :
    r = some (int (0 - n)) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fG = some fn' → cl ∈ fn'.clauses → cl = clG := fun h1 h2 => by
    rw [hd.lg] at h1; cases h1; simpa [fnG] using h2
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hmatch
    cases hvs
    exact evalSub_inv hd (PatVal.var_inv hv) hrhs
  | rest hfn' hnone =>
    rw [hd.lg] at hfn'; cases hfn'
    exact (fails_one (rmS_sortOf_int d n) rfl rfl rfl rfl (hnone clG (List.mem_singleton_self _))).elim
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

/-! ### h -/

/-- The truth value of h's `post` where X is n and #Cut0 is w: whether w is both n and `0 -Int n`. -/
def postVal (n : Int) (w : GroundTerm) : Bool := sameResult (some w) (some (int n)) && sameResult (some w) (some (int (0 - n)))

theorem post_holds (hd : Reads d) {n : Int} {w : GroundTerm} (h0 : σ.lookup 0 = some (int n))
    (h1 : σ.lookup 1 = some w) : Holds d 2 σ clH.post (postVal n w) := by
  have hf := call_of hd.cf fHook hd.pf h0 (f_val hd (int n) (rmS_sortOf_int d n))
  have hg := call_of hd.cg gHook hd.pg h0 (g_val hd n)
  refine holds_cast (Holds.and (Holds.mem .var hf) (Holds.mem .var hg)) ?_
  rw [h1]; rfl

theorem post_inv (hd : Reads d) {n : Int} {w : GroundTerm} (h0 : σ.lookup 0 = some (int n))
    (h1 : σ.lookup 1 = some w) {t : Bool} (h : Holds d 2 σ clH.post t) : t = postVal n w := by
  cases h with
  | and ha hb =>
    cases ha with
    | mem ha1 ha2 =>
      cases hb with
      | mem hb1 hb2 =>
        obtain rfl := EvalTerm.var_inv ha1
        obtain rfl := EvalTerm.var_inv hb1
        obtain rfl := f_inv hd (rmS_sortOf_int d n) (call_inv hd.cf fHook hd.pf hd.lf h0 ha2)
        obtain rfl := g_inv hd (call_inv hd.cg gHook hd.pg hd.lg h0 hb2)
        rw [h1]; rfl

/-- The value w is both n and `0 -Int n` only at w = n = 0. -/
theorem postVal_true {n : Int} {w : GroundTerm} (h : postVal n w = true) : w = int n ∧ n = 0 := by
  simp only [postVal, Bool.and_eq_true] at h
  have e1 := sameResult_some.mp h.1
  have e2 := sameResult_some.mp h.2
  subst e1
  have e3 : n = 0 - n := by simpa [KCore.int] using e2
  exact ⟨rfl, by omega⟩

theorem postVal_zero : postVal 0 (int 0) = true := by decide +kernel

/-- Every instance at a match giving X the value n is decided: it gives n where its `post` holds,
which is at #Cut0 := 0 and n = 0 only, and nothing elsewhere. -/
theorem inst_all (hd : Reads d) {n : Int} (h0 : σ.lookup 0 = some (int n)) (hw : d.WellSorted clH.vars σ)
    {r : Option GroundTerm} (hr : n = 0 → r = some (int 0)) : InstIs d σ clH r := by
  obtain ⟨w, hw1, -⟩ := hw 1 Srt.int rfl
  cases hb : postVal n w with
  | true =>
    obtain ⟨rfl, rfl⟩ := postVal_true hb
    rw [hr rfl]
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht) (holds_cast (post_holds hd h0 hw1) hb)
  | false => exact .fails (post_holds hd h0 hw1) (.post (holds_cast (post_holds hd h0 hw1) hb))

/-- An instance whose `post` holds does not give nothing. -/
theorem inst_not_none (hd : Reads d) {n : Int} {w : GroundTerm} (h0 : σ.lookup 0 = some (int n))
    (h1 : σ.lookup 1 = some w) (hp : postVal n w = true) : ¬ InstIs d σ clH none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hq => have e := post_inv hd h0 h1 hq; rw [hp] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e

theorem agree_x {σ' : Subst} (h : AgreeOff clH.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 := h 0 (by decide)

theorem ext_sorted {n : Int} (w : Int) (h0 : σ.lookup 0 = some (int n)) :
    d.WellSorted clH.vars ((1, int w) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) (rmS_sortOf_int d n) (lkSelf _ _ _) (rmS_sortOf_int d w)

/-- **`h(0)` is 0**, by `Eval.clauseEx` at #Cut0 := 0. -/
theorem value_zero (hd : Reads d) : Eval d fH [int 0] (some (int 0)) :=
  have h0 : ([(1, int 0), (0, int 0)] : Subst).lookup 0 = some (int 0) := rfl
  .clauseEx (fn := fnH) (cl := clH) (σ := [(1, int 0), (0, int 0)]) hd.lh (List.mem_singleton_self _)
    (sorted2 rfl (rmS_sortOf_int d 0) rfl (rmS_sortOf_int d 0)) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht) (holds_cast (post_holds hd h0 rfl) postVal_zero)
    (fun σ' ha hw => inst_all hd ((agree_x ha).trans h0) hw (fun _ => rfl))

/-- **`h(n)` is none at n ≠ 0**, by `Eval.exNone`: every instance has `post` false. -/
theorem value_ne (hd : Reads d) {n : Int} (hn : n ≠ 0) : Eval d fH [int n] none :=
  .exNone (fn := fnH) (cl := clH) (σ := [(0, int n)]) hd.lh (List.mem_singleton_self _) (by decide)
    (fun i hi s hs => by
      have : i = 0 := by simp [Clause.univ, clH] at hi; omega
      subst this; cases hs; exact ⟨int n, rfl, rmS_sortOf_int d n⟩)
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    ⟨(1, int 0) :: [(0, int n)], agree_set1 _ _, ext_sorted 0 rfl⟩
    (fun σ' ha hw => inst_all hd ((agree_x ha).trans rfl) hw (fun h => absurd h hn))

/-- **`h(n)` has no result but the one above**: `0` at 0, none elsewhere. -/
theorem alone (hd : Reads d) {n : Int} {r : Option GroundTerm} (h : Eval d fH [int n] r) :
    (n = 0 → r = some (int 0)) ∧ (n ≠ 0 → r = none) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fH = some fn' → cl ∈ fn'.clauses → cl = clH := fun h1 h2 => by
    rw [hd.lh] at h1; cases h1; simpa [fnH] using h2
  have hx : ∀ {σ : Subst}, PatVals d σ clH.pats [int n] → σ.lookup 0 = some (int n) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hd.lh] at hfn'; cases hfn'
    cases hnone clH (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clH.vars [(1, int n), (0, int n)] :=
        sorted2 rfl (rmS_sortOf_int d n) rfl (rmS_sortOf_int d n)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | @clauseEx _ _ _ _ σ v hfn' hmem hσ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx hmatch
    obtain ⟨w, hw1, -⟩ := hσ 1 Srt.int rfl
    have e := post_inv hd h0 hw1 hpost
    obtain ⟨rfl, rfl⟩ := postVal_true e.symm
    have e' := EvalTerm.var_inv hrhs
    rw [hw1] at e'
    exact ⟨fun _ => e', fun h => absurd rfl h⟩
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx hmatch
    refine ⟨fun hn0 => ?_, fun _ => rfl⟩
    subst hn0
    exact absurd (hall _ (agree_set1 σ _) (ext_sorted 0 h0))
      (inst_not_none hd ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _) postVal_zero)

end Clauses

/-! ### The expectations, for every H -/

/-- **`h(0) = 0`, for every H**: the conjuncts f(0) and g(0) agree. -/
theorem h_zero (H : HookParams) : Eval (cH H) fH [int 0] (some (int 0)) := value_zero (readsH H)

/-- **`h(0)` has no other result, for every H.** -/
theorem h_zero_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) fH [int 0] r) :
    r = some (int 0) := (alone (readsH H) h).1 rfl

/-- **`h(n)` has the result none at n ≠ 0, for every H**: the conjuncts f(n) = n and
g(n) = 0 -Int n differ. -/
theorem h_ne (H : HookParams) {n : Int} (hn : n ≠ 0) : Eval (cH H) fH [int n] none := value_ne (readsH H) hn

/-- **`h(n)` has no other result at n ≠ 0, for every H**: no value. -/
theorem h_ne_alone (H : HookParams) {n : Int} (hn : n ≠ 0) {r : Option GroundTerm}
    (h : Eval (cH H) fH [int n] r) : r = none := (alone (readsH H) h).2 hn

/-- **`f(n) = n` alone and `g(n) = 0 -Int n` alone, for every H**: the two conjuncts. -/
theorem fg_values (H : HookParams) (n : Int) :
    Eval (cH H) fF [int n] (some (int n)) ∧ Eval (cH H) fG [int n] (some (int (0 - n))) ∧
    (∀ r, Eval (cH H) fF [int n] r → r = some (int n)) ∧ (∀ r, Eval (cH H) fG [int n] r → r = some (int (0 - n))) :=
  ⟨f_val (readsH H) _ (rmS_sortOf_int _ n), g_val (readsH H) n,
   fun _ h => f_inv (readsH H) (rmS_sortOf_int _ n) h, fun _ h => g_inv (readsH H) h⟩

end ExClauseFixtures.AndTerm

/-- info: 'ExClauseFixtures.AndTerm.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.AndTerm.read
#print axioms ExClauseFixtures.AndTerm.h_zero
#print axioms ExClauseFixtures.AndTerm.h_zero_alone
#print axioms ExClauseFixtures.AndTerm.h_ne
#print axioms ExClauseFixtures.AndTerm.h_ne_alone
#print axioms ExClauseFixtures.AndTerm.fg_values
