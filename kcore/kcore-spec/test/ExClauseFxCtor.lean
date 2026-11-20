/-
  The fixture e3-eq-exists-ctor (an equation with an existential variable of a constructor sort): the
  clause the reader gives for its text and the results of `pick`, for every hook interpretation.
  Run from the package root: `lake env lean -j1 test/ExClauseFxCtor.lean`.

  `syntax Col ::= "r" | "g"`, `rule pick(X) => ?C ensures ?C =/=K X`. kompile rejects `?C` on an
  equation (fixture `e3-eq-exists-ctor`), so the text exists in the `#Exists` spelling
  (`e3-eq-exists-ctor-ml`): `pick(X) => #Exists C:Col. (C #And {(C =/=K X) #Equals true})`, its
  axiom 187.

  From the sentence: `pick(x)` is the set of the elements c of Col with `(c =/=K x) = true`. The
  elements of Col are those of `r` and `g` (its no-junk sentence), so `pick(r) = g` and
  `pick(g) = r`, and nothing else.

  The statements are on `defn`, the definition the reader gives for the text
  (`f2-examples/e3-eq-exists-ctor-ml.kompile.kore`), each for every hook interpretation H:
  - The clause read is `clP` (`read`): `[X:Col, C:Col]`, `exs [1]`, `rhs C`,
    `post (C ~> .K =/=K X ~> .K) = true`; `pick` has no other clause and is not `total`.
  - Col is confined (`plainEx`), and its values are `r` and `g` (`col_values`).
  - `pick_value`: `pick(x)` has as result the other value of Col, by `Eval.clauseEx`; the instance
    at C := x has `post` false and gives nothing. `pick_alone`: it has no other result.
    `pick_r`, `pick_r_alone`: the two at `r`.

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

namespace ExClauseFixtures.ExCtor

open GroundTerm ExClauseFixtures.CeFx

definition_of defn from "f2-examples/e3-eq-exists-ctor-ml.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def col : Srt := 32
def gS : Sym := 385
def rS : Sym := 386
def pickS : Sym := 387

/-- `X ~> .K`, X the variable i of Col. -/
def kOfVar (i : Nat) : Term := .app kseq [.inj col Srt.kitem (.var i), .app dotk []]

/-- `pick(X) => C` with `exs = [C]` and `post := (C ~> .K =/=K X ~> .K) = true`, X and C of Col. -/
def clP : Clause :=
  { vars := [col, col], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.bool (.app kNe [kOfVar 1, kOfVar 0]) (.dv Srt.bool (.bool true)) }

def fnP : Fn := { label := pickS, args := [col], result := col, clauses := [clP] }

/-- **The reading**: the text's one function is `pick`, with the one clause `clP`. -/
theorem read : c.fns = [fnP] := by kernel_rfl

theorem names : c.symName pickS = "Lblpick" ∧ c.symName rS = "Lblr" ∧ c.symName gS = "Lblg" ∧
    c.symName kNe = "Lbl'UndsEqlsSlshEqls'K'Unds'" ∧ c.sortName col = "Col" := by decide +kernel

/-- C is of the confined sort Col: the clause is one `clausePlainEx` admits. -/
theorem plainEx : c.confined col = true ∧ c.clausePlainEx clP = true := by decide +kernel

theorem lookupP : c.lookupFn pickS = some fnP := by rw [Semantics.lookupFn_eq]; rfl
theorem flags : c.isCtor kNe = false ∧ c.isCtor kseq = true ∧ c.isCtor dotk = true := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noOvls : c.ovls = [] := by decide +kernel

/-- The value of Col: `g` at `true`, `r` at `false`. -/
def colOf (b : Bool) : GroundTerm := .ctor (if b then gS else rS) []

theorem col_sort (b : Bool) : c.sortOf (colOf b) = some col := by cases b <;> decide +kernel

/-! ### The values of Col -/

/-- A value of a sort that no subsort, collection or literal reaches is a constructor's term, in a
semantics without overloading symbols and open generators. -/
theorem ctor_of_sort {d : Semantics} (hno : d.ovls = []) (hraw : ∀ k ∈ d.params, k.raw = false)
    {v : GroundTerm} {s : Srt} (h : d.sortOf v = some s)
    (hsub : ∀ p ∈ d.subsorts, p.2 ≠ s) (hcoll : d.collOf s = none) (hdv : ∀ lit, dvOK d.lib s lit = false) :
    ∃ f ts k, v = .ctor f ts ∧ lookupSig d.ctorSigs f = some k ∧ d.sortsOf ts = some k.args ∧
      s = k.result := by
  cases v with
  | ctor f ts =>
    obtain ⟨k, hk, hs, he⟩ := (d.sortOf_ctor_of_none hno hraw).mp h
    exact ⟨f, ts, k, rfl, hk, hs, he⟩
  | inj a b t =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      exact absurd rfl (hsub _ hc.1.1)
    · cases h
  | dv s' lit =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hd; cases h; rw [hdv] at hd; cases hd
    · cases h
  | map s' es =>
    obtain ⟨k, -, hk, -, -, -, rfl⟩ := d.sortOf_map_inv h
    rw [hcoll] at hk; cases hk
  | set s' es =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i k ss hk _
      split at h
      · cases h; rw [hcoll] at hk; cases hk
      · cases h
    · cases h
  | list s' es =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i k ss hk _
      split at h
      · cases h; rw [hcoll] at hk; cases hk
      · cases h
    · cases h

/-- A sort whose carrier is no literal sort has no literal. -/
theorem dv_none {l : Lib} {s : Srt} (hi : (l.carrier s == Srt.int) = false)
    (hb : (l.carrier s == Srt.bool) = false) (hk : (l.carrier s == Srt.kconfigVar) = false)
    (hs : (l.carrier s == Srt.string) = false) (ht : l.tokenSorts.contains (l.carrier s) = false)
    (hy : (l.carrier s == Srt.bytes) = false) (hys : l.byteSorts.contains (l.carrier s) = false)
    (hf : (l.carrier s == Srt.float) = false) (lit : Lit) : dvOK l s lit = false := by
  cases lit <;> simp only [dvOK, hi, hb, hk, hs, ht, hy, hys, hf, Bool.or_false, Bool.false_and]

theorem col_dv : ∀ lit, dvOK c.lib col lit = false :=
  dv_none (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem col_facts : (∀ p ∈ c.subsorts, p.2 ≠ col) ∧ c.collOf col = none ∧
    ∀ k ∈ c.ctorSigs, k.result = col → (k.name = gS ∨ k.name = rS) ∧ k.args = [] := by decide +kernel

/-- **The values of Col are `r` and `g`.** -/
theorem col_values {v : GroundTerm} (h : c.sortOf v = some col) : ∃ b, v = colOf b := by
  obtain ⟨f, ts, k, rfl, hk, hs, he⟩ := ctor_of_sort noOvls noRaw h col_facts.1 col_facts.2.1 col_dv
  have hfk : k ∈ c.ctorSigs ∧ k.name = f := by
    rw [lookupSig_eq] at hk
    exact ⟨List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk⟩
  obtain ⟨hn, ha⟩ := col_facts.2.2 k hfk.1 he.symm
  rw [ha] at hs
  obtain rfl := sortsOf_inv_nil hs
  rw [hfk.2] at hn
  rcases hn with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

/-! ### The clause in a semantics that reads it -/

/-- `x ~> .K`. -/
def kOf (x : GroundTerm) : GroundTerm := .ctor kseq [injNormal col Srt.kitem x, .ctor dotk []]

/-- `=/=K` at every pair of terms (domains.md 2355, `notBool (K1 ==K K2)`). -/
theorem kNe_hook (a b : GroundTerm) : hook kNe [a, b] = some (some (bool (!decide (a = b)))) := by
  rw [hook_eq]
  have hf : hookTable.find? (·.1 == kNe) = some (kNe, fun vs => match vs with
      | [a, b] => some (bool (GroundTerm.cmp a b != .eq)) | _ => none) := rfl
  rw [hf]
  have hc : (GroundTerm.cmp a b != .eq) = !decide (a = b) := by
    by_cases h : a = b
    · subst h; simp [GroundTerm.cmp_refl]
    · have hne : GroundTerm.cmp a b ≠ .eq := fun h' => h (cmp_eq_iff.mp h')
      simp [h, hne]
  simp only [Option.map_some, hc]

/-- Two values of Col under `~> .K` differ exactly where they do. -/
theorem ne_col (a b : Bool) : (!decide (kOf (colOf a) = kOf (colOf b))) = (a != b) := by
  cases a <;> cases b <;> decide +kernel

theorem sr_bool (t : Bool) : sameResult (some (bool t)) (some (.dv Srt.bool (.bool true))) = t := by
  cases t <;> decide +kernel

/-- What a semantics must give for the clause to be read in it: `=/=K` the hook, `~>` and `.K`
constructors, and Col with the values `r` and `g`. -/
structure Reads (d : Semantics) : Prop where
  ne : d.isCtor kNe = false
  kseq : d.isCtor kseq = true
  dotk : d.isCtor dotk = true
  sort : ∀ b, d.sortOf (colOf b) = some col
  values : ∀ {v}, d.sortOf v = some col → ∃ b, v = colOf b

section Clause

variable {d : Semantics} {σ : Subst}

theorem neHook : isHook kNe = true := by decide +kernel

theorem evalK (hd : Reads d) {i : Nat} {x : GroundTerm} (hi : σ.lookup i = some x) :
    EvalTerm d σ (kOfVar i) (some (kOf x)) := by
  have h : EvalTerm d σ (kOfVar i) _ :=
    .ctor hd.kseq (.cons (.inj (a := col) (b := Srt.kitem) (.var (i := i))) (.cons (.ctor hd.dotk .nil) .nil))
  rw [hi] at h
  exact h

theorem evalK_inv (hd : Reads d) {i : Nat} {x : GroundTerm} (hi : σ.lookup i = some x)
    {r : Option GroundTerm} (h : EvalTerm d σ (kOfVar i) r) : r = some (kOf x) := by
  obtain ⟨rs, hts, rfl⟩ := EvalTerm.ctor_inv hd.kseq h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := terms2_inv hts
  obtain ⟨r1', h1', rfl⟩ := EvalTerm.inj_inv h1
  obtain rfl := EvalTerm.var_inv h1'
  obtain ⟨rs2, hts2, rfl⟩ := EvalTerm.ctor_inv hd.dotk h2
  obtain rfl := EvalTerms.nil_inv hts2
  rw [hi]; rfl

/-- The clause's `post` at a match giving X the value `colOf b` and C the value `colOf a`: whether
the two differ. -/
theorem post_holds (hd : Reads d) {a b : Bool} (h0 : σ.lookup 0 = some (colOf b))
    (h1 : σ.lookup 1 = some (colOf a)) : Holds d 2 σ clP.post (a != b) := by
  have hne : EvalTerm d σ (.app kNe [kOfVar 1, kOfVar 0]) (some (bool (a != b))) :=
    .hook hd.ne neHook (.cons (evalK hd h1) (.cons (evalK hd h0) .nil))
      (fun vs hvs => by
        cases hvs
        rw [Semantics.hookRes_of_value (kNe_hook _ _), ne_col])
      (fun hn => by cases hn)
  exact holds_cast (Holds.equals hne .dv) (sr_bool _)

theorem post_inv (hd : Reads d) {a b : Bool} (h0 : σ.lookup 0 = some (colOf b))
    (h1 : σ.lookup 1 = some (colOf a)) {t : Bool} (h : Holds d 2 σ clP.post t) : t = (a != b) := by
  cases h with
  | equals hl hr =>
    obtain ⟨rs, hts, hh, -⟩ := hook_inv hd.ne neHook hl
    obtain ⟨r1, r2, rfl, e1, e2⟩ := terms2_inv hts
    obtain rfl := evalK_inv hd h1 e1
    obtain rfl := evalK_inv hd h0 e2
    have := hh _ rfl
    rw [Semantics.hookRes_of_value (kNe_hook _ _), ne_col] at this
    obtain rfl := Option.some.inj this
    obtain rfl := EvalTerm.dv_inv hr
    exact sr_bool _

/-- **Every instance is decided and gives the other value of Col or nothing**: at C the other
value it gives it, at C := x its `post` is false. -/
theorem inst_all (hd : Reads d) {b : Bool} (h0 : σ.lookup 0 = some (colOf b))
    (hw : d.WellSorted clP.vars σ) : InstIs d σ clP (some (colOf (!b))) := by
  obtain ⟨w, hw1, hws⟩ := hw 1 col rfl
  obtain ⟨a, rfl⟩ := hd.values hws
  by_cases hab : a = !b
  · subst hab
    exact .gives (hw1 ▸ .var) (fun t ht => nomatch ht)
      (holds_cast (post_holds hd h0 hw1) (by cases b <;> rfl))
  · exact .fails (post_holds hd h0 hw1)
      (.post (holds_cast (post_holds hd h0 hw1) (by cases a <;> cases b <;> simp at hab ⊢)))

/-- The instance at C the other value does not give nothing. -/
theorem inst_not_none (hd : Reads d) {b : Bool} (h0 : σ.lookup 0 = some (colOf b))
    (h1 : σ.lookup 1 = some (colOf (!b))) : ¬ InstIs d σ clP none := by
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := post_inv hd h0 h1 hp
      cases b <;> cases e
    | rhs h => have := EvalTerm.var_inv h; rw [h1] at this; cases this

theorem ext_sorted (hd : Reads d) {b : Bool} (h0 : σ.lookup 0 = some (colOf b)) (a : Bool) :
    d.WellSorted clP.vars ((1, colOf a) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) (hd.sort b) (lkSelf _ _ _) (hd.sort a)

theorem ext_agree (σ : Subst) (w : GroundTerm) : AgreeOff clP.exsFree σ ((1, w) :: σ) := agree_set1 σ w

theorem agree_x {σ' : Subst} (h : AgreeOff clP.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by decide)

/-- **`pick(x)` is the other value of Col**, by `Eval.clauseEx` at C the other value. -/
theorem value (hd : Reads d) (hfn : d.lookupFn pickS = some fnP) (b : Bool) :
    Eval d pickS [colOf b] (some (colOf (!b))) :=
  have h0 : ([(1, colOf (!b)), (0, colOf b)] : Subst).lookup 0 = some (colOf b) := rfl
  .clauseEx (fn := fnP) (cl := clP) (σ := [(1, colOf (!b)), (0, colOf b)]) hfn (List.mem_singleton_self _)
    (sorted2 rfl (hd.sort b) rfl (hd.sort (!b))) (.cons (.var rfl) .nil)
    (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnP, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) .var (fun t ht => nomatch ht)
    (holds_cast (post_holds hd h0 rfl) (by cases b <;> rfl))
    (fun σ' ha hw => inst_all hd ((agree_x ha).trans h0) hw)

/-- **`pick(x)` has no other result.** -/
theorem alone (hd : Reads d) (hfn : d.lookupFn pickS = some fnP) {b : Bool}
    {r : Option GroundTerm} (h : Eval d pickS [colOf b] r) : r = some (colOf (!b)) := by
  have hcl : ∀ {cl fn'}, d.lookupFn pickS = some fn' → cl ∈ fn'.clauses → cl = clP := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnP] using h2
  have hx : ∀ {σ : Subst}, PatVals d σ clP.pats [colOf b] → σ.lookup 0 = some (colOf b) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clP (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clP.vars [(1, colOf b), (0, colOf b)] := sorted2 rfl (hd.sort b) rfl (hd.sort b)
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem hσ hmatch _ _ _ _ hrhs _ hpost _ =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨w, hw1, hws⟩ := hσ 1 col rfl
    obtain ⟨a, rfl⟩ := hd.values hws
    have e := post_inv hd (hx hmatch) hw1 hpost
    have hv := EvalTerm.var_inv hrhs
    rw [hw1] at hv
    rw [hv]
    cases a <;> cases b <;> first | rfl | cases e
  | @exNone _ _ _ _ σ hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    have h0 := hx hmatch
    exact absurd (hall _ (ext_agree σ _) (ext_sorted hd h0 (!b)))
      (inst_not_none hd ((lkNe _ _ (by decide)).trans h0) (lkSelf _ _ _))

end Clause

/-! ### The expectations, for every H -/

/-- The text's semantics reads the clause, under every H. -/
theorem readsH (H : HookParams) : Reads (cH H) where
  ne := (isCtor_wh c H _).trans flags.1
  kseq := (isCtor_wh c H _).trans flags.2.1
  dotk := (isCtor_wh c H _).trans flags.2.2
  sort := fun b => by rw [Semantics.sortOf_withHooks c H noRaw]; exact col_sort b
  values := fun h => by rw [Semantics.sortOf_withHooks c H noRaw] at h; exact col_values h

theorem lookupPH (H : HookParams) : (cH H).lookupFn pickS = some fnP := by
  rw [Semantics.lookupFn_withHooks]; exact lookupP

/-- **The values of Col are `r` and `g`, for every H.** -/
theorem col_valuesH (H : HookParams) {v : GroundTerm} (h : (cH H).sortOf v = some col) : ∃ b, v = colOf b :=
  (readsH H).values h

/-- **`pick(x)` is the other value of Col, for every H.** -/
theorem pick_value (H : HookParams) (b : Bool) : Eval (cH H) pickS [colOf b] (some (colOf (!b))) :=
  value (readsH H) (lookupPH H) b

/-- **`pick(x)` has no other result, for every H.** -/
theorem pick_alone (H : HookParams) {b : Bool} {r : Option GroundTerm} (h : Eval (cH H) pickS [colOf b] r) :
    r = some (colOf (!b)) :=
  alone (readsH H) (lookupPH H) h

/-- **`pick(r) = g`, for every H.** -/
theorem pick_r (H : HookParams) : Eval (cH H) pickS [.ctor rS []] (some (.ctor gS [])) := pick_value H false

/-- **`pick(r)` has no result but `g`, for every H.** -/
theorem pick_r_alone (H : HookParams) {r : Option GroundTerm} (h : Eval (cH H) pickS [.ctor rS []] r) :
    r = some (.ctor gS []) := pick_alone H (b := false) h

end ExClauseFixtures.ExCtor

/-- info: 'ExClauseFixtures.ExCtor.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.ExCtor.read
/-- info: 'ExClauseFixtures.ExCtor.col_valuesH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCtor.col_valuesH
/-- info: 'ExClauseFixtures.ExCtor.pick_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCtor.pick_value
/-- info: 'ExClauseFixtures.ExCtor.pick_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCtor.pick_alone
/-- info: 'ExClauseFixtures.ExCtor.pick_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCtor.pick_r
/-- info: 'ExClauseFixtures.ExCtor.pick_r_alone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.ExCtor.pick_r_alone
