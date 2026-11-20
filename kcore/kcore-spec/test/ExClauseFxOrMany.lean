/-
  The fixture e3-ml-eq-rhs-or-many (`rule k(_) => 1 #Or 2 #Or … #Or 9`, k `[function, total]` over
  Int): the clause the reader gives for its text, the results of `k`, and that the text has no
  model, for every hook interpretation. Run from the package root:
  `lake env lean -j1 test/ExClauseFxOrMany.lean`.

  The text is `f2-examples/e3-ml-eq-rhs-or-many.kompile.kore`; sentence numbers are `AxiomDecl.index`:
  235 is k's equation `k(X0) = (((1 ∨ 2) ∨ 3) ∨ … ∨ 9) ∧ \top` (with `X0 ∈ _Gen0`), 95 k's functional
  sentence `∃Val. Val = k(K0)`.

  From the sentences: k(x) is the set {1, …, 9} (235) and one element of Int (95). The nine values
  are distinct elements, so the text has no model.

  The statements are on `defn`, the definition the reader gives for the text, each for every H:
  - The clause read is `clK` (`read`): `[_Gen0:Int, #Or0:Int]`, `exs [1]`, `rhs #Or0`, `post` the
    disjunction of the nine memberships `#Or0 ∈ k`, nested as the text nests them; k is `total`.
  - `no_result`: `k(n)` has no result at all, neither a value nor none. The instances at #Or0 := 1
    and #Or0 := 2 give 1 and 2, so no `Eval.clauseEx` derivation exists (it asks every instance to
    give the one value or nothing), no `Eval.exNone` (it asks every instance to give nothing), and
    the clause applies at every argument, so no `Eval.rest`.
  - `not_matchIndependent`: the owed fact the package names for the clause (`MatchIndependent`) is
    false: the clause decides at every argument and has no result there (`Clause.Res`).
  - `not_fnHyp`: `FnHyp` is false (k has no result at 0).
  - `no_model` (C7 form (r)): the premise set `Pre H` is the two sentences 235 and 95 as the text
    writes them, with the signature (`ΓSig`: definedness, the sort Int) and the domains of the
    reading (`ΓDomains`: each Int value one element of Int, distinct Int values distinct elements),
    and nothing else of Γ. Read at X0 = _Gen0 = 1: 235 puts the elements of 1 and of 2 in k(1), 95
    makes k(1) one element of Int, and 1 and 2 are distinct elements.
  Nothing is stated of Γ's consistency: Γ holds no functional axiom of a function, and k's clause,
  read as the union its sentence states, gives k(x) the nine elements.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse

/-! ## Common facts -/

namespace ExClauseFixtures.OrManyFx

open GroundTerm

variable {d : Semantics} {σ : Subst}

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

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

/-- The predicate p has the truth value b under σ, and no other. -/
def Dec (d : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  Holds d n σ p b ∧ ∀ t, Holds d n σ p t → t = b

theorem dec_or {n : Nat} {p q : Cond} {b b' : Bool} (hp : Dec d n σ p b) (hq : Dec d n σ q b') :
    Dec d n σ (.or p q) (b || b') :=
  ⟨.or hp.1 hq.1, fun t ht => by cases ht with | or h h' => rw [hp.2 _ h, hq.2 _ h']⟩

end ExClauseFixtures.OrManyFx

namespace ExClauseFixtures.OrMany

open GroundTerm ExClauseFixtures.OrManyFx

kore_term kore from "f2-examples/e3-ml-eq-rhs-or-many.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or-many.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or-many.kompile.kore" module "E3-ML-EQ-RHS-OR-MANY"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fK : Sym := 384

/-- The membership `#Or0 ∈ k` of the disjunction's variable (the variable 1) in the literal k. -/
def memK (k : Int) : Cond := .mem Srt.int (.var 1) (.dv Srt.int (.int k))

/-- `((#Or0 ∈ 1 ∨ #Or0 ∈ 2) ∨ #Or0 ∈ 3) ∨ … ∨ #Or0 ∈ 9`, nested as the text nests the disjunctions. -/
def postK : Cond := [2, 3, 4, 5, 6, 7, 8, 9].foldl (fun p k => .or p (memK k)) (memK 1)

/-- `k(_Gen0) => #Or0` with `exs = [#Or0]` and `post := postK`, both variables of Int. -/
def clK : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postK }

def fnK : Fn := { label := fK, args := [Srt.int], result := Srt.int, clauses := [clK], total := true }

/-- **The reading**: the text's one function is `k`, `total`, with the one clause `clK`. -/
theorem read : c.fns = [fnK] := by kernel_rfl

theorem names : c.symName fK = "Lblk" ∧ c.sortName Srt.int = "Int" := by decide +kernel

/-- #Or0 is not of a confined sort; each alternative fixes it by a literal: `clausePlainEx` admits
the clause. -/
theorem plainEx : c.confined Srt.int = false ∧ c.clausePlainEx clK = true := by decide +kernel

theorem lookupK : c.lookupFn fK = some fnK := by rw [Semantics.lookupFn_eq]; rfl
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ### The clause in a semantics that reads it -/

section Clause

variable {d : Semantics} {σ : Subst}

/-- The truth value of `#Or0 ∈ k` where #Or0 has the value w. -/
def memVal (w : GroundTerm) (k : Int) : Bool := sameResult (some w) (some (int k))

theorem dec_mem {n : Nat} {w : GroundTerm} (h1 : σ.lookup 1 = some w) (k : Int) :
    Dec d n σ (memK k) (memVal w k) := by
  refine ⟨holds_cast (Holds.mem .var .dv) (by rw [h1]; rfl), fun t ht => ?_⟩
  cases ht with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := EvalTerm.dv_inv h'
    rw [h1]; rfl

theorem dec_fold {n : Nat} {w : GroundTerm} (h1 : σ.lookup 1 = some w) :
    ∀ (ks : List Int) (p : Cond) (b : Bool), Dec d n σ p b →
      Dec d n σ (ks.foldl (fun p k => .or p (memK k)) p) (ks.foldl (fun b k => b || memVal w k) b)
  | [], _, _, h => h
  | k :: ks, _, _, h => dec_fold h1 ks _ _ (dec_or h (dec_mem h1 k))

/-- The truth value of the clause's `post` where #Or0 has the value w: whether w is one of the nine
literals. -/
def postVal (w : GroundTerm) : Bool := [2, 3, 4, 5, 6, 7, 8, 9].foldl (fun b k => b || memVal w k) (memVal w 1)

theorem dec_post {n : Nat} {w : GroundTerm} (h1 : σ.lookup 1 = some w) : Dec d n σ postK (postVal w) :=
  dec_fold h1 _ _ _ (dec_mem h1 1)

theorem postVal_1 : postVal (int 1) = true := by decide +kernel
theorem postVal_2 : postVal (int 2) = true := by decide +kernel

/-- An instance at which #Or0 is the literal k of the nine gives k: its `post` is true. -/
theorem inst_eq {σ' : Subst} {k : Int} {r : Option GroundTerm} (h1 : σ'.lookup 1 = some (int k))
    (hk : postVal (int k) = true) (h : InstIs d σ' clK r) : r = some (int k) := by
  cases h with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := (dec_post (d := d) h1).2 _ hp
      rw [hk] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- **The instances at #Or0 := 1 and #Or0 := 2 do not agree on one result**: no r is the result of
every instance of the clause at a match giving `_Gen0` a value of Int. -/
theorem two_insts {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm}
    (hall : ∀ σ', AgreeOff clK.exsFree σ σ' → d.WellSorted clK.vars σ' → InstIs d σ' clK r) : False := by
  have hw : ∀ k : Int, d.WellSorted clK.vars ((1, int k) :: σ) := fun k =>
    sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) (rmS_sortOf_int d k)
  have e1 := inst_eq (lkSelf 1 (int 1) σ) postVal_1 (hall _ (agree_set1 σ _) (hw 1))
  have e2 := inst_eq (lkSelf 1 (int 2) σ) postVal_2 (hall _ (agree_set1 σ _) (hw 2))
  rw [e1] at e2
  exact absurd e2 (by decide)

/-- **`k(x)` has no result**, at every value x of Int. -/
theorem no_res (hfn : d.lookupFn fK = some fnK) {x : GroundTerm} (hx : d.sortOf x = some Srt.int)
    {r : Option GroundTerm} (h : Eval d fK [x] r) : False := by
  have hcl : ∀ {cl fn'}, d.lookupFn fK = some fn' → cl ∈ fn'.clauses → cl = clK := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnK] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clK.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clK (List.mem_singleton_self _) with
    | intro hF =>
      have hs : d.WellSorted clK.vars [(1, x), (0, x)] := sorted2 rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd hex (by decide)
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts (hx0 hmatch) hx hall
  | exNone hfn' hmem _ _ hmatch _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    exact two_insts (hx0 hmatch) hx hall

/-- **The clause is not match independent**: it decides at `[0]` and has no result there. -/
theorem not_mi (hfn : d.lookupFn fK = some fnK) : ¬ MatchIndependent d clK := by
  intro hm
  have hs : d.WellSorted clK.vars [(1, int 0), (0, int 0)] :=
    sorted2 rfl (rmS_sortOf_int d 0) rfl (rmS_sortOf_int d 0)
  have hdec : clK.Decides d fnK [(1, int 0), (0, int 0)] [int 0] :=
    ⟨⟨hs.at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnK, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 (by decide) fK fnK [int 0] _ hfn (List.mem_singleton_self _) hdec
  unfold Clause.Res Clause.ResEx at hr
  rcases hr with ⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, -, hall⟩⟩
  · exact absurd hex (by decide)
  · exact two_insts (σ := [(1, int 0), (0, int 0)]) rfl (rmS_sortOf_int d 0) hall
  · exact two_insts (σ := [(1, int 0), (0, int 0)]) rfl (rmS_sortOf_int d 0) hall

end Clause

/-! ### The results, for every H -/

theorem lookupKH (H : HookParams) : (cH H).lookupFn fK = some fnK := by
  rw [Semantics.lookupFn_withHooks]; exact lookupK

/-- **`k(n)` has no result, for every H and every n**: neither a value nor none. -/
theorem no_result (H : HookParams) (n : Int) (r : Option GroundTerm) : ¬ Eval (cH H) fK [int n] r :=
  fun h => no_res (lookupKH H) (rmS_sortOf_int _ n) h

/-- **The owed fact the package names for k's clause, `MatchIndependent`, is false, for every H.** -/
theorem not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) clK := not_mi (lookupKH H)

/-- **`FnHyp` is false, for every H**: k has no result at 0. -/
theorem not_fnHyp (H : HookParams) : ¬ FnHyp (cH H) := by
  intro hf
  have hso : (cH H).sortsOf [int 0] = some fnK.args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw]; rfl
  obtain ⟨r, hr⟩ := hf.1 fnK (by rw [show (cH H).fns = c.fns from rfl, read]; exact List.mem_singleton_self _) [int 0] hso
  exact no_result H 0 r hr

/-! ## The text has no model -/

section NoModel

open ML Faithful KoreAML

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

def sI : Kore.KSort := srt "Int"
def vX0 : Kore.Pattern := ev "X0" sI
def kX0 : VarKey := .evar "X0" sI
def nG : String := "Var'Unds'Gen0"

/-- The premise `\top ∧ (X0 ∈ _Gen0 ∧ \top)` of k's equation. -/
def premP : Kore.Pattern :=
  .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in sI KoreAML.R vX0 (ev nG sI), .top KoreAML.R]]

/-- `(((1 ∨ 2) ∨ 3) ∨ …) ∨ 9`, the right side of k's equation. -/
def orRhs : Kore.Pattern :=
  ["3", "4", "5", "6", "7", "8", "9"].foldl (fun p k => .or sI [p, .dv sI k]) (.or sI [.dv sI "1", .dv sI "2"])

theorem s235 : U.ax235.ax.pattern =
    .implies KoreAML.R premP (.equals sI KoreAML.R (ap "Lblk" [vX0]) (.and sI [orRhs, .top sI])) := by
  decide +kernel
theorem s95 : U.ax95.ax.pattern =
    .exist KoreAML.R (evar "Val" sI) (.equals sI KoreAML.R (ev "Val" sI) (ap "Lblk" [ev "K0" sI])) := by
  decide +kernel
theorem trS_plain : (trS U.ax95).pat = (trAxiom [] [] U.ax95).pat ∧ (trS U.ax235).pat = (trAxiom [] [] U.ax235).pat := by
  decide +kernel

theorem free235 : (U.ax235.ax.sortVars.map sortVarKey ++ freeOf [] U.ax235.ax.pattern).eraseDups =
    [.sortVar "R", kX0, .evar nG sI] := by decide +kernel
/-- The table's numbering: the sort variable R is 1, X0 is 2, _Gen0 is 3. -/
theorem tab235 : (tableOf U.ax235.ax.sortVars U.ax235.ax.pattern).ev (.sortVar "R") = ⟨1⟩ ∧
    (tableOf U.ax235.ax.sortVars U.ax235.ax.pattern).ev kX0 = ⟨2⟩ ∧
    (tableOf U.ax235.ax.sortVars U.ax235.ax.pattern).ev (.evar nG sI) = ⟨3⟩ := by decide +kernel
theorem free95 : (U.ax95.ax.sortVars.map sortVarKey ++ freeOf [] U.ax95.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K0" sI] := by decide +kernel
theorem tab95 : (tableOf U.ax95.ax.sortVars U.ax95.ax.pattern).ev (.sortVar "R") = ⟨1⟩ ∧
    (tableOf U.ax95.ax.sortVars U.ax95.ax.pattern).ev (.evar "Val" sI) = ⟨2⟩ ∧
    (tableOf U.ax95.ax.sortVars U.ax95.ax.pattern).ev (.evar "K0" sI) = ⟨3⟩ := by decide +kernel

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The valuation the refutation reads the sentences at: the sort variable R (variable 1) is Int,
every other element variable the element m1. -/
def valAt (σI m1 : M) : Valuation M := ⟨Function.update (fun _ => m1) ⟨1⟩ σI, KoreAML.val0.evalSvar⟩

theorem valAt_1 (σI m1 : M) : (valAt σI m1).evalEvar ⟨1⟩ = σI := by
  simp [valAt]
theorem valAt_ne (σI m1 : M) {x : EVar} (h : x ≠ ⟨1⟩) : (valAt σI m1).evalEvar x = m1 := by
  simp [valAt, Function.update_noteq h]

/-- **k's equation (235) read at `valAt`**: where X0 and _Gen0 are the element m1 of Int, the
elements of Int in `k(X0)` are those of the disjunction of the nine literals. -/
theorem eqn_read (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M}
    (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI2 : IsSort I σI)
    (hT : I ⊧ᴵ (trAxiom [] [] U.ax235).pat) (m1 : M) (hm1 : Inh I σI m1) (b : M) (hb : Inh I σI b) :
    ((sym (.symbol "Lblk") ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b ↔
      (tr ⟨tableOf U.ax235.ax.sortVars U.ax235.ax.pattern, []⟩ orRhs).interpret I (valAt σI m1) b) := by
  have h := hT (valAt σI m1) m1
  unfold trAxiom at h
  dsimp only at h
  rw [free235] at h
  have htab := tab235
  generalize ht : tableOf U.ax235.ax.sortVars U.ax235.ax.pattern = t at h htab ⊢
  obtain ⟨h1, h2, h3⟩ := htab
  rw [s235] at h
  rw [interpret_impl] at h
  have hS : ∀ b, (trSort t sI).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h2v : (valAt σI m1).evalEvar (t.ev kX0) = m1 := by rw [h2]; exact valAt_ne σI m1 (by decide)
  have h3v : (valAt σI m1).evalEvar (t.ev (.evar nG sI)) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hg : (conjList ([VarKey.sortVar "R", kX0, .evar nG sI].map (guardOf t))).interpret I (valAt σI m1) m1 := by
    simp only [List.map, conjList, interpret_conj]
    refine ⟨(interp_guard_sortVar hD).mpr (by rw [h1, valAt_1]; exact hσI2), ?_, ?_⟩
    · exact (interp_guard_evar hD).mpr (by rw [show (VarKey.evar "X0" sI) = kX0 from rfl, h2v]; exact (interp_inhOf_of hS).mpr hm1)
    · exact (interp_guard_evar hD).mpr (by rw [h3v]; exact (interp_inhOf_of hS).mpr hm1)
  have h4 := (interp_equal hD).mp (h hg) m1
  simp only [sortOf] at h4
  have h5 := h4.mpr ((interp_inhOf_of hRv).mpr hm1)
  rw [KoreAML.tr, interp_sImp] at h5
  have hprem : (tr ⟨t, []⟩ premP).interpret I (valAt σI m1) m1 := by
    have hvx0 : tr ⟨t, []⟩ vX0 = .evar (t.ev kX0) := rfl
    have hvx : tr ⟨t, []⟩ (ev nG sI) = .evar (t.ev (.evar nG sI)) := rfl
    have htop : (tr ⟨t, []⟩ (.top KoreAML.R)).interpret I (valAt σI m1) m1 := by
      rw [KoreAML.tr, interp_sTop hD (by rw [trSort_R, h1]; rfl), interp_inhOf_of hRv]; exact hm1
    unfold premP
    rw [interp_and (List.cons_ne_nil _ _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨htop, ?_⟩
    rw [interp_and (List.cons_ne_nil _ _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, htop⟩
    rw [KoreAML.tr, hvx0, hvx]
    exact (interp_sIn_evar_svin hD hc hS hRv hσI2 hσI2 (by rw [h2v]; exact hm1) m1).mpr ⟨h2v.trans h3v.symm, hm1⟩
  have h6 := h5.2 hprem
  rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hσI2] at h6
  have h7 := h6.2 b hb
  have hF : tr ⟨t, []⟩ (ap "Lblk" [vX0]) = sym (.symbol "Lblk") ⬝ .evar ⟨2⟩ := by
    unfold ap vX0 ev; rw [tr_app0, trArgs_cons, trArgs_nil, KoreAML.tr]; rw [show evarKey (evar "X0" sI) = kX0 from rfl, h2]
  rw [hF, interp_and (List.cons_ne_nil _ _)] at h7
  rw [h7]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [KoreAML.tr, interp_sTop hD (by unfold sI; rw [trSort_srt]; rfl), interp_inhOf_of hS]
  exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩

/-- **k's functional sentence (95) read at `valAt`**: `k(m1)` is one element of Int. -/
theorem fnl_read (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M}
    (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI2 : IsSort I σI)
    (hT : I ⊧ᴵ (trAxiom [] [] U.ax95).pat) (m1 : M) (hm1 : Inh I σI m1) :
    ∃ y, ∀ b, Inh I σI b → ((sym (.symbol "Lblk") ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b ↔ b = y) := by
  have h := hT (valAt σI m1) m1
  unfold trAxiom at h
  dsimp only at h
  rw [free95] at h
  generalize ht : tableOf U.ax95.ax.sortVars U.ax95.ax.pattern = t at h
  have htab := tab95
  rw [ht] at htab
  obtain ⟨h1, h2, h3⟩ := htab
  rw [s95] at h
  rw [interpret_impl] at h
  have hS : ∀ (e : Valuation M) b, (trSort t sI).interpret I e b ↔ b = σI := fun _ b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h3v : (valAt σI m1).evalEvar (t.ev (.evar "K0" sI)) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hg : (conjList ([VarKey.sortVar "R", .evar "K0" sI].map (guardOf t))).interpret I (valAt σI m1) m1 := by
    simp only [List.map, conjList, interpret_conj]
    refine ⟨(interp_guard_sortVar hD).mpr (by rw [h1, valAt_1]; exact hσI2), ?_⟩
    exact (interp_guard_evar hD).mpr (by rw [h3v]; exact (interp_inhOf_of (hS _)).mpr hm1)
  have h4 := (interp_equal hD).mp (h hg) m1
  simp only [sortOf] at h4
  have h5 := h4.mpr ((interp_inhOf_of hRv).mpr hm1)
  rw [KoreAML.tr, interp_sExists] at h5
  obtain ⟨y, -, h6⟩ := h5
  rw [show evarKey (evar "Val" sI) = VarKey.evar "Val" sI from rfl, h2] at h6
  generalize he' : (⟨Function.update (valAt σI m1).evalEvar ⟨2⟩ y, (valAt σI m1).evalSvar⟩ : Valuation M) = e' at h6
  have he'1 : e'.evalEvar ⟨1⟩ = σI := by
    rw [← he']; dsimp only; rw [Function.update_noteq (by decide), valAt_1]
  have he'2 : e'.evalEvar ⟨2⟩ = y := by
    rw [← he']; dsimp only; rw [Function.update_same]
  have he'3 : e'.evalEvar ⟨3⟩ = m1 := by
    rw [← he']; dsimp only; rw [Function.update_noteq (by decide), valAt_ne σI m1 (by decide)]
  have hR' : ∀ b, (trSort t KoreAML.R).interpret I e' b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, he'1]
  rw [KoreAML.tr, interp_sEquals hD hc (hS e') hR' hσI2 hσI2] at h6
  refine ⟨y, fun b hb => ?_⟩
  have h7 := h6.2 b hb
  have hv : tr ⟨t, []⟩ (ev "Val" sI) = .evar ⟨2⟩ := by
    unfold ev; rw [KoreAML.tr, show evarKey (evar "Val" sI) = VarKey.evar "Val" sI from rfl, h2]
  have hF : tr ⟨t, []⟩ (ap "Lblk" [ev "K0" sI]) = sym (.symbol "Lblk") ⬝ .evar ⟨3⟩ := by
    unfold ap ev; rw [tr_app0, trArgs_cons, trArgs_nil, KoreAML.tr, show evarKey (evar "K0" sI) = VarKey.evar "K0" sI from rfl, h3]
  rw [hv, hF, interp_evar, he'2] at h7
  refine (interp_app_congr (e := valAt σI m1) (e' := e') (φ := sym (.symbol "Lblk")) (φ' := sym (.symbol "Lblk"))
    (ψ := .evar ⟨2⟩) (ψ' := .evar ⟨3⟩) (fun _ => Iff.rfl) (fun m => ?_) b).trans h7.symm
  rw [interp_evar, interp_evar, he'3, valAt_ne σI m1 (by decide)]

omit [Inhabited M] in
/-- An element of Int in one side of a disjunction is in the disjunction. -/
theorem or_intro {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) {t : VarTable} {e : Valuation M}
    {p q : Kore.Pattern} {b : M} (hb : Inh I σI b)
    (h : (tr ⟨t, []⟩ p).interpret I e b ∨ (tr ⟨t, []⟩ q).interpret I e b) :
    (tr ⟨t, []⟩ (.or sI [p, q])).interpret I e b := by
  have ht : tr ⟨t, []⟩ (.or sI [p, q]) = sOr (trSort t sI) (tr ⟨t, []⟩ p) (tr ⟨t, []⟩ q) := by
    rw [KoreAML.tr]; simp only [trOrList]
  rw [ht, interp_sOr]
  exact ⟨(interp_inhOf_of (S := trSort _ sI) (fun b => by unfold sI; rw [trSort_srt]; exact hσI1 b)).mpr hb, h⟩

omit [Inhabited M] in
/-- An element of Int in the innermost disjunction is in the whole right side. -/
theorem fold_intro {σI : M} (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) {t : VarTable}
    {e : Valuation M} {b : M} (hb : Inh I σI b) :
    ∀ (ks : List String) (p : Kore.Pattern), (tr ⟨t, []⟩ p).interpret I e b →
      (tr ⟨t, []⟩ (ks.foldl (fun p k => .or sI [p, .dv sI k]) p)).interpret I e b
  | [], _, h => h
  | _ :: ks, _, h => fold_intro hσI1 hb ks _ (or_intro hσI1 hb (Or.inl h))

end NoModel

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem den_int1 (H : HookParams) : KCore.den (cH H) (KCore.int 1) = KoreAML.sym (.dv "1") ⬝ KoreAML.sym (.sort "SortInt") := by
  show KCore.den c (KCore.int 1) = _; decide +kernel
theorem den_int2 (H : HookParams) : KCore.den (cH H) (KCore.int 2) = KoreAML.sym (.dv "2") ⬝ KoreAML.sym (.sort "SortInt") := by
  show KCore.den c (KCore.int 2) = _; decide +kernel
theorem int_distinct (H : HookParams) : (Faithful.distinctSorts (cH H)).contains Srt.int = true := by
  unfold Faithful.distinctSorts
  exact List.contains_iff_mem.mpr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_cons_self ..)))))

section NoModel2

open ML Faithful KoreAML

/-- **The premises the refutation uses**: sentences 235 (`k(X) = 1 ∨ … ∨ 9`) and 95 (k is
functional) as the text writes them, with the signature and the domains of the reading (each Int
value one element of Int, distinct Int values distinct elements), for every H. No other item of Γ. -/
noncomputable def Pre (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts [(trS U.ax235).pat, (trS U.ax95).pat] ∪ ΓSig (cH H) ∪ ΓDomains (cH H)

/-- **The text's sentences have no model, for every H** (C7 form (r)): at X = 1, sentence 235 puts
the elements of 1 and of 2 in k(1), and 95 makes k(1) one element of Int; the values 1 and 2 of Int
are distinct elements. -/
theorem no_model (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Pre H := by
  rintro ⟨M, _, I, hI⟩
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inl (Or.inr hφ))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  have hT : ∀ φ ∈ [(trS U.ax235).pat, (trS U.ax95).pat], I ⊧ᴵ φ :=
    fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl hφ)))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
  rw [int_name] at hσI1
  have hSI : ∀ (e : Valuation M) b, (sortP "Int").interpret I e b ↔ b = σI := fun _ b => hσI1 b
  -- the elements of 1 and 2
  obtain ⟨m1, hm1d, hm1s⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int 1) = some Srt.int from rfl) KoreAML.val0
  obtain ⟨m2, hm2d, hm2s⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int 2) = some Srt.int from rfl) KoreAML.val0
  rw [int_name] at hm1s hm2s
  have hm1 : Inh I σI m1 := (interp_inhOf_of (hSI _)).mp hm1s
  have hm2 : Inh I σI m2 := (interp_inhOf_of (hSI _)).mp hm2s
  let e := valAt σI m1
  have hden1 : ∀ b, (den (cH H) (KCore.int 1)).interpret I e b ↔ b = m1 := fun b =>
    ((den_closed (cH H) (KCore.int 1)).interp e KoreAML.val0 b).trans (hm1d b)
  have hden2 : ∀ b, (den (cH H) (KCore.int 2)).interpret I e b ↔ b = m2 := fun b =>
    ((den_closed (cH H) (KCore.int 2)).interp e KoreAML.val0 b).trans (hm2d b)
  -- 235: k(1) holds the elements of 1 and 2
  have hC := eqn_read hD hc hσI1 hσI2 (by rw [← trS_plain.2]; exact hT _ (by simp)) m1 hm1
  have hk : ∀ b, Inh I σI b → ((tr ⟨tableOf U.ax235.ax.sortVars U.ax235.ax.pattern, []⟩ (.dv sI "1")).interpret I e b ∨
      (tr ⟨tableOf U.ax235.ax.sortVars U.ax235.ax.pattern, []⟩ (.dv sI "2")).interpret I e b) →
      (sym (.symbol "Lblk") ⬝ .evar ⟨2⟩).interpret I e b := fun b hb h =>
    (hC b hb).mpr (fold_intro hσI1 hb _ _ (or_intro hσI1 hb h))
  have hk1 := hk m1 hm1 (Or.inl (by
    show (KoreAML.sym (.dv "1") ⬝ KoreAML.sym (.sort "SortInt")).interpret I e m1
    rw [← den_int1 H]; exact (hden1 m1).mpr rfl))
  have hk2 := hk m2 hm2 (Or.inr (by
    show (KoreAML.sym (.dv "2") ⬝ KoreAML.sym (.sort "SortInt")).interpret I e m2
    rw [← den_int2 H]; exact (hden2 m2).mpr rfl))
  -- 95: k(1) is one element of Int
  obtain ⟨y, hy⟩ := fnl_read hD hc hσI1 hσI2 (by rw [← trS_plain.1]; exact hT _ (by simp)) m1 hm1
  have e1 : m1 = y := (hy m1 hm1).mp hk1
  have e2 : m2 = y := (hy m2 hm2).mp hk2
  -- 1 and 2 are distinct elements of Int
  have hax := hDom _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.int 1, KCore.int 2, Srt.int, int_distinct H, rfl, rfl,
    by decide, rfl⟩))))
  have := hax e m1
  rw [interpret_neg, interpret_conj] at this
  exact this ⟨(hden1 m1).mpr rfl, (hden2 m1).mpr (e1.trans e2.symm)⟩

end NoModel2

end ExClauseFixtures.OrMany

/-- info: 'ExClauseFixtures.OrMany.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.OrMany.read
#print axioms ExClauseFixtures.OrMany.no_result
#print axioms ExClauseFixtures.OrMany.not_matchIndependent
#print axioms ExClauseFixtures.OrMany.not_fnHyp
#print axioms ExClauseFixtures.OrMany.no_model
