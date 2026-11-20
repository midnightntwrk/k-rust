/-
  The function functional sentences of construct fixture e5-ovl-fun-clause at values in every model
  of `Γc`, for every H, on the literals `kore` and `defn`. Nothing here reads `Parse.parse` or
  `emit`. Written by hand; run from the package root:
  `lake env lean -j1 test/TieE5OvlFunClauseFnFun.lean`.

  `f2-examples/e5-ovl-fun-clause.kompile.kore` states 17 `functional` sentences of functions
  (indices 60, 64-79, the function functional class of the whole-text tie
  test/TieE5OvlFunClause.lean): sentence 60 of `capN : N → N`, declared total, and 16 of the sort
  predicates `isX`. The clause of `uncap` has the predicate `X ∈ capGas(G)` (`Clause.pre`), so
  `Semantics.clausesPreTop` is false (`preTop_false`); the statements here read no clause predicate
  as `\top`: the model reads a predicate through `PreRead`.
  - `fnFun_text`: the sentences are those of the indices, sentence 60 the `functional` sentence of
    a function of the text declared total, the others of a sort predicate (`fnFun_checked`), none
    reading a declaration or an alias (`fnFun_trS`).
  - `total_capN`: `capN` has a value at every argument list of its sorts, for every H: N holds `z`
    only (`val_N`) and `capN(z)` is `z` (`eval_z`).
  - `openClausesH`: no clause's condition is owed (`owed_clauses`), so each is decided where
    `needsWitness` holds, for every H.
  - `fnFun_at_values` (`EntailsAtValuesΓc`), and `fnFun_at_values_step` in every model of `Γc` with
    the step's closure, for every H: sentence 60 by `LibEv.fnFun_evC_pre`, the others by
    `LibEv.sortPredFun_evC_pre_withHooks`. The clauses bind no variable by `\exists`
    (`clauses_noExs`); a sort predicate's clauses have no existential variable and the right-side
    predicate `\top` by their text (`Semantics.sortPreds_exs`, `Semantics.sortPreds_post`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunClauseFnFun

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-clause.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-clause.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-clause.kompile.kore" module "E5-OVL-FUN-CLAUSE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## The reading of the functions -/

def gasS : Srt := 32
def nS : Srt := 33
def zS : Sym := 387
def capN : Sym := 388
def uncapS : Sym := 389
def capGas : Sym := 390

theorem syms_named : c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.symName zS = "Lblz" ∧
    c.symName capN = "LblcapN" ∧ c.symName uncapS = "Lbluncap" ∧ c.symName capGas = "LblcapGas" := by
  decide +kernel

/-- `capN(z #as X) = X`. -/
def capCl : Clause := { vars := [nS], pats := [.as (.app zS []) 0], req := none, rhs := .var 0, ens := none }
/-- `capN : N → N`, declared total. -/
def capNFn : Fn := ⟨capN, [nS], nS, [capCl], true⟩
/-- `uncap(X) = G` where `X ∈ capGas(G)`: X is V1, G is V0. -/
def uncapCl : Clause :=
  { vars := [gasS, gasS], pats := [.var 1], req := none, rhs := .var 0, ens := none,
    pre := .mem gasS (.var 1) (.app capGas [.var 0]) }
/-- `uncap : Gas → Gas`, not declared total. -/
def uncapFn : Fn := ⟨uncapS, [gasS], gasS, [uncapCl], false⟩
def zSig : CtorSig := ⟨zS, [], nS⟩

kernel_rfl fns_c : c.fns = [capNFn, uncapFn]
kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn capN = some capNFn
kernel_rfl isCtor_H : ∀ H : HookParams, (cH H).isCtor zS = true
kernel_rfl sort_z_H : ∀ H : HookParams, (cH H).sortOf (.ctor zS []) = some nS

/-- A clause's predicate is not `\top` (`uncapCl`'s membership), and no clause binds a variable by
`\exists`. -/
theorem preTop_false : c.clausesPreTop = false := by decide +kernel
theorem clauses_noExs : (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true := by
  decide +kernel

/-! ## `capN` has a value at every argument list of its sorts, for every H -/

/-- A sort whose one generator is a constant holds that constant only: no other constructor, no
overloading symbol and no raw parameter ends at it, nothing is below it, and it has neither
literals nor collections. -/
theorem onlyConst {c : Semantics} {s : Srt} {k0 : CtorSig} (ha : k0.args = [])
    (hk : ∀ k ∈ c.ctorSigs, k.result = s → k = k0)
    (ho : ∀ o ∈ c.ovls, o.sig.result ≠ s)
    (hp : ∀ k ∈ c.params, k.raw = false)
    (hsub : ∀ p ∈ c.subsorts, p.2 ≠ s)
    (hdv : ∀ lit, dvOK c.lib s lit = false)
    (hcoll : c.collOf s = none)
    {v : GroundTerm} (h : c.sortOf v = some s) : v = .ctor k0.name [] := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk', hs, hr⟩ | ⟨-, o, hlo, -, -, hr⟩ | ⟨-, -, k, hko, -⟩
    · obtain ⟨hm, hn⟩ := lookupSig_spec hk'
      have := hk k hm hr.symm
      subst this
      rw [ha] at hs
      rw [sortsOf_inv_nil hs, hn]
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec hlo
      exact absurd hr.symm (ho o (he ▸ List.getElem_mem hi))
    · obtain ⟨hm, hraw, -⟩ := Semantics.lookupOpen_spec _ hko
      rw [hp k hm] at hraw; cases hraw
  | inj a b t =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact absurd rfl (hsub _ (List.contains_iff_mem.mp hc.1.1))
    · cases h
  | dv s' lit =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc; cases h; rw [hdv lit] at hc; cases hc
    · cases h
  | map s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_map_sort h
    rw [hcoll] at hc; cases hc
  | set s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_set_sort h
    rw [hcoll] at hc; cases hc
  | list s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_list_sort h
    rw [hcoll] at hc; cases hc

/-- A sort that is no carrier of literals has none. -/
theorem noLit {l : Lib} {s : Srt}
    (h : (l.carrier s == Srt.int || l.carrier s == Srt.bool || l.carrier s == Srt.kconfigVar ||
      l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) || l.carrier s == Srt.bytes ||
      l.byteSorts.contains (l.carrier s) || l.carrier s == Srt.float) = false) (lit : Lit) :
    dvOK l s lit = false := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases lit <;> simp only [dvOK, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.or_self]

/-- **N holds `z` only.** -/
theorem val_N {v : GroundTerm} (h : c.sortOf v = some nS) : v = .ctor zS [] :=
  onlyConst (k0 := zSig) rfl (by decide +kernel) (by decide +kernel) noRaw (by decide +kernel)
    (noLit (by decide +kernel)) (by decide +kernel) h

/-- **`capN(z)` evaluates to `z`**, by its one clause, under every H. -/
theorem eval_z (H : HookParams) : Eval (cH H) capN [.ctor zS []] (some (.ctor zS [])) :=
  .clause (fn := capNFn) (cl := capCl) (σ := [(0, .ctor zS [])]) (lookupFn_H H) (List.mem_singleton_self _)
    (fun i s h => by
      cases i with
      | zero => cases h; exact ⟨.ctor zS [], rfl, sort_z_H H⟩
      | succ i => simp [capCl] at h)
    (.cons (.as (.ctor (isCtor_H H) .nil) rfl) .nil) (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      rw [show capNFn.clauses = [capCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t h => by cases h) .top

/-- **`capN` has a value at every argument list of its sorts, for every H**: its one clause decides
at `z`, the one value of N. -/
theorem total_capN (H : HookParams) : ∀ vs, (cH H).sortsOf vs = some capNFn.args →
    ∃ v, Eval (cH H) capNFn.label vs (some v) := fun vs hvs => by
  rw [show capNFn.args = [nS] from rfl, Semantics.sortsOf_withHooks _ _ noRaw] at hvs
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons hvs
  cases sortsOf_inv_nil hws
  cases val_N hw
  exact ⟨_, eval_z H⟩

/-- **The functions of the text declared total have a value at every argument list of their
sorts, for every H**: `capN` is the one. -/
theorem total_fns (H : HookParams) : ∀ fn ∈ c.fns, fn.total = true →
    ∀ vs, (cH H).sortsOf vs = some fn.args → ∃ v, Eval (cH H) fn.label vs (some v) := by
  intro fn hfn ht
  rw [fns_c] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · exact total_capN H
  · cases ht

/-! ## No condition is owed, for every H -/

theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- **Each clause's condition is decided where `needsWitness` holds, for every H**: none is owed. -/
theorem openClausesH (H : HookParams) :
    ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = true → cl.CondDecided (cH H) :=
  openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)

/-! ## Function functional (17), at values in every model of `Γc`, for every H -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [60, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) = fnFunIdx := by decide +kernel

/-- The sentence is the `functional` sentence, over the one sort variable `R`, of a function of the
text declared total, with its variables' sorts any of `c`, or of a sort predicate, with its
variables' sorts the registry's. -/
noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    ((c.fns.any fun fn => fn.total && decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunRegS c fn.sig) ||
     (c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig))

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- Sentence 60 is `capN`'s, and the 16 others are sort predicates'. -/
theorem fnFun_text : (U.ax60.ax.pattern = LibEv.funPat c capNFn.sig) ∧
    (fnFunText.filter (·.index != 60)).all (fun ad =>
      c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig)) = true := by
  decide +kernel

/-- None of the 17 reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), with a clause's predicate other than `\top`. -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
  simp only [fnFunOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany | hany⟩ := hok
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    obtain ⟨⟨ht, hp⟩, hr⟩ := hfp
    exact LibEv.fnFun_evC_pre (c := cH H) (coreOKH H) (Semantics.fnsNoExs_of_all clauses_noExs)
      (openClausesH H) (List.mem_append_left (cH H).sortPreds hfn) (total_fns H fn hfn ht)
      ((LibEv.predFunRegS_withHooksSP c H _).trans hr) ad (hp.trans (LibEv.funPat_withHooksSP c H _).symm) hsv
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    exact LibEv.sortPredFun_evC_pre_withHooks H coreOK (Semantics.fnsNoExs_of_all clauses_noExs)
      (openClausesH H) hfn hfp.2 ad hfp.1 hsv

/-- The same in every model of `Γc` with the step's closure, the theory `Consistent` asks a model of. -/
theorem fnFun_at_values_step (H : HookParams) : ∀ ad ∈ fnFunText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H)) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had M hM I hI => fnFun_at_values H ad had M hM I (fun φ hφ => hI φ (Or.inl hφ))

end KCore.TieE5OvlFunClauseFnFun

#check @KCore.TieE5OvlFunClauseFnFun.preTop_false
#check @KCore.TieE5OvlFunClauseFnFun.total_capN
#check @KCore.TieE5OvlFunClauseFnFun.openClausesH
#check @KCore.TieE5OvlFunClauseFnFun.fnFun_indices
#check @KCore.TieE5OvlFunClauseFnFun.fnFun_text
#check @KCore.TieE5OvlFunClauseFnFun.fnFun_at_values
#check @KCore.TieE5OvlFunClauseFnFun.fnFun_at_values_step
#print axioms KCore.TieE5OvlFunClauseFnFun.fnFun_at_values
#print axioms KCore.TieE5OvlFunClauseFnFun.fnFun_at_values_step
