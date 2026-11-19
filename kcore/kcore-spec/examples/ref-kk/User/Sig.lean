/-
  `KCore.KK.sig`: the signature the three statements of KKStatements.lean (`SuccsSound`,
  `SuccsStuck`, `SuccsComplete`) are about, on kore.k's semantics read from its kompiled text: the
  semantics `RefKk.defn.sem`, the symbol of `succs` (`succs_name` states its KORE name), the
  embeddings of User.Emb, and `enc`, `encDef` of KKEnc.lean and KKEncDef.lean.

  kore.k's member the statements read, `K₀ sig`, is the spike's `c₀` (`K₀_sig`), so every fact
  of the spike's modules at `c₀` is one at `K₀ sig`. The embeddings are values of their kore.k
  sorts there (`emb_sorted`, `embTs_sorted`, `embD_sorted`, `embSt_sorted`), and at
  `RefKk.defn.sem` itself, which has no parameter (the `_sem` forms).
-/
import User.Emb
import User.PrioDecided

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK

/-- kore.k's semantics, its `succs`, the embeddings and the encodings. -/
noncomputable def sig : Sig := ⟨RefKk.defn.sem, 510, emb, embD, embSt, enc, encDef⟩

/-- The symbol `sig` names is kore.k's `succs`. -/
theorem succs_name :
    RefKk.defn.sem.symName sig.succs = "Lblsuccs'LParUndsCommUndsRParUnds'KORE'Unds'Step'Unds'Def'Unds'Term" := by
  decide +kernel

theorem K₀_sig : K₀ sig = _root_.KK.c₀ := rfl

/-! ## Sorts at `K₀ sig` -/

theorem emb_sorted (t : T) : (K₀ sig).sortOf (emb t) = some 33 := emb_sorted_c₀ t
theorem embTs_sorted (ts : List T) : (K₀ sig).sortOf (embTs ts) = some 43 := embTs_sorted_c₀ ts
theorem embD_sorted (E : D) : (K₀ sig).sortOf (embD E) = some 45 := embD_sorted_c₀ E
theorem embSt_sorted (s : St) : (K₀ sig).sortOf (embSt s) = some 38 := embSt_sorted_c₀ s

/-! ## Sorts at `RefKk.defn.sem` -/

theorem sortOf_sem_kemb (v : GroundTerm) : RefKk.defn.sem.sortOf v = (K₀ sig).sortOf v :=
  (congrFun (Semantics.sortOf_withHooks RefKk.defn.sem HookParams.none
    (by intro k hk; rw [show RefKk.defn.sem.params = _root_.KK.c₀.params from rfl,
      _root_.KK.Prio.hparams] at hk; cases hk)) v).symm

theorem emb_sorted_sem (t : T) : RefKk.defn.sem.sortOf (emb t) = some 33 :=
  (sortOf_sem_kemb _).trans (emb_sorted t)
theorem embTs_sorted_sem (ts : List T) : RefKk.defn.sem.sortOf (embTs ts) = some 43 :=
  (sortOf_sem_kemb _).trans (embTs_sorted ts)
theorem embD_sorted_sem (E : D) : RefKk.defn.sem.sortOf (embD E) = some 45 :=
  (sortOf_sem_kemb _).trans (embD_sorted E)
theorem embSt_sorted_sem (s : St) : RefKk.defn.sem.sortOf (embSt s) = some 38 :=
  (sortOf_sem_kemb _).trans (embSt_sorted s)

/-! ## The sort numbers are kore.k's sorts -/

/-- The sort numbers the embeddings' values have are the KORE sorts of the productions they
write. -/
theorem emb_sortNames :
    RefKk.defn.sem.sortName 32 = "Subs" ∧ RefKk.defn.sem.sortName 33 = "Term" ∧
    RefKk.defn.sem.sortName 34 = "Kind" ∧ RefKk.defn.sem.sortName 35 = "Clauses" ∧
    RefKk.defn.sem.sortName 38 = "Step" ∧ RefKk.defn.sem.sortName 39 = "Fns" ∧
    RefKk.defn.sem.sortName 42 = "Rules" ∧ RefKk.defn.sem.sortName 43 = "Ts" ∧
    RefKk.defn.sem.sortName 45 = "Def" := by
  decide +kernel

/-- `succs` takes a `Def` and a `Term` and gives a `Step`: `embD`'s, `emb`'s and `embSt`'s sorts. -/
theorem succs_sig_kemb :
    ((K₀ sig).lookupFn sig.succs).map (fun fn => (fn.args, fn.result)) = some ([45, 33], 38) := by
  decide +kernel

/-! ## Checks -/

#check @emb
#check @embTs
#check @embS
#check @embD
#check @embSt
#check @sig
#check @embTs_eq
#check @emb_sorted
#check @embTs_sorted
#check @embD_sorted
#check @embSt_sorted
#check @emb_sorted_sem
#check @emb_injective
#check @embTs_injective
#check @embSt_injective
#check @succs_name
#check @K₀_sig

open Lean in
#eval show CoreM Unit from do
  for n in [``emb_names, ``emb_sorted, ``embTs_sorted, ``embD_sorted, ``embSt_sorted, ``emb_sorted_sem,
      ``embD_sorted_sem, ``embSt_sorted_sem, ``emb_injective, ``embTs_injective, ``embSt_injective,
      ``succs_name, ``K₀_sig, ``emb_sortNames, ``succs_sig_kemb] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
