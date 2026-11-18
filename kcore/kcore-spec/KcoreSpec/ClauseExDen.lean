/-
  KCore. A clause with existential variables that decides, read in a model of `Γ`.

  The clause's equation is `premise → f(X̄) = (∃ē. (rhs ∧ ens ∧ post)) ∧ ⊤` (`clauseRhs`): the
  function's elements at the arguments are those of the instances of the right side over elements
  of the sorts of ē at which `ens` and `post` hold. `eqn_atRightEx` reads an equation of a function
  with any right side at the valuation of a match of values. `clauseRightEx_read` reads the right
  side: an instance at values that gives `v` puts `v`'s element in it, and an element in it is in an
  instance at elements; where each such instance is one at values (`Witnessed`, what `exs_values`
  concludes) and every instance at values is decided and gives `r` or nothing, the right side is
  what `r` denotes. `clause_den_exCore` puts the two together with the readings as hypotheses.
  `eval_den_exRead` discharges the right side's at an instance, from the readings of the terms
  each instance evaluates (`InstIsRead`) and of the left side at that instance; `eval_den_ex` is it
  with the readings the soundness of `EvalTerm` in the model gives: `f(vs) = den v` for
  `Eval.clauseEx`'s premises and `f(vs) = ⊥` for `Eval.exNone`'s.
-/
import KcoreSpec.ExsValues
import KcoreSpec.SoundPP
import KcoreSpec.ModelChoicePP
import KcoreSpec.OpenClauseDen

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-- The conclusion of an equation of `fn` with the right side `right`: `f(X̄) = right`. -/
def eqConclEx (c : Semantics) (fn : Fn) (right : Kore.Pattern) : Kore.Pattern :=
  .equals (KoreAML.srt (c.sortName fn.result)) KoreAML.R
    (KoreAML.ap (c.symName fn.label) (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))
    right

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **An equation of a function with any right side, read in a model**: at the arguments `ws` and a
well-sorted σ' under which the premise holds, there are a table holding the axiom's variables and a
valuation that agrees with σ' at which the elements of `f(ws)` are the elements of the result sort
in `right`. `eqn_atCl` for a right side that is not `rhs ∧ ens`. -/
theorem eqn_atRightEx [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vars : List Srt} {prem right : Kore.Pattern}
    (hmem : KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := .implies KoreAML.R prem (eqConclEx c fn right), attributes := [] }⟩ ∈ fnItems c)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted vars σ')
    (hXin : ∀ (j : Nat) s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.varsOf prem)
    (hVin : ∀ i < vars.length,
      canonKey c vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn right)))
    (hfree : ∀ k ∈ KoreAML.freeOf [] prem,
      (∃ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i < vars.length, k = canonKey c vars i)
    (hfreeR : ∀ k ∈ KoreAML.freeOf [] right, ∃ i, i < vars.length ∧ k = canonKey c vars i)
    (hprem : ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M), (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      Agrees c I tbl (canonVars c vars) σ' e →
      (∀ (j : Nat) w s, ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
        e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w) →
      (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr → Inh I σr m0 →
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret I e m0)
    (e0 : Valuation M) :
    ∃ (tbl : VarTable) (e' : Valuation M),
      (∀ k ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn right)), k ∈ tbl) ∧
      VarKey.sortVar "R" ∈ tbl ∧ Agrees c I tbl (canonVars c vars) σ' e' ∧
      ∀ m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔
        InS I (c.sortName fn.result) m ∧ (KoreAML.tr ⟨tbl, []⟩ right).interpret I e' m := by
  obtain ⟨hfnm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := hnn.2.2 fn hfnm
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnum fn.result (List.mem_cons_self ..))
  have hlen : ws.length = fn.args.length := sortsOf_length hws
  let vs := canonVars c vars
  let ax : Kore.Axiom :=
    { sortVars := [KoreAML.Rv], pattern := .implies KoreAML.R prem (eqConclEx c fn right), attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  let e' : Valuation M := valOf tbl (clauseVal c I σr fn.args.length vars.length ws σ')
  have hvarsP : ∀ k, k ∈ KoreAML.varsOf prem → k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn right))
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hRmem : VarKey.sortVar "R" ∈ tbl :=
    List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hXmem : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => hvarsP _ (hXin j s hj)
  have hVmem : ∀ i, i < vars.length → canonKey c vars i ∈ tbl := fun i hi =>
    List.mem_eraseDups.mpr (List.mem_append_right _ (hVin i hi))
  have hRv : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e' a ↔ a = σr := fun a => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]; rfl
  have hXv : ∀ j s w, (fn.args.map c.sortName)[j]? = some s → ws[j]? = some w →
      e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w := fun j s w hj hw => by
    have hjn : j < fn.args.length := by simpa using (List.getElem?_eq_some_iff.mp hj).1
    rw [valOf_ev (hXmem j s hj)]
    simp only [clauseVal]
    rw [xIdx_eq hjn]
    dsimp only
    rw [List.getD_eq_getElem?_getD, hw]; rfl
  have hVv : ∀ i, i < vars.length → e'.evalEvar (tbl.ev (canonKey c vars i)) =
      (match σ'.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [clauseVal]
    rw [xIdx_var, varIdx_eq hi]
    all_goals rfl
  have hvsort : ∀ i, i < vars.length → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (vars.getD i 0) :=
    fun i hi => hσ' i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ' e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  have hargsort : ∀ j s w, (fn.args.map c.sortName)[j]? = some s → ws[j]? = some w →
      ∃ a, s = c.sortName a ∧ c.sortOf w = some a := fun j s w hj hw => by
    rw [List.getElem?_map] at hj
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hj
    obtain ⟨w', hw', hsw'⟩ := sortsOf_get hws ha
    rw [hw] at hw'; cases hw'
    exact ⟨a, rfl, hsw'⟩
  have hfree : ∀ k, k ∈ KoreAML.freeOf [] ax.pattern →
      (∃ j s, (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i, i < vars.length ∧ k = canonKey c vars i := fun k hk => by
    change k ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (eqConclEx c fn right)) at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · rcases hfree k hk with h | ⟨i, hi, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, h⟩
    · unfold eqConclEx at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · unfold KoreAML.ap at hk; rw [KoreAML.freeOf] at hk
        obtain ⟨n, s, hn, rfl⟩ := freeOf_callX _ 0 hk
        exact Or.inl ⟨n, s, hn, by rw [Nat.zero_add]⟩
      · exact Or.inr (hfreeR k hk)
  have hg : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    rcases List.mem_append.mp (List.mem_eraseDups.mp hk) with hk | hk
    · obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hk
      rw [mem_one h1]
      show (KoreAML.guardOf tbl (.sortVar "R")).interpret I e' m'
      rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσr2
    · rcases hfree k hk with ⟨j, s, hj, rfl⟩ | ⟨i, hi, rfl⟩
      · rw [KoreAML.interp_guard_evar hD, trSort_srt]
        obtain ⟨w, hw, -⟩ : ∃ w, ws[j]? = some w ∧ True := by
          have hjn : j < ws.length := by rw [hlen]; simpa using (List.getElem?_eq_some_iff.mp hj).1
          exact ⟨_, List.getElem?_eq_getElem hjn, trivial⟩
        obtain ⟨a, rfl, hsw⟩ := hargsort j s w hj hw
        rw [hXv j _ w hj hw]
        exact (elemOf_spec hI hsw e').2
      · obtain ⟨w, hw, hsw⟩ := hvsort i hi
        have hk := canonKey_eq c hi
        rw [hk, KoreAML.interp_guard_evar hD, trSort_srt, ← hk, hVv i hi, hw]
        exact (elemOf_spec hI hsw e').2
  have hall' : ∀ a, Inh I σr a →
      ((KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
        (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' a ↔
        (KoreAML.tr ⟨tbl, []⟩ (right)).interpret I e' a) := fun m0 hm0 => by
    have hax := sat_fns hI (Or.inl ⟨_, hmem, rfl⟩)
    have hP := (KoreAML.trAxiom_at hD hax e' hg m0).mpr (by
      show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' m0
      rw [KoreAML.interp_inhOf_of hRv]; exact hm0)
    have hP' : (KoreAML.tr ⟨tbl, []⟩ (.implies KoreAML.R prem (eqConclEx c fn right))).interpret I e' m0 := hP
    rw [KoreAML.tr, KoreAML.interp_sImp] at hP'
    obtain ⟨-, himp⟩ := hP'
    have hprem := himp (hprem tbl e' σr m0 hvarsP hag (fun j w s hw hs => hXv j s w hs hw) hRv hσr2 hm0)
    unfold eqConclEx at hprem
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσr1) hRv hσr2 hσr2] at hprem
    obtain ⟨-, hall⟩ := hprem
    exact hall m0 hm0
  have hcall : ∀ m, (KoreAML.den (symApp c fn.label (GroundTerm.koreList c ws))).interpret I e0 m ↔
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
        (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' m := by
    intro m
    unfold KoreAML.den
    rw [tr_symApp]
    unfold symHead
    rw [hnn.2.1 fn hfnm]
    dsimp only
    unfold KoreAML.ap
    rw [KoreAML.tr_app0]
    refine call_congr (e0 := e0) (e' := e') (fn.args.map c.sortName) ws 0 _ _ (by rw [List.length_map]; exact hlen)
      (fun k s w hk hw m => ?_) (fun m => sym_congr (e := e0) (e' := e') _ m) m
    rw [Nat.zero_add, hXv k s w hk hw]
    obtain ⟨a, -, hsw⟩ := hargsort k s w hk hw
    exact (elemOf_spec hI hsw e0).1 m
  have harity : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' a → Inh I σr a := by
    intro a ha
    have hit := sat_sigItem hI (sig_arity (fn_sig_mem hfnm))
    unfold symArityItem at hit
    rw [show iteSort? (c.symName fn.sig.name) = none from hnn.2.1 fn hfnm] at hit
    dsimp only at hit
    unfold KoreAML.arityItem at hit
    dsimp only [KoreAML.paramTable, List.map_nil, KoreAML.appList, Fn.sig] at hit
    have hinc := (KoreAML.interp_included hD).mp (hit e' default) a
    unfold srtOf at hinc
    rw [trSort_srt, KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσr1] at hinc
    apply hinc
    unfold KoreAML.ap at ha
    rw [KoreAML.tr_app0] at ha
    have := call_arity (fn.args.map c.sortName) 0 _ (KoreAML.sym (.symbol (c.symName fn.label))) a ha
      (fun k s hk => ?_) (fun _ h => h)
    · rw [List.map_map] at this
      rw [List.map_map]
      exact this
    · rw [Nat.zero_add]
      obtain ⟨w, hw, -⟩ : ∃ w, ws[k]? = some w ∧ True := by
        have hjn : k < ws.length := by rw [hlen]; simpa using (List.getElem?_eq_some_iff.mp hk).1
        exact ⟨_, List.getElem?_eq_getElem hjn, trivial⟩
      obtain ⟨b, rfl, hsw⟩ := hargsort k s w hk hw
      rw [hXv k _ w hk hw]
      exact (elemOf_spec hI hsw e').2
  have hInS : ∀ m, Inh I σr m ↔ InS I (c.sortName fn.result) m := fun m =>
    (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e') hσr1).symm.trans (inS_iff e')
  refine ⟨tbl, e', fun k hk => List.mem_eraseDups.mpr (List.mem_append_right _ hk), hRmem, hag,
    fun m => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · have h1 := (hcall m).mp hm
    exact ⟨(hInS m).mp (harity m h1), (hall' m (harity m h1)).mp h1⟩
  · exact (hcall m).mpr ((hall' m ((hInS m).mpr hm.1)).mpr hm.2)

end

/-! ## The right side of a clause with existential variables -/

open Model in
section
variable {c : Semantics}

/-- The binders of a clause's existential variables. -/
def clauseExBinders (c : Semantics) (cl : Clause) : List Kore.EVar :=
  cl.exs.map fun i => ((canonVars c cl.vars).getD i default).kore

/-- The body of the right side of a clause with existential variables: `rhs ∧ ens ∧ post`, without
the last where `post` is `\top`. -/
def clauseRhsBody (c : Semantics) (fn : Fn) (cl : Clause) : Kore.Pattern :=
  .and (srtOf c fn.result) ([Term.kore c (canonVars c cl.vars) cl.rhs,
    reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))] ++
    Cond.conj c (canonVars c cl.vars) (srtOf c fn.result) cl.post)

/-- The right side of the equation of a clause with existential variables, as `equationAx` writes
it from `clauseRhs`: `(∃ē. (rhs ∧ ens ∧ post)) ∧ ⊤`. -/
def clauseRightEx (c : Semantics) (fn : Fn) (cl : Clause) : Kore.Pattern :=
  .and (KoreAML.srt (c.sortName fn.result))
    [KoreAML.existsAll (srtOf c fn.result) (clauseExBinders c cl) (clauseRhsBody c fn cl),
      reqPat (srtOf c fn.result) none]

/-- The pair `clauseRhs` gives for a clause with existential variables in scope. -/
theorem clauseRhs_eqEx {fn : Fn} {cl : Clause} (hne : cl.exs ≠ []) (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) :
    clauseRhs c fn cl = (KoreAML.existsAll (srtOf c fn.result) (clauseExBinders c cl) (clauseRhsBody c fn cl),
      reqPat (srtOf c fn.result) none) := by
  unfold clauseRhs clauseExBinders clauseRhsBody KoreAML.existsAll
  dsimp only
  simp only [List.isEmpty_iff, hne, ↓reduceIte]
  rw [filterMap_getElem?_of_lt _ _ (by rw [canonVars_length]; exact hlt)]
  simp only [List.foldr_map]

theorem clauseExBinders_keys {cl : Clause} :
    (clauseExBinders c cl).map KoreAML.evarKey = cl.exs.map (canonKey c cl.vars) := by
  unfold clauseExBinders canonKey
  rw [List.map_map]
  rfl

/-- A free variable of the right side of a clause with existential variables is a variable of the
clause. -/
theorem freeOf_clauseRightEx {fn : Fn} {cl : Clause} (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hokQ : c.condOK cl.vars cl.post = true) {k : VarKey}
    (hk : k ∈ KoreAML.freeOf [] (clauseRightEx c fn cl)) : ∃ i, i < cl.vars.length ∧ k = canonKey c cl.vars i := by
  unfold clauseRightEx at hk
  obtain ⟨φ, hφ, hk⟩ := mem_freeOf_and hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl
  · rw [freeOf_existsAll_eqEx, List.append_nil] at hk
    unfold clauseRhsBody at hk
    obtain ⟨φ, hφ, hk⟩ := mem_freeOf_and hk
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hφ
    rcases hφ with rfl | rfl | hφ
    · obtain ⟨-, i, hi, rfl⟩ := freeOf_kore_bound c _ cl.rhs hk
      exact ⟨i, hrhsv i hi, rfl⟩
    · cases hq : cl.ens with
      | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨-, i, hi, rfl⟩ := freeOf_kore_bound c _ t hk
          exact ⟨i, hensv t hq i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
    · rw [mem_condConj hφ] at hk
      obtain ⟨-, i, hi, rfl⟩ := freeOf_condKore _ cl.post hokQ hk
      exact ⟨i, varOccsCond_lt_twoT cl.post hokQ i hi, rfl⟩
  · simp only [reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk

/-- A variable of the body of the right side is a variable of the equation's axiom. -/
theorem varsOf_body_inAxEx {fn : Fn} {cl : Clause} {prem : Kore.Pattern} {k : VarKey}
    (h : k ∈ KoreAML.varsOf (KoreAML.existsAll (srtOf c fn.result) (clauseExBinders c cl) (clauseRhsBody c fn cl))) :
    k ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) := by
  rw [KoreAML.varsOf]
  refine List.mem_append_right _ ?_
  unfold eqConclEx
  rw [KoreAML.varsOf]
  refine List.mem_append_right _ ?_
  unfold clauseRightEx
  exact varsOf_and_mem (List.mem_cons_self ..) h

/-- **Each variable of a clause with existential variables occurs in its equation's axiom**, where
each is existential or occurs in the clause: a variable of its patterns, `requires` or predicate in
the premise (here any pattern whose variables include those of the premise with the predicate), an
existential one as a binder of the right side, one of the right-hand side, `ensures` or the right
side's predicate under the binders. -/
theorem clause_keys_inAxEx {fn : Fn} {cl : Clause} {prem : Kore.Pattern}
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hP : ∀ k, k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.varsOf prem) :
    ∀ i < cl.vars.length,
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) := by
  intro i hi
  have hinP : canonKey c cl.vars i ∈ KoreAML.varsOf prem →
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) := fun h => by
    rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have hinR : canonKey c cl.vars i ∈ KoreAML.varsOf (KoreAML.existsAll (srtOf c fn.result) (clauseExBinders c cl)
        (clauseRhsBody c fn cl)) →
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) :=
    varsOf_body_inAxEx
  have hinB : canonKey c cl.vars i ∈ KoreAML.varsOf (clauseRhsBody c fn cl) →
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) :=
    fun h => hinR (varsOf_existsAll_bodyEx h _)
  rcases hocc i hi with hX | h
  · refine hinR (varsOf_existsAll_binder _ ?_)
    exact List.mem_map_of_mem hX
  simp only [List.mem_append] at h
  rcases h with (((hP' | hC) | hR) | hE) | hQ
  · exact hinP (hP _ (HoldsShape.varsOf_withPre_prem ((premise_varsCl (c := c) hpats hreqv).2.1 i hP')))
  · rcases List.mem_append.mp (show i ∈ (cl.req.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.pre from hC)
      with hC | hC
    · cases ht : cl.req with
      | none => rw [ht] at hC; cases hC
      | some t =>
        rw [ht] at hC
        refine hinP (hP _ (HoldsShape.varsOf_withPre_prem ?_))
        unfold clausePrem premise
        rw [ht]
        refine varsOf_and_mem (List.mem_cons_self ..) ?_
        simp only [Option.map_some, reqPat, KoreAML.varsOf]
        exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hC))
    · have hpt : cl.pre.isTop = false := by
        cases hpt : cl.pre.isTop with
        | false => rfl
        | true => rw [Cond.eq_top_of_isTop hpt] at hC; simp [varOccsCond] at hC
      exact hinP (hP _ (HoldsShape.varsOf_withPre_pre hpt
        (condKore_keys KoreAML.R cl.pre (bound := []) hi hC rfl).2))
  · exact hinB (by unfold clauseRhsBody; exact varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c _ cl.rhs hR))
  · cases ht : cl.ens with
    | none => rw [ht] at hE; cases hE
    | some t =>
      rw [ht] at hE
      refine hinB ?_
      unfold clauseRhsBody
      refine varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      rw [ht]
      simp only [Option.map_some, reqPat, KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hE))
  · have hT : cl.post.isTop = false := by
      cases hq : cl.post
      case top => rw [hq] at hQ; simp [varOccsCond] at hQ
      all_goals rfl
    refine hinB ?_
    unfold clauseRhsBody
    exact varsOf_and_mem (by simp [Cond.conj, hT]) (condKore_keys (bound := []) (srtOf c fn.result) cl.post hi hQ rfl).2

end

/-! ## The right side and the equation, read in a model -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The right side `(∃ē. (rhs ∧ ens ∧ post)) ∧ ⊤`, read in a model** at an element `m` of the
result sort: it holds `m` exactly where `r` denotes `m`, where the body at the valuation itself
holds what `r` denotes (`hgive`) and the body at a valuation that differs at the binders only, each
at an element of its sort, holds `m` only if `r` denotes it (`hsound`). -/
theorem clauseRightEx_read (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) {fn : Fn} (hfnm : fn ∈ c.allFns)
    {cl : Clause} (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) (hnd : cl.exs.Nodup) {tbl : VarTable}
    (hkeys : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) {e : Valuation M} {r : Option GroundTerm}
    (hinE : ∀ i ∈ cl.exs, InS I (c.sortName (cl.vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c cl.vars i))))
    (hgive : ∀ m, Res c I e r m → (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e m)
    {m : M} (hm : InS I (c.sortName fn.result) m)
    (hsound : ∀ (e'' : Valuation M),
      (∀ x, (∀ i ∈ cl.exs, x ≠ tbl.ev (canonKey c cl.vars i)) → e''.evalEvar x = e.evalEvar x) →
      (∀ i ∈ cl.exs, InS I (c.sortName (cl.vars.getD i 0)) (e''.evalEvar (tbl.ev (canonKey c cl.vars i)))) →
      (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e'' m → Res c I e r m) :
    (KoreAML.tr ⟨tbl, []⟩ (clauseRightEx c fn cl)).interpret I e m ↔ Res c I e r m := by
  have hD := defOK hI
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..))
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c fn.result)).interpret I e b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  have htop : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c fn.result) none)).interpret I e m := by
    simp only [reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e) hσr1).mp ((inS_iff e).mpr hm)
  have hndB := binders_nodupEx hkeys hlt hnd
  have hsB := binders_sortEx (c := c) (vars := cl.vars) hlt
  have hsort : ∀ i ∈ cl.exs,
      ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (cl.vars.getD i 0)) :=
    fun i hi => by rw [canonVars_getD c (hlt i hi)]; rfl
  unfold clauseRightEx
  rw [tr_and2, KoreAML.interp_sAnd]
  constructor
  · rintro ⟨hx, -⟩
    obtain ⟨e'', hoff, hguard, hbody⟩ := existsAll_elim hD (clauseExBinders c cl) e m hndB hsB hx
    refine hsound e'' (fun x hx' => hoff x fun b hb => ?_) (fun i hi => ?_) hbody
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      exact hx' i hi
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c cl.vars).getD i default).kore) hi) _ (hsort i hi)
  · intro hr
    refine ⟨existsAll_intro_at hD (clauseExBinders c cl) e e m hndB hsB (fun _ _ => rfl) rfl (fun b hb n hn => ?_)
      (hgive m hr), htop⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    rw [hsort i hi] at hn
    rw [← srt_inj hn]
    exact hinE i hi

/-- **An equation of a clause with existential variables, read in a model**, under any premise that
holds at the valuations of the match σ' (`hprem`): `f` applied to the arguments' elements is what
`r` denotes, where the body of the right side at a valuation that agrees with σ' holds what `r`
denotes (`hgive`), and at one that differs from it at the binders only holds an element of the
result sort only if `r` denotes it (`hsound`). -/
theorem clause_den_exAt (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause} {prem : Kore.Pattern}
    (hmem : KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := .implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl)),
        attributes := [] }⟩ ∈ fnItems c)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ')
    (hXin : ∀ (j : Nat) s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.varsOf prem)
    (hP : ∀ k, k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.varsOf prem)
    (hfree : ∀ k ∈ KoreAML.freeOf [] prem,
      (∃ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i < cl.vars.length, k = canonKey c cl.vars i)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hokQ : c.condOK cl.vars cl.post = true)
    (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) (hnd : cl.exs.Nodup)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (hprem : ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M), (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ (j : Nat) w s, ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
        e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w) →
      (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr → Inh I σr m0 →
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret I e m0)
    (hgive : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
      (∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl) →
      ∀ m, Res c I e r m → (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e m)
    (hsound : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
      (∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl) →
      ∀ (e'' : Valuation M) (m : M),
      (∀ x, (∀ i ∈ cl.exs, x ≠ tbl.ev (canonKey c cl.vars i)) → e''.evalEvar x = e.evalEvar x) →
      (∀ i ∈ cl.exs, InS I (c.sortName (cl.vars.getD i 0)) (e''.evalEvar (tbl.ev (canonKey c cl.vars i)))) →
      InS I (c.sortName fn.result) m →
      (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e'' m → Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  have hfnm := (lookupFn_spec hfn).1
  have hVin := clause_keys_inAxEx (prem := prem) hpats hreqv hocc hP
  obtain ⟨tbl, e', hk, -, hag, hiff⟩ := eqn_atRightEx hI hnn hfn hmem hws hσ' hXin hVin hfree
    (fun k hk => freeOf_clauseRightEx hrhsv hensv hokQ hk) hprem e0
  have hkeys : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl := fun i hi => hk _ (hVin i hi)
  have hkB : ∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl := fun k hk' =>
    hk _ (varsOf_body_inAxEx (Model.varsOf_existsAll_bodyEx hk' _))
  have hinE : ∀ i ∈ cl.exs, InS I (c.sortName (cl.vars.getD i 0)) (e'.evalEvar (tbl.ev (canonKey c cl.vars i))) := by
    intro i hi
    obtain ⟨w, hw, hsw⟩ := hσ' i (cl.vars.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlt i hi)]; rfl)
    have he : elemOf c I w = e'.evalEvar (tbl.ev (canonKey c cl.vars i)) :=
      (hag i w (by rw [canonVars_length]; exact hlt i hi) hw _).mpr (((elemOf_spec hI hsw e').1 _).mpr rfl)
    rw [← he]
    exact (inS_iff e').mp (elemOf_spec hI hsw e').2
  have hread : ∀ {m : M}, InS I (c.sortName fn.result) m →
      ((KoreAML.tr ⟨tbl, []⟩ (clauseRightEx c fn cl)).interpret I e' m ↔ Res c I e' r m) := fun {m} hm =>
    clauseRightEx_read hI hnn hfnm hlt hnd hkeys hinE (hgive tbl e' hag hkeys hkB) hm
      (fun e'' hoff hin hb => hsound tbl e' hag hkeys hkB e'' m hoff hin hm hb)
  rw [hiff m]
  constructor
  · rintro ⟨hin, hright⟩
    exact (Res_closed r e' e0 m).mp ((hread hin).mp hright)
  · intro hm
    have hm' := (Res_closed r e0 e' m).mp hm
    have hin : InS I (c.sortName fn.result) m := by
      cases r with
      | none => exact hm.elim
      | some v =>
        have hs := elemOf_spec hI (hr v rfl) e'
        rw [(hs.1 m).mp hm']
        exact (inS_iff e').mp hs.2
    exact ⟨hin, (hread hin).mpr hm'⟩

/-- **A clause with existential variables that decides, read in a model**: `clause_den4Cl` for such
a clause, the reading of its right side `rhs ∧ ens` replaced by the two readings of the body
`rhs ∧ ens ∧ post` under the binders (`hgive`, `hsound`). σ' is a match that is well sorted on all
the clause's variables (an instance). -/
theorem clause_den_exCore (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) [OvlOK c]
    (hph : patHooksApart c = true) {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ' : Subst}
    {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses)
    (hws : c.sortsOf ws = some fn.args) (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true) (hokQ : c.condOK cl.vars cl.post = true)
    (hne : cl.exs ≠ []) (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) (hnd : cl.exs.Nodup)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ t, cl.req = some t → ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
        (den c (bool true)).interpret I e' m')
    (ihpre : cl.pre.isTop = false → ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M),
      Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr →
      Inh I σr m0 → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m0)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hgive : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
      (∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl) →
      ∀ m, Res c I e r m → (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e m)
    (hsound : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
      (∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl) →
      ∀ (e'' : Valuation M) (m : M),
      (∀ x, (∀ i ∈ cl.exs, x ≠ tbl.ev (canonKey c cl.vars i)) → e''.evalEvar x = e.evalEvar x) →
      (∀ i ∈ cl.exs, InS I (c.sortName (cl.vars.getD i 0)) (e''.evalEvar (tbl.ev (canonKey c cl.vars i)))) →
      InS I (c.sortName fn.result) m →
      (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e'' m → Res c I e r m)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have hfnm := (lookupFn_spec hfn).1
  have hv := premise_varsCl (c := c) hpats hreqv
  have htr := hsc.trans
  have ihreq' := fun tbl e' hag t ht m' => ihreq t ht tbl e' hag m'
  by_cases hlow' : lowerClauses fn cl = []
  · have hmem := clauseEquation_mem (c := c) hcl hlow'
    unfold clauseEquation at hmem
    rw [clauseRhs_eqEx hne hlt] at hmem
    exact clause_den_exAt hI hnn hfn (prem := withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))
      (eqn_item_mem hfnm hmem) hws hσ' (fun j s hj => HoldsShape.varsOf_withPre_prem (hv.1 j s hj)) (fun _ h => h)
      (fun k hk => freeOf_withPreCl hpreOK hpats hreqv hk) hpats hreqv hrhsv hensv hokQ hlt hnd hocc hr
      (fun tbl e σr m0 hk hag hX hRv hσr2 hm0 =>
        withPre_holdsCl (premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpats hag hX hRv hσr2 hm0 (ihreq' tbl e hag))
          hk (fun hpt hkp hRk => ihpre hpt tbl e σr m0 hag hkp hRk hRv hσr2 hm0))
      hgive hsound e m
  · have hmem := competingEquation_mem (c := c) hcl hlow'
    unfold competingEquation at hmem
    rw [clauseRhs_eqEx hne hlt] at hmem
    have hD := defOK hI
    have hothers : ∀ cl' ∈ lowerClauses fn cl, c.condOK cl'.vars cl'.pre = true ∧
        sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
        (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
        ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws := fun cl' hcl' => by
      obtain ⟨hcl'', hna'', hlt'⟩ := mem_lowerClauses.mp hcl'
      exact hlow cl' hcl'' hna'' hlt'
    let comps := (lowerClauses fn cl).map fun cl' => exclusion c fn cl' (canonClausePres cl')
    let P := withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)
    let CP : Kore.Pattern := .and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P]
    have hP : ∀ k, k ∈ KoreAML.varsOf P → k ∈ KoreAML.varsOf CP := fun k hk => by
      show k ∈ KoreAML.varsOf (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])
      rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk))
    have hN : ∀ k, k ∈ KoreAML.varsOf (anyOfC KoreAML.R comps) → k ∈ KoreAML.varsOf CP := fun k hk => by
      show k ∈ KoreAML.varsOf (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])
      rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf, anyOf_eq]
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hk))
    refine clause_den_exAt hI hnn hfn (prem := CP) (eqn_item_mem hfnm hmem) hws hσ'
      (fun j s hj => hP _ (HoldsShape.varsOf_withPre_prem (hv.1 j s hj))) hP (fun k hk => ?_)
      hpats hreqv hrhsv hensv hokQ hlt hnd hocc hr (fun tbl e σr m0 hkeys hag hX hRv hσr2 hm0 => ?_) hgive hsound e m
    · change k ∈ KoreAML.freeOf [] (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P]) at hk
      rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOf] at hk
      simp only [List.append_nil, List.mem_append] at hk
      rcases hk with hk | hk
      · rw [anyOf_eq] at hk
        obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
        obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
        obtain ⟨hpre', hp', hq', -⟩ := hothers cl' hcl'
        exact Or.inl (freeOf_exclusionCl hpre' hp' hq' hk)
      · exact freeOf_withPreCl hpreOK hpats hreqv hk
    · have hR' : e.evalEvar (tbl.ev (.sortVar "R")) = σr := (hRv _).mp (by rw [trSort_R, KoreAML.interp_evar])
      have hRkey : VarKey.sortVar "R" ∈ tbl := hkeys _ (by
        show _ ∈ KoreAML.varsOf (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])
        rw [KoreAML.varsOf]
        exact List.mem_append_left _ (List.mem_singleton_self _))
      show (KoreAML.tr ⟨tbl, []⟩ (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])).interpret I e m0
      rw [tr_and2, KoreAML.interp_sAnd]
      refine ⟨?_, withPre_holdsCl
        (premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpats hag hX hRv hσr2 hm0 (ihreq' tbl e hag))
        (fun k hk => hkeys k (hP k hk)) (fun hpt hkp hRk => ihpre hpt tbl e σr m0 hag hkp hRk hRv hσr2 hm0)⟩
      rw [KoreAML.tr, KoreAML.interp_sNot]
      refine ⟨?_, (KoreAML.interp_inhOf_of hRv).mpr hm0⟩
      rw [anyOf_eq]
      refine anyOfC_empty hD isFree_R comps (fun φ hφ => ?_)
      obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨-, -, -, hpl', hf', hmf'⟩ := hothers cl' hcl'
      exact hpl' hws hf' hmf'
        (fun i hi hil => hkeys _ (hN _ (mem_varsOf_anyOfC hφ (varsOf_exclusionCl hi hil))))
        (fun hpt k hk => hkeys _ (hN _ (mem_varsOf_anyOfC hφ (varsOf_exclusion_preCl hpt hk))))
        (fun j s hj => hkeys _ (hP _ (HoldsShape.varsOf_withPre_prem (hv.1 j _ (by rw [List.getElem?_map, hj]; rfl)))))
        hRkey (fun j w s hw hs => hX j w _ hw (by rw [List.getElem?_map, hs]; rfl)) hR' hσr2 m0

/-- **An element valuation that gives each existential variable a value's element is one at
values**: where `e''` differs from a valuation `e` that agrees with a well-sorted σ₀ at the
existential variables only, and gives each of them the element of a value of its sort, there is a
well-sorted σ' that is σ₀ off the existential variables with which `e''` agrees. -/
theorem subst_of_witnessedEx (hI : I ⊧ᴵP Γ c) [OvlOK c] (hg : genWf c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {cl : Clause} (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) {σ₀ : Subst} (hσ₀ : c.WellSorted cl.vars σ₀)
    {tbl : VarTable} (hkeys : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) {e e'' : Valuation M}
    (hag : Agrees c I tbl (canonVars c cl.vars) σ₀ e)
    (hoff : ∀ x, (∀ i ∈ cl.exs, x ≠ tbl.ev (canonKey c cl.vars i)) → e''.evalEvar x = e.evalEvar x)
    (hwit : ∀ i ∈ cl.exs, Witnessed c I tbl (canonVars c cl.vars) cl.vars e'' i) :
    ∃ σ', AgreeOff cl.exs σ₀ σ' ∧ c.WellSorted cl.vars σ' ∧ Agrees c I tbl (canonVars c cl.vars) σ' e'' := by
  have hsj : ∀ j, j < cl.vars.length → cl.vars[j]? = some (cl.vars.getD j 0) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hun : ∀ i, i < cl.vars.length → i ∉ cl.exs → ∃ v, σ₀.lookup i = some v ∧
      c.sortOf v = some (cl.vars.getD i 0) ∧
      elemOf c I v = e''.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i)) := fun i hi hx => by
    obtain ⟨v, hv, hsv⟩ := hσ₀ i _ (hsj i hi)
    refine ⟨v, hv, hsv, ?_⟩
    rw [show keyAt (canonVars c cl.vars) i = canonKey c cl.vars i from rfl,
      hoff _ fun j hj he => hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)]
    exact (hag i v (by rw [canonVars_length]; exact hi) hv _).mpr (((elemOf_spec hI hsv e).1 _).mpr rfl)
  have hall : ∀ i < cl.vars.length, Witnessed c I tbl (canonVars c cl.vars) cl.vars e'' i := fun i hi => by
    by_cases hx : i ∈ cl.exs
    · exact hwit i hx
    · obtain ⟨v, -, hsv, he⟩ := hun i hi hx
      exact ⟨v, hsv, he⟩
  obtain ⟨hws, hags⟩ := substOf_ok hI hg htr (canonVars_length c cl.vars) hall
  have hlk : ∀ i, i < cl.vars.length →
      (substOf c I tbl (canonVars c cl.vars) cl.vars e'' ++ σ₀).lookup i =
        (substOf c I tbl (canonVars c cl.vars) cl.vars e'').lookup i := fun i hi => by
    rw [List.lookup_append, substOf_lookup hi]; rfl
  have hlk' : ∀ i, ¬ i < cl.vars.length →
      (substOf c I tbl (canonVars c cl.vars) cl.vars e'' ++ σ₀).lookup i = σ₀.lookup i := fun i hi => by
    rw [List.lookup_append]
    cases h : (substOf c I tbl (canonVars c cl.vars) cl.vars e'').lookup i with
    | none => rfl
    | some v => exact absurd (substOf_lookup_some h).1 hi
  refine ⟨substOf c I tbl (canonVars c cl.vars) cl.vars e'' ++ σ₀, fun i hx => ?_, fun i s hs => ?_,
    fun i v hi hv m => ?_⟩
  · by_cases hi : i < cl.vars.length
    · obtain ⟨v, hv, hsv, he⟩ := hun i hi hx
      rw [hlk i hi, hv, substOf_lookup hi, ← he, pick_eq hI hg htr hsv]
    · exact hlk' i hi
  · have hi := (List.getElem?_eq_some_iff.mp hs).1
    rw [hlk i hi]
    exact hws i s hs
  · rw [canonVars_length] at hi
    rw [hlk i hi] at hv
    exact hags i v (by rw [canonVars_length]; exact hi) hv m

open HoldsShape in
/-- **A clause with existential variables that decides, read in a model of `Γc`**, from the
readings of the evaluations at hand. σ₀ is an instance under which the clause matches `ws` (well
sorted on all the clause's variables); its `requires` and its predicate `pre` are read at σ₀
(`ihreq`, `ihpre`); the clauses of a smaller priority it negates fail; every instance that is σ₀ off
the existential variables is decided and gives `r` or nothing, with the readings of the terms it
evaluates (`InstIsRead`); and where `r` is `some v` the instance at σ₀ gives `v`. Then `f` applied
to the arguments' elements is what `r` denotes. The soundness of `EvalTerm` in the model is not
asked.

The clause's equation is read through `clauseRhs`: its right side is `∃ē. (rhs ∧ ens ∧ post)`. The
instance at σ₀ that gives `v` puts `v`'s element in it. An element in it is in an instance at
elements of the sorts of ē; `post` holding there, each existential variable is at a value's
element (`exs_values_hr`: confined, or fixed by `post`), so the instance is one at values, which
gives `r` or nothing. -/
theorem eval_den_exRead (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ₀ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true) (hne : cl.exs ≠ [])
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hσ₀ : c.WellSorted cl.vars σ₀) (hmatch0 : PatVals c σ₀ cl.pats ws)
    (ihreq : ∀ t, cl.req = some t → ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₀ e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
        (den c (bool true)).interpret I e' m')
    (ihpre : cl.pre.isTop = false → ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M),
      Agrees c I tbl (canonVars c cl.vars) σ₀ e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr →
      Inh I σr m0 → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m0)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hall0 : ∀ σ', AgreeOff cl.exs σ₀ σ' → c.WellSorted cl.vars σ' → InstIsRead c I σ' cl r)
    (hgive0 : ∀ v, r = some v → EvalTerm c σ₀ cl.rhs (some v) ∧ TermAt c I σ₀ cl.rhs (some v) ∧
      (∀ t, cl.ens = some t → TermAt c I σ₀ t (some (bool true))) ∧
      HoldsRead c I cl.vars.length σ₀ cl.post true)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have N : NodeFacts c I := nodeFacts_of_core h hIc
  have hfnm := (lookupFn_spec hfn).1
  have hS : fn.result < nRegSorts + c.sortNames.length := hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..)
  have G : hasBinder cl.post = true → BinderFacts c I := fun _ => binderFacts_of_core h hrc hIc
  -- the clause's facts
  have hs' := hs
  simp only [Semantics.clauseExOK, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨hltB, hndB⟩, hleft⟩, hokQ⟩ := hs'
  have hlt : ∀ i ∈ cl.exs, i < cl.vars.length := fun i hi => of_decide_eq_true (List.all_eq_true.mp hltB i hi)
  have hnd : cl.exs.Nodup := (NamesApart.nodupB_iff _).mp hndB
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (hreqs t ht)
  have hrhsv := varOccs_lt _ hrhss
  have hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (henss t ht)
  have hfreeF : cl.exs.filter (!cl.leftVars.contains ·) = cl.exs :=
    List.filter_eq_self.mpr fun i hi => List.all_eq_true.mp hleft i hi
  have hsj : ∀ j, j < cl.vars.length → cl.vars[j]? = some (cl.vars.getD j 0) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hr : ∀ v, r = some v → c.sortOf v = some fn.result := fun v hv =>
    EvalTerm.sorted hsc (hgive0 v hv).1 fns_headsOK hσ₀ hrhss rfl
  -- a term's reading at a valuation that agrees with a well-sorted σ' and holds every key
  have allOf : ∀ {σ' : Subst} {t : Term} {r' : Option GroundTerm} {s : Srt} {tbl : VarTable} {e : Valuation M},
      TermAt c I σ' t r' → c.WellSorted cl.vars σ' → Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r' m :=
    fun {σ' t r' s tbl e} hTA hw hag hkeys ht m =>
      hTA hw (fun i hi => hi) (reads_of_agrees hw hag (P := fun i => i ∈ varOccs t)
        fun i hi => ⟨varOccs_lt t ht i hi, hkeys i (varOccs_lt t ht i hi)⟩) ht m
  -- the keys of the right side's predicate are keys of the body
  have hkQ : ∀ {tbl : VarTable}, (∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl) →
      ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post), k ∈ tbl := by
    intro tbl hkB k hk
    cases hpt : cl.post.isTop with
    | false =>
      refine hkB k ?_
      unfold clauseRhsBody
      exact Model.varsOf_and_mem (by simp [Cond.conj, hpt]) hk
    | true =>
      rw [Cond.eq_top_of_isTop hpt] at hk
      simp [Cond.kore, KoreAML.varsOf, srtOf, KoreAML.srt, KoreAML.sortVarsOf, KoreAML.sortVarsOfList] at hk
  have hinSort : ∀ {tbl : VarTable} {e : Valuation M} {m : M}, InS I (c.sortName fn.result) m →
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c fn.result))).interpret I e m := fun {tbl e m} hm => by
    unfold srtOf; rw [trSort_srt]; exact (inS_iff e).mpr hm
  -- the body's first two conjuncts are the right side `rhs ∧ ens`
  have hbody : ∀ {tbl : VarTable} {e : Valuation M} {m : M},
      (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e m ↔
        (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ∧
          (cl.post.isTop = false →
            (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post)).interpret I e m) := by
    intro tbl e m
    unfold clauseRhsBody clauseRight
    rw [interp_and (by simp), tr_and2, KoreAML.interp_sAnd]
    constructor
    · intro hq
      refine ⟨⟨hq _ (by simp), hq _ (by simp)⟩, fun hpt => hq _ (by simp [Cond.conj, hpt])⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩ q hq
      rcases List.mem_append.mp hq with hq | hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact h1
        · exact h2
      · have hq' := Model.mem_condConj hq
        subst hq'
        refine h3 ?_
        cases hpt : cl.post.isTop with
        | false => rfl
        | true => simp [Cond.conj, hpt] at hq
  refine clause_den_exCore hI hnn hsc hph hfn hcl hws hσ₀ hmatch0 hpats hpreOK hokQ hne hlt hnd hocc hreqv hrhsv hensv hr
    ihreq ihpre hlow ?_ ?_ e m
  · -- the instance at σ₀ gives what `r` denotes
    intro tbl e hag hkeys hkB m hm
    cases r with
    | none => exact hm.elim
    | some v =>
      obtain ⟨hrhs, hrhsT, hensT, hpost⟩ := hgive0 v rfl
      have hmS : InS I (c.sortName fn.result) m := by
        have hsp := elemOf_spec hI (hr v rfl) e
        rw [(hsp.1 m).mp hm]
        exact (inS_iff e).mp hsp.2
      refine hbody.mpr ⟨(right_iff hI hnn hfnm hr
        (fun m' => allOf hrhsT hσ₀ hag hkeys hrhss m')
        (fun t ht m' => allOf (hensT t ht) hσ₀ hag hkeys (henss t ht) m') m).mpr hm, fun _ => ?_⟩
      have hrd := reads_of_agrees hσ₀ hag (P := fun i => i ∈ varOccsCond cl.vars.length cl.post)
        fun i hi => ⟨varOccsCond_lt_twoT cl.post hokQ i hi, hkeys i (varOccsCond_lt_twoT cl.post hokQ i hi)⟩
      exact (hpost.holdsAt N G rfl hσ₀ hokQ hb (fun i hi _ => hi) hrd (hkQ hkB) hS m (hinSort hmS)).mpr rfl
  · -- an instance at elements that holds `m` is one at values, which gives `r` or nothing
    intro tbl e hag hkeys hkB e'' m hoff hin hmS hb''
    obtain ⟨hR, hQ⟩ := hbody.mp hb''
    have hkey : ∀ i, i < cl.vars.length → i ∉ cl.exs →
        e''.evalEvar (tbl.ev (canonKey c cl.vars i)) = e.evalEvar (tbl.ev (canonKey c cl.vars i)) := fun i hi hx =>
      hoff _ fun j hj he => hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)
    -- `post` holds at the instance
    have hpostE : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post)).interpret I e'' m := by
      cases hpt : cl.post.isTop with
      | false => exact hQ hpt
      | true =>
        have hrd : Reads c I cl.vars (fun i => i ∈ varOccsCond cl.vars.length cl.post) σ₀ tbl e'' := fun i hi => by
          rw [Cond.eq_top_of_isTop hpt] at hi; simp [varOccsCond] at hi
        have hpT : HoldsAt c I cl.vars.length σ₀ cl.post true := by
          rw [Cond.eq_top_of_isTop hpt]; exact holdsAt_top N
        exact (hpT rfl hσ₀ hokQ hb (fun i hi _ => hi) hrd (hkQ hkB) hS m (hinSort hmS)).mpr rfl
    have hwit := CE.exs_values_hr h hrc hIc N hs hb hp (σ := σ₀) (hσ₀.at _) ⟨σ₀, AgreeOff.refl _ _, hσ₀⟩
      (fun σ' ha hw => (hall0 σ' (hfreeF ▸ ha) hw).post)
      (tbl := tbl) (e := e'') (S := fn.result)
      (fun i hi v hv m' => by
        have hiu := List.mem_filter.mp hi
        have hil : i < cl.vars.length := List.mem_range.mp hiu.1
        have hix : i ∉ cl.exs := by simpa using hiu.2
        show m' = e''.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
        rw [hkey i hil hix]
        exact (hag i v (by rw [canonVars_length]; exact hil) hv m').trans ((den_closed c v).interp e e'' m'))
      (fun i hi s hs'' => by
        have hil := hlt i hi
        rw [hsj i hil] at hs''
        cases hs''
        exact (inS_iff e'').mpr (hin i hi))
      (fun j hj => hkeys j hj) (hkQ hkB) hS ⟨m, hinSort hmS, hpostE⟩
    obtain ⟨σ', hao, hw', hag'⟩ := subst_of_witnessedEx hI hg hsc.trans hlt hσ₀ hkeys hag hoff hwit
    cases hall0 σ' hao hw' with
    | fails hp' hf =>
      exfalso
      cases hf with
      | ens ht he hTe hw =>
        exact (right_empty hI hnn hfnm ht hw (fun v hv => EvalTerm.sorted hsc he fns_headsOK hw' (henss _ ht) hv)
          (fun m' => allOf hTe hw' hag' hkeys (henss _ ht) m') m).mp hR
      | post hf' =>
        cases hpt : cl.post.isTop with
        | true =>
          have hf'' := hf'.holds
          rw [Cond.eq_top_of_isTop hpt] at hf''
          exact absurd hf''.top_eq (by simp)
        | false =>
          have hrd := reads_of_agrees hw' hag' (P := fun i => i ∈ varOccsCond cl.vars.length cl.post)
            fun i hi => ⟨varOccsCond_lt_twoT cl.post hokQ i hi, hkeys i (varOccsCond_lt_twoT cl.post hokQ i hi)⟩
          exact absurd ((hf'.holdsAt N G rfl hw' hokQ hb (fun i hi _ => hi) hrd (hkQ hkB) hS m (hinSort hmS)).mp (hQ hpt))
            (by simp)
      | rhs hn hTn =>
        unfold clauseRight at hR
        rw [tr_and2, KoreAML.interp_sAnd] at hR
        exact (allOf hTn hw' hag' hkeys hrhss m).mp hR.1
    | gives hrhs hrhsT _ _ =>
      unfold clauseRight at hR
      rw [tr_and2, KoreAML.interp_sAnd] at hR
      exact (Res_closed _ e'' e m).mp ((allOf hrhsT hw' hag' hkeys hrhss m).mp hR.1)


open HoldsShape in
/-- **A clause with existential variables that decides, read in a model of `Γc`** in which
`EvalTerm` is sound. The clause matches `ws` under σ, the clauses of a smaller priority it negates
fail, it has an instance (a well-sorted σ' that is σ off the existential variables the left side
does not hold), and every instance is decided and gives `r` or nothing (`InstIs`), one of them
giving `v` where `r` is `some v`. Then `f` applied to the arguments' elements is what `r` denotes:
`f(ws) = den v` for the premises of `Eval.clauseEx`, `f(ws) = ⊥` for those of `Eval.exNone`.

The clause's equation is read through `clauseRhs`: its right side is `∃ē. (rhs ∧ ens ∧ post)`. An
instance at values that gives `v` puts `v`'s element in it. An element in it is in an instance at
elements of the sorts of ē; `post` holding there, each existential variable is at a value's
element (`exs_values`: confined, or fixed by `post`), so the instance is one at values, which gives
`r` or nothing. -/
theorem eval_den_ex (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (hT : HoldsShape.TermSound c I)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true) (hne : cl.exs ≠ [])
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hpreR : cl.pre ≠ .top → PreRead c I cl)
    (hmatch : PatVals c σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hsome : ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ')
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl r)
    (hgv : ∀ v, r = some v → ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have F : AtomFacts c I := atomFacts_of_core h hIc hT
  have hfree : cl.exsFree = cl.exs := by
    have hs' := hs
    simp only [Semantics.clauseExOK, Bool.and_eq_true] at hs'
    exact List.filter_eq_self.mpr fun i hi => List.all_eq_true.mp hs'.1.2 i hi
  -- an instance, the one that gives `v` where `r` is `some v`
  obtain ⟨σ₀, hag0, hσ₀, hgive0⟩ : ∃ σ₀, AgreeOff cl.exsFree σ σ₀ ∧ c.WellSorted cl.vars σ₀ ∧
      ∀ v, r = some v → cl.Gives c σ₀ v := by
    cases r with
    | none =>
      obtain ⟨σ₀, h1, h2⟩ := hsome
      exact ⟨σ₀, h1, h2, fun v hv => by cases hv⟩
    | some v =>
      obtain ⟨σ₀, h1, h2, h3⟩ := hgv v rfl
      exact ⟨σ₀, h1, h2, fun v' hv' => by cases hv'; exact h3⟩
  -- the left side reads σ₀ as it reads σ
  have hl : ∀ i ∈ cl.leftVars, σ₀.lookup i = σ.lookup i := fun i hi =>
    hag0 i (by simp [Clause.exsFree, hi])
  have hmatch0 : PatVals c σ₀ cl.pats ws :=
    PatVals.congr_lookup hmatch fun j hj => hl j (List.mem_append_left _ hj)
  have hreq0 : ∀ t, cl.req = some t → EvalTerm c σ₀ t (some (bool true)) := fun t ht =>
    Exec.EvalTerm.congr (hreq t ht) fun i hi => (hl i (Clause.req_leftVars ht i hi)).symm
  have hpre0 : Holds c cl.vars.length σ₀ cl.pre true :=
    Holds.congr_NI hpre fun j hj => (hl j (Clause.pre_leftVarsRH j hj)).symm
  have hall0 : ∀ σ', AgreeOff cl.exs σ₀ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl r := fun σ' ha hw =>
    hall σ' (hag0.trans (hfree ▸ ha)) hw
  have HD : ∀ p : Cond, HoldsDen' c I p := fun p =>
    holds_den_binders' F p fun _ => binderFacts_of_core h hrc hIc
  exact eval_den_exRead h hrc hIc hfn hcl hws hpats hpreOK hs hb hp hne hocc hreqs hrhss henss hσ₀ hmatch0
    (fun t ht tbl e' hag m' => hT (hreq0 t ht) hσ₀ (canonVars_length c cl.vars) hag (hreqs t ht) m')
    (fun hpt tbl e' σr m0 hag hkp hRk hRv hσr hm0 =>
      (preRead_agreesCl (hpreR (ne_top_of_isTop_false hpt)) hpreOK (holdsAt_of_den (HD _) hpre0) hσ₀ hag hkp hRk hRv hσr
        hm0).mpr rfl)
    hlow (fun σ' ha hw => InstIsRead.of_instIs F (hall0 σ' ha hw))
    (fun v hv => by
      obtain ⟨hrhs, hens, hpost⟩ := hgive0 v hv
      exact ⟨hrhs, F.termAt hrhs, fun t ht => F.termAt (hens t ht), HoldsReadT.of_holds F.termAt _ hpost⟩) e m

/-- **`Eval.clauseEx`, read in a model**: under its premises (the instance at σ gives `v`, every
instance is decided and gives `v` or nothing), `f(ws) = den v`. -/
theorem eval_den_clauseEx (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (hT : HoldsShape.TermSound c I)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ : Subst} {v : GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hpreR : cl.pre ≠ .top → HoldsShape.PreRead c I cl)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) (hne : cl.exs ≠ [])
    (hrhs : EvalTerm c σ cl.rhs (some v))
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c cl.vars.length σ cl.post true)
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl (some v))
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ (den c v).interpret I e m :=
  eval_den_ex h hrc hIc hT hfn hcl hws hpats hpreOK hs hb hp hne hocc hreqs hrhss henss hpreR hmatch hreq hpre hlow
    ⟨σ, AgreeOff.refl _ _, hσ⟩ hall
    (fun v' hv' => by cases hv'; exact ⟨σ, AgreeOff.refl _ _, hσ, hrhs, hens, hpost⟩) e m

/-- **`Eval.exNone`, read in a model**: under its premises (an instance exists, every instance is
decided and gives nothing), `f(ws) = ⊥`. -/
theorem eval_den_exNone (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (hT : HoldsShape.TermSound c I)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ : Subst}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hpreR : cl.pre ≠ .top → HoldsShape.PreRead c I cl)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hne : cl.exs ≠ []) (hmatch : PatVals c σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hsome : ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ')
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl none)
    (e : Valuation M) (m : M) :
    ¬ (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m :=
  (eval_den_ex h hrc hIc hT hfn hcl hws hpats hpreOK hs hb hp hne hocc hreqs hrhss henss hpreR hmatch hreq hpre hlow
    hsome hall (fun v' hv' => by cases hv') e m).mp

end

end Faithful

end KCore
