/-
  KCore. An equation of a sort predicate that is an instance of one of its clauses at a
  constructor pattern (`Parse.predInstOK`): `Γ` entails it.

  The clause `isX(kseq(inj{X,KItem}(V), dotk)) = r` of `Semantics.sortPreds` states a premise of
  `Γ` (`sortPred_items`). Its instance at a constructor pattern p of the sort X,
  `isX(kseq(inj{X,KItem}(p), dotk)) = r`, holds in every model of `Γ` at every valuation
  (`predInst_core`): where the instance's premise holds, the argument `X0` is an element of
  `kseq(inj{X,KItem}(p), dotk)`, so of `kseq(inj{X,KItem}(x), dotk)` for an element x of p's
  denotation (an application is read element by element, `predInst_kseqInj_iff`), and x is an element of
  X (`patSortC`: the constructors' arities, the variables' guards); the clause's premise holds at
  the valuation that gives V the element x, and the two equations' conclusions read `X0` and the
  sort `R` alone.

  - `predInst_kseqInj_iff`: the elements of `kseq(inj{X,KItem}(t), dotk)`, element by element of t.
  - `predInst_core`: the instance's item holds in a model of `Γ` where the clause's does.
  - `predInstOfClause_spec`: what `Parse.predInstOfClause` checks, as equations.
  - `predInst_entailed`: where `predInstOK` accepts an equation of the text, its reading is a
    clause whose equation `Γ` entails; with `predProjOK_sortPred` and `sortPredEqn_in_Γ`
    (GenEqsConservative.lean) for the equations that are clauses of the predicate.

  A sort predicate's `[owise]` equation whose exclusion also names such instances
  (`Parse.predOwiseInstOK`) negates more disjuncts than `Γ`'s item of the clause, which negates the
  exclusions of the clauses before it: its premise is narrower, so the item entails it.
  - `owiRen`, `interp_owiRen`, `sat_owiRen`: a pattern with its variables renamed one-to-one,
    binders included, denotes what the pattern denotes at the valuation read through the renaming;
    a valid pattern stays valid.
  - `tr_owiRen`: the translation of a KORE pattern under one table is its translation under
    another, renamed, where the renaming takes each variable's index in the one to its index in the
    other (`owiF`, `owiG`, one-to-one where the one table's keys are the other's).
  - `owi_sat_narrower`: an axiom `prem' → concl` is valid where `prem → concl` is, over one sort
    variable list, `prem'` holding the variables of `prem` and denoting, under every table, a part
    of it; the two tables differ, and the valid one is read under the other's by `owiRen`.
  - `owiseWith c fn ds cl`: the clause's equation with the disjuncts `ds` negated;
    `owiseWith_entailed`: `Γ` entails it where `ds` holds the exclusions of the clauses before `cl`.
  - `predOwiseInst_entailed`: where `predOwiseInstOK` accepts the `[owise]` equation of a sort
    predicate, its reading without the instances' disjuncts is a clause `ow` of the predicate, and
    `Γ` entails `ow`'s equation under the negation of any disjuncts that hold the exclusions of the
    clauses before `ow`, the instances' among them.
-/
import KcoreSpec.GenEqsConservative
import KcoreSpec.FaithfulCollPat
import KcoreSpec.OpenSuccessor
import KcoreSpec.HypWf

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace GenEqs

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- `kseq(inj{X,KItem}(x), dotk)` holds `a`, its closed parts read at any valuation. -/
def predInstKInj (c : Semantics) (I : Interpretation KoreAML.Sym M) (X : Srt) (x a : M) : Prop :=
  ∃ u d h y, (symHead c kseq).interpret I KoreAML.val0 h ∧
    GS I (c.sortName Srt.kitem) (.inj (c.sortName X)) [x] y ∧ I.evalApp h y u ∧
    (symHead c dotk).interpret I KoreAML.val0 d ∧ I.evalApp u d a

theorem predInst_kseqInj_iff {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation M} (X : Srt) (t : Term) (a : M) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.app kseq [.inj X Srt.kitem t, .app dotk []]))).interpret I e a ↔
      ∃ x, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e x ∧ predInstKInj c I X x a := by
  rw [kore_app, tr_symApp]
  simp only [Term.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  rw [kore_app, tr_symApp, Term.koreList, KoreAML.trArgs_nil, Term.kore, KoreAML.tr_injP]
  simp only [interpret_app, interp_injApp]
  constructor
  · rintro ⟨u, d, ⟨h, y, hh, ⟨x, hx, hy⟩, hu⟩, hd, ha⟩
    exact ⟨x, hx, u, d, h, y, ((symHead_closed kseq).interp e _ h).mp hh, hy, hu,
      ((symHead_closed dotk).interp e _ d).mp hd, ha⟩
  · rintro ⟨x, hx, u, d, h, y, hh, hy, hu, hd, ha⟩
    exact ⟨u, d, ⟨h, y, ((symHead_closed kseq).interp e _ h).mpr hh, ⟨x, hx, hy⟩, hu⟩,
      ((symHead_closed dotk).interp e _ d).mpr hd, ha⟩

theorem predInst_core (hc : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {fn : Fn} (hfnm : fn ∈ c.allFns)
    (hargs : fn.args = [Srt.k])
    {cl0 cl : Clause} (hgen : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl0⟩).pat)
    {X : Srt} {p : Term} {s : Srt} {lit : Lit}
    (h0v : cl0.vars = [X]) (h0p : cl0.pats = [.app kseq [.inj X Srt.kitem (.var 0), .app dotk []]])
    (h0s : sortsOfTerms c.patCtxAll cl0.vars cl0.pats = some fn.args)
    (hp : cl.pats = [.app kseq [.inj X Srt.kitem p, .app dotk []]])
    (hq0 : cl0.req = none) (he0 : cl0.ens = none) (hr0 : cl0.rhs = .dv s lit)
    (hcp : collPat c p = true) (hsp : sortOfTerm c.patCtxNF cl.vars p = some X)
    (hbind : ∀ i < cl.vars.length, i ∈ varOccs p)
    (hq : cl.req = none) (he : cl.ens = none) (hrhs : cl.rhs = cl0.rhs) :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl⟩).pat := by
  have hD := defOK hI
  have hcd := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core hc
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hconcl : clauseConcl c fn cl = clauseConcl c fn cl0 := by
    simp only [clauseConcl, clauseRight, hrhs, hr0, he, he0, Term.kore, Option.map_none]
  -- the argument's key and the sort variable's
  let X0k : KoreAML.VarKey := .evar ("X" ++ toString 0) (KoreAML.srt (c.sortName Srt.k))
  have hX0c : ∀ {cl' : Clause}, X0k ∈ KoreAML.freeOf [] (clauseAxiom c fn cl').pattern := by
    intro cl'
    show X0k ∈ KoreAML.freeOf [] (.implies KoreAML.R (clausePrem c fn cl') (clauseConcl c fn cl'))
    rw [KoreAML.freeOf]
    refine List.mem_append_right _ ?_
    unfold clauseConcl
    rw [KoreAML.freeOf]
    refine List.mem_append_left _ ?_
    rw [hargs]
    simp [KoreAML.ap, KoreAML.vars, KoreAML.numbered, KoreAML.freeOf, KoreAML.freeOfList, X0k]
    rfl
  have hKn : Srt.k < nRegSorts + c.sortNames.length := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
  obtain ⟨σK, hσK1, hσK2⟩ := sortSing hI hKn
  -- the general clause: its premise's variables
  have hb0 : ∀ i < cl0.vars.length, i ∈ varOccsList cl0.pats := by
    intro i hi
    rw [h0v] at hi
    rw [h0p, show i = 0 by simpa using hi]
    simp [varOccsList, varOccs]
  have hpv := premise_vars (c := c) h0s hb0 (fun t ht => by rw [hq0] at ht; cases ht)
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  rw [interpret_impl]
  intro hgd
  generalize ht : KoreAML.tableOf (clauseAxiom c fn cl).sortVars (clauseAxiom c fn cl).pattern = t at hgd ⊢
  have hguard : ∀ k ∈ (List.map KoreAML.sortVarKey (clauseAxiom c fn cl).sortVars ++
      KoreAML.freeOf [] (clauseAxiom c fn cl).pattern).eraseDups, (KoreAML.guardOf t k).interpret I e m :=
    fun k hk => conjList_mem hgd _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp
      (hguard _ (List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_singleton_self _))))
  have hX0 : (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt (c.sortName Srt.k)))).interpret I e (e.evalEvar (t.ev X0k)) :=
    (KoreAML.interp_guard_evar hD).mp (hguard _ (List.mem_eraseDups.mpr (List.mem_append_right _ hX0c)))
  have hvar : ∀ i < cl.vars.length, InS I (c.sortName (cl.vars.getD i 0))
      (e.evalEvar (t.ev (keyAt (canonVars c cl.vars) i))) := by
    intro i hi
    have hfree : canonKey c cl.vars i ∈ KoreAML.freeOf [] (clauseAxiom c fn cl).pattern := by
      show _ ∈ KoreAML.freeOf [] (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl))
      rw [KoreAML.freeOf]
      refine List.mem_append_left _ ?_
      exact Model.freeOf_premise_var (by rw [hp, hargs]; rfl) (by rw [hp]; simp [varOccsList, varOccs, hbind i hi])
    have hk := canonKey_eq c hi
    have hg0 := hguard _ (List.mem_eraseDups.mpr (List.mem_append_right _ hfree))
    rw [hk, KoreAML.interp_guard_evar hD, trSort_srt] at hg0
    rw [← inS_iff e]
    show (KoreAML.inhOf (KoreAML.Cons.sortP _)).interpret I e (e.evalEvar (t.ev (canonKey c cl.vars i)))
    rw [hk]; exact hg0
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [KoreAML.interp_equal hD]
  intro b
  show (KoreAML.tr ⟨t, []⟩ (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl))).interpret I e b ↔
    (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e b
  rw [KoreAML.tr, KoreAML.interp_sImp]
  refine ⟨fun h => h.1, fun hb => ⟨hb, fun hprem => ?_⟩⟩
  simp only [clausePrem, hargs, hq, hp, Option.map_none, List.map, Term.koreList] at hprem
  unfold premise at hprem
  simp only [List.zip, List.zipWith, KoreAML.argsConj, reqPat] at hprem
  rw [tr_and2, KoreAML.interp_sAnd, tr_and2, KoreAML.interp_sAnd] at hprem
  have hin := hprem.2.1
  rw [KoreAML.tr] at hin
  have hSK : ∀ a, (KoreAML.trSort t (KoreAML.srt (c.sortName Srt.k))).interpret I e a ↔ a = σK := fun a => by
    rw [trSort_srt, KoreAML.interp_sym]; exact hσK1 a
  have hX0e : ∀ a, (KoreAML.tr ⟨t, []⟩ (KoreAML.ev (toString "X" ++ toString 0)
      (KoreAML.srt (c.sortName Srt.k)))).interpret I e a ↔ a = e.evalEvar (t.ev X0k) := fun a => Iff.rfl
  rw [KoreAML.interp_sIn hD hcd hSK hRv hσK2 hR
    (fun a ha => by rw [(hX0e a).mp ha]; exact (KoreAML.interp_inhOf_of hSK).mp hX0) b] at hin
  obtain ⟨⟨a0, ha0, hP⟩, -⟩ := hin
  rw [(hX0e a0).mp ha0] at hP
  obtain ⟨x, hx, hK⟩ := (predInst_kseqInj_iff X p _).mp hP
  have hxs : InS I (c.sortName X) x :=
    patSortC hI hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c cl.vars) hvar hcp hsp x hx
  -- the valuation of the general clause's table: `R` and `X0` as here, its variable `x`
  have h00 : 0 < cl0.vars.length := by rw [h0v]; exact Nat.zero_lt_one
  let Vk := canonKey c cl0.vars 0
  have hVk : Vk = .evar ("Var" ++ ("V" ++ toString 0)) (KoreAML.srt (c.sortName X)) := by
    show canonKey c cl0.vars 0 = _
    rw [canonKey_eq c h00, h0v]; rfl
  generalize htg : KoreAML.tableOf (clauseAxiom c fn cl0).sortVars (clauseAxiom c fn cl0).pattern = tg
  let σR := e.evalEvar (t.ev (.sortVar "R"))
  let a0 := e.evalEvar (t.ev X0k)
  let e' : Valuation M := valOf tg (fun k => if k = .sortVar "R" then σR else if k = X0k then a0 else x)
  have hvarsG : ∀ k, k ∈ KoreAML.varsOf (clausePrem c fn cl0) → k ∈ tg := fun k hk => by
    rw [← htg]
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.implies KoreAML.R (clausePrem c fn cl0) (clauseConcl c fn cl0))
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hRm : KoreAML.VarKey.sortVar "R" ∈ tg := by
    rw [← htg]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hXm : X0k ∈ tg := hvarsG _ (hpv.1 0 _ (by rw [hargs]; rfl))
  have hVm : Vk ∈ tg := hvarsG _ (hpv.2.1 0 h00)
  have heR : e'.evalEvar (tg.ev (.sortVar "R")) = σR := by rw [valOf_ev hRm]; simp
  have heX : e'.evalEvar (tg.ev X0k) = a0 := by rw [valOf_ev hXm]; simp [X0k]
  have heV : e'.evalEvar (tg.ev Vk) = x := by
    rw [valOf_ev hVm, hVk]; simp [X0k]; intro h; exact absurd h (by decide)
  have hRv' : ∀ b, (KoreAML.trSort tg KoreAML.R).interpret I e' b ↔ b = σR :=
    fun b => by rw [trSort_R, KoreAML.interp_evar, heR]
  -- the general clause's guards hold at e'
  have hgG : ∀ k ∈ ((clauseAxiom c fn cl0).sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (clauseAxiom c fn cl0).pattern).eraseDups, ∀ m',
      (KoreAML.guardOf tg k).interpret I e' m' := by
    intro k hk m'
    rcases List.mem_append.mp (List.mem_eraseDups.mp hk) with hk | hk
    · obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hk
      rw [mem_one h1]
      show (KoreAML.guardOf tg (.sortVar "R")).interpret I e' m'
      rw [KoreAML.interp_guard_sortVar hD, heR]
      exact hR
    · have hk' : k = X0k ∨ k = Vk := by
        change k ∈ KoreAML.freeOf [] (.implies KoreAML.R (clausePrem c fn cl0) (clauseConcl c fn cl0)) at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · rcases hpv.2.2 k hk with ⟨j, s', hj, rfl⟩ | ⟨i, hi, rfl⟩
          · rw [hargs] at hj
            obtain ⟨rfl, rfl⟩ : j = 0 ∧ s' = c.sortName Srt.k := by
              cases j with
              | zero => simp at hj; exact ⟨rfl, hj.symm⟩
              | succ j => simp at hj
            exact Or.inl rfl
          · rw [h0v] at hi
            rw [show i = 0 by simpa using hi]
            exact Or.inr rfl
        · unfold clauseConcl at hk
          rw [KoreAML.freeOf] at hk
          rcases List.mem_append.mp hk with hk | hk
          · unfold KoreAML.ap at hk; rw [KoreAML.freeOf] at hk
            obtain ⟨n, s', hn, rfl⟩ := freeOf_callX _ 0 hk
            rw [hargs] at hn
            cases n with
            | zero => simp at hn; subst hn; exact Or.inl rfl
            | succ n => simp at hn
          · obtain ⟨i, hi, -⟩ := freeOf_clauseConclRight hk
            rcases hi with hi | ⟨t', ht', -⟩
            · rw [hr0] at hi; simp [varOccs] at hi
            · rw [he0] at ht'; cases ht'
      rcases hk' with rfl | rfl
      · rw [KoreAML.interp_guard_evar hD, heX, trSort_srt]
        rw [trSort_srt] at hX0
        exact ((KoreAML.Closed.sym _).app (KoreAML.Closed.sym _)).interp e e' a0 |>.mp hX0
      · rw [hVk, KoreAML.interp_guard_evar hD, trSort_srt, ← hVk, heV]
        exact (inS_iff e').mpr hxs
  have hb' : (KoreAML.inhOf (KoreAML.trSort tg KoreAML.R)).interpret I e' b :=
    (KoreAML.interp_inhOf_of hRv').mpr ((KoreAML.interp_inhOf_of hRv).mp hb)
  have hpg := (KoreAML.trAxiom_at hD hgen e' (by rw [htg]; exact hgG) b).mpr (by rw [htg]; exact hb')
  rw [htg] at hpg
  change (KoreAML.tr ⟨tg, []⟩ (.implies KoreAML.R (clausePrem c fn cl0) (clauseConcl c fn cl0))).interpret I e' b at hpg
  rw [KoreAML.tr, KoreAML.interp_sImp] at hpg
  have hprem0 : (KoreAML.tr ⟨tg, []⟩ (clausePrem c fn cl0)).interpret I e' b := by
    simp only [clausePrem, hargs, hq0, h0p, Option.map_none, List.map, Term.koreList]
    unfold premise
    simp only [List.zip, List.zipWith, KoreAML.argsConj, reqPat]
    rw [tr_and2, KoreAML.interp_sAnd, tr_and2, KoreAML.interp_sAnd]
    have htop : (KoreAML.tr ⟨tg, []⟩ (Kore.Pattern.top KoreAML.R)).interpret I e' b := by
      rw [KoreAML.tr, KoreAML.interp_sTop hD isFree_R]; exact hb'
    refine ⟨htop, ?_, htop⟩
    rw [KoreAML.tr]
    have hSK' : ∀ a, (KoreAML.trSort tg (KoreAML.srt (c.sortName Srt.k))).interpret I e' a ↔ a = σK := fun a => by
      rw [trSort_srt, KoreAML.interp_sym]; exact hσK1 a
    have hX0e' : ∀ a, (KoreAML.tr ⟨tg, []⟩ (KoreAML.ev (toString "X" ++ toString 0)
        (KoreAML.srt (c.sortName Srt.k)))).interpret I e' a ↔ a = a0 := fun a => by
      show a = e'.evalEvar (tg.ev X0k) ↔ _
      rw [heX]
    rw [KoreAML.interp_sIn hD hcd hSK' hRv' hσK2 hR
      (fun a ha => by rw [(hX0e' a).mp ha]; exact (KoreAML.interp_inhOf_of hSK).mp hX0) b]
    refine ⟨⟨a0, (hX0e' a0).mpr rfl, (predInst_kseqInj_iff X (.var 0) a0).mpr ⟨x, ?_, hK⟩⟩,
      (KoreAML.interp_inhOf_of hRv).mp hb⟩
    rw [tr_var]
    exact heV.symm
  have hc0 := hpg.2 hprem0
  rw [hconcl]
  unfold clauseConcl at hc0 ⊢
  rw [KoreAML.tr] at hc0 ⊢
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..))
  have hSr : ∀ (tb : KoreAML.VarTable) (ev : Valuation M) a,
      (KoreAML.trSort tb (KoreAML.srt (c.sortName fn.result))).interpret I ev a ↔ a = σr :=
    fun tb ev a => by rw [trSort_srt, KoreAML.interp_sym]; exact hσr1 a
  rw [KoreAML.interp_sEquals hD hcd (hSr tg e') hRv' hσr2 hR] at hc0
  rw [KoreAML.interp_sEquals hD hcd (hSr t e) hRv hσr2 hR]
  refine ⟨hc0.1, fun a ha => ?_⟩
  have hca := hc0.2 a ha
  have hap : ∀ a, (KoreAML.tr ⟨tg, []⟩ (KoreAML.ap (c.symName fn.label)
        (KoreAML.vars (KoreAML.numbered "X" 0 (List.map c.sortName fn.args))))).interpret I e' a ↔
      (KoreAML.tr ⟨t, []⟩ (KoreAML.ap (c.symName fn.label)
        (KoreAML.vars (KoreAML.numbered "X" 0 (List.map c.sortName fn.args))))).interpret I e a := by
    intro a
    rw [hargs]
    simp only [List.map, KoreAML.numbered, KoreAML.vars, KoreAML.ap]
    rw [KoreAML.tr, KoreAML.tr]
    simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte, KoreAML.trSortApp, KoreAML.trArgs_cons,
      KoreAML.trArgs_nil, Function.comp_apply]
    refine KoreAML.interp_app_congr (e := e') (e' := e) (fun _ => Iff.rfl) (fun m => ?_) a
    rw [KoreAML.tr, KoreAML.tr]
    show m = e'.evalEvar (tg.ev X0k) ↔ m = e.evalEvar (t.ev X0k)
    rw [heX]
  have hright : ∀ a, (KoreAML.tr ⟨tg, []⟩ (clauseRight c fn cl0)).interpret I e' a ↔
      (KoreAML.tr ⟨t, []⟩ (clauseRight c fn cl0)).interpret I e a := by
    intro a
    unfold clauseRight
    rw [hr0, he0]
    simp only [Option.map_none, reqPat, Term.kore]
    rw [tr_and2, tr_and2, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    unfold srtOf
    rw [KoreAML.tr_dv, KoreAML.tr_dv, KoreAML.tr, KoreAML.tr, trSort_srt, trSort_srt,
      KoreAML.interp_sTop hD rfl, KoreAML.interp_sTop hD rfl]
    exact and_congr (((KoreAML.Closed.sym _).app (KoreAML.Closed.sym _)).interp e' e a)
      (((KoreAML.Closed.sym _).app (KoreAML.Closed.sym _)).interp e' e a)
  exact (hap a).symm.trans (hca.trans (hright a))

/-- **What `predInstOfClause` checks.** -/
theorem predInstOfClause_spec {cl0 cl : Clause} (h : Parse.predInstOfClause c cl0 cl = true) :
    ∃ (X : Srt) (p : Term) (s : Srt) (lit : Lit), cl0.vars = [X] ∧
      cl0.pats = [.app kseq [.inj X Srt.kitem (.var 0), .app dotk []]] ∧
      cl.pats = [.app kseq [.inj X Srt.kitem p, .app dotk []]] ∧
      cl0.req = none ∧ cl0.ens = none ∧ cl0.exs = [] ∧ cl0.pre = .top ∧ cl0.post = .top ∧
      cl0.rhs = .dv s lit ∧
      Parse.predInstCtorPat c p = true ∧ sortOfTerm c.patCtxAll cl.vars p = some X ∧
      (∀ i < cl.vars.length, i ∈ varOccs p) ∧
      cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top ∧ cl.post = .top ∧
      cl.rhs = cl0.rhs ∧ cl.prio = cl0.prio ∧ cl.aside = cl0.aside := by
  unfold Parse.predInstOfClause at h
  split at h
  · rename_i X k X' K d k' Y K' p d' h0v h0p hp
    split at h
    · rename_i s lit hr
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, List.isEmpty_iff] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hd⟩, hK⟩, hX'⟩, hq0⟩, he0⟩, hx0⟩, hpr0⟩, hpo0⟩, hk'⟩, hd'⟩, hK'⟩, hY⟩,
        hcp⟩, hsp⟩, hb⟩, hq⟩, he⟩, hx⟩, hpr⟩, hpo⟩, hrhs⟩, hprio⟩, hasd⟩ := h
      subst hk hd hK hk' hd' hK'
      rw [hX'] at h0p
      rw [hY] at hp
      exact ⟨X, p, s, lit, h0v, h0p, hp, hq0, he0, hx0, GenEqs.isTop_eq hpr0, GenEqs.isTop_eq hpo0, hr,
        hcp, hsp, fun i hi => by simpa [binds] using List.all_eq_true.mp hb i (List.mem_range.mpr hi),
        hq, he, hx, GenEqs.isTop_eq hpr, GenEqs.isTop_eq hpo, Det.Term.beq_sound hrhs, hprio, hasd⟩
    · cases h
  · cases h

/-- A constructor is no function-overloaded symbol: such a symbol is an overloading symbol. -/
theorem not_fnOvl_of_isCtorPI (H : OvlLaws.OvlFnFacts c) {f : Sym} (hf : c.isCtor f = true) : f ∉ c.fnOvlSyms := by
  intro hm
  unfold Semantics.fnOvlSyms at hm
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
  have hc := (c.isOvl_parts (H.isOvl o (List.mem_filter.mp ho).1)).1
  rw [hf] at hc
  cases hc

mutual
  /-- A constructor pattern applies no function-overloaded symbol. -/
  theorem predInstCtorPat_noFnOvl (H : OvlLaws.OvlFnFacts c) :
      ∀ {t : Term}, Parse.predInstCtorPat c t = true → c.NoFnOvlIn t
    | .var _, _ => by simp [Semantics.NoFnOvlIn, symOccs]
    | .app g ts, h => by
      rw [Parse.predInstCtorPat, Bool.and_eq_true] at h
      exact NoFnOvlIn.mk_app (not_fnOvl_of_isCtorPI H h.1) (predInstCtorPatList_noFnOvl H h.2)
    | .dv _ _, h | .inj _ _ _, h | .as _ _, h => by simp [Parse.predInstCtorPat] at h
    termination_by structural t => t
  theorem predInstCtorPatList_noFnOvl (H : OvlLaws.OvlFnFacts c) :
      ∀ {ts : List Term}, Parse.predInstCtorPatList c ts = true → c.NoFnOvlInL ts
    | [], _ => NoFnOvlIn.nil
    | t :: ts, h => by
      rw [Parse.predInstCtorPatList, Bool.and_eq_true] at h
      exact NoFnOvlIn.mk_cons (predInstCtorPat_noFnOvl H h.1) (predInstCtorPatList_noFnOvl H h.2)
    termination_by structural ts => ts
end

mutual
  theorem predInstCtorPat_coll : ∀ {t : Term}, Parse.predInstCtorPat c t = true → collPat c t = true
    | .var _, _ => by rw [collPat]
    | .app g ts, h => by
      rw [Parse.predInstCtorPat, Bool.and_eq_true] at h
      rw [collPat, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨Or.inl h.1, predInstCtorPatList_coll h.2⟩
    | .dv _ _, h | .inj _ _ _, h | .as _ _, h => by simp [Parse.predInstCtorPat] at h
    termination_by structural t => t
  theorem predInstCtorPatList_coll : ∀ {ts : List Term},
      Parse.predInstCtorPatList c ts = true → collPats c ts = true
    | [], _ => by rw [collPats]
    | t :: ts, h => by
      rw [Parse.predInstCtorPatList, Bool.and_eq_true] at h
      rw [collPats, Bool.and_eq_true]
      exact ⟨predInstCtorPat_coll h.1, predInstCtorPatList_coll h.2⟩
    termination_by structural ts => ts
end

/-- A clause of a function with no clause before it, without a predicate or existential
variables: its equation is `clauseAxiom`'s. -/
theorem predInst_prioEquation_axiom {fn : Fn} {cl : Clause} (hlow : lowerClauses fn cl = []) (hpre : cl.pre = .top)
    (hex : cl.exs = []) : prioEquation c fn cl = .axiom (clauseAxiom c fn cl) := by
  unfold prioEquation
  rw [hlow]
  simp only [List.isEmpty_nil, ↓reduceIte]
  rw [clauseEquation_top hpre hex]
  rfl

/-- **An instance of a sort predicate's clause at a constructor pattern is entailed**: where
`predInstOK` accepts an equation of the text, read as a clause (`clause?`, without an exclusion)
its equation (`prioEquation`, among the predicate's clauses) holds in every model of `Γ`. -/
theorem predInst_entailed {N : Parse.Names} {msrc : String} {e : Parse.RawEqn}
    (hc : c.coreOK = true) (h : Parse.predInstOK N msrc c e = true) :
    ∃ fn ∈ c.sortPreds, c.symName fn.label = e.fn ∧ ∃ cl cp, Parse.clause? N msrc e none = .ok (cl, cp) ∧
      ∀ it ∈ kernelItems [prioEquation c fn cl], Γ c ⊧ it.pat := by
  unfold Parse.predInstOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hm⟩ := h
  split at hm
  · rename_i fn cl cp hf hr
    have hfn : fn ∈ c.sortPreds := List.mem_of_find?_eq_some hf
    have hname : c.symName fn.label = e.fn := by simpa using List.find?_some hf
    have hcl : Parse.clause? N msrc e none = .ok (cl, cp) := by
      cases hq : Parse.clause? N msrc e none with
      | error _ => rw [hq] at hr; cases hr
      | ok r => rw [hq] at hr; simp only [Except.toOption, Option.some.injEq] at hr; rw [hr]
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.all_eq_true] at hm
    obtain ⟨hargs, cl0, hcl0, ⟨hi, hs⟩, hall⟩ := hm
    obtain ⟨X, p, s, lit, h0v, h0p, hp, hq0, he0, hx0, hpr0, hpo0, hr0, hcp, hsp, hbind, hq, he, hx, hpr, hpo,
      hrhs, hprio, -⟩ := predInstOfClause_spec hi
    have hlow0 : lowerClauses fn cl0 = [] := by
      unfold lowerClauses
      refine List.filter_eq_nil_iff.mpr fun cl' hcl' => ?_
      have := hall cl' hcl'
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_and]
      rcases this with h1 | h1
      · intro h2; rw [h1] at h2; cases h2
      · exact fun _ => h1
    have hlow : lowerClauses fn cl = [] := by
      unfold lowerClauses at hlow0 ⊢; rw [hprio]; exact hlow0
    refine ⟨fn, hfn, hname, cl, cp, hcl, fun it hit => ?_⟩
    rw [predInst_prioEquation_axiom hlow hpr hx] at hit
    rw [show kernelItems [.axiom (clauseAxiom c fn cl)] = [KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl⟩]
      from rfl, List.mem_singleton] at hit
    subst hit
    intro M _ I hI
    have hit0 : KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl0⟩ ∈ kernelItems [prioEquation c fn cl0] := by
      rw [predInst_prioEquation_axiom hlow0 hpr0 hx0]; exact List.mem_singleton_self _
    have hgen : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl0⟩).pat :=
      hI _ (show Γ c _ from Or.inl (Or.inl (Or.inr (sortPred_items hfn hcl0 _ hit0))))
    have hH : OvlLaws.OvlFnFacts c := by
      obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core hc
      exact (hno.hyp (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans).fnFacts
    exact predInst_core hc hI (List.mem_append_right _ hfn) hargs hgen h0v h0p hs hp hq0 he0 hr0
      (predInstCtorPat_coll hcp) (sortOfTerm_to_nf p hsp (predInstCtorPat_noFnOvl hH hcp)) hbind hq he hrhs
  · cases hm

end

/-! ## An item read under another table -/

/-- Every element and set variable of an AML pattern renamed, binders included. -/
def owiRen (f : EVar → EVar) (g : SVar → SVar) : KoreAML.P → KoreAML.P
  | .evar x => .evar (f x)
  | .svar X => .svar (g X)
  | .bottom => .bottom
  | .symbol σ => .symbol σ
  | .application φ ψ => .application (owiRen f g φ) (owiRen f g ψ)
  | .implication φ ψ => .implication (owiRen f g φ) (owiRen f g ψ)
  | .existential x φ => .existential (f x) (owiRen f g φ)
  | .mu X φ => .mu (g X) (owiRen f g φ)

section
variable {M : Type} {I : Interpretation KoreAML.Sym M} {f : EVar → EVar} {g : SVar → SVar}

theorem owiRen_update_comp {α β : Type} [DecidableEq α] {h : α → α} (hh : Function.Injective h) (v : α → β)
    (x : α) (a : β) : (Function.update v (h x) a ∘ h) = Function.update (v ∘ h) x a := by
  funext y
  by_cases hy : y = x
  · subst hy; simp only [Function.comp_apply, Function.update_same]
  · simp only [Function.comp_apply]
    rw [Function.update_noteq (fun e => hy (hh e)), Function.update_noteq hy]
    rfl

/-- **A renamed pattern denotes, at a valuation, what the pattern denotes at the valuation read
through the renaming**, for one-to-one renamings. -/
theorem interp_owiRen (hf : Function.Injective f) (hg : Function.Injective g) :
    ∀ (φ : KoreAML.P) (e : Valuation M) (m : M),
      (owiRen f g φ).interpret I e m ↔ φ.interpret I ⟨e.evalEvar ∘ f, e.evalSvar ∘ g⟩ m := by
  intro φ
  induction φ with
  | evar x => intro e m; exact Iff.rfl
  | svar X => intro e m; exact Iff.rfl
  | bottom => intro e m; exact Iff.rfl
  | symbol σ => intro e m; exact Iff.rfl
  | application φ ψ ih1 ih2 =>
    intro e m
    simp only [owiRen, Pattern.interpret]
    exact exists_congr fun a => exists_congr fun b => and_congr (ih1 e a) (and_congr_left' (ih2 e b))
  | implication φ ψ ih1 ih2 =>
    intro e m
    simp only [owiRen, Pattern.interpret]
    exact imp_congr (ih1 e m) (ih2 e m)
  | existential x φ ih =>
    intro e m
    simp only [owiRen, Pattern.interpret]
    refine exists_congr fun a => ?_
    rw [ih]
    simp only [owiRen_update_comp hf]
  | mu X φ ih =>
    intro e m
    simp only [owiRen, Pattern.interpret]
    refine forall_congr' fun B => ?_
    have : ∀ m', (owiRen f g φ).interpret I ⟨e.evalEvar, Function.update e.evalSvar (g X) B⟩ m' ↔
        φ.interpret I ⟨e.evalEvar ∘ f, Function.update (e.evalSvar ∘ g) X B⟩ m' := fun m' => by
      rw [ih]; simp only [owiRen_update_comp hg]
    simp only [this]

/-- A valid pattern stays valid under a one-to-one renaming. -/
theorem sat_owiRen (hf : Function.Injective f) (hg : Function.Injective g) {φ : KoreAML.P} (h : I ⊧ᴵ φ) :
    I ⊧ᴵ owiRen f g φ := fun e m => (interp_owiRen hf hg φ e m).mpr (h _ m)

theorem owiRen_substSvar (hg : Function.Injective g) (X : SVar) (χ : KoreAML.P) :
    ∀ φ : KoreAML.P, owiRen f g (φ.substSvar X χ) = (owiRen f g φ).substSvar (g X) (owiRen f g χ)
  | .evar _ => rfl
  | .svar Y => by
    by_cases h : X = Y
    · subst h; simp [owiRen, Pattern.substSvar]
    · have h' : g X ≠ g Y := fun e => h (hg e)
      simp [owiRen, Pattern.substSvar, h, h']
  | .bottom => rfl
  | .symbol _ => rfl
  | .application φ ψ => by
    simp only [Pattern.substSvar, owiRen]; rw [owiRen_substSvar hg X χ φ, owiRen_substSvar hg X χ ψ]
  | .implication φ ψ => by
    simp only [Pattern.substSvar, owiRen]; rw [owiRen_substSvar hg X χ φ, owiRen_substSvar hg X χ ψ]
  | .existential x φ => by
    simp only [Pattern.substSvar, owiRen]; rw [owiRen_substSvar hg X χ φ]
  | .mu Y φ => by
    by_cases h : X = Y
    · subst h; simp [owiRen, Pattern.substSvar]
    · have h' : g X ≠ g Y := fun e => h (hg e)
      simp only [Pattern.substSvar, owiRen, h, h', ite_false]
      rw [owiRen_substSvar hg X χ φ]

end

section
variable {f : EVar → EVar} {g : SVar → SVar}
open KoreAML

theorem owiRen_sNot (s φ : P) : owiRen f g (sNot s φ) = sNot (owiRen f g s) (owiRen f g φ) := rfl
theorem owiRen_sAnd (φ ψ : P) : owiRen f g (sAnd φ ψ) = sAnd (owiRen f g φ) (owiRen f g ψ) := rfl
theorem owiRen_sOr (s φ ψ : P) : owiRen f g (sOr s φ ψ) = sOr (owiRen f g s) (owiRen f g φ) (owiRen f g ψ) := rfl
theorem owiRen_sImp (s φ ψ : P) : owiRen f g (sImp s φ ψ) = sImp (owiRen f g s) (owiRen f g φ) (owiRen f g ψ) := rfl
theorem owiRen_sIff (s φ ψ : P) : owiRen f g (sIff s φ ψ) = sIff (owiRen f g s) (owiRen f g φ) (owiRen f g ψ) := rfl
theorem owiRen_sExists (x : EVar) (s φ : P) :
    owiRen f g (sExists x s φ) = sExists (f x) (owiRen f g s) (owiRen f g φ) := rfl
theorem owiRen_sForall (s : P) (x : EVar) (s' φ : P) :
    owiRen f g (sForall s x s' φ) = sForall (owiRen f g s) (f x) (owiRen f g s') (owiRen f g φ) := rfl
theorem owiRen_sTop (h0 : f topVar = topVar) (s : P) : owiRen f g (sTop s) = sTop (owiRen f g s) := by
  show owiRen f g (sExists topVar s (.evar topVar)) = _
  rw [owiRen_sExists]; show sExists (f topVar) _ (.evar (f topVar)) = _; rw [h0]; rfl
theorem owiRen_sBot (h0 : f topVar = topVar) (s : P) : owiRen f g (sBot s) = sBot (owiRen f g s) := by
  show owiRen f g (sNot s (sTop s)) = _; rw [owiRen_sNot, owiRen_sTop h0]; rfl
theorem owiRen_sCeil (s s' φ : P) : owiRen f g (sCeil s s' φ) = sCeil (owiRen f g s) (owiRen f g s') (owiRen f g φ) := rfl
theorem owiRen_sFloor (s s' φ : P) :
    owiRen f g (sFloor s s' φ) = sFloor (owiRen f g s) (owiRen f g s') (owiRen f g φ) := rfl
theorem owiRen_sEquals (s s' φ ψ : P) :
    owiRen f g (sEquals s s' φ ψ) = sEquals (owiRen f g s) (owiRen f g s') (owiRen f g φ) (owiRen f g ψ) := rfl
theorem owiRen_sIn (s s' φ ψ : P) :
    owiRen f g (sIn s s' φ ψ) = sIn (owiRen f g s) (owiRen f g s') (owiRen f g φ) (owiRen f g ψ) := rfl
theorem owiRen_sNext (φ : P) : owiRen f g (sNext φ) = sNext (owiRen f g φ) := rfl
theorem owiRen_sRewrites (s φ ψ : P) :
    owiRen f g (sRewrites s φ ψ) = sRewrites (owiRen f g s) (owiRen f g φ) (owiRen f g ψ) := rfl
theorem owiRen_sNu (hg : Function.Injective g) (s : P) (X : SVar) (φ : P) :
    owiRen f g (sNu s X φ) = sNu (owiRen f g s) (g X) (owiRen f g φ) := by
  unfold sNu
  rw [owiRen_sNot, show owiRen f g (.mu X (sNot s (φ.substSvar X (sNot s (.svar X))))) =
    .mu (g X) (owiRen f g (sNot s (φ.substSvar X (sNot s (.svar X))))) from rfl, owiRen_sNot,
    owiRen_substSvar hg, owiRen_sNot]
  rfl
theorem owiRen_sym (σ : KoreAML.Sym) : owiRen f g (sym σ) = sym σ := rfl
theorem owiRen_app (φ ψ : P) : owiRen f g (φ ⬝ ψ) = owiRen f g φ ⬝ owiRen f g ψ := rfl
theorem owiRen_member (x : EVar) (φ : P) : owiRen f g (x ∈∈ φ) = (f x ∈∈ owiRen f g φ) := rfl
theorem owiRen_included (φ ψ : P) : owiRen f g (φ ⊆⊆ ψ) = (owiRen f g φ ⊆⊆ owiRen f g ψ) := rfl
theorem owiRen_equal (φ ψ : P) : owiRen f g (φ ≡ ψ) = (owiRen f g φ ≡ owiRen f g ψ) := rfl
theorem owiRen_impl (φ ψ : P) : owiRen f g (φ ⇒ ψ) = (owiRen f g φ ⇒ owiRen f g ψ) := rfl
theorem owiRen_inhOf (s : P) : owiRen f g (inhOf s) = inhOf (owiRen f g s) := rfl
theorem owiRen_conjList : ∀ (ws : List P), owiRen f g (conjList ws) = conjList (ws.map (owiRen f g))
  | [] => rfl
  | [_] => rfl
  | w :: v :: ws => by
    show owiRen f g (w ⋀ conjList (v :: ws)) = _
    rw [show owiRen f g (w ⋀ conjList (v :: ws)) = (owiRen f g w ⋀ owiRen f g (conjList (v :: ws))) from rfl,
      owiRen_conjList (v :: ws)]
    rfl

/-- The renaming takes the variables of `tg` to those of `t`, at the keys `ks`. -/
def OwiAt (f : EVar → EVar) (g : SVar → SVar) (tg t : VarTable) (ks : List VarKey) : Prop :=
  ∀ k ∈ ks, f (tg.ev k) = t.ev k ∧ g (tg.sv k) = t.sv k

theorem OwiAt.sub {tg t : VarTable} {ks ks' : List VarKey} (h : OwiAt f g tg t ks) (hs : ∀ k ∈ ks', k ∈ ks) :
    OwiAt f g tg t ks' := fun k hk => h k (hs k hk)

mutual
  theorem trSort_owiRen {tg t : VarTable} : ∀ (s : Kore.KSort), OwiAt f g tg t (sortVarsOf s) →
      trSort t s = owiRen f g (trSort tg s)
    | .var α, h => by
      rw [trSort, trSort]
      show _ = (Pattern.evar (f _) : P)
      rw [(h (sortVarKey α) (by simp [sortVarsOf])).1]
    | .ctor _ args, h => by
      rw [trSort, trSort, ← owiRen_sym]; exact trSortApp_owiRen args _ (by rw [sortVarsOf] at h; exact h)
  theorem trSortApp_owiRen {tg t : VarTable} : ∀ (ss : List Kore.KSort) (acc : P),
      OwiAt f g tg t (sortVarsOfList ss) → trSortApp t (owiRen f g acc) ss = owiRen f g (trSortApp tg acc ss)
    | [], _, _ => rfl
    | s :: ss, acc, h => by
      rw [trSortApp, trSortApp, trSort_owiRen s (h.sub fun k hk => by simp [sortVarsOfList, hk]),
        ← owiRen_app, trSortApp_owiRen ss _ (h.sub fun k hk => by simp [sortVarsOfList, hk])]
end

end

/-- A key is among the keys of a pattern, of a list of patterns or of sorts, by their equations. -/
macro "owi_vmem" : tactic =>
  `(tactic| (simp only [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.sortVarsOf, KoreAML.sortVarsOfList,
      List.mem_append, List.mem_cons, List.mem_singleton]; simp [*]))

section
variable {f : EVar → EVar} {g : SVar → SVar} {c c' : KoreAML.Ctx}
open KoreAML

set_option maxHeartbeats 4000000 in
mutual
  /-- **One pattern under two tables**: where the renaming takes the index of each variable of p in
  the one table to its index in the other, keeps `topVar` and is one-to-one on set variables, the
  translation under the other table is the translation under the one, renamed. -/
  theorem tr_owiRen (h0 : f topVar = topVar) (hg : Function.Injective g) (hal : c'.aliases = c.aliases) :
      ∀ (p : Kore.Pattern), OwiAt f g c.vars c'.vars (varsOf p) → tr c' p = owiRen f g (tr c p)
    | .var (.evar x), h => by
      simp only [tr]; show _ = (Pattern.evar (f _) : P); rw [(h (evarKey x) (by owi_vmem)).1]
    | .var (.svar X), h => by
      simp only [tr]; show _ = (Pattern.svar (g _) : P); rw [(h (svarKey X) (by owi_vmem)).2]
    | .app hd ss ps, h => by
      simp only [tr, hal]
      split
      · rfl
      · rw [← owiRen_sym, trSortApp_owiRen ss _ (h.sub fun k hk => by owi_vmem),
          trArgs_owiRen h0 hg hal ps _ (h.sub fun k hk => by owi_vmem)]; rfl
    | .string _, _ => by simp only [tr]; rfl
    | .top s, h => by
      simp only [tr]; rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), owiRen_sTop h0]
    | .bottom s, h => by
      simp only [tr]; rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), owiRen_sBot h0]
    | .dv s _, h => by
      simp only [tr]; rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem)]; rfl
    | .not s p, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]; rfl
    | .next s p, h => by
      simp only [tr]; rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]; rfl
    | .and s ps, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), trAndList_owiRen h0 hg hal ps _ (h.sub fun k hk => by owi_vmem)]
    | .or s ps, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), trOrList_owiRen h0 hg hal ps _ (h.sub fun k hk => by owi_vmem)]
    | .implies s p q, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal q (h.sub fun k hk => by owi_vmem)]; rfl
    | .iff s p q, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal q (h.sub fun k hk => by owi_vmem)]; rfl
    | .rewrites s p q, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal q (h.sub fun k hk => by owi_vmem)]; rfl
    | .exist s x p, h => by
      simp only [tr]
      rw [trSort_owiRen x.sort (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem),
        owiRen_sExists, (h (evarKey x) (by owi_vmem)).1]
    | .forall s x p, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), trSort_owiRen x.sort (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), owiRen_sForall, (h (evarKey x) (by owi_vmem)).1]
    | .mu X p, h => by
      simp only [tr]
      rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]
      show _ = Pattern.mu (g _) _
      rw [(h (svarKey X) (by owi_vmem)).2]
    | .nu X p, h => by
      simp only [tr]
      rw [trSort_owiRen X.sort (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem),
        owiRen_sNu hg, (h (svarKey X) (by owi_vmem)).2]
    | .ceil s s' p, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), trSort_owiRen s' (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]; rfl
    | .floor s s' p, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), trSort_owiRen s' (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]; rfl
    | .equals s s' p q, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), trSort_owiRen s' (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal q (h.sub fun k hk => by owi_vmem)]; rfl
    | .in s s' p q, h => by
      simp only [tr]
      rw [trSort_owiRen s (h.sub fun k hk => by owi_vmem), trSort_owiRen s' (h.sub fun k hk => by owi_vmem),
        tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), tr_owiRen h0 hg hal q (h.sub fun k hk => by owi_vmem)]; rfl
    | .leftAssoc hd ss ps, h => by
      simp only [tr]
      rw [← owiRen_sym, trSortApp_owiRen ss _ (h.sub fun k hk => by owi_vmem),
        trLeftAssoc_owiRen h0 hg hal ps _ (h.sub fun k hk => by owi_vmem)]; rfl
    | .rightAssoc hd ss ps, h => by
      simp only [tr]
      rw [← owiRen_sym, trSortApp_owiRen ss _ (h.sub fun k hk => by owi_vmem),
        trRightAssoc_owiRen h0 hg hal ps _ (h.sub fun k hk => by owi_vmem)]; rfl
  theorem trArgs_owiRen (h0 : f topVar = topVar) (hg : Function.Injective g) (hal : c'.aliases = c.aliases) :
      ∀ (ps : List Kore.Pattern) (acc : P), OwiAt f g c.vars c'.vars (varsOfList ps) →
      trArgs c' (owiRen f g acc) ps = owiRen f g (trArgs c acc ps)
    | [], _, _ => by simp only [trArgs]
    | p :: ps, acc, h => by
      simp only [trArgs]
      rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), ← owiRen_app,
        trArgs_owiRen h0 hg hal ps _ (h.sub fun k hk => by owi_vmem)]
  theorem trAndList_owiRen (h0 : f topVar = topVar) (hg : Function.Injective g) (hal : c'.aliases = c.aliases) :
      ∀ (ps : List Kore.Pattern) (s : P), OwiAt f g c.vars c'.vars (varsOfList ps) →
      trAndList c' (owiRen f g s) ps = owiRen f g (trAndList c s ps)
    | [], s, _ => by simp only [trAndList]; rw [owiRen_sTop h0]
    | [p], s, h => by
      simp only [trAndList]; rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]
    | p :: q :: ps, s, h => by
      have ih := trAndList_owiRen h0 hg hal (q :: ps) s
        (h.sub fun k hk => by rw [varsOfList]; exact List.mem_append_right _ hk)
      simp only [trAndList] at ih ⊢
      rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), ih]; rfl
  theorem trOrList_owiRen (h0 : f topVar = topVar) (hg : Function.Injective g) (hal : c'.aliases = c.aliases) :
      ∀ (ps : List Kore.Pattern) (s : P), OwiAt f g c.vars c'.vars (varsOfList ps) →
      trOrList c' (owiRen f g s) ps = owiRen f g (trOrList c s ps)
    | [], s, _ => by simp only [trOrList]; rw [owiRen_sBot h0]
    | [p], s, h => by
      simp only [trOrList]; rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]
    | p :: q :: ps, s, h => by
      have ih := trOrList_owiRen h0 hg hal (q :: ps) s
        (h.sub fun k hk => by rw [varsOfList]; exact List.mem_append_right _ hk)
      simp only [trOrList] at ih ⊢
      rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), ih]; rfl
  theorem trLeftAssoc_owiRen (h0 : f topVar = topVar) (hg : Function.Injective g) (hal : c'.aliases = c.aliases) :
      ∀ (ps : List Kore.Pattern) (head : P), OwiAt f g c.vars c'.vars (varsOfList ps) →
      trLeftAssoc c' (owiRen f g head) ps = owiRen f g (trLeftAssoc c head ps)
    | [], _, _ => by simp only [trLeftAssoc]
    | p :: ps, head, h => by
      simp only [trLeftAssoc]
      rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem),
        trLeftAssocRest_owiRen h0 hg hal ps _ _ (h.sub fun k hk => by owi_vmem)]
  theorem trLeftAssocRest_owiRen (h0 : f topVar = topVar) (hg : Function.Injective g) (hal : c'.aliases = c.aliases) :
      ∀ (ps : List Kore.Pattern) (head acc : P), OwiAt f g c.vars c'.vars (varsOfList ps) →
      trLeftAssocRest c' (owiRen f g head) (owiRen f g acc) ps = owiRen f g (trLeftAssocRest c head acc ps)
    | [], _, _, _ => by simp only [trLeftAssocRest]
    | p :: ps, head, acc, h => by
      simp only [trLeftAssocRest]
      rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), ← owiRen_app, ← owiRen_app,
        trLeftAssocRest_owiRen h0 hg hal ps _ _ (h.sub fun k hk => by owi_vmem)]
  theorem trRightAssoc_owiRen (h0 : f topVar = topVar) (hg : Function.Injective g) (hal : c'.aliases = c.aliases) :
      ∀ (ps : List Kore.Pattern) (head : P), OwiAt f g c.vars c'.vars (varsOfList ps) →
      trRightAssoc c' (owiRen f g head) ps = owiRen f g (trRightAssoc c head ps)
    | [], _, _ => by simp only [trRightAssoc]
    | [p], head, h => by
      simp only [trRightAssoc]; rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem)]
    | p :: q :: ps, head, h => by
      have ih := trRightAssoc_owiRen h0 hg hal (q :: ps) head
        (h.sub fun k hk => by rw [varsOfList]; exact List.mem_append_right _ hk)
      simp only [trRightAssoc] at ih ⊢
      rw [tr_owiRen h0 hg hal p (h.sub fun k hk => by owi_vmem), ih]; rfl
end

end

section
open KoreAML

mutual
  theorem owi_sortVarsOf_sv : ∀ (s : Kore.KSort) (k : VarKey), k ∈ sortVarsOf s → ∃ n, k = .sortVar n
    | .var α, k, h => ⟨_, mem_one h⟩
    | .ctor _ args, k, h => by rw [sortVarsOf] at h; exact owi_sortVarsOfList_sv args k h
  theorem owi_sortVarsOfList_sv : ∀ (ss : List Kore.KSort) (k : VarKey), k ∈ sortVarsOfList ss → ∃ n, k = .sortVar n
    | [], _, h => absurd h List.not_mem_nil
    | s :: ss, k, h => by
      rw [sortVarsOfList, List.mem_append] at h
      rcases h with h | h
      · exact owi_sortVarsOf_sv s k h
      · exact owi_sortVarsOfList_sv ss k h
end

/-- The sort of a variable key: its sort variables are keys of the pattern too. -/
def owiKeySorts : VarKey → List VarKey
  | .sortVar _ => []
  | .evar _ s => sortVarsOf s
  | .svar _ s => sortVarsOf s

theorem owi_keySorts_key {k : VarKey} (hk : ∃ n, k = .sortVar n) : owiKeySorts k = [] := by
  obtain ⟨n, rfl⟩ := hk; rfl

mutual
  /-- **The sort variables of a variable's sort are keys of the pattern.** -/
  theorem owi_keySorts_varsOf : ∀ (p : Kore.Pattern) (k : VarKey), k ∈ varsOf p → ∀ k' ∈ owiKeySorts k, k' ∈ varsOf p
    | .var (.evar x), k, h, k', h' => by
      simp only [varsOf, List.mem_append, List.mem_singleton] at h ⊢
      rcases h with h | rfl
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inl h'
    | .var (.svar X), k, h, k', h' => by
      simp only [varsOf, List.mem_append, List.mem_singleton] at h ⊢
      rcases h with h | rfl
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inl h'
    | .app _ ss ps, k, h, k', h' | .leftAssoc _ ss ps, k, h, k', h' | .rightAssoc _ ss ps, k, h, k', h' => by
      simp only [varsOf, List.mem_append] at h ⊢
      rcases h with h | h
      · rw [owi_keySorts_key (owi_sortVarsOfList_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inr (owi_keySorts_varsOfList ps k h k' h')
    | .string _, k, h, _, _ => by simp [varsOf] at h
    | .top s, k, h, k', h' | .bottom s, k, h, k', h' | .dv s _, k, h, k', h' => by
      simp only [varsOf] at h
      rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
    | .not s p, k, h, k', h' | .next s p, k, h, k', h' => by
      simp only [varsOf, List.mem_append] at h ⊢
      rcases h with h | h
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inr (owi_keySorts_varsOf p k h k' h')
    | .and s ps, k, h, k', h' | .or s ps, k, h, k', h' => by
      simp only [varsOf, List.mem_append] at h ⊢
      rcases h with h | h
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inr (owi_keySorts_varsOfList ps k h k' h')
    | .implies s p q, k, h, k', h' | .iff s p q, k, h, k', h' | .rewrites s p q, k, h, k', h' => by
      simp only [varsOf, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inl (Or.inr (owi_keySorts_varsOf p k h k' h'))
      · exact Or.inr (owi_keySorts_varsOf q k h k' h')
    | .exist s x p, k, h, k', h' | .forall s x p, k, h, k', h' => by
      simp only [varsOf, List.mem_append, List.mem_singleton] at h ⊢
      rcases h with ((h | h) | rfl) | h
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inl (Or.inl (Or.inr h'))
      · exact Or.inr (owi_keySorts_varsOf p k h k' h')
    | .mu X p, k, h, k', h' | .nu X p, k, h, k', h' => by
      simp only [varsOf, List.mem_append, List.mem_singleton] at h ⊢
      rcases h with ((h | rfl) | h)
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inl (Or.inl h')
      · exact Or.inr (owi_keySorts_varsOf p k h k' h')
    | .ceil s s' p, k, h, k', h' | .floor s s' p, k, h, k', h' => by
      simp only [varsOf, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inr (owi_keySorts_varsOf p k h k' h')
    | .equals s s' p q, k, h, k', h' | .in s s' p q, k, h, k', h' => by
      simp only [varsOf, List.mem_append] at h ⊢
      rcases h with ((h | h) | h) | h
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · rw [owi_keySorts_key (owi_sortVarsOf_sv _ _ h)] at h'; exact absurd h' List.not_mem_nil
      · exact Or.inl (Or.inr (owi_keySorts_varsOf p k h k' h'))
      · exact Or.inr (owi_keySorts_varsOf q k h k' h')
  theorem owi_keySorts_varsOfList : ∀ (ps : List Kore.Pattern) (k : VarKey), k ∈ varsOfList ps →
      ∀ k' ∈ owiKeySorts k, k' ∈ varsOfList ps
    | [], _, h, _, _ => absurd h List.not_mem_nil
    | p :: ps, k, h, k', h' => by
      rw [varsOfList, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (owi_keySorts_varsOf p k h k' h')
      · exact Or.inr (owi_keySorts_varsOfList ps k h k' h')
end

end

section
open KoreAML

mutual
  /-- A free variable of a pattern is one of its variables. -/
  theorem owi_freeOf_varsOf : ∀ (p : Kore.Pattern) (b : List VarKey) (k : VarKey), k ∈ freeOf b p → k ∈ varsOf p
    | .var (.evar x), b, k, h => by
      simp only [freeOf] at h; split at h
      · exact absurd h List.not_mem_nil
      · simp only [varsOf, List.mem_append]; exact Or.inr h
    | .var (.svar X), b, k, h => by
      simp only [freeOf] at h; split at h
      · exact absurd h List.not_mem_nil
      · simp only [varsOf, List.mem_append]; exact Or.inr h
    | .app _ ss ps, b, k, h | .leftAssoc _ ss ps, b, k, h | .rightAssoc _ ss ps, b, k, h => by
      simp only [freeOf] at h; simp only [varsOf, List.mem_append]; exact Or.inr (owi_freeOfList_varsOf ps b k h)
    | .and s ps, b, k, h | .or s ps, b, k, h => by
      simp only [freeOf] at h; simp only [varsOf, List.mem_append]; exact Or.inr (owi_freeOfList_varsOf ps b k h)
    | .string _, _, _, h | .top _, _, _, h | .bottom _, _, _, h | .dv _ _, _, _, h => by
      simp [freeOf] at h
    | .not s p, b, k, h | .next s p, b, k, h => by
      simp only [freeOf] at h; simp only [varsOf, List.mem_append]; exact Or.inr (owi_freeOf_varsOf p b k h)
    | .ceil s s' p, b, k, h | .floor s s' p, b, k, h => by
      simp only [freeOf] at h; simp only [varsOf, List.mem_append]; exact Or.inr (owi_freeOf_varsOf p b k h)
    | .implies s p q, b, k, h | .iff s p q, b, k, h | .rewrites s p q, b, k, h => by
      simp only [freeOf, List.mem_append] at h; simp only [varsOf, List.mem_append]
      rcases h with h | h
      · exact Or.inl (Or.inr (owi_freeOf_varsOf p b k h))
      · exact Or.inr (owi_freeOf_varsOf q b k h)
    | .equals s s' p q, b, k, h | .in s s' p q, b, k, h => by
      simp only [freeOf, List.mem_append] at h; simp only [varsOf, List.mem_append]
      rcases h with h | h
      · exact Or.inl (Or.inr (owi_freeOf_varsOf p b k h))
      · exact Or.inr (owi_freeOf_varsOf q b k h)
    | .exist s x p, b, k, h | .forall s x p, b, k, h => by
      simp only [freeOf] at h; simp only [varsOf, List.mem_append]; exact Or.inr (owi_freeOf_varsOf p _ k h)
    | .mu X p, b, k, h | .nu X p, b, k, h => by
      simp only [freeOf] at h; simp only [varsOf, List.mem_append]; exact Or.inr (owi_freeOf_varsOf p _ k h)
  theorem owi_freeOfList_varsOf : ∀ (ps : List Kore.Pattern) (b : List VarKey) (k : VarKey),
      k ∈ freeOfList b ps → k ∈ varsOfList ps
    | [], _, _, h => absurd h List.not_mem_nil
    | p :: ps, b, k, h => by
      simp only [freeOfList, List.mem_append] at h; simp only [varsOfList, List.mem_append]
      rcases h with h | h
      · exact Or.inl (owi_freeOf_varsOf p b k h)
      · exact Or.inr (owi_freeOfList_varsOf ps b k h)
end

/-- A key's index in the table `tg` read as its index in `t`: 0 (`topVar`) as 0, an index no key of
`tg` has past every index of `t`. -/
def owiIdx (tg t : VarTable) (n : Nat) : Nat :=
  if n = 0 then 0 else match tg.find? (fun k => tg.index k == n) with
    | some k => t.index k
    | none => n + t.length + 1

theorem owi_index_le {t : VarTable} {k : VarKey} (hk : k ∈ t) : t.index k ≤ t.length :=
  List.idxOf_lt_length_of_mem hk

theorem owi_index_inj {t : VarTable} {k k' : VarKey} (hk : k ∈ t) (hk' : k' ∈ t) (h : t.index k = t.index k') :
    k = k' := ev_inj hk hk' (by simp only [VarTable.ev, h])

theorem owiIdx_key {tg t : VarTable} {k : VarKey} (hk : k ∈ tg) : owiIdx tg t (tg.index k) = t.index k := by
  unfold owiIdx
  have hne : tg.index k ≠ 0 := by simp [VarTable.index]
  simp only [hne, ↓reduceIte]
  split
  · rename_i k' hf
    have hk'm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    rw [owi_index_inj hk'm hk hp]
  · rename_i hf
    exact absurd (List.find?_eq_none.mp hf k hk) (by simp)

theorem owiIdx_inj {tg t : VarTable} (hsub : ∀ k ∈ tg, k ∈ t) : Function.Injective (owiIdx tg t) := by
  intro n₁ n₂ h
  have hpos : ∀ n, n ≠ 0 → owiIdx tg t n ≠ 0 := fun n hn => by
    unfold owiIdx; simp only [hn, ↓reduceIte]; split
    · simp [VarTable.index]
    · omega
  by_cases h1 : n₁ = 0
  · by_cases h2 : n₂ = 0
    · rw [h1, h2]
    · exact absurd (h.symm.trans (by unfold owiIdx; simp only [h1, ↓reduceIte])) (hpos n₂ h2)
  · by_cases h2 : n₂ = 0
    · exact absurd (h.trans (by unfold owiIdx; simp only [h2, ↓reduceIte])) (hpos n₁ h1)
    · unfold owiIdx at h
      simp only [h1, h2, ↓reduceIte] at h
      cases hf₁ : tg.find? (fun k => tg.index k == n₁) with
      | none =>
        cases hf₂ : tg.find? (fun k => tg.index k == n₂) with
        | none => rw [hf₁, hf₂] at h; simp only at h; omega
        | some k₂ =>
          rw [hf₁, hf₂] at h; simp only at h
          have := owi_index_le (hsub _ (List.mem_of_find?_eq_some hf₂)); omega
      | some k₁ =>
        cases hf₂ : tg.find? (fun k => tg.index k == n₂) with
        | none =>
          rw [hf₁, hf₂] at h; simp only at h
          have := owi_index_le (hsub _ (List.mem_of_find?_eq_some hf₁)); omega
        | some k₂ =>
          rw [hf₁, hf₂] at h; simp only at h
          have e₁ := List.find?_some hf₁; have e₂ := List.find?_some hf₂
          simp only [beq_iff_eq] at e₁ e₂
          rw [← e₁, ← e₂, owi_index_inj (hsub _ (List.mem_of_find?_eq_some hf₁)) (hsub _ (List.mem_of_find?_eq_some hf₂)) h]

/-- The renaming of the element variables of `tg`'s numbering into `t`'s. -/
def owiF (tg t : VarTable) (x : EVar) : EVar := ⟨owiIdx tg t x.val⟩
/-- The renaming of the set variables of `tg`'s numbering into `t`'s. -/
def owiG (tg t : VarTable) (X : SVar) : SVar := ⟨owiIdx tg t X.val⟩

theorem owiF_inj {tg t : VarTable} (hsub : ∀ k ∈ tg, k ∈ t) : Function.Injective (owiF tg t) := fun x y h => by
  have := owiIdx_inj hsub (congrArg EVar.val h); cases x; cases y; simp_all
theorem owiG_inj {tg t : VarTable} (hsub : ∀ k ∈ tg, k ∈ t) : Function.Injective (owiG tg t) := fun x y h => by
  have := owiIdx_inj hsub (congrArg SVar.val h); cases x; cases y; simp_all
theorem owiF_top {tg t : VarTable} : owiF tg t topVar = topVar := rfl

theorem owiAt_table {tg t : VarTable} : OwiAt (owiF tg t) (owiG tg t) tg t tg := fun k hk =>
  ⟨by simp only [owiF, VarTable.ev, owiIdx_key hk], by simp only [owiG, VarTable.sv, owiIdx_key hk]⟩

theorem owiRen_guardOf {tg t : VarTable} {k : VarKey} (hk : k ∈ tg) (hks : ∀ k' ∈ owiKeySorts k, k' ∈ tg) :
    owiRen (owiF tg t) (owiG tg t) (guardOf tg k) = guardOf t k := by
  have hA := (owiAt_table (tg := tg) (t := t))
  cases k with
  | sortVar n =>
    show owiRen _ _ (sortGuard _) = sortGuard _
    unfold sortGuard
    rw [owiRen_member, (hA _ hk).1]; rfl
  | evar n s =>
    simp only [guardOf]
    rw [owiRen_member, owiRen_inhOf, (hA _ hk).1, ← trSort_owiRen s (hA.sub hks)]
  | svar n s =>
    simp only [guardOf]
    rw [owiRen_included, owiRen_inhOf, ← trSort_owiRen s (hA.sub hks)]
    show (Pattern.svar (owiG tg t (tg.sv _)) ⊆⊆ _ : P) = _
    rw [(hA _ hk).2]

end

section
open KoreAML
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A pattern whose one-to-one renaming is valid is valid: at any valuation, the valuation that
gives each renamed variable the element of its original reads the renamed pattern as the pattern. -/
theorem sat_of_owiRen [Inhabited M] {f : EVar → EVar} {g : SVar → SVar} (hf : Function.Injective f)
    (hg : Function.Injective g) {φ : P} (h : I ⊧ᴵ owiRen f g φ) : I ⊧ᴵ φ := by
  classical
  intro e m
  let e0 : Valuation M := ⟨fun y => if hy : ∃ x, f x = y then e.evalEvar (Classical.choose hy) else default,
    fun Y => if hY : ∃ X, g X = Y then e.evalSvar (Classical.choose hY) else fun _ => False⟩
  have h1 : ∀ x, e0.evalEvar (f x) = e.evalEvar x := fun x => by
    have hy : ∃ x', f x' = f x := ⟨x, rfl⟩
    show (if hy : ∃ x', f x' = f x then e.evalEvar (Classical.choose hy) else default) = _
    simp only [hy, ↓reduceDIte]
    rw [hf (Classical.choose_spec hy)]
  have h2 : ∀ X, e0.evalSvar (g X) = e.evalSvar X := fun X => by
    have hY : ∃ X', g X' = g X := ⟨X, rfl⟩
    show (if hY : ∃ X', g X' = g X then e.evalSvar (Classical.choose hY) else fun _ => False) = _
    simp only [hY, ↓reduceDIte]
    rw [hg (Classical.choose_spec hY)]
  have he : (⟨e0.evalEvar ∘ f, e0.evalSvar ∘ g⟩ : Valuation M) = e := by
    cases e with
    | mk ev sv =>
      have hev : e0.evalEvar ∘ f = ev := funext fun x => h1 x
      have hsv : e0.evalSvar ∘ g = sv := funext fun X => h2 X
      rw [hev, hsv]
  have := (interp_owiRen hf hg φ e0 m).mp (h e0 m)
  rwa [he] at this

/-- **An axiom with a wider premise than a valid one is valid where the valid one's premise is the
wider at its guards**: the reverse of `owi_sat_narrower`. Two axioms over one sort variable list,
`prem → concl` and `prem' → concl` at one sort, `prem'` holding the variables of `prem` and its free
ones among those of `prem`, where `prem → concl` is valid and, read under the table of `prem' →
concl` at a valuation that its guards hold at, `prem` denotes a part of what `prem'` denotes: the
axiom `prem → concl` is valid. It is read under the other's table by `owiRen`, whose validity
gives back its own (`sat_of_owiRen`). -/
theorem owi_sat_wider [Inhabited M] (hD : DefOK I) {a a' : Kore.Axiom} (hsv : a'.sortVars = a.sortVars)
    {R : Kore.KSort} {prem prem' concl : Kore.Pattern}
    (ha : a.pattern = .implies R prem concl) (ha' : a'.pattern = .implies R prem' concl)
    (hvars : ∀ k ∈ varsOf prem, k ∈ varsOf prem') (hfree : ∀ k ∈ freeOf [] prem', k ∈ freeOf [] prem)
    (hprem : ∀ (e : Valuation M) (m b : M),
      (conjList (((a'.sortVars.map sortVarKey ++ freeOf [] a'.pattern).eraseDups).map
        (guardOf (tableOf a'.sortVars a'.pattern)))).interpret I e m →
      (tr ⟨tableOf a'.sortVars a'.pattern, []⟩ prem).interpret I e b →
      (tr ⟨tableOf a'.sortVars a'.pattern, []⟩ prem').interpret I e b)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a'⟩).pat) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  generalize htg : tableOf a.sortVars a.pattern = tg
  generalize ht : tableOf a'.sortVars a'.pattern = t
  have hvp : ∀ k ∈ varsOf a.pattern, k ∈ varsOf a'.pattern := by
    rw [ha, ha']; intro k hk
    simp only [varsOf, List.mem_append] at hk ⊢
    rcases hk with (hk | hk) | hk
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr (hvars k hk))
    · exact Or.inr hk
  have hsub : ∀ k ∈ tg, k ∈ t := by
    rw [← htg, ← ht]; intro k hk
    unfold tableOf at hk ⊢
    rw [List.mem_eraseDups, List.mem_append] at hk ⊢
    rw [hsv]
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr (hvp k hk)
  have hkt : ∀ k ∈ varsOf a.pattern, k ∈ tg := fun k hk => by
    rw [← htg]; unfold tableOf; exact List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hst : ∀ k ∈ a.sortVars.map sortVarKey, k ∈ tg := fun k hk => by
    rw [← htg]; unfold tableOf; exact List.mem_eraseDups.mpr (List.mem_append_left _ hk)
  have hA : OwiAt (owiF tg t) (owiG tg t) tg t tg := owiAt_table
  have hsort : ∀ (ax : Kore.Axiom), ax.pattern = .implies R prem concl ∨ ax.pattern = .implies R prem' concl →
      sortOf [] ax.pattern = some R := fun ax hax => by rcases hax with hax | hax <;> rw [hax] <;> rfl
  have hR : owiRen (owiF tg t) (owiG tg t) (trSort tg R) = trSort t R := by
    rw [← trSort_owiRen R (hA.sub fun k hk => hkt k (by rw [ha]; simp only [varsOf, List.mem_append]; exact Or.inl (Or.inl hk)))]
  have hP : owiRen (owiF tg t) (owiG tg t) (tr ⟨tg, []⟩ a.pattern) = tr ⟨t, []⟩ a.pattern :=
    (tr_owiRen (c := ⟨tg, []⟩) (c' := ⟨t, []⟩) owiF_top (owiG_inj hsub) rfl a.pattern (hA.sub hkt)).symm
  have hfreeT : ∀ k ∈ (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups, k ∈ tg ∧ ∀ k' ∈ owiKeySorts k, k' ∈ tg := by
    intro k hk
    rw [List.mem_eraseDups, List.mem_append] at hk
    rcases hk with hk | hk
    · refine ⟨hst k hk, fun k' hk' => ?_⟩
      obtain ⟨α, -, rfl⟩ := List.mem_map.mp hk
      exact absurd hk' List.not_mem_nil
    · have hv := owi_freeOf_varsOf _ _ _ hk
      exact ⟨hkt k hv, fun k' hk' => hkt k' (owi_keySorts_varsOf _ k hv k' hk')⟩
  refine sat_of_owiRen (owiF_inj hsub) (owiG_inj hsub) ?_
  intro e m
  change (owiRen (owiF tg t) (owiG tg t) (conjList (((a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups).map
    (guardOf (tableOf a.sortVars a.pattern)))) ⇒ owiRen (owiF tg t) (owiG tg t) (tr ⟨tableOf a.sortVars a.pattern, []⟩ a.pattern ≡
      (match sortOf [] a.pattern with
        | some s => inhOf (trSort (tableOf a.sortVars a.pattern) s)
        | none => sym (.untranslated "sort of the axiom")))).interpret I e m
  rw [hsort a (Or.inl ha), htg]
  simp only
  rw [owiRen_conjList, owiRen_equal, owiRen_inhOf, hR, hP, List.map_map]
  intro hg
  have hgt : ∀ k ∈ (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups, (guardOf t k).interpret I e m :=
    fun k hk => by
      have := conjList_mem hg _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
      rwa [Function.comp_apply, owiRen_guardOf (hfreeT k hk).1 (hfreeT k hk).2] at this
  have hg' : (conjList (((a'.sortVars.map sortVarKey ++ freeOf [] a'.pattern).eraseDups).map (guardOf t))).interpret I e m := by
    refine interp_conjList fun w hw => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
    refine hgt k ?_
    rw [List.mem_eraseDups, List.mem_append] at hk ⊢
    rw [← hsv]
    rcases hk with hk | hk
    · exact Or.inl hk
    · refine Or.inr ?_
      rw [ha'] at hk; rw [ha]
      simp only [freeOf, List.mem_append] at hk ⊢
      rcases hk with hk | hk
      · exact Or.inl (hfree k hk)
      · exact Or.inr hk
  have h0 := h e m
  change (conjList (((a'.sortVars.map sortVarKey ++ freeOf [] a'.pattern).eraseDups).map
      (guardOf (tableOf a'.sortVars a'.pattern))) ⇒ (tr ⟨tableOf a'.sortVars a'.pattern, []⟩ a'.pattern ≡
        (match sortOf [] a'.pattern with
          | some s => inhOf (trSort (tableOf a'.sortVars a'.pattern) s)
          | none => sym (.untranslated "sort of the axiom")))).interpret I e m at h0
  rw [hsort a' (Or.inr ha'), ht] at h0
  have h1 := (interp_equal hD).mp (h0 hg')
  refine (interp_equal hD).mpr fun b => ?_
  have h2 := h1 b
  rw [ha'] at h2; rw [ha]
  simp only [tr, interp_sImp] at h2 ⊢
  exact ⟨fun hb => hb.1, fun hb => ⟨hb, fun hp => (h2.mpr hb).2 (by have := hprem e m b (by rw [ht]; exact hg') (by rw [ht]; exact hp); rwa [ht] at this)⟩⟩

/-- **An axiom with a narrower premise than a valid one is valid**: two axioms over one sort
variable list, `prem → concl` and `prem' → concl` at one sort, where `prem'` holds the variables of
`prem` (free ones free) and, read under any table at any valuation, denotes a part of what `prem`
denotes. Their tables differ (the variables of `prem'` may come first); the valid one is read under
the other's table by a renaming of its variables (`owiRen`), which keeps its validity. -/
theorem owi_sat_narrower (hD : DefOK I) {a a' : Kore.Axiom} (hsv : a'.sortVars = a.sortVars)
    {R : Kore.KSort} {prem prem' concl : Kore.Pattern}
    (ha : a.pattern = .implies R prem concl) (ha' : a'.pattern = .implies R prem' concl)
    (hvars : ∀ k ∈ varsOf prem, k ∈ varsOf prem') (hfree : ∀ k ∈ freeOf [] prem, k ∈ freeOf [] prem')
    (hprem : ∀ (t : VarTable) (e : Valuation M) (b : M),
      (tr ⟨t, []⟩ prem').interpret I e b → (tr ⟨t, []⟩ prem).interpret I e b)
    (h : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a'⟩).pat := by
  generalize htg : tableOf a.sortVars a.pattern = tg
  generalize ht : tableOf a'.sortVars a'.pattern = t
  have hvp : ∀ k ∈ varsOf a.pattern, k ∈ varsOf a'.pattern := by
    rw [ha, ha']; intro k hk
    simp only [varsOf, List.mem_append] at hk ⊢
    rcases hk with (hk | hk) | hk
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr (hvars k hk))
    · exact Or.inr hk
  have hsub : ∀ k ∈ tg, k ∈ t := by
    rw [← htg, ← ht]; intro k hk
    unfold tableOf at hk ⊢
    rw [List.mem_eraseDups, List.mem_append] at hk ⊢
    rw [hsv]
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr (hvp k hk)
  have hkt : ∀ k ∈ varsOf a.pattern, k ∈ tg := fun k hk => by
    rw [← htg]; unfold tableOf; exact List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hst : ∀ k ∈ a.sortVars.map sortVarKey, k ∈ tg := fun k hk => by
    rw [← htg]; unfold tableOf; exact List.mem_eraseDups.mpr (List.mem_append_left _ hk)
  have hA : OwiAt (owiF tg t) (owiG tg t) tg t tg := owiAt_table
  have hren := sat_owiRen (owiF_inj hsub) (owiG_inj hsub) h
  have hsort : ∀ (ax : Kore.Axiom), ax.pattern = .implies R prem concl ∨ ax.pattern = .implies R prem' concl →
      sortOf [] ax.pattern = some R := fun ax hax => by rcases hax with hax | hax <;> rw [hax] <;> rfl
  -- the valid item, read under `t`
  have hR : owiRen (owiF tg t) (owiG tg t) (trSort tg R) = trSort t R := by
    rw [← trSort_owiRen R (hA.sub fun k hk => hkt k (by rw [ha]; simp only [varsOf, List.mem_append]; exact Or.inl (Or.inl hk)))]
  have hP : owiRen (owiF tg t) (owiG tg t) (tr ⟨tg, []⟩ a.pattern) = tr ⟨t, []⟩ a.pattern :=
    (tr_owiRen (c := ⟨tg, []⟩) (c' := ⟨t, []⟩) owiF_top (owiG_inj hsub) rfl a.pattern (hA.sub hkt)).symm
  have hfreeT : ∀ k ∈ (a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups, k ∈ tg ∧ ∀ k' ∈ owiKeySorts k, k' ∈ tg := by
    intro k hk
    rw [List.mem_eraseDups, List.mem_append] at hk
    rcases hk with hk | hk
    · refine ⟨hst k hk, fun k' hk' => ?_⟩
      obtain ⟨α, -, rfl⟩ := List.mem_map.mp hk
      exact absurd hk' List.not_mem_nil
    · have hv := owi_freeOf_varsOf _ _ _ hk
      exact ⟨hkt k hv, fun k' hk' => hkt k' (owi_keySorts_varsOf _ k hv k' hk')⟩
  have hG : ∀ (e : Valuation M) (m : M),
      (conjList (((a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups).map (guardOf t))).interpret I e m →
      (tr ⟨t, []⟩ a.pattern ≡ inhOf (trSort t R)).interpret I e m := by
    intro e m hg
    have := hren e m
    change (owiRen (owiF tg t) (owiG tg t) (conjList (((a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups).map
      (guardOf (tableOf a.sortVars a.pattern)))) ⇒ owiRen (owiF tg t) (owiG tg t) (tr ⟨tableOf a.sortVars a.pattern, []⟩ a.pattern ≡
        (match sortOf [] a.pattern with
          | some s => inhOf (trSort (tableOf a.sortVars a.pattern) s)
          | none => sym (.untranslated "sort of the axiom")))).interpret I e m at this
    rw [hsort a (Or.inl ha), htg] at this
    simp only at this
    rw [owiRen_conjList, owiRen_equal, owiRen_inhOf, hR, hP, List.map_map] at this
    refine this ?_
    refine interp_conjList fun w hw => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
    rw [Function.comp_apply, owiRen_guardOf (hfreeT k hk).1 (hfreeT k hk).2]
    exact conjList_mem hg _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  intro e m
  change (conjList (((a'.sortVars.map sortVarKey ++ freeOf [] a'.pattern).eraseDups).map
      (guardOf (tableOf a'.sortVars a'.pattern))) ⇒ (tr ⟨tableOf a'.sortVars a'.pattern, []⟩ a'.pattern ≡
        (match sortOf [] a'.pattern with
          | some s => inhOf (trSort (tableOf a'.sortVars a'.pattern) s)
          | none => sym (.untranslated "sort of the axiom")))).interpret I e m
  rw [hsort a' (Or.inr ha'), ht]
  intro hg'
  have hg : (conjList (((a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups).map (guardOf t))).interpret I e m := by
    refine interp_conjList fun w hw => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
    refine conjList_mem hg' _ (List.mem_map.mpr ⟨k, ?_, rfl⟩)
    rw [List.mem_eraseDups, List.mem_append] at hk ⊢
    rw [hsv]
    rcases hk with hk | hk
    · exact Or.inl hk
    · refine Or.inr ?_
      rw [ha] at hk; rw [ha']
      simp only [freeOf, List.mem_append] at hk ⊢
      rcases hk with hk | hk
      · exact Or.inl (hfree k hk)
      · exact Or.inr hk
  have h1 := (interp_equal hD).mp (hG e m hg)
  refine (interp_equal hD).mpr fun b => ?_
  have h2 := h1 b
  rw [ha] at h2; rw [ha']
  simp only [tr, interp_sImp] at h2 ⊢
  exact ⟨fun hb => hb.1, fun hb => ⟨hb, fun hp => (h2.mpr hb).2 (hprem t e b hp)⟩⟩

end

section
open KoreAML
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

theorem owi_varsOf_anyOf {k : VarKey} : ∀ {xs : List Kore.Pattern},
    k ∈ varsOf (anyOf xs) ↔ k ∈ sortVarsOf R ∨ ∃ x ∈ xs, k ∈ varsOf x
  | [] => by simp [anyOf, varsOf]
  | x :: xs => by
    have ih := owi_varsOf_anyOf (k := k) (xs := xs)
    simp only [anyOf, varsOf, varsOfList, List.append_nil, List.mem_append, List.mem_cons, exists_eq_or_imp] at ih ⊢
    rw [ih]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

theorem owi_freeOf_anyOf {b : List VarKey} {k : VarKey} : ∀ {xs : List Kore.Pattern},
    k ∈ freeOf b (anyOf xs) ↔ ∃ x ∈ xs, k ∈ freeOf b x
  | [] => by simp [anyOf, freeOf]
  | x :: xs => by
    have ih := owi_freeOf_anyOf (b := b) (k := k) (xs := xs)
    simp only [anyOf, freeOf, freeOfList, List.append_nil, List.mem_append, List.mem_cons, exists_eq_or_imp] at ih ⊢
    rw [ih]

theorem owi_anyOf_iff (hD : DefOK I) {t : VarTable} {e : Valuation M} {b : M} : ∀ {xs : List Kore.Pattern},
    (tr ⟨t, []⟩ (anyOf xs)).interpret I e b ↔
      (inhOf (trSort t R)).interpret I e b ∧ ∃ x ∈ xs, (tr ⟨t, []⟩ x).interpret I e b
  | [] => by
    simp only [anyOf, tr]
    unfold sBot
    rw [interp_sNot, interp_sTop hD isFree_R]
    simp
  | x :: xs => by
    simp only [anyOf, tr, trOrList]
    rw [interp_sOr, owi_anyOf_iff hD (xs := xs)]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ⟨hR, h | ⟨-, h⟩⟩
      · exact ⟨hR, Or.inl h⟩
      · exact ⟨hR, Or.inr h⟩
    · rintro ⟨hR, h | h⟩
      · exact ⟨hR, Or.inl h⟩
      · exact ⟨hR, Or.inr ⟨hR, h⟩⟩

/-- **A premise that negates more disjuncts is narrower**: under any table, where `¬ ⋁ ys ∧ P` holds
and every disjunct of `xs` is one of `ys`, `¬ ⋁ xs ∧ P` holds. -/
theorem owi_negAnyOf_narrower (hD : DefOK I) {xs ys : List Kore.Pattern} (hsub : ∀ x ∈ xs, x ∈ ys)
    {P0 : Kore.Pattern} (t : VarTable) (e : Valuation M) (b : M) :
    (tr ⟨t, []⟩ (.and R [.not R (anyOf ys), P0])).interpret I e b →
      (tr ⟨t, []⟩ (.and R [.not R (anyOf xs), P0])).interpret I e b := by
  simp only [tr, trAndList]
  rw [interp_sAnd, interp_sAnd, interp_sNot, interp_sNot, owi_anyOf_iff hD, owi_anyOf_iff hD]
  rintro ⟨⟨hn, hR⟩, hp⟩
  exact ⟨⟨fun ⟨hR', x, hx, hb⟩ => hn ⟨hR', x, hsub x hx, hb⟩, hR⟩, hp⟩

/-- **The equation of a function with a narrower premise holds where the equation holds**: the
equation `eqnSentence c fn prem rhs ens` valid, `prem'` holding the variables of `prem` (free ones
free) and, under every table, a part of it: the equation with `prem'` is valid. -/
theorem owi_eqn_narrower (hD : DefOK I) {fn : Fn} {prem prem' rhs ens : Kore.Pattern}
    (hvars : ∀ k ∈ varsOf prem, k ∈ varsOf prem') (hfree : ∀ k ∈ freeOf [] prem, k ∈ freeOf [] prem')
    (hprem : ∀ (t : VarTable) (e : Valuation M) (b : M),
      (tr ⟨t, []⟩ prem').interpret I e b → (tr ⟨t, []⟩ prem).interpret I e b)
    (h : ∀ it ∈ kernelItems [eqnSentence c fn prem rhs ens], I ⊧ᴵ it.pat) :
    ∀ it ∈ kernelItems [eqnSentence c fn prem' rhs ens], I ⊧ᴵ it.pat := by
  intro it hit
  simp only [kernelItems, eqnSentence, equationAx, axiomR, List.filterMap_cons, List.filterMap_nil,
    List.mem_singleton] at hit h
  subst hit
  exact owi_sat_narrower (a := ⟨[Rv], .implies R prem _, []⟩) hD rfl rfl rfl hvars hfree hprem (h _ rfl)

/-- Each item of a clause's equation is a premise of `Γ`. -/
theorem owi_prio_items {fn : Fn} {cl : Clause} (hfn : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses) :
    ∀ it ∈ kernelItems [prioEquation c fn cl], Γ c it.pat := by
  intro it hit
  refine Or.inl (Or.inl (Or.inr (Or.inl ⟨it, ?_, rfl⟩)))
  unfold fnItems
  refine List.mem_flatMap.mpr ⟨fn, hfn, ?_⟩
  unfold kernelItems at hit ⊢
  obtain ⟨s, hs, hs'⟩ := List.mem_filterMap.mp hit
  rw [List.mem_singleton] at hs
  subst hs
  exact List.mem_filterMap.mpr ⟨_, List.mem_map.mpr ⟨cl, hcl, rfl⟩, hs'⟩

end

/-- A clause's equation with the disjuncts `ds` negated in place of the exclusions of the clauses
before it: `¬ ⋁ ds ∧ ⌈req = true⌉ ∧ X̄ ∈ p̄ → f(X̄) = rhs ∧ ens`, the premise `competingPremise`
writes. With the exclusions of `lowerClauses` as `ds` it is the clause's competing equation
(`competingEquation_top`). -/
def owiseWith (c : Semantics) (fn : Fn) (ds : List Kore.Pattern) (cl : Clause) : Kore.Sentence :=
  eqnSentence c fn
    (competingPremise (fn.args.map c.sortName) ds (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats))
    (Term.kore c (canonVars c cl.vars) cl.rhs)
    (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))

/-- **A clause's equation under the negation of more disjuncts is entailed**: for a clause of a
function, without a predicate or existential variables, and disjuncts `ds` among which are the
exclusions of the clauses before it, `Γ` entails the equation that applies where none of `ds` holds
(`owiseWith`). Where `ds` is just those exclusions it is `Γ`'s item; each further disjunct only
narrows the premise. -/
theorem owiseWith_entailed {c : Semantics} {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hpre : cl.pre = .top) (hex : cl.exs = []) {ds : List Kore.Pattern}
    (hds : ∀ cl' ∈ lowerClauses fn cl, exclusion c fn cl' (canonClausePres cl') ∈ ds) :
    ∀ it ∈ kernelItems [owiseWith c fn ds cl], Γ c ⊧ it.pat := by
  intro it hit M _ I hI
  have hD := defOK hI
  have hΓ : ∀ it' ∈ kernelItems [prioEquation c fn cl], I ⊧ᴵ it'.pat := fun it' h => hI _ (owi_prio_items hfn hcl it' h)
  unfold prioEquation at hΓ
  split at hΓ
  · rw [clauseEquation_top hpre hex] at hΓ
    refine owi_eqn_narrower hD ?_ ?_ ?_ hΓ it hit
    · intro k hk
      simp only [competingPremise, KoreAML.varsOf, KoreAML.varsOfList, List.mem_append, List.append_nil]
      exact Or.inr (Or.inr hk)
    · intro k hk
      simp only [competingPremise, KoreAML.freeOf, KoreAML.freeOfList, List.mem_append, List.append_nil]
      exact Or.inr hk
    · intro t e b hb
      simp only [competingPremise, KoreAML.tr, KoreAML.trAndList] at hb
      exact (KoreAML.interp_sAnd.mp hb).2
  · rw [competingEquation_top hpre hex] at hΓ
    have hsub : ∀ x ∈ (lowerClauses fn cl).map (fun cl' => exclusion c fn cl' (canonClausePres cl')), x ∈ ds :=
      fun x hx => by obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hx; exact hds cl' hcl'
    refine owi_eqn_narrower hD ?_ ?_ (fun t e b => owi_negAnyOf_narrower hD hsub t e b) hΓ it hit
    · intro k hk
      simp only [KoreAML.varsOf, KoreAML.varsOfList, List.mem_append, List.append_nil] at hk ⊢
      rcases hk with hk | (hk | hk) | hk
      · exact Or.inl hk
      · exact Or.inr (Or.inl (Or.inl hk))
      · rw [owi_varsOf_anyOf] at hk ⊢
        rcases hk with hk | ⟨x, hx, hk⟩
        · exact Or.inr (Or.inl (Or.inr (Or.inl hk)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨x, hsub x hx, hk⟩)))
      · exact Or.inr (Or.inr hk)
    · intro k hk
      simp only [KoreAML.freeOf, KoreAML.freeOfList, List.mem_append, List.append_nil] at hk ⊢
      rcases hk with hk | hk
      · rw [owi_freeOf_anyOf] at hk ⊢
        obtain ⟨x, hx, hk⟩ := hk
        exact Or.inl ⟨x, hsub x hx, hk⟩
      · exact Or.inr hk

/-- The generated sort predicates' clauses have `\top` predicates. -/
theorem owi_sortPreds_pre {c : Semantics} {fn : Fn} (hfn : fn ∈ c.sortPreds) : ∀ cl ∈ fn.clauses, cl.pre = .top := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  · subst hcl; rfl
  · rcases hcl with rfl | rfl <;> rfl
  · rcases hcl with rfl | rfl <;> rfl

/-- **A sort predicate's `[owise]` equation whose exclusion also names instances of its clauses is
entailed** (`Parse.predOwiseInstOK`): its exclusion is `ds`; without the disjuncts of the instances
(`predInstDrop`) it is, read as `predEqnOK` reads it (`clause?` without an exclusion), a clause `ow`
of the predicate (`clauseSame`), with one disjunct for each clause before `ow`. Its premise negates
the instances' disjuncts beside those: for every list of disjuncts that holds the exclusions of the
clauses before `ow` (`exclusion` under the canonical presentation, as `Γ` writes them), `Γ`
entails `ow`'s equation under their negation (`owiseWith_entailed`). The instances need no fact:
negating more disjuncts only narrows the premise. -/
theorem predOwiseInst_entailed {c : Semantics} {N : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn}
    {e : Parse.RawEqn} {fn : Fn} (hfn : fn ∈ c.sortPreds) (h : Parse.predOwiseInstOK N msrc eqs c fn e = true) :
    ∃ ds ds', e.competitors = some ds ∧
      Parse.predInstDrop (eqs.filter fun e' => e'.fn == e.fn && Parse.predInstOK N msrc c e' &&
        !Parse.predEqnOK N msrc eqs fn e') ds = some ds' ∧
      ∃ cl cp ow, Parse.clause? N msrc { e with competitors := some ds' } none = .ok (cl, cp) ∧
        ow ∈ fn.clauses ∧ Parse.clauseSame cl ow = true ∧
        ∀ ds₀ : List Kore.Pattern, (∀ cl' ∈ lowerClauses fn ow, exclusion c fn cl' (canonClausePres cl') ∈ ds₀) →
          ∀ it ∈ kernelItems [owiseWith c fn ds₀ ow], Γ c ⊧ it.pat := by
  unfold Parse.predOwiseInstOK at h
  cases hc : e.competitors with
  | none => rw [hc] at h; cases h
  | some ds =>
    rw [hc] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split at h
    · rename_i ds' hd
      refine ⟨ds, ds', rfl, hd, ?_⟩
      unfold Parse.predEqnOK at h
      dsimp only at h
      generalize hq : Parse.clause? N msrc { e with competitors := some ds' } none = q at h
      by_cases hcond : (e.req.isNone && e.ens.isNone && !e.dom) = true
      · simp only [hcond, ↓reduceIte] at h
        cases q with
        | error _ => simp [Except.toOption] at h
        | ok r =>
          obtain ⟨cl', cp⟩ := r
          simp only [Except.toOption, Option.map_some, Bool.and_eq_true, List.any_eq_true] at h
          obtain ⟨⟨ow, how, hsame⟩, -⟩ := h
          exact ⟨cl', cp, ow, rfl, how, hsame, fun ds₀ hds₀ =>
            owiseWith_entailed (List.mem_append_right _ hfn) how (owi_sortPreds_pre hfn ow how)
              (Semantics.sortPreds_exs hfn ow how) hds₀⟩
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    · cases h

end GenEqs
end KCore
