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
end GenEqs
end KCore
