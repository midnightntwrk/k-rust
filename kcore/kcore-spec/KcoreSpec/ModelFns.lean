/-
  KCore. The reading of a function's equation in the value model (`sat_eqn`, `premise_iff`,
  `eval_of_decides`; the equations themselves, `SatFnsGoal`, in ModelFnsCl.lean), and what the
  interpretation decides where the text is silent (`SatFallbackGoal`), a function's rest among it.

  A function `f` is interpreted by `Eval`: `f(w̄)` is the values `v` with `Eval c f w̄ (some v)`.
  An equation `premise → f(X̄) = rhs` is read at a valuation giving `X̄` values `w̄` of `f`'s
  argument sorts and each variable a value of its sort, read as σ: where its premise holds, the
  clause decides at `w̄` (`Clause.DecidesAt`): it applies under σ (its patterns match, its
  `requires` evaluates to `true`) and no clause of a smaller priority applies at `w̄` under any
  substitution (vacuously where there is none; the negated exclusions otherwise, `exclusion_iffCl`).
  There the values of `f` are those of `rhs` under σ (`eval_of_decides`): `FnSolves` for a function
  of the definition, and for a sort predicate the same by `solves_of_parts` (its clauses have no
  `requires` and a literal as right-hand side). No result of a clause that does not apply is read.
  Where every clause fails at values `w̄` of its argument sorts, `Eval` gives `f` its rest
  (`Eval.rest`), the only result there (`FnDet`), so `f(w̄)` is the rest's graph.
-/
import KcoreSpec.ModelStep

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

theorem HypModelCore.fnApart (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) :
    c.isCtor fn.label = false ∧ isHook fn.label = false ∧ c.isParam fn.label = false := by
  have := List.all_eq_true.mp h.fns fn hfn
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem HypModelCore.fnSorts (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) :
    ∀ s ∈ fn.result :: fn.args, s < nRegSorts + c.sortNames.length := h.hyp.2.2.1.2.2 fn hfn

/-! ## The sort variable, the arguments and the call -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem R_read {tbl : KoreAML.VarTable} (e : Valuation Elem) (a : Elem) :
    (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = e.evalEvar (tbl.ev (.sortVar "R")) := by
  rw [trSort_R, KoreAML.interp_evar]

end AtT

theorem R_read {tbl : KoreAML.VarTable} (e : Valuation Elem) (a : Elem) :
    (KoreAML.trSort tbl KoreAML.R).interpret (stdI c) e a ↔ a = e.evalEvar (tbl.ev (.sortVar "R")) :=
  AtT.R_read (c := c) (T := StepM c) (tbl := tbl) (e := e) (a := a)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem vars_numbered_read {tbl : KoreAML.VarTable} {e : Valuation Elem} :
    ∀ (ss : List String) (ws : List GroundTerm) (j : Nat), ss.length = ws.length →
    (∀ (n : Nat) (w : GroundTerm) (s : String), ws[n]? = some w → ss[n]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))) = .val w) →
    All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
      ((KoreAML.vars (KoreAML.numbered "X" j ss)).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map Elem.val)
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | s :: ss, w :: ws, j, hl, hX => by
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    refine .cons (fun m => ?_) ?_
    · rw [KoreAML.tr, KoreAML.interp_evar]
      have := hX 0 w s rfl rfl
      rw [Nat.add_zero] at this
      exact Iff.of_eq (congrArg (m = ·) this)
    · have := vars_numbered_read ss ws (j + 1) (by simpa using hl)
        (fun n w' s' h1 h2 => by
          have := hX (n + 1) w' s' (by simpa using h1) (by simpa using h2)
          rwa [show j + (n + 1) = j + 1 + n by omega] at this)
      simpa [KoreAML.vars] using this

end AtT

theorem vars_numbered_read {tbl : KoreAML.VarTable} {e : Valuation Elem} :
    ∀ (ss : List String) (ws : List GroundTerm) (j : Nat), ss.length = ws.length →
    (∀ (n : Nat) (w : GroundTerm) (s : String), ws[n]? = some w → ss[n]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))) = .val w) →
    All2 (fun φ x => ∀ m, φ.interpret (stdI c) e m ↔ m = x)
      ((KoreAML.vars (KoreAML.numbered "X" j ss)).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map Elem.val) :=
  AtT.vars_numbered_read (c := c) (T := StepM c) (tbl := tbl) (e := e)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The call `f(X̄)`**, at a valuation giving `X̄` the arguments' values: the values `Eval`
gives. -/
theorem call_read (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {tbl : KoreAML.VarTable} {e : Valuation Elem}
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hX : ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = .val w) (b : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret (stdI_T c T) e b ↔
      ∃ v, b = .val v ∧ Eval c fn.label ws (some v) := by
  obtain ⟨hc, hh, hp⟩ := h.fnApart hfn
  have hl : ws.length = fn.args.length := sortsOf_len hws
  rw [tr_ap_tbl, interp_symList _ _ (ws.map Elem.val)
    (vars_numbered_read _ ws 0 (by simp [hl]) (fun n w s h1 h2 => by rw [Nat.zero_add]; exact hX n w s h1 h2)) b]
  rw [show c.symName fn.label = c.symName fn.sig.name from rfl,
    symE_vals h.namesK (fn_sig_mem hfn) (by rw [hl]; rfl) b]
  exact result_fn (k := fn.sig) hc hh hp (c.isOvl_of_lookupFn (h.lookupFn hfn)) b

end AtT

/-- **The call `f(X̄)`**, at a valuation giving `X̄` the arguments' values: the values `Eval`
gives. -/
theorem call_read (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {tbl : KoreAML.VarTable} {e : Valuation Elem}
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hX : ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = .val w) (b : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret (stdI c) e b ↔
      ∃ v, b = .val v ∧ Eval c fn.label ws (some v) :=
  AtT.call_read (c := c) (T := StepM c) (h := h) (fn := fn) (hfn := hfn) (tbl := tbl) (e := e) (ws := ws) (hws := hws) (hX := hX) (b := b)

/-! ## Disjunctions -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem anyOfC_iff {tbl : KoreAML.VarTable} {S : Kore.KSort} {e : Valuation Elem} {σS : Elem}
    (hS : ∀ a, (KoreAML.trSort tbl S).interpret (stdI_T c T) e a ↔ a = σS)
    (hfree : (KoreAML.trSort tbl S).isFreeEvar KoreAML.topVar = false) :
    ∀ (cs : List Kore.Pattern) (a : Elem), (KoreAML.tr ⟨tbl, []⟩ (anyOfC S cs)).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σS a ∧ ∃ φ ∈ cs, (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI_T c T) e a
  | [], a => by
    rw [anyOfC, KoreAML.tr]
    unfold KoreAML.sBot
    rw [KoreAML.interp_sNot, KoreAML.interp_sTop defOK_std hfree]
    simp
  | φ :: cs, a => by
    rw [anyOfC, KoreAML.tr]
    simp only [KoreAML.trOrList]
    rw [KoreAML.interp_sOr, anyOfC_iff hS hfree cs a, KoreAML.interp_inhOf_of hS]
    constructor
    · rintro ⟨hi, hφ | ⟨-, ψ, hψ, hψa⟩⟩
      · exact ⟨hi, φ, List.mem_cons_self .., hφ⟩
      · exact ⟨hi, ψ, List.mem_cons_of_mem _ hψ, hψa⟩
    · rintro ⟨hi, ψ, hψ, hψa⟩
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact ⟨hi, Or.inl hψa⟩
      · exact ⟨hi, Or.inr ⟨hi, ψ, hψ, hψa⟩⟩

end AtT

theorem anyOfC_iff {tbl : KoreAML.VarTable} {S : Kore.KSort} {e : Valuation Elem} {σS : Elem}
    (hS : ∀ a, (KoreAML.trSort tbl S).interpret (stdI c) e a ↔ a = σS)
    (hfree : (KoreAML.trSort tbl S).isFreeEvar KoreAML.topVar = false) :
    ∀ (cs : List Kore.Pattern) (a : Elem), (KoreAML.tr ⟨tbl, []⟩ (anyOfC S cs)).interpret (stdI c) e a ↔
      KoreAML.Inh (stdI c) σS a ∧ ∃ φ ∈ cs, (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI c) e a :=
  AtT.anyOfC_iff (c := c) (T := StepM c) (tbl := tbl) (S := S) (e := e) (σS := σS) (hS := hS) (hfree := hfree)

/-! ## The arguments' part of a premise -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem argsConj_iff {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI_T c T) σR) :
    ∀ (j : Nat) (l : List (String × Kore.Pattern)),
    (∀ (n : Nat) (s : String) (p : Kore.Pattern), l[n]? = some (s, p) → ∃ σs, (∀ a, (KoreAML.trSort tbl (KoreAML.srt s)).interpret (stdI_T c T) e a ↔ a = σs) ∧
      KoreAML.IsSort (stdI_T c T) σs ∧
      KoreAML.Inh (stdI_T c T) σs (e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))))) →
    ∀ a, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.argsConj j l)).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ ∀ (n : Nat) (s : String) (p : Kore.Pattern), l[n]? = some (s, p) →
        (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI_T c T) e (e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))))
  | j, [], _, a => by
    simp only [KoreAML.argsConj]
    rw [KoreAML.tr, KoreAML.interp_sTop defOK_std isFree_R, KoreAML.interp_inhOf_of hR]
    simp
  | j, (s, p) :: l, hs, a => by
    simp only [KoreAML.argsConj]
    rw [tr_and2, KoreAML.interp_sAnd, argsConj_iff hR hRs (j + 1) l (fun n s' p' hn => by
      obtain ⟨σs, h1, h2, h3⟩ := hs (n + 1) s' p' (by simpa using hn)
      exact ⟨σs, h1, h2, by rwa [show j + (n + 1) = j + 1 + n by omega] at h3⟩) a]
    obtain ⟨σs, hσs, hσss, hXs⟩ := hs 0 s p rfl
    rw [Nat.add_zero] at hXs
    have hXr : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ev s!"X{j}" (KoreAML.srt s))).interpret (stdI_T c T) e b ↔
        b = e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) := fun b => by
      unfold KoreAML.ev; rw [KoreAML.tr, KoreAML.interp_evar]; rfl
    rw [KoreAML.tr, KoreAML.interp_sIn defOK_std sat_ceilDef hσs hR hσss hRs (fun b hb => by
      rw [(hXr b).mp hb]; exact hXs)]
    have hex : (∃ b, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ev s!"X{j}" (KoreAML.srt s))).interpret (stdI_T c T) e b ∧
        (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI_T c T) e b) ↔
        (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI_T c T) e (e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s)))) :=
      ⟨fun ⟨b, hb, hp⟩ => (hXr b).mp hb ▸ hp, fun hp => ⟨_, (hXr _).mpr rfl, hp⟩⟩
    rw [hex]
    constructor
    · rintro ⟨⟨hp, hi⟩, -, hrest⟩
      refine ⟨hi, fun n s' p' hn => ?_⟩
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        rw [Nat.add_zero]; exact hp
      | succ n =>
        have := hrest n s' p' (by simpa using hn)
        rwa [show j + 1 + n = j + (n + 1) by omega] at this
    · rintro ⟨hi, hall⟩
      refine ⟨⟨?_, hi⟩, hi, fun n s' p' hn => ?_⟩
      · have := hall 0 s p rfl; rwa [Nat.add_zero] at this
      · have := hall (n + 1) s' p' (by simpa using hn)
        rwa [show j + (n + 1) = j + 1 + n by omega] at this

end AtT

theorem argsConj_iff {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI c) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI c) σR) :
    ∀ (j : Nat) (l : List (String × Kore.Pattern)),
    (∀ (n : Nat) (s : String) (p : Kore.Pattern), l[n]? = some (s, p) → ∃ σs, (∀ a, (KoreAML.trSort tbl (KoreAML.srt s)).interpret (stdI c) e a ↔ a = σs) ∧
      KoreAML.IsSort (stdI c) σs ∧
      KoreAML.Inh (stdI c) σs (e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))))) →
    ∀ a, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.argsConj j l)).interpret (stdI c) e a ↔
      KoreAML.Inh (stdI c) σR a ∧ ∀ (n : Nat) (s : String) (p : Kore.Pattern), l[n]? = some (s, p) →
        (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI c) e (e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s)))) :=
  AtT.argsConj_iff (c := c) (T := StepM c) (tbl := tbl) (e := e) (σR := σR) (hR := hR) (hRs := hRs)

theorem patVals_of_get {σ : Subst} : ∀ {ps : List Term} {ws : List GroundTerm}, ps.length = ws.length →
    (∀ (n : Nat) (p : Term) (w : GroundTerm), ps[n]? = some p → ws[n]? = some w → PatVal c σ p w) → PatVals c σ ps ws
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | p :: ps, w :: ws, hl, h => .cons (h 0 p w rfl rfl)
      (patVals_of_get (by simpa using hl) (fun n p' w' h1 h2 => h (n + 1) p' w' (by simpa using h1) (by simpa using h2)))

theorem patVals_get {σ : Subst} : ∀ {ps : List Term} {ws : List GroundTerm}, PatVals c σ ps ws →
    ∀ (n : Nat) (p : Term) (w : GroundTerm), ps[n]? = some p → ws[n]? = some w → PatVal c σ p w
  | _, _, .nil, n, _, _, h1, _ => by simp at h1
  | _, _, .cons hp _, 0, _, _, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1; subst h2; exact hp
  | _, _, .cons _ hs, n + 1, p, w, h1, h2 => patVals_get hs n p w (by simpa using h1) (by simpa using h2)

theorem koreList_eq_map (vs : List KoreAML.Var) : ∀ ps : List Term, Term.koreList c vs ps = ps.map (Term.kore c vs)
  | [] => by rw [Term.koreList]; rfl
  | p :: ps => by rw [Term.koreList, koreList_eq_map vs ps]; rfl

theorem koreList_get {vs : List KoreAML.Var} {ps : List Term} {n : Nat} {p : Term} (h : ps[n]? = some p) :
    (Term.koreList c vs ps)[n]? = some (Term.kore c vs p) := by
  rw [koreList_eq_map, List.getElem?_map, h]; rfl

theorem koreList_get_inv {vs : List KoreAML.Var} {ps : List Term} {n : Nat} {q : Kore.Pattern}
    (h : (Term.koreList c vs ps)[n]? = some q) : ∃ p, ps[n]? = some p ∧ Term.kore c vs p = q := by
  rw [koreList_eq_map, List.getElem?_map] at h
  exact Option.map_eq_some_iff.mp h

/-- The facts a valuation of an equation gives the formal arguments `X̄` and the sort variable. -/
structure ArgsAt (c : Semantics) (tbl : KoreAML.VarTable) (e : Valuation Elem) (args : List Srt)
    (ws : List GroundTerm) : Prop where
  sorts : c.sortsOf ws = some args
  num : ∀ s ∈ args, s < nRegSorts + c.sortNames.length
  X : ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w → (args.map c.sortName)[j]? = some s →
    e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = .val w

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **A premise** `⌈req = true⌉ ∧ X̄ ∈ p̄` holds exactly where the `requires` evaluates to `true`
under σ and the patterns denote the arguments under σ. -/
theorem premise_iff (h : HypModelCore c) {vars args : List Srt} {req : Option Term} {pats : List Term}
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI_T c T) σR)
    {σ : Subst}
    (hvar : ∀ i, i < vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v)
    (hreqOK : ∀ t, req = some t → TermOK c (· < vars.length) t)
    (hpatOK : ∀ p ∈ pats, PatOK c (· < vars.length) p) (hlen : pats.length = args.length)
    {ws : List GroundTerm} (hX : ArgsAt c tbl e args ws) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ (∀ t, req = some t → EvalTerm c σ t (some (bool true))) ∧ PatVals c σ pats ws := by
  have hn := h.namesK
  have hwl : ws.length = args.length := sortsOf_len hX.sorts
  unfold premise
  rw [tr_and2, KoreAML.interp_sAnd]
  have hreq : (KoreAML.tr ⟨tbl, []⟩ (reqPat KoreAML.R (req.map (Term.kore c (canonVars c vars))))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ ∀ t, req = some t → EvalTerm c σ t (some (bool true)) := by
    cases hq : req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop defOK_std isFree_R, KoreAML.interp_inhOf_of hR]
      simp
    | some t =>
      simp only [Option.map_some]
      rw [reqPat_iff h hvar (hreqOK t hq) hR hRs]
      simp
  rw [hreq, argsConj_iff hR hRs 0 _ (fun n s p hn' => ?_)]
  · constructor
    · rintro ⟨⟨hi, hq⟩, -, hall⟩
      refine ⟨hi, hq, patVals_of_get (by rw [hlen, hwl]) fun n p w hp hw => ?_⟩
      have hlt : n < args.length := by rw [← hwl]; exact (List.getElem?_eq_some_iff.mp hw).1
      have hs : (args.map c.sortName)[n]? = some (c.sortName (args[n]'hlt)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
      have hl : ((args.map c.sortName).zip (Term.koreList c (canonVars c vars) pats))[n]? =
          some (c.sortName (args[n]'hlt), Term.kore c (canonVars c vars) p) := by
        rw [List.getElem?_zip_eq_some]
        refine ⟨hs, ?_⟩
        rw [koreList_get hp]
      have := hall n _ _ hl
      rw [Nat.zero_add, hX.X n w _ hw hs] at this
      obtain ⟨v, hv, he⟩ := (tr_pat h hvar (hpatOK p (List.mem_of_getElem? hp)) _).mp this
      cases he
      exact hv
    · rintro ⟨hi, hq, hpv⟩
      refine ⟨⟨hi, hq⟩, hi, fun n s p hl => ?_⟩
      obtain ⟨hs, hp⟩ := List.getElem?_zip_eq_some.mp hl
      obtain ⟨p0, hp0, rfl⟩ := koreList_get_inv (c := c) hp
      rw [List.getElem?_map] at hs
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨w, hw, -⟩ := sortsOf_get hX.sorts ha0
      rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl)]
      exact (tr_pat h hvar (hpatOK p0 (List.mem_of_getElem? hp0)) _).mpr ⟨w, patVals_get hpv n p0 w hp0 hw, rfl⟩
  · obtain ⟨hs, -⟩ := List.getElem?_zip_eq_some.mp hn'
    rw [List.getElem?_map] at hs
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hnum := hX.num a0 (List.mem_of_getElem? ha0)
    obtain ⟨w, hw, hsw⟩ := sortsOf_get hX.sorts ha0
    refine ⟨.srt a0, fun b => by rw [trSort_srt]; exact sort_den hn hnum e b,
      (isSort_iff _).mpr ⟨a0, List.mem_range.mpr hnum, rfl⟩, ?_⟩
    rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl), inh_srt]
    exact hsw

end AtT

/-- **A premise** `⌈req = true⌉ ∧ X̄ ∈ p̄` holds exactly where the `requires` evaluates to `true`
under σ and the patterns denote the arguments under σ. -/
theorem premise_iff (h : HypModelCore c) {vars args : List Srt} {req : Option Term} {pats : List Term}
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI c) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI c) σR)
    {σ : Subst}
    (hvar : ∀ i, i < vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI c) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v)
    (hreqOK : ∀ t, req = some t → TermOK c (· < vars.length) t)
    (hpatOK : ∀ p ∈ pats, PatOK c (· < vars.length) p) (hlen : pats.length = args.length)
    {ws : List GroundTerm} (hX : ArgsAt c tbl e args ws) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats))).interpret (stdI c) e a ↔
      KoreAML.Inh (stdI c) σR a ∧ (∀ t, req = some t → EvalTerm c σ t (some (bool true))) ∧ PatVals c σ pats ws :=
  AtT.premise_iff (c := c) (T := StepM c) (h := h) (vars := vars) (args := args) (req := req) (pats := pats) (tbl := tbl) (e := e) (σR := σR) (hR := hR) (hRs := hRs) (σ := σ) (hvar := hvar) (hreqOK := hreqOK) (hpatOK := hpatOK) (hlen := hlen) (ws := ws) (hX := hX) (a := a)

/-! ## A clause that fails -/

theorem canonKey_ne_X' {vars : List Srt} {i : Nat} (hi : i < vars.length) (n : String) (s : Kore.KSort) :
    KoreAML.VarKey.evar ("X" ++ n) s ≠ canonKey c vars i := by
  rw [canonKey_eq c hi]
  intro he
  injection he with he
  exact x_ne_var he

theorem reqFails_of_true {σ : Subst} {cl : Clause} (hmi : FnDet c)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) (hf : ReqFails c σ cl) : False := by
  cases hf with
  | intro ht he hr => exact hr (EvalTerm.functional_of_fnDet hmi he (hreq _ ht))
  | pre hf => exact absurd (Holds.functional_of_fnDet hmi hpre hf) (by simp)

/-! ## What `Eval` gives where a clause applies -/

theorem eval_iff_of {f : Sym} {ws : List GroundTerm} {r1 : Option GroundTerm} (hmi : FnDet c)
    (h1 : Eval c f ws r1) (r : Option GroundTerm) : Eval c f ws r ↔ r = r1 :=
  ⟨fun h2 => hmi _ _ _ _ h2 h1, fun he => he ▸ h1⟩

theorem evalTerm_iff_of {σ : Subst} {t : Term} {r1 : Option GroundTerm} (hmi : FnDet c)
    (h1 : EvalTerm c σ t r1) (r : Option GroundTerm) : EvalTerm c σ t r ↔ r = r1 :=
  ⟨fun h2 => EvalTerm.functional_of_fnDet hmi h2 h1, fun he => he ▸ h1⟩

theorem fails_false {ws : List GroundTerm} {cl : Clause} {σ : Subst} (hmi : FnDet c)
    (hσ : c.WellSorted cl.vars σ) (hpv : PatVals c σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) (hf : Fails c ws cl) : False := by
  cases hf with
  | intro hf => exact reqFails_of_true hmi hreq hpre (hf σ (hσ.at _) hpv)

/-- **A clause that decides gives the function's values**: where it applies under σ and no
clause of a smaller priority applies, the values of the function are those of its right-hand side
under σ. For a function of the definition this is `FnSolves`, its clauses having no existential
variable and the right side's predicate `\top`; a sort predicate's clauses have no
`requires` and a literal as right-hand side, so `solves_of_parts`' conditions hold of it. -/
theorem eval_of_decides (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args) {σ : Subst} (hdec : cl.DecidesAt c fn σ ws) :
    ∀ v, Eval c fn.label ws (some v) ↔
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) := by
  rcases List.mem_append.mp hfn with hu | hp
  · intro v
    have hpl := Semantics.clausePlainOpen_parts ((Semantics.sortedOKCl_parts h.hyp.1).2.1 fn hu cl hcl).2
    exact (h.solves fn hu ws hws cl hcl σ hdec v).trans (Clause.gives_iff_noExs hpl.1 hpl.2.2.1 hdec.1.1 v)
  · have hsh := sortPreds_shape hp
    exact solves_of_parts (h.lookupFn hfn) h.det
      (fun cl' hcl' => ⟨Semantics.sortPreds_exs hp cl' hcl', Semantics.sortPreds_post hp cl' hcl'⟩)
      (fun _ _ _ _ cl' hcl' _ _ σ' _ _ => ⟨(fun t ht => by rw [(hsh cl' hcl').1] at ht; cases ht), true,
        Clause.holds_preTop (Semantics.sortPreds_pre hp cl' hcl') σ'⟩)
      (fun _ _ cl' _ _ hcl' _ _ _ => by
        obtain ⟨_, s, l, he⟩ := hsh cl' hcl'
        refine ⟨some (.dv s l), .inl ⟨fun t ht => (by rw [sortPreds_ens hp cl' hcl'] at ht; cases ht), ?_⟩⟩
        rw [he]; exact .dv)
      hcl hdec

/-! ## The variables of an equation -/

theorem X_mem_call : ∀ (ss : List String) (j n : Nat) (s : String), ss[n]? = some s →
    KoreAML.VarKey.evar ("X" ++ toString (j + n)) (KoreAML.srt s) ∈
      KoreAML.freeOfList [] (KoreAML.vars (KoreAML.numbered "X" j ss))
  | [], _, _, _, h => by simp at h
  | s' :: ss, j, 0, s, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.freeOfList, KoreAML.freeOf]
    simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  | s' :: ss, j, n + 1, s, h => by
    simp only [List.getElem?_cons_succ] at h
    have := X_mem_call ss (j + 1) n s h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.freeOfList]
    rw [show j + (n + 1) = j + 1 + n by omega]
    exact List.mem_append_right _ (by simpa [KoreAML.vars] using this)

theorem freeOf_argsConj_mem : ∀ (l : List (String × Kore.Pattern)) (j : Nat) {q : String × Kore.Pattern}
    {k : KoreAML.VarKey}, q ∈ l → k ∈ KoreAML.freeOf [] q.2 → k ∈ KoreAML.freeOf [] (KoreAML.argsConj j l)
  | [], _, _, _, h, _ => absurd h List.not_mem_nil
  | (s, p) :: l, j, q, k, h, hk => by
    simp only [KoreAML.argsConj]
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (Or.inr hk)
    · exact Or.inr (freeOf_argsConj_mem l (j + 1) h hk)

theorem varOccsList_mem : ∀ {ts : List Term} {i : Nat}, i ∈ varOccsList ts → ∃ (n : Nat) (t : Term), ts[n]? = some t ∧ i ∈ varOccs t
  | [], _, h => by rw [varOccsList] at h; cases h
  | t :: ts, i, h => by
    rw [varOccsList] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨0, t, rfl, h⟩
    · obtain ⟨n, t', h1, h2⟩ := varOccsList_mem h
      exact ⟨n + 1, t', by simpa using h1, h2⟩

/-- A variable of a premise's patterns is free in the premise. -/
theorem freeOf_premise_var {args : List Srt} {req : Option Kore.Pattern} {pats : List Term} {vars : List Srt}
    (hlen : pats.length = args.length) {i : Nat} (hi : i ∈ varOccsList pats) :
    canonKey c vars i ∈ KoreAML.freeOf [] (premise (args.map c.sortName) req (Term.koreList c (canonVars c vars) pats)) := by
  obtain ⟨n, t, ht, hit⟩ := varOccsList_mem hi
  have hlt : n < args.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp ht).1
  have hq : (c.sortName (args[n]'hlt), Term.kore c (canonVars c vars) t) ∈
      (args.map c.sortName).zip (Term.koreList c (canonVars c vars) pats) := by
    refine List.mem_iff_getElem?.mpr ⟨n, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl, koreList_get ht⟩
  unfold premise
  simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append]
  exact Or.inr (freeOf_argsConj_mem _ 0 hq (kore_freeOf c _ t hit))

/-! ## An equation -/

theorem argsAt_of {tbl : KoreAML.VarTable} {e : Valuation Elem} {args : List Srt}
    (hnum : ∀ s ∈ args, s < nRegSorts + c.sortNames.length)
    (hin : ∀ (j : Nat) (hj : j < args.length),
      InSort c (args[j]'hj) (e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName (args[j]'hj))))))) :
    ∃ ws, ArgsAt c tbl e args ws := by
  let ws := (List.range args.length).map fun j => toVal (e.evalEvar (tbl.ev (.evar ("X" ++ toString j)
    (KoreAML.srt (c.sortName (args.getD j 0))))))
  have hget : ∀ j (hj : j < args.length), ws[j]? = some (toVal (e.evalEvar (tbl.ev (.evar ("X" ++ toString j)
      (KoreAML.srt (c.sortName (args[j]'hj))))))) := fun j hj => by
    simp [ws, List.getElem?_map, List.getElem?_range hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hval : ∀ j (hj : j < args.length), ∃ v, e.evalEvar (tbl.ev (.evar ("X" ++ toString j)
      (KoreAML.srt (c.sortName (args[j]'hj))))) = .val v ∧ c.sortOf v = some (args[j]'hj) :=
    fun j hj => inSort_val (hin j hj)
  have hlen : ws.length = args.length := by simp [ws]
  refine ⟨ws, ⟨?_, hnum, fun j w s hw hs => ?_⟩⟩
  · have : ∀ (l : List Srt) (wl : List GroundTerm), wl.length = l.length →
        (∀ j (hj : j < l.length) w, wl[j]? = some w → c.sortOf w = some (l[j]'hj)) → c.sortsOf wl = some l := by
      intro l
      induction l with
      | nil => intro wl hl _; rw [List.length_eq_zero_iff.mp hl]; exact sortsOf_nil
      | cons a l ih =>
        intro wl hl hs
        cases wl with
        | nil => simp at hl
        | cons w wl =>
          exact sortsOf_cons.mpr ⟨a, l, hs 0 (by simp) w rfl, ih wl (by simpa using hl)
            (fun j hj w' hw' => hs (j + 1) (by simpa using hj) w' (by simpa using hw')), rfl⟩
    refine this args ws hlen fun j hj w hw => ?_
    rw [hget j hj] at hw
    obtain ⟨v, hv, hsv⟩ := hval j hj
    rw [hv] at hw
    cases hw
    exact hsv
  · have hj : j < args.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hw).1
    rw [hget j hj] at hw
    rw [List.getElem?_map, List.getElem?_eq_getElem hj] at hs
    cases hs
    obtain ⟨v, hv, -⟩ := hval j hj
    rw [hv] at hw ⊢
    cases hw
    rfl

/-- The conclusion of a function's equations, `f(X̄) = rhs ∧ ens`, over the sort variable `R`. -/
def fnConcl (c : Semantics) (fn : Fn) (rhs ens : Kore.Pattern) : Kore.Pattern :=
  .equals (KoreAML.srt (c.sortName fn.result)) KoreAML.R
    (KoreAML.ap (c.symName fn.label) (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))
    (.and (KoreAML.srt (c.sortName fn.result)) [rhs, ens])

/-- The facts the guards of an equation give, at the table of the axiom. -/
structure EqnAt (c : Semantics) (fn : Fn) (vars : List Srt) (tbl : KoreAML.VarTable) (e : Valuation Elem)
    (ws : List GroundTerm) : Prop where
  R : KoreAML.VarKey.sortVar "R" ∈ tbl
  Xk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
    KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl
  Vk : ∀ i < vars.length, canonKey c vars i ∈ tbl
  Rs : KoreAML.IsSort (stdI c) (e.evalEvar (tbl.ev (.sortVar "R")))
  args : ArgsAt c tbl e fn.args ws
  vin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))

namespace AtT

/-- `EqnAt` (ModelFns.lean) in the value model at `T`. -/
structure EqnAt (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (fn : Fn) (vars : List Srt)
    (tbl : KoreAML.VarTable) (e : ML.Valuation Elem) (ws : List GroundTerm) : Prop where
  R : KoreAML.VarKey.sortVar "R" ∈ tbl
  Xk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
    KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl
  Vk : ∀ i < vars.length, canonKey c vars i ∈ tbl
  Rs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R")))
  args : ArgsAt c tbl e fn.args ws
  vin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))

end AtT

theorem X_mem_varsOf_call : ∀ (ss : List String) (j n : Nat) (s : String), ss[n]? = some s →
    KoreAML.VarKey.evar ("X" ++ toString (j + n)) (KoreAML.srt s) ∈
      KoreAML.varsOfList (KoreAML.vars (KoreAML.numbered "X" j ss))
  | [], _, _, _, h => by simp at h
  | s' :: ss, j, 0, s, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.varsOfList, KoreAML.varsOf, Nat.add_zero]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  | s' :: ss, j, n + 1, s, h => by
    simp only [List.getElem?_cons_succ] at h
    have := X_mem_varsOf_call ss (j + 1) n s h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.varsOfList]
    rw [show j + (n + 1) = j + 1 + n by omega]
    exact List.mem_append_right _ (by simpa [KoreAML.vars] using this)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **An equation holds in the value model** where, at every valuation of its guards, its premise
gives `Eval` what the right-hand side gives. Each variable is free in the axiom, in its premise or
in its conclusion, so the guards give it an element of its sort. -/
theorem sat_eqnCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {vars : List Srt}
    (hnum : ∀ i < vars.length, vars.getD i 0 < nRegSorts + c.sortNames.length)
    {prem : Kore.Pattern} {rhs : Term} (hrhsOK : TermOK c (· < vars.length) rhs)
    {ens : Option Term} (hensOK : ∀ t, ens = some t → TermOK c (· < vars.length) t)
    (hV : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c vars) rhs) (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))))
    (hVv : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c vars) rhs) (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))))
    (hread : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (a : Elem), EqnAt c T fn vars tbl e ws →
      (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a → (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI_T c T) e a →
      ∀ v, Eval c fn.label ws (some v) ↔ EvalTerm c (substE c tbl vars e) rhs (some v) ∧
        ∀ t, ens = some t → EvalTerm c (substE c tbl vars e) t (some (bool true))) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  have hn := h.namesK
  have hfs := h.fnSorts hfn
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  have hsortP : KoreAML.sortOf [] (.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))) =
      some KoreAML.R := rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  generalize hP : (Kore.Pattern.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))) = P at hgs ⊢
  have hPv : ∀ k ∈ KoreAML.varsOf prem, k ∈ KoreAML.varsOf P := fun k hk => by
    rw [← hP, KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk)
  generalize htb : KoreAML.tableOf [KoreAML.Rv] P = tbl at hgs ⊢
  have hvarsP : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk => by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hguard : ∀ k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups,
      (KoreAML.guardOf tbl k).interpret (stdI_T c T) e m := fun k hk =>
    conjList_elim hgs _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] P, k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups :=
    fun k hk => List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) := by
    have := hguard (.sortVar "R") (List.mem_eraseDups.mpr (List.mem_append_left _
      (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩)))
    obtain ⟨s, hs, he⟩ := sortGuard_iff.mp this
    rw [he]; exact (isSort_iff _).mpr ⟨s, hs, rfl⟩
  have hcallF : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.freeOf [] P := fun j s hj => by
    rw [← hP, KoreAML.freeOf]
    refine List.mem_append_right _ ?_
    unfold fnConcl
    rw [KoreAML.freeOf]
    refine List.mem_append_left _ ?_
    unfold KoreAML.ap
    rw [KoreAML.freeOf]
    have := X_mem_call _ 0 j s hj
    rwa [Nat.zero_add] at this
  have hXk : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => by
    refine hvarsP _ ?_
    rw [← hP, KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    unfold fnConcl
    rw [KoreAML.varsOf]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    unfold KoreAML.ap
    rw [KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    have := X_mem_varsOf_call _ 0 j s hj
    rwa [Nat.zero_add] at this
  obtain ⟨ws, hws⟩ := argsAt_of (tbl := tbl) (e := e) (fun s hs => hfs s (List.mem_cons_of_mem _ hs)) (fun j hj => by
    have hs : (fn.args.map c.sortName)[j]? = some (c.sortName (fn.args[j]'hj)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hg := hguard _ (hfreeP _ (hcallF j _ hs))
    rw [KoreAML.interp_guard_evar defOK_std, trSort_srt] at hg
    exact (inhOf_sort hn (hfs _ (List.mem_cons_of_mem _ (List.getElem_mem hj))) e _).mp hg)
  have hvin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i))) := by
    intro i hi
    have hk : canonKey c vars i ∈ KoreAML.freeOf [] P := hP ▸ hV i hi
    have hg := hguard _ (hfreeP _ hk)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar defOK_std, trSort_srt, ← hkk] at hg
    exact (inhOf_sort hn (hnum i hi) e _).mp hg
  have hEq : EqnAt c T fn vars tbl e ws :=
    ⟨hRmem, hXk, fun i hi => hvarsP _ (hP ▸ hVv i hi), hRs, hws, hvin⟩
  obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hvin
  have hres := hfs fn.result (List.mem_cons_self ..)
  rw [KoreAML.interp_equal defOK_std]
  intro a
  have hPtr : KoreAML.tr ⟨tbl, []⟩ P = KoreAML.sImp (KoreAML.trSort tbl KoreAML.R) (KoreAML.tr ⟨tbl, []⟩ prem)
      (KoreAML.tr ⟨tbl, []⟩ (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))) := by
    rw [← hP, KoreAML.tr]
  rw [hPtr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [KoreAML.interp_inhOf_of (R_read e)] at ha
    have hrd := hread tbl e ws a hEq (fun k hk => hvarsP _ (hPv _ hk)) ha hprem
    have hSres : ∀ b, (KoreAML.trSort tbl (KoreAML.srt (c.sortName fn.result))).interpret (stdI_T c T) e b ↔
        b = .srt fn.result := fun b => by rw [trSort_srt]; exact sort_den hn hres e b
    unfold fnConcl
    rw [KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hSres (R_read e)
      ((isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩) hRs]
    refine ⟨ha, fun b hb => ?_⟩
    have hSres' : ∀ b, (KoreAML.trSort tbl (srtOf c fn.result)).interpret (stdI_T c T) e b ↔
        b = .srt fn.result := fun b => by unfold srtOf; exact hSres b
    have hens : ((KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c fn.result)
        (ens.map (Term.kore c (canonVars c vars))))).interpret (stdI_T c T) e b ↔
          ∀ t, ens = some t → EvalTerm c (substE c tbl vars e) t (some (bool true))) := by
      cases hq : ens with
      | none =>
        simp only [Option.map_none, reqPat]
        rw [KoreAML.tr, KoreAML.interp_sTop defOK_std (by unfold srtOf; rw [trSort_srt]; rfl),
          KoreAML.interp_inhOf_of hSres']
        exact ⟨fun _ t ht => (nomatch ht), fun _ => hb⟩
      | some t =>
        rw [Option.map_some, reqPat_iff h hvar (hensOK t hq) hSres'
          ((isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩) b]
        exact ⟨fun h' t' ht' => by cases ht'; exact h'.2, fun h' => ⟨hb, h' t rfl⟩⟩
    rw [inh_srt] at hb
    rw [call_read h hfn hws.sorts hws.X, tr_and2, KoreAML.interp_sAnd, hens, tr_term h hvar hrhsOK]
    constructor
    · rintro ⟨v, rfl, hv⟩
      obtain ⟨h1, h2⟩ := (hrd _).mp hv
      exact ⟨⟨v, h1, rfl⟩, h2⟩
    · rintro ⟨⟨v, hv, rfl⟩, h2⟩
      exact ⟨v, rfl, (hrd _).mpr ⟨hv, h2⟩⟩

end AtT

/-- **An equation holds in the value model** where, at every valuation of its guards, its premise
gives `Eval` what the right-hand side gives. Each variable is free in the axiom, in its premise or
in its conclusion, so the guards give it an element of its sort. -/
theorem sat_eqnCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {vars : List Srt}
    (hnum : ∀ i < vars.length, vars.getD i 0 < nRegSorts + c.sortNames.length)
    {prem : Kore.Pattern} {rhs : Term} (hrhsOK : TermOK c (· < vars.length) rhs)
    {ens : Option Term} (hensOK : ∀ t, ens = some t → TermOK c (· < vars.length) t)
    (hV : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c vars) rhs) (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))))
    (hVv : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c vars) rhs) (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))))
    (hread : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (a : Elem), EqnAt c fn vars tbl e ws →
      (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      KoreAML.Inh (stdI c) (e.evalEvar (tbl.ev (.sortVar "R"))) a → (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI c) e a →
      ∀ v, Eval c fn.label ws (some v) ↔ EvalTerm c (substE c tbl vars e) rhs (some v) ∧
        ∀ t, ens = some t → EvalTerm c (substE c tbl vars e) t (some (bool true))) :
    stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars))))), []⟩ : Kore.Axiom)⟩).pat :=
  AtT.sat_eqnCl (c := c) (T := StepM c) (h := h) (fn := fn) (hfn := hfn) (vars := vars) (hnum := hnum) (prem := prem) (rhs := rhs) (hrhsOK := hrhsOK) (ens := ens) (hensOK := hensOK) (hV := hV) (hVv := hVv)
    (hread := fun tbl e ws a hE => hread tbl e ws a ⟨hE.R, hE.Xk, hE.Vk, hE.Rs, hE.args, hE.vin⟩)

/-- `sat_eqnCl` where every variable is free in the premise. -/
theorem sat_eqn (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {vars : List Srt}
    (hnum : ∀ i < vars.length, vars.getD i 0 < nRegSorts + c.sortNames.length)
    {prem : Kore.Pattern} {rhs : Term} (hrhsOK : TermOK c (· < vars.length) rhs)
    {ens : Option Term} (hensOK : ∀ t, ens = some t → TermOK c (· < vars.length) t)
    (hV : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.freeOf [] prem)
    (hVv : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.varsOf prem)
    (hread : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (a : Elem), EqnAt c fn vars tbl e ws →
      (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      KoreAML.Inh (stdI c) (e.evalEvar (tbl.ev (.sortVar "R"))) a → (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI c) e a →
      ∀ v, Eval c fn.label ws (some v) ↔ EvalTerm c (substE c tbl vars e) rhs (some v) ∧
        ∀ t, ens = some t → EvalTerm c (substE c tbl vars e) t (some (bool true))) :
    stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars))))), []⟩ : Kore.Axiom)⟩).pat :=
  sat_eqnCl h hfn hnum hrhsOK hensOK (fun i hi => by rw [KoreAML.freeOf]; exact List.mem_append_left _ (hV i hi))
    (fun i hi => by rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ (hVv i hi))) hread

theorem varsOf_not_excl {fn : Fn} {cls : List Clause} {cl : Clause} (hcl : cl ∈ cls) (hpre : cl.pre = .top)
    (hbd : binds cl.vars.length (varOccsList cl.pats) = true) {i : Nat} (hi : i < cl.vars.length) :
    canonKey c cl.vars i ∈ KoreAML.varsOf (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl)))) := by
  simp only [KoreAML.varsOf]
  rw [anyOf_eq]
  exact List.mem_append_right _ (mem_varsOf_anyOfC (List.mem_map.mpr ⟨cl, hcl, rfl⟩) (varsOf_exclusion hpre hbd hi))

theorem varsOf_premise_var {args : List Srt} {req : Option Kore.Pattern} {pats : List Term} {vars : List Srt}
    (hlen : pats.length = args.length) {i : Nat} (hi : i ∈ varOccsList pats) :
    canonKey c vars i ∈ KoreAML.varsOf (premise (args.map c.sortName) req (Term.koreList c (canonVars c vars) pats)) := by
  obtain ⟨n, t, ht, hit⟩ := varOccsList_mem hi
  have hlt : n < args.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp ht).1
  have hq : (c.sortName (args[n]'hlt), Term.kore c (canonVars c vars) t) ∈
      (args.map c.sortName).zip (Term.koreList c (canonVars c vars) pats) := by
    refine List.mem_iff_getElem?.mpr ⟨n, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl, koreList_get ht⟩
  unfold premise
  exact varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (varsOf_argsConj_pat _ 0 hq (varsOf_kore c _ t hit))

/-! ## The rests -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **A function's rest graph holds**: where every clause fails at values of its argument sorts,
`f` applied to them is the values `Eval` gives there (`result_fn`), and `Eval.rest` with
`FnDet` makes that the rest. -/
theorem sat_restGraph (h : HypModelCore c) {fn : Fn} {vs : List GroundTerm} (hfn : fn ∈ c.allFns)
    (hvs : c.sortsOf vs = some fn.args) (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) :
    stdI_T c T ⊧ᴵ (KoreAML.den (symApp c fn.label (GroundTerm.koreList c vs)) ≡ (match c.fnRest fn vs with
      | some v => den c v
      | none => ⊥)) := by
  obtain ⟨hc, hh, hp⟩ := h.fnApart hfn
  have hE : Eval c fn.label vs (c.fnRest fn vs) := .rest (h.lookupFn hfn) hnone
  have hmi := h.det
  intro e m
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [show fn.label = fn.sig.name from rfl, symApp_val h (fn_sig_mem hfn) hvs (sortsOf_length hvs),
    result_fn (k := fn.sig) hc hh hp (c.isOvl_of_lookupFn (h.lookupFn hfn))]
  revert hE
  cases hr : c.fnRest fn vs with
  | none =>
    intro hE
    simp only [Pattern.interpret]
    constructor
    · rintro ⟨v, -, hv⟩; cases hmi _ _ _ _ hv hE
    · intro hf; exact hf.elim
  | some v =>
    intro hE
    dsimp only
    rw [den_val h v (Semantics.fnRest_sorted hr) e a]
    constructor
    · rintro ⟨v', rfl, hv'⟩; cases hmi _ _ _ _ hv' hE; rfl
    · rintro rfl; exact ⟨v, rfl, hE⟩

end AtT

/-- **A function's rest graph holds**: where every clause fails at values of its argument sorts,
`f` applied to them is the values `Eval` gives there (`result_fn`), and `Eval.rest` with
`FnDet` makes that the rest. -/
theorem sat_restGraph (h : HypModelCore c) {fn : Fn} {vs : List GroundTerm} (hfn : fn ∈ c.allFns)
    (hvs : c.sortsOf vs = some fn.args) (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) :
    stdI c ⊧ᴵ (KoreAML.den (symApp c fn.label (GroundTerm.koreList c vs)) ≡ (match c.fnRest fn vs with
      | some v => den c v
      | none => ⊥)) :=
  AtT.sat_restGraph (c := c) (T := StepM c) (h := h) (fn := fn) (vs := vs) (hfn := hfn) (hvs := hvs) (hnone := hnone)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatFallbackGoal`**: the value model satisfies what the interpretation decides where the
text is silent: an interpreted symbol's result at its silent points (`sat_silentGraph`), and a
function's rest where every clause fails (`sat_restGraph`). -/
theorem satFallbackGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓFallback c) := by
  rintro φ (⟨k, vs, hk, hvs, hh, hs, rfl⟩ | ⟨fn, vs, hfn, hvs, hnone, rfl⟩)
  · exact sat_silentGraph h hk hvs hh hs
  · exact sat_restGraph h hfn hvs hnone

end AtT

/-- **`SatFallbackGoal`**: the value model satisfies what the interpretation decides where the
text is silent: an interpreted symbol's result at its silent points (`sat_silentGraph`), and a
function's rest where every clause fails (`sat_restGraph`). -/
theorem satFallbackGoal (h : HypModelCore c) : SatFallbackGoal c :=
  AtT.satFallbackGoal (c := c) (T := StepM c) (h := h)

end Model

end Faithful

end KCore
