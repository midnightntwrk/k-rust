/-
  KCore. Step completeness: with the step's closure axiom (`Γstep`), in every model of `Γ c` every
  successor of a configuration's element is the element of a configuration `Step` gives.

  The closure axiom puts a configuration's element `a` with a successor `b` in a rule's disjunct
  `∃x̄. (L ∧ b ∈ R)`, at a valuation of the rule's variables in their sorts. The rule's left-hand
  side, read downwards from the configuration (`patVal_backC`), gives every variable the element of
  a value of its sort: every variable of a rule occurs in its left-hand side, and a value's element
  lies in a pattern's translation only where the pattern matches the value under the substitution
  of those values (constructors, injections, domain values and collection patterns alike). The
  `requires` and the right-hand side are then read upwards at that substitution (`evalTerm_den4`):
  each evaluates where every function has a result at arguments of its sorts (`evalTerm_total`,
  `FnTerminates`), the `requires` to `true` since `⌈req = true⌉` holds
  (`reqFalse_empty`), the right-hand side to a configuration whose element is `b`. A rule of a
  smaller priority does not apply: if it did, the configuration's element would be in its
  `applies` pattern (`applies_holds`), which the disjunct negates. So the rule makes a step of
  `Step` to a configuration that denotes `b` (`step_complete`).
-/
import KcoreSpec.HypWf

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## Patterns of the encoding, in any model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
theorem disjList_of_mem {e : Valuation M} {m : M} : ∀ {ws : List KoreAML.P} {w : KoreAML.P}, w ∈ ws →
    w.interpret I e m → (KoreAML.disjList ws).interpret I e m
  | [], _, hw, _ => absurd hw List.not_mem_nil
  | [_], _, hw, h => by rw [List.mem_singleton.mp hw] at h; exact h
  | w' :: w'' :: ws, w, hw, h => by
    unfold KoreAML.disjList
    rw [interpret_disj]
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl h
    · exact Or.inr (disjList_of_mem hw h)

theorem srt_inj {n n' : String} (h : KoreAML.srt n = KoreAML.srt n') : n = n' := by
  unfold KoreAML.srt at h
  injection h with h
  injection h with h
  injection h with h
  exact append_cancel h

/-- Under the existentials of a closure disjunct: a valuation that differs from the outer one at
the binders only, gives each binder an element of its sort, and satisfies the body. Two binders at
one index have one sort. -/
theorem sExists_foldr_elim (hD : DefOK I) {tbl : VarTable} {body : KoreAML.P} :
    ∀ (free : List (VarKey × Kore.KSort)) (e : Valuation M) (m : M),
    (∀ ks ∈ free, ∀ ks' ∈ free, tbl.ev ks.1 = tbl.ev ks'.1 → ks.2 = ks'.2) →
    (∀ ks ∈ free, ∃ n, ks.2 = KoreAML.srt n) →
    (free.foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ) body).interpret I e m →
    ∃ e' : Valuation M, (∀ x, (∀ ks ∈ free, x ≠ tbl.ev ks.1) → e'.evalEvar x = e.evalEvar x) ∧
      (∀ ks ∈ free, ∀ n, ks.2 = KoreAML.srt n → InS I n (e'.evalEvar (tbl.ev ks.1))) ∧
      body.interpret I e' m
  | [], e, m, _, _, h => ⟨e, fun _ _ => rfl, fun _ hb => absurd hb List.not_mem_nil, h⟩
  | (k, s) :: free, e, m, hone, hs, h => by
    have h' : (KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s)
        (free.foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ) body)).interpret I e m := h
    rw [KoreAML.interp_sExists] at h'
    obtain ⟨a, ha, h'⟩ := h'
    obtain ⟨e', h1, h2, h3⟩ := sExists_foldr_elim hD free _ m
      (fun ks hks ks' hks' => hone ks (List.mem_cons_of_mem _ hks) ks' (List.mem_cons_of_mem _ hks'))
      (fun ks hks => hs ks (List.mem_cons_of_mem _ hks)) h'
    refine ⟨e', fun x hx => ?_, fun ks hks n hn => ?_, h3⟩
    · rw [h1 x (fun ks hks => hx ks (List.mem_cons_of_mem _ hks))]
      exact Function.update_noteq (hx (k, s) (List.mem_cons_self ..)) _ _
    · rcases List.mem_cons.mp hks with rfl | hks
      · by_cases hre : ∃ ks' ∈ free, tbl.ev k = tbl.ev ks'.1
        · obtain ⟨ks', hks', he⟩ := hre
          obtain ⟨n', hn'⟩ := hs ks' (List.mem_cons_of_mem _ hks')
          have hss := hone (k, s) (List.mem_cons_self ..) ks' (List.mem_cons_of_mem _ hks') he
          have hnn : n = n' := srt_inj (hn.symm.trans (hss.trans hn'))
          subst hnn
          show InS I n (e'.evalEvar (tbl.ev k))
          rw [he]
          exact h2 ks' hks' n hn'
        · have hev : e'.evalEvar (tbl.ev k) = a := by
            rw [h1 _ (fun ks' hks' heq => hre ⟨ks', hks', heq⟩)]
            exact Function.update_same _ _ _
          show InS I n (e'.evalEvar (tbl.ev k))
          rw [hev]
          rw [KoreAML.interp_member hD] at ha
          simp only [Function.update_same] at ha
          rw [show s = KoreAML.srt n from hn, trSort_srt] at ha
          exact (inS_iff _).mp ha
      · exact h2 ks hks n hn

/-- `∃b̄. body` holds at `e` where `body` holds at a valuation that differs from `e` at the binders
only, and gives each binder an element of its sort. -/
theorem existsAll_intro_at (hD : DefOK I) {tbl : VarTable} {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (e e' : Valuation M) (m : M),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e'.evalEvar x = e.evalEvar x) →
    e'.evalSvar = e.evalSvar →
    (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS I n (e'.evalEvar (tbl.ev (KoreAML.evarKey b)))) →
    (KoreAML.tr ⟨tbl, []⟩ body).interpret I e' m →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)).interpret I e m
  | [], e, e', m, _, _, hoff, hsv, _, hb => by
    have : e' = e := by
      cases e; cases e'
      simp only at hsv
      subst hsv
      congr 1
      funext x
      exact hoff x (fun _ h => absurd h List.not_mem_nil)
    subst this
    exact hb
  | b :: bs, e, e', m, hnd, hs, hoff, hsv, hg, hb => by
    show (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret I e m
    rw [KoreAML.tr, KoreAML.interp_sExists]
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨e'.evalEvar (tbl.ev (KoreAML.evarKey b)), ?_, ?_⟩
    · rw [KoreAML.interp_member hD]
      simp only [Function.update_same]
      obtain ⟨n, hn⟩ := hs b (List.mem_cons_self ..)
      rw [hn, trSort_srt]
      exact (inS_iff _).mpr (hg b (List.mem_cons_self ..) n hn)
    · refine existsAll_intro_at hD bs _ e' m hnd.2 (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb'))
        (fun x hx => ?_) hsv (fun b' hb' => hg b' (List.mem_cons_of_mem _ hb')) hb
      show e'.evalEvar x = Function.update e.evalEvar (tbl.ev (KoreAML.evarKey b)) (e'.evalEvar (tbl.ev (KoreAML.evarKey b))) x
      by_cases hxb : x = tbl.ev (KoreAML.evarKey b)
      · subst hxb; simp only [Function.update_same]
      · rw [Function.update_noteq hxb]
        exact hoff x (fun b' hb' => by
          rcases List.mem_cons.mp hb' with rfl | hb'
          · exact hxb
          · exact hx b' hb')

omit [Inhabited M] in
/-- An element of a competitor's pattern and of the sort is in the disjunction of the competitors. -/
theorem anyOfC_of_mem {tbl : VarTable} {S : Kore.KSort} {e : Valuation M} {m : M}
    (hS : (KoreAML.inhOf (KoreAML.trSort tbl S)).interpret I e m) : ∀ {comps : List Kore.Pattern} {φ : Kore.Pattern},
    φ ∈ comps → (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e m → (KoreAML.tr ⟨tbl, []⟩ (anyOfC S comps)).interpret I e m
  | [], _, hφ, _ => absurd hφ List.not_mem_nil
  | ψ :: comps, φ, hφ, h => by
    rw [anyOfC, KoreAML.tr]
    simp only [KoreAML.trOrList]
    rw [KoreAML.interp_sOr]
    refine ⟨hS, ?_⟩
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact Or.inl h
    · exact Or.inr (anyOfC_of_mem hS hφ h)

end

/-! ## The disjuncts of the closure, read back -/

/-- Every disjunct of the closure is one pattern's, read through its table placed at an offset
that leaves its variables below the total. -/
theorem stepF_cases (y : EVar) : ∀ (pats : List Kore.Pattern) (acc : List String × List KoreAML.P × Nat),
    ∀ φ ∈ (pats.foldl (Model.stepF y) acc).2.1, φ ∈ acc.2.1 ∨
      ∃ p ∈ pats, ∃ off, off + (KoreAML.tableOf [] p).length ≤ Model.tablesLen pats acc.2.2 ∧
        φ = (KoreAML.closureDisjunct [] off y p).2
  | [], _, _, h => Or.inl h
  | q :: pats, acc, φ, h => by
    rw [List.foldl_cons] at h
    have hlen : (Model.stepF y acc q).2.2 = acc.2.2 + (KoreAML.tableOf [] q).length := by
      show acc.2.2 + (KoreAML.closureDisjunct [] acc.2.2 y q).1.length = _
      rw [Model.closureDisjunct_names_length]
    rcases stepF_cases y pats (Model.stepF y acc q) φ h with h | ⟨p, hp, off, hoff, rfl⟩
    · have h' : φ ∈ acc.2.1 ++ [(KoreAML.closureDisjunct [] acc.2.2 y q).2] := h
      rcases List.mem_append.mp h' with h' | h'
      · exact Or.inl h'
      · right
        refine ⟨q, List.mem_cons_self .., acc.2.2, ?_, List.mem_singleton.mp h'⟩
        unfold Model.tablesLen
        rw [List.foldl_cons]
        exact Model.tablesLen_ge pats _
    · right
      rw [hlen] at hoff
      refine ⟨p, List.mem_cons_of_mem _ hp, off, ?_, rfl⟩
      unfold Model.tablesLen
      rw [List.foldl_cons]
      exact hoff

/-- A closure disjunct of a rule's axiom `\rewrites(L, R)`, written out. -/
theorem closureDisjunct_rewrites (off : Nat) (y : EVar) (S : Kore.KSort) (L R : Kore.Pattern) :
    (KoreAML.closureDisjunct [] off y (.rewrites S L R)).2 =
      ((Model.evarsOf (KoreAML.freeOf [] (.rewrites S L R)).eraseDups).foldr
        (fun (k, s) φ => KoreAML.sExists (VarTable.ev (List.replicate off (VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites S L R)) k)
          (KoreAML.trSort (List.replicate off (VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites S L R)) s) φ)
        (KoreAML.tr ⟨List.replicate off (VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites S L R), []⟩ L ⋀
          (y ∈∈ KoreAML.tr ⟨List.replicate off (VarKey.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites S L R), []⟩ R))) := by
  unfold KoreAML.closureDisjunct
  rfl

/-! ## The valuation of a substitution, in any model -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

open Classical in
/-- The valuation that gives the canonical variables of `vars`, through `tbl`, the elements of
their values in σ, and agrees with `e` elsewhere. -/
noncomputable def overV (c : Semantics) (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (vars : List Srt)
    (σ : Subst) (e : Valuation M) : Valuation M :=
  ⟨fun x => if h : ∃ i < vars.length, x = tbl.ev (canonKey c vars i)
    then elemOf c I ((σ.lookup (Classical.choose h)).getD default) else e.evalEvar x, e.evalSvar⟩

theorem overV_at {tbl : VarTable} {vars : List Srt} {σ : Subst} {e : Valuation M}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl) {i : Nat} (hi : i < vars.length) :
    (overV c I tbl vars σ e).evalEvar (tbl.ev (canonKey c vars i)) = elemOf c I ((σ.lookup i).getD default) := by
  have hex : ∃ j < vars.length, tbl.ev (canonKey c vars i) = tbl.ev (canonKey c vars j) := ⟨i, hi, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, hje⟩ := Classical.choose_spec hex
  have e1 : Classical.choose hex = i := (canonKey_inj hi hj (ev_inj (hkeys i hi) (hkeys _ hj) hje)).symm
  rw [e1]

theorem overV_off {tbl : VarTable} {vars : List Srt} {σ : Subst} {e : Valuation M} {x : EVar}
    (hx : ∀ i < vars.length, x ≠ tbl.ev (canonKey c vars i)) : (overV c I tbl vars σ e).evalEvar x = e.evalEvar x := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (fun ⟨i, hi, he⟩ => hx i hi he)]

theorem overV_agrees (hI : I ⊧ᴵP Γ c) [OvlOK c] {tbl : VarTable} {vars : List Srt} {σ : Subst} {e : Valuation M}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl) (hσ : c.WellSorted vars σ) :
    Agrees c I tbl (canonVars c vars) σ (overV c I tbl vars σ e) := by
  intro i v hi hl m
  rw [canonVars_length] at hi
  show m = (overV c I tbl vars σ e).evalEvar (tbl.ev (canonKey c vars i)) ↔ _
  rw [overV_at hkeys hi, hl]
  obtain ⟨w, hw, hsw⟩ := hσ i (vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  rw [hl] at hw; cases hw
  exact ((elemOf_spec hI hsw _).1 m).symm

end

/-! ## A rule that applies, in a model -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hsc : SortCtx c)
  (hok : c.sortedOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hph : patHooksApart c = true)
  (hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmpty c I fn cl)
include hI hnn hsc hok hbc hph hneg

/-- **A rule that applies, in a model**: a configuration that a rule's left-hand side matches
under a well-sorted σ, with its `requires` evaluating to `true`, has its element in the rule's
`applies` pattern `∃x̄. (lhs ∧ ⌈req = true⌉)`. -/
theorem applies_holds (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) (hpre : r.pre = .top) (hb : binds r.vars.length (varOccs r.lhs) = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {x : Config c}
    (hmatch : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) (e : Valuation M) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := by
  have hD := defOK hI
  let vs := canonVars c r.vars
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hag := overV_agrees hI hkeys hσ (e := e)
  have h := lhs_req_hold4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hr hσ hmatch hreq hag
  rw [applies_top _ hpre hb]
  show (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll (srtOf c topCellSort) (vs.map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs))]))).interpret
        I e _
  refine existsAll_intro_at hD _ e (overV c I tbl r.vars σ e) _ hnd hsrt (fun z hz => ?_) rfl (fun b hb n hn => ?_) ?_
  · refine overV_off fun i hi he => hz _ ?_ he
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    show ((canonVars c r.vars).getD i default).kore ∈ vs.map KoreAML.Var.kore
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.mem_map_of_mem (List.getElem_mem hlt)
  · obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb
    have hs : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c hi]; rfl
    rw [hs] at hn
    rw [← srt_inj hn]
    show InS I _ ((overV c I tbl r.vars σ e).evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [overV_at hkeys hi]
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    rw [hw]
    exact (inS_iff e).mp (elemOf_spec hI hsw e).2
  · rw [tr_and2, KoreAML.interp_sAnd]
    exact h

end

/-! ## Step completeness -/

section
variable {c : Semantics}

/-- A rule's axiom `\rewrites(L, R)`, its left-hand part `L` read: the rule's variables occur
free in `L`, the canonical variables of the rule and of its competitors are among `L`'s, and an
element of `L` is in the left-hand side and in `⌈req = true⌉`, and in no competitor's `applies`. -/
theorem rule_parts {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hok : c.sortedOK = true)
    (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    {r : Rule} (hr : r ∈ c.rules) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L
        (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.freeOf [] L) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, canonKey c r'.vars i ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.tr ⟨tbl, []⟩ L).interpret I e a →
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e a ∧
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret
          I e a ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio →
          ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e a := by
  have hbinds := Exec.binds_all (hb _ hr)
  obtain ⟨hpre₀, hpost₀⟩ := htop _ hr
  have hex₀ : r.exs = [] := Semantics.sortedOK_exsNil hok hr (hb r hr)
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  have hfree : ∀ (ps : List Kore.Pattern), ∀ i < r.vars.length,
      canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C (Term.kore c vs r.lhs :: ps)) :=
    fun ps i hi => Model.freeOf_and_lhs (Model.kore_freeOf c vs r.lhs (hbinds i hi))
  have hvars : ∀ (ps : List Kore.Pattern), ∀ i < r.vars.length,
      canonKey c r.vars i ∈ KoreAML.varsOf (.and C (Term.kore c vs r.lhs :: ps)) :=
    fun ps i hi => Model.varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c vs r.lhs (hbinds i hi))
  by_cases hce : comps.isEmpty
  · have hnone : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio := fun r' hr' hlt => by
      have := hcomp r' hr' hlt
      rw [List.isEmpty_iff.mp hce] at this
      exact absurd this List.not_mem_nil
    refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])],
      by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce], hfree _, hvars _,
      fun r' hr' hlt => absurd hlt (hnone r' hr'), fun tbl e a h => ?_⟩
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
    exact ⟨h.1, h.2.1, fun r' hr' hlt => absurd hlt (hnone r' hr')⟩
  · refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .not C (anyOfC C comps),
        .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])],
      by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce], hfree _, hvars _, fun r' hr' hlt i hi => ?_,
      fun tbl e a h => ?_⟩
    · refine Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
      simp only [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr' hlt)
        (varsOf_applies (htop _ hr').1 (hb _ hr') hi))
    · rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
      obtain ⟨h1, h2, h3, -⟩ := h
      rw [KoreAML.tr, KoreAML.interp_sNot] at h3
      exact ⟨h1, h2, fun r' hr' hlt happ => h3.1 (anyOfC_of_mem h3.2 (hcomp r' hr' hlt) happ)⟩

open Classical in
/-- **Step completeness**: with the step's closure axiom, in every model of `Γ c`, every successor
of the element of a configuration `x` is the element of a configuration that `ref`, a step function
listing `Step`'s successors, gives for `x`. -/
theorem step_complete (hpreTop : c.clausesPreTop = true) (h : HypSoundCore c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hft : FnTerminates c) (ref : StepFn) (href : StepIs c ref) (x : Config c) :
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c)))) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro M _ I hI e m
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hD := defOK hIΓ
  -- every clause's exclusion is empty where it fails, as for soundness
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hIΓ hph hcs hcso hg hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hok hfn hcl)
        (Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfn hcl hp') hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  have hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmpty c I fn cl :=
    fun fn hfn cl hcl _ => hex fn hfn cl hcl
  rw [interpret_impl]
  intro hmx
  have hmx' : m = elemOf c I x.val := ((elemOf_spec hIΓ x.property e).1 m).mp hmx
  subst hmx'
  unfold KoreAML.allNext
  rw [interpret_neg]
  intro hnext
  unfold KoreAML.sNext at hnext
  rw [KoreAML.interp_app] at hnext
  obtain ⟨n0, b, hn0, hnb, happ⟩ := hnext
  rw [interpret_neg] at hnb
  apply hnb
  -- the closure axiom, at `y := b`
  have hcl := hI _ (Or.inr rfl) e (elemOf c I x.val)
  rw [Model.stepClosure_pat] at hcl
  dsimp only at hcl
  generalize hy : (⟨Model.tablesLen (c.rules.map (prioRuleK c)) 0 + 1⟩ : EVar) = y at hcl
  let e1 : Valuation M := ⟨Function.update e.evalEvar y b, e.evalSvar⟩
  have hψ : (KoreAML.sNext (.evar y) ⊆⊆
      KoreAML.disjList ((c.rules.map (prioRuleK c)).foldl (Model.stepF y) ([], [], 0)).2.1).interpret I e1
        (elemOf c I x.val) := by
    unfold Pattern.universal at hcl
    rw [interpret_neg, interpret_exists] at hcl
    exact Classical.byContradiction fun hc => hcl ⟨b, by rw [interpret_neg]; exact hc⟩
  rw [KoreAML.interp_included hD] at hψ
  have hdisj := hψ (elemOf c I x.val) (by
    unfold KoreAML.sNext
    rw [KoreAML.interp_app]
    exact ⟨n0, b, hn0, by show b = Function.update e.evalEvar y b y; simp, happ⟩)
  obtain ⟨φ, hφ, hφm⟩ := disjList_mem hdisj
  rcases stepF_cases y _ _ φ hφ with hφ | ⟨p, hp, off, hoff, rfl⟩
  · exact absurd hφ List.not_mem_nil
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hlhs, hreqs, hrhss⟩ := rule_ctx hok hr
  have hbinds := Exec.binds_all (hb _ hr)
  obtain ⟨L, hPL, hLfree, hLvars, hLcomp, hLread⟩ := rule_parts (I := I) hok hb htop hr
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let R : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] (.rewrites C L R), ∃ i < r.vars.length, k = canonKey c r.vars i :=
    fun k hk => Model.freeOf_prio_of_sorted hok hb htop hr (by rw [hPL]; exact hk)
  rw [hPL] at hφm hoff
  rw [closureDisjunct_rewrites] at hφm
  -- the table of the disjunct
  let tbl : VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites C L R)
  have hin_tbl : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ (by
      simp only [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ hk))))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hin_tbl _ (hLvars i hi)
  have hy_ne : ∀ k ∈ tbl, y ≠ tbl.ev k := by
    intro k hk he
    have h1 := Model.index_le hk
    have hoff' : off + (KoreAML.tableOf [] (.rewrites C L R)).length ≤ Model.tablesLen (c.rules.map (prioRuleK c)) 0 :=
      hoff
    rw [← he, ← hy] at h1
    have h2 : tbl.length = off + (KoreAML.tableOf [] (.rewrites C L R)).length := by simp [tbl]
    simp only at h1
    omega
  -- the binders of the disjunct are the rule's variables
  let free := Model.evarsOf (KoreAML.freeOf [] (.rewrites C L R)).eraseDups
  have hfree : ∀ ks ∈ free, ∃ i < r.vars.length, ks.1 = canonKey c r.vars i ∧
      ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, n, hn⟩ := Model.mem_filterMap_evar hks
    obtain ⟨i, hi, he⟩ := hfreeP _ (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, he, ?_⟩
    rw [he, canonKey_eq c hi] at hn
    injection hn with _ h2
    exact h2.symm
  obtain ⟨e2, he2, hguard, hbody⟩ := sExists_foldr_elim hD free e1 _
    (fun ks hks ks' hks' heq => by
      obtain ⟨i, hi, h1, h2⟩ := hfree ks hks
      obtain ⟨j, hj, h1', h2'⟩ := hfree ks' hks'
      have hij := canonKey_inj hi hj (by rw [← h1, ← h1']; exact ev_inj (h1 ▸ hkeys i hi) (h1' ▸ hkeys j hj) heq)
      subst hij
      rw [h2, h2'])
    (fun ks hks => by obtain ⟨i, -, -, h2⟩ := hfree ks hks; exact ⟨_, h2⟩) hφm
  have he2y : e2.evalEvar y = b := by
    rw [he2 y (fun ks hks => by
      obtain ⟨i, hi, h1, -⟩ := hfree ks hks
      rw [h1]; exact hy_ne _ (hkeys i hi))]
    show Function.update e.evalEvar y b y = b
    simp
  rw [interpret_conj] at hbody
  obtain ⟨hL, hRm⟩ := hbody
  rw [KoreAML.interp_member hD, he2y] at hRm
  change (KoreAML.tr ⟨tbl, []⟩ (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])).interpret
    I e2 b at hRm
  rw [tr_and2, KoreAML.interp_sAnd] at hRm
  obtain ⟨hl, hreq, hcomp⟩ := hLread tbl e2 _ hL
  -- the valuation of the rule's variables is a well-sorted substitution of values
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e2.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] (.rewrites C L R) := by
      rw [KoreAML.freeOf]; exact List.mem_append_left _ (hLfree i hi)
    have hks := Model.evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    have := hguard _ hks _ rfl
    show InS I _ (e2.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [canonKey_eq c hi]
    exact this
  obtain ⟨hmatch, hwit⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.lhs_nf OvlOK.ok hr hlhs) x.property hl
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) (fun i hi => hwit i (hbinds i hi))
  -- the `requires` evaluates to `true`
  have hreqT : ∀ t, r.req = some t → EvalTerm c (substOf c I tbl vs r.vars e2) t (some (bool true)) := by
    intro t ht
    obtain ⟨v, hv⟩ := Model.evalTerm_total h hft fns_headsOK hσ (hreqs t ht)
    by_cases hvt : v = some (bool true)
    · rw [hvt] at hv; exact hv
    · exfalso
      rw [ht] at hreq
      obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
      exact reqFalse_empty hIΓ (S' := srtOf c topCellSort) (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2
        hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hreqs t ht) hu)
        (evalTerm_den4 (hpreTop := hpreTop) hIΓ hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t ht))
        _ hreq
  -- the `ensures` evaluates to `true`
  have hensS := rule_ctx_ens hok hr
  have hensT : ∀ t, r.ens = some t → EvalTerm c (substOf c I tbl vs r.vars e2) t (some (bool true)) := by
    intro t ht
    obtain ⟨v, hv⟩ := Model.evalTerm_total h hft fns_headsOK hσ (hensS t ht)
    by_cases hvt : v = some (bool true)
    · rw [hvt] at hv; exact hv
    · exfalso
      have hE := hRm.2
      rw [ht] at hE
      obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
      exact reqFalse_empty hIΓ (S' := srtOf c topCellSort) (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2
        hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hensS t ht) hu)
        (evalTerm_den4 (hpreTop := hpreTop) hIΓ hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht))
        _ hE
  -- no rule of a smaller priority applies
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    intro r' hr' hlt
    refine Classical.byContradiction fun hna => ?_
    have hex' : ∃ σ', c.WellSorted r'.vars σ' ∧ PatVal c σ' r'.lhs x.val ∧ ¬ RuleReqFails c σ' r' :=
      Classical.byContradiction fun hne => hna <| NotApplies.of_wellSorted (hb _ hr') fun σ' h1 h2 =>
        Classical.byContradiction fun h3 => hne ⟨σ', h1, h2, h3⟩
    obtain ⟨σ', hσ', hpv', hnf⟩ := hex'
    obtain ⟨-, hreqs', -⟩ := rule_ctx hok hr'
    have hreq' : ∀ t, r'.req = some t → EvalTerm c σ' t (some (bool true)) := by
      intro t ht
      obtain ⟨v, hv⟩ := Model.evalTerm_total h hft fns_headsOK hσ' (hreqs' t ht)
      by_cases hvt : v = some (bool true)
      · rw [hvt] at hv; exact hv
      · exact absurd (RuleReqFails.intro ht hv hvt) hnf
    exact hcomp r' hr' hlt (applies_holds (hpreTop := hpreTop) hIΓ hnn hsc hok hbc hph hneg hr' (htop _ hr').1 (hb _ hr') hσ' hpv' hreq'
      (fun i hi => hin_tbl _ (hLcomp r' hr' hlt i hi)) e2)
  -- the right-hand side evaluates to a configuration whose element is `b`
  obtain ⟨v, hv⟩ := Model.evalTerm_total h hft fns_headsOK hσ hrhss
  have hbR := (evalTerm_den4 (hpreTop := hpreTop) hIΓ hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b).mp
    hRm.1
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hstep := step_of_apply_core hok hsr (OvlOK.ovlCase inferInstance) hr hσ hmatch hreqT ((htop _ hr).1 ▸ .top) hv hensT
      ((htop _ hr).2 ▸ .top) hprio
    have hmem : yv ∈ ref x.val := (href x yv).mpr ⟨_, hstep⟩
    exact disjList_of_mem (List.mem_map_of_mem hmem) (((den_closed c yv).interp e2 e b).mp hbR)

end

end Faithful

end KCore
