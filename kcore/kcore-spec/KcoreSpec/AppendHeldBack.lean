/-
  KCore. K's `append` has `HeldBack` in every model of `Γ` (`appendHeld_backX`).

  `Semantics.appendHeldX c f` (FaithOK.lean) holds where f is a function of `(K, K) → K` whose two
  clauses are `f(dotk, T) = T` and `f(kseq(I, KS), T) = kseq(I, f(KS, T))` (no `requires`, no
  `ensures`, `\top` predicates, one priority), K is a constructor sort of the theory and K's
  generators are `kseq` and `dotk` alone. Then in a model of `Γ`, where a value's element w is in
  `f(b₁, b₂)` for elements b₁, b₂ of K, b₁ and b₂ are values' elements: by induction on w,
  splitting b₁ by K's no-junk item (`noJunk_elim`):
  - b₁ in `dotk`: the first clause's equation gives `f(b₁, b₂) = b₂`, so b₂ is w's element, and
    b₁ is `dotk`'s (`gen_value`);
  - b₁ in `kseq(i, ks)`: the second clause's equation gives `f(b₁, b₂) = kseq(i, f(ks, b₂))`, so w's
    element is `kseq(i, a)` for some a in `f(ks, b₂)`; Cons-Inj and Cons-Dist (`ctor_back`) give
    `w = kseq(v, W)` with i v's element and a W's, the induction at W gives ks and b₂ as values'
    elements, and b₁ is then `kseq`'s application to values' elements, a value's (`gen_value`).

  The equations are read at elements, not values (`clause_atElX`): a clause's item holds at every
  valuation of its variables in their sorts.
-/
import KcoreSpec.OccsUnder
import KcoreSpec.Confined
import KcoreSpec.FaithfulStage2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The valuation of a clause's equation at elements: the sort `σr` to the sort variable `R`, the
j-th element of `xs` to `Xⱼ`, the i-th element of `ys` to the clause's variable i. -/
noncomputable def clauseValElX (σr : M) (nargs nvars : Nat) (xs ys : List M) : VarKey → M
  | .sortVar _ => σr
  | .evar n _ => match xIdx nargs n with
    | some j => xs.getD j default
    | none => match varIdx nvars n with
      | some i => ys.getD i default
      | none => default
  | .svar _ _ => default

/-- **A clause's equation, read at elements.** For a clause of a function with no clause of a
smaller priority, no `requires`, no `ensures`, no existential variable and the predicate `\top`,
at the valuation of its table that gives the formal arguments the elements `xs` and the clause's
variables the elements `ys`, each of its sort: the valuation gives each key its element, and where
the premise holds, the function's application to the formal arguments and the right side denote
the same elements of the result sort. -/
theorem clause_atElX (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    {fn : Fn} (hfnm : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl = []) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreq : cl.req = none) (hens : cl.ens = none)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    {σr : M} (hσr1 : ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName fn.result)) a ↔ a = σr) (hσr2 : IsSort I σr)
    {xs ys : List M}
    (hxs : ∀ j s, (fn.args.map c.sortName)[j]? = some s → InS I s (xs.getD j default))
    (hys : ∀ i < cl.vars.length, InS I (c.sortName (cl.vars.getD i 0)) (ys.getD i default)) :
    let t := KoreAML.tableOf (clauseAxiom c fn cl).sortVars (clauseAxiom c fn cl).pattern
    let e := valOf t (clauseValElX σr fn.args.length cl.vars.length xs ys)
    (∀ j s, (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (t.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = xs.getD j default) ∧
    (∀ i < cl.vars.length, e.evalEvar (t.ev (canonKey c cl.vars i)) = ys.getD i default) ∧
    (∀ a, (KoreAML.trSort t KoreAML.R).interpret I e a ↔ a = σr) ∧
    ((∃ b, Inh I σr b ∧ (KoreAML.tr ⟨t, []⟩ (clausePrem c fn cl)).interpret I e b) →
      ∀ a, Inh I σr a →
        ((KoreAML.tr ⟨t, []⟩ (symApp c fn.label
          (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e a ↔
        (KoreAML.tr ⟨t, []⟩ (clauseRight c fn cl)).interpret I e a)) := by
  intro t e
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hv := premise_vars (c := c) hpats hbinds (fun t ht => by rw [hreq] at ht; cases ht)
  have hvarsP : ∀ k, k ∈ KoreAML.varsOf (clausePrem c fn cl) → k ∈ t := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl))
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hRmem : VarKey.sortVar "R" ∈ t :=
    List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hXv : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (t.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = xs.getD j default := fun j s hj => by
    have hjn : j < fn.args.length := by simpa using (List.getElem?_eq_some_iff.mp hj).1
    rw [valOf_ev (hvarsP _ (hv.1 j s hj))]
    simp only [clauseValElX]
    rw [xIdx_eq hjn]
  have hVv : ∀ i < cl.vars.length, e.evalEvar (t.ev (canonKey c cl.vars i)) = ys.getD i default := fun i hi => by
    rw [valOf_ev (hvarsP _ (hv.2.1 i hi)), canonKey_eq c hi]
    simp only [clauseValElX]
    rw [xIdx_var, varIdx_eq hi]
  have hRv : ∀ a, (KoreAML.trSort t KoreAML.R).interpret I e a ↔ a = σr := fun a => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]; rfl
  refine ⟨hXv, hVv, hRv, ?_⟩
  rintro ⟨b, hb, hprem⟩
  have hfree : ∀ k, k ∈ KoreAML.freeOf [] (clauseAxiom c fn cl).pattern →
      (∃ j s, (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i, i < cl.vars.length ∧ k = canonKey c cl.vars i := fun k hk => by
    change k ∈ KoreAML.freeOf [] (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl)) at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · rcases hv.2.2 k hk with h | ⟨i, hi, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, h⟩
    · unfold clauseConcl at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · rw [freeOf_symApp] at hk
        obtain ⟨n, s, hn, rfl⟩ := freeOf_callX _ 0 hk
        exact Or.inl ⟨n, s, hn, by rw [Nat.zero_add]⟩
      · obtain ⟨i, hi, rfl⟩ := freeOf_clauseConclRight hk
        refine Or.inr ⟨i, ?_, rfl⟩
        rcases hi with hi | ⟨u, hu, -⟩
        · exact hrhsv i hi
        · rw [hens] at hu; cases hu
  have hg : ∀ k ∈ ((clauseAxiom c fn cl).sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (clauseAxiom c fn cl).pattern).eraseDups, ∀ m,
      (KoreAML.guardOf t k).interpret I e m := by
    intro k hk m'
    rcases List.mem_append.mp (List.mem_eraseDups.mp hk) with hk | hk
    · obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hk
      rw [mem_one h1]
      show (KoreAML.guardOf t (.sortVar "R")).interpret I e m'
      rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσr2
    · rcases hfree k hk with ⟨j, s, hj, rfl⟩ | ⟨i, hi, rfl⟩
      · rw [KoreAML.interp_guard_evar hD, trSort_srt, hXv j s hj]
        exact (inS_iff e).mpr (hxs j s hj)
      · have hk := canonKey_eq c hi
        rw [hk, KoreAML.interp_guard_evar hD, trSort_srt, ← hk, hVv i hi]
        exact (inS_iff e).mpr (hys i hi)
  have hax := sat_fns hI (Or.inl ⟨_, clause_item_mem hfnm hcl hlow hpre hexs, rfl⟩)
  intro a ha
  have hP := (KoreAML.trAxiom_at hD hax e hg b).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e b
    rw [KoreAML.interp_inhOf_of hRv]; exact hb)
  have hP' : (KoreAML.tr ⟨t, []⟩ (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl))).interpret I e b := hP
  rw [KoreAML.tr, KoreAML.interp_sImp] at hP'
  have hcon := hP'.2 hprem
  unfold clauseConcl at hcon
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσr1) hRv hσr2 hσr2] at hcon
  exact hcon.2 a ha

/-- `kseq`'s signature, as `fixedCtors` gives it. -/
def kseqSigX : CtorSig := ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩

/-- `dotk`'s signature, as `fixedCtors` gives it. -/
def dotkSigX : CtorSig := ⟨dotk, [], Srt.k⟩

omit [Inhabited M] in
theorem lookup_kseqX : lookupSig c.ctorSigs kseq = some kseqSigX := by
  rw [lookupSig_eq]; rfl

omit [Inhabited M] in
theorem lookup_dotkX : lookupSig c.ctorSigs dotk = some dotkSigX := by
  rw [lookupSig_eq]; rfl

omit [Inhabited M] in
theorem patLookup_ofCtorX {f : Sym} {k : CtorSig} (h : lookupSig c.ctorSigs f = some k) :
    lookupSig c.patCtxAll.heads f = some k := by
  simp only [Semantics.patCtxAll, Semantics.patCtx]
  exact lookupSig_append_some (lookupSig_append_some h)

/-- An application of `f` to the formal arguments `X0`, `X1` of sort K, at a valuation that gives
them `x0` and `x1`: `f` applied to them. -/
theorem symApp_x01X {fn : Fn} (hargs : fn.args = [Srt.k, Srt.k]) (hite : (∀ ps, symApp c fn.label ps = .app ⟨⟨c.symName fn.label⟩⟩ [] ps))
    {t : VarTable} {e : Valuation M} {x0 x1 : M}
    (h0 : e.evalEvar (t.ev (.evar ("X" ++ toString 0) (KoreAML.srt (c.sortName Srt.k)))) = x0)
    (h1 : e.evalEvar (t.ev (.evar ("X" ++ toString 1) (KoreAML.srt (c.sortName Srt.k)))) = x1) (m : M) :
    (KoreAML.tr ⟨t, []⟩ (symApp c fn.label
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e m ↔
    SymE I (c.symName fn.label) [x0, x1] m := by
  rw [tr_symApp, symHead_plain_irs hite, trArgs_appList, hargs]
  refine interp_symList _ _ _ (.cons (fun m => ?_) (.cons (fun m => ?_) .nil)) m
  · change m = e.evalEvar (t.ev (.evar ("X" ++ toString 0) (KoreAML.srt (c.sortName Srt.k)))) ↔ _; rw [h0]
  · change m = e.evalEvar (t.ev (.evar ("X" ++ toString 1) (KoreAML.srt (c.sortName Srt.k)))) ↔ _; rw [h1]

/-- **`append(dotk, T) = T`, read at elements**: where `x0` is `dotk`'s element, `f(x0, x1)`
holds only `x1`. -/
theorem appendDot_atX (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    {fn : Fn} (hfnm : fn ∈ c.allFns) (hargs : fn.args = [Srt.k, Srt.k]) (hres : fn.result = Srt.k)
    (hite : (∀ ps, symApp c fn.label ps = .app ⟨⟨c.symName fn.label⟩⟩ [] ps))
    {cl : Clause} (hcl : cl ∈ fn.clauses) (hlow : lowerClauses fn cl = [])
    (hv : cl.vars = [Srt.k]) (hp : cl.pats = [.app dotk [], .var 0]) (hreq : cl.req = none)
    (hr : cl.rhs = .var 0) (hens : cl.ens = none) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {x0 x1 : M} (hx0s : InS I (c.sortName Srt.k) x0)
    (hx0 : GS I (c.sortName Srt.k) (Gen.toK c (.ctor dotkSigX)) [] x0) (hx1 : InS I (c.sortName Srt.k) x1)
    {m : M} (hm : InS I (c.sortName Srt.k) m) (hf : SymE I (c.symName fn.label) [x0, x1] m) : m = x1 := by
  have hD := defOK hI
  have hcd := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σK, hσK1, hσK2⟩ := sortSing hI (hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..))
  rw [hres] at hσK1
  have hinh : ∀ {a : M}, InS I (c.sortName Srt.k) a → Inh I σK a := fun ha =>
    (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσK1).mp ha
  have hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args := by
    rw [hv, hp, hargs]
    simp [sortsOfTerms, sortOfTerm, patLookup_ofCtorX lookup_dotkX, dotkSigX]
  have hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats := by
    intro i hi; rw [hv] at hi; rw [hp, show i = 0 by simpa using hi]; simp [varOccsList, varOccs]
  have hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length := by
    intro i hi; rw [hr] at hi; rw [hv]; simp [varOccs] at hi; simp [hi]
  obtain ⟨hXv, hVv, hRv, hmain⟩ := clause_atElX (xs := [x0, x1]) (ys := [x1]) hI hnn hfnm hcl hlow hpre hexs
    hpats hbinds hreq hens hrhsv (by rw [hres]; exact hσK1) hσK2
    (fun j s hj => by
      rw [hargs] at hj
      match j, hj with
      | 0, hj => simp at hj; subst hj; exact hx0s
      | 1, hj => simp at hj; subst hj; exact hx1)
    (fun i hi => by
      rw [hv] at hi ⊢
      rw [show i = 0 by simpa using hi]; exact hx1)
  generalize KoreAML.tableOf (clauseAxiom c fn cl).sortVars (clauseAxiom c fn cl).pattern = t at hXv hVv hRv hmain
  generalize (valOf t (clauseValElX σK fn.args.length cl.vars.length [x0, x1] [x1]) : Valuation M) = e at hXv hVv hRv hmain
  have hX0 := hXv 0 (c.sortName Srt.k) (by rw [hargs]; rfl)
  have hX1 := hXv 1 (c.sortName Srt.k) (by rw [hargs]; rfl)
  have hV0 := hVv 0 (by rw [hv]; exact Nat.zero_lt_one)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hX0 hX1 hV0
  have hSK : ∀ a, (KoreAML.trSort t (KoreAML.srt (c.sortName Srt.k))).interpret I e a ↔ a = σK := fun a => by
    rw [trSort_srt, KoreAML.interp_sym]; exact hσK1 a
  have hprem : (KoreAML.tr ⟨t, []⟩ (clausePrem c fn cl)).interpret I e x1 := by
    simp only [clausePrem, hargs, hreq, hp, Option.map_none, List.map, Term.koreList]
    unfold premise
    simp only [List.zip, List.zipWith, KoreAML.argsConj, reqPat]
    rw [tr_and2, KoreAML.interp_sAnd, tr_and2, KoreAML.interp_sAnd, tr_and2, KoreAML.interp_sAnd]
    have htop : (KoreAML.tr ⟨t, []⟩ (Kore.Pattern.top KoreAML.R)).interpret I e x1 := by
      rw [KoreAML.tr, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRv]; exact hinh hx1
    have hXe : ∀ (n : Nat) (x a : M), e.evalEvar (t.ev (.evar ("X" ++ toString n) (KoreAML.srt (c.sortName Srt.k)))) = x →
        ((KoreAML.tr ⟨t, []⟩ (KoreAML.ev (toString "X" ++ toString n)
          (KoreAML.srt (c.sortName Srt.k)))).interpret I e a ↔ a = x) := fun n x a hx => by
      rw [← hx]; exact Iff.rfl
    refine ⟨htop, ?_, ?_, htop⟩
    · rw [KoreAML.tr, KoreAML.interp_sIn hD hcd hSK hRv hσK2 hσK2
        (fun a ha => by rw [(hXe 0 x0 a hX0).mp ha]; exact hinh hx0s) x1]
      refine ⟨⟨x0, (hXe 0 x0 x0 hX0).mpr rfl, ?_⟩, hinh hx1⟩
      rw [kore_app_plain hnn.1 lookup_dotkX, Term.koreList, KoreAML.trArgs_nil]
      obtain ⟨a, ha, rfl⟩ := hx0
      exact ha
    · rw [KoreAML.tr, KoreAML.interp_sIn hD hcd hSK hRv hσK2 hσK2
        (fun a ha => by rw [(hXe 1 x1 a hX1).mp ha]; exact hinh hx1) x1]
      refine ⟨⟨x1, (hXe 1 x1 x1 hX1).mpr rfl, ?_⟩, hinh hx1⟩
      rw [tr_var]
      exact hV0.symm
  have hc := (hmain ⟨x1, hinh hx1, hprem⟩ m (hinh hm)).mp ((symApp_x01X hargs hite hX0 hX1 m).mpr hf)
  unfold clauseRight at hc
  rw [hr, hens, tr_and2, KoreAML.interp_sAnd, tr_var] at hc
  exact hc.1.trans hV0

/-- **`append(kseq(I, KS), T) = kseq(I, append(KS, T))`, read at elements**: where `x0` is
`kseq(i, ks)`'s element, an element of `f(x0, x1)` is `kseq(i, a)`'s for an element a of
`f(ks, x1)`. -/
theorem appendKseq_atX (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    {fn : Fn} (hfnm : fn ∈ c.allFns) (hargs : fn.args = [Srt.k, Srt.k]) (hres : fn.result = Srt.k)
    (hite : (∀ ps, symApp c fn.label ps = .app ⟨⟨c.symName fn.label⟩⟩ [] ps))
    {cl : Clause} (hcl : cl ∈ fn.clauses) (hlow : lowerClauses fn cl = [])
    (hv : cl.vars = [Srt.kitem, Srt.k, Srt.k]) (hp : cl.pats = [.app kseq [.var 0, .var 1], .var 2])
    (hreq : cl.req = none) (hr : cl.rhs = .app kseq [.var 0, .app fn.label [.var 1, .var 2]])
    (hens : cl.ens = none) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {x0 x1 i ks : M} (hx0s : InS I (c.sortName Srt.k) x0) (his : InS I (c.sortName Srt.kitem) i)
    (hkss : InS I (c.sortName Srt.k) ks)
    (hx0 : GS I (c.sortName Srt.k) (Gen.toK c (.ctor kseqSigX)) [i, ks] x0) (hx1 : InS I (c.sortName Srt.k) x1)
    {m : M} (hm : InS I (c.sortName Srt.k) m) (hf : SymE I (c.symName fn.label) [x0, x1] m) :
    ∃ a, SymE I (c.symName fn.label) [ks, x1] a ∧ GS I (c.sortName Srt.k) (Gen.toK c (.ctor kseqSigX)) [i, a] m := by
  have hD := defOK hI
  have hcd := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σK, hσK1, hσK2⟩ := sortSing hI (hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..))
  rw [hres] at hσK1
  have hinh : ∀ {a : M}, InS I (c.sortName Srt.k) a → Inh I σK a := fun ha =>
    (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσK1).mp ha
  have hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args := by
    rw [hv, hp, hargs]
    simp [sortsOfTerms, sortOfTerm, patLookup_ofCtorX lookup_kseqX, kseqSigX]
  have hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats := by
    intro i hi; rw [hv] at hi; rw [hp]
    simp only [varOccsList, varOccs, List.mem_append, List.mem_singleton, List.append_nil]
    simp only [List.length_cons, List.length_nil] at hi
    omega
  have hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length := by
    intro i hi; rw [hr] at hi; rw [hv]
    simp only [varOccs, varOccsList, List.mem_append, List.mem_singleton, List.append_nil] at hi
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨hXv, hVv, hRv, hmain⟩ := clause_atElX (xs := [x0, x1]) (ys := [i, ks, x1]) hI hnn hfnm hcl hlow hpre hexs
    hpats hbinds hreq hens hrhsv (by rw [hres]; exact hσK1) hσK2
    (fun j s hj => by
      rw [hargs] at hj
      match j, hj with
      | 0, hj => simp at hj; subst hj; exact hx0s
      | 1, hj => simp at hj; subst hj; exact hx1)
    (fun j hj => by
      rw [hv] at hj ⊢
      match j, hj with
      | 0, _ => exact his
      | 1, _ => exact hkss
      | 2, _ => exact hx1)
  generalize KoreAML.tableOf (clauseAxiom c fn cl).sortVars (clauseAxiom c fn cl).pattern = t at hXv hVv hRv hmain
  generalize (valOf t (clauseValElX σK fn.args.length cl.vars.length [x0, x1] [i, ks, x1]) : Valuation M) = e
    at hXv hVv hRv hmain
  have hX0 := hXv 0 (c.sortName Srt.k) (by rw [hargs]; rfl)
  have hX1 := hXv 1 (c.sortName Srt.k) (by rw [hargs]; rfl)
  have hV0 := hVv 0 (by rw [hv]; decide)
  have hV1 := hVv 1 (by rw [hv]; decide)
  have hV2 := hVv 2 (by rw [hv]; decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hX0 hX1 hV0 hV1 hV2
  have hSK : ∀ a, (KoreAML.trSort t (KoreAML.srt (c.sortName Srt.k))).interpret I e a ↔ a = σK := fun a => by
    rw [trSort_srt, KoreAML.interp_sym]; exact hσK1 a
  have hvar : ∀ (j : Nat) (x a : M), e.evalEvar (t.ev (canonKey c cl.vars j)) = x →
      ((KoreAML.tr ⟨t, []⟩ (Term.kore c (canonVars c cl.vars) (.var j))).interpret I e a ↔ a = x) :=
    fun j x a hx => by rw [tr_var, ← hx]; exact Iff.rfl
  have hprem : (KoreAML.tr ⟨t, []⟩ (clausePrem c fn cl)).interpret I e x1 := by
    simp only [clausePrem, hargs, hreq, hp, Option.map_none, List.map, Term.koreList]
    unfold premise
    simp only [List.zip, List.zipWith, KoreAML.argsConj, reqPat]
    rw [tr_and2, KoreAML.interp_sAnd, tr_and2, KoreAML.interp_sAnd, tr_and2, KoreAML.interp_sAnd]
    have htop : (KoreAML.tr ⟨t, []⟩ (Kore.Pattern.top KoreAML.R)).interpret I e x1 := by
      rw [KoreAML.tr, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRv]; exact hinh hx1
    have hXe : ∀ (n : Nat) (x a : M), e.evalEvar (t.ev (.evar ("X" ++ toString n) (KoreAML.srt (c.sortName Srt.k)))) = x →
        ((KoreAML.tr ⟨t, []⟩ (KoreAML.ev (toString "X" ++ toString n)
          (KoreAML.srt (c.sortName Srt.k)))).interpret I e a ↔ a = x) := fun n x a hx => by
      rw [← hx]; exact Iff.rfl
    refine ⟨htop, ?_, ?_, htop⟩
    · rw [KoreAML.tr, KoreAML.interp_sIn hD hcd hSK hRv hσK2 hσK2
        (fun a ha => by rw [(hXe 0 x0 a hX0).mp ha]; exact hinh hx0s) x1]
      refine ⟨⟨x0, (hXe 0 x0 x0 hX0).mpr rfl, ?_⟩, hinh hx1⟩
      rw [kore_app_plain hnn.1 lookup_kseqX, trArgs_appList]
      simp only [Term.koreList, List.map]
      rw [interp_appList_sing _ _ [i, ks] (.cons (hvar 0 i · hV0) (.cons (hvar 1 ks · hV1) .nil))]
      exact hx0
    · rw [KoreAML.tr, KoreAML.interp_sIn hD hcd hSK hRv hσK2 hσK2
        (fun a ha => by rw [(hXe 1 x1 a hX1).mp ha]; exact hinh hx1) x1]
      refine ⟨⟨x1, (hXe 1 x1 x1 hX1).mpr rfl, (hvar 2 x1 x1 hV2).mpr rfl⟩, hinh hx1⟩
  have hc := (hmain ⟨x1, hinh hx1, hprem⟩ m (hinh hm)).mp ((symApp_x01X hargs hite hX0 hX1 m).mpr hf)
  unfold clauseRight at hc
  rw [hr, hens, tr_and2, KoreAML.interp_sAnd] at hc
  have hc1 := hc.1
  rw [kore_app_plain hnn.1 lookup_kseqX, trArgs_appList, interp_appList] at hc1
  obtain ⟨h, hh, bs, hbs, happ⟩ := hc1
  simp only [Term.koreList, List.map] at hbs
  cases hbs with
  | cons hb0 hbs => cases hbs with
    | cons hb1 hbs => cases hbs with
      | nil =>
        rw [(hvar 0 i _ hV0).mp hb0] at happ
        refine ⟨_, ?_, h, hh, happ⟩
        rw [kore_app, tr_symApp, symHead_plain_irs hite, trArgs_appList] at hb1
        simp only [Term.koreList, List.map] at hb1
        exact (interp_symList _ _ [ks, x1] (.cons (hvar 1 ks · hV1) (.cons (hvar 2 x1 · hV2) .nil)) _).mp hb1


/-- No function overload covers any arguments of a constructor. -/
theorem fnCover_ctorX [hO : OvlOK c] (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {k : CtorSig} (hk : k ∈ c.ctorSigs) (ws : List GroundTerm) : c.fnCover k.name ws = none := by
  refine OvlLaws.fnCover_none_of_not_fnOvl (fun hm => ?_) ws
  unfold Semantics.fnOvlSyms at hm
  obtain ⟨o, ho, hn⟩ := List.mem_map.mp hm
  have h1 := (hO.hyp htr).fnFacts.isOvl o (List.mem_filter.mp ho).1
  rw [hn, isOvl_of_ctorSigs hk] at h1
  cases h1

/-- A function's application to elements of its argument sorts gives elements of its result sort. -/
theorem symE_arityX (hI : I ⊧ᴵP Γ c) {fn : Fn} (hfnm : fn ∈ c.allFns) (hite : (∀ ps, symApp c fn.label ps = .app ⟨⟨c.symName fn.label⟩⟩ [] ps))
    {xs : List M} (hxs : All2 (fun s x => InS I s x) (fn.args.map c.sortName) xs) {a : M}
    (ha : SymE I (c.symName fn.label) xs a) : InS I (c.sortName fn.result) a := by
  have h := symArity_at hI (fn_sig_mem hfnm) KoreAML.val0 a (by
    obtain ⟨h0, hh0, happ⟩ := ha
    rw [interp_appList]
    refine ⟨h0, by show (symHead c fn.label).interpret I KoreAML.val0 h0; rw [symHead_plain_irs hite]; exact hh0, xs, ?_, happ⟩
    show All2 _ ((fn.args.map c.sortName).map _) xs
    clear happ
    generalize fn.args.map c.sortName = ss at hxs ⊢
    induction hxs with
    | nil => exact .nil
    | cons hx _ ih =>
      refine .cons ?_ ih
      show (KoreAML.inhOf (KoreAML.trSort [] (KoreAML.srt _))).interpret I KoreAML.val0 _
      rw [trSort_srt]; exact hx)
  exact h

/-- **K's `append` at a value, from its clauses**: in a model of `Γ`, where a value's element of
sort K is in `f(x0, x1)` for elements x0, x1 of K, x0 and x1 are values' elements of sort K. By
induction on the value, splitting x0 by K's no-junk item. -/
theorem appendHeld_backCoreX (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hg : genWf c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) (hn : Model.NamesApartK c)
    (hrw : ∀ k ∈ c.params, k.raw = true → instDecode? (c.symName k.sig.name) = none)
    (hK : Srt.k ∈ consSorts c) (hgens : c.gens Srt.k = [.ctor kseqSigX, .ctor dotkSigX])
    {fn : Fn} (hfnm : fn ∈ c.allFns) (hargs : fn.args = [Srt.k, Srt.k]) (hres : fn.result = Srt.k)
    (hite : (∀ ps, symApp c fn.label ps = .app ⟨⟨c.symName fn.label⟩⟩ [] ps))
    {cd ck : Clause} (hcd : cd ∈ fn.clauses) (hck : ck ∈ fn.clauses)
    (hld : lowerClauses fn cd = []) (hlk : lowerClauses fn ck = [])
    (hdv : cd.vars = [Srt.k]) (hdp : cd.pats = [.app dotk [], .var 0]) (hdq : cd.req = none)
    (hdr : cd.rhs = .var 0) (hde : cd.ens = none) (hdpre : cd.pre = .top) (hdx : cd.exs = [])
    (hkv : ck.vars = [Srt.kitem, Srt.k, Srt.k]) (hkp : ck.pats = [.app kseq [.var 0, .var 1], .var 2])
    (hkq : ck.req = none) (hkr : ck.rhs = .app kseq [.var 0, .app fn.label [.var 1, .var 2]])
    (hke : ck.ens = none) (hkpre : ck.pre = .top) (hkx : ck.exs = []) :
    ∀ {w : GroundTerm}, c.sortOf w = some Srt.k → ∀ {x0 x1 : M}, InS I (c.sortName Srt.k) x0 →
      InS I (c.sortName Srt.k) x1 → SymE I (c.symName fn.label) [x0, x1] (elemOf c I w) →
      ∃ v0 v1, c.sortOf v0 = some Srt.k ∧ c.sortOf v1 = some Srt.k ∧ x0 = elemOf c I v0 ∧ x1 = elemOf c I v1 := by
  have hD := defOK hI
  have hnj : ∀ {x : M}, InS I (c.sortName Srt.k) x → ∃ g ∈ (c.gens Srt.k).map (Gen.toK c), ∃ xs,
      All2 (fun s y => InS I s y) g.argSorts xs ∧ GS I (c.sortName Srt.k) g xs x := fun hx =>
    noJunk_elim hD (sat_cons hI (Or.inl ⟨_, noJunkItem_mem hK (by rw [hgens]; rfl), rfl⟩)) hx
  rw [hgens] at hnj
  have hmemK : Gen.ctor kseqSigX ∈ c.gens Srt.k := by rw [hgens]; exact List.mem_cons_self ..
  have hmemD : Gen.ctor dotkSigX ∈ c.gens Srt.k := by rw [hgens]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hkm : kseqSigX ∈ c.ctorSigs := (lookupSig_spec (lookup_kseqX (c := c))).1
  have hdm : dotkSigX ∈ c.ctorSigs := (lookupSig_spec (lookup_dotkX (c := c))).1
  suffices H : ∀ (n : Nat) (w : GroundTerm), sizeOf w ≤ n → c.sortOf w = some Srt.k → ∀ {x0 x1 : M},
      InS I (c.sortName Srt.k) x0 → InS I (c.sortName Srt.k) x1 → SymE I (c.symName fn.label) [x0, x1] (elemOf c I w) →
      ∃ v0 v1, c.sortOf v0 = some Srt.k ∧ c.sortOf v1 = some Srt.k ∧ x0 = elemOf c I v0 ∧ x1 = elemOf c I v1 from
    fun {w} => H _ w (Nat.le_refl _)
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro w hle hw x0 x1 hx0 hx1 hf
  obtain ⟨g, hgm, xs, hxs, hgs⟩ := hnj hx0
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hgm
  rcases hgm with rfl | rfl
  · -- x0 is `kseq(i, ks)`
    rw [toK_argSorts] at hxs
    obtain ⟨i, ks, rfl, hi, hks⟩ : ∃ i ks, xs = [i, ks] ∧ InS I (c.sortName Srt.kitem) i ∧ InS I (c.sortName Srt.k) ks := by
      cases hxs with
      | cons h1 h2 => cases h2 with
        | cons h2 h3 => cases h3 with
          | nil => exact ⟨_, _, rfl, h1, h2⟩
    obtain ⟨a, ha, hka⟩ := appendKseq_atX hI hnn hfnm hargs hres hite hck hlk hkv hkp hkq hkr hke hkpre hkx
      hx0 hi hks hgs hx1 ((elemOf_spec hI hw KoreAML.val0).2) hf
    have has : InS I (c.sortName Srt.k) a := by
      have := symE_arityX hI hfnm hite (xs := [ks, x1]) (by rw [hargs]; exact .cons hks (.cons hx1 .nil)) ha
      rwa [hres] at this
    obtain ⟨ws, rfl, hws, hbs⟩ := ctor_back hI hg htr (lookup_kseqX (c := c)) hw (bs := [i, a]) rfl
      (fun j x s hj hs => by
        match j, hj, hs with
        | 0, hj, hs => simp [kseqSigX] at hj hs; subst hj hs; exact hi
        | 1, hj, hs => simp [kseqSigX] at hj hs; subst hj hs; exact has) hka
    obtain ⟨v, W, rfl, hv, hW⟩ : ∃ v W, ws = [v, W] ∧ c.sortOf v = some Srt.kitem ∧ c.sortOf W = some Srt.k := by
      cases ws with
      | nil => cases hws
      | cons v ws' =>
        obtain ⟨hv, hws'⟩ := OvlLaws.sortsOf_cons_iff.mp hws
        cases ws' with
        | nil => cases hws'
        | cons W ws'' =>
          obtain ⟨hW, hws''⟩ := OvlLaws.sortsOf_cons_iff.mp hws'
          rw [sortsOf_nil_eq hws'']
          exact ⟨v, W, rfl, hv, hW⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hbs
    obtain ⟨rfl, rfl⟩ := hbs
    have hlt : sizeOf W < n := Nat.lt_of_lt_of_le (by simp; omega) hle
    obtain ⟨u0, u1, hu0, hu1, rfl, rfl⟩ := ih _ hlt W (Nat.le_refl _) hW hks hx1 ha
    obtain ⟨v0, hv0, rfl⟩ := gen_value hI htr hn hrw hmemK (ws := [v, u0])
      (by simp only [Gen.argSorts, kseqSigX]; exact OvlLaws.sortsOf_cons_iff.mpr ⟨hv, OvlLaws.sortsOf_cons_iff.mpr ⟨hu0, rfl⟩⟩)
      (fun k hk => by cases hk; exact fnCover_ctorX htr hkm _) hgs
    exact ⟨v0, u1, hv0, hu1, rfl, rfl⟩
  · -- x0 is `dotk`
    obtain rfl : xs = [] := by cases hxs; rfl
    have hm := appendDot_atX hI hnn hfnm hargs hres hite hcd hld hdv hdp hdq hdr hde hdpre hdx hx0 hgs hx1
      ((elemOf_spec hI hw KoreAML.val0).2) hf
    obtain ⟨v0, hv0, rfl⟩ := gen_value hI htr hn hrw hmemD (ws := [])
      (by simp only [Gen.argSorts, dotkSigX]; rfl) (fun k hk => by cases hk; exact fnCover_ctorX htr hdm _) hgs
    exact ⟨v0, w, hv0, hw, rfl, hm.symm⟩


omit [Inhabited M] in
/-- What `Clause.appendDotX` checks. -/
theorem appendDotX_spec {cl : Clause} (h : cl.appendDotX = true) :
    cl.vars = [Srt.k] ∧ cl.pats = [.app dotk [], .var 0] ∧ cl.req = none ∧ cl.rhs = .var 0 ∧ cl.ens = none ∧
      cl.pre = .top ∧ cl.exs = [] := by
  unfold Clause.appendDotX at h
  split at h
  · rename_i s d hv hp hq hr he hx hpre hpost
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hv, hp, hq, hr, he, hpre, hx⟩
  · cases h

omit [Inhabited M] in
/-- What `Clause.appendKseqX` checks. -/
theorem appendKseqX_spec {f : Sym} {cl : Clause} (h : cl.appendKseqX f = true) :
    cl.vars = [Srt.kitem, Srt.k, Srt.k] ∧ cl.pats = [.app kseq [.var 0, .var 1], .var 2] ∧ cl.req = none ∧
      cl.rhs = .app kseq [.var 0, .app f [.var 1, .var 2]] ∧ cl.ens = none ∧ cl.pre = .top ∧ cl.exs = [] := by
  unfold Clause.appendKseqX at h
  split at h
  · rename_i s0 s1 s2 k0 k1 g hv hp hq hr he hx hpre hpost
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
    exact ⟨hv, hp, hq, hr, he, hpre, hx⟩
  · cases h

omit [Inhabited M] in
/-- What `Semantics.appendHeldX` checks. -/
theorem appendHeldX_spec {f : Sym} (h : c.appendHeldX f = true) :
    isHook f = false ∧ c.isParam f = false ∧ instDecode? (c.symName f) = none ∧ Srt.k ∈ consSorts c ∧
      c.gens Srt.k = [.ctor kseqSigX, .ctor dotkSigX] ∧
      ∃ fn, c.lookupFn f = some fn ∧ fn.args = [Srt.k, Srt.k] ∧ fn.result = Srt.k ∧
        ∃ cd ck, cd ∈ fn.clauses ∧ ck ∈ fn.clauses ∧ lowerClauses fn cd = [] ∧ lowerClauses fn ck = [] ∧
          cd.appendDotX = true ∧ ck.appendKseqX f = true := by
  unfold Semantics.appendHeldX at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨hh, hp⟩, hite⟩, hK⟩, hgm⟩, hfm⟩ := h
  refine ⟨hh, hp, hite, hK, ?_, ?_⟩
  · split at hgm
    · rename_i a b hgs
      simp only [Bool.and_eq_true, beq_iff_eq] at hgm
      obtain ⟨rfl, rfl⟩ := hgm
      exact hgs
    · cases hgm
  · split at hfm
    · rename_i fn hfn
      simp only [Bool.and_eq_true, beq_iff_eq] at hfm
      obtain ⟨⟨hargs, hres⟩, hcm⟩ := hfm
      refine ⟨fn, hfn, hargs, hres, ?_⟩
      split at hcm
      · rename_i a b hcl
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcm
        obtain ⟨hpr, hab⟩ := hcm
        have hlow : ∀ cl ∈ fn.clauses, cl.prio = a.prio → lowerClauses fn cl = [] := by
          intro cl _ hcp
          simp [lowerClauses, hcl, hcp, hpr]
        have ha : a ∈ fn.clauses := by rw [hcl]; exact List.mem_cons_self ..
        have hb : b ∈ fn.clauses := by rw [hcl]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        rcases hab with ⟨hd, hk⟩ | ⟨hd, hk⟩
        · exact ⟨a, b, ha, hb, hlow a ha rfl, hlow b hb hpr.symm, hd, hk⟩
        · exact ⟨b, a, hb, ha, hlow b hb hpr.symm, hlow a ha rfl, hd, hk⟩
      · cases hcm
    · cases hfm

omit [Inhabited M] in
/-- `symApp` writes the symbol `appendHeldX` accepts at its name, at no sort. This is the one lemma
that reads `appendHeldX`'s condition on the name. -/
theorem appendHeldX_writes_irs {f : Sym} (h : c.appendHeldX f = true) :
    ∀ ps, symApp c f ps = .app ⟨⟨c.symName f⟩⟩ [] ps := by
  intro ps; exact symApp_noInst (appendHeldX_spec h).2.2.1

/-- **K's `append` has `HeldBack`** in a model of `Γ`: a symbol `appendHeldX` accepts, with the
signature a right side's context gives it. -/
theorem appendHeld_backX (hI : I ⊧ᴵP Γ c) [OvlOK c] (hsc : SortCtx c) (hnn : NamesNumbered c)
    (hg : genWf c = true) (hn : Model.NamesApartK c)
    (hrw : ∀ k ∈ c.params, k.raw = true → instDecode? (c.symName k.sig.name) = none)
    {f : Sym} {k : CtorSig} (hc : c.isCtor f = false) (hh : c.appendHeldX f = true)
    (hk : lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k) : HeldBack c I f k := by
  have hite := appendHeldX_writes_irs hh
  obtain ⟨hhk, hpa, -, hK, hgens, fn, hfn, hargs, hres, cd, ck, hcd, hck, hld, hlk, hd, hkk⟩ :=
    appendHeldX_spec hh
  obtain ⟨fn', hfnm, rfl, hfn'⟩ := rhs_lookup_call hsc fns_headsOK hc hhk hpa (by rw [hfn]; simp) hk
  rw [hfn] at hfn'
  cases hfn'
  obtain ⟨-, hlab⟩ := lookupFn_spec hfn
  subst hlab
  obtain ⟨hdv, hdp, hdq, hdr, hde, hdpre, hdx⟩ := appendDotX_spec hd
  obtain ⟨hkv, hkp, hkq, hkr, hke, hkpre, hkx⟩ := appendKseqX_spec hkk
  refine ⟨hite, fun {w} hw {bs} hbl hbs hm => ?_⟩
  simp only [Fn.sig] at hw hbl hbs ⊢
  rw [hres] at hw
  rw [hargs] at hbl hbs ⊢
  obtain ⟨x0, x1, rfl⟩ : ∃ x0 x1, bs = [x0, x1] := by
    match bs, hbl with
    | [x0, x1], _ => exact ⟨x0, x1, rfl⟩
  have hx0 := hbs 0 x0 _ rfl rfl
  have hx1 := hbs 1 x1 _ rfl rfl
  obtain ⟨v0, v1, hv0, hv1, rfl, rfl⟩ := appendHeld_backCoreX (I := I) hI hnn hg hsc.trans hn hrw hK hgens hfnm hargs hres hite
    hcd hck hld hlk hdv hdp hdq hdr hde hdpre hdx hkv hkp hkq hkr hke hkpre hkx hw hx0 hx1 hm
  exact ⟨[v0, v1], OvlLaws.sortsOf_cons_iff.mpr ⟨hv0, OvlLaws.sortsOf_cons_iff.mpr ⟨hv1, rfl⟩⟩, rfl⟩


end

end Faithful

end KCore
