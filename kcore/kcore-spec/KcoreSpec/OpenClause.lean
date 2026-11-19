/-
  KCore. A clause whose patterns need not bind every variable, in any model of `Γc c`.

  The clause facts are asked as decided conditions of their own (SortedCl.lean):
  - `Semantics.clauseSortedOpen`: `clauseSorted` with "each variable occurs in the clause" (its
    patterns, conditions, right side, `ensures` or right side's predicate) in place of "the patterns
    bind each variable";
  - `Semantics.clausePlainOpen`: no existential variable and the right side's predicate `\top`, with
    what `clausesPlain` asks of a clause's premise and of its open condition variables: none, or
    closed conditions, or each of a confined sort.

  A clause's exclusion `∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄` binds the variables of its patterns and
  conditions (`leftVars`) only. At an element of it, those binders are elements of their sorts:
  the patterns' variables are values' (`patVals_backC`); an open condition variable is a value's
  where its sort is confined (`confined_value`). So where every open condition variable is of a
  confined sort, the binders give a substitution of values at which the clause fails, and the
  model's reading of its `requires` there (`ModelFailsCl`) makes `⌈req = true⌉` empty. Otherwise
  the conditions are closed and `needsWitness` holds, so they are decided: `Witnessed` with the
  patterns' match is a substitution of values at which the clause fails (`Fails`), so its
  `requires` there has a result other than `true`, while the witness's `requires` has no result but
  `true`, and the two read the same values; and `Refuted` fails where the conditions hold at the binders
  (`Clause.not_refuted_at`). This is `exclEmptyCl_of`. The variables outside `leftVars` are given
  Bool and `true` (`Clause.leftSortsB`, `fillV`).

  Where the clause's predicate is not `\top` the exclusion's body carries it at `R` (`withPre`), and
  the clause fails also where `Holds` gives its predicate `false` (`ReqFails.pre`): that truth value
  with its terms' readings in the model (`HoldsRead`, `ModelFailsCl`'s second case) read at `R`
  (`PreRead.atR`) makes
  the predicate empty; a clause with a predicate other than `\top` is not one whose conditions need
  a witness (`needsWitness`); and the predicate at the binders moves to Bool (`PreRead.toBool`)
  against `Refuted`.

  `ModelFailsCl` is a hypothesis of `exclEmptyCl_of`, as `ModelFails` is of `ExclEmpty`: the
  evaluation lemmas give it, and for a semantics `coreOK` accepts it follows from `Fails`
  (`modelFailsCl_of_core`, through `evalTerm_den4`).
-/
import KcoreSpec.OpenCompete
import KcoreSpec.ModelFns
import KcoreSpec.ClausePreRead

set_option autoImplicit false

namespace KCore

theorem mem_varOccsList_of_getCl : ∀ {ps : List Term} {j : Nat} {q : Term} {i : Nat}, ps[j]? = some q →
    i ∈ varOccs q → i ∈ varOccsList ps
  | [], _, _, _, h, _ => by simp at h
  | p :: ps, 0, q, i, h, hi => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; rw [varOccsList]; exact List.mem_append_left _ hi
  | p :: ps, j + 1, q, i, h, hi => by
    rw [varOccsList]; exact List.mem_append_right _ (mem_varOccsList_of_getCl (by simpa using h) hi)

/-- The sorts of the clause's variables, each variable that neither the patterns nor the
conditions hold given Bool. -/
def Clause.leftSortsB (cl : Clause) : List Srt :=
  (List.range cl.vars.length).map fun i => if cl.leftVars.contains i then cl.vars.getD i 0 else Srt.bool

theorem Clause.leftSortsB_length (cl : Clause) : cl.leftSortsB.length = cl.vars.length := by
  simp [Clause.leftSortsB]

theorem Clause.leftSortsB_getElem? {cl : Clause} {i : Nat} (hi : i < cl.vars.length) (hl : i ∈ cl.leftVars) :
    cl.leftSortsB[i]? = cl.vars[i]? := by
  simp [Clause.leftSortsB, hi, hl, List.getD_eq_getElem?_getD]

theorem Clause.leftSortsB_getD {cl : Clause} {i : Nat} (hi : i < cl.vars.length) (hl : i ∈ cl.leftVars) :
    cl.leftSortsB.getD i 0 = cl.vars.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, cl.leftSortsB_getElem? hi hl]

theorem Clause.leftSortsB_getD_off {cl : Clause} {i : Nat} (hi : i < cl.vars.length) (hl : i ∉ cl.leftVars) :
    cl.leftSortsB.getD i 0 = Srt.bool := by
  simp [Clause.leftSortsB, hi, hl, List.getD_eq_getElem?_getD]

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-- A clause's exclusion under its canonical presentation, its predicate `\top`:
`∃x̄'. ⌈req = true⌉ ∧ X̄ ∈ p̄`, x̄' the variables of its patterns and conditions. -/
theorem exclusion_canonCl (c : Semantics) (fn : Fn) (cl : Clause) (hpre : cl.pre = .top) :
    exclusion c fn cl (canonClausePres cl) = KoreAML.existsAll KoreAML.R
      ((((List.range cl.vars.length).filter cl.leftVars.contains).filterMap ((canonVars c cl.vars)[·]?)).map
        KoreAML.Var.kore)
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) :=
  congrArg (KoreAML.existsAll KoreAML.R _) (withPre_top hpre)

/-- A clause's exclusion under its canonical presentation: `∃x̄'. (⌈req = true⌉ ∧ X̄ ∈ p̄) ∧ pre`, x̄'
the variables of its patterns and conditions, without the predicate where it is `\top`
(`withPre`). -/
theorem exclusion_canonPre (c : Semantics) (fn : Fn) (cl : Clause) :
    exclusion c fn cl (canonClausePres cl) = KoreAML.existsAll KoreAML.R
      ((((List.range cl.vars.length).filter cl.leftVars.contains).filterMap ((canonVars c cl.vars)[·]?)).map
        KoreAML.Var.kore)
      (withPre c (canonVars c cl.vars) cl
        (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
          (Term.koreList c (canonVars c cl.vars) cl.pats))) := rfl

/-- **The clause fails in the model at the substitutions of values on its patterns and
conditions**: under every σ well sorted over a list of sorts that agrees with the clause's at the
variables of its patterns and conditions, under which the patterns denote `ws`: at every valuation
that agrees with σ, the clause has a `requires` whose translation denotes a result other than
`true`; or its predicate is not `\top` and `Holds` gives it the truth value `false` under σ with
the reading in I of each term it evaluates (`HoldsRead`). `ModelFails` with the clause's other
variables at any sort. -/
def ModelFailsCl {M : Type} (c : Semantics) (I : Interpretation KoreAML.Sym M) (cl : Clause) (ws : List GroundTerm) :
    Prop :=
  ∀ vars : List Srt, vars.length = cl.vars.length → (∀ i ∈ cl.leftVars, vars[i]? = cl.vars[i]?) →
  ∀ σ, c.WellSorted vars σ → PatVals c σ cl.pats ws →
    (∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ e →
      ∃ t r, cl.req = some t ∧ r ≠ some (bool true) ∧ (∀ v, r = some v → c.sortOf v = some Srt.bool) ∧
        ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r m) ∨
    (cl.pre ≠ .top ∧ HoldsShape.HoldsRead c I cl.vars.length σ cl.pre false)

/-- **A clause's exclusion is empty where it fails**, in the model `I`: at arguments of `fn`'s
sorts where the clause fails (`Fails`, and in the model `ModelFailsCl`), its exclusion is empty, at
a valuation that gives each formal argument `Xⱼ` the argument's element and `R` a sort. Only the
keys of the variables of its patterns and conditions, and of the variables of its predicate's
pattern where the predicate is not `\top`, are asked of the table. `ExclEmpty` for a clause whose
patterns need not bind every variable. -/
def ExclEmptyCl {M : Type} [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (fn : Fn) (cl : Clause) :
    Prop :=
  ∀ {ws : List GroundTerm}, c.sortsOf ws = some fn.args → Fails c ws cl → ModelFailsCl c I cl ws →
    ∀ {tbl : VarTable}, (∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl) →
    (cl.pre.isTop = false →
      ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
    (∀ (j : Nat) s, fn.args[j]? = some s → VarKey.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)) ∈ tbl) →
    VarKey.sortVar "R" ∈ tbl →
    ∀ {e : Valuation M}, (∀ (j : Nat) w s, ws[j]? = some w → fn.args[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = elemOf c I w) →
    ∀ {σR : M}, e.evalEvar (tbl.ev (.sortVar "R")) = σR → IsSort I σR →
    ∀ m, ¬ (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret I e m

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
theorem fillV_keyCl {tbl : VarTable} {vars : List Srt} {is : List Nat} {a : M} {e : Valuation M} {k : VarKey}
    (hk : k ∈ tbl) (hne : ∀ i < vars.length, k ≠ canonKey c vars i) :
    (fillV c tbl vars is a e).evalEvar (tbl.ev k) = e.evalEvar (tbl.ev k) := by
  show (if _ then _ else _) = _
  rw [if_neg]
  rintro ⟨i, hi, -, he⟩
  exact ev_ne hk (hne i hi) he

/-- **`⌈t = true⌉` at a sort S, under two tables**: where two valuations give each variable of t
one element and S one sort, the translations denote one set. -/
theorem reqPat_congrCl (hI : I ⊧ᴵP Γ c) [OvlOK c] {vs : List KoreAML.Var} {tbl tbl' : VarTable}
    {e e' : Valuation M} {S : Kore.KSort} {σS : M} (hS : ∀ a, (KoreAML.trSort tbl S).interpret I e a ↔ a = σS)
    (hS' : ∀ a, (KoreAML.trSort tbl' S).interpret I e' a ↔ a = σS) (hσS : IsSort I σS) {t : Term}
    (h : ∀ i ∈ varOccs t, e.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl'.ev (keyAt vs i))) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c vs t)))).interpret I e m ↔
      (KoreAML.tr ⟨tbl', []⟩ (reqPat S (some (Term.kore c vs t)))).interpret I e' m := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  simp only [reqPat]
  rw [KoreAML.tr, KoreAML.tr,
    KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hS hσB2 hσS,
    KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hS' hσB2 hσS]
  refine and_congr Iff.rfl (forall_congr' fun a => imp_congr_right fun _ => ?_)
  rw [KoreAML.tr_dv, KoreAML.tr_dv]
  exact iff_congr (tr_kore_congr t h a) (((Closed.sym _).app (Closed.sym _)).interp e e' a)

/-- **`⌈φ = true⌉` read at another sort**: the predicate holds at every element of a sort where it
holds at one element of another. -/
theorem reqPat_resortCl (hI : I ⊧ᴵP Γ c) [OvlOK c] {tbl : VarTable} {e : Valuation M} {S S' : Kore.KSort}
    {σS σS' : M} (hS : ∀ a, (KoreAML.trSort tbl S).interpret I e a ↔ a = σS) (hσS : IsSort I σS)
    (hS' : ∀ a, (KoreAML.trSort tbl S').interpret I e a ↔ a = σS') (hσS' : IsSort I σS')
    {tp : Kore.Pattern} {m m' : M} (hm' : Inh I σS' m')
    (h : (KoreAML.tr ⟨tbl, []⟩ (reqPat S (some tp))).interpret I e m) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat S' (some tp))).interpret I e m' := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  simp only [reqPat] at h ⊢
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hS hσB2 hσS] at h
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hS' hσB2 hσS']
  exact ⟨hm', h.2⟩

/-- `⌈req = true⌉`, or `⊤` without a `requires`, at a sort holds at elements of that sort only. -/
theorem reqPat_inhCl (hI : I ⊧ᴵP Γ c) [OvlOK c] {tbl : VarTable} {e : Valuation M} {S : Kore.KSort} {σS : M}
    (hS : ∀ a, (KoreAML.trSort tbl S).interpret I e a ↔ a = σS) (hσS : IsSort I σS)
    (hfree : (KoreAML.trSort tbl S).isFreeEvar KoreAML.topVar = false) {req : Option Kore.Pattern} {m : M}
    (h : (KoreAML.tr ⟨tbl, []⟩ (reqPat S req)).interpret I e m) : Inh I σS m := by
  have hD := defOK hI
  cases req with
  | none =>
    simp only [reqPat] at h
    rw [KoreAML.tr, KoreAML.interp_sTop hD hfree] at h
    exact (KoreAML.interp_inhOf_of hS).mp h
  | some tp =>
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
    rw [sortName_bool] at hσB1
    simp only [reqPat] at h
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hS hσB2 hσS] at h
    exact h.1

/-- **A clause's conditions that hold are not refuted.** In a model of `Γc`, where `⌈req = true⌉`
holds, at some sort, at a valuation of the conditions' variables in their sorts, and the clause's
predicate (where it is not `\top`) holds at Bool at every valuation that gives its variables the
same elements, the clause's conditions `∃ō. (⌈req = true⌉ ∧ pre)` (`Clause.condK`) are satisfied at
Bool, so `Clause.Refuted` fails. -/
theorem Clause.not_refuted_at (hI : I ⊧ᴵP Γc c) [OvlOK c] {cl : Clause} (hpreOK : c.condOK cl.vars cl.pre = true)
    {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < cl.vars.length, i ∈ cl.condVars → InS I (c.sortName (cl.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i))))
    (hlt : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {S : Kore.KSort} {σS : M} (hS : ∀ a, (KoreAML.trSort tbl S).interpret I e a ↔ a = σS) (hσS : IsSort I σS)
    {m : M} (hm : ∀ t, cl.req = some t →
      (KoreAML.tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c (canonVars c cl.vars) t)))).interpret I e m)
    (hpreB : cl.pre.isTop = false → ∀ (tbl2 : VarTable) (e2 : Valuation M) (mB : M),
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c Srt.bool) cl.pre), k ∈ tbl2) →
      (∀ i ∈ varOccsCond cl.vars.length cl.pre,
        e.evalEvar (tbl.ev (canonKey c cl.vars i)) = e2.evalEvar (tbl2.ev (canonKey c cl.vars i))) →
      (KoreAML.inhOf (KoreAML.trSort tbl2 (srtOf c Srt.bool))).interpret I e2 mB →
      (KoreAML.tr ⟨tbl2, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c Srt.bool) cl.pre)).interpret I e2 mB) :
    ¬ cl.Refuted c := by
  intro href
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hD := defOK hIΓ
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hIΓ (bool_numbered (c := c))
  let B := srtOf c Srt.bool
  let vs := canonVars c cl.vars
  let l := (List.range cl.vars.length).filter cl.condVars.contains
  have hl : ∀ i ∈ l, i < cl.vars.length := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  have hK : cl.condK c = KoreAML.existsAll B ((l.map (vs.getD · default)).map KoreAML.Var.kore)
      (.and B ([reqPat B (cl.req.map (Term.kore c vs))] ++ Cond.conj c vs B cl.pre)) :=
    congrArg (fun (bs : List KoreAML.Var) => KoreAML.existsAll B (bs.map KoreAML.Var.kore)
      (.and B ([reqPat B (cl.req.map (Term.kore c vs))] ++ Cond.conj c vs B cl.pre))) hbs
  unfold Clause.Refuted at href
  rw [hK] at href
  unfold KoreAML.denB at href
  generalize htbl : KoreAML.tableOf [] _ = tbl2 at href
  have hkeys2 : ∀ i < cl.vars.length, i ∈ l → canonKey c cl.vars i ∈ tbl2 := fun i _ hil => by
    rw [← htbl]; unfold KoreAML.tableOf canonKey
    exact List.mem_eraseDups.mpr (List.mem_append_right _
      (mem_varsOf_existsAll (List.mem_map_of_mem (List.mem_map_of_mem hil))))
  let e' := moveV c tbl tbl2 cl.vars l e
  let mB := elemOf c I (bool true)
  have hneg := href hI e' mB
  rw [interpret_neg] at hneg
  apply hneg
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl2.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys2 i (hl i hi) hi) (hkeys2 j (hl j hj) hj) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  refine existsAll_intro_at hD _ e' e' mB hnd hsrt (fun _ _ => rfl) rfl (fun b hb n hn => ?_) ?_
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
    have hs' : ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (cl.vars.getD i 0)) := by
      rw [canonVars_getD c (hl i hil)]; rfl
    change ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt n at hn
    rw [hs'] at hn
    rw [← srt_inj hn]
    show InS I _ (e'.evalEvar (tbl2.ev (canonKey c cl.vars i)))
    rw [moveV_at hkeys2 (hl i hil) hil]
    exact hin i (hl i hil) (by simpa using (List.mem_filter.mp hil).2)
  · show (KoreAML.tr ⟨tbl2, []⟩ (.and B ([reqPat B (cl.req.map (Term.kore c vs))] ++ Cond.conj c vs B cl.pre))).interpret
      I e' mB
    have hB : ∀ (tb : VarTable) (ev : Valuation M) (a : M), (KoreAML.trSort tb B).interpret I ev a ↔ a = σB :=
      fun tb ev a => by
        show (KoreAML.trSort tb (srtOf c Srt.bool)).interpret I ev a ↔ _
        unfold srtOf; rw [trSort_srt]; exact hσB1 a
    have hmB : Inh I σB mB := by
      have := (elemOf_spec hIΓ (sortOf_bool (c := c) true) e).2
      exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσB1).mp this
    have hreqB : (KoreAML.tr ⟨tbl2, []⟩ (reqPat B (cl.req.map (Term.kore c vs)))).interpret I e' mB := by
      cases ht : cl.req with
      | none =>
        show (KoreAML.tr ⟨tbl2, []⟩ (.top (srtOf c Srt.bool))).interpret I e' mB
        rw [KoreAML.tr, KoreAML.interp_sTop hD Model.srtOf_free_stdI]
        exact (KoreAML.interp_inhOf_of (hB tbl2 e')).mpr hmB
      | some t =>
        have h1 := reqPat_resortCl hIΓ hS hσS (hB tbl e) hσB2 hmB (hm t ht)
        exact (reqPat_congrCl hIΓ (hB tbl e) (hB tbl2 e') hσB2 (fun i hi => (moveV_at hkeys2 (hlt t ht i hi)
          (List.mem_filter.mpr ⟨List.mem_range.mpr (hlt t ht i hi),
            by simpa using Clause.req_condVars ht i hi⟩)).symm) mB).mp h1
    cases hpt : cl.pre.isTop with
    | true =>
      rw [show Cond.conj c vs B cl.pre = [] from by simp [Cond.conj, hpt]]
      rw [KoreAML.tr]
      simp only [List.append_nil, KoreAML.trAndList]
      exact hreqB
    | false =>
      rw [show Cond.conj c vs B cl.pre = [Cond.kore c vs B cl.pre] from by simp [Cond.conj, hpt]]
      show (KoreAML.tr ⟨tbl2, []⟩ (.and B [reqPat B (cl.req.map (Term.kore c vs)), Cond.kore c vs B cl.pre])).interpret
        I e' mB
      rw [tr_and2, KoreAML.interp_sAnd]
      refine ⟨hreqB, hpreB hpt tbl2 e' mB (fun k hk => ?_) (fun i hi => ?_)
        ((KoreAML.interp_inhOf_of (hB tbl2 e')).mpr hmB)⟩
      · rw [← htbl]; unfold KoreAML.tableOf
        exact List.mem_eraseDups.mpr (List.mem_append_right _ (Model.varsOf_existsAll_bodyEx
          (Model.varsOf_and_mem (List.mem_append_right _
            (show Cond.kore c vs B cl.pre ∈ Cond.conj c vs B cl.pre by simp [Cond.conj, hpt])) hk) _))
      · have hi' := varOccsCond_lt_twoT cl.pre hpreOK i hi
        have hc : i ∈ cl.condVars := List.mem_append_right _ hi
        exact (moveV_at hkeys2 hi' (List.mem_filter.mpr ⟨List.mem_range.mpr hi', by simpa using hc⟩)).symm

/-- **A clause that fails has an empty exclusion in a model of `Γc`**, from what the proof reads
of the semantics: for a clause whose patterns have the argument sorts, whose premise predicate is
well sorted, whose `requires` is a Bool, and whose open condition variables are of confined sorts
or whose conditions are closed; where its conditions are decided when `needsWitness` holds
and the definition reads a confined sort where an open condition variable is of one. Where the
predicate is not `\top`, it is read in the model (`PreRead`) and the clause's conditions are not
closed over an open variable of a sort that is not confined (`needsWitness`). -/
theorem exclEmptyCl_ofCl (hI : I ⊧ᴵP Γc c) (hnn : NamesNumbered c) (hg : genWf c = true) (hsc : SortCtx c)
    [OvlOK c] (hph : patHooksApart c = true) (hcso : collSortsOK c = true) (hcs : collsOK c = true)
    (hph' : patHeadsOK c = true)
    (hcv : c.readsConfined = true → ∀ s, c.confined s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x)
    {fn : Fn} {cl : Clause} {L : List CtorSig}
    (hpatsN : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hpR : cl.pre ≠ .top → HoldsShape.PreRead c I cl ∧ cl.needsWitness c = false)
    (hreqS : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hconj : (!cl.reqOpen || cl.reqClosed ||
      cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false) = true)
    (hrc : cl.openCondVars.any (fun i => (cl.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hw : cl.needsWitness c = true → cl.CondDecided c) : ExclEmptyCl c I fn cl := by
  have hpats := sortsOfTerms_all_of_nf hpatsN
  intro ws hws hf hmf tbl hkeys hpkeys hXkeys hRkey e hX σR hR hσR m hm
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hD := defOK hIΓ
  let vs := canonVars c cl.vars
  let n := cl.vars.length
  let l := (List.range n).filter cl.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ cl.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ cl.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  have hpl : ∀ i ∈ varOccsList cl.pats, i < n := varOccsList_lt cl.pats hpats
  have hpL : ∀ i ∈ varOccsList cl.pats, i ∈ cl.leftVars := fun i hi => List.mem_append_left _ hi
  have hreqlt : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < n := fun t ht => Exec.sortOfTerm_vars (hreqS t ht)
  have hprelt : ∀ i ∈ varOccsCond cl.vars.length cl.pre, i < n := varOccsCond_lt_twoT cl.pre hpreOK
  have hleftlt : ∀ i ∈ cl.leftVars, i < n := fun i hi => by
    rcases List.mem_append.mp hi with hP | hC
    · exact hpl i hP
    · rcases List.mem_append.mp (show i ∈ (cl.req.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.pre from hC)
        with hC | hC
      · cases ht : cl.req with
        | none => rw [ht] at hC; cases hC
        | some t => rw [ht] at hC; exact hreqlt t ht i hC
      · exact hprelt i hC
  rw [exclusion_canonPre] at hm
  change (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll KoreAML.R ((l.filterMap (vs[·]?)).map KoreAML.Var.kore)
    (withPre c vs cl (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c vs))
      (Term.koreList c vs cl.pats))))).interpret I e m at hm
  rw [hbs] at hm
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  obtain ⟨e', hagE, hguard, hbody⟩ := existsAll_elim hD _ e m hnd hsrt hm
  -- the formal arguments and `R` keep e's elements
  have hnotb : ∀ k, k ∈ tbl → (∀ i < n, k ≠ canonKey c cl.vars i) →
      ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, tbl.ev k ≠ tbl.ev (KoreAML.evarKey b) := by
    intro k hk hne b hb heq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
    exact hne i (hl i hil) (ev_inj hk (hkeys i (hl i hil) (hlm i hil)) heq)
  have hneX : ∀ (j : Nat) (s : Srt), ∀ i < n,
      VarKey.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)) ≠ canonKey c cl.vars i :=
    fun j s i hi => Model.canonKey_ne_X' hi _ _
  have hneR : ∀ i < n, VarKey.sortVar "R" ≠ canonKey c cl.vars i := fun i hi h => by
    rw [canonKey_eq c hi] at h; cases h
  have he'X : ∀ (j : Nat) s, fn.args[j]? = some s →
      e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) =
        e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) :=
    fun j s hj => hagE _ (hnotb _ (hXkeys j s hj) (hneX j s))
  have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) :=
    hagE _ (hnotb _ hRkey hneR)
  have hRv' : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e' a ↔ a = σR := fun a => by
    rw [trSort_R, KoreAML.interp_evar, he'R, hR]
  -- the premise, and the predicate where it is not `\top`
  obtain ⟨hprem, hpreE⟩ : (KoreAML.tr ⟨tbl, []⟩ (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c vs))
      (Term.koreList c vs cl.pats))).interpret I e' m ∧
      (cl.pre.isTop = false → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs KoreAML.R cl.pre)).interpret I e' m) := by
    cases hpt : cl.pre.isTop with
    | true => rw [withPre_isTop hpt] at hbody; exact ⟨hbody, fun h => by cases h⟩
    | false => exact ⟨((HoldsShape.withPre_interp hpt).mp hbody).1, fun _ => ((HoldsShape.withPre_interp hpt).mp hbody).2⟩
  unfold premise at hprem
  rw [tr_and2, KoreAML.interp_sAnd] at hprem
  obtain ⟨hreqE, hargs⟩ := hprem
  have hmR : Inh I σR m := reqPat_inhCl hIΓ hRv' hσR isFree_R hreqE
  have hcon := argsConj_back 0 _ hargs
  -- the binders are in their sorts
  have hinL : ∀ i < n, i ∈ cl.leftVars → InS I (c.sortName (cl.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) :=
    fun i hi hil => hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
      (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  -- the other variables: Bool and `true`
  let a := elemOf c I (bool true)
  let e1 := fillV c tbl cl.vars cl.leftVars a e'
  have hoff1 : ∀ i < n, i ∈ cl.leftVars → e1.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hil => fillV_off hkeys hi hil
  have hR1 : e1.evalEvar (tbl.ev (.sortVar "R")) = σR := by
    show (fillV c tbl cl.vars cl.leftVars a e').evalEvar _ = _
    rw [fillV_keyCl hRkey hneR, he'R, hR]
  have hRv1 : ∀ a', (KoreAML.trSort tbl KoreAML.R).interpret I e1 a' ↔ a' = σR := fun a' => by
    rw [trSort_R, KoreAML.interp_evar, hR1]
  have hvsl : vs.length = cl.leftSortsB.length := by rw [canonVars_length, Clause.leftSortsB_length]
  have hwitF : ∀ i < n, i ∉ cl.leftVars → Witnessed c I tbl vs cl.leftSortsB e1 i := fun i hi hil =>
    ⟨bool true, by rw [Clause.leftSortsB_getD_off hi hil]; exact sortOf_bool true, (fillV_on hi hil).symm⟩
  have hin1 : ∀ i < cl.leftSortsB.length, InS I (c.sortName (cl.leftSortsB.getD i 0))
      (e1.evalEvar (tbl.ev (keyAt vs i))) := fun i hi => by
    rw [Clause.leftSortsB_length] at hi
    by_cases hil : i ∈ cl.leftVars
    · rw [Clause.leftSortsB_getD hi hil, hoff1 i hi hil]; exact hinL i hi hil
    · obtain ⟨v, hv, he⟩ := hwitF i hi hil
      rw [← he]; exact (inS_iff e1).mp (elemOf_spec hIΓ hv e1).2
  -- the patterns, at e1
  have hlenp : (Term.koreList c vs cl.pats).length = fn.args.length := by
    rw [koreList_length]; exact sortsOfTerms_length hpats
  have hall : All2 (fun φ b => φ.interpret I e1 b) ((Term.koreList c vs cl.pats).map (KoreAML.tr ⟨tbl, []⟩))
      (ws.map (elemOf c I)) := by
    refine All2.of_get (by simp [hlenp, sortsOf_length hws]) (fun j φ b hφ hb => ?_)
    rw [List.getElem?_map] at hφ hb
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hφ
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hjl : j < fn.args.length := by
      rw [← sortsOf_length hws]; exact (List.getElem?_eq_some_iff.mp hw).1
    have hs' : fn.args[j]? = some fn.args[j] := List.getElem?_eq_getElem hjl
    have hl' : ((fn.args.map c.sortName).zip (Term.koreList c vs cl.pats))[j]? = some (c.sortName fn.args[j], p) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨by rw [List.getElem?_map, hs']; rfl, hp⟩
    have hj := hcon j _ p hl'
    rw [Nat.zero_add, he'X j _ hs', hX j w _ hw hs'] at hj
    obtain ⟨q, hq, rfl⟩ := Model.koreList_get_inv (c := c) hp
    exact (tr_kore_congr q (fun i hi => (hoff1 i (hpl i (mem_varOccsList_of_getCl hq hi))
      (hpL i (mem_varOccsList_of_getCl hq hi))).symm) _).mp hj
  have hpats' : sortsOfTerms c.patCtxAll cl.leftSortsB cl.pats = some fn.args := by
    rw [sortsOfTerms_congr cl.pats (fun i hi => Clause.leftSortsB_getElem? (hpl i hi) (hpL i hi))]; exact hpats
  have hpatsN' : sortsOfTerms c.patCtxNF cl.leftSortsB cl.pats = some fn.args := by
    rw [sortsOfTerms_congr cl.pats (fun i hi => Clause.leftSortsB_getElem? (hpl i hi) (hpL i hi))]; exact hpatsN
  obtain ⟨hpv, hwitP⟩ := patVals_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 hvsl hin1 (collPats_of_sorted hph' hpats')
    hpatsN' hws hall
  -- the `requires`, at e1
  have hreq1 : ∀ t, cl.req = some t →
      (KoreAML.tr ⟨tbl, []⟩ (reqPat KoreAML.R (some (Term.kore c vs t)))).interpret I e1 m := fun t ht => by
    have h0 : (KoreAML.tr ⟨tbl, []⟩ (reqPat KoreAML.R (some (Term.kore c vs t)))).interpret I e' m := by
      rw [ht] at hreqE; exact hreqE
    exact (reqPat_congrCl hIΓ hRv' hRv1 hσR (fun i hi => (hoff1 i (hreqlt t ht i hi)
      (Clause.req_leftVars ht i hi)).symm) m).mp h0
  -- a variable of the conditions that the patterns do not hold is an open condition variable
  have hopen : ∀ i < n, i ∈ cl.leftVars → i ∉ varOccsList cl.pats → i ∈ cl.openCondVars := fun i hi hil hnl => by
    have hcv : i ∈ cl.condVars := by
      rcases List.mem_append.mp hil with h' | h'
      · exact absurd h' hnl
      · exact h'
    refine List.mem_filter.mpr ⟨?_, by simpa using hcv⟩
    simp only [Clause.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hnl⟩
  -- the predicate is not given `false` under a substitution of values that e1 agrees with
  have hpreNo : cl.pre ≠ .top → ∀ {σ : Subst}, c.WellSorted cl.leftSortsB σ → Agrees c I tbl vs σ e1 →
      HoldsShape.HoldsRead c I cl.vars.length σ cl.pre false → False := fun hne σ hσ hag hF => by
    have hpt := HoldsShape.isTop_false_of_ne hne
    have hrd : ∀ i ∈ varOccsCond cl.vars.length cl.pre, ∀ v, σ.lookup i = some v →
        ∀ m', m' = e'.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ (den c v).interpret I e' m' := fun i hi v hv m' => by
      have hlt := hprelt i hi
      have h1 := hag i v (by rw [canonVars_length]; exact hlt) hv m'
      have h2 : e'.evalEvar (tbl.ev (canonKey c cl.vars i)) = e1.evalEvar (tbl.ev (canonKey c cl.vars i)) :=
        (hoff1 i hlt (Clause.pre_leftVarsRH i hi)).symm
      rw [h2]
      exact h1.trans ((den_closed c v).interp e1 e' m')
    have hiff := (hpR hne).1.atR (vars := cl.leftSortsB) (tbl := tbl) (e := e') hF (Clause.leftSortsB_length cl)
      (fun i hi => Clause.leftSortsB_getElem? (hleftlt i hi) hi) hσ hrd (hpkeys hpt) hRkey hRv' hσR m hmR
    exact absurd (hiff.mp (hpreE hpt)) (by decide)
  by_cases hconf : cl.openCondVars.all (fun i => (cl.vars[i]?.map c.confined).getD false) = true
  · -- every open condition variable is of a confined sort: the binders are values'
    have hwit2 : ∀ i < cl.leftSortsB.length, Witnessed c I tbl vs cl.leftSortsB e1 i := fun i hi => by
      rw [Clause.leftSortsB_length] at hi
      by_cases hil : i ∈ cl.leftVars
      · by_cases hP : i ∈ varOccsList cl.pats
        · exact hwitP i hP
        · have hoc := hopen i hi hil hP
          obtain ⟨s, hvs⟩ : ∃ s, cl.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
          have hcs' : c.confined s = true := by
            have := List.all_eq_true.mp hconf i hoc; rw [hvs] at this; exact this
          have hin' := hin1 i (by rw [Clause.leftSortsB_length]; exact hi)
          rw [Clause.leftSortsB_getD hi hil, List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
          obtain ⟨v, hv, hel⟩ := hcv (hrc (List.any_eq_true.mpr ⟨i, hoc, by rw [hvs]; exact hcs'⟩)) s hcs' _ hin'
          exact witnessed_of (by rw [Clause.leftSortsB_getElem? hi hil]; exact hvs) hv hel
      · exact hwitF i hi hil
    obtain ⟨hσ2, hag2⟩ := substOf_ok hIΓ hg hsc.trans hvsl hwit2
    rcases hmf cl.leftSortsB (Clause.leftSortsB_length cl)
      (fun i hi => Clause.leftSortsB_getElem? (hleftlt i hi) hi) _ hσ2 hpv with hreqF | ⟨hne, hpreF⟩
    · obtain ⟨t, r, ht, hr, hrs, hden⟩ := hreqF tbl e1 hag2
      exact reqFalse_empty hIΓ (S' := KoreAML.R) hRv1 hσR hr hrs hden m (hreq1 t ht)
    · exact hpreNo hne hσ2 hag2 hpreF
  -- otherwise the conditions are closed, and `needsWitness` holds
  have hall' : cl.openCondVars.all (fun i => (cl.vars[i]?.map c.confined).getD false) = false := by
    cases hb : cl.openCondVars.all (fun i => (cl.vars[i]?.map c.confined).getD false) with
    | false => rfl
    | true => exact absurd hb hconf
  obtain ⟨i0, hi0, -⟩ := List.all_eq_false.mp hall'
  have hro : cl.reqOpen = true := by
    unfold Clause.reqOpen
    cases h' : cl.openCondVars with
    | nil => rw [h'] at hi0; cases hi0
    | cons _ _ => rfl
  have hrcl : cl.reqClosed = true := by
    rw [hro, hall'] at hconj; simpa using hconj
  have hnw : cl.needsWitness c = true := by
    unfold Clause.needsWitness; rw [hro, hrcl, hall']; rfl
  have hcvp : ∀ j ∈ cl.condVars, j ∉ varOccsList cl.pats := fun j hj hjp => by
    have hc2 := hrcl
    unfold Clause.reqClosed at hc2
    have := List.all_eq_true.mp hc2 j hj
    rw [List.contains_iff_mem.mpr hjp] at this
    exact absurd this (by decide)
  rcases hw hnw with hW | href
  · obtain ⟨σw, hσw, hreqw, hprew⟩ := id hW
    -- witnessed: the witness's values at the conditions' variables and the patterns' match elsewhere
    -- give a valuation of values, at whose substitution the clause fails
    have hkeysC : ∀ i < n, i ∈ cl.condVars → canonKey c cl.vars i ∈ tbl :=
      fun i hi hc => hkeys i hi (List.mem_append_right _ hc)
    let e2 := setV c tbl cl.vars cl.condVars (fun j => elemOf c I ((σw.lookup j).getD default)) e1
    have hσwv : ∀ i ∈ cl.condVars, i < n → ∃ w, σw.lookup i = some w ∧ c.sortOf w = some (cl.vars.getD i 0) :=
      fun i hc hi => hσw i hc _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    have hget : ∀ j < n, cl.leftSortsB[j]? = some (cl.leftSortsB.getD j 0) := fun j hj => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Clause.leftSortsB_length]; exact hj)]; rfl
    have hwitE : ∀ i < cl.leftSortsB.length, Witnessed c I tbl vs cl.leftSortsB e2 i := fun i hi => by
      rw [Clause.leftSortsB_length] at hi
      by_cases hc : i ∈ cl.condVars
      · obtain ⟨w, hw', hws'⟩ := hσwv i hc hi
        refine ⟨w, by rw [Clause.leftSortsB_getD hi (List.mem_append_right _ hc)]; exact hws', ?_⟩
        show elemOf c I w = (setV c tbl cl.vars cl.condVars _ e1).evalEvar (tbl.ev (canonKey c cl.vars i))
        rw [setV_on hkeysC hi hc, hw', Option.getD_some]
      · obtain ⟨v, hv, he⟩ : Witnessed c I tbl vs cl.leftSortsB e1 i := by
          by_cases hil : i ∈ cl.leftVars
          · rcases List.mem_append.mp hil with hP | hC
            · exact hwitP i hP
            · exact absurd hC hc
          · exact hwitF i hi hil
        refine ⟨v, hv, ?_⟩
        show _ = (setV c tbl cl.vars cl.condVars _ e1).evalEvar (tbl.ev (canonKey c cl.vars i))
        rw [setV_off hkeysC hi hc]; exact he
    have hin2 : ∀ i < cl.leftSortsB.length, InS I (c.sortName (cl.leftSortsB.getD i 0))
        (e2.evalEvar (tbl.ev (keyAt vs i))) := fun i hi => by
      obtain ⟨v, hv, he⟩ := hwitE i hi; rw [← he]; exact (inS_iff e2).mp (elemOf_spec hIΓ hv e2).2
    obtain ⟨hσ2, hag2⟩ := substOf_ok hIΓ hg hsc.trans hvsl hwitE
    -- the patterns' match: e2 is e1 at the patterns' variables
    have hpv2 : PatVals c (substOf c I tbl vs cl.leftSortsB e2) cl.pats ws := PatVals.congr_lookup hpv fun j hj => by
      obtain ⟨v, hv, he⟩ := hwitP j hj
      have hlt := hpl j hj
      have he2 : elemOf c I v = e2.evalEvar (tbl.ev (keyAt vs j)) := by
        rw [he]
        show _ = (setV c tbl cl.vars cl.condVars _ e1).evalEvar (tbl.ev (canonKey c cl.vars j))
        rw [setV_off hkeysC hlt (fun hc => hcvp j hc hj)]; rfl
      rw [substOf_var hIΓ hg hsc.trans hnn.1 hvsl hin2 (hget j hlt) hv he2,
        substOf_var hIΓ hg hsc.trans hnn.1 hvsl hin1 (hget j hlt) hv he]
    -- the clause fails at the valuation's substitution, which reads the `requires` at the
    -- witness's values: its result there is `true` and no other
    have hσL : c.WellSortedAt cl.vars cl.leftVars (substOf c I tbl vs cl.leftSortsB e2) := fun i hi s hs =>
      hσ2 i s (by rw [Clause.leftSortsB_getElem? (hleftlt i hi) hi]; exact hs)
    cases hf with
    | intro hf =>
      cases hf _ hσL hpv2 with
      | intro ht' he hr =>
        refine hr ((hreqw _ ht').2 _ (Exec.EvalTerm.congr he fun i hi => Eq.symm ?_))
        have hc := Clause.req_condVars ht' i hi
        have hi' := hreqlt _ ht' i hi
        obtain ⟨w, hw', hws'⟩ := hσwv i hc hi'
        rw [hw', substOf_var hIΓ hg hsc.trans hnn.1 hvsl hin2 (hget i hi')
          (by rw [Clause.leftSortsB_getD hi' (List.mem_append_right _ hc)]; exact hws') (by
            show elemOf c I w = (setV c tbl cl.vars cl.condVars _ e1).evalEvar (tbl.ev (canonKey c cl.vars i))
            rw [setV_on hkeysC hi' hc, hw', Option.getD_some])]
      | pre hpf =>
        -- a clause with a predicate other than `\top` needs no witness
        by_cases hne : cl.pre = .top
        · rw [hne] at hpf; exact absurd hpf.top_eq (by simp)
        · exact absurd hnw (by rw [(hpR hne).2]; decide)
  · -- refuted: but the conditions hold at the binders
    exact Clause.not_refuted_at hI hpreOK (fun i hi hc => hinL i hi (List.mem_append_right _ hc)) hreqlt hRv' hσR
      (fun t ht => by rw [ht] at hreqE; exact hreqE)
      (fun hpt tbl2 e2 mB hk2 hag2 hmB =>
        (hpR (fun h => by rw [h] at hpt; simp [Cond.isTop] at hpt)).1.toBool (hpkeys hpt) hRkey hk2
          (fun i hi => ⟨hinL i (hprelt i hi) (Clause.pre_leftVarsRH i hi), hag2 i hi⟩) hRv' hσR hmR hmB (hpreE hpt))
      href

/-- **A clause that fails has an empty exclusion in a model of `Γc`** (`exclEmptyCl_ofCl`), for a
semantics `coreOK` accepts and a clause with `clauseSortedOpen` and `clausePlainOpen` over
signatures of the semantics' functions whose premise's predicate is `\top`, where its conditions are decided when `needsWitness` holds
and the definition reads a confined sort where an open condition variable is of one. -/
theorem exclEmptyCl_of (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {fn : Fn} {cl : Clause}
    {L : List CtorSig} (_hL : HeadsOK c L) (hs : c.clauseSortedOpen fn L cl = true) (hp : c.clausePlainOpen cl = true)
    (hpre : cl.pre = .top)
    (hrc : cl.openCondVars.any (fun i => (cl.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hw : cl.needsWitness c = true → cl.CondDecided c) : ExclEmptyCl c I fn cl := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  obtain ⟨hpats, -, hreqS, -, -⟩ := Semantics.clauseSortedOpen_parts hs
  obtain ⟨-, -, hconj, -⟩ := Semantics.clausePlainOpen_partsP hp
  have hcv : c.readsConfined = true → ∀ s, c.confined s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := fun hr s hs' x hx => by
    obtain ⟨v, hv, hden⟩ := confined_value h hr hI hs' KoreAML.val0 x ((inS_iff KoreAML.val0).mpr hx)
    exact ⟨v, hv, (hden _).mp (((elemOf_spec hIΓ hv KoreAML.val0).1 _).mpr rfl)⟩
  intro ws
  exact exclEmptyCl_ofCl hI hnn hg (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)) hph hcso hcs hph' hcv
    (Semantics.clauseSortedOpen_pats_nf hs)
    (by rw [hpre, Semantics.condOK]) (fun hne => absurd hpre hne) hreqS hconj hrc hw

/-- **For a semantics `coreOK` accepts, a clause that fails fails in the model at the
substitutions of values on its patterns and conditions** (`evalTerm_den4`), where its predicate is
`\top`. -/
theorem modelFailsCl_of_core (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl' ∈ fn.clauses, binds cl'.vars.length (varOccsList cl'.pats) = true)
    (hIΓ : I ⊧ᴵP Γ c) {cl : Clause} {L : List CtorSig}
    (hL : HeadsOK c L) (hreqS : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hpre : cl.pre = .top)
    {ws : List GroundTerm} (hf : Fails c ws cl) : ModelFailsCl c I cl ws := by
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro vars hlen hagl σ hσ hpv
  refine Or.inl fun tbl e hag => ?_
  have hσL : c.WellSortedAt cl.vars cl.leftVars σ := fun i hi s hs => hσ i s (by rw [hagl i hi]; exact hs)
  cases hf with
  | intro hf =>
    cases hf σ hσL hpv with
    | intro ht he hr =>
      rename_i t r
      have htS : sortOfTerm (c.rhsCtx L) vars t = some Srt.bool := by
        rw [sortOfTerm_congr t fun i hi => hagl i (Clause.req_leftVars ht i hi)]; exact hreqS t ht
      exact ⟨t, r, ht, hr, fun v hv => EvalTerm.sorted hsc he hL hσ htS hv,
        evalTerm_den4 (hpreTop := hpreTop) hIΓ hnn hsc hok hbc hph (neg_of_core (hpreTop := hpreTop) h hbc hIΓ) he hL hσ (by rw [canonVars_length, hlen]) hag htS⟩
    | pre hpf => rw [hpre] at hpf; exact absurd hpf.top_eq (by simp)

/-- `exclEmptyCl_of` for a semantics `coreOK` accepts, from `Fails` alone. -/
theorem exclEmptyCl_core (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hbc : ∀ fn' ∈ c.fns, ∀ cl' ∈ fn'.clauses, binds cl'.vars.length (varOccsList cl'.pats) = true)
    (hI : I ⊧ᴵP Γc c) {fn : Fn} {cl : Clause}
    {L : List CtorSig} (hL : HeadsOK c L) (hs : c.clauseSortedOpen fn L cl = true) (hp : c.clausePlainOpen cl = true)
    (hpre : cl.pre = .top)
    (hrc : cl.openCondVars.any (fun i => (cl.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hw : cl.needsWitness c = true → cl.CondDecided c) {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hf : Fails c ws cl) {tbl : VarTable} (hkeys : ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl)
    (hXkeys : ∀ (j : Nat) s, fn.args[j]? = some s → VarKey.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)) ∈ tbl)
    (hRkey : VarKey.sortVar "R" ∈ tbl) {e : Valuation M}
    (hX : ∀ (j : Nat) w s, ws[j]? = some w → fn.args[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = elemOf c I w)
    {σR : M} (hR : e.evalEvar (tbl.ev (.sortVar "R")) = σR) (hσR : IsSort I σR) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret I e m :=
  exclEmptyCl_of h hI hL hs hp hpre hrc hw hws hf
    (modelFailsCl_of_core (hpreTop := hpreTop) h hbc (fun φ hφ => hI φ (Or.inl hφ)) hL (Semantics.clauseSortedOpen_parts hs).2.2.1
      hpre hf)
    hkeys (fun hpt => by rw [hpre] at hpt; simp [Cond.isTop] at hpt)
    hXkeys hRkey hX hR hσR m

end

end Faithful

end KCore
