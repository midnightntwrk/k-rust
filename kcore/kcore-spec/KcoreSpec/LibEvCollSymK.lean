/-
  KCore, checked layer: the lemmas of MAP-KORE-SYMBOLIC (domains.md, K 7.1.337) whose `requires`
  compares two KItem variables with `=/=K` or `==K`, entailed at values (`EntailsAtValues`) for
  every semantics meeting `coreOK` whose Map values are maps (`shapesOK`).

  kompile writes `K1 =/=K K2` over two variables of the sort KItem as
  `=/=K(kseq(K1, dotk()), kseq(K2, dotk()))`: each side is the K sequence of the one item, with no
  injection (the item is already of the sort KItem).
  - `LibEv.KReq`: a `requires` term: a library term (`LibEv.Term`), the K sequence
    `kseq(t, dotk())` of one item `t` of the sort KItem, or an interpreted hooked symbol applied to
    such terms; `KReq.kpat` its pattern over the registry's names, `KReq.kval` its value.
  - `LibEv.KReq.kden`: in a model of `Γ c`, at a valuation that gives each variable its value's
    element, the translated term denotes its value's element, or nothing where it has none: the K
    sequence of one item denotes the element of the value `kseq(v, dotk())` (`kseq1_res`).
  - `LibEv.EqnK`, `EqnK.entailed`: an equation `lhs => rhs requires req`, with an optional
    `ensures`, whose left side has the right side's value wherever the `requires` is `true` and the
    `ensures` is `true`, and none where the `requires` is `true` and the `ensures` is not.
  - The sentences: 422 (`msUpdConcatNe`), 429 (`msRemConcatNe`), 433 (`msLookupConcatNe`),
    435 (`msLookupUpdNe`), 438 (`msLookupDefConcatNe`), 440 (`msLookupDefUpdNe`),
    446 (`msInKeysUpdOr`), 447 (`msInKeysUpdNe`).
  - 451 and 452 (`msInKeysConcatSv`), over the set variables `@Key`, `@M` and the element variables
    `Key'`, `Val` (`LibEv.SvEqn` with `evs`; the right side has `#Not`): refuted at values
    (`msInKeysConcatSv_refuted_at`), and holding at sets of at most one value
    (`msInKeysConcatSv_one`).
-/
import KcoreSpec.LibEvCollSym
import KcoreSpec.LibEvFnKNe
import KcoreSpec.LibEvFnBoolInt

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- A `requires` term: a library term, the K sequence `kseq(t, dotk())` of one item `t` of the sort
KItem, or an interpreted hooked symbol applied to such terms. -/
inductive KReq where
  | term (t : Term)
  | kseq1 (t : Term)
  | app (f : Sym) (qs : List KReq)

namespace KReq

/-- The K sequence of the one item `v`. -/
def kseqV (v : GroundTerm) : GroundTerm := .ctor kseq [v, .ctor dotk []]

mutual
  /-- The term as a KORE pattern over the registry's names, the i-th variable under its name in
  `vars`. -/
  def kpat (vars : Vars) : KReq → Kore.Pattern
    | .term t => koreR vars t
    | .kseq1 t => KoreAML.kseq1 (koreR vars t)
    | .app f qs => .app ⟨⟨regSymNames.getD f ""⟩⟩ [] (kpats vars qs)
    termination_by structural q => q
  def kpats (vars : Vars) : List KReq → List Kore.Pattern
    | [] => []
    | q :: qs => kpat vars q :: kpats vars qs
    termination_by structural qs => qs
end

mutual
  /-- The value of the term at σ: a library term's (`val`), the K sequence of the item's value, Γ's
  value of an interpreted symbol at its arguments' values; none where an argument has none. -/
  def kval (c : Semantics) (σ : Subst) : KReq → Option GroundTerm
    | .term t => val c σ t
    | .kseq1 t => (val c σ t).map kseqV
    | .app f qs => (allSome (kvals c σ qs)).bind (c.hv f)
    termination_by structural q => q
  def kvals (c : Semantics) (σ : Subst) : List KReq → List (Option GroundTerm)
    | [] => []
    | q :: qs => kval c σ q :: kvals c σ qs
    termination_by structural qs => qs
end

mutual
  /-- The sort of the term: a library term's, K for the K sequence of a term of the sort KItem, the
  result sort of an interpreted hooked symbol applied to terms of its argument sorts. -/
  def ksrt? (c : Semantics) (vars : Vars) : KReq → Option Srt
    | .term t => srt? c vars t
    | .kseq1 t => if srt? c vars t == some Srt.kitem then some Srt.k else none
    | .app f qs => (lookupSig hookSigs f).bind fun k =>
        if ksrts? c vars qs == some k.args then some k.result else none
    termination_by structural q => q
  def ksrts? (c : Semantics) (vars : Vars) : List KReq → Option (List Srt)
    | [] => some []
    | q :: qs => (ksrt? c vars q).bind fun s => (ksrts? c vars qs).map (s :: ·)
    termination_by structural qs => qs
end

mutual
  /-- The term's symbols and sorts are the registry's, and none of its symbols is named like an
  `ite` at a sort. -/
  def kreg : KReq → Bool
    | .term t => reg t
    | .kseq1 t => reg t
    | .app f qs => decide (f < nRegSyms) && (iteSort? (regSymNames.getD f "")).isNone && kregs qs
    termination_by structural q => q
  def kregs : List KReq → Bool
    | [] => true
    | q :: qs => kreg q && kregs qs
    termination_by structural qs => qs
end

/-- The K sequence of one item of the sort KItem is a value of K. -/
theorem sortOf_kseqV {c : Semantics} (h : c.coreOK = true) {v : GroundTerm} (hv : c.sortOf v = some Srt.kitem) :
    c.sortOf (kseqV v) = some Srt.k := by
  obtain ⟨hok, -, -, -, hids⟩ := Semantics.coreOK_parts h
  have htr := NamesApart.subsorts_trans_of hids hok
  have hw : wrapK Srt.kitem v = kseqV v := by
    unfold wrapK kseqV
    simp only [show Srt.kitem ≠ Srt.k by decide, ↓reduceIte]
  rw [← hw]
  exact sortOf_wrapK htr (Or.inr (Or.inl rfl)) hv

/-- **The K sequence of one item denotes the sequence of the item's value.** Where `x` denotes the
element of the value `r` (nothing where `r` is none), the translated `kseq(x, dotk())` denotes the
element of `kseq(r, dotk())`, nothing where `r` is none. -/
theorem kseq1_res {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    {tbl : KoreAML.VarTable} {e : Valuation M} {x : Kore.Pattern} {r : Option GroundTerm}
    (hx : ∀ m, (KoreAML.tr ⟨tbl, []⟩ x).interpret I e m ↔ Res c I e r m) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.kseq1 x)).interpret I e m ↔ Res c I e (r.map kseqV) m := by
  unfold KoreAML.kseq1 KoreAML.ap
  rw [KoreAML.tr_app0]
  simp only [KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  cases r with
  | none =>
    refine ⟨fun hm => ?_, fun hf => False.elim hf⟩
    obtain ⟨a, _, ha, -, -⟩ := KoreAML.interp_app.mp hm
    obtain ⟨_, b, -, hb, -⟩ := KoreAML.interp_app.mp ha
    exact False.elim ((hx b).mp hb)
  | some v =>
    show _ ↔ (den c (kseqV v)).interpret I e m
    have hkseq : c.symName kseq = "kseq" := symName_reg c (by decide)
    unfold kseqV
    rw [den_ctor, hkseq]
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    refine KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => hx m))
      (fun m => ?_) m
    show _ ↔ (KoreAML.tr ⟨[], []⟩ (GroundTerm.kore c (.ctor dotk []))).interpret I e m
    rw [GroundTerm.kore, KoreAML.tr_app0, KoreAML.tr_app0]
    rfl

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
  (hvR : ∀ p ∈ vars, p.2 < nRegSorts)
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (den c v).interpret I e m)
include h hI hvR hσ hag

set_option linter.unusedSectionVars false in
mutual
  /-- **A `requires` term denotes its value.** In a model of `Γ c`, at a valuation that gives each
  variable the element of its value under σ, the translation of a term of the sort `s` denotes the
  element of its value, or nothing where it has none; and its value is of the sort `s`. -/
  theorem kden : ∀ (q : KReq) {s : Srt}, q.kreg = true → q.ksrt? c vars = some s →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (q.kpat vars)).interpret I e m ↔ Res c I e (q.kval c σ) m) ∧
      (∀ v, q.kval c σ = some v → c.sortOf v = some s)
    | .term t, s, hr, ht => by
      rw [kreg] at hr
      rw [ksrt?] at ht
      rw [kpat, kval, ← kore_reg c hvR t hr]
      exact den_val (tbl := tbl) (e := e) h hI hσ hag t ht
    | .kseq1 t, s, hr, ht => by
      rw [kreg] at hr
      rw [ksrt?] at ht
      by_cases hk : srt? c vars t = some Srt.kitem
      · simp only [hk, beq_self_eq_true, ite_true, Option.some.injEq] at ht
        subst ht
        have d := den_val (tbl := tbl) (e := e) h hI hσ hag t hk
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [kpat, kval, ← kore_reg c hvR t hr]
          exact kseq1_res d.1 m
        · rw [kval] at hw
          obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hw
          exact sortOf_kseqV h (d.2 v hv)
      · simp [hk] at ht
    | .app f qs, s, hr, ht => by
      simp only [kreg, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hr
      obtain ⟨⟨hf, -⟩, hrs⟩ := hr
      rw [ksrt?] at ht
      obtain ⟨k, hk, hk2⟩ := Option.bind_eq_some_iff.mp ht
      by_cases hargs : ksrts? c vars qs = some k.args
      · simp only [hargs, beq_self_eq_true, ite_true, Option.some.injEq] at hk2
        subst hk2
        obtain ⟨hks, hkn⟩ := lookupSig_spec hk
        have hih := kdens qs hrs hargs
        have hhook : isHook f = true := by
          cases hh : isHook f with
          | true => rfl
          | false => rw [lookupSig_hookSigs_of_not_isHook hh] at hk; cases hk
        have hhead : KoreAML.sym (.symbol (regSymNames.getD f "")) = symHead c f := by
          rw [symHead_noInst (by rw [symName_reg c hf]; exact Faithful.regSym_noInst_irs hf), symName_reg c hf]
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [kpat, KoreAML.tr_app0, hhead, kval]
          cases hall : allSome (kvals c σ qs) with
          | none =>
            simp only [Option.bind_none, Res, iff_false]
            exact hih.2 hall _ m
          | some ws =>
            obtain ⟨hws, hcong⟩ := hih.1 ws hall
            obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
            have hax := sat_hookRes hI hks hws (by rw [hkn]; exact ho)
            have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
            rw [hkn] at hgr
            unfold KoreAML.den at hgr
            rw [tr_symApp] at hgr
            rw [hcong _ _ (fun _ => Iff.rfl) m, hgr]
            simp only [Option.bind_some, Semantics.hv, ho, Option.join_some]
            cases o with
            | none => simp [Res, Pattern.interpret]
            | some v => rfl
        · rw [kval] at hw
          cases hall : allSome (kvals c σ qs) with
          | none => rw [hall] at hw; cases hw
          | some ws =>
            rw [hall] at hw
            obtain ⟨hws, -⟩ := hih.1 ws hall
            obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
            have ho' : o = some w := by simpa [Semantics.hv, ho] using hw
            exact hookRes_sorted (fun _ => rangeBelow_of_core h) hk hws (ho' ▸ ho)
      · simp [hargs] at hk2
  termination_by structural q => q
  /-- The arguments of an application: where each has a value, the values are of the argument
  sorts and the application of any head to the translated arguments is its application to the
  values' patterns; where one has none, the application denotes nothing. -/
  theorem kdens : ∀ (qs : List KReq) {ss : List Srt}, kregs qs = true → ksrts? c vars qs = some ss →
      (∀ ws, allSome (kvals c σ qs) = some ws → c.sortsOf ws = some ss ∧
        ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
          ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (kpats vars qs)).interpret I e m ↔
            (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome (kvals c σ qs) = none →
        ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (kpats vars qs)).interpret I e m)
    | [], ss, _, ht => by
      simp only [ksrts?, Option.some.injEq] at ht
      subst ht
      refine ⟨fun ws hws => ?_, fun hn => by simp [kvals, allSome] at hn⟩
      simp only [kvals, allSome, Option.some.injEq] at hws
      subst hws
      refine ⟨sortsOf_nil, fun acc acc' hacc m => ?_⟩
      rw [kpats, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | q :: qs, ss, hr, ht => by
      simp only [kregs, Bool.and_eq_true] at hr
      simp only [ksrts?] at ht
      obtain ⟨s, h1, hrest⟩ := Option.bind_eq_some_iff.mp ht
      obtain ⟨ss', h2, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ih1 := kden q hr.1 h1
      have ih2 := kdens qs hr.2 h2
      constructor
      · intro ws hws
        simp only [kvals, allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, hw, ws', hws', rfl⟩ := hws
        obtain ⟨hs', hc'⟩ := ih2.1 ws' hws'
        refine ⟨sortsOf_cons.mpr ⟨s, ss', ih1.2 w hw, hs', rfl⟩, fun acc acc' hacc m => ?_⟩
        rw [kpats, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact hc' _ _ (KoreAML.interp_app_congr hacc (fun m => by rw [ih1.1 m, hw]; rfl)) m
      · intro hn acc m
        rw [kpats, KoreAML.trArgs_cons]
        cases hr' : kval c σ q with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            have hb' := (ih1.1 b).mp hb
            rw [hr'] at hb'
            exact hb') _ m
        | some w =>
          cases hrs : allSome (kvals c σ qs) with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [kvals, allSome, hr', hrs] at hn
  termination_by structural qs => qs
end

end

end KReq

/-! ## An equation whose `requires` is over K sequences -/

/-- A library equation `lhs => rhs requires req`, with the `ensures` `ens` where it has one, over
the variables `vars`, its sides of the sort `s`. -/
structure EqnK where
  vars : Vars
  s : Srt
  req : KReq
  lhs : Term
  rhs : Term
  ens : Option Term

namespace EqnK

/-- The right conjunct kompile writes beside the right side: `\top` without an `ensures`,
`ens = true` with one. -/
def concl (E : EqnK) : Kore.Pattern :=
  match E.ens with
  | none => .top (regSrtK E.s)
  | some q => .equals (regSrtK Srt.bool) (regSrtK E.s) (koreR E.vars q) (.dv (regSrtK Srt.bool) "true")

/-- The pattern of the equation's axiom with the registry's names, over the sort variable `R`. -/
def patR (E : EqnK) : Kore.Pattern :=
  .implies KoreAML.R
    (.equals (regSrtK Srt.bool) KoreAML.R (E.req.kpat E.vars) (.dv (regSrtK Srt.bool) "true"))
    (.equals (regSrtK E.s) KoreAML.R (koreR E.vars E.lhs) (.and (regSrtK E.s) [koreR E.vars E.rhs, E.concl]))

/-- The equation is over the registry's symbols and sorts, and each of its variables is free in
its pattern. -/
def regular (E : EqnK) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  E.req.kreg && reg E.lhs && reg E.rhs && (match E.ens with | none => true | some q => reg q) &&
  E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

/-- The `requires` is a term of the sort Bool, the sides terms of the sort `s`, the `ensures` a
term of the sort Bool. -/
def typed (c : Semantics) (E : EqnK) : Bool :=
  E.req.ksrt? c E.vars == some Srt.bool && srt? c E.vars E.lhs == some E.s &&
  srt? c E.vars E.rhs == some E.s &&
  (match E.ens with | none => true | some q => srt? c E.vars q == some Srt.bool)

/-- At every substitution of values of the variables' sorts at which the `requires` has the value
`true`, the left side has the right side's value, where the `ensures` (if any) has the value `true`,
and none elsewhere. -/
def Holds (c : Semantics) (E : EqnK) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    E.req.kval c σ = some (bool true) →
    val c σ E.lhs = match E.ens with
      | none => val c σ E.rhs
      | some q => if val c σ q = some (bool true) then val c σ E.rhs else none

end EqnK

/-- **An equation whose `requires` is over K sequences, and that holds of the values, is entailed
at values.** For a semantics meeting `coreOK` and an equation `E` that `Holds`: the translation of
any axiom declaration whose pattern is `E.patR`, over the one sort variable `R`, holds in every
model of `Γ c` at every valuation that sends the axiom's free element variables to values. -/
theorem EqnK.entailed {c : Semantics} (h : c.coreOK = true) (E : EqnK) (hr : E.regular = true)
    (ht : E.typed c = true) (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  obtain ⟨vars, s, req, lhs, rhs, ens⟩ := E
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hr' := hr
  simp only [EqnK.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr'
  obtain ⟨⟨⟨⟨⟨⟨hsR, hvR⟩, hrq⟩, hl⟩, hrr⟩, hens⟩, hf⟩ := hr'
  simp only [EqnK.typed, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨htq, htl⟩, htr⟩, hte⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  have hfv : ∀ i, i < vars.length → vkey c vars i ∈ KoreAML.freeOf [] ad.ax.pattern := by
    intro i hi
    have hmem : vars.getD i ("", 0) ∈ vars := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    have := hf _ hmem
    rw [hp]
    unfold vkey
    rw [srtOf_reg c (hvR _ hmem)]
    exact List.mem_of_elem_eq_true this
  obtain ⟨σ, hσ, hag⟩ := fq_subst h hI vars hvR ad.ax hfv e hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hag ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srt? c vars u = some s) =>
    den_val (tbl := t) (e := e) h hI hσ hag u hu
  have hKQ := KReq.kden (tbl := t) (e := e) h hI hvR hσ hag req hrq htq
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI (hnum (show Srt.bool < nRegSorts by decide))
  have hdist : (distinctSorts c).contains Srt.bool = true := by
    refine List.elem_eq_true_of_mem ?_
    unfold distinctSorts
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  have hT : c.sortOf (bool true) = some Srt.bool := rmS_sortOf_bool c true
  obtain ⟨hT1, hT2⟩ := elemOf_spec hI hT e
  have hinh : KoreAML.Inh I τb (elemOf c I (bool true)) := by
    refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hT2
    have := hτb t e a'
    rwa [trSort_srtOf_twoT] at this
  have hdvT : ∀ a, (KoreAML.tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e a ↔
      (den c (bool true)).interpret I e a := by
    intro a
    unfold den KoreAML.den bool
    rw [GroundTerm.kore]
    unfold srtOf
    rw [KoreAML.tr_dv, KoreAML.tr_dv]
    rfl
  -- a Bool term's equation with `true` holds exactly where its value is `true`
  have hboolP : ∀ (p : Kore.Pattern) (r : Option GroundTerm),
      (∀ a, (KoreAML.tr ⟨t, []⟩ p).interpret I e a ↔ Res c I e r a) →
      (∀ w, r = some w → c.sortOf w = some Srt.bool) →
      ((∀ a, KoreAML.Inh I τb a → ((KoreAML.tr ⟨t, []⟩ p).interpret I e a ↔
        (KoreAML.tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e a)) ↔ r = some (bool true)) := by
    intro p r hp' hs'
    constructor
    · intro hq
      have hq1 := (hq _ hinh).mpr ((hdvT _).mpr ((hT1 _).mpr rfl))
      rw [hp'] at hq1
      cases r with
      | none => exact hq1.elim
      | some w =>
        have hw := hs' w rfl
        by_cases hne : w = bool true
        · rw [hne]
        · exact absurd ⟨hq1, (hT1 _).mpr rfl⟩ (dom_apart hI hdist hw hT hne e _)
    · intro hv a _
      rw [hp', hv, hdvT]
      rfl
  have hbs : regSrtK Srt.bool = srtOf c Srt.bool := (srtOf_reg c (by decide)).symm
  have hss : regSrtK s = srtOf c s := (srtOf_reg c hsR).symm
  rw [hp]
  unfold EqnK.patR EqnK.concl
  dsimp only
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [hbs, KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb t e) hRv hτbsort hR] at hprem
    have hreq : req.kval c σ = some (bool true) := (hboolP _ _ hKQ.1 hKQ.2).mp hprem.2
    have heq := hE σ hσ hreq
    rw [hss, ← kore_reg c hvR lhs hl, ← kore_reg c hvR rhs hrr, KoreAML.tr,
      KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [(hDV lhs _ htl).1 b, heq]
    cases ens with
    | none =>
      dsimp only
      rw [← (hDV rhs _ htr).1 b, KoreAML.tr]
      show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (kore c vars rhs))
        (KoreAML.tr ⟨t, []⟩ (.top (srtOf c s)))).interpret I e b
      rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c s)) =
        KoreAML.sTop (KoreAML.trSort t (srtOf c s)) from by rw [KoreAML.tr]]
      rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e)]
      exact ⟨fun h' => ⟨h', hb⟩, And.left⟩
    | some q =>
      dsimp only at hens hte ⊢
      have hte' : srt? c vars q = some Srt.bool := eq_of_beq hte
      rw [hbs, ← kore_reg c hvR q hens, KoreAML.tr]
      show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (kore c vars rhs))
        (KoreAML.tr ⟨t, []⟩ (.equals (srtOf c Srt.bool) (srtOf c s) (kore c vars q)
          (.dv (srtOf c Srt.bool) "true")))).interpret I e b
      rw [KoreAML.interp_sAnd, KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb t e) (hτ t e) hτbsort hτsort,
        hboolP _ _ (hDV q _ hte').1 (hDV q _ hte').2]
      have hrv := (hDV rhs _ htr).1 b
      by_cases hv : val c σ q = some (bool true)
      · rw [if_pos hv]
        exact ⟨fun h' => ⟨hrv.mpr h', hb, hv⟩, fun h' => hrv.mp h'.1⟩
      · rw [if_neg hv]
        exact ⟨fun h' => h'.elim, fun h' => absurd h'.2.2 hv⟩

/-! ## Facts of the maps at two distinct keys -/

theorem csk_hasKey_insertE_ne {k k' v : GroundTerm} {m : Entries} (h : k ≠ k') :
    hasKey k (insertE k' v m) = hasKey k m := by
  rw [Map.hasKey_eq, Map.hasKey_eq, Map.find_insert_ne v h]

theorem csk_hasKey_eraseK_ne {k k' : GroundTerm} {m : Entries} (h : k ≠ k') :
    hasKey k (eraseK k' m) = hasKey k m := by
  rw [Map.hasKey_eq, Map.hasKey_eq, Map.find_erase_ne h]

theorem csk_hasKey_insertE_self (k v : GroundTerm) (m : Entries) : hasKey k (insertE k v m) = true := by
  rw [Map.hasKey_eq, Map.find_insert_self]; rfl

/-- Updating two distinct keys in either order gives one map. -/
theorem csk_insertE_comm {k1 k2 v1 v2 : GroundTerm} {m : Entries} (hc : Map.Canon m) (h : k1 ≠ k2) :
    insertE k2 v2 (insertE k1 v1 m) = insertE k1 v1 (insertE k2 v2 m) := by
  refine Map.ext (Map.insert_canon (Map.insert_canon hc)) (Map.insert_canon (Map.insert_canon hc)) fun k => ?_
  simp only [Map.find_insert]
  by_cases h2 : k = k2
  · by_cases h1 : k = k1
    · exact absurd (h1.symm.trans h2) h
    · subst h2; simp [h1]
  · simp [h2]

/-- Removing a key other than the one just added commutes with adding it. -/
theorem csk_eraseK_insertE_ne {k1 k2 v1 : GroundTerm} {m : Entries} (hc : Map.Canon m) (h : k1 ≠ k2) :
    eraseK k2 (insertE k1 v1 m) = insertE k1 v1 (eraseK k2 m) := by
  refine Map.ext (Map.erase_canon (Map.insert_canon hc)) (Map.insert_canon (Map.erase_canon hc)) fun k => ?_
  rw [Map.find_erase (Map.insert_canon hc), Map.find_insert, Map.find_insert, Map.find_erase hc]
  by_cases h2 : k = k2
  · by_cases h1 : k = k1
    · exact absurd (h1.symm.trans h2) h
    · subst h2; simp [h1]
  · simp [h2]

/-! ## The `requires` `K1 =/=K K2` and `K1 ==K K2 orBool K1 in_keys(M)` -/

theorem csk_bool_inj {a b : Bool} (h : bool a = bool b) : a = b := by
  unfold bool at h; injection h with _ h; injection h

/-- `K_i =/=K K_j` over two variables of the sort KItem. -/
def kNeReq (i j : Nat) : KReq := .app kNe [.kseq1 (.var i), .kseq1 (.var j)]

section
variable {c : Semantics}

theorem csk_kseq_var {σ : Subst} {i : Nat} {a : GroundTerm} (ha : σ.lookup i = some a) :
    (KReq.kseq1 (.var i)).kval c σ = some (KReq.kseqV a) := by
  rw [KReq.kval, val, ha]; rfl

theorem csk_kseqV_inj {a b : GroundTerm} (h : KReq.kseqV a = KReq.kseqV b) : a = b := by
  unfold KReq.kseqV at h
  injection h with _ h
  injection h

/-- Where `K_i =/=K K_j` is `true`, the two values differ. -/
theorem kNeReq_ne {σ : Subst} {i j : Nat} {a b : GroundTerm} (ha : σ.lookup i = some a)
    (hb : σ.lookup j = some b) (hq : (kNeReq i j).kval c σ = some (bool true)) : a ≠ b := by
  rintro rfl
  simp [kNeReq, KReq.kval, KReq.kvals, val, ha, hb, allSome, fhv_kNe, GroundTerm.cmp_refl, bool] at hq

end

local syntax "csk_eval" "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| csk_eval [$ls,*] $[$loc]?) => `(tactic|
    simp only [val, valList, allSome, Option.bind_some, Option.map_some, boolT, dv_bool, csHv_mapElem,
      csHv_mapUpdate, csHv_mapRemove, csHv_mapLookup, csHv_mapLookupOrDefault, csHv_mapInKeys,
      csHv_boolNot, fhv_mapConcat, cs_union_single, $ls,*] $[$loc]?)

/-! ## 435: `( MAP:Map [ K1 <- _V1 ]) [ K2 ] => MAP [ K2 ] requires K1 =/=K K2` -/

def msLookupUpdNe : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("VarMAP", Srt.map), ("Var'Unds'V1", Srt.kitem)], Srt.kitem,
    kNeReq 0 1, .app mapLookup [.app mapUpdate [.var 2, .var 0, .var 3], .var 1],
    .app mapLookup [.var 2, .var 1], none⟩

theorem msLookupUpdNe_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupUpdNe.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarMAP") rfl
  obtain ⟨v1, hv1, -⟩ := hσ 3 ("Var'Unds'V1", Srt.kitem) rfl
  have hne := kNeReq_ne hk1 hk2 hq
  simp only [msLookupUpdNe]
  csk_eval [hk1, hk2, hm, hv1]
  rw [Map.find_insert_ne v1 (Ne.symm hne)]

theorem msLookupUpdNe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msLookupUpdNe.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msLookupUpdNe (by decide +kernel) (by rfl) (msLookupUpdNe_holds hs) ad hp hsv

/-! ## 440: `( MAP:Map [ K1 <- _V1 ]) [ K2 ] orDefault D => MAP [ K2 ] orDefault D requires K1 =/=K K2` -/

def msLookupDefUpdNe : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("VarMAP", Srt.map), ("Var'Unds'V1", Srt.kitem),
      ("VarD", Srt.kitem)], Srt.kitem,
    kNeReq 0 1, .app mapLookupOrDefault [.app mapUpdate [.var 2, .var 0, .var 3], .var 1, .var 4],
    .app mapLookupOrDefault [.var 2, .var 1, .var 4], none⟩

theorem msLookupDefUpdNe_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupDefUpdNe.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarMAP") rfl
  obtain ⟨v1, hv1, -⟩ := hσ 3 ("Var'Unds'V1", Srt.kitem) rfl
  obtain ⟨d, hd, -⟩ := hσ 4 ("VarD", Srt.kitem) rfl
  have hne := kNeReq_ne hk1 hk2 hq
  simp only [msLookupDefUpdNe]
  csk_eval [hk1, hk2, hm, hv1, hd]
  rw [Map.find_insert_ne v1 (Ne.symm hne)]

theorem msLookupDefUpdNe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msLookupDefUpdNe.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msLookupDefUpdNe (by decide +kernel) (by rfl) (msLookupDefUpdNe_holds hs) ad hp hsv

/-! ## 433: `(K1 |-> _V M:Map) [ K2 ] => M [K2] requires K1 =/=K K2 ensures notBool (K1 in_keys(M))` -/

def msLookupConcatNe : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("Var'Unds'V", Srt.kitem), ("VarM", Srt.map)], Srt.kitem,
    kNeReq 0 1, .app mapLookup [.app mapConcat [.app mapElem [.var 0, .var 2], .var 3], .var 1],
    .app mapLookup [.var 3, .var 1], some (.app boolNot [.app mapInKeys [.var 0, .var 3]])⟩

theorem msLookupConcatNe_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupConcatNe.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨v, hv, -⟩ := hσ 2 ("Var'Unds'V", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 3 (n := "VarM") rfl
  have hne := kNeReq_ne hk1 hk2 hq
  simp only [msLookupConcatNe]
  csk_eval [hk1, hk2, hv, hm]
  cases hkm : hasKey k1 m
  · simp [csHv_mapLookup, Map.find_insert_ne v (Ne.symm hne), bool]
  · simp [bool]

theorem msLookupConcatNe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msLookupConcatNe.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msLookupConcatNe (by decide +kernel) (by rfl) (msLookupConcatNe_holds hs) ad hp hsv

/-! ## 438: `(K1 |-> _V M:Map) [ K2 ] orDefault D => M [K2] orDefault D requires K1 =/=K K2
ensures notBool (K1 in_keys(M))` -/

def msLookupDefConcatNe : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("Var'Unds'V", Srt.kitem), ("VarM", Srt.map),
      ("VarD", Srt.kitem)], Srt.kitem,
    kNeReq 0 1, .app mapLookupOrDefault [.app mapConcat [.app mapElem [.var 0, .var 2], .var 3], .var 1, .var 4],
    .app mapLookupOrDefault [.var 3, .var 1, .var 4], some (.app boolNot [.app mapInKeys [.var 0, .var 3]])⟩

theorem msLookupDefConcatNe_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupDefConcatNe.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨v, hv, -⟩ := hσ 2 ("Var'Unds'V", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 3 (n := "VarM") rfl
  obtain ⟨d, hd, -⟩ := hσ 4 ("VarD", Srt.kitem) rfl
  have hne := kNeReq_ne hk1 hk2 hq
  simp only [msLookupDefConcatNe]
  csk_eval [hk1, hk2, hv, hm, hd]
  cases hkm : hasKey k1 m
  · simp [csHv_mapLookupOrDefault, Map.find_insert_ne v (Ne.symm hne), bool]
  · simp [bool]

theorem msLookupDefConcatNe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = msLookupDefConcatNe.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msLookupDefConcatNe (by decide +kernel) (by rfl) (msLookupDefConcatNe_holds hs) ad hp hsv

/-! ## 422: `(K1 |-> V1 M:Map) [ K2 <- V2 ] => (K1 |-> V1 (M [ K2 <- V2 ])) requires K1 =/=K K2` -/

def msUpdConcatNe : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("VarV1", Srt.kitem), ("VarM", Srt.map), ("VarV2", Srt.kitem)],
    Srt.map, kNeReq 0 1,
    .app mapUpdate [.app mapConcat [.app mapElem [.var 0, .var 2], .var 3], .var 1, .var 4],
    .app mapConcat [.app mapElem [.var 0, .var 2], .app mapUpdate [.var 3, .var 1, .var 4]], none⟩

theorem msUpdConcatNe_holds {c : Semantics} (hs : c.shapesOK = true) : msUpdConcatNe.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨v1, hv1, -⟩ := hσ 2 ("VarV1", Srt.kitem) rfl
  obtain ⟨m, hm, hcm⟩ := fq_map_at hs hσ 3 (n := "VarM") rfl
  obtain ⟨v2, hv2, -⟩ := hσ 4 ("VarV2", Srt.kitem) rfl
  have hne := kNeReq_ne hk1 hk2 hq
  simp only [msUpdConcatNe]
  csk_eval [hk1, hk2, hv1, hm, hv2, csk_hasKey_insertE_ne (v := v2) (m := m) hne]
  cases hkm : hasKey k1 m <;> simp [csHv_mapUpdate, csk_insertE_comm hcm hne]

theorem msUpdConcatNe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msUpdConcatNe.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msUpdConcatNe (by decide +kernel) (by rfl) (msUpdConcatNe_holds hs) ad hp hsv

/-! ## 429: `(K1 |-> V1 M:Map) [ K2 <- undef ] => (K1 |-> V1 (M [ K2 <- undef ])) requires K1 =/=K K2` -/

def msRemConcatNe : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("VarV1", Srt.kitem), ("VarM", Srt.map)], Srt.map, kNeReq 0 1,
    .app mapRemove [.app mapConcat [.app mapElem [.var 0, .var 2], .var 3], .var 1],
    .app mapConcat [.app mapElem [.var 0, .var 2], .app mapRemove [.var 3, .var 1]], none⟩

theorem msRemConcatNe_holds {c : Semantics} (hs : c.shapesOK = true) : msRemConcatNe.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨v1, hv1, -⟩ := hσ 2 ("VarV1", Srt.kitem) rfl
  obtain ⟨m, hm, hcm⟩ := fq_map_at hs hσ 3 (n := "VarM") rfl
  have hne := kNeReq_ne hk1 hk2 hq
  simp only [msRemConcatNe]
  csk_eval [hk1, hk2, hv1, hm, csk_hasKey_eraseK_ne (m := m) hne]
  cases hkm : hasKey k1 m <;> simp [csHv_mapRemove, csk_eraseK_insertE_ne hcm hne]

theorem msRemConcatNe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msRemConcatNe.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msRemConcatNe (by decide +kernel) (by rfl) (msRemConcatNe_holds hs) ad hp hsv

/-! ## 447: `K1 in_keys(M [ K2 <- _ ]) => K1 in_keys(M) requires K1 =/=K K2` -/

def msInKeysUpdNe : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("VarM", Srt.map), ("Var'Unds'Gen0", Srt.kitem)], Srt.bool,
    kNeReq 0 1, .app mapInKeys [.var 0, .app mapUpdate [.var 2, .var 1, .var 3]],
    .app mapInKeys [.var 0, .var 2], none⟩

theorem msInKeysUpdNe_holds {c : Semantics} (hs : c.shapesOK = true) : msInKeysUpdNe.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarM") rfl
  obtain ⟨g, hg, -⟩ := hσ 3 ("Var'Unds'Gen0", Srt.kitem) rfl
  have hne := kNeReq_ne hk1 hk2 hq
  simp only [msInKeysUpdNe]
  csk_eval [hk1, hk2, hm, hg]
  rw [csk_hasKey_insertE_ne hne]

theorem msInKeysUpdNe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msInKeysUpdNe.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msInKeysUpdNe (by decide +kernel) (by rfl) (msInKeysUpdNe_holds hs) ad hp hsv

/-! ## 446: `K1 in_keys(M [ K2 <- _ ]) => true requires K1 ==K K2 orBool K1 in_keys(M)` -/

def msInKeysUpdOr : EqnK :=
  ⟨[("VarK1", Srt.kitem), ("VarK2", Srt.kitem), ("VarM", Srt.map), ("Var'Unds'Gen0", Srt.kitem)], Srt.bool,
    .app boolOr [.app kEq [.kseq1 (.var 0), .kseq1 (.var 1)], .term (.app mapInKeys [.var 0, .var 2])],
    .app mapInKeys [.var 0, .app mapUpdate [.var 2, .var 1, .var 3]], .dv Srt.bool (.bool true), none⟩

theorem msInKeysUpdOr_holds {c : Semantics} (hs : c.shapesOK = true) : msInKeysUpdOr.Holds c := by
  intro σ hσ hq
  obtain ⟨k1, hk1, -⟩ := hσ 0 ("VarK1", Srt.kitem) rfl
  obtain ⟨k2, hk2, -⟩ := hσ 1 ("VarK2", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarM") rfl
  obtain ⟨g, hg, -⟩ := hσ 3 ("Var'Unds'Gen0", Srt.kitem) rfl
  have hor : k1 = k2 ∨ hasKey k1 m = true := by
    simp only [msInKeysUpdOr, KReq.kval, KReq.kvals, val, valList, allSome, Option.bind_some, Option.map_some,
      Function.comp_apply, hk1, hk2, hm, csHv_mapInKeys, fhv_kEq, fhv_boolOr] at hq
    have hb := csk_bool_inj (Option.some.inj hq)
    simp only [Bool.or_eq_true, beq_iff_eq, cmp_eq_iff] at hb
    rcases hb with he | he
    · exact Or.inl (csk_kseqV_inj he)
    · exact Or.inr he
  simp only [msInKeysUpdOr]
  csk_eval [hk1, hk2, hm, hg]
  rcases hor with rfl | hk
  · rw [csk_hasKey_insertE_self]
  · by_cases h12 : k1 = k2
    · subst h12; rw [csk_hasKey_insertE_self]
    · rw [csk_hasKey_insertE_ne h12, hk]

theorem msInKeysUpdOr_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msInKeysUpdOr.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnK.entailed h msInKeysUpdOr (by decide +kernel) (by rfl) (msInKeysUpdOr_holds hs) ad hp hsv

/-! ## 451, 452: `{false #Equals @Key in_keys(Key' |-> Val @M)} => #Ceil(@Key) #And
#Ceil(Key' |-> Val @M) #And #Not({@Key #Equals Key'}) #And {false #Equals @Key in_keys(@M)}` and the flip

Over the set variables `@Key`, `@M` and the element variables `Key'`, `Val`. The left side holds
where `@Key in_keys(Key' |-> Val @M)` denotes `false` alone: the choices of `@M` at which
`Key' |-> Val @M` has no value contribute nothing to it, while the right side's test
`@Key in_keys(@M)` ranges over every choice. At `@Key = {a}` and `@M` the maps `m1` and `m2`, where
`Key' |-> Val m1` has a value without the key `a` and `m2` has the keys `Key'` and `a`, the left
side holds and the test denotes `true`: the sentence fails there (`SvEqn.refuted_at`). At sets of
at most one value both sides say that `a` is not `Key'` and no key of `M`, and `Key'` no key of `M`
(`SvEqn.entailed_one`). -/

/-- The sentence, `flip` with `false` second (452). -/
def msInKeysConcatSv (flip : Bool) : SvEqn :=
  let cat : Term := .app mapConcat [.app mapElem [.var 1, .var 2], .var 3]
  let eqF (t : Term) : SvPred := if flip then .eq Srt.bool t (boolT false) else .eq Srt.bool (boolT false) t
  { vars := [("VarKey", Srt.kitem), ("VarKey'Apos'", Srt.kitem), ("VarVal", Srt.kitem), ("VarM", Srt.map)],
    lhs := eqF (.app mapInKeys [.var 0, cat]),
    rhs := .and (.and (.and (.ceil Srt.kitem (.var 0)) (.ceil Srt.map cat)) (.not (.eq Srt.kitem (.var 0) (.var 1))))
      (eqF (.app mapInKeys [.var 0, .var 3])),
    evs := [1, 2] }

theorem msInKeysConcatSv_apart {c : Semantics} (h : c.coreOK = true) (flip : Bool) :
    (msInKeysConcatSv flip).lhs.Apart c ∧ (msInKeysConcatSv flip).rhs.Apart c := by
  haveI : OvlOK c := ovlOK_of_core h
  have hb : apartSort c Srt.bool = true := apart_of_distinct bool_distinct
  have hki : apartSort c Srt.kitem = true := by simp [apartSort]
  cases flip <;> exact ⟨hb, ⟨⟨trivial, trivial⟩, hki⟩, hb⟩

/-- An equation's two orders say one thing. -/
theorem csk_eq_comm {c : Semantics} {ρ : Nat → GroundTerm → Prop} (s : Srt) (t u : Term) :
    (SvPred.eq s t u).Holds c ρ ↔ (SvPred.eq s u t).Holds c ρ := by
  simp only [SvPred.Holds]
  exact forall_congr' fun _ => Iff.comm

/-- The two sides do not depend on the flip. -/
theorem msInKeysConcatSv_flip {c : Semantics} (ρ : Nat → GroundTerm → Prop) :
    ((msInKeysConcatSv true).lhs.Holds c ρ ↔ (msInKeysConcatSv false).lhs.Holds c ρ) ∧
    ((msInKeysConcatSv true).rhs.Holds c ρ ↔ (msInKeysConcatSv false).rhs.Holds c ρ) := by
  simp only [msInKeysConcatSv, ite_true, Bool.false_eq_true, ite_false]
  refine ⟨csk_eq_comm _ _ _, ?_⟩
  simp only [SvPred.Holds] at *
  rw [show (∀ v, svVals c ρ (.app mapInKeys [.var 0, .var 3]) v ↔ svVals c ρ (boolT false) v) ↔
      (∀ v, svVals c ρ (boolT false) v ↔ svVals c ρ (.app mapInKeys [.var 0, .var 3]) v) from
    forall_congr' fun _ => Iff.comm]

/-- The values of `@Key in_keys(Key' |-> Val @M)` and of `@Key in_keys(@M)`, where `@M` holds
maps. -/
theorem msInKeysConcatSv_vals {c : Semantics} (ρ : Nat → GroundTerm → Prop)
    (hM : ∀ w, ρ 3 w → ∃ es, w = .map Srt.map es) (w : GroundTerm) :
    (svVals c ρ (.app mapInKeys [.var 0, .app mapConcat [.app mapElem [.var 1, .var 2], .var 3]]) w ↔
      ∃ a k v m, ρ 0 a ∧ ρ 1 k ∧ ρ 2 v ∧ ρ 3 (.map Srt.map m) ∧ hasKey k m = false ∧
        w = bool (hasKey a (insertE k v m))) ∧
    (svVals c ρ (.app mapConcat [.app mapElem [.var 1, .var 2], .var 3]) w ↔
      ∃ k v m, ρ 1 k ∧ ρ 2 v ∧ ρ 3 (.map Srt.map m) ∧ hasKey k m = false ∧ w = .map Srt.map (insertE k v m)) ∧
    (svVals c ρ (.app mapInKeys [.var 0, .var 3]) w ↔
      ∃ a m, ρ 0 a ∧ ρ 3 (.map Srt.map m) ∧ w = bool (hasKey a m)) := by
  have hcat : ∀ u, svVals c ρ (.app mapConcat [.app mapElem [.var 1, .var 2], .var 3]) u ↔
      ∃ k v m, ρ 1 k ∧ ρ 2 v ∧ ρ 3 (.map Srt.map m) ∧ hasKey k m = false ∧ u = .map Srt.map (insertE k v m) := by
    intro u
    simp only [svVals, svValsList]
    constructor
    · rintro ⟨_, ⟨_, _, rfl, ⟨_, ⟨k, _, rfl, hk, v, _, rfl, hv, rfl⟩, he⟩, mw, _, rfl, hm, rfl⟩, hc⟩
      rw [csHv_mapElem] at he
      cases he
      obtain ⟨m, rfl⟩ := hM mw hm
      rw [fhv_mapConcat, cs_union_single] at hc
      cases hkm : hasKey k m with
      | true => rw [hkm] at hc; simp at hc
      | false =>
        rw [hkm] at hc
        simp only [Bool.false_eq_true, ite_false, Option.map_some, Option.some.injEq] at hc
        exact ⟨k, v, m, hk, hv, hm, hkm, hc.symm⟩
    · rintro ⟨k, v, m, hk, hv, hm, hkm, rfl⟩
      exact ⟨[.map Srt.map [(k, v)], .map Srt.map m], ⟨_, _, rfl, ⟨[k, v], ⟨k, _, rfl, hk, v, _, rfl, hv, rfl⟩,
        csHv_mapElem k v⟩, _, [], rfl, hm, rfl⟩, by rw [fhv_mapConcat, cs_union_single, hkm]; rfl⟩
  refine ⟨?_, hcat w, ?_⟩
  · simp only [svVals, svValsList]
    constructor
    · rintro ⟨_, ⟨a, _, rfl, ha, u, _, rfl, hu, rfl⟩, hw⟩
      obtain ⟨k, v, m, hk, hv, hm, hkm, rfl⟩ := (hcat u).mp hu
      rw [csHv_mapInKeys] at hw
      exact ⟨a, k, v, m, ha, hk, hv, hm, hkm, (Option.some.inj hw).symm⟩
    · rintro ⟨a, k, v, m, ha, hk, hv, hm, hkm, rfl⟩
      exact ⟨[a, .map Srt.map (insertE k v m)], ⟨a, _, rfl, ha, _, [], rfl, (hcat _).mpr ⟨k, v, m, hk, hv, hm, hkm, rfl⟩,
        rfl⟩, csHv_mapInKeys _ _ _⟩
  · simp only [svVals, svValsList]
    constructor
    · rintro ⟨_, ⟨a, _, rfl, ha, mw, _, rfl, hm, rfl⟩, hw⟩
      obtain ⟨m, rfl⟩ := hM mw hm
      rw [csHv_mapInKeys] at hw
      exact ⟨a, m, ha, hm, (Option.some.inj hw).symm⟩
    · rintro ⟨a, m, ha, hm, rfl⟩
      exact ⟨[a, .map Srt.map m], ⟨a, _, rfl, ha, _, [], rfl, hm, rfl⟩, csHv_mapInKeys _ _ _⟩

theorem csk_svVals_dv {c : Semantics} {ρ : Nat → GroundTerm → Prop} (b : Bool) (w : GroundTerm) :
    svVals c ρ (boolT b) w ↔ w = bool b := Iff.rfl

theorem csk_svVals_var {c : Semantics} {ρ : Nat → GroundTerm → Prop} (i : Nat) (w : GroundTerm) :
    svVals c ρ (.var i) w ↔ ρ i w := Iff.rfl

/-- **451 and 452 are refuted at values**: in every model of `Γ c`, at `@Key = {a}`, `Key' = k`,
`Val = v` and `@M` the maps `m1` (`k |-> v m1` has a value without the key `a`) and `m2` (with the
keys `k` and `a`), the left side holds and `@Key in_keys(@M)` denotes `true`. -/
theorem msInKeysConcatSv_refuted_at {c : Semantics} (h : c.coreOK = true) (flip : Bool)
    (hr : (msInKeysConcatSv flip).regular = true) (ht : (msInKeysConcatSv flip).typed c = true)
    (a k v : GroundTerm) (m1 m2 : Entries) (ha : c.sortOf a = some Srt.kitem) (hk : c.sortOf k = some Srt.kitem)
    (hv : c.sortOf v = some Srt.kitem)
    (hm1 : c.sortOf (.map Srt.map m1) = some Srt.map) (hm2 : c.sortOf (.map Srt.map m2) = some Srt.map)
    (h1 : hasKey k m1 = false) (h2 : hasKey a (insertE k v m1) = false) (h3 : hasKey k m2 = true)
    (h4 : hasKey a m2 = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (msInKeysConcatSv flip).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  let ρ : Nat → GroundTerm → Prop := fun i w => (i = 0 ∧ w = a) ∨ (i = 1 ∧ w = k) ∨ (i = 2 ∧ w = v) ∨
    (i = 3 ∧ (w = .map Srt.map m1 ∨ w = .map Srt.map m2))
  have hM : ∀ w, ρ 3 w → ∃ es, w = .map Srt.map es := by
    rintro w (⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, rfl | rfl⟩)
    · cases h'
    · cases h'
    · cases h'
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have hL : (msInKeysConcatSv false).lhs.Holds c ρ := by
    simp only [msInKeysConcatSv, Bool.false_eq_true, ite_false, SvPred.Holds]
    intro w
    rw [(msInKeysConcatSv_vals ρ hM w).1, csk_svVals_dv]
    constructor
    · rintro rfl
      exact ⟨a, k, v, m1, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)), h1, by rw [h2]⟩
    · rintro ⟨a', k', v', m, ha', hk', hv', hm, hkm, rfl⟩
      obtain ⟨-, rfl⟩ : 0 = 0 ∧ a' = a := by
        rcases ha' with h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> first | exact h' | cases h'
      obtain ⟨-, rfl⟩ : 1 = 1 ∧ k' = k := by
        rcases hk' with ⟨h', -⟩ | h' | ⟨h', -⟩ | ⟨h', -⟩ <;> first | exact h' | cases h'
      obtain ⟨-, rfl⟩ : 2 = 2 ∧ v' = v := by
        rcases hv' with ⟨h', -⟩ | ⟨h', -⟩ | h' | ⟨h', -⟩ <;> first | exact h' | cases h'
      rcases hm with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, hm | hm⟩
      · cases h'
      · cases h'
      · cases h'
      · injection hm with _ hm; subst hm; rw [h2]
      · injection hm with _ hm; subst hm; rw [h3] at hkm; cases hkm
  have hR : ¬ (msInKeysConcatSv false).rhs.Holds c ρ := by
    simp only [msInKeysConcatSv, Bool.false_eq_true, ite_false, SvPred.Holds]
    rintro ⟨-, heq⟩
    have := (heq (bool true)).mpr ((msInKeysConcatSv_vals ρ hM _).2.2.mpr
      ⟨a, m2, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)), by rw [h4]⟩)
    simp [svVals, boolT, bool] at this
  have hfl := msInKeysConcatSv_flip (c := c) ρ
  refine SvEqn.refuted_at h _ hr ht (msInKeysConcatSv_apart h flip) ρ ?_ ?_ ?_ ad hp hsv hI
  · intro i x hx w hw
    have hx' : ∀ y, (msInKeysConcatSv flip).vars[i]? = some y → x = y := fun y hy => by rw [hx] at hy; cases hy; rfl
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · rw [hx' _ (by cases flip <;> rfl)]; exact ha
    · rw [hx' _ (by cases flip <;> rfl)]; exact hk
    · rw [hx' _ (by cases flip <;> rfl)]; exact hv
    · rw [hx' _ (by cases flip <;> rfl)]; exact hm1
    · rw [hx' _ (by cases flip <;> rfl)]; exact hm2
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by cases flip <;> simpa [msInKeysConcatSv] using hi
    rcases hi' with rfl | rfl
    · refine ⟨k, fun w => ⟨fun hw => ?_, fun hw => Or.inr (Or.inl ⟨rfl, hw⟩)⟩⟩
      rcases hw with ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> first | exact h' | cases h'
    · refine ⟨v, fun w => ⟨fun hw => ?_, fun hw => Or.inr (Or.inr (Or.inl ⟨rfl, hw⟩))⟩⟩
      rcases hw with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩ <;> first | exact h' | cases h'
  · intro hiff
    cases flip
    · exact hR (hiff.mp hL)
    · exact hR (hfl.2.mp (hiff.mp (hfl.1.mpr hL)))

/-- **The companion of 451 and 452**: at sets of at most one value the sentence holds, in every
semantics whose Map values are maps (`shapesOK`). -/
theorem msInKeysConcatSv_one {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (flip : Bool)
    (hr : (msInKeysConcatSv flip).regular = true) (ht : (msInKeysConcatSv flip).typed c = true)
    (hkap : apartSort c Srt.map = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (msInKeysConcatSv flip).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    SvAtMostOne c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI : OvlOK c := ovlOK_of_core h
  have hki : apartSort c Srt.kitem = true := by simp [apartSort]
  refine SvEqn.entailed_one h _ hr ht (msInKeysConcatSv_apart h flip)
    (fun x hx => by
      have hx' : x ∈ [("VarKey", Srt.kitem), ("VarKey'Apos'", Srt.kitem), ("VarVal", Srt.kitem), ("VarM", Srt.map)] := by
        cases flip <;> exact hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl | rfl
      · exact hki
      · exact hki
      · exact hki
      · exact hkap) ?_ ad hp hsv
  intro ρ hρ hone
  have hρ' : SvEqn.Sorted c (msInKeysConcatSv false).vars ρ := by cases flip <;> exact hρ
  have hM : ∀ w, ρ 3 w → ∃ es, w = .map Srt.map es := fun w hw => shape_map hs (hρ' 3 _ rfl w hw)
  suffices hfalse : (msInKeysConcatSv false).lhs.Holds c ρ ↔ (msInKeysConcatSv false).rhs.Holds c ρ by
    cases flip
    · exact hfalse
    · have hfl := msInKeysConcatSv_flip (c := c) ρ
      rw [hfl.1, hfl.2]; exact hfalse
  have hV := msInKeysConcatSv_vals (c := c) ρ hM
  simp only [msInKeysConcatSv, Bool.false_eq_true, ite_false, SvPred.Holds, csk_svVals_dv, csk_svVals_var]
  constructor
  · intro hl
    obtain ⟨a, k, v, m, ha, hk, hv, hm, hkm, hb⟩ := (hV _).1.mp ((hl _).mp rfl)
    have hakv : hasKey a (insertE k v m) = false := (csk_bool_inj hb).symm
    have hak : a ≠ k := by
      rintro rfl; rw [csk_hasKey_insertE_self] at hakv; cases hakv
    have ham : hasKey a m = false := by rw [← csk_hasKey_insertE_ne hak]; exact hakv
    refine ⟨⟨⟨⟨a, ha⟩, _, (hV _).2.1.mpr ⟨k, v, m, hk, hv, hm, hkm, rfl⟩⟩, fun he => hak ?_⟩, fun w => ⟨?_, ?_⟩⟩
    · exact hone 1 _ _ ((he a).mp ha) hk
    · rintro rfl; exact (hV _).2.2.mpr ⟨a, m, ha, hm, by rw [ham]⟩
    · rintro hw
      obtain ⟨a', m', ha', hm', rfl⟩ := (hV _).2.2.mp hw
      obtain rfl := hone 0 _ _ ha ha'
      obtain rfl : m = m' := by have := hone 3 _ _ hm hm'; injection this
      rw [ham]
  · rintro ⟨⟨⟨⟨a, ha⟩, _, hcat⟩, hne⟩, heq⟩
    obtain ⟨k, v, m, hk, hv, hm, hkm, -⟩ := (hV _).2.1.mp hcat
    obtain ⟨a', m', ha', hm', hb⟩ := (hV _).2.2.mp ((heq _).mp rfl)
    obtain rfl := hone 0 _ _ ha ha'
    obtain rfl : m = m' := by have := hone 3 _ _ hm hm'; injection this
    have ham : hasKey a m = false := (csk_bool_inj hb).symm
    have hak : a ≠ k := by
      rintro rfl
      exact hne fun w => ⟨fun hw => by rw [hone 0 _ _ hw ha]; exact hk, fun hw => by rw [hone 1 _ _ hw hk]; exact ha⟩
    intro w
    constructor
    · rintro rfl
      exact (hV _).1.mpr ⟨a, k, v, m, ha, hk, hv, hm, hkm, by rw [csk_hasKey_insertE_ne hak, ham]⟩
    · intro hw
      obtain ⟨a', k', v', m', ha', hk', hv', hm', -, rfl⟩ := (hV _).1.mp hw
      obtain rfl := hone 0 _ _ ha ha'
      obtain rfl := hone 1 _ _ hk hk'
      obtain rfl := hone 2 _ _ hv hv'
      obtain rfl : m = m' := by have := hone 3 _ _ hm hm'; injection this
      rw [csk_hasKey_insertE_ne hak, ham]

end LibEv

end KCore
