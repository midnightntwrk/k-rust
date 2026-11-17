/-
  KCore. A condition is a predicate.

  In a model of `Γ c`, `Cond.kore c vs S p` for a well-sorted condition p (`condOK`) denotes, at a
  valuation that gives each free variable of p an element of its sort, either the whole sort `S` or
  nothing (`cond_predAt`): whether it holds at one element of `S` does not depend on the element
  (`cond_pred_transfer`, CondPred.lean). From the connectives' meaning:
  - `\ceil{s,S}(t)` is the whole sort `S` where t denotes some element and empty where it denotes
    none, for t's elements in its sort `s` (`interp_sCeil`): the model's `⌈_⌉{s,S}` is constrained
    only at elements of `s` (`ceilDefItem`), so the term's elements must lie in `s`. They do: the
    term is well sorted, its variables are valued in their sorts, and every head maps elements of its
    argument sorts into its result sort (`rhsSort_at`, `rhsSort` with the hypothesis on the term's
    own variables only);
  - `\in{s,S}(t, u)` is `\ceil` of `t ∧ u`, whose elements are t's;
  - `\equals{s,S}(t, u)` is `\floor` of a pattern inside `s`, at any valuation;
  - `\top`, `\bottom`, `\not`, `\and`, `\or`, `\implies` at `S` keep a pattern that is all of `S` or
    nothing such a pattern, at the elements of `S`;
  - a binder (`ex`, `all`, the `\exists` of `exMatch`) ranges over the elements of its sort, so the
    body is read at a valuation that again gives each of its free variables an element of its sort.
  Without the sort hypothesis the fact is false: `⌈x⌉{s,S}` for x valued outside `s` is any subset
  of the model's choosing.
-/
import KcoreSpec.CondTwoTables
import KcoreSpec.RhsValues

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## A right-hand side's elements, over the term's own variables -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
variable [OvlOK c] (hg : genWf c = true) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable}
  {e : Valuation M} {L : List CtorSig} (hL : HeadsOK c L)
include hI hg hL

set_option linter.unusedSectionVars false

mutual
  /-- **The sort of a right-hand side, over its own variables**: the elements of a well-sorted
  right-hand side's translation, at a valuation of the term's variables in their sorts, lie in its
  sort (`rhsSort`, which asks it of every variable in scope). -/
  theorem rhsSort_at : ∀ {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx L) vars t = some s →
      (∀ i ∈ varOccs t, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i)))) →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m → InS I (c.sortName s) m
    | .var i, s, ht, hin, m, hm => by
      have hi := sortOfTerm_var.mp ht
      rw [tr_var] at hm
      rw [hm]
      have := hin i (by simp [varOccs])
      rwa [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
    | .dv s' lit, s, ht, _, m, hm => by
      have hdv : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.dv s' lit))).interpret I e m ↔
          (den c (.dv s' lit)).interpret I e m := by
        rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
        rw [KoreAML.tr_dv, KoreAML.tr_dv]
      rw [hdv] at hm
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      have hs := elemOf_spec hI (sortOf_dv.mpr ⟨hok, rfl⟩) e
      rw [(hs.1 m).mp hm]
      exact (inS_iff _).mp hs.2
    | .app f ts, s, ht, hin, m, hm => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk'
      rw [kore_app, tr_symApp, trArgs_appList, interp_appList] at hm
      obtain ⟨a, ha, bs, hbs, hm⟩ := hm
      have hsorts := rhsSorts_at hargs (fun i hi => hin i (by rw [varOccs]; exact hi)) hbs
      subst hkn
      exact head_arity hI (Model.rhsHead_kernel hL hkm) ha hsorts.1 hsorts.2 hm
    | .inj a b t, s, ht, hin, m, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := rhsSort_at ht' (fun i hi => hin i (by rw [varOccs]; exact hi)) x hx
      obtain ⟨y, hy, hys⟩ := gen_fun hI (genWf_sub hg hab).1 (gensF_inj hab) rfl (xs := [x]) rfl (single_sorts hxs)
      rw [(hys m).mp hm]; exact hy
    | .as _ _, s, ht, _, _, _ => absurd ht Model.sortOfTerm_rhs_as
  theorem rhsSorts_at : ∀ {ts : List Term} {ss : List Srt} {bs : List M},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss →
      (∀ i ∈ varOccsList ts, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i)))) →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      bs.length = (ss.map c.sortName).length ∧
        ∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x
    | [], ss, bs, ht, _, hbs => by
      rw [sortsOfTerms_nil.mp ht]
      rw [Term.koreList] at hbs
      cases hbs
      exact ⟨rfl, fun i x s h _ => by simp at h⟩
    | t :: ts, ss, bs, ht, hin, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [Term.koreList, List.map_cons] at hbs
      cases hbs with
      | cons hb hbs =>
        have ih := rhsSorts_at h2 (fun i hi => hin i (by rw [varOccsList]; exact List.mem_append_right _ hi)) hbs
        refine ⟨by simp [ih.1], fun i x s' hx hs' => ?_⟩
        cases i with
        | zero =>
          simp at hx hs'; subst hx; subst hs'
          exact rhsSort_at h1 (fun i hi => hin i (by rw [varOccsList]; exact List.mem_append_left _ hi)) _ hb
        | succ i => exact ih.2 i x s' (by simpa using hx) (by simpa using hs')
end

end

/-! ## Patterns that are the whole sort or nothing -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- At the valuation e, φ holds at one element of the sort τ iff at any other. -/
def PredAt (I : Interpretation KoreAML.Sym M) (τ : M) (φ : KoreAML.P) (e : Valuation M) : Prop :=
  ∀ m m', Inh I τ m → Inh I τ m' → (φ.interpret I e m ↔ φ.interpret I e m')

variable {τ : M} {e : Valuation M} {s φ ψ : KoreAML.P}

theorem predAt_form {Q : Prop} (h : ∀ m, φ.interpret I e m ↔ Q ∧ Inh I τ m) : PredAt I τ φ e :=
  fun m m' hm hm' => by
    rw [h m, h m']
    exact ⟨fun hq => ⟨hq.1, hm'⟩, fun hq => ⟨hq.1, hm⟩⟩

theorem predAt_sNot (hs : ∀ a, s.interpret I e a ↔ a = τ) (h : PredAt I τ φ e) :
    PredAt I τ (KoreAML.sNot s φ) e := fun m m' hm hm' => by
  rw [KoreAML.interp_sNot, KoreAML.interp_sNot, KoreAML.interp_inhOf_of hs, KoreAML.interp_inhOf_of hs,
    h m m' hm hm']
  exact ⟨fun hq => ⟨hq.1, hm'⟩, fun hq => ⟨hq.1, hm⟩⟩

theorem predAt_sAnd (h1 : PredAt I τ φ e) (h2 : PredAt I τ ψ e) : PredAt I τ (KoreAML.sAnd φ ψ) e :=
  fun m m' hm hm' => by
    rw [KoreAML.interp_sAnd, KoreAML.interp_sAnd, h1 m m' hm hm', h2 m m' hm hm']

theorem predAt_sOr (hs : ∀ a, s.interpret I e a ↔ a = τ) (h1 : PredAt I τ φ e) (h2 : PredAt I τ ψ e) :
    PredAt I τ (KoreAML.sOr s φ ψ) e := fun m m' hm hm' => by
  rw [KoreAML.interp_sOr, KoreAML.interp_sOr, KoreAML.interp_inhOf_of hs, KoreAML.interp_inhOf_of hs,
    h1 m m' hm hm', h2 m m' hm hm']
  exact ⟨fun hq => ⟨hm', hq.2⟩, fun hq => ⟨hm, hq.2⟩⟩

theorem predAt_sImp (hs : ∀ a, s.interpret I e a ↔ a = τ) (h1 : PredAt I τ φ e) (h2 : PredAt I τ ψ e) :
    PredAt I τ (KoreAML.sImp s φ ψ) e := fun m m' hm hm' => by
  rw [KoreAML.interp_sImp, KoreAML.interp_sImp, KoreAML.interp_inhOf_of hs, KoreAML.interp_inhOf_of hs,
    h1 m m' hm hm', h2 m m' hm hm']
  exact ⟨fun hq => ⟨hm', hq.2⟩, fun hq => ⟨hm, hq.2⟩⟩

/-- A sorted binder over a body that is a predicate at each element of the binder's sort. -/
theorem predAt_sExists (hD : DefOK I) {x : EVar} {s' : KoreAML.P} (hs' : Closed s')
    (h : ∀ a, (KoreAML.inhOf s').interpret I e a → PredAt I τ φ ⟨Function.update e.evalEvar x a, e.evalSvar⟩) :
    PredAt I τ (KoreAML.sExists x s' φ) e := fun m m' hm hm' => by
  rw [KoreAML.interp_sExists, KoreAML.interp_sExists]
  simp only [KoreAML.interp_member hD, Function.update_same]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, ha, (h a (((closed_inhOf_twoT hs').interp _ e a).mp ha) m m' hm hm').mp hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, ha, (h a (((closed_inhOf_twoT hs').interp _ e a).mp ha) m m' hm hm').mpr hb⟩

variable [Inhabited M]

/-- `existsAll` over a body that is a predicate at every valuation that differs from e at the
binders only and gives each binder an element of its sort. -/
theorem predAt_existsAll (hD : DefOK I) {tbl : VarTable} {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (e : Valuation M),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (∀ e₁ : Valuation M, (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e₁.evalEvar x = e.evalEvar x) →
      (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS I n (e₁.evalEvar (tbl.ev (KoreAML.evarKey b)))) →
      PredAt I τ (KoreAML.tr ⟨tbl, []⟩ body) e₁) →
    PredAt I τ (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)) e
  | [], e, _, _, h => h e (fun _ _ => rfl) (fun _ hb => absurd hb List.not_mem_nil)
  | b :: bs, e, hnd, hs, h => by
    show PredAt I τ (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body))) e
    obtain ⟨n, hn⟩ := hs b (List.mem_cons_self ..)
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [KoreAML.tr, hn, trSort_srt]
    refine predAt_sExists hD (KoreAML.Closed.sym _) fun a ha => ?_
    refine predAt_existsAll hD bs _ hnd.2 (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb'))
      fun e₁ hoff hg => h e₁ (fun x hx => ?_) (fun b' hb' n' hn' => ?_)
    · rw [hoff x (fun b' hb' => hx b' (List.mem_cons_of_mem _ hb'))]
      exact Function.update_noteq (hx b (List.mem_cons_self ..)) _ _
    · rcases List.mem_cons.mp hb' with rfl | hb''
      · rw [hoff _ (fun b'' hb'' he => hnd.1 (List.mem_map.mpr ⟨b'', hb'', he.symm⟩))]
        show InS I n' (Function.update e.evalEvar _ a _)
        rw [Function.update_same, ← srt_inj (hn.symm.trans hn')]
        exact (inS_iff _).mp ha
      · exact hg b' hb'' n' hn'

end

/-! ## A condition's pattern is a predicate -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The binders of the canonical variables at the indices `l` have named sorts. -/
theorem binders_sortEx {vars : List Srt} {l : List Nat} (hl : ∀ i ∈ l, i < vars.length) :
    ∀ b ∈ l.map (fun i => ((canonVars c vars).getD i default).kore), ∃ n, b.sort = KoreAML.srt n := fun b hb => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩

/-- A numbered sort denotes one element, a sort, under every table and valuation. -/
theorem srt_den (hI : I ⊧ᴵP Γ c) [OvlOK c] {s : Srt} (hs : s < nRegSorts + c.sortNames.length) :
    ∃ τ, IsSort I τ ∧ ∀ (tbl : VarTable) (e : Valuation M) (a : M),
      (KoreAML.trSort tbl (srtOf c s)).interpret I e a ↔ a = τ := by
  obtain ⟨σ, h1, h2⟩ := sortSing hI hs
  exact ⟨σ, h2, fun tbl e a => by rw [trSort_srtOf_twoT]; exact h1 a⟩

/-- A condition's term, at a valuation of its variables in their sorts, denotes elements of its sort. -/
theorem condTerm_inh (hI : I ⊧ᴵP Γ c) [OvlOK c] (hg : genWf c = true) {vars : List Srt} {tbl : VarTable}
    {e : Valuation M} {t : Term} {s : Srt} {τ : M}
    (hτ : ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.trSort tbl (srtOf c s)).interpret I e a ↔ a = τ)
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (hin : ∀ i ∈ varOccs t, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i)))) :
    ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e a → Inh I τ a := fun a ha =>
  (KoreAML.interp_inhOf_of (hτ tbl e)).mp
    (HoldsShape.inhOf_srtOf_inS.mpr (rhsSort_at hI hg fns_headsOK ht hin a ha))

/-- Under one more binder, at an element of its sort: each free variable of the body has its key in
the table and an element of its sort. -/
theorem binder_inS {vars : List Srt} {s : Srt} {body : Cond} {tbl : VarTable} {e : Valuation M}
    (hok : c.condOK (vars ++ [s]) body = true)
    (hK : canonKey c (vars ++ [s]) vars.length ∈ tbl)
    (hf : ∀ i ∈ varOccsCond (vars.length + 1) body, i < vars.length → canonKey c vars i ∈ tbl ∧
      InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    {a : M} (ha : InS I (c.sortName s) a) :
    ∀ i ∈ varOccsCond (vars ++ [s]).length body, canonKey c (vars ++ [s]) i ∈ tbl ∧
      InS I (c.sortName ((vars ++ [s]).getD i 0))
        ((⟨Function.update e.evalEvar (tbl.ev (canonKey c (vars ++ [s]) vars.length)) a, e.evalSvar⟩ :
          Valuation M).evalEvar (tbl.ev (canonKey c (vars ++ [s]) i))) := by
  intro i hi
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hlt := varOccsCond_lt_twoT body hok i hi
  rw [hlen] at hlt hi
  by_cases hin : i < vars.length
  · obtain ⟨h1, h2⟩ := hf i hi hin
    have hk' := Model.canonKey_appendStdI (c := c) (ys := [s]) hin
    rw [hk', Model.getD_appendL_stdI _ _ _ hin]
    refine ⟨h1, ?_⟩
    show InS I _ (Function.update e.evalEvar _ a _)
    rw [Function.update_noteq]
    · exact h2
    · intro he
      have := canonKey_inj (c := c) (vars := vars ++ [s]) (i := i) (j := vars.length) (by simp; omega) (by simp)
        (hk'.trans (ev_inj h1 hK he))
      omega
  · have hi' : i = vars.length := by omega
    subst hi'
    refine ⟨hK, ?_⟩
    have hs : (vars ++ [s]).getD vars.length 0 = s := by simp [List.getD_eq_getElem?_getD]
    show InS I (c.sortName ((vars ++ [s]).getD vars.length 0)) (Function.update e.evalEvar _ a _)
    rw [hs, Function.update_same]
    exact ha

/-- **A condition's pattern is a predicate**, by structural recursion on the condition: at a
valuation that gives each free variable an element of its sort, through a table holding the keys of
the pattern's variables, the pattern holds at one element of the sort `τS` that `S` denotes iff at
any other. -/
theorem cond_predAt (hI : I ⊧ᴵP Γ c) (hD : DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) [OvlOK c]
    (hg : genWf c = true) {S : Srt} {τS : M}
    (hτS : ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.trSort tbl (srtOf c S)).interpret I e a ↔ a = τS)
    (hσS : IsSort I τS) :
    ∀ (p : Cond) {vars : List Srt} {tbl : VarTable} {e : Valuation M}, c.condOK vars p = true →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    (∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
      InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
    PredAt I τS (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)) e
  | .top, vars, tbl, e, _, _, _ => predAt_form (Q := True) fun m => by
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sTop hD Model.srtOf_free_stdI, KoreAML.interp_inhOf_of (hτS tbl e)]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | .bot, vars, tbl, e, _, _, _ => predAt_form (Q := False) fun m => by
    rw [Cond.kore, KoreAML.tr]
    unfold KoreAML.sBot
    rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD Model.srtOf_free_stdI]
    exact ⟨fun h => (h.1 h.2).elim, fun h => h.1.elim⟩
  | .not p, vars, tbl, e, hok, hk, hf => by
    rw [Semantics.condOK] at hok
    have ih := cond_predAt hI hD hc hg hτS hσS p hok
      (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0))
      (fun i hi => hf i (by rw [varOccsCond]; exact hi))
    rw [Cond.kore, KoreAML.tr]
    exact predAt_sNot (hτS tbl e) ih
  | .and p q, vars, tbl, e, hok, hk, hf => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := cond_predAt hI hD hc hg hτS hσS p hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_left _ hk0)))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi))
    have ihq := cond_predAt hI hD hc hg hτS hσS q hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0))))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi))
    rw [Cond.kore, tr_and2]
    exact predAt_sAnd ihp ihq
  | .or p q, vars, tbl, e, hok, hk, hf => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := cond_predAt hI hD hc hg hτS hσS p hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_left _ hk0)))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi))
    have ihq := cond_predAt hI hD hc hg hτS hσS q hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0))))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi))
    rw [Cond.kore, Model.tr_or2Stdi]
    exact predAt_sOr (hτS tbl e) ihp ihq
  | .implies p q, vars, tbl, e, hok, hk, hf => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := cond_predAt hI hD hc hg hτS hσS p hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk0)))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi))
    have ihq := cond_predAt hI hD hc hg hτS hσS q hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0))
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi))
    rw [Cond.kore, KoreAML.tr]
    exact predAt_sImp (hτS tbl e) ihp ihq
  | .ceil s t, vars, tbl, e, hok, _, hf => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨ht, hs⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := srt_den hI hs
    rw [Cond.kore, KoreAML.tr]
    exact predAt_form fun m => KoreAML.interp_sCeil hD hc (hτ tbl e) (hτS tbl e) hσ hσS
      (condTerm_inh hI hg hτ ht fun i hi => (hf i (by rw [varOccsCond]; exact hi)).2) m
  | .equals s t u, vars, tbl, e, hok, _, _ => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨-, hs⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := srt_den hI hs
    rw [Cond.kore, KoreAML.tr]
    exact predAt_form fun m => (KoreAML.interp_sEquals hD hc (hτ tbl e) (hτS tbl e) hσ hσS m).trans and_comm
  | .mem s t u, vars, tbl, e, hok, _, hf => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨ht, -⟩, hs⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := srt_den hI hs
    rw [Cond.kore, KoreAML.tr]
    exact predAt_form fun m => KoreAML.interp_sIn hD hc (hτ tbl e) (hτS tbl e) hσ hσS
      (condTerm_inh hI hg hτ ht fun i hi => (hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi)).2) m
  | .exMatch ys s p t body, vars, tbl, e, hok, hk, hf => by
    have hok0 := hok
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hpS, htS⟩, hbody⟩, hsN⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := srt_den hI hsN
    have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.exMatch ys s p t body) =
        KoreAML.existsAll (srtOf c S)
          ((List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore)
          (.and (srtOf c S)
            [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
             Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body]) := by
      rw [← Model.binders_eqStdI (c := c) vars ys, ← Model.canonVars_appendStdI c vars ys]; rfl
    rw [hkore] at hk ⊢
    have hl : ∀ i ∈ List.range' vars.length ys.length, vars.length ≤ i ∧ i < (vars ++ ys).length :=
      fun i hi => by
        have := List.mem_range'_1.mp hi
        simp only [List.length_append]; omega
    have hkB : ∀ i ∈ List.range' vars.length ys.length, canonKey c (vars ++ ys) i ∈ tbl := fun i hi =>
      hk _ (varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c (vars ++ ys)).getD i default).kore) hi))
    have hnd : (((List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore).map
        fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
      rw [List.map_map]
      refine List.pairwise_map.mpr ((List.nodup_range' (s := vars.length) (n := ys.length)).imp_of_mem fun {i j} hi hj hne he => hne ?_)
      exact canonKey_inj (hl i hi).2 (hl j hj).2 (ev_inj (hkB i hi) (hkB j hj) he)
    have hsrt := binders_sortEx (c := c) (vars := vars ++ ys) (l := List.range' vars.length ys.length)
      fun i hi => (hl i hi).2
    -- off the binders, the outer free variables keep their elements
    have hout : ∀ i ∈ varOccsCond vars.length (.exMatch ys s p t body), ∀ e₁ : Valuation M,
        (∀ x, (∀ b ∈ (List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore,
          x ≠ tbl.ev (KoreAML.evarKey b)) → e₁.evalEvar x = e.evalEvar x) →
        e₁.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) := by
      intro i hi e₁ hoff
      refine hoff _ fun b hb he => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hlt := varOccsCond_lt_twoT (.exMatch ys s p t body) hok0 i hi
      have := canonKey_inj (c := c) (vars := vars ++ ys) (i := i) (j := j) (by simp only [List.length_append]; omega)
        (hl j hj).2 ((Model.canonKey_appendStdI hlt).trans (ev_inj (hf i hi).1 (hkB j hj) he))
      have := (hl j hj).1
      omega
    refine predAt_existsAll hD _ e hnd hsrt fun e₁ hoff hguard => ?_
    rw [tr_and2]
    refine predAt_sAnd ?_ ?_
    · rw [KoreAML.tr]
      refine predAt_form fun m => KoreAML.interp_sIn hD hc (hτ tbl e₁) (hτS tbl e₁) hσ hσS
        (condTerm_inh hI hg hτ htS fun i hi => ?_) m
      have hiO : i ∈ varOccsCond vars.length (.exMatch ys s p t body) := by
        rw [varOccsCond]; exact List.mem_append_left _ hi
      rw [hout i hiO e₁ hoff]; exact (hf i hiO).2
    · refine cond_predAt hI hD hc hg hτS hσS body hbody (fun k hk0 => hk k (HoldsShape.varsOf_existsAll_bodyHF
        (Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk0) _)) fun i hi => ?_
      have hlt := varOccsCond_lt_twoT body hbody i hi
      have hlen : (vars ++ ys).length = vars.length + ys.length := by simp
      rw [hlen] at hlt hi
      by_cases hin : i < vars.length
      · have hiO : i ∈ varOccsCond vars.length (.exMatch ys s p t body) := by
          rw [varOccsCond]
          exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append_right _ hi, by simpa using hin⟩)
        rw [Model.canonKey_appendStdI hin, Model.getD_appendL_stdI _ _ _ hin, hout i hiO e₁ hoff]
        exact hf i hiO
      · have hil : i ∈ List.range' vars.length ys.length := List.mem_range'_1.mpr ⟨by omega, by omega⟩
        refine ⟨hkB i hil, hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c (vars ++ ys)).getD i default).kore) hil) _ ?_⟩
        show ((canonVars c (vars ++ ys)).getD i default).kore.sort = _
        rw [canonVars_getD c (show i < (vars ++ ys).length by rw [hlen]; exact hlt)]; rfl
  | .ex s body, vars, tbl, e, hok, hk, hf => by
    rw [Semantics.condOK] at hok
    have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.ex s body) =
        .exist (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
          (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
      rw [← Model.canonVars_snocStdI c vars s]; rfl
    rw [hkore] at hk
    have hkb := Model.binder_keyStdI (c := c) vars s
    have hK := hk (canonKey c (vars ++ [s]) vars.length) (by rw [KoreAML.varsOf, hkb]; simp)
    have hbs : (Cond.binder c (canonVars c vars).length s).kore.sort = srtOf c s := rfl
    rw [hkore, KoreAML.tr, hbs, hkb, trSort_srtOf_twoT]
    exact predAt_sExists hD (KoreAML.Closed.sym _) fun a ha => cond_predAt hI hD hc hg hτS hσS body hok
      (fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0))
      (binder_inS hok hK (fun i hi hl => hf i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hl⟩))
        ((inS_iff e).mp ha))
  | .all s body, vars, tbl, e, hok, hk, hf => by
    rw [Semantics.condOK] at hok
    have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.all s body) =
        .forall (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
          (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
      rw [← Model.canonVars_snocStdI c vars s]; rfl
    rw [hkore] at hk
    have hkb := Model.binder_keyStdI (c := c) vars s
    have hK := hk (canonKey c (vars ++ [s]) vars.length) (by rw [KoreAML.varsOf, hkb]; simp)
    have hbs : (Cond.binder c (canonVars c vars).length s).kore.sort = srtOf c s := rfl
    rw [hkore, KoreAML.tr, hbs, hkb]
    unfold KoreAML.sForall
    refine predAt_sNot (hτS tbl e) ?_
    rw [trSort_srtOf_twoT]
    exact predAt_sExists hD (KoreAML.Closed.sym _) fun a ha => predAt_sNot (hτS tbl _)
      (cond_predAt hI hD hc hg hτS hσS body hok
        (fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0))
        (binder_inS hok hK (fun i hi hl => hf i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hl⟩))
          ((inS_iff e).mp ha)))

end

end Faithful

end KCore
