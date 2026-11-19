/-
  KCore. A clause's predicate in its sentences, at one evaluation.

  A clause's premise carries its predicate at the sort variable `R` (`withPre`). `holdsAt_atR` reads
  it there from the reading of one truth value `Holds` gives over a Bool that bounds its binders
  (`HoldsAtB`): `holds_atR` at one evaluation. `preRead_ofB` gives what the clause lemmas ask of the
  model for a clause's predicate (`PreRead`, ClausePreRead.lean) from a Bool that bounds its binders
  and the reading over it of each truth value that comes with its terms' readings (`HoldsRead`,
  which a recursion on evaluations supplies: `holdsRead_den4ClPre`); `preRead_of` is it at
  `Cond.boundConf`, through `HoldsReadT.holdsAt`. So `eval_den4ClPre` and `exclEmptyCl_ofCl` hold
  for clauses with a predicate in the premise.
  `nodeFacts_of_core`: every model of `Γc` of a definition `coreOK` accepts has the constructors'
  facts.
-/
import KcoreSpec.CondCross
import KcoreSpec.ClausePreRead

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace HoldsShape

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A model of `Γc` of a definition `coreOK` accepts has the constructors' facts.** -/
theorem nodeFacts_of_core (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) : NodeFacts c I := by
  have htn : ∀ {vars : List Srt} {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
      (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
      s < nRegSorts + c.sortNames.length := fun {vars t s} ht hv =>
    sortOfTerm_numbered (sortOf_numbered_of (hypSound_of_core h) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h)) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h)
      (fun k hk => Model.rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl t ht hv
  have hvn : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length :=
    fun hv => sortOf_numbered_of (hypSound_of_core h) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hv
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  refine ⟨defOK hI, sat_sigItem hI (by simp [sigItems]), fun {s} hs => ?_, fun {v s} hv tbl e => ?_,
    fun {v w s} hv hw e a h1 h2 => ?_, hsc, htn, hvn⟩
  · obtain ⟨τ, hτ, hτs⟩ := sortSing hI hs
    exact ⟨τ, hτs, fun tbl e a => by unfold srtOf; rw [trSort_srt]; exact hτ a⟩
  · refine ⟨elemOf c I v, (elemOf_spec hI hv e).1, ?_⟩
    have := (elemOf_spec hI hv e).2
    unfold srtOf; rw [trSort_srt]; exact this
  · exact values_apart hI hg hsc.trans (apartSort_of_sorted hg hv) hv hw
      (((elemOf_spec hI hv e).1 a).mp h1 ▸ ((elemOf_spec hI hw e).1 a).mp h2 ▸ rfl)

/-- **One truth value of a condition, read at the sort variable `R`**: where the truth value b
that `Holds` gives p under σ is read in I (`HoldsAt`), at a valuation that reads p's free
variables as their values under σ and gives `R` a sort `σr`, through a table holding `R` and the
variables of the pattern at `R`, an element of `σr` is in `Cond.kore … R p` exactly where b is
`true`. -/
theorem holdsAt_atR (F : NodeFacts c I) (hT : TermsInSort c I) {bd : Nat → Cond → Bool} {p : Cond}
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M}
    (hp : HoldsAtB bd c I vars.length σ p b)
    (hok : c.condOK vars p = true) (hbd : bd vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : Reads c I vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) KoreAML.R p), k ∈ tbl)
    (hRm : KoreAML.VarKey.sortVar "R" ∈ tbl) {σr : M}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) (hσr : KoreAML.IsSort I σr)
    (a : M) (ha : KoreAML.Inh I σr a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) KoreAML.R p)).interpret I e a ↔ b = true := by
  have hS : Srt.bool < nRegSorts + c.sortNames.length := F.valNum (sortOf_bool (c := c) true)
  obtain ⟨a0, -, ha0⟩ := F.val (sortOf_bool (c := c) true) tbl e
  obtain ⟨τS, hσS, hτS⟩ := F.sort hS
  have hRe : e.evalEvar (tbl.ev (.sortVar "R")) = σr :=
    ((hR _).mp (by rw [trSort_R, KoreAML.interp_evar])).symm ▸ rfl
  have hf : ∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
      InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))) := fun i hi => by
    have hPi := hP i hi (varOccsCond_lt_twoT p hok i hi)
    exact ⟨(hr i hPi).2.1, inhOf_srtOf_inS.mp (hr.inSortN F hPi)⟩
  rw [cond_crossAt F.defOK F.ceilDef F.sort hT hτS hσS hσr p hok hk hRm hf hRe a a0 ha
    ((KoreAML.interp_inhOf_of (hτS tbl e)).mp ha0)]
  exact hp rfl hok hbd hP hr (fun k hk0 => hk k (condKore_varsOf_resort (sortVarsOf_srtOf c Srt.bool) p _ k hk0))
    hS a0 ha0

/-- A condition without a binder has every binder in a sort where values and elements agree. -/
theorem _root_.KCore.Cond.boundConf_of_noBinder (c : Semantics) :
    ∀ (p : Cond) (n : Nat), hasBinder p = false → Cond.boundConf c n p = true
  | .top, _, _ | .bot, _, _ | .ceil .., _, _ | .equals .., _, _ | .mem .., _, _ => by simp [Cond.boundConf]
  | .exMatch .., _, h | .ex .., _, h | .all .., _, h => by simp [hasBinder] at h
  | .not p, n, h => by
    rw [hasBinder] at h; rw [Cond.boundConf]; exact Cond.boundConf_of_noBinder c p n h
  | .and p q, n, h | .or p q, n, h | .implies p q, n, h => by
    rw [hasBinder, Bool.or_eq_false_iff] at h; rw [Cond.boundConf, Bool.and_eq_true]
    exact ⟨Cond.boundConf_of_noBinder c p n h.1, Cond.boundConf_of_noBinder c q n h.2⟩

/-- **A clause's predicate is read in I** (`PreRead`): in an interpretation with the constructors'
facts and the elements of well-sorted terms in their sorts, for a predicate that is well sorted
with binders a Bool `bd` bounds, where each truth value `Holds` gives it with its terms' readings
(`HoldsRead`) is read in I over `bd`. That reading is read at `R` by `holdsAt_atR`, the sorts of
the variables outside the clause's patterns and conditions being any (`condOK_congrVars`,
`condKore_congrCanon`); the predicate at `R` is the predicate at Bool (`cond_crossAt`), which reads
its variables' elements only (`tr_condKore_twoT`). -/
theorem preRead_ofB {cl : Clause} (F : NodeFacts c I) (hT : TermsInSort c I)
    (hok : c.condOK cl.vars cl.pre = true) {bd : Nat → Cond → Bool} (hbd : bd cl.vars.length cl.pre = true)
    (hconv : ∀ {σ : Subst} {b : Bool}, HoldsRead c I cl.vars.length σ cl.pre b →
      HoldsAtB bd c I cl.vars.length σ cl.pre b) : PreRead c I cl where
  atR := by
    intro vars σ b tbl e σr hH hlen hagl hσ hrd hk hRm hR hσr a ha
    have hocc : ∀ i, i ∈ varOccsCond vars.length cl.pre → i ∈ varOccsCond cl.vars.length cl.pre :=
      fun i hi => by rw [← hlen]; exact hi
    have hagP : ∀ i ∈ varOccsCond vars.length cl.pre, vars[i]? = cl.vars[i]? := fun i hi =>
      hagl i (Clause.pre_leftVarsRH i (hocc i hi))
    have hokV : c.condOK vars cl.pre = true := by rw [condOK_congrVars cl.pre hlen hagP]; exact hok
    have hkore : Cond.kore c (canonVars c vars) KoreAML.R cl.pre =
        Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre := condKore_congrCanon KoreAML.R cl.pre hlen hagP
    have hlt : ∀ i ∈ varOccsCond vars.length cl.pre, i < vars.length := varOccsCond_lt_twoT cl.pre hokV
    have hkey : ∀ i ∈ varOccsCond vars.length cl.pre, canonKey c vars i = canonKey c cl.vars i := fun i hi => by
      unfold canonKey; rw [canonVars_getD_congrVars c hlen (hagP i hi)]
    have hr : Reads c I vars (fun i => i ∈ varOccsCond vars.length cl.pre) σ tbl e := fun i hi => by
      have hi' := hlt i hi
      obtain ⟨v, hv, hsv⟩ := hσ i vars[i] (List.getElem?_eq_getElem hi')
      refine ⟨hi', ?_, v, hv, ?_, ?_⟩
      · rw [hkey i hi]
        exact hk _ (Model.condKore_keys KoreAML.R cl.pre (bound := []) (by rw [← hlen]; exact hi') (hocc i hi) rfl).2
      · rw [hsv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
      · rw [hkey i hi]; exact hrd i (hocc i hi) v hv
    rw [← hkore]
    exact holdsAt_atR F hT (by rw [hlen]; exact hconv hH) hokV (by rw [hlen]; exact hbd)
      (fun i hi _ => hi) hr
      (by rw [hkore]; exact hk) hRm hR hσr a ha
  toBool := by
    intro tbl tbl' e e' σr m mB hk hRm hk' hf hR hσr hm hmB h
    have hS : Srt.bool < nRegSorts + c.sortNames.length := F.valNum (sortOf_bool (c := c) true)
    obtain ⟨τS, hσS, hτS⟩ := F.sort hS
    have hRe : e.evalEvar (tbl.ev (.sortVar "R")) = σr :=
      ((hR _).mp (by rw [trSort_R, KoreAML.interp_evar])).symm ▸ rfl
    have hlt := varOccsCond_lt_twoT cl.pre hok
    have hkey : ∀ i ∈ varOccsCond cl.vars.length cl.pre, canonKey c cl.vars i ∈ tbl := fun i hi =>
      hk _ (Model.condKore_keys KoreAML.R cl.pre (bound := []) (hlt i hi) hi rfl).2
    have hkey' : ∀ i ∈ varOccsCond cl.vars.length cl.pre, canonKey c cl.vars i ∈ tbl' := fun i hi =>
      hk' _ (Model.condKore_keys (srtOf c Srt.bool) cl.pre (bound := []) (hlt i hi) hi rfl).2
    have h1 := (cond_crossAt F.defOK F.ceilDef F.sort hT hτS hσS hσr cl.pre hok hk hRm
      (fun i hi => ⟨hkey i hi, (hf i hi).1⟩) hRe m mB hm ((KoreAML.interp_inhOf_of (hτS tbl' e')).mp hmB)).mp h
    exact (tr_condKore_twoT F.defOK cl.pre hok
      (fun k hk0 => ⟨hk k (condKore_varsOf_resort (sortVarsOf_srtOf c Srt.bool) cl.pre _ k hk0), hk' k hk0⟩)
      (fun i hi => ⟨hkey i hi, hkey' i hi, (hf i hi).2⟩) mB).mp h1

/-- **A clause's predicate is read in I over `Cond.boundConf`** (`preRead_ofB`): in an
interpretation with the constructors' facts, the binders' where the predicate holds a binder, and
the elements of well-sorted terms in their sorts, a truth value with its terms' readings is read in
I (`HoldsReadT.holdsAt`). -/
theorem preRead_of {cl : Clause} (F : NodeFacts c I) (G : hasBinder cl.pre = true → BinderFacts c I)
    (hT : TermsInSort c I) (hok : c.condOK cl.vars cl.pre = true)
    (hbd : Cond.boundConf c cl.vars.length cl.pre = true) : PreRead c I cl :=
  preRead_ofB F hT hok hbd fun hh => HoldsReadT.holdsAt F hh G

end

end HoldsShape

end KCore
