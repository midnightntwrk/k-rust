/-
  KCore. A clause's predicate in its sentences, at one evaluation.

  A clause's premise carries its predicate at the sort variable `R` (`withPre`). `holdsAt_atR` reads
  it there from the reading of one truth value `Holds` gives (`HoldsAt`, which a recursion on
  evaluations supplies: `holds_den4Cl`): `holds_atR` at one evaluation. `withPre_interp` splits the
  premise of a clause whose predicate is not `\top`. `nodeFacts_of_core`: every model of `Γc` of a
  definition `coreOK` accepts has the constructors' facts.
-/
import KcoreSpec.CondResort
import KcoreSpec.HoldsNode

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
theorem holdsAt_atR (F : NodeFacts c I) (hT : TermsInSort c I) {p : Cond}
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M}
    (hp : HoldsAt c I vars.length σ p b) (hσ : c.WellSorted vars σ)
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
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
  exact hp rfl hσ hok hbd hP hr (fun k hk0 => hk k (condKore_varsOf_resort (sortVarsOf_srtOf c Srt.bool) p _ k hk0))
    hS a0 ha0

omit [Inhabited M] in
/-- The premise of a clause whose predicate is not `\top`, read: the premise without the predicate
and the predicate at `R`. -/
theorem withPre_interp {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern} (hne : cl.pre.isTop = false)
    {tbl : KoreAML.VarTable} {e : Valuation M} {m : M} :
    (KoreAML.tr ⟨tbl, []⟩ (withPre c vs cl prem)).interpret I e m ↔
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret I e m ∧
        (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs KoreAML.R cl.pre)).interpret I e m := by
  unfold withPre
  rw [hne, if_neg (by simp), tr_and2, KoreAML.interp_sAnd]

end

end HoldsShape

end KCore
