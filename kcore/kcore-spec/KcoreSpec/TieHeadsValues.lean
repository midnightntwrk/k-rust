/-
  The heads of the values and graphs in Γ (`ΓDomains`, `ΓFallback`): each applies only heads of Γ
  (`gammaHeadsP`), under `coreOK`.

  - **A value's KORE applies Γ's heads only** (`kore_val`). A value of a sort is a constructor, an
    overloading symbol or an open generator (a raw parameter) applied to values, each a symbol of
    Γ named plainly (`sortOf_ctor_iff`, `ovl_parts`, `lookupOpen_spec` with `raw_of_core`); an
    injection from a subsort (`sortOf_inj`); a domain value; or a collection of a collection sort
    (`collOf`), whose unit, element and concatenation are symbols of Γ named plainly
    (`collSyms_ks`).
  - **A graph applies its symbol at its head of Γ** (`symApp_gammaHead`), to values, and equates
    it with a value of the symbol's result sort (`hook_sorted`, `paramVal_sorted`,
    `fallback_sorted`, `fnRest_sorted`) or with ⊥.
-/
import KcoreSpec.TieHeadsAml

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GHVal

open KoreAML (P)
open GHWalk GHAml

variable {c : Semantics}

/-- A collection of `allColls`'s symbols are heads of Γ as the KORE writes them. -/
theorem collSym_mem (h : c.coreOK = true) {k : CollSig} (hk : k ∈ c.allColls) {f : Sym}
    (hf : f ∈ [k.unit, k.elem, k.concat]) : (c.symName f, []) ∈ gammaHeads c := by
  obtain ⟨k', hk', rfl, hi⟩ := collSyms_ks h hk f hf
  exact plain_mem hk' hi

/-- The collection of a sort is one of `allColls`. -/
theorem collOf_mem {s : Srt} {k : CollSig} (h : c.collOf s = some k) : k ∈ c.allColls :=
  List.mem_of_find?_eq_some h

/-- The symbol of a value applied to values is a symbol of Γ named plainly, under `coreOK`: a
constructor, an overloading symbol or an open generator. -/
theorem valHead_mem (h : c.coreOK = true) {f : Sym} {ts : List GroundTerm} {s : Srt}
    (hs : c.sortOf (.ctor f ts) = some s) :
    (c.symName f, []) ∈ gammaHeads c ∧ ∃ ss, c.sortsOf ts = some ss := by
  rcases (c.sortOf_ctor_iff).mp hs with ⟨k, hk, hts, -⟩ | ⟨-, o, ho, hts, -, -⟩ | ⟨-, -, k, hk, hts, -, -⟩
  · rw [lookupSig_eq] at hk
    have hn : k.name = f := by simpa using List.find?_some hk
    have hm := List.mem_of_find?_eq_some hk
    refine ⟨?_, _, hts⟩
    rw [← hn]; exact plain_mem (ks_ctor hm) (ctor_ite h hm)
  · obtain ⟨ho', hn, -⟩ := OvlLaws.ovl_parts (Semantics.coreOK_ovls h) ho
    have hi := OvlLaws.ovl_noInst_irs (Semantics.coreOK_ovls h) ho
    refine ⟨?_, _, hts⟩
    have := plain_mem (ks_ovl (List.mem_map_of_mem (f := (·.sig)) ho')) (by rw [hn]; exact hi)
    rwa [hn] at this
  · obtain ⟨hk', hr, hn, -⟩ := c.lookupOpen_spec hk
    refine ⟨?_, _, hts⟩
    have := plain_mem (ks_param hk') (Semantics.raw_noInst_core_irs h hk' hr)
    rwa [hn] at this

section
variable (h : c.coreOK = true)
include h

mutual
/-- **A value's KORE applies Γ's heads only**, under `coreOK`. -/
theorem kore_val : ∀ (v : GroundTerm) (s : Srt), c.sortOf v = some s →
    ∀ x ∈ appHeadsOf (v.kore c), x ∈ gammaHeads c
  | .ctor f ts, s, hs, x, hx => by
    obtain ⟨hf, ss, hts⟩ := valHead_mem h hs
    simp only [GroundTerm.kore, appHeadsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf
    · exact koreList_val ts ss hts x hx
  | .inj a b t, s, hs, x, hx => by
    obtain ⟨hab, -, ht, -⟩ := (sortOf_inj (c := c)).mp hs
    simp only [GroundTerm.kore, KoreAML.injP, appHeadsOf, appHeadsOfList, List.append_nil,
      List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact inj_mem hab
    · exact kore_val t a ht x hx
  | .dv _ _, _, _, x, hx => by simp [GroundTerm.kore, appHeadsOf] at hx
  | .map s es, s', hs, x, hx => by
    cases hk : c.collOf s with
    | none => simp [Semantics.sortOf, hk] at hs
    | some k =>
      cases hv : k.val with
      | none => simp [Semantics.sortOf, hk, hv] at hs
      | some vs =>
        cases he : c.entriesOK k.key vs es with
        | false => simp [Semantics.sortOf, hk, hv, he] at hs
        | true =>
          have hsig : c.collSig .map s = k := by simp [Semantics.collSig, hk]
          simp only [GroundTerm.kore, hsig] at hx
          exact koreEntries_val (collOf_mem hk) es k.key vs he x hx
  | .set s es, s', hs, x, hx => by
    cases hk : c.collOf s with
    | none => simp [Semantics.sortOf, hk] at hs
    | some k =>
      cases hss : c.sortsOf es with
      | none => simp [Semantics.sortOf, hk, hss] at hs
      | some ss =>
        have hsig : c.collSig .set s = k := by simp [Semantics.collSig, hk]
        simp only [GroundTerm.kore, hsig] at hx
        exact koreElems_val (collOf_mem hk) es ss hss x hx
  | .list s es, s', hs, x, hx => by
    cases hk : c.collOf s with
    | none => simp [Semantics.sortOf, hk] at hs
    | some k =>
      cases hss : c.sortsOf es with
      | none => simp [Semantics.sortOf, hk, hss] at hs
      | some ss =>
        have hsig : c.collSig .list s = k := by simp [Semantics.collSig, hk]
        simp only [GroundTerm.kore, hsig] at hx
        exact koreElems_val (collOf_mem hk) es ss hss x hx
  termination_by structural v => v

theorem koreList_val : ∀ (vs : List GroundTerm) (ss : List Srt), c.sortsOf vs = some ss →
    ∀ x ∈ appHeadsOfList (GroundTerm.koreList c vs), x ∈ gammaHeads c
  | [], _, _, x, hx => by simp [GroundTerm.koreList, appHeadsOfList] at hx
  | v :: vs, ss, hss, x, hx => by
    simp only [Semantics.sortsOf] at hss
    split at hss
    · rename_i s ss' hv hvs
      simp only [GroundTerm.koreList, appHeadsOfList, List.mem_append] at hx
      rcases hx with hx | hx
      · exact kore_val v s hv x hx
      · exact koreList_val vs ss' hvs x hx
    · cases hss
  termination_by structural vs => vs

theorem koreEntries_val {k : CollSig} (hk : k ∈ c.allColls) : ∀ (es : List (GroundTerm × GroundTerm))
    (ks vs : Srt), c.entriesOK ks vs es = true → ∀ x ∈ appHeadsOf (GroundTerm.koreEntries c k es), x ∈ gammaHeads c
  | [], _, _, _, x, hx => by
    simp only [GroundTerm.koreEntries, KoreAML.ap, appHeadsOf, appHeadsOfList, List.mem_singleton] at hx
    subst hx; exact collSym_mem h hk (List.mem_cons_self ..)
  | [e], ks, vs, he, x, hx => by
    simp only [Semantics.entriesOK, Bool.and_eq_true] at he
    simp only [GroundTerm.koreEntries] at hx
    exact koreEntry_val hk e ks vs he.1 x hx
  | e :: e' :: es, ks, vs, he, x, hx => by
    simp only [Semantics.entriesOK, Bool.and_eq_true] at he
    simp only [GroundTerm.koreEntries, KoreAML.ap, appHeadsOf, appHeadsOfList, List.append_nil, List.mem_cons,
      List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact collSym_mem h hk (by simp)
    · exact koreEntry_val hk e ks vs he.1 x hx
    · have : c.entriesOK ks vs (e' :: es) = true := by
        simp only [Semantics.entriesOK, Bool.and_eq_true]; exact he.2
      exact koreEntries_val hk (e' :: es) ks vs this x hx
  termination_by structural es => es

theorem koreEntry_val {k : CollSig} (hk : k ∈ c.allColls) : ∀ (e : GroundTerm × GroundTerm) (ks vs : Srt),
    c.entryOK ks vs e = true → ∀ x ∈ appHeadsOf (GroundTerm.koreEntry c k e), x ∈ gammaHeads c
  | (a, b), ks, vs, he, x, hx => by
    simp only [Semantics.entryOK, Bool.and_eq_true, beq_iff_eq] at he
    simp only [GroundTerm.koreEntry, KoreAML.ap, appHeadsOf, appHeadsOfList, List.append_nil, List.mem_cons,
      List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact collSym_mem h hk (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact kore_val a ks he.1 x hx
    · exact kore_val b vs he.2 x hx
  termination_by structural e => e

theorem koreElems_val {k : CollSig} (hk : k ∈ c.allColls) : ∀ (es : List GroundTerm) (ss : List Srt),
    c.sortsOf es = some ss → ∀ x ∈ appHeadsOf (GroundTerm.koreElems c k es), x ∈ gammaHeads c
  | [], _, _, x, hx => by
    simp only [GroundTerm.koreElems, KoreAML.ap, appHeadsOf, appHeadsOfList, List.mem_singleton] at hx
    subst hx; exact collSym_mem h hk (List.mem_cons_self ..)
  | [e], ss, hss, x, hx => by
    simp only [Semantics.sortsOf] at hss
    split at hss
    · rename_i s ss' hv _
      simp only [GroundTerm.koreElems, KoreAML.ap, appHeadsOf, appHeadsOfList, List.append_nil, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact collSym_mem h hk (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact kore_val e s hv x hx
    · cases hss
  | e :: e' :: es, ss, hss, x, hx => by
    simp only [Semantics.sortsOf] at hss
    split at hss
    · rename_i s ss' hv hvs
      simp only [GroundTerm.koreElems, KoreAML.ap, appHeadsOf, appHeadsOfList, List.append_nil, List.mem_cons,
        List.mem_append] at hx
      rcases hx with rfl | (rfl | hx) | hx
      · exact collSym_mem h hk (by simp)
      · exact collSym_mem h hk (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact kore_val e s hv x hx
      · exact koreElems_val hk (e' :: es) ss' hvs x hx
    · cases hss
  termination_by structural es => es
end

/-- **A value's pattern applies Γ's heads only**, under `coreOK`. -/
theorem den_val {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) : InGH c (den c v) :=
  headsP_tr_gamma c _ _ (kore_val h v s hv)

/-- A value or ⊥ applies Γ's heads only. -/
theorem den_opt {r : Option GroundTerm} (hr : ∀ v, r = some v → ∃ s, c.sortOf v = some s) :
    InGH c (match (generalizing := false) r with
      | some v => den c v
      | none => ⊥) := by
  cases r with
  | none => exact inGH_bot
  | some v => obtain ⟨s, hs⟩ := hr v rfl; exact den_val h hs

end

/-- **The application of a symbol of Γ to values applies Γ's heads only**: the symbol at its head
of Γ (`symApp_gammaHead`), and the values'. -/
theorem symApp_val (h : c.coreOK = true) {k : CtorSig} (hk : k ∈ kernelSyms c) {vs : List GroundTerm}
    {ss : List Srt} (hvs : c.sortsOf vs = some ss) :
    InGH c (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))) := by
  refine headsP_tr_gamma c _ _ fun x hx => ?_
  rw [symApp_gammaHead] at hx
  simp only [appHeadsOf, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact List.mem_append_left _ (List.mem_map_of_mem hk)
  · exact koreList_val h vs ss hvs x hx

/-- **The domains apply Γ's heads only**, under `coreOK`: the graphs of the interpreted hooked
symbols and of the parameter symbols, the values' elements, their distinctness, and no junk in
each collection sort. -/
theorem ΓDomains_inGH (h : c.coreOK = true) : ∀ φ, ΓDomains c φ → InGH c φ := by
  rintro φ (⟨k, vs, r, hk, hvs, hr, -, rfl⟩ | ⟨k, vs, hk, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ | ⟨v, w, s, -, hv, hw, -, rfl⟩ |
    ⟨k, hk, rfl⟩)
  · refine inGH_eq (symApp_val h (ks_hook hk) hvs) (den_opt h fun v hrv => ?_)
    subst hrv
    exact ⟨_, hook_sorted (fun _ => rangeBelow_of_core h) (hookSigs_lookup k hk) hvs hr⟩
  · refine inGH_eq (symApp_val h (ks_param hk) hvs) (den_opt h fun v hpv => ?_)
    obtain ⟨_, -, hs⟩ := c.paramVal_sorted hpv
    exact ⟨_, hs⟩
  · exact inGH_sExists _ (inGH_sortP _) (inGH_eq (den_val h hv) (inGH_evar _))
  · exact inGH_neg (inGH_and (den_val h hv) (den_val h hw))
  · exact collNoJunk_inGH h hk

/-- **What the interpretation decides where the text is silent applies Γ's heads only**, under
`coreOK`: the graphs of the interpreted hooked symbols at their silent points, and of each
function where every clause fails. -/
theorem ΓFallback_inGH (h : c.coreOK = true) : ∀ φ, ΓFallback c φ → InGH c φ := by
  rintro φ (⟨k, vs, hk, hvs, -, -, rfl⟩ | ⟨fn, vs, hfn, hvs, -, rfl⟩)
  · refine inGH_eq (symApp_val h (ks_hook hk) hvs) (den_opt h fun v hfv => ?_)
    exact ⟨_, c.fallback_sorted (hookSigs_lookup k hk) hfv⟩
  · refine inGH_eq (symApp_val h (k := fn.sig) (ks_fn hfn) hvs) (den_opt h fun v hfv => ?_)
    exact ⟨_, Semantics.fnRest_sorted hfv⟩

end GHVal

end KCore
