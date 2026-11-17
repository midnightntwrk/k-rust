/-
  KCore, checked layer: the collection laws are entailed at values (`EntailsAtValues`), for every
  semantics meeting `coreOK` whose Map, Set and List values are collections (`shapesOK`) and every
  interpretation.

  A collection law is the sentence kompile writes for the `assoc` and `unit` attributes of a
  collection's concatenation: `\equals{s, R}(l, r)` over the sort variable `R`, `l` and `r` terms
  over element variables and interpreted hooked symbols.

  - `LibEv.Law`: such an equation; `Law.Holds`: its sides have the same value, or both none, at
    every substitution of values of the variables' sorts; `Law.entailed`, `Law.entailed_reg`: a law
    that holds is entailed at values, whatever axiom declaration of a text holds its pattern.
  - `lawAssoc f s`, `lawUnitR f u s`, `lawUnitL f u s`: associativity and the two units of the
    symbol `f` with unit `u` at the sort `s`, in the variable names kompile writes (`K1`, `K2`,
    `K3`; `K`).
  - They hold of `_List_` (concatenation, total), of `_Set_` (the union of two sets without a
    common member: both groupings have a value exactly where the three sets are pairwise without
    a common member, and then the same) and of `_Map_` (the same with keys): `listAssoc_ev` …
    `mapUnitL_ev`.
-/
import KcoreSpec.LibEvFnColl

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- A collection law `lhs = rhs` over the variables `vars`, its sides of the sort `s`. -/
structure Law where
  vars : Vars
  s : Srt
  lhs : Term
  rhs : Term

namespace Law

/-- The pattern of the law's axiom, as kompile writes it over the sort variable `R`. -/
def pattern (c : Semantics) (E : Law) : Kore.Pattern :=
  .equals (srtOf c E.s) KoreAML.R (kore c E.vars E.lhs) (kore c E.vars E.rhs)

/-- The law is over registry sorts and its sides are terms of the sort `s`. -/
def typed (c : Semantics) (E : Law) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  srt? c E.vars E.lhs == some E.s && srt? c E.vars E.rhs == some E.s

/-- The two sides have the same value, or both none, at every substitution of values of the
variables' sorts. -/
def Holds (c : Semantics) (E : Law) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    val c σ E.lhs = val c σ E.rhs

end Law

/-- **A collection law that holds of the values is entailed at values.** For a semantics meeting
`coreOK` and a law `E` whose sides have equal values (`Law.Holds`): the translation of any axiom
declaration whose pattern is `E`'s, over the one sort variable `R` and with each variable of `E`
free in it, holds in every model of `Γ c` at every valuation that sends the axiom's free element
variables to values. -/
theorem Law.entailed {c : Semantics} (h : c.coreOK = true) (E : Law) (ht : E.typed c = true)
    (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.pattern c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [Law.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨σ, hσ, hag⟩ := fq_subst h hI E.vars hvR ad.ax hfv e hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hag ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srt? c E.vars u = some s) =>
    den_val (tbl := t) (e := e) h hI hσ hag u hu
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [hp]
  unfold Law.pattern
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
  constructor
  · exact fun h' => (KoreAML.interp_inhOf_of hRv).mpr h'.1
  · intro ha
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b _ => ?_⟩
    rw [(hDV E.lhs _ htl).1 b, hE σ hσ, ← (hDV E.rhs _ htr).1 b]

namespace Law

/-- `pattern` with the registry's names. -/
def patR (E : Law) : Kore.Pattern :=
  .equals (regSrtK E.s) KoreAML.R (koreR E.vars E.lhs) (koreR E.vars E.rhs)

/-- The law is over the registry's symbols and sorts, and each of its variables is free in its
pattern. -/
def regular (E : Law) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) && reg E.lhs && reg E.rhs &&
  E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

theorem pattern_reg (c : Semantics) {E : Law} (hr : E.regular = true) : E.pattern c = E.patR := by
  simp only [regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨⟨hs, hv⟩, hl⟩, hrr⟩, -⟩ := hr
  unfold pattern patR
  rw [kore_reg c hv _ hl, kore_reg c hv _ hrr, srtOf_reg c hs]

end Law

/-- `Law.entailed` for a law over the registry's names: the axiom's pattern is compared with a
pattern that does not depend on the semantics. -/
theorem Law.entailed_reg {c : Semantics} (h : c.coreOK = true) (E : Law) (hr : E.regular = true)
    (ht : E.typed c = true) (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  refine Law.entailed h E ht hE ad (hp.trans (Law.pattern_reg c hr).symm) hsv (fun i hi => ?_)
  have hr' := hr
  simp only [Law.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr'
  obtain ⟨⟨⟨⟨-, hv⟩, -⟩, -⟩, hf⟩ := hr'
  have hmem : E.vars.getD i ("", 0) ∈ E.vars := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have := hf _ hmem
  rw [hp]
  unfold vkey
  rw [srtOf_reg c (hv _ hmem)]
  exact List.mem_of_elem_eq_true this

/-! ## Associativity and the two units -/

/-- `f(f(K1, K2), K3) = f(K1, f(K2, K3))` at the sort `s`. -/
def lawAssoc (f : Sym) (s : Srt) : Law :=
  ⟨[("K1", s), ("K2", s), ("K3", s)], s, .app f [.app f [.var 0, .var 1], .var 2],
    .app f [.var 0, .app f [.var 1, .var 2]]⟩

/-- `f(K, u()) = K` at the sort `s`. -/
def lawUnitR (f u : Sym) (s : Srt) : Law := ⟨[("K", s)], s, .app f [.var 0, .app u []], .var 0⟩

/-- `f(u(), K) = K` at the sort `s`. -/
def lawUnitL (f u : Sym) (s : Srt) : Law := ⟨[("K", s)], s, .app f [.app u [], .var 0], .var 0⟩

/-- Evaluates a law's sides at a substitution, given the values of its variables as rewriting
facts. -/
syntax "fq_law" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| fq_law [$ls,*]) => `(tactic| simp only [lawAssoc, lawUnitR, lawUnitL, val, valList, allSome,
      Option.bind_some, Option.map_some, $ls,*])

/-- A partial operation is associative where each grouping that has a value gives the other
that value. -/
theorem fq_assoc {α : Type} (p : α → α → Option α) (a b d : α)
    (h1 : ∀ u m, p a b = some u → p u d = some m → ∃ w, p b d = some w ∧ p a w = some m)
    (h2 : ∀ w m, p b d = some w → p a w = some m → ∃ u, p a b = some u ∧ p u d = some m) :
    ((p a b).bind fun u => p u d) = (p b d).bind fun w => p a w := by
  cases hL : (p a b).bind fun u => p u d with
  | some m =>
    obtain ⟨u, hu, hm⟩ := Option.bind_eq_some_iff.mp hL
    obtain ⟨w, hw, hm'⟩ := h1 u m hu hm
    rw [hw, Option.bind_some, hm']
  | none =>
    cases hR : (p b d).bind fun w => p a w with
    | none => rfl
    | some m =>
      obtain ⟨w, hw, hm⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨u, hu, hm'⟩ := h2 w m hw hm
      rw [hu, Option.bind_some, hm'] at hL
      cases hL

/-! ### `_List_` -/

theorem listAssoc_holds {c : Semantics} (hs : c.shapesOK = true) : (lawAssoc listConcat Srt.list).Holds c := by
  intro σ hσ
  obtain ⟨a, ha⟩ := fq_list_at hs hσ 0 (n := "K1") rfl
  obtain ⟨b, hb⟩ := fq_list_at hs hσ 1 (n := "K2") rfl
  obtain ⟨d, hd⟩ := fq_list_at hs hσ 2 (n := "K3") rfl
  fq_law [ha, hb, hd, fhv_listConcat, List.append_assoc]

theorem listUnitR_holds {c : Semantics} (hs : c.shapesOK = true) : (lawUnitR listConcat listUnit Srt.list).Holds c := by
  intro σ hσ
  obtain ⟨a, ha⟩ := fq_list_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_listUnit, fhv_listConcat, List.append_nil]

theorem listUnitL_holds {c : Semantics} (hs : c.shapesOK = true) : (lawUnitL listConcat listUnit Srt.list).Holds c := by
  intro σ hσ
  obtain ⟨a, ha⟩ := fq_list_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_listUnit, fhv_listConcat, List.nil_append]

/-! ### `_Set_` -/

/-- `_Set_` is associative on sets with their elements in order: each grouping has a value
exactly where no two of the three sets share a member. -/
theorem fq_concatS_assoc {a b d : List GroundTerm} (hd : Set.Canon d) :
    ((concatS a b).bind fun u => concatS u d) = (concatS b d).bind fun w => concatS a w := by
  refine fq_assoc concatS a b d (fun u m hu hm => ?_) (fun w m hw hm => ?_)
  · obtain ⟨hab, rfl⟩ := Model.concatS_iff.mp hu
    obtain ⟨hud, rfl⟩ := Model.concatS_iff.mp hm
    have hbd : ∀ x ∈ b, x ∉ d := fun x hx => hud x ((Set.mem_union x a b).mpr (Or.inr hx))
    refine ⟨unionS b d, Model.concatS_iff.mpr ⟨hbd, rfl⟩, Model.concatS_iff.mpr ⟨fun x hx hx' => ?_, ?_⟩⟩
    · rcases (Set.mem_union x b d).mp hx' with h' | h'
      · exact hab x hx h'
      · exact hud x ((Set.mem_union x a b).mpr (Or.inl hx)) h'
    · exact Set.ext (Set.union_canon (Set.union_canon hd)) (Set.union_canon hd) fun x => by
        simp only [Set.mem_union, or_assoc]
  · obtain ⟨hbd, rfl⟩ := Model.concatS_iff.mp hw
    obtain ⟨haw, rfl⟩ := Model.concatS_iff.mp hm
    have hab : ∀ x ∈ a, x ∉ b := fun x hx hx' => haw x hx ((Set.mem_union x b d).mpr (Or.inl hx'))
    refine ⟨unionS a b, Model.concatS_iff.mpr ⟨hab, rfl⟩, Model.concatS_iff.mpr ⟨fun x hx hx' => ?_, ?_⟩⟩
    · rcases (Set.mem_union x a b).mp hx with h' | h'
      · exact haw x h' ((Set.mem_union x b d).mpr (Or.inr hx'))
      · exact hbd x h' hx'
    · exact Set.ext (Set.union_canon hd) (Set.union_canon (Set.union_canon hd)) fun x => by
        simp only [Set.mem_union, or_assoc]

/-- The empty set is a right unit of `_Set_` on a set with its elements in order. -/
theorem fq_concatS_nil {a : List GroundTerm} (ha : Set.Canon a) : concatS a [] = some a :=
  Model.concatS_of (by rfl) ha (fun _ _ h => nomatch h) (fun x => by simp)

theorem setAssoc_holds {c : Semantics} (hs : c.shapesOK = true) : (lawAssoc setConcat Srt.set).Holds c := by
  intro σ hσ
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "K1") rfl
  obtain ⟨b, hb, -⟩ := fq_set_at hs hσ 1 (n := "K2") rfl
  obtain ⟨d, hd, hcd⟩ := fq_set_at hs hσ 2 (n := "K3") rfl
  fq_law [ha, hb, hd, fhv_setConcat]
  have key := fq_concatS_assoc (a := a) (b := b) hcd
  cases h1 : concatS a b <;> cases h2 : concatS b d <;> rw [h1, h2] at key <;>
    simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, fhv_setConcat] at key ⊢
  · exact (congrArg (Option.map (GroundTerm.set Srt.set)) key).trans (by rfl)
  · exact (congrArg (Option.map (GroundTerm.set Srt.set)) key)
  · exact (congrArg (Option.map (GroundTerm.set Srt.set)) key)

theorem setUnitR_holds {c : Semantics} (hs : c.shapesOK = true) : (lawUnitR setConcat setUnit Srt.set).Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_setUnit, fhv_setConcat, fq_concatS_nil hca]

theorem setUnitL_holds {c : Semantics} (hs : c.shapesOK = true) : (lawUnitL setConcat setUnit Srt.set).Holds c := by
  intro σ hσ
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_setUnit, fhv_setConcat]
  rfl

/-! ### `_Map_` -/

/-- One half of the associativity of `_Map_`: where the grouping to the left has a value, the
grouping to the right has it. -/
theorem fq_union_assoc_l {a b d u m : Entries} (ha : Map.Canon a) (hb : Map.Canon b) (hd : Map.Canon d)
    (hu : union a b = some u) (hm : union u d = some m) : ∃ w, union b d = some w ∧ union a w = some m := by
  obtain ⟨hcu, hfu⟩ := Map.union_find ha hb hu
  obtain ⟨hcm, hfm⟩ := Map.union_find hcu hd hm
  have hab := (Map.union_defined ha hb).mp ⟨u, hu⟩
  have hud := (Map.union_defined hcu hd).mp ⟨m, hm⟩
  obtain ⟨w, hw⟩ := (Map.union_defined hb hd).mpr fun k => by
    rcases hud k with h' | h'
    · rw [hfu] at h'
      cases hbk : Map.find b k with
      | none => exact Or.inl rfl
      | some v => rw [hbk] at h'; cases hak : Map.find a k <;> rw [hak] at h' <;> cases h'
    · exact Or.inr h'
  obtain ⟨hcw, hfw⟩ := Map.union_find hb hd hw
  obtain ⟨m', hm'⟩ := (Map.union_defined ha hcw).mpr fun k => by
    cases hak : Map.find a k with
    | none => exact Or.inl rfl
    | some v =>
      refine Or.inr ?_
      rw [hfw]
      have hbk : Map.find b k = none := by rcases hab k with h' | h'; · rw [hak] at h'; cases h'
                                           · exact h'
      have hdk : Map.find d k = none := by
        rcases hud k with h' | h'
        · rw [hfu, hak] at h'; cases h'
        · exact h'
      rw [hbk, hdk]; rfl
  obtain ⟨hcm', hfm'⟩ := Map.union_find ha hcw hm'
  refine ⟨w, hw, ?_⟩
  rw [hm']
  exact congrArg some (Map.ext hcm' hcm fun k => by rw [hfm', hfw, hfm, hfu, Option.or_assoc])

/-- The other half: where the grouping to the right has a value, the grouping to the left has
it. -/
theorem fq_union_assoc_r {a b d w m : Entries} (ha : Map.Canon a) (hb : Map.Canon b) (hd : Map.Canon d)
    (hw : union b d = some w) (hm : union a w = some m) : ∃ u, union a b = some u ∧ union u d = some m := by
  obtain ⟨hcw, hfw⟩ := Map.union_find hb hd hw
  obtain ⟨hcm, hfm⟩ := Map.union_find ha hcw hm
  have hbd := (Map.union_defined hb hd).mp ⟨w, hw⟩
  have haw := (Map.union_defined ha hcw).mp ⟨m, hm⟩
  obtain ⟨u, hu⟩ := (Map.union_defined ha hb).mpr fun k => by
    rcases haw k with h' | h'
    · exact Or.inl h'
    · rw [hfw] at h'
      refine Or.inr ?_
      cases hbk : Map.find b k with
      | none => rfl
      | some v => rw [hbk] at h'; cases h'
  obtain ⟨hcu, hfu⟩ := Map.union_find ha hb hu
  obtain ⟨m', hm'⟩ := (Map.union_defined hcu hd).mpr fun k => by
    cases hdk : Map.find d k with
    | none => exact Or.inr rfl
    | some v =>
      refine Or.inl ?_
      rw [hfu]
      have hbk : Map.find b k = none := by rcases hbd k with h' | h'; · exact h'
                                           · rw [hdk] at h'; cases h'
      have hak : Map.find a k = none := by
        rcases haw k with h' | h'
        · exact h'
        · rw [hfw, hbk, hdk] at h'; cases h'
      rw [hak, hbk]; rfl
  obtain ⟨hcm', hfm'⟩ := Map.union_find hcu hd hm'
  refine ⟨u, hu, ?_⟩
  rw [hm']
  exact congrArg some (Map.ext hcm' hcm fun k => by rw [hfm', hfu, hfm, hfw, Option.or_assoc])

/-- The empty map is a right unit of `_Map_` on a map with its keys in order. -/
theorem fq_union_nil {a : Entries} (ha : Map.Canon a) : union a [] = some a := by
  obtain ⟨m, hm⟩ := (Map.union_defined ha (by rfl : Map.Canon [])).mpr fun k => Or.inr rfl
  obtain ⟨hcm, hfm⟩ := Map.union_find ha (by rfl : Map.Canon []) hm
  rw [hm]
  exact congrArg some (Map.ext hcm ha fun k => by rw [hfm, Map.find_nil, Option.or_none])

theorem mapAssoc_holds {c : Semantics} (hs : c.shapesOK = true) : (lawAssoc mapConcat Srt.map).Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_map_at hs hσ 0 (n := "K1") rfl
  obtain ⟨b, hb, hcb⟩ := fq_map_at hs hσ 1 (n := "K2") rfl
  obtain ⟨d, hd, hcd⟩ := fq_map_at hs hσ 2 (n := "K3") rfl
  fq_law [ha, hb, hd, fhv_mapConcat]
  have key := fq_assoc union a b d (fun u m hu hm => fq_union_assoc_l hca hcb hcd hu hm)
    (fun w m hw hm => fq_union_assoc_r hca hcb hcd hw hm)
  cases h1 : union a b <;> cases h2 : union b d <;> rw [h1, h2] at key <;>
    simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, fhv_mapConcat] at key ⊢
  · exact (congrArg (Option.map (GroundTerm.map Srt.map)) key).trans (by rfl)
  · exact (congrArg (Option.map (GroundTerm.map Srt.map)) key)
  · exact (congrArg (Option.map (GroundTerm.map Srt.map)) key)

theorem mapUnitR_holds {c : Semantics} (hs : c.shapesOK = true) : (lawUnitR mapConcat mapUnit Srt.map).Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_map_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_mapUnit, fhv_mapConcat, fq_union_nil hca]

theorem mapUnitL_holds {c : Semantics} (hs : c.shapesOK = true) : (lawUnitL mapConcat mapUnit Srt.map).Holds c := by
  intro σ hσ
  obtain ⟨a, ha, -⟩ := fq_map_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_mapUnit, fhv_mapConcat]
  rfl

/-! ### The nine laws, entailed at values -/

section
variable {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
  (hsv : ad.ax.sortVars = [KoreAML.Rv])
include h hs hsv

theorem listAssoc_ev (hp : ad.ax.pattern = (lawAssoc listConcat Srt.list).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (listAssoc_holds hs) ad hp hsv
theorem listUnitR_ev (hp : ad.ax.pattern = (lawUnitR listConcat listUnit Srt.list).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (listUnitR_holds hs) ad hp hsv
theorem listUnitL_ev (hp : ad.ax.pattern = (lawUnitL listConcat listUnit Srt.list).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (listUnitL_holds hs) ad hp hsv
theorem setAssoc_ev (hp : ad.ax.pattern = (lawAssoc setConcat Srt.set).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (setAssoc_holds hs) ad hp hsv
theorem setUnitR_ev (hp : ad.ax.pattern = (lawUnitR setConcat setUnit Srt.set).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (setUnitR_holds hs) ad hp hsv
theorem setUnitL_ev (hp : ad.ax.pattern = (lawUnitL setConcat setUnit Srt.set).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (setUnitL_holds hs) ad hp hsv
theorem mapAssoc_ev (hp : ad.ax.pattern = (lawAssoc mapConcat Srt.map).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (mapAssoc_holds hs) ad hp hsv
theorem mapUnitR_ev (hp : ad.ax.pattern = (lawUnitR mapConcat mapUnit Srt.map).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (mapUnitR_holds hs) ad hp hsv
theorem mapUnitL_ev (hp : ad.ax.pattern = (lawUnitL mapConcat mapUnit Srt.map).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (mapUnitL_holds hs) ad hp hsv

end

end LibEv

end KCore
