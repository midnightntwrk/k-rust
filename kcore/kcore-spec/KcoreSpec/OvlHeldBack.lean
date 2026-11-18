/-
  KCore. An `ovlHeld` symbol at a value: in a model of `Γc`, an application of an overloading
  symbol each function in whose overload closure takes arguments of confined sorts, that is a
  value's element, has values' elements as arguments.

  - `ovlCovered_elem`, `ovlCovered_values`: arguments that lift elements of confined sorts are
    values' elements. It is the case of arguments a function overload covers: the covering
    signature's argument sorts are confined, so the lifted elements are values'
    (`confinedAt_value`), and the injection of a value's element is a value's. It is stated over
    two lists of sorts, reads no item of the covering symbol and no item of the covered one, and
    asks for some covering list, not a unique one.
  - `OvlConfOver`: every function among a symbol's overloads takes arguments of confined sorts;
    an `ovlHeld` symbol has it (`ovlConfOver_of_held`) and so does each symbol it overloads.
  - `ovlValsOrInSOB`: sorted arguments of such a symbol are values' elements, or the symbol builds
    elements of its result sort from them. `Γ` states the symbol's functionality at uncovered
    arguments only; at arguments a constructor or an overloading symbol covers, the overload
    equation and the covering symbol's own case give it, and arguments a function covers are
    values' elements already.
  - `ovlBackConfOB`: the image at a value for such a symbol, by induction on the rank: arguments a
    function overload covers by `ovlCovered_values`; arguments a constructor or an overloading
    symbol covers by the overload equation and that symbol's own case; uncovered arguments by the
    injectivity and the apartness `Γ` states at uncovered arguments.
  - `ovlHeld_back`: the statement for an `ovlHeld` symbol. Where no function is among the symbol's
    overloads the proof is `ovl_back`; where one is, `hrc` (the definition reads a confined sort
    where the symbol's closure holds a function) gives what `ovlCovered_values` takes and the
    proof is `ovlBackConfOB`.
  - `heldBackAll_collOvl`: the `collHeld` and the `ovlHeld` symbols have `HeldBack` in every model
    of `Γc`.
-/
import KcoreSpec.HeldBackAll

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful

section OvlHeldBack
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An argument that lifts an element of a confined sort is a value's element.** A, the sort the
argument is lifted from, is confined, and B, the argument's sort, is A or a sort A is a subsort of;
where they differ the argument is the injection of an element of A. -/
theorem ovlCovered_elem (h : c.coreOK = true) (hr : c.readsConfined = true) (hI : I ⊧ᴵP Γc c)
    {A B : Srt} (hsub : A ≠ B → (A, B) ∈ c.subsorts) (hA : c.confined A = true) {b : M}
    (hb : InS I (c.sortName B) b)
    (hcov : A ≠ B → ∃ y, InS I (c.sortName A) y ∧ GS I (c.sortName B) (.inj (c.sortName A)) [y] b) :
    ∃ w, c.sortOf w = some B ∧ b = elemOf c I w := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  by_cases hAB : A = B
  · subst hAB
    obtain ⟨v, hv, rfl⟩ := confinedAt_value h hr hI _ A hA b hb
    exact ⟨v, hv, rfl⟩
  · obtain ⟨y, hy, hyb⟩ := hcov hAB
    obtain ⟨v, hv, rfl⟩ := confinedAt_value h hr hI _ A hA y hy
    have hs := sortOf_injNormal hsc.trans (hsub hAB) hv
    exact ⟨injNormal A B v, hs, ((elemOf_spec hIΓ hs KoreAML.val0).1 b).mp
      ((den_injNormal_gs hIΓ hsc.trans (hsub hAB) hv KoreAML.val0 b).mpr hyb)⟩

/-- **Arguments a signature of confined argument sorts covers are values' elements.** `As` are the
covering signature's argument sorts, `Bs` the covered symbol's; `hcov` is the covering in the
model: each argument whose two sorts differ is the injection of an element of the covering sort. -/
theorem ovlCovered_values (h : c.coreOK = true) (hr : c.readsConfined = true) (hI : I ⊧ᴵP Γc c) :
    ∀ (As Bs : List Srt) (bs : List M), As.length = Bs.length →
      bs.length = (Bs.map c.sortName).length →
      (∀ (i : Nat) (A B : Srt), As[i]? = some A → Bs[i]? = some B → A ≠ B → (A, B) ∈ c.subsorts) →
      (∀ A ∈ As, c.confined A = true) →
      (∀ (i : Nat) x s, bs[i]? = some x → (Bs.map c.sortName)[i]? = some s → InS I s x) →
      (∀ (i : Nat) (A B : Srt) (b : M), As[i]? = some A → Bs[i]? = some B → bs[i]? = some b → A ≠ B →
        ∃ y, InS I (c.sortName A) y ∧ GS I (c.sortName B) (.inj (c.sortName A)) [y] b) →
      ∃ ws, c.sortsOf ws = some Bs ∧ bs = ws.map (elemOf c I) := by
  intro As
  induction As with
  | nil =>
    intro Bs bs hl hbl _ _ _ _
    cases Bs with
    | nil =>
      cases bs with
      | nil => exact ⟨[], sortsOf_nil, rfl⟩
      | cons _ _ => simp at hbl
    | cons _ _ => simp at hl
  | cons A As ih =>
    intro Bs bs hl hbl hsub hconf hbs hcov
    cases Bs with
    | nil => simp at hl
    | cons B Bs =>
      cases bs with
      | nil => simp at hbl
      | cons b bs =>
        obtain ⟨w, hw, rfl⟩ := ovlCovered_elem h hr hI (fun hAB => hsub 0 A B rfl rfl hAB)
          (hconf A (List.mem_cons_self ..)) (hbs 0 b _ rfl rfl) (fun hAB => hcov 0 A B b rfl rfl rfl hAB)
        obtain ⟨ws, hws, rfl⟩ := ih Bs bs (by simpa using hl) (by simpa using hbl)
          (fun i A' B' hA' hB' => hsub (i + 1) A' B' (by simpa using hA') (by simpa using hB'))
          (fun A' hA' => hconf A' (List.mem_cons_of_mem _ hA'))
          (fun i x s hx hs => hbs (i + 1) x s (by simpa using hx) (by simpa using hs))
          (fun i A' B' b' hA' hB' hb' => hcov (i + 1) A' B' b' (by simpa using hA') (by simpa using hB')
            (by simpa using hb'))
        exact ⟨w :: ws, OvlLaws.sortsOf_cons_iff.mpr ⟨hw, hws⟩, rfl⟩

end OvlHeldBack

/-! ## An overloading symbol whose function overloads take confined arguments -/

section OvlBackConf
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- Every function among the overloads of `f` takes arguments of confined sorts (true of a symbol
that is no overloading symbol, and of one with no function among its overloads). -/
def OvlConfOver (c : Semantics) (f : Sym) : Prop :=
  ∀ o, c.lookupOvl f = some o → ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true → ∀ A ∈ kg.args, c.confined A = true

/-- A symbol that `f` overloads has it where `f` has: an overloading symbol lists the functions
that the overloading symbols it overloads list. -/
theorem OvlConfOver.over (F : OvlLaws.OvlFnFacts c) {f : Sym} (h : OvlConfOver c f) {o : OvlSig}
    (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) : OvlConfOver c kg.name :=
  fun o' ho' kg' hkg' hb =>
    h o ho kg' (F.closed o (OvlLaws.mem_of_lookupOvl ho) kg hkg o' ho' kg' hkg' hb) hb

theorem ovlReach_selfOB (n : Nat) (g : Sym) : g ∈ c.ovlReach n g := by
  cases n <;> simp [Semantics.ovlReach]

/-- A symbol that `f` overloads is in `f`'s overload closure. -/
theorem ovlClosure_overOB {f g : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) (hg : g ∈ o.over) :
    g ∈ c.ovlClosure f := by
  unfold Semantics.ovlClosure
  simp only [Semantics.ovlReach, ho]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, ovlReach_selfOB _ g⟩)

/-- A function among the overloads of `f` is one of `fnOverloads f`. -/
theorem fnOverloads_of_byFnOB {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig}
    (hkg : kg ∈ c.ovlOver o) (hb : c.ovlByFn kg = true) :
    ∃ fn ∈ c.fnOverloads f, kg = ⟨fn.label, fn.args, fn.result⟩ := by
  obtain ⟨fn, hfn, -, hsig⟩ := OvlLaws.byFn_fn hkg hb
  refine ⟨fn, ?_, hsig⟩
  unfold Semantics.fnOverloads
  refine List.mem_flatMap.mpr ⟨kg.name, ovlClosure_overOB ho (OvlLaws.mem_ovlOver hkg),
    List.mem_filter.mpr ⟨hfn, ?_⟩⟩
  rw [hsig]; simp

/-- The function overloads of an `ovlHeld` symbol take arguments of confined sorts. -/
theorem ovlConfOver_of_held {f : Sym} (hh : c.ovlHeld f = true) : OvlConfOver c f := by
  intro o ho kg hkg hb A hA
  obtain ⟨fn, hfn, hsig⟩ := fnOverloads_of_byFnOB ho hkg hb
  unfold Semantics.ovlHeld at hh
  have hall := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hh).2 fn hfn
  rw [hsig] at hA
  exact List.all_eq_true.mp hall A hA

/-- The overload `kg` of `o` covers the elements `bs` in the model: each element at a position
whose two sorts differ is what the injection builds from an element of `kg`'s sort. -/
def OvlCovE (c : Semantics) (I : Interpretation KoreAML.Sym M) (kg : CtorSig) (o : OvlSig) (bs : List M) : Prop :=
  ∀ (i : Nat) (A B : Srt) (b : M), kg.args[i]? = some A → o.sig.args[i]? = some B → bs[i]? = some b → A ≠ B →
    ∃ y, InS I (c.sortName A) y ∧ GS I (c.sortName B) (.inj (c.sortName A)) [y] b

/-- `zs` are elements of `kg`'s argument sorts that the elements `bs` of `o`'s lift: the element
itself where the two sorts are the same, the injection's image otherwise. -/
def OvlLiftsE (c : Semantics) (I : Interpretation KoreAML.Sym M) (kg : CtorSig) (o : OvlSig) (bs zs : List M) : Prop :=
  ∀ (i : Nat) (z : M), zs[i]? = some z → ∀ A B b, kg.args[i]? = some A → o.sig.args[i]? = some B →
    bs[i]? = some b → InS I (c.sortName A) z ∧ (A = B → z = b) ∧
      (A ≠ B → GS I (c.sortName B) (.inj (c.sortName A)) [z] b)

/-- Elements an overload covers in the model lift elements of the overload's argument sorts. -/
theorem ovlZsOB {o : OvlSig} {kg : CtorSig} {bs : List M} (hlen : kg.args.length = o.sig.args.length)
    (hbl' : bs.length = o.sig.args.length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (o.sig.args.map c.sortName)[i]? = some s → InS I s x)
    (hcv : OvlCovE c I kg o bs) : ∃ zs : List M, zs.length = bs.length ∧ OvlLiftsE c I kg o bs zs := by
  refine choose_list (n := bs.length) (P := fun i z => ∀ A B b, kg.args[i]? = some A →
      o.sig.args[i]? = some B → bs[i]? = some b → InS I (c.sortName A) z ∧ (A = B → z = b) ∧
        (A ≠ B → GS I (c.sortName B) (.inj (c.sortName A)) [z] b)) (fun i hi => ?_)
  obtain ⟨A, hA⟩ : ∃ A, kg.args[i]? = some A := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨B, hB⟩ : ∃ B, o.sig.args[i]? = some B := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨_, List.getElem?_eq_getElem hi⟩
  have hbB : InS I (c.sortName B) b := hbs i b _ hb (by simp [hB])
  by_cases hAB : A = B
  · subst hAB
    exact ⟨b, fun A' B' b' hA' hB' hb' => by
      rw [hA] at hA'; rw [hB] at hB'; rw [hb] at hb'; cases hA'; cases hB'; cases hb'
      exact ⟨hbB, fun _ => rfl, fun h => absurd rfl h⟩⟩
  · obtain ⟨z, hz, hzb⟩ := hcv i A B b hA hB hb hAB
    exact ⟨z, fun A' B' b' hA' hB' hb' => by
      rw [hA] at hA'; rw [hB] at hB'; rw [hb] at hb'; cases hA'; cases hB'; cases hb'
      exact ⟨hz, fun h => absurd h hAB, fun _ => hzb⟩⟩

/-- The lifted elements are of the overload's argument sorts. -/
theorem ovlZsSortsOB {o : OvlSig} {kg : CtorSig} {bs zs : List M} (hlen : kg.args.length = o.sig.args.length)
    (hbl' : bs.length = o.sig.args.length) (hzl : zs.length = bs.length) (hzs : OvlLiftsE c I kg o bs zs) :
    ∀ (i : Nat) x s, zs[i]? = some x → (kg.args.map c.sortName)[i]? = some s → InS I s x := by
  intro i x s hx hs
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  have hi : i < bs.length := by rw [← hzl]; exact (List.getElem?_eq_some_iff.mp hx).1
  exact (hzs i x hx A _ _ hA (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)).1

variable (hI : I ⊧ᴵP Γ c) [hO : OvlOK c] (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI hg htr

/-- Where an overload's sort and the symbol's differ at a position, the first is a subsort. -/
theorem ovlSubAtOB {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) :
    ∀ (i : Nat) (A B : Srt), kg.args[i]? = some A → o.sig.args[i]? = some B → A ≠ B → (A, B) ∈ c.subsorts := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  obtain ⟨-, hle, -, -⟩ := OvlLaws.over_ovlF H.fnFacts ho hkg
  intro i A B hA hB hAB
  obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp hA
  obtain ⟨h2, rfl⟩ := List.getElem?_eq_some_iff.mp hB
  exact OvlLaws.mem_of_le ((OvlLaws.zip2_all_iff.mp hle) i h1 h2) hAB

/-- **Elements that lift values' elements are values' elements**: the lifted values'. -/
theorem ovlLiftBackOB {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o)
    {bs : List M} (hbl' : bs.length = o.sig.args.length) {us : List GroundTerm}
    (hus : c.sortsOf us = some kg.args) (hzs : OvlLiftsE c I kg o bs (us.map (elemOf c I))) :
    ∃ ws, c.sortsOf ws = some o.sig.args ∧ bs = ws.map (elemOf c I) := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  obtain ⟨hlen, hle, -, -⟩ := OvlLaws.over_ovlF H.fnFacts ho hkg
  have hsubAt := ovlSubAtOB hI hg htr ho hkg
  refine ⟨liftAll kg.args o.sig.args us, OvlLaws.sortsOf_liftAll H hlen hus hle, ?_⟩
  have hul := sortsOf_length hus
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < bs.length
  · obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨A, hA⟩ : ∃ A, kg.args[i]? = some A := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨B, hB⟩ : ∃ B, o.sig.args[i]? = some B := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨u, hu⟩ : ∃ u, us[i]? = some u := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hz : (us.map (elemOf c I))[i]? = some (elemOf c I u) := by simp [hu]
    obtain ⟨-, heq, hne⟩ := hzs i _ hz A B b hA hB hb
    obtain ⟨u', hu', hsu⟩ := sortsOf_get hus hA
    rw [hu] at hu'; cases hu'
    have hli : (liftAll kg.args o.sig.args us)[i]? = some (lift A B u) := by
      have hz3 : ((kg.args.zip o.sig.args).zip us)[i]? = some ((A, B), u) :=
        List.getElem?_zip_eq_some.mpr ⟨List.getElem?_zip_eq_some.mpr ⟨hA, hB⟩, hu⟩
      rw [liftAll, List.getElem?_map, hz3]; rfl
    rw [hb, List.getElem?_map, hli]
    by_cases hAB : A = B
    · subst hAB; rw [OvlLaws.lift_self, ← heq rfl]; rfl
    · have hsub := hsubAt i A B hA hB hAB
      rw [OvlLaws.lift_ne hAB]
      have := (den_injNormal_gs hI htr hsub hsu KoreAML.val0 b).mpr (hne hAB)
      rw [(elemOf_spec hI (sortOf_injNormal htr hsub hsu) KoreAML.val0).1 b] at this
      rw [this]; rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [OvlLaws.length_liftAll]; omega)]

/-- **The overload equation at lifted elements**: the overloading symbol applied to `bs` builds what
the overload `kg` builds from the elements `zs` that `bs` lift, lifted to the symbol's result sort. -/
theorem ovlKeyOB {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o)
    {bs zs : List M} (hbl' : bs.length = o.sig.args.length) (hzl : zs.length = bs.length)
    (hzs : OvlLiftsE c I kg o bs zs) (m : M) :
    GS I (c.sortName o.sig.result) (.ctor (toK c o.sig)) bs m ↔
      (if (toK c kg).result == (toK c o.sig).result then GS I (c.sortName kg.result) (.ctor (toK c kg)) zs m
        else ∃ x, GS I (c.sortName kg.result) (.ctor (toK c kg)) zs x ∧
          GS I (toK c o.sig).result (.inj (toK c kg).result) [x] m) := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  have hom := OvlLaws.mem_of_lookupOvl ho
  obtain ⟨hlen, -, -, -⟩ := OvlLaws.over_ovlF H.fnFacts ho hkg
  have hsubAt := ovlSubAtOB hI hg htr ho hkg
  have hax := sat_cons hI (Or.inl ⟨_, ovlEqItem_mem hom hkg, rfl⟩)
  refine ovlEq_at (defOK hI) (N := c.sortName o.sig.result) (N' := c.sortName kg.result) hax
    (zs := zs) (ys := bs) (by simp [toK, hzl, hbl', hlen]) (by simp [toK, hlen]) (by simp [toK, hbl', hlen])
    (ovlZsSortsOB hlen hbl' hzl hzs) (fun i A B z b hA hB hz hb m' => ?_) m
  simp only [toK, List.getElem?_map, Option.map_eq_some_iff] at hA hB
  obtain ⟨Ai, hAi, rfl⟩ := hA
  obtain ⟨Bi, hBi, rfl⟩ := hB
  obtain ⟨hzA, heq, hne⟩ := hzs i z hz Ai Bi b hAi hBi hb
  by_cases hAB : Ai = Bi
  · subst hAB; simp only [beq_self_eq_true, ↓reduceIte, heq rfl]
  · have hn' : c.sortName Ai ≠ c.sortName Bi := fun he => hAB (hO.names o hom kg hkg Ai
      (List.mem_cons_of_mem _ (List.mem_of_getElem? hAi)) Bi (List.mem_cons_of_mem _ (List.mem_of_getElem? hBi)) he)
    simp only [beq_iff_eq, hn', ↓reduceIte]
    have hsub := hsubAt i Ai Bi hAi hBi hAB
    obtain ⟨y', -, hy'⟩ := gen_fun hI (genWf_sub hg hsub).1 (gensF_inj hsub) rfl (xs := [z]) rfl (single_sorts hzA)
    have : y' = b := ((hy' b).mp (hne hAB)).symm
    subst this
    exact hy' m'

/-- Elements no overload covers in the model are uncovered as the items at uncovered arguments
read it. -/
theorem ovlUncOB {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {bs : List M}
    (hcov : ¬ ∃ kg ∈ c.ovlOver o, OvlCovE c I kg o bs) :
    ∀ covs, ovlArgsOf c (.ctor o.sig) = some covs → UncE I covs (Gen.toK c (.ctor o.sig)).argSorts bs := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  obtain ⟨hom, hn, hio, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts ho
  intro covs hcovs
  rw [← hn] at ho hio
  simp only [ovlArgsOf, hio, ↓reduceIte, ho, Option.map_some, Option.some.injEq] at hcovs
  subst hcovs
  intro as has
  obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp has
  obtain ⟨i, A, B, b, hA, hB, hb, hAB, hnl⟩ : ∃ (i : Nat) (A B : Srt) (b : M), kg.args[i]? = some A ∧
      o.sig.args[i]? = some B ∧ bs[i]? = some b ∧ A ≠ B ∧
      ¬ ∃ y, InS I (c.sortName A) y ∧ GS I (c.sortName B) (.inj (c.sortName A)) [y] b :=
    Classical.byContradiction fun hc => hcov ⟨kg, hkg, fun i A B b hA hB hb hAB =>
      Classical.byContradiction fun hl => hc ⟨i, A, B, b, hA, hB, hb, hAB, hl⟩⟩
  exact ⟨i, c.sortName A, c.sortName B, b, by simp [hA], by
    show (o.sig.args.map c.sortName)[i]? = _
    simp [hB], fun he => hAB (hO.names o hom kg hkg A (List.mem_cons_of_mem _ (List.mem_of_getElem? hA)) B
      (List.mem_cons_of_mem _ (List.mem_of_getElem? hB)) he), hb, hnl⟩

/-- **A constructor or an overloading symbol builds elements of its result sort** from arguments
that no overload covers in the model where it is function-overloaded: `Γ` states its functionality
there. -/
theorem ovlKnownInSOB {k : CtorSig} (hk : OvlLaws.KnownSig c k) {bs : List M}
    (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x)
    (hu : c.fnOvl (.ctor k) = true → UncE I ((ovlArgsOf c (.ctor k)).getD []) (Gen.toK c (.ctor k)).argSorts bs) :
    ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs m → InS I (c.sortName k.result) m := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  have hres : k.result ∈ consSorts c := by
    rcases OvlLaws.knownSig_mem hk with h | h
    · exact genWf_ctor hg h
    · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp h
      exact (OvlLaws.ovl_parts H.ok (OvlLaws.lookupOvl_of_mem H ho')).2.2.2.2
  have hgk : Gen.ctor k ∈ (c.gens k.result).filter (!c.isOpenGen ·) := by
    rcases OvlLaws.knownSig_mem hk with h | h
    · exact gensF_ctor hg h
    · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp h
      exact gensF_of_ovl hg ho'
  obtain ⟨y, hy, hyy⟩ := gen_funU hI hres hgk hbl hbs hu
  intro m hm
  rw [(hyy m).mp hm]; exact hy

variable (h : c.coreOK = true) (hr : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
include h hr hIc

/-- **Arguments a function overload covers in the model are values' elements**, where the function
takes arguments of confined sorts. No item of the function or of the symbol is read. -/
theorem ovlFnCovOB {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o)
    (hb : c.ovlByFn kg = true) (hc : OvlConfOver c f) {bs : List M}
    (hbl : bs.length = (o.sig.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (o.sig.args.map c.sortName)[i]? = some s → InS I s x)
    (hcv : OvlCovE c I kg o bs) : ∃ ws, c.sortsOf ws = some o.sig.args ∧ bs = ws.map (elemOf c I) := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  obtain ⟨hlen, -, -, -⟩ := OvlLaws.over_ovlF H.fnFacts ho hkg
  exact ovlCovered_values h hr hIc kg.args o.sig.args bs hlen hbl (ovlSubAtOB hI hg htr ho hkg)
    (hc o ho kg hkg hb) hbs hcv

/-- **Arguments of a constructor or an overloading symbol are values' elements, or the symbol
builds elements of its result sort from them**, where each function among the symbol's overloads
takes arguments of confined sorts. By induction on the rank: arguments a function overload covers
in the model are values' elements; at arguments no overload covers `Γ` states the symbol's
functionality; at arguments another overload covers, by its equation and the overloaded symbol's
case. -/
theorem ovlValsOrInSOB : ∀ (n : Nat) (k : CtorSig), OvlLaws.KnownSig c k → OvlLaws.ovlRank c k.name ≤ n →
    OvlConfOver c k.name → ∀ {bs : List M}, bs.length = (k.args.map c.sortName).length →
    (∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) →
    (∃ ws, c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I)) ∨
      ∀ m, GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs m → InS I (c.sortName k.result) m := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  have F := H.fnFacts
  intro n
  induction n with
  | zero =>
    intro k hk hrk _ bs hbl hbs
    have hn := OvlLaws.lookupOvl_none_of_rank (c := c) (f := k.name) (by omega)
    exact Or.inr (ovlKnownInSOB hI hg htr hk hbl hbs (fun hf => by simp [Semantics.fnOvl, hn] at hf))
  | succ n ih =>
    intro k hk hrk hc bs hbl hbs
    cases ho : c.lookupOvl k.name with
    | none => exact Or.inr (ovlKnownInSOB hI hg htr hk hbl hbs (fun hf => by simp [Semantics.fnOvl, ho] at hf))
    | some o =>
    obtain ⟨hom, hn, -, -, hks, -⟩ := OvlLaws.ovl_facts_ovlF F ho
    have hko : k = o.sig := OvlLaws.knownSig_inj hk hks hn.symm
    subst hko
    have hbl' : bs.length = o.sig.args.length := by simpa using hbl
    by_cases hcov : ∃ kg ∈ c.ovlOver o, OvlCovE c I kg o bs
    · obtain ⟨kg, hkg, hcv⟩ := hcov
      cases hb : c.ovlByFn kg with
      | true => exact Or.inl (ovlFnCovOB hI hg htr h hr hIc ho hkg hb hc hbl hbs hcv)
      | false =>
        have hkk := OvlLaws.known_of_not_byFn hkg hb
        obtain ⟨hlen, hle, hres, hrank⟩ := OvlLaws.over_ovlF F ho hkg
        obtain ⟨zs, hzl, hzs⟩ := ovlZsOB hlen hbl' hbs hcv
        have hzsorts := ovlZsSortsOB hlen hbl' hzl hzs
        have hzl' : zs.length = (kg.args.map c.sortName).length := by simp [hzl, hbl', hlen]
        rcases ih kg hkk (by omega) (hc.over F ho hkg) hzl' hzsorts with ⟨us, hus, rfl⟩ | hin
        · exact Or.inl (ovlLiftBackOB hI hg htr ho hkg hbl' hus hzs)
        · refine Or.inr fun m hm => ?_
          have hk := (ovlKeyOB hI hg htr ho hkg hbl' hzl hzs m).mp hm
          by_cases hRR : kg.result = o.sig.result
          · simp only [toK, hRR, beq_self_eq_true, ↓reduceIte] at hk
            rw [← hRR] at hk ⊢
            exact hin m hk
          · have hn' : c.sortName kg.result ≠ c.sortName o.sig.result := fun he =>
              hRR (hO.names o hom kg hkg _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) he)
            have hsub : (kg.result, o.sig.result) ∈ c.subsorts := OvlLaws.mem_of_le hres hRR
            simp only [toK, beq_iff_eq, hn', ↓reduceIte] at hk
            obtain ⟨x, hx, hxw⟩ := hk
            obtain ⟨y, hy, hyy⟩ := gen_fun hI (genWf_sub hg hsub).1 (gensF_inj hsub) rfl (xs := [x]) rfl
              (single_sorts (hin x hx))
            rw [(hyy m).mp hxw]; exact hy
    · exact Or.inr (ovlKnownInSOB hI hg htr hks hbl hbs
        (fun hf => uncE_getD (ovlUncOB hI hg htr ho hcov) hf))

set_option maxHeartbeats 1600000 in
/-- **An overloading symbol's image at a value, where its function overloads take confined
arguments.** If the element of a value lies in what a constructor or an overloading symbol builds
from elements of its argument sorts, those are values' elements. By induction on the rank:
arguments a function overload covers in the model are values' elements (`ovlFnCovOB`); where a
constructor or an overloading symbol among the overloads covers them, by its equation and the
overloaded symbol's image, the element it builds being of its result sort or its arguments values'
elements already (`ovlValsOrInSOB`); otherwise the value is a raw application of the symbol itself,
which `Γ` states injective at uncovered arguments and apart there from every other generator of
its sort. -/
theorem ovlBackConfOB : ∀ (n : Nat) (k : CtorSig), OvlLaws.KnownSig c k →
    OvlLaws.ovlRank c k.name ≤ n → OvlConfOver c k.name → ∀ {w : GroundTerm}, c.sortOf w = some k.result →
    ∀ {bs : List M}, bs.length = (k.args.map c.sortName).length →
    (∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) →
    GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs (elemOf c I w) →
    ∃ ws, c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I) := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  have F := H.fnFacts
  have ctorCase : ∀ k : CtorSig, OvlLaws.KnownSig c k → c.lookupOvl k.name = none → ∀ {w : GroundTerm},
      c.sortOf w = some k.result → ∀ {bs : List M}, bs.length = (k.args.map c.sortName).length →
      (∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) →
      GS I (c.sortName k.result) (Gen.toK c (.ctor k)) bs (elemOf c I w) →
      ∃ ws, c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I) := by
    intro k hk hn w hw bs hbl hbs hm
    obtain ⟨ws, -, hws, rfl⟩ := ctor_back hI hg htr (OvlLaws.known_ctor_parts H hk hn) hw hbl hbs hm
    exact ⟨ws, hws, rfl⟩
  intro n
  induction n with
  | zero =>
    intro k hk hrk _
    exact ctorCase k hk (OvlLaws.lookupOvl_none_of_rank (c := c) (f := k.name) (by omega))
  | succ n ih =>
    intro k hk hrk hc w hw bs hbl hbs hm
    cases ho : c.lookupOvl k.name with
    | none => exact ctorCase k hk ho hw hbl hbs hm
    | some o =>
    obtain ⟨-, hn, hio, hct, hks, -⟩ := OvlLaws.ovl_facts_ovlF F ho
    have hko : k = o.sig := OvlLaws.knownSig_inj hk hks hn.symm
    subst hko
    obtain ⟨hom, -, -, -, hN⟩ := OvlLaws.ovl_parts H.ok ho
    have hgo : Gen.ctor o.sig ∈ (c.gens o.sig.result).filter (!c.isOpenGen ·) := gensF_of_ovl hg hom
    have hbl' : bs.length = o.sig.args.length := by simpa using hbl
    by_cases hcov : ∃ kg ∈ c.ovlOver o, OvlCovE c I kg o bs
    · obtain ⟨kg, hkg, hcv⟩ := hcov
      cases hb : c.ovlByFn kg with
      | true => exact ovlFnCovOB hI hg htr h hr hIc ho hkg hb hc hbl hbs hcv
      | false =>
        have hkk := OvlLaws.known_of_not_byFn hkg hb
        have hck := hc.over F ho hkg
        obtain ⟨hlen, hle, hres, hrank⟩ := OvlLaws.over_ovlF F ho hkg
        have hrk' : OvlLaws.ovlRank c kg.name ≤ n := by omega
        obtain ⟨zs, hzl, hzs⟩ := ovlZsOB hlen hbl' hbs hcv
        have hzsorts := ovlZsSortsOB hlen hbl' hzl hzs
        have hzl' : zs.length = (kg.args.map c.sortName).length := by simp [hzl, hbl', hlen]
        have hk := (ovlKeyOB hI hg htr ho hkg hbl' hzl hzs (elemOf c I w)).mp hm
        by_cases hRR : kg.result = o.sig.result
        · simp only [toK, hRR, beq_self_eq_true, ↓reduceIte] at hk
          rw [← hRR] at hw hk
          obtain ⟨us, hus, rfl⟩ := ih kg hkk hrk' hck hw hzl' hzsorts hk
          exact ovlLiftBackOB hI hg htr ho hkg hbl' hus hzs
        · have hn' : c.sortName kg.result ≠ c.sortName o.sig.result := fun he =>
            hRR (hO.names o hom kg hkg _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) he)
          have hsub : (kg.result, o.sig.result) ∈ c.subsorts := OvlLaws.mem_of_le hres hRR
          simp only [toK, beq_iff_eq, hn', ↓reduceIte] at hk
          obtain ⟨x, hx, hxw⟩ := hk
          rcases ovlValsOrInSOB hI hg htr h hr hIc n kg hkk hrk' hck hzl' hzsorts with ⟨us, hus, rfl⟩ | hin
          · exact ovlLiftBackOB hI hg htr ho hkg hbl' hus hzs
          · obtain ⟨w', hw', -, rfl⟩ := inj_back hI hg htr w hsub hw (hin x hx) hxw
            obtain ⟨us, hus, rfl⟩ := ih kg hkk hrk' hck hw' hzl' hzsorts hx
            exact ovlLiftBackOB hI hg htr ho hkg hbl' hus hzs
    · -- no overload covers the elements: the value is a raw application of o itself
      have hU := ovlUncOB hI hg htr ho hcov
      obtain ⟨y, -, hy⟩ := gen_funU hI hN hgo hbl hbs (fun hf => uncE_getD hU hf)
      have hyw : y = elemOf c I w := ((hy _).mp hm).symm
      have hset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) bs m ↔ m = elemOf c I w :=
        fun m => by rw [hy, hyw]
      have hback : ∀ u : GroundTerm, ∀ (A B : Srt), (A, B) ∈ c.subsorts → c.sortOf u = some B → ∀ (y : M),
          InS I (c.sortName A) y → GS I (c.sortName B) (.inj (c.sortName A)) [y] (elemOf c I u) →
          c.lies A B u = true := fun u A B hAB hsu y hy hmy => by
        obtain ⟨w', hw', rfl, -⟩ := inj_back hI hg htr u hAB hsu hy hmy
        exact lies_injNormal hw'
      rcases consSort_shape hg hN hw with ⟨g, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
      · rcases sortOf_ctor_cases hg hw with ⟨kg, hkg, hws, hres⟩ | ⟨o', hlo', -, hws, hu, hres, -⟩ |
          ⟨kp, hko, -, -, -, -, hres, -⟩
        rotate_right
        · -- no overloading symbol has an open generator's sort (`genWf`'s flat conjunct)
          exact absurd hres (genWf_flat_ovl hg (c.lookupOpen_spec hko).1 (c.lookupOpen_spec hko).2.1
            (List.mem_map_of_mem (f := (·.sig)) hom))
        · exfalso
          obtain ⟨hkgm, -⟩ := lookupSig_spec hkg
          have hvset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor kg)) (ws.map (elemOf c I)) m ↔
              m = elemOf c I (.ctor g ws) := fun m => by
            rw [hres, ← den_ctor_gs hI hkg hws KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
          rw [lookupSig_eq] at hct
          exact gen_dist' hI hN hgo (by rw [hres]; exact gensF_ctor hg hkgm)
            (fun h => by injection h with h; subst h; exact absurd (List.find?_eq_none.mp hct _ hkgm) (by simp))
            (fun _ _ h _ => by cases h) hbl (elems_length hI hws) hbs (elems_sorts hI hws) hU
            (fun covs h => by simp [ovlArgsOf, isOvl_of_ctorSigs hkgm] at h) (fun m => by rw [hset, hvset])
        · by_cases hgf : g = o.sig.name
          · subst hgf
            rw [ho] at hlo'
            cases hlo'
            have hvset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (ws.map (elemOf c I)) m ↔
                m = elemOf c I (.ctor o.sig.name ws) := fun m => by
              rw [← den_sig_gs hI rfl hws KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
            refine ⟨ws, hws, ?_⟩
            by_cases hne : o.sig.args = []
            · have h1 : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hbl, hne]; rfl)
              rw [hne] at hws
              rw [h1, sortsOf_nil_eq hws]; rfl
            · exact gen_injU hI hN hgo hne hbl (elems_length hI hws) hbs (elems_sorts hI hws)
                (fun hf => uncE_getD hU hf)
                (fun hf => uncE_getD (uncE_of_value hI hg htr ho hws hu fun u _ => hback u) hf)
                (fun m => by rw [hset, hvset])
          · exfalso
            obtain ⟨hom', hn', -⟩ := OvlLaws.ovl_parts H.ok hlo'
            have hvset : ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o'.sig)) (ws.map (elemOf c I)) m ↔
                m = elemOf c I (.ctor g ws) := fun m => by
              rw [hres, ← den_sig_gs hI hn' hws KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
            exact gen_dist' hI hN hgo (by rw [hres]; exact gensF_of_ovl hg hom')
              (fun h => by injection h with h; exact hgf (by rw [← hn', ← h]))
              (fun _ _ h _ => by cases h) hbl (elems_length hI hws) hbs (elems_sorts hI hws) hU
              (uncE_of_value hI hg htr hlo' hws hu fun u _ => hback u) (fun m => by rw [hset, hvset])
      · exfalso
        obtain ⟨hab, -, hw0, hb⟩ := sortOf_inj.mp hw
        subst hb
        have hvset : ∀ m, GS I (c.sortName o.sig.result) (.inj (c.sortName a)) [elemOf c I w0] m ↔
            m = elemOf c I (.inj a o.sig.result w0) := fun m => by
          rw [← den_inj_gs hI hw0 KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
        exact gen_dist' hI hN hgo (gensF_inj hab) (fun h => by cases h) (fun _ _ h _ => by cases h) hbl rfl hbs
          (single_sorts ((inS_iff _).mp (elemOf_spec hI hw0 KoreAML.val0).2)) hU
          (fun covs h => by simp [ovlArgsOf] at h) (fun m => by rw [hset]; exact (hvset m).symm)

end OvlBackConf

section OvlHeldBack
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An `ovlHeld` symbol at a value**: in a model of `Γc`, an application of an `ovlHeld` symbol
that is a value's element has values' elements as arguments. `hrc`: the definition reads a
confined sort where the symbol's overload closure holds a function. -/
theorem ovlHeld_back (h : c.coreOK = true) {f : Sym}
    (hrc : (c.fnOverloads f).isEmpty = false → c.readsConfined = true)
    (hI : I ⊧ᴵP Γc c) {o : OvlSig} (hlo : c.lookupOvl f = some o) (hh : c.ovlHeld f = true)
    {w : GroundTerm} (hw : c.sortOf w = some o.sig.result) {bs : List M}
    (hbl : bs.length = (o.sig.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (o.sig.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : SymE I (c.symName f) bs (elemOf c I w)) :
    ∃ ws, c.sortsOf ws = some o.sig.args ∧ bs = ws.map (elemOf c I) := by
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨-, hn, -, -, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
  have H := (inferInstance : OvlOK c).hyp hsc.trans
  obtain ⟨-, -, -, -, hks, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts hlo
  obtain ⟨a, ha, hm⟩ := hm
  have hgs : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) bs (elemOf c I w) :=
    ⟨a, by rw [← hn] at ha; exact ha, hm⟩
  by_cases hall : ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = false
  · -- no function among the overloads
    have hnf : OvlLaws.NoFnOver c o.sig.name := fun o' ho' kg hkg => by
      rw [hn, hlo] at ho'; cases ho'
      exact hall kg hkg
    obtain ⟨ws, hws, hb, -⟩ := ovl_back hIΓ hsc.trans hg _ o.sig hks (OvlLaws.ovlRank_le _) hnf hw hbl hbs hgs
    exact ⟨ws, hws, hb⟩
  · -- a function among the overloads: the definition reads a confined sort
    obtain ⟨kg, hkg, hb⟩ : ∃ kg ∈ c.ovlOver o, c.ovlByFn kg = true :=
      Classical.byContradiction fun hc => hall fun kg hkg => by
        cases hb : c.ovlByFn kg with
        | false => rfl
        | true => exact absurd ⟨kg, hkg, hb⟩ hc
    have hr : c.readsConfined = true := hrc (by
      obtain ⟨fn, hfn, -⟩ := fnOverloads_of_byFnOB hlo hkg hb
      cases hfo : c.fnOverloads f with
      | nil => rw [hfo] at hfn; cases hfn
      | cons _ _ => rfl)
    exact ovlBackConfOB hIΓ hg hsc.trans h hr hI _ o.sig hks (OvlLaws.ovlRank_le _)
      (by rw [hn]; exact ovlConfOver_of_held hh) hw hbl hbs hgs

end OvlHeldBack

/-- **The `collHeld` and the `ovlHeld` symbols have `HeldBack` in every model of `Γc`.** `hrc`: the
definition reads a confined sort where an overload closure holds a function. -/
theorem heldBackAll_collOvl {c : Semantics} (h : c.coreOK = true)
    (hrc : c.ovls.any (fun o => !(c.fnOverloads o.sig.name).isEmpty) = true → c.readsConfined = true) :
    HeldBackAll c (fun f => collHeld c f || c.ovlHeld f) := by
  intro M _ I hI f k hc hh hk
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  rcases Bool.or_eq_true_iff.mp hh with hh | hh
  · exact collHeld_back (fun φ hφ => hI φ (Or.inl hφ)) hg hsc.trans hph hcs hcso hc hh hk
  · have ho : c.isOvl f = true := by
      unfold Semantics.ovlHeld at hh; exact (Bool.and_eq_true_iff.mp hh).1
    obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc fns_headsOK hk ho
    obtain ⟨hom, hn, -, hit, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
    refine ⟨hit, fun {w} hw {bs} hbl hbs hm => ovlHeld_back h (fun hne => hrc ?_) hI hlo hh hw hbl hbs hm⟩
    exact List.any_eq_true.mpr ⟨o, hom, by rw [hn, hne]; rfl⟩

end KCore
