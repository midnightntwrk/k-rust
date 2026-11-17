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
  - `ovlHeld_back`: the statement for an `ovlHeld` symbol. `hrc` (the definition reads a confined
    sort where the symbol's closure holds a function) is what `ovlCovered_values` takes; where
    `overloadsOK` asks every overload to be a constructor or an overloading symbol, no closure
    holds a function and the proof is `ovl_back`.
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
  obtain ⟨-, -, -, hks, -⟩ := OvlLaws.ovl_facts H hlo
  obtain ⟨a, ha, hm⟩ := hm
  obtain ⟨ws, hws, hb, -⟩ := ovl_back hIΓ hsc.trans hg _ o.sig hks (OvlLaws.ovlRank_le _) hw hbl hbs
    ⟨a, by rw [← hn] at ha; exact ha, hm⟩
  exact ⟨ws, hws, hb⟩

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
