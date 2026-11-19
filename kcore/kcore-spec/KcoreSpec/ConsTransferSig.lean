/-
  The extension of a model of the theory without the detached names (`extModel`,
  ConsExtModel.lean) satisfies the premises of the signature that name nothing of `D`
  (`sat_own_sig`), and the premises of the collections that name nothing of `D` (`sat_own_colls`),
  for names `D` that are sort constants and symbols of the definition.

  Five of the signature's items are not of the class `OwnSorted` (ConsTransfer.lean) and are
  carried directly: definedness (`sat_definedness_sg`: `⌈_⌉` holds of everything in the
  extension); the sort constant of a sort outside `D` (`sat_sortConst_sg`: its name denotes the
  old element it denotes in the model, a sort of the extension); `ceilDefItem` and `ceilArityItem`
  (`sat_ceilDef_sg`, `sat_ceilArity_sg`), whose sort variables range over the sorts of the
  extension, the old sorts and the detached sort names (`isSort_ext_sg`): at two old sorts
  `⌈x⌉{σ,σ'}` is the model's, and where one is a detached sort name it is the inhabitants of `σ'`
  through the added elements `ceil1`, `ceil2` (`ceilE_sorts_sg`); `dvArityItem` (`sat_dvArity_sg`):
  a literal applied to a detached sort name gives values of that sort.

  The arity items and the arity of next are of the class at no name (`own_arity_sg`,
  `own_next_sg`); a pattern of the class at any names none of whose symbols is in `D` is of the
  class at `D` (`ownSorted_clean_sg`), so `transfer` carries them (`transfer0_sg`).

  The collections' axioms (`ΓColls`) are guarded premises of the class: their guards put each
  variable in a sort, and their bodies are built from definedness, equality and sorted
  quantifiers over the collection's symbols (`own_mapUnitSplit_sg` and the others), so
  `transfer` carries those that name nothing of `D` (`transferG_sg`, `sat_own_colls`).
-/
import KcoreSpec.ConsRegistrySat
import KcoreSpec.ConsTransferInst

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort CeilE)

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

theorem notD_sg {σ : KoreAML.Sym} (h : ¬ plainSym σ) : ¬ D σ := fun h' => h (hD σ h')

/-- The inhabitants, in the extension, of an old element: the old inhabitants. -/
theorem inh_old_sg {σ : M} {x : Ext M} :
    Inh (extModel c D I) (.inl σ) x ↔ ∃ m, x = .inl m ∧ Inh I σ m := by
  constructor
  · rintro ⟨i, hi, happ⟩
    cases i with
    | inl i0 =>
      cases x with
      | inl m => exact ⟨m, rfl, i0, (sym_old (notD_sg hD (σ := .inh) (fun h => h)) i0).mp hi, happ⟩
      | inr n => exact absurd happ app_inl_inl_inr
    | inr ni =>
      rcases sym_new (σ := .inh) (fun h => h) hi with ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
        first | cases h' | skip
      exact happ.elim
  · rintro ⟨m, rfl, i, hi, happ⟩
    exact ⟨.inl i, (sym_old (notD_sg hD (σ := .inh) (fun h => h)) i).mpr hi, happ⟩

/-- The sorts of the extension: the old sorts and the detached sort names. -/
theorem isSort_ext_sg {x : Ext M} :
    IsSort (extModel c D I) x ↔ (∃ σ, x = .inl σ ∧ IsSort I σ) ∨ (∃ n, x = .inr (.srt n) ∧ D (.sort n)) := by
  constructor
  · rintro ⟨s0, hs0, hinh⟩
    cases s0 with
    | inl s1 =>
      obtain ⟨m, rfl, hm⟩ := (inh_old_sg hD).mp hinh
      exact .inl ⟨m, rfl, s1, (sym_old (notD_sg hD (σ := .sortSort) (fun h => h)) s1).mp hs0, hm⟩
    | inr n0 =>
      rcases sym_new (σ := .sortSort) (fun h => h) hs0 with ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
        first | cases h' | skip
      obtain ⟨i, hi, happ⟩ := hinh
      cases i with
      | inl i0 => exact absurd happ app_inl_inr
      | inr ni =>
        rcases sym_new (σ := .inh) (fun h => h) hi with ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
          first | cases h' | skip
        obtain ⟨nm, hnm, rfl⟩ := happ
        exact .inr ⟨nm, rfl, hnm⟩
  · rintro (⟨σ, rfl, s1, hs1, hinh⟩ | ⟨n, rfl, hn⟩)
    · exact ⟨.inl s1, (sym_old (notD_sg hD (σ := .sortSort) (fun h => h)) s1).mpr hs1, (inh_old_sg hD).mpr ⟨σ, rfl, hinh⟩⟩
    · exact ⟨.inr .sorts, rfl, .inr .inh, rfl, ⟨n, hn, rfl⟩⟩

/-- An element of a sort of the extension: by the sort's code (`InhX`). -/
theorem inh_code_sg (s : M ⊕ String) {x : Ext M} :
    Inh (extModel c D I) (match s with | .inl σ => .inl σ | .inr n => .inr (.srt n)) x ↔ InhX c D I s x := by
  cases s with
  | inl σ => exact inh_old_sg hD
  | inr n => exact inh_new

omit hD in
/-- `⌈x⌉{σ,σ'}` in the extension where `σ` or `σ'` is a detached sort name: the inhabitants of
`σ'`, for `x` in `σ`. -/
theorem ceilE_mixed_sg (s s' : M ⊕ String) (hmix : (∃ n, s = .inr n) ∨ (∃ n, s' = .inr n)) {x m : Ext M} :
    CeilE (extModel c D I) (match s with | .inl σ => .inl σ | .inr n => .inr (.srt n))
      (match s' with | .inl σ => .inl σ | .inr n => .inr (.srt n)) x m ↔ InhX c D I s x ∧ InhX c D I s' m := by
  have hceil : ∀ {nh : Added M}, (extModel c D I).evalSymb .ceil (.inr nh) → nh = .ceil := fun {nh} hh => by
    rcases sym_new (σ := .ceil) (fun h => h) hh with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨_, h', _⟩ <;>
      first | cases h' | rfl
  cases s with
  | inl a =>
    cases s' with
    | inl b => rcases hmix with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    | inr n' =>
      constructor
      · rintro ⟨a2, ⟨a1, ⟨h, hh, h1⟩, h2⟩, h3⟩
        cases h with
        | inl h0 =>
          cases a1 with
          | inl a10 => exact absurd h2 app_inl_inr
          | inr na => exact absurd h1 app_inl_inl_inr
        | inr nh =>
          obtain rfl := hceil hh
          have e1 : a1 = .inr (.ceil1 (.inl a)) := h1
          subst e1
          have e2 : a2 = .inr (.ceil2 (.inl a) (.inr n')) := h2
          subst e2
          exact h3
      · intro h
        exact ⟨_, ⟨_, ⟨.inr .ceil, rfl, rfl⟩, rfl⟩, h⟩
  | inr n =>
    cases s' with
    | inl b =>
      constructor
      · rintro ⟨a2, ⟨a1, ⟨h, hh, h1⟩, h2⟩, h3⟩
        cases h with
        | inl h0 => exact absurd h1 app_inl_inr
        | inr nh =>
          obtain rfl := hceil hh
          have e1 : a1 = .inr (.ceil1 (.inr n)) := h1
          subst e1
          have e2 : a2 = .inr (.ceil2 (.inr n) (.inl b)) := h2
          subst e2
          exact h3
      · intro h
        exact ⟨_, ⟨_, ⟨.inr .ceil, rfl, rfl⟩, rfl⟩, h⟩
    | inr n' =>
      constructor
      · rintro ⟨a2, ⟨a1, ⟨h, hh, h1⟩, h2⟩, h3⟩
        cases h with
        | inl h0 => exact absurd h1 app_inl_inr
        | inr nh =>
          obtain rfl := hceil hh
          have e1 : a1 = .inr (.ceil1 (.inr n)) := h1
          subst e1
          have e2 : a2 = .inr (.ceil2 (.inr n) (.inr n')) := h2
          subst e2
          exact h3
      · intro h
        exact ⟨_, ⟨_, ⟨.inr .ceil, rfl, rfl⟩, rfl⟩, h⟩

/-- **`⌈x⌉{σ,σ'}` in the extension is the sort `σ'`**, for sorts `σ`, `σ'` of the extension and
`x` in `σ`, where the model satisfies `ceilDefItem`: at two old sorts by the model, and where one
is a detached sort name by the added elements `ceil1`, `ceil2`. -/
theorem ceilE_sorts_sg (hDI : DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) {σ σ' x : Ext M}
    (hσ : IsSort (extModel c D I) σ) (hσ' : IsSort (extModel c D I) σ') (hx : Inh (extModel c D I) σ x)
    (m : Ext M) : CeilE (extModel c D I) σ σ' x m ↔ Inh (extModel c D I) σ' m := by
  rcases (isSort_ext_sg hD).mp hσ with ⟨a, rfl, ha⟩ | ⟨n, rfl, -⟩ <;>
    rcases (isSort_ext_sg hD).mp hσ' with ⟨b, rfl, hb⟩ | ⟨n', rfl, -⟩
  · obtain ⟨x0, rfl, hx0⟩ := (inh_old_sg hD).mp hx
    have hcs : ¬ D .ceil := notD_sg hD (σ := .ceil) (fun h => h)
    constructor
    · rintro ⟨a2, ⟨a1, ⟨h, hh, h1⟩, h2⟩, h3⟩
      cases h with
      | inl h0 =>
        cases a1 with
        | inr na => exact absurd h1 app_inl_inl_inr
        | inl a10 =>
          cases a2 with
          | inr na => exact absurd h2 app_inl_inl_inr
          | inl a20 =>
            cases m with
            | inr nm => exact absurd h3 app_inl_inl_inr
            | inl m0 =>
              exact (inh_old_sg hD).mpr ⟨m0, rfl, (KoreAML.ceilE_of hDI hc ha hb hx0 m0).mp
                ⟨a20, ⟨a10, ⟨h0, (sym_old hcs h0).mp hh, h1⟩, h2⟩, h3⟩⟩
      | inr nh =>
        rcases sym_new (σ := .ceil) (fun h => h) hh with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨_, h', _⟩ <;>
          first | cases h' | skip
        have e1 : a1 = .inr (.ceil1 (.inl a)) := h1
        subst e1
        exact h2.elim
    · intro hm
      obtain ⟨m0, rfl, hm0⟩ := (inh_old_sg hD).mp hm
      obtain ⟨a20, ⟨a10, ⟨h0, hh, h1⟩, h2⟩, h3⟩ := (KoreAML.ceilE_of hDI hc ha hb hx0 m0).mpr hm0
      exact ⟨.inl a20, ⟨.inl a10, ⟨.inl h0, (sym_old hcs h0).mpr hh, h1⟩, h2⟩, h3⟩
  · rw [ceilE_mixed_sg (.inl a) (.inr n') (.inr ⟨n', rfl⟩), inh_code_sg hD (.inr n')]
    exact and_iff_right ((inh_code_sg hD (.inl a)).mp hx)
  · rw [ceilE_mixed_sg (.inr n) (.inl b) (.inl ⟨n, rfl⟩), inh_code_sg hD (.inl b)]
    exact and_iff_right ((inh_code_sg hD (.inr n)).mp hx)
  · rw [ceilE_mixed_sg (.inr n) (.inr n') (.inl ⟨n, rfl⟩), inh_code_sg hD (.inr n')]
    exact and_iff_right ((inh_code_sg hD (.inr n)).mp hx)

/-! ## The signature's items outside the class -/

omit hD in
/-- **Definedness holds in the extension.** -/
theorem sat_definedness_sg (x : EVar) : extModel c D I ⊧ᴵ @definedness KoreAML.Sym _ x := by
  intro e m
  simp only [definedness, Pattern.interpret]
  rintro ⟨a, ha⟩
  exact ha ⟨.inr .dfn, _, rfl, rfl, trivial⟩

/-- **`ceilDefItem` holds in the extension**, where the model satisfies it. -/
theorem sat_ceilDef_sg (hDI : DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) :
    extModel c D I ⊧ᴵ KoreAML.ceilDefItem.pat := by
  intro e' pt
  unfold KoreAML.ceilDefItem
  dsimp only
  rw [guarded_iff]
  intro hw
  have h1 := hw _ (List.mem_cons_self ..)
  have h2 := hw _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3 := hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  unfold KoreAML.sortGuard at h1 h2
  rw [KoreAML.interp_member (ext_defOK c D I), KoreAML.interp_sortsDomain] at h1 h2
  rw [KoreAML.interp_member (ext_defOK c D I), KoreAML.interp_inhOf_of (fun a => KoreAML.interp_evar)] at h3
  rw [KoreAML.interp_equal (ext_defOK c D I)]
  intro m
  rw [KoreAML.interp_sCeil_raw, KoreAML.interp_inhOf_of (fun a => KoreAML.interp_evar)]
  simp only [KoreAML.interp_evar]
  constructor
  · rintro ⟨_, _, _, rfl, rfl, rfl, h⟩
    exact (ceilE_sorts_sg hD hDI hc h1 h2 h3 m).mp h
  · intro h
    exact ⟨_, _, _, rfl, rfl, rfl, (ceilE_sorts_sg hD hDI hc h1 h2 h3 m).mpr h⟩

/-- **`ceilArityItem` holds in the extension**, where the model satisfies `ceilDefItem`. -/
theorem sat_ceilArity_sg (hDI : DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) :
    extModel c D I ⊧ᴵ KoreAML.ceilArityItem.pat := by
  intro e' pt
  unfold KoreAML.ceilArityItem
  dsimp only
  rw [guarded_iff]
  intro hw
  have h1 := hw _ (List.mem_cons_self ..)
  have h2 := hw _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold KoreAML.sortGuard at h1 h2
  rw [KoreAML.interp_member (ext_defOK c D I), KoreAML.interp_sortsDomain] at h1 h2
  rw [KoreAML.interp_included (ext_defOK c D I)]
  intro a ha
  rw [KoreAML.interp_sCeil_raw] at ha
  obtain ⟨σ, σ', x, hσ, hσ', hx, hce⟩ := ha
  rw [KoreAML.interp_evar] at hσ hσ'
  subst hσ hσ'
  rw [KoreAML.interp_inhOf_of (fun a => KoreAML.interp_evar)] at hx ⊢
  exact (ceilE_sorts_sg hD hDI hc h1 h2 hx a).mp hce

/-- **`dvArityItem` holds in the extension**, where the model satisfies it: at an old sort by the
model, at a detached sort name because a literal applied to it gives values of that sort. -/
theorem sat_dvArity_sg (hDI : DefOK I) {lit : String} (hdv : I ⊧ᴵ (KoreAML.dvArityItem lit).pat) :
    extModel c D I ⊧ᴵ (KoreAML.dvArityItem lit).pat := by
  intro e' pt
  unfold KoreAML.dvArityItem
  dsimp only
  rw [guarded_iff]
  intro hw
  have h1 := hw _ (List.mem_cons_self ..)
  unfold KoreAML.sortGuard at h1
  rw [KoreAML.interp_member (ext_defOK c D I), KoreAML.interp_sortsDomain] at h1
  rw [KoreAML.interp_included (ext_defOK c D I)]
  intro a ha
  rw [KoreAML.interp_app] at ha
  obtain ⟨d, b, hd, hb, happ⟩ := ha
  rw [KoreAML.interp_evar] at hb
  subst hb
  rw [KoreAML.interp_inhOf_of (fun a => KoreAML.interp_evar)]
  rcases (isSort_ext_sg hD).mp h1 with ⟨σ, hσe, hσ⟩ | ⟨n, hne, hn⟩
  · rw [hσe] at happ ⊢
    cases d with
    | inl d0 =>
      cases a with
      | inr na => exact absurd happ app_inl_inl_inr
      | inl a0 =>
        have hI1 := hdv ⟨fun _ => σ, fun _ _ => False⟩ default
        unfold KoreAML.dvArityItem at hI1
        dsimp only at hI1
        rw [guarded_iff] at hI1
        have h3 := hI1 (fun w hw => by
          rcases List.mem_cons.mp hw with rfl | hw
          · unfold KoreAML.sortGuard
            rw [KoreAML.interp_member hDI, KoreAML.interp_sortsDomain]
            exact hσ
          · cases hw)
        rw [KoreAML.interp_included hDI] at h3
        have h4 := h3 a0 (KoreAML.interp_app.mpr
          ⟨d0, σ, (sym_old (notD_sg hD (σ := .dv lit) (fun h => h)) d0).mp hd, rfl, happ⟩)
        rw [KoreAML.interp_inhOf_of (fun a => KoreAML.interp_evar)] at h4
        exact (inh_old_sg hD).mpr ⟨a0, rfl, h4⟩
    | inr nd =>
      rcases sym_new (σ := .dv lit) (fun h => h) hd with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h', rfl⟩ <;>
        first | cases h' | skip
      exact happ.elim
  · rw [hne] at happ ⊢
    cases d with
    | inl d0 => exact absurd happ app_inl_inr
    | inr nd =>
      rcases sym_new (σ := .dv lit) (fun h => h) hd with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h', rfl⟩ <;>
        first | cases h' | skip
      obtain ⟨s, lit', hn', -, hds, hv, rfl⟩ := happ
      exact inh_new.mpr ⟨s, _, hn', hds, hv, rfl⟩

/-- **The sort constant of a sort outside `D` holds in the extension**, where the model satisfies
it: the sort's name denotes the same old element, which is a sort of the extension. -/
theorem sat_sortConst_sg (hDI : DefOK I) {n : String} (hn : ¬ D (.sort n))
    (h : I ⊧ᴵ (KoreAML.sortConstantItem ⟨n, [], false⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.sortConstantItem ⟨n, [], false⟩).pat := by
  have hss : ¬ D .sortSort := notD_sg hD (σ := .sortSort) (fun h => h)
  intro e' pt
  have hI0 := h KoreAML.val0 default
  change (KoreAML.sExists ⟨1⟩ (KoreAML.sym .sortSort)
    (KoreAML.sym (.sort n) ≡ .evar ⟨1⟩)).interpret I KoreAML.val0 default at hI0
  show (KoreAML.sExists ⟨1⟩ (KoreAML.sym .sortSort)
    (KoreAML.sym (.sort n) ≡ .evar ⟨1⟩)).interpret (extModel c D I) e' pt
  rw [interp_sExists' hDI] at hI0
  rw [interp_sExists' (ext_defOK c D I)]
  obtain ⟨y0, hy0, heq⟩ := hI0
  rw [KoreAML.interp_equal hDI] at heq
  refine ⟨.inl y0, ?_, ?_⟩
  · rw [KoreAML.interp_inhOf] at hy0 ⊢
    obtain ⟨σ, hσ, hinh⟩ := hy0
    exact ⟨.inl σ, (sym_old hss σ).mpr hσ, (inh_old_sg hD).mpr ⟨y0, rfl, hinh⟩⟩
  · rw [KoreAML.interp_equal (ext_defOK c D I)]
    intro a
    simp only [KoreAML.interp_evar, Function.update_same]
    have hy : ∀ m, I.evalSymb (.sort n) m ↔ m = y0 := fun m => by
      have := heq m
      simp only [KoreAML.interp_evar, Function.update_same] at this
      exact this
    cases a with
    | inl m =>
      rw [KoreAML.interp_sym, sym_old hn m, hy m]
      exact ⟨fun h => h ▸ rfl, fun h => Sum.inl.inj h⟩
    | inr na =>
      rw [KoreAML.interp_sym]
      exact ⟨fun h' => absurd h' ((inv_sym (c := c) (I := I) (σ := .sort n) trivial hn).2 na), fun h' => by cases h'⟩

end

/-! ## Patterns of the class whose symbols are outside `D` -/

section
variable {D : KoreAML.Sym → Prop}

/-- `D` reaches a pattern of the class only through its symbols: a pattern of the class at any
set of names, none of whose symbols is in `D`, is of the class at `D`. -/
theorem ownSorted_clean_sg {D' : KoreAML.Sym → Prop} {V : List EVar} {W : List SVar} {k : OwnKind}
    {φ : KoreAML.P} (h : OwnSorted D' V W k φ) : (∀ σ ∈ psyms φ, ¬ D σ) → OwnSorted D V W k φ := by
  induction h with
  | evar hx => intro _; exact .evar hx
  | svar hX => intro _; exact .svar hX
  | bot => intro _; exact .bot
  | botP => intro _; exact .botP
  | sym hp _ => intro hn; exact .sym hp (hn _ (List.mem_singleton_self _))
  | inh => intro _; exact .inh
  | dv l => intro _; exact .dv l
  | ceil _ ih => intro hn; exact .ceil (ih fun σ h => hn σ (by simp [psyms, h]))
  | sorts => intro _; exact .sorts
  | appH _ _ ih1 ih2 =>
    intro hn; exact .appH (ih1 fun σ h => hn σ (by simp [psyms, h])) (ih2 fun σ h => hn σ (by simp [psyms, h]))
  | appE _ _ ih1 ih2 =>
    intro hn; exact .appE (ih1 fun σ h => hn σ (by simp [psyms, h])) (ih2 fun σ h => hn σ (by simp [psyms, h]))
  | defined hk _ ih => intro hn; exact .defined hk (ih fun σ h => hn σ (by simp [psyms, h]))
  | impEO _ _ ih1 ih2 =>
    intro hn; exact .impEO (ih1 fun σ h => hn σ (by simp [psyms, h])) (ih2 fun σ h => hn σ (by simp [psyms, h]))
  | impOU _ _ ih1 ih2 =>
    intro hn; exact .impOU (ih1 fun σ h => hn σ (by simp [psyms, h])) (ih2 fun σ h => hn σ (by simp [psyms, h]))
  | impUE _ _ ih1 ih2 =>
    intro hn; exact .impUE (ih1 fun σ h => hn σ (by simp [psyms, h])) (ih2 fun σ h => hn σ (by simp [psyms, h]))
  | impPP _ _ ih1 ih2 =>
    intro hn; exact .impPP (ih1 fun σ h => hn σ (by simp [psyms, h])) (ih2 fun σ h => hn σ (by simp [psyms, h]))
  | impOO _ _ ih1 ih2 =>
    intro hn; exact .impOO (ih1 fun σ h => hn σ (by simp [psyms, h])) (ih2 fun σ h => hn σ (by simp [psyms, h]))
  | sEx _ hV' hk _ ihs ih =>
    intro hn
    exact .sEx (ihs fun σ h => hn σ (by
        simp [psyms, KoreAML.sExists, ML.member, KoreAML.inhOf, KoreAML.sym, Pattern.conjunction,
          Pattern.disjunction, Pattern.negation, h]))
      hV' hk (ih fun σ h => hn σ (by
        simp [psyms, KoreAML.sExists, ML.member, KoreAML.inhOf, KoreAML.sym, Pattern.conjunction,
          Pattern.disjunction, Pattern.negation, h]))
  | mu _ ih => intro hn; exact .mu (ih fun σ h => hn σ (by simp [psyms, h]))
  | weak hk _ ih => intro hn; exact .weak hk (ih hn)

/-- The arity item of a symbol is of the class at no name. -/
theorem own_arity_sg (c : Semantics) (k : CtorSig) :
    OwnSorted (fun _ => False) [] [] .pred (symArityItem c k).pat := by
  obtain ⟨h, xs, -, hw⟩ := symApp_head c k.name
  rw [symArity_pat_rs hw]
  refine .included (.appList (.symC id) ?_) (.toOld (.inhOf (.sortC id)))
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
    exact .toOld (.sortC id)
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
    exact .toOld (.inhOf (.sortC id))

/-- The arity item of next at a sort without parameters is of the class at no name. -/
theorem own_next_sg (n : String) :
    OwnSorted (fun _ => False) [] [] .pred (KoreAML.nextArityItem [] (KoreAML.srt n)).pat := by
  simp only [KoreAML.nextArityItem, KoreAML.srt, KoreAML.sortVarsOf, KoreAML.sortVarsOfList, List.eraseDups_nil,
    List.map_nil, KoreAML.guarded, KoreAML.trSort_const]
  exact .included (.sNext id (.toOld (.inhOf (.sortC id)))) (.toOld (.inhOf (.sortC id)))

end

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- `transfer` without guards, for a pattern of the class at no name whose symbols are outside
`D`. -/
theorem transfer0_sg (hDI : DefOK I) {body : KoreAML.P} {k : OwnKind}
    (hb : OwnSorted (fun _ => False) [] [] k body) (hk : k = .pred ∨ k = .co)
    (hn : ∀ σ ∈ psyms body, ¬ D σ) (h : I ⊧ᴵ body) : extModel c D I ⊧ᴵ body :=
  transfer (gs := []) hD hDI nil_sub (ownSorted_clean_sg hb hn) hk h

omit hD in
/-- A premise of `ΓSig` that names nothing of `D` is a premise of `Γown`. -/
theorem own_of_sig_sg {φ : KoreAML.P} (h : ΓSig c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : Γown c D φ :=
  ⟨.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl h))))))), hn⟩

omit hD in
/-- `plainSym`, decided. -/
theorem noPlain_of_sg {φ : KoreAML.P}
    (h : (psyms φ).all (fun σ => match σ with
      | .sort _ | .symbol _ | .next | .str _ | .untranslated _ => false | _ => true) = true) :
    ∀ σ ∈ psyms φ, ¬ plainSym σ := by
  intro σ hσ hp
  have := List.all_eq_true.mp h σ hσ
  cases σ <;> first | exact absurd this Bool.false_ne_true | exact hp

/-- The symbols of a pattern that are no sort constant and no symbol of the definition are
outside `D`. -/
theorem clean_of_plain_sg {φ : KoreAML.P} (h : ∀ σ ∈ psyms φ, ¬ plainSym σ) : ∀ σ ∈ psyms φ, ¬ D σ :=
  fun σ hσ => notD_sg hD (h σ hσ)

/-- **The extension satisfies every premise of `ΓSig` that names nothing of `D`**, for a model of
`Γown c D` and names `D` that are sort constants and symbols of the definition. -/
theorem sat_own_sig (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : ΓSig c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) :
    extModel c D I ⊧ᴵ φ := by
  have hDI : DefOK I := KoreAML.defOK_of fun x =>
    hI _ (own_of_sig_sg (.inl (.inr ⟨x, rfl⟩)) (clean_of_plain_sg hD fun σ hσ => by
      simp [psyms, definedness, Pattern.universal, Pattern.negation] at hσ
      subst hσ; exact id))
  have hc : I ⊧ᴵ KoreAML.ceilDefItem.pat := hI _ (own_of_sig_sg
    (.inl (.inl ⟨KoreAML.ceilDefItem, by unfold sigItems; simp, rfl⟩))
    (clean_of_plain_sg hD (noPlain_of_sg (by decide))))
  rcases hφ with (⟨it, hit, rfl⟩ | ⟨x, rfl⟩) | ⟨lit, rfl⟩
  · have hI' := hI _ (own_of_sig_sg (.inl (.inl ⟨it, hit, rfl⟩)) hn)
    unfold sigItems at hit
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hit
    rcases hit with ((rfl | ⟨s, -, rfl⟩) | ⟨k, -, rfl⟩) | (rfl | rfl | rfl)
    · exact sat_definedness_sg ⟨1⟩
    · exact sat_sortConst_sg hD hDI (hn _ (by simp [psyms, KoreAML.sortConstantItem, sortDeclOf, KoreAML.guarded,
        KoreAML.sExists, KoreAML.appList, KoreAML.sym, ML.equal, ML.total, Pattern.negation])) hI'
    · exact transfer0_sg hD hDI (own_arity_sg c k) (.inl rfl) hn hI'
    · exact sat_ceilArity_sg hD hDI hc
    · exact sat_ceilDef_sg hD hDI hc
    · exact transfer0_sg hD hDI (own_next_sg _) (.inl rfl) hn hI'
  · exact sat_definedness_sg x
  · exact sat_dvArity_sg hD hDI (hI _ (own_of_sig_sg (.inr ⟨lit, rfl⟩) hn))

end

/-! ## Guarded premises -/

theorem psyms_conjList_sg : ∀ {ws : List KoreAML.P} {w : KoreAML.P} {σ : KoreAML.Sym}, w ∈ ws →
    σ ∈ psyms w → σ ∈ psyms (KoreAML.conjList ws)
  | [], _, _, hw, _ => absurd hw List.not_mem_nil
  | [_], _, _, hw, hσ => by rw [List.mem_singleton.mp hw] at hσ; exact hσ
  | w1 :: w2 :: ws, w, σ, hw, hσ => by
    have key : σ ∈ psyms w1 ∨ σ ∈ psyms (KoreAML.conjList (w2 :: ws)) := by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inl hσ
      · exact .inr (psyms_conjList_sg hw hσ)
    unfold KoreAML.conjList
    simp only [psyms, List.mem_append, List.not_mem_nil, or_false]
    rcases key with h | h <;> simp [h]

theorem psyms_guarded_body_sg {ws : List KoreAML.P} {φ : KoreAML.P} {σ : KoreAML.Sym} (h : σ ∈ psyms φ) :
    σ ∈ psyms (KoreAML.guarded ws φ) := by
  cases ws with
  | nil => exact h
  | cons w ws => simp [KoreAML.guarded, psyms, h]

theorem psyms_guarded_guard_sg {gs : List (EVar × KoreAML.P)} {body : KoreAML.P} {p : EVar × KoreAML.P}
    {σ : KoreAML.Sym} (hp : p ∈ gs) (hσ : σ ∈ psyms p.2) : σ ∈ psyms (KoreAML.guarded (memGs gs) body) := by
  have hw : p.1 ∈∈ KoreAML.inhOf p.2 ∈ memGs gs := List.mem_map.mpr ⟨p, hp, rfl⟩
  have h1 : σ ∈ psyms (p.1 ∈∈ KoreAML.inhOf p.2) := by
    simp [ML.member, psyms, KoreAML.inhOf, KoreAML.sym, Pattern.conjunction, Pattern.disjunction,
      Pattern.negation, hσ]
  have h2 := psyms_conjList_sg hw h1
  cases hg : memGs gs with
  | nil => rw [hg] at hw; exact absurd hw List.not_mem_nil
  | cons w ws =>
    rw [hg] at h2
    show σ ∈ psyms (KoreAML.conjList (w :: ws) ⇒ body)
    simp [psyms, h2]

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- `transfer` for a guarded premise of the class at no name whose symbols are outside `D`. -/
theorem transferG_sg (hDI : DefOK I) {gs : List (EVar × KoreAML.P)} {body : KoreAML.P} {k : OwnKind}
    (hs : ∀ p ∈ gs, OwnSorted (fun _ => False) [] [] .ex p.2)
    (hb : OwnSorted (fun _ => False) (gs.map (·.1)) [] k body) (hk : k = .pred ∨ k = .co)
    (hn : ∀ σ ∈ psyms (KoreAML.guarded (memGs gs) body), ¬ D σ)
    (h : I ⊧ᴵ KoreAML.guarded (memGs gs) body) : extModel c D I ⊧ᴵ KoreAML.guarded (memGs gs) body :=
  transfer hD hDI (fun p hp => ownSorted_clean_sg (hs p hp) fun σ hσ => hn σ (psyms_guarded_guard_sg hp hσ))
    (ownSorted_clean_sg hb fun σ hσ => hn σ (psyms_guarded_body_sg hσ)) hk h

omit [Inhabited M] in
/-- A model of `Γown c D` satisfies definedness. -/
theorem defOK_own_sg (hI : I ⊧ᴵP Γown c D) : DefOK I :=
  KoreAML.defOK_of fun x =>
    hI _ (own_of_sig_sg (.inl (.inr ⟨x, rfl⟩)) (clean_of_plain_sg hD fun σ hσ => by
      simp [psyms, definedness, Pattern.universal, Pattern.negation] at hσ
      subst hσ; exact id))

end

/-! ## The collections' axioms -/

section
variable {V : List EVar} {W : List SVar} (c : Semantics) (k : CollSig)

local notation "Own0" => OwnSorted (fun _ => False)

theorem ownC_sg {a b : KoreAML.P} (ha : Own0 V W .old a) (hb : Own0 V W .old b) : Own0 V W .ex (collC c k a b) :=
  .appE (.appE (.symC id) ha) hb
theorem ownE_sg {a b : KoreAML.P} (ha : Own0 V W .old a) (hb : Own0 V W .old b) : Own0 V W .ex (collE c k a b) :=
  .appE (.appE (.symC id) ha) hb
theorem ownI_sg {a : KoreAML.P} (ha : Own0 V W .old a) : Own0 V W .ex (collI c k a) :=
  .appE (.symC id) ha

/-- Derives that a collection axiom's body is of the class at no name. -/
local macro "own_tac" : tactic => `(tactic| repeat (first
  | exact OwnSorted.evar (by decide)
  | exact OwnSorted.toOld (OwnSorted.evar (by decide))
  | exact OwnSorted.botP
  | exact OwnSorted.symC id
  | exact OwnSorted.sortC id
  | apply OwnSorted.sEx (V' := []) (OwnSorted.sortC id) nil_sub (.inr (.inl rfl))
  | apply OwnSorted.conj_pred
  | apply OwnSorted.conj_ex_old
  | apply OwnSorted.disj_pred
  | apply OwnSorted.equal_ex
  | apply OwnSorted.defined (.inl rfl)
  | apply OwnSorted.neg_pred
  | apply OwnSorted.impPP
  | apply ownC_sg
  | apply ownE_sg
  | apply ownI_sg
  | apply OwnSorted.toOld (k := OwnKind.ex)))

theorem own_mapUnitSplit_sg : Own0 [⟨1⟩, ⟨2⟩] [] .pred
    (⌈collU c k ⋀ collC c k (.evar ⟨1⟩) (.evar ⟨2⟩)⌉ ⇒ ((.evar ⟨1⟩ ≡ collU c k) ⋀ (.evar ⟨2⟩ ≡ collU c k))) := by own_tac

theorem own_mapElemNotUnit_sg : Own0 [⟨1⟩, ⟨2⟩] [] .pred
    (∼⌈collU c k ⋀ collE c k (.evar ⟨1⟩) (.evar ⟨2⟩)⌉) := by own_tac

theorem own_mapElemAtom_sg : Own0 [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩] [] .pred
    (⌈collE c k (.evar ⟨3⟩) (.evar ⟨4⟩) ⋀ collC c k (collE c k (.evar ⟨1⟩) (.evar ⟨2⟩)) (.evar ⟨5⟩)⌉ ⇒
      ((.evar ⟨1⟩ ≡ .evar ⟨3⟩) ⋀ (.evar ⟨2⟩ ≡ .evar ⟨4⟩) ⋀ (.evar ⟨5⟩ ≡ collU c k))) := by own_tac

theorem own_mapDecomp_sg : Own0 [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩] [] .pred
    (⌈collC c k (collE c k (.evar ⟨1⟩) (.evar ⟨2⟩)) (.evar ⟨3⟩) ⋀ collC c k (.evar ⟨4⟩) (.evar ⟨5⟩)⌉ ⇒
      (KoreAML.sExists ⟨6⟩ (sortP (c.sortName k.sort))
          ((.evar ⟨4⟩ ≡ collC c k (collE c k (.evar ⟨1⟩) (.evar ⟨2⟩)) (.evar ⟨6⟩)) ⋀
            (.evar ⟨3⟩ ≡ collC c k (.evar ⟨6⟩) (.evar ⟨5⟩))) ⋁
        KoreAML.sExists ⟨6⟩ (sortP (c.sortName k.sort))
          ((.evar ⟨5⟩ ≡ collC c k (collE c k (.evar ⟨1⟩) (.evar ⟨2⟩)) (.evar ⟨6⟩)) ⋀
            (.evar ⟨3⟩ ≡ collC c k (.evar ⟨4⟩) (.evar ⟨6⟩))))) := by own_tac

theorem own_elemNotUnit_sg : Own0 [⟨1⟩] [] .pred (∼⌈collU c k ⋀ collI c k (.evar ⟨1⟩)⌉) := by own_tac

theorem own_elemAtom_sg : Own0 [⟨1⟩, ⟨2⟩, ⟨3⟩] [] .pred
    (⌈collI c k (.evar ⟨2⟩) ⋀ collC c k (collI c k (.evar ⟨1⟩)) (.evar ⟨3⟩)⌉ ⇒
      ((.evar ⟨1⟩ ≡ .evar ⟨2⟩) ⋀ (.evar ⟨3⟩ ≡ collU c k))) := by own_tac

theorem own_elemAtomBack_sg : Own0 [⟨1⟩, ⟨2⟩, ⟨3⟩] [] .pred
    (⌈collI c k (.evar ⟨2⟩) ⋀ collC c k (.evar ⟨3⟩) (collI c k (.evar ⟨1⟩))⌉ ⇒
      ((.evar ⟨1⟩ ≡ .evar ⟨2⟩) ⋀ (.evar ⟨3⟩ ≡ collU c k))) := by own_tac

theorem own_listDecomp_sg : Own0 [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] [] .pred
    (⌈collC c k (collI c k (.evar ⟨1⟩)) (.evar ⟨2⟩) ⋀ collC c k (.evar ⟨3⟩) (.evar ⟨4⟩)⌉ ⇒
      (((.evar ⟨3⟩ ≡ collU c k) ⋀ (.evar ⟨4⟩ ≡ collC c k (collI c k (.evar ⟨1⟩)) (.evar ⟨2⟩))) ⋁
        KoreAML.sExists ⟨5⟩ (sortP (c.sortName k.sort))
          ((.evar ⟨3⟩ ≡ collC c k (collI c k (.evar ⟨1⟩)) (.evar ⟨5⟩)) ⋀
            (.evar ⟨2⟩ ≡ collC c k (.evar ⟨5⟩) (.evar ⟨4⟩))))) := by own_tac

theorem own_setDecomp_sg : Own0 [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] [] .pred
    (⌈collC c k (collI c k (.evar ⟨1⟩)) (.evar ⟨2⟩) ⋀ collC c k (.evar ⟨3⟩) (.evar ⟨4⟩)⌉ ⇒
      (KoreAML.sExists ⟨5⟩ (sortP (c.sortName k.sort))
          ((.evar ⟨3⟩ ≡ collC c k (collI c k (.evar ⟨1⟩)) (.evar ⟨5⟩)) ⋀
            (.evar ⟨2⟩ ≡ collC c k (.evar ⟨5⟩) (.evar ⟨4⟩))) ⋁
        KoreAML.sExists ⟨5⟩ (sortP (c.sortName k.sort))
          ((.evar ⟨4⟩ ≡ collC c k (collI c k (.evar ⟨1⟩)) (.evar ⟨5⟩)) ⋀
            (.evar ⟨2⟩ ≡ collC c k (.evar ⟨3⟩) (.evar ⟨5⟩))))) := by own_tac

end

/-- Guards at sort constants are of the class at no name. -/
theorem own_sortGuards_sg {gs : List (EVar × KoreAML.P)} (h : ∀ p ∈ gs, ∃ n, p.2 = sortP n) :
    ∀ p ∈ gs, OwnSorted (fun _ => False) [] [] .ex p.2 := fun p hp => by
  obtain ⟨n, hn⟩ := h p hp
  rw [hn]
  exact .sortC id

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- **The extension satisfies every premise of `ΓColls` that names nothing of `D`**, for a model of
`Γown c D` and names `D` that are sort constants and symbols of the definition: each axiom of a
collection is a guarded premise of the class. -/
theorem sat_own_colls (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : ΓColls c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) :
    extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inl (.inl (.inl (.inl (.inl (.inr hφ))))), hn⟩
  obtain ⟨k, -, hmem⟩ := hφ
  have hg : ∀ (l : List EVar) (ss : List Srt), l.length = ss.length →
      ∀ p ∈ l.zip (ss.map fun s => sortP (c.sortName s)), ∃ n, p.2 = sortP n := fun l ss _ p hp => by
    obtain ⟨-, h2⟩ := List.of_mem_zip hp
    obtain ⟨s, -, hs⟩ := List.mem_map.mp h2
    exact ⟨_, hs.symm⟩
  unfold collAxioms at hmem
  split at hmem
  · simp only [mapCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩] : List EVar).zip ([k.sort, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_mapUnitSplit_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩] : List EVar).zip ([k.key, valSort k].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_mapElemNotUnit_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩] : List EVar).zip
          ([k.key, valSort k, k.key, valSort k, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_mapElemAtom_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩] : List EVar).zip
          ([k.key, valSort k, k.sort, k.sort, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_mapDecomp_sg c k) (.inl rfl) hn hI'
  · simp only [setCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩] : List EVar).zip ([k.sort, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_mapUnitSplit_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩] : List EVar).zip ([k.key].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_elemNotUnit_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩, ⟨3⟩] : List EVar).zip ([k.key, k.key, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_elemAtom_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] : List EVar).zip
          ([k.key, k.sort, k.sort, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_setDecomp_sg c k) (.inl rfl) hn hI'
  · simp only [listCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩] : List EVar).zip ([k.sort, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_mapUnitSplit_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩] : List EVar).zip ([k.key].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_elemNotUnit_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩, ⟨3⟩] : List EVar).zip ([k.key, k.key, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_elemAtom_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩, ⟨3⟩] : List EVar).zip ([k.key, k.key, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_elemAtomBack_sg c k) (.inl rfl) hn hI'
    · exact transferG_sg hD hDI (gs := ([⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] : List EVar).zip
          ([k.key, k.sort, k.sort, k.sort].map fun s => sortP (c.sortName s)))
        (own_sortGuards_sg (hg _ _ rfl)) (own_listDecomp_sg c k) (.inl rfl) hn hI'
  · exact absurd hmem List.not_mem_nil

end

end KCore.Cons
