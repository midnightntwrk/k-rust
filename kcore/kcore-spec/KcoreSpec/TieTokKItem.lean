/-
  A no-junk sentence that leaves out an injection (`Parse.ReadingNote.tokKItem`): where the sort the
  injection comes from has a value, the sentence has no model with `Γ`, for every interpretation of
  the parameters; at an element of that sort, no model of `Γ` satisfies it. KItem's no-junk
  sentence over its generators but the injections from a list of sorts: in a model of `Γ` it holds
  exactly where none of those sorts has an element (`kitemOmit_holds_iff_empty`).
-/
import KcoreSpec.Confined
import KcoreSpec.HypWf
import KcoreSpec.FnObligations
import KcoreSpec.TieLemmas
import KcoreSpec.Inhabited

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace Faithful

/-- **A no-junk sentence without an injection is refuted, for every interpretation.** Let N be a
constructor sort, `inj{a, N}` one of its generators that is not open, w a value of the sort a, and
`gs` generators of N each an injection `inj{b, N}` that is not open, from a sort b other than a,
incomparable with a and with no lower bound in common with it. Then no model of `Γ (c.withHooks H)`
satisfies the no-junk sentence of N over `gs`: `inj{a, N}(w)` is an element of N; the sentence
says it is one that some `inj{b, N}` builds from an element of b, which `inj{b, N}` builds alone
(Cons-Fun), so the two injections build one element, which their Cons-Dist item denies. -/
theorem noJunk_omitted_refuted {c : Semantics} (hcore : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (H : HookParams) {N a : Srt} (hN : N ∈ consSorts c) (hno : c.fnOvlSyms = [])
    (ha : Gen.inj a ∈ (c.gens N).filter (!c.isOpenGen ·)) {w : GroundTerm} (hw : c.sortOf w = some a)
    (hv : c.sortOf (.inj a N w) = some N) {gs : List Gen}
    (hgs : ∀ g ∈ gs, ∃ b, g = .inj b ∧ Gen.inj b ∈ (c.gens N).filter (!c.isOpenGen ·) ∧ b ≠ a ∧
      (c.le a b || c.le b a) = false ∧ c.lowerBounds a b = [] ∧ c.lowerBounds b a = [])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (c.withHooks H)) :
    ¬ (I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName N) (gs.map (Gen.toK c))).pat) := by
  intro hax
  haveI : OvlOK (c.withHooks H) := ovlOK_of_core ((Semantics.coreOK_withHooks c H).trans hcore)
  have hD := defOK hI
  have hw' : (c.withHooks H).sortOf w = some a := by rw [Semantics.sortOf_withHooks _ _ hr]; exact hw
  have hv' : (c.withHooks H).sortOf (.inj a N w) = some N := by rw [Semantics.sortOf_withHooks _ _ hr]; exact hv
  have hx : InS I (c.sortName N) (elemOf (c.withHooks H) I (.inj a N w)) :=
    (inS_iff _).mp (elemOf_spec hI hv' KoreAML.val0).2
  have hxw : InS I (c.sortName a) (elemOf (c.withHooks H) I w) :=
    (inS_iff _).mp (elemOf_spec hI hw' KoreAML.val0).2
  obtain ⟨g, hg, ys, hys, hgs'⟩ := noJunk_elim hD hax hx
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨b, rfl, hbmem, hba, hle, hlb1, hlb2⟩ := hgs g0 hg0
  obtain ⟨y, hy, rfl⟩ : ∃ y, InS I (c.sortName b) y ∧ ys = [y] := by
    cases hys with
    | cons hy hr => cases hr; exact ⟨_, hy, rfl⟩
  have hN' : N ∈ consSorts (c.withHooks H) := hN
  have hno' : (c.withHooks H).fnOvlSyms = [] := hno
  have hbmem' : Gen.inj b ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := hbmem
  have hamem' : Gen.inj a ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := ha
  obtain ⟨y1, -, hy1⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem hN' hbmem' rfl, rfl⟩)) (xs := [y]) rfl
    (single_sorts hy)
  have hy1 : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔ m = y1 := hy1
  have hset_b : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔
      m = elemOf (c.withHooks H) I (.inj a N w) := fun m => by
    rw [hy1 m, ← (hy1 _).mp hgs']
  have hset_a : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [elemOf (c.withHooks H) I w] m ↔
      m = elemOf (c.withHooks H) I (.inj a N w) := fun m => by
    rw [← (elemOf_spec hI hv' KoreAML.val0).1 m]
    exact (den_inj_gs hI hw' KoreAML.val0 m).symm
  have hseq : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [elemOf (c.withHooks H) I w] m ↔
      GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m := fun m => by rw [hset_a, hset_b]
  have hne : Gen.inj a ≠ Gen.inj b := fun h => hba (by cases h; rfl)
  rcases mem_pairs_of hne hamem' hbmem' with hp | hp
  · rcases injPair_mem hN' hp hle with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [_]) (ys := [y]) rfl rfl
        (single_sorts hxw) (single_sorts hy) hseq
    · exact hl hlb1
  · rcases injPair_mem hN' hp (by rw [Bool.or_comm]; exact hle) with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [y]) (ys := [_]) rfl rfl
        (single_sorts hy) (single_sorts hxw) (fun m => (hseq m).symm)
    · exact hl hlb2

/-- **A no-junk sentence without an injection, at an element of the injection's source sort.** Let
N be a constructor sort, `inj{a, N}` one of its generators that is not open, x an element of the
sort a in a model of `Γ (c.withHooks H)`, and `gs` generators of N each an injection `inj{b, N}`
that is not open, from a sort b other than a, incomparable with a and with no lower bound in common
with it. Then the model does not satisfy the no-junk sentence of N over `gs`: `inj{a, N}` builds
one element of N from x (Cons-Fun); the sentence says it is one that some `inj{b, N}` builds from
an element of b, so the two injections build one element, which their Cons-Dist item denies. -/
theorem noJunk_omitted_refuted_elem {c : Semantics} (H : HookParams) {N a : Srt} (hN : N ∈ consSorts c)
    (hno : c.fnOvlSyms = []) (ha : Gen.inj a ∈ (c.gens N).filter (!c.isOpenGen ·)) {gs : List Gen}
    (hgs : ∀ g ∈ gs, ∃ b, g = .inj b ∧ Gen.inj b ∈ (c.gens N).filter (!c.isOpenGen ·) ∧ b ≠ a ∧
      (c.le a b || c.le b a) = false ∧ c.lowerBounds a b = [] ∧ c.lowerBounds b a = [])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (c.withHooks H))
    {x : M} (hx : InS I (c.sortName a) x) :
    ¬ (I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName N) (gs.map (Gen.toK c))).pat) := by
  intro hax
  have hD := defOK hI
  have hN' : N ∈ consSorts (c.withHooks H) := hN
  have hno' : (c.withHooks H).fnOvlSyms = [] := hno
  have hamem' : Gen.inj a ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := ha
  obtain ⟨y0, hy0, hset_a⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem hN' hamem' rfl, rfl⟩))
    (xs := [x]) rfl (single_sorts hx)
  have hset_a : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [x] m ↔ m = y0 := hset_a
  obtain ⟨g, hg, ys, hys, hgs'⟩ := noJunk_elim hD hax hy0
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨b, rfl, hbmem, hba, hle, hlb1, hlb2⟩ := hgs g0 hg0
  obtain ⟨y, hy, rfl⟩ : ∃ y, InS I (c.sortName b) y ∧ ys = [y] := by
    cases hys with
    | cons hy hr => cases hr; exact ⟨_, hy, rfl⟩
  have hbmem' : Gen.inj b ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := hbmem
  obtain ⟨y1, -, hy1⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem hN' hbmem' rfl, rfl⟩)) (xs := [y]) rfl
    (single_sorts hy)
  have hy1 : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔ m = y1 := hy1
  have hset_b : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔ m = y0 := fun m => by
    rw [hy1 m, ← (hy1 _).mp hgs']
  have hseq : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [x] m ↔
      GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m := fun m => by rw [hset_a, hset_b]
  have hne : Gen.inj a ≠ Gen.inj b := fun h => hba (by cases h; rfl)
  rcases mem_pairs_of hne hamem' hbmem' with hp | hp
  · rcases injPair_mem hN' hp hle with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [_]) (ys := [y]) rfl rfl
        (single_sorts hx) (single_sorts hy) hseq
    · exact hl hlb1
  · rcases injPair_mem hN' hp (by rw [Bool.or_comm]; exact hle) with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [y]) (ys := [_]) rfl rfl
        (single_sorts hy) (single_sorts hx) (fun m => (hseq m).symm)
    · exact hl hlb2

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The no-junk sentence without injections from empty sorts is a consequence.** In a model of
definedness, the no-junk item of the sort N over the generators `gs'` entails the one over `gs`
where each generator of `gs'` is one of `gs` or an injection from a sort without an element there:
every element of N is a generator of `gs'` applied to elements of its argument sorts, and an
injection from a sort without an element builds none. -/
theorem noJunkItem_of_omitEmpty (hD : KoreAML.DefOK I) {N : String} {gs gs' : List KoreAML.Gen}
    (hsub : ∀ g ∈ gs', g ∈ gs ∨ ∃ b, g = .inj b ∧ ¬ ∃ y, InS I b y)
    (h : I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs').pat) :
    I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs).pat := by
  let X := Kore.Pattern.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs)
  let t := KoreAML.tableOf [] X
  have hfree : KoreAML.freeOf [] X = [] := by
    show KoreAML.freeOf [] (.or _ _) = []
    rw [KoreAML.freeOf]
    exact freeOfList_nil fun p hp => by
      rcases noJunkDisjuncts_cases N [] gs p hp with rfl | ⟨g, -, bs, body, rfl, -, -, hb, -⟩
      · rw [KoreAML.freeOf]
      · exact nj_freeOf_existsAll bs [] fun B _ hB => hb B hB
  intro e m
  show (KoreAML.conjList ((([] : List KoreAML.VarKey) ++ KoreAML.freeOf [] X).eraseDups.map (KoreAML.guardOf t)) ⇒
    (KoreAML.tr ⟨t, []⟩ X ≡ KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N)))).interpret I e m
  rw [interpret_impl]
  intro _
  rw [KoreAML.interp_equal hD]
  intro a
  show (KoreAML.tr ⟨t, []⟩ (.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs))).interpret I e a ↔ _
  rw [KoreAML.tr]
  constructor
  · exact tieOr_inh (ctx := ⟨t, []⟩) (tieNoJunk_last N [] gs)
  · intro ha
    have hx : InS I N a := by rw [trSort_srt] at ha; exact (inS_iff _).mp ha
    obtain ⟨g, hg', xs, hxs, a0, ha0, happ⟩ := noJunk_elim hD h hx
    have hg : g ∈ gs := by
      rcases hsub g hg' with hg | ⟨b, rfl, hb⟩
      · exact hg
      · cases hxs with
        | cons hy _ => exact absurd ⟨_, hy⟩ hb
    obtain ⟨bs, body, hmem, hsorts, hnd, htr⟩ := Model.noJunkDisjuncts_gen N [] gs g hg
    have hkt : ∀ b ∈ bs, KoreAML.evarKey b ∈ t := fun b hb => List.mem_eraseDups.mpr (List.mem_append_right _ (by
      show KoreAML.evarKey b ∈ KoreAML.varsOf (.or _ _)
      rw [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOfList hmem (Model.varsOf_existsAll' hb))))
    have hidx : (bs.map fun b => t.ev (KoreAML.evarKey b)).Nodup := by
      rw [show (bs.map fun b => t.ev (KoreAML.evarKey b)) = (bs.map KoreAML.evarKey).map t.ev by rw [List.map_map]; rfl]
      refine Model.nodup_map_of_injOn t.ev (fun k hk k' hk' he => ?_) hnd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hk'
      exact ev_inj (hkt b hb) (hkt b' hb') he
    refine tieOr_intro hmem ha (tieExistsAll_intro hD bs g.argSorts xs e hidx hsorts hxs fun e' _ _ hall => ?_)
    rw [htr t, genPat_eq, interp_appList]
    exact ⟨a0, (genHead_val0 N g e' a0).mpr ha0, xs, tieAll2_evars hall, happ⟩

end

/-! ## KItem's no-junk sentence over its generators but the injections from a list of sorts -/

/-- KItem's generators in kompile's order (`gensInOrder`) but the injections from the sorts `xs`. -/
def kitemOmitGens (c : Semantics) (p : Presentation) (xs : List Srt) : List Gen :=
  (gensInOrder c p Srt.kitem).filter fun g => match g with
    | .inj b => !xs.contains b
    | .ctor _ => true

/-- `inj{b, KItem}` is a generator of KItem (`Semantics.gens`). -/
def kitemOmitGenB (c : Semantics) (b : Srt) : Bool :=
  (c.gens Srt.kitem).any fun g => match g with
    | .inj b' => b' == b
    | .ctor _ => false

/-- What the lemmas below ask of the sorts `xs` a KItem no-junk sentence leaves out and of the
generators `gs` it lists, decided: `xs` is not empty; for each x of `xs`, `inj{x, KItem}` is a
generator of KItem that is not open, and each generator of `gs` is an injection `inj{b, KItem}`, a
generator of KItem that is not open, from a sort b other than x, incomparable with x and with no
lower bound in common with it; and each generator of KItem is an injection from a sort of `xs` or
one of `gs`. -/
def kitemOmitB (c : Semantics) (xs : List Srt) (gs : List Gen) : Bool :=
  !xs.isEmpty &&
  xs.all (fun x => kitemOmitGenB c x && !c.isOpenGen (.inj x) &&
    gs.all fun g => match g with
      | .inj b => kitemOmitGenB c b && !c.isOpenGen (.inj b) && b != x && !(c.le x b || c.le b x) &&
          (c.lowerBounds x b).isEmpty && (c.lowerBounds b x).isEmpty
      | .ctor _ => false) &&
  (c.gens Srt.kitem).all fun g => match g with
    | .inj b => xs.contains b || gs.any fun g' => match g' with
      | .inj b' => b' == b
      | .ctor _ => false
    | .ctor _ => false

theorem kitemOmit_gen_mem {c : Semantics} {b : Srt} (h : kitemOmitGenB c b = true) :
    Gen.inj b ∈ c.gens Srt.kitem := by
  obtain ⟨g, hg, hm⟩ := List.any_eq_true.mp h
  cases g with
  | ctor _ => cases hm
  | inj b' => rw [← (beq_iff_eq.mp hm)]; exact hg

/-- The parts of `kitemOmitB`. -/
theorem kitemOmit_parts {c : Semantics} {xs : List Srt} {gs : List Gen} (h : kitemOmitB c xs gs = true) :
    xs ≠ [] ∧
    (∀ x ∈ xs, Gen.inj x ∈ (c.gens Srt.kitem).filter (!c.isOpenGen ·) ∧
      ∀ g ∈ gs, ∃ b, g = .inj b ∧ Gen.inj b ∈ (c.gens Srt.kitem).filter (!c.isOpenGen ·) ∧ b ≠ x ∧
        (c.le x b || c.le b x) = false ∧ c.lowerBounds x b = [] ∧ c.lowerBounds b x = []) ∧
    (∀ g ∈ c.gens Srt.kitem, ∃ b, g = .inj b ∧ (b ∈ xs ∨ Gen.inj b ∈ gs)) := by
  simp only [kitemOmitB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hne, hxs⟩, hgen⟩ := h
  refine ⟨hne, fun x hx => ?_, fun g hg => ?_⟩
  · have hx' := List.all_eq_true.mp hxs x hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx'
    obtain ⟨⟨hxg, hxo⟩, hgs⟩ := hx'
    refine ⟨List.mem_filter.mpr ⟨kitemOmit_gen_mem hxg, by rw [hxo]; rfl⟩, fun g hg => ?_⟩
    have hap := List.all_eq_true.mp hgs g hg
    cases g with
    | ctor k => cases hap
    | inj b =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.isEmpty_iff] at hap
      obtain ⟨⟨⟨⟨⟨hbm, hbo⟩, hbt⟩, hle⟩, hlb1⟩, hlb2⟩ := hap
      exact ⟨b, rfl, List.mem_filter.mpr ⟨kitemOmit_gen_mem hbm, by rw [hbo]; rfl⟩, hbt, hle, hlb1, hlb2⟩
  · have hg' := List.all_eq_true.mp hgen g hg
    cases g with
    | ctor k => cases hg'
    | inj b =>
      refine ⟨b, rfl, ?_⟩
      simp only [Bool.or_eq_true, List.contains_iff_mem] at hg'
      rcases hg' with hb | hb
      · exact .inl hb
      · obtain ⟨g', hg'm, hm⟩ := List.any_eq_true.mp hb
        cases g' with
        | ctor _ => cases hm
        | inj b' => rw [← (beq_iff_eq.mp hm)]; exact .inr hg'm

/-- **The sentence entails `Γ`'s item, in every interpretation with definedness.** KItem's no-junk
sentence over `gs` entails the no-junk item of KItem over all its generators (`noJunkItem_of_subset`:
each generator of `gs` is one of KItem's). -/
theorem kitemOmit_entails_item {c : Semantics} {xs : List Srt} {gs : List Gen} (hok : kitemOmitB c xs gs = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I)
    (h : I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gs.map (Gen.toK c))).pat) :
    I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c))).pat := by
  obtain ⟨hne, hx, -⟩ := kitemOmit_parts hok
  obtain ⟨x, xs', rfl⟩ := List.exists_cons_of_ne_nil hne
  refine noJunkItem_of_subset hD (fun g hg => ?_) h
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨b, rfl, hb, -⟩ := (hx x (List.mem_cons_self ..)).2 g0 hg0
  exact List.mem_map.mpr ⟨_, (List.mem_filter.mp hb).1, rfl⟩

/-- That item is `Γ`'s, for every H. -/
theorem kitemOmit_item_in_gamma {c : Semantics} {xs : List Srt} {gs : List Gen} (hok : kitemOmitB c xs gs = true)
    (hN : Srt.kitem ∈ consSorts c) (H : HookParams) :
    KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c)) ∈
      consItemsK (c.withHooks H) := by
  obtain ⟨hne, hx, -⟩ := kitemOmit_parts hok
  obtain ⟨x, xs', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hmem := (List.mem_filter.mp (hx x (List.mem_cons_self ..)).1).1
  have hg : (c.gens Srt.kitem).isEmpty = false := by
    cases h : c.gens Srt.kitem with
    | nil => rw [h] at hmem; cases hmem
    | cons _ _ => rfl
  exact noJunkItem_mem (c := c.withHooks H) (N := Srt.kitem) hN hg

/-- **In a model of `Γ`, KItem's no-junk sentence over `gs` holds exactly where no sort of `xs` has
an element**, for every H. Where some x of `xs` has an element, `noJunk_omitted_refuted_elem`
refutes the sentence. Where none has, `Γ`'s no-junk item of KItem gives each element of KItem a
generator of KItem applied to elements of its argument sorts; an injection from a sort of `xs`
builds none, so it is one of `gs` (`noJunkItem_of_omitEmpty`). -/
theorem kitemOmit_holds_iff_empty {c : Semantics} {xs : List Srt} {gs : List Gen} (hok : kitemOmitB c xs gs = true)
    (hN : Srt.kitem ∈ consSorts c) (hno : c.fnOvlSyms = []) (H : HookParams)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (c.withHooks H)) :
    (I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gs.map (Gen.toK c))).pat) ↔
      ∀ x ∈ xs, ¬ ∃ y, InS I (c.sortName x) y := by
  obtain ⟨-, hx, hgen⟩ := kitemOmit_parts hok
  constructor
  · rintro h x hxs ⟨y, hy⟩
    exact noJunk_omitted_refuted_elem H hN hno (hx x hxs).1 (hx x hxs).2 hI hy h
  · intro hemp
    have hitem := sat_cons hI (Or.inl ⟨_, kitemOmit_item_in_gamma hok hN H, rfl⟩)
    refine noJunkItem_of_omitEmpty (defOK hI) (fun g hg => ?_) hitem
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨b, rfl, hb | hb⟩ := hgen g0 hg0
    · exact .inr ⟨c.sortName b, rfl, hemp b hb⟩
    · exact .inl (List.mem_map.mpr ⟨_, hb, rfl⟩)

/-- **Where a sort of `xs` has a value the reader exhibits, `Γ` with KItem's no-junk sentence over
`gs` has no model**, for every H: the value's element is an element of that sort in every model of
`Γ` (`inhabited_of_exhibit_withHooks`), at which the sentence fails (`kitemOmit_holds_iff_empty`). -/
theorem kitemOmit_refuted_exhibit {c : Semantics} {xs : List Srt} {gs : List Gen} (hok : kitemOmitB c xs gs = true)
    (hN : Srt.kitem ∈ consSorts c) (hno : c.fnOvlSyms = []) (H : HookParams) {x : Srt} (hx : x ∈ xs)
    {v : GroundTerm} (hv : Parse.exhibit? c x = some v)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (c.withHooks H)) :
    ¬ (I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gs.map (Gen.toK c))).pat) := by
  intro h
  obtain ⟨y, hy⟩ := inhabited_of_exhibit_withHooks H hI hv KoreAML.val0
  exact (kitemOmit_holds_iff_empty hok hN hno H hI).mp h x hx ⟨y, (inS_iff _).mp hy⟩

/-- **No model of `Γ` satisfies KItem's no-junk sentence over `gs` together with the G-nonempty item
of a sort of `xs`**, for every H: that item gives the sort an element (`KoreAML.nonempty_of`), at
which the sentence fails (`kitemOmit_holds_iff_empty`). -/
theorem kitemOmit_refuted_nonempty {c : Semantics} {xs : List Srt} {gs : List Gen} (hok : kitemOmitB c xs gs = true)
    (hN : Srt.kitem ∈ consSorts c) (hno : c.fnOvlSyms = []) (H : HookParams) {x : Srt} (hx : x ∈ xs) {b : Bool}
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (c.withHooks H))
    (hne : I ⊧ᴵ (KoreAML.nonemptyItem ⟨"Sort" ++ c.sortName x, [], b⟩).pat) :
    ¬ (I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gs.map (Gen.toK c))).pat) := by
  intro h
  obtain ⟨y, hy⟩ := KoreAML.nonempty_of (defOK hI) hne (e := KoreAML.val0)
  exact (kitemOmit_holds_iff_empty hok hN hno H hI).mp h x hx ⟨y, hy⟩

end Faithful

end KCore
