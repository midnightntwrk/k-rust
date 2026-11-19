/-
  KCore. The sorts the closure axiom (`Γcl`, Faithful.lean) and the constructors confine.

  - `boolValues`: where Bool holds only its literals (`litSort`), its values are `true` and
    `false`; `boolClosed_model`: the value model satisfies `boolClosed`.
  - `confined_value`: in every model of `Γc`, every element of a confined sort is a value's
    element. Bool by `boolClosed`; a constructor sort by the text's no-junk sentence, read in the
    model (`noJunk_elim`): each element is a generator applied to elements of the generator's
    argument sorts, each a value's element at a smaller depth.
-/
import KcoreSpec.FaithfulFamilies

set_option autoImplicit false

namespace KCore

open ML Faithful

theorem sortOf_map_sort {c : Semantics} {s t : Srt} {es : List (GroundTerm × GroundTerm)}
    (h : c.sortOf (.map s es) = some t) : t = s ∧ (c.collOf s).isSome = true := by
  obtain ⟨_, _, hk, _, _, _, rfl⟩ := c.sortOf_map_inv h
  exact ⟨rfl, by rw [hk]; rfl⟩

theorem sortOf_set_sort {c : Semantics} {s t : Srt} {es : List GroundTerm}
    (h : c.sortOf (.set s es) = some t) : t = s ∧ (c.collOf s).isSome = true := by
  unfold Semantics.sortOf at h
  split at h
  · rename_i k ss hk _
    split at h
    · exact ⟨(Option.some.inj h).symm, by rw [hk]; rfl⟩
    · cases h
  · cases h

theorem sortOf_list_sort {c : Semantics} {s t : Srt} {es : List GroundTerm}
    (h : c.sortOf (.list s es) = some t) : t = s ∧ (c.collOf s).isSome = true := by
  unfold Semantics.sortOf at h
  split at h
  · rename_i k ss hk _
    split at h
    · exact ⟨(Option.some.inj h).symm, by rw [hk]; rfl⟩
    · cases h
  · cases h

/-- **In a definition where Bool holds only literals, its values are the two literals.** -/
theorem boolValues {c : Semantics} (h : c.coreOK = true) (hl : c.litSort Srt.bool = true)
    {v : GroundTerm} (hv : c.sortOf v = some Srt.bool) : ∃ b, v = .dv Srt.bool (.bool b) := by
  have _ := h
  simp only [Semantics.litSort, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨hct, hov⟩, hsub⟩, hpr⟩, hcoll⟩, htok⟩, hbyte⟩, -⟩ := hl
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, -, hs⟩ | ⟨-, o, ho, -, -, hs⟩ | ⟨-, -, k, hk, -, -, hs⟩
    · exact absurd hs.symm (hct k (lookupSig_spec hk).1)
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec ho
      exact absurd hs.symm (hov o.sig (List.mem_map.mpr ⟨o, he ▸ List.getElem_mem hi, rfl⟩))
    · obtain ⟨hm, hraw, -, -⟩ := c.lookupOpen_spec hk
      have := hpr k hm
      simp [hraw, ← hs] at this
  | inj a b t =>
    obtain ⟨hab, -, -, rfl⟩ := OvlLaws.sortOf_inj_iff.mp hv
    exact (hsub _ hab rfl).elim
  | dv s lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hv
    cases lit with
    | bool b => exact ⟨b, rfl⟩
    | int _ => simp only [dvOK, Lib.carrier_bool, beq_iff_eq] at hok; exact absurd hok (by decide)
    | float _ _ _ => simp only [dvOK, Lib.carrier_bool, Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
    | tok t =>
      simp only [dvOK, Lib.carrier_bool, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ((hk | hk) | hk) | ⟨hk, -⟩
      · cases hk
      · cases hk
      · exact absurd hk (by simpa using htok)
      · rcases hk with hk | hk
        · cases hk
        · exact absurd hk (by simpa using hbyte)
  | map s es => obtain ⟨rfl, hk⟩ := sortOf_map_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk
  | set s es => obtain ⟨rfl, hk⟩ := sortOf_set_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk
  | list s es => obtain ⟨rfl, hk⟩ := sortOf_list_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk

namespace Faithful.Model.AtT

variable {T : GroundTerm → GroundTerm → Prop}

open Faithful.Model in
/-- **The value model satisfies the closure axiom** where Bool holds only literals: its elements of
Bool are the values of Bool, `true` and `false` (`boolValues`). -/
theorem boolClosed_model {c : Semantics} (h : HypModelCore c) (hc : c.coreOK = true)
    (hl : c.litSort Srt.bool = true) : stdI_T c T ⊧ᴵ boolClosed c := by
  intro e m
  unfold boolClosed
  rw [KoreAML.interp_included defOK_std]
  intro a ha
  have ha' := (inhOf_sort h.namesK (bool_numbered (c := c)) e a).mp ha
  obtain ⟨v, rfl, hv⟩ := inSort_val ha'
  obtain ⟨b, rfl⟩ := boolValues hc hl hv
  have hs := den_val (T := T) h (.dv Srt.bool (.bool b)) hv e
  simp only [Pattern.interpret]
  intro hn
  cases b with
  | true => exact absurd ((hs _).mpr rfl) hn
  | false => exact (hs _).mpr rfl

end Faithful.Model.AtT

open Faithful.Model in
/-- **The value model satisfies the closure axiom** where Bool holds only literals: its elements of
Bool are the values of Bool, `true` and `false` (`boolValues`). -/
theorem boolClosed_model {c : Semantics} (h : HypModelCore c) (hc : c.coreOK = true)
    (hl : c.litSort Srt.bool = true) : stdI c ⊧ᴵ boolClosed c :=
  Faithful.Model.AtT.boolClosed_model (c := c) (T := StepM c) (h := h) (hc := hc) (hl := hl)

/-! ## Confined sorts -/

namespace Faithful

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem genHead_val0 (N : String) (g : KoreAML.Gen) (e : Valuation M) (a : M) :
    (genHead N g).interpret I e a ↔ (genHead N g).interpret I KoreAML.val0 a := by
  cases g with
  | ctor k => exact (KoreAML.Closed.sym _).interp e _ a
  | inj A => exact (KoreAML.Closed.appList (KoreAML.Closed.sym _) (fun ψ hψ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
      rcases hψ with rfl | rfl <;> exact KoreAML.Closed.sym _)).interp e _ a

/-- Elements each of which is a value's element, of the sorts `ss`, are the elements of a list of
values of those sorts. -/
theorem values_of_elems : ∀ (ss : List Srt) (xs : List M), xs.length = ss.length →
    (∀ (j : Nat) x s, xs[j]? = some x → ss[j]? = some s → ∃ w, c.sortOf w = some s ∧ elemOf c I w = x) →
    ∃ ws, c.sortsOf ws = some ss ∧ ws.map (elemOf c I) = xs
  | [], [], _, _ => ⟨[], rfl, rfl⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | s :: ss, x :: xs, hl, h => by
    obtain ⟨w, hw, rfl⟩ := h 0 x s rfl rfl
    obtain ⟨ws, hws, rfl⟩ := values_of_elems ss xs (by simpa using hl)
      (fun j x s h1 h2 => h (j + 1) x s (by simpa using h1) (by simpa using h2))
    exact ⟨w :: ws, OvlLaws.sortsOf_cons_iff.mpr ⟨hw, hws⟩, rfl⟩

theorem all2_map_get {α β γ : Type} {R : α → β → Prop} {f : γ → α} {l : List γ} {xs : List β}
    (h : All2 R (l.map f) xs) {j : Nat} {y : β} (hy : xs[j]? = some y) {b : γ} (hb : l[j]? = some b) :
    R (f b) y :=
  h.get (by rw [List.getElem?_map, hb]; rfl) hy

/-! ### The no-junk sentence in any model -/

omit [Inhabited M] in
theorem freeOfList_nil {B : List KoreAML.VarKey} : ∀ {ps : List Kore.Pattern},
    (∀ p ∈ ps, KoreAML.freeOf B p = []) → KoreAML.freeOfList B ps = []
  | [], _ => by rw [KoreAML.freeOfList]
  | p :: ps, h => by
    rw [KoreAML.freeOfList, h p (List.mem_cons_self ..), freeOfList_nil fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

omit [Inhabited M] in
/-- Variables, each bound, applied as arguments: no free variable. -/
theorem freeOfList_vars {B : List KoreAML.VarKey} : ∀ {xs : List Kore.EVar},
    (∀ b ∈ xs, KoreAML.evarKey b ∈ B) → KoreAML.freeOfList B (KoreAML.vars xs) = []
  | [], _ => by simp only [KoreAML.vars, List.map_nil, KoreAML.freeOfList]
  | x :: xs, h => by
    have ih := freeOfList_vars (B := B) (xs := xs) fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [KoreAML.vars, List.map_cons, Function.comp, KoreAML.freeOfList, KoreAML.freeOf] at ih ⊢
    simp [h x (List.mem_cons_self ..), ih]

omit [Inhabited M] in
/-- `∃b̄. body` has no free variable where the body has none beyond the binders and `bound`. -/
theorem nj_freeOf_existsAll {S : Kore.KSort} {body : Kore.Pattern} : ∀ (bs : List Kore.EVar) (bound : List KoreAML.VarKey),
    (∀ B : List KoreAML.VarKey, (∀ k ∈ bound, k ∈ B) → (∀ b ∈ bs, KoreAML.evarKey b ∈ B) → KoreAML.freeOf B body = []) →
    KoreAML.freeOf bound (KoreAML.existsAll S bs body) = []
  | [], bound, h => h bound (fun _ hk => hk) (fun _ hb => absurd hb List.not_mem_nil)
  | b :: bs, bound, h => by
    show KoreAML.freeOf bound (.exist S b (KoreAML.existsAll S bs body)) = []
    rw [KoreAML.freeOf]
    refine nj_freeOf_existsAll bs _ fun B hB hbs => h B (fun k hk => hB k (List.mem_cons_of_mem _ hk)) fun b' hb' => ?_
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact hB _ (List.mem_cons_self ..)
    · exact hbs b' hb'

omit [Inhabited M] in
/-- The disjuncts of the no-junk sentence: the closing `\bottom`, or the disjunct of a generator,
binders at its argument sorts with distinct keys around the generator applied to them. -/
theorem noJunkDisjuncts_cases (N : String) : ∀ (seen : List (String × List String)) (gs : List KoreAML.Gen)
    (p : Kore.Pattern), p ∈ KoreAML.noJunkDisjuncts N seen gs →
    p = .bottom (KoreAML.srt N) ∨ ∃ g ∈ gs, ∃ (bs : List Kore.EVar) (body : Kore.Pattern),
      p = KoreAML.existsAll (KoreAML.srt N) bs body ∧
      bs.map (·.sort) = g.argSorts.map KoreAML.srt ∧ (bs.map KoreAML.evarKey).Nodup ∧
      (∀ B : List KoreAML.VarKey, (∀ b ∈ bs, KoreAML.evarKey b ∈ B) → KoreAML.freeOf B body = []) ∧
      ∀ t : KoreAML.VarTable, KoreAML.tr ⟨t, []⟩ body =
        KoreAML.Cons.genPat N g (bs.map fun b => .evar (t.ev (KoreAML.evarKey b)))
  | _, [], p, h => Or.inl (List.mem_singleton.mp h)
  | seen, .ctor k :: gs, p, h => by
    let xs := (KoreAML.noJunkVars seen (((List.range k.args.length).map (fun i => "X" ++ toString i)).zip k.args)).1
    have h' : p ∈ KoreAML.existsAll (KoreAML.srt N) xs (KoreAML.ap k.name (KoreAML.vars xs)) ::
        KoreAML.noJunkDisjuncts N (KoreAML.noJunkVars seen
          (((List.range k.args.length).map (fun i => "X" ++ toString i)).zip k.args)).2 gs := h
    rcases List.mem_cons.mp h' with rfl | h'
    · refine Or.inr ⟨.ctor k, List.mem_cons_self .., xs, KoreAML.ap k.name (KoreAML.vars xs), rfl, ?_,
        Model.ctorBinders_nodup seen k.args, fun B hB => ?_, fun t => ?_⟩
      · rw [(Model.noJunkVars_shape seen _).1, ← List.map_map, List.map_snd_zip (by simp)]; rfl
      · rw [KoreAML.ap, KoreAML.freeOf]; exact freeOfList_vars hB
      · rw [KoreAML.ap, KoreAML.tr_app0, trArgs_appList]
        simp only [KoreAML.vars, List.map_map]
        rfl
    · rcases noJunkDisjuncts_cases N _ gs p h' with h' | ⟨g, hg, r⟩
      · exact Or.inl h'
      · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, r⟩
  | seen, .inj a :: gs, p, h => by
    let x := KoreAML.evar (KoreAML.noJunkName seen "Val" a).1 (KoreAML.srt a)
    have h' : p ∈ Kore.Pattern.exist (KoreAML.srt N) x (KoreAML.injP a N (.var (.evar x))) ::
        KoreAML.noJunkDisjuncts N (KoreAML.noJunkName seen "Val" a).2 gs := h
    rcases List.mem_cons.mp h' with rfl | h'
    · refine Or.inr ⟨.inj a, List.mem_cons_self .., [x], KoreAML.injP a N (.var (.evar x)), rfl, rfl,
        by simp, fun B hB => ?_, fun t => ?_⟩
      · have hx := hB x (List.mem_singleton_self _)
        simp only [KoreAML.injP, KoreAML.freeOf, KoreAML.freeOfList]
        simp [hx]
      · rw [KoreAML.tr_injP]; rfl
    · rcases noJunkDisjuncts_cases N _ gs p h' with h' | ⟨g, hg, r⟩
      · exact Or.inl h'
      · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, r⟩

omit [Inhabited M] in
theorem trOrList_elim {ctx : KoreAML.Ctx} {s : KoreAML.P} {e : Valuation M} {m : M} :
    ∀ {ps : List Kore.Pattern}, ps ≠ [] → (KoreAML.trOrList ctx s ps).interpret I e m →
      ∃ p ∈ ps, (KoreAML.tr ctx p).interpret I e m
  | [], hne, _ => absurd rfl hne
  | [p], _, h => ⟨p, List.mem_singleton_self _, by rw [KoreAML.trOrList] at h; exact h⟩
  | p :: q :: ps, _, h => by
    rw [KoreAML.trOrList, KoreAML.interp_sOr] at h
    rcases h.2 with h | h
    · exact ⟨p, List.mem_cons_self .., h⟩
    · obtain ⟨p', hp', h'⟩ := trOrList_elim (List.cons_ne_nil _ _) h
      exact ⟨p', List.mem_cons_of_mem _ hp', h'⟩

theorem all2_inS_of {t : KoreAML.VarTable} {e' : Valuation M} : ∀ {bs : List Kore.EVar} {ss : List String} {ys : List M},
    bs.map (·.sort) = ss.map KoreAML.srt →
    (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS I n (e'.evalEvar (t.ev (KoreAML.evarKey b)))) →
    All2 (fun (φ : KoreAML.P) y => φ.interpret I e' y) (bs.map fun b => (Pattern.evar (t.ev (KoreAML.evarKey b)) : KoreAML.P)) ys →
    All2 (fun s y => InS I s y) ss ys
  | [], [], _, _, _, hys => by cases hys; exact .nil
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | b :: bs, s :: ss, ys, h, hin, hys => by
    simp only [List.map_cons, List.cons.injEq] at h
    cases hys with
    | cons hy hys =>
      refine .cons ?_ (all2_inS_of h.2 (fun b' hb' => hin b' (List.mem_cons_of_mem _ hb')) hys)
      rw [KoreAML.interp_evar.mp hy]
      exact hin b (List.mem_cons_self ..) s h.1

/-- **The text's no-junk sentence, in any model of it**: where the translation of
`\or{N}(∃x̄. g(x̄), …, \bottom{N}())` is the whole of the sort N, every element of N is a generator
of N applied to elements of the generator's argument sorts. -/
theorem noJunk_elim (hD : KoreAML.DefOK I) {N : String} {gs : List KoreAML.Gen}
    (h : I ⊧ᴵ (KoreAML.Cons.noJunkItem N gs).pat) {x : M} (hx : InS I N x) :
    ∃ g ∈ gs, ∃ xs, All2 (fun s y => InS I s y) g.argSorts xs ∧ GS I N g xs x := by
  let X := Kore.Pattern.or (KoreAML.srt N) (KoreAML.noJunkDisjuncts N [] gs)
  let t := KoreAML.tableOf [] X
  have hfree : KoreAML.freeOf [] X = [] := by
    show KoreAML.freeOf [] (.or _ _) = []
    rw [KoreAML.freeOf]
    exact freeOfList_nil fun p hp => by
      rcases noJunkDisjuncts_cases N [] gs p hp with rfl | ⟨g, -, bs, body, rfl, -, -, hb, -⟩
      · rw [KoreAML.freeOf]
      · exact nj_freeOf_existsAll bs [] fun B _ hB => hb B hB
  have hX := (KoreAML.trAxiom_at hD (ds := []) (al := []) (ad := ⟨0, "kernel", KoreAML.Cons.noJunkAx N gs⟩)
    h KoreAML.val0 (fun k hk => by
      change k ∈ (([] : List KoreAML.VarKey) ++ KoreAML.freeOf [] X).eraseDups at hk
      rw [hfree, List.nil_append, List.mem_eraseDups] at hk
      exact absurd hk List.not_mem_nil) x).mpr (by
    change (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N))).interpret I KoreAML.val0 x
    rw [trSort_srt]
    exact hx)
  change (KoreAML.tr ⟨t, []⟩ (.or (KoreAML.srt N) _)).interpret I KoreAML.val0 x at hX
  rw [KoreAML.tr] at hX
  obtain ⟨p, hp, hpx⟩ := trOrList_elim (Model.noJunkDisjuncts_ne_nil N [] gs) hX
  rcases noJunkDisjuncts_cases N [] gs p hp with rfl | ⟨g, hg, bs, body, rfl, hsorts, hnd, -, htr⟩
  · rw [KoreAML.tr] at hpx
    unfold KoreAML.sBot at hpx
    rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD (by rw [trSort_srt]; rfl)] at hpx
    exact absurd hpx.2 hpx.1
  have hkt : ∀ b ∈ bs, KoreAML.evarKey b ∈ t := fun b hb => List.mem_eraseDups.mpr (List.mem_append_right _ (by
    show KoreAML.evarKey b ∈ KoreAML.varsOf (.or _ _)
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ (mem_varsOfList hp (Model.varsOf_existsAll' hb))))
  have hidx : (bs.map fun b => t.ev (KoreAML.evarKey b)).Nodup := by
    rw [show (bs.map fun b => t.ev (KoreAML.evarKey b)) = (bs.map KoreAML.evarKey).map t.ev by rw [List.map_map]; rfl]
    refine Model.nodup_map_of_injOn t.ev (fun k hk k' hk' he => ?_) hnd
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hk'
    exact ev_inj (hkt b hb) (hkt b' hb') he
  have hsrt : ∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    have : b.sort ∈ g.argSorts.map KoreAML.srt := hsorts ▸ List.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨n, -, hn⟩ := List.mem_map.mp this
    exact ⟨n, hn.symm⟩
  obtain ⟨e', -, hin, hb⟩ := existsAll_elim hD bs KoreAML.val0 x hidx hsrt hpx
  rw [htr t, genPat_eq, interp_appList] at hb
  obtain ⟨a, ha, ys, hys, happ⟩ := hb
  exact ⟨g, hg, ys, all2_inS_of hsorts hin hys, a, (genHead_val0 N g e' a).mp ha, happ⟩

/-- A constructor or an overloading symbol's signature is the one its name finds
(`KnownSig`): names are the kernel's symbols' own (`NamesApartK`). -/
theorem knownSig_of_mem (hn : Model.NamesApartK c) {k : CtorSig} (hk : k ∈ c.ctorSigs ++ c.ovlSigs) :
    OvlLaws.KnownSig c k := by
  have kern : ∀ x, x ∈ c.ctorSigs ++ c.ovlSigs → x ∈ kernelSyms c := fun x hx => by
    unfold kernelSyms
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx)))
    · exact List.mem_append_right _ hx
  unfold OvlLaws.KnownSig
  rw [lookupSig_eq]
  cases hf : (c.ctorSigs ++ c.ovlSigs).find? (·.name == k.name) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (hf k hk) (by simp)
  | some k' =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 : k'.name = k.name := by simpa using List.find?_some hf
    rw [hn.1 k' (kern _ h1) k (kern _ hk) (by rw [h2])]

/-- A generator that passes `confinedAt`'s text on overloads ("no overloading symbol of its name
overloads a function") is not function-overloaded. -/
theorem not_fnOvl_of_confinedGen {c : Semantics} {g : Gen}
    (h : (match g with
      | .ctor kg => c.ovls.all fun o => o.sig.name != kg.name || o.over.all fun f => c.fns.all (·.label != f)
      | .inj _ => true) = true) {k : CtorSig} (hg : g = .ctor k) : k.name ∉ c.fnOvlSyms := by
  subst hg
  intro hmem
  unfold Semantics.fnOvlSyms at hmem
  obtain ⟨o, ho, hname⟩ := List.mem_map.mp hmem
  obtain ⟨hom, hany⟩ := List.mem_filter.mp ho
  obtain ⟨f, hf, hfn⟩ := List.any_eq_true.mp hany
  obtain ⟨fn, hfnm, hlab⟩ := List.any_eq_true.mp hfn
  have ho' := List.all_eq_true.mp h o hom
  rw [hname] at ho'
  simp only [bne_self_eq_false, Bool.false_or] at ho'
  have := List.all_eq_true.mp (List.all_eq_true.mp ho' f hf) fn hfnm
  rw [bne_iff_ne] at this
  exact this (by simpa using hlab)

/-- No function overload covers any arguments of such a generator. -/
theorem fnCover_none_of_confinedGen {c : Semantics} {g : Gen}
    (h : (match g with
      | .ctor kg => c.ovls.all fun o => o.sig.name != kg.name || o.over.all fun f => c.fns.all (·.label != f)
      | .inj _ => true) = true) (ws : List GroundTerm) :
    ∀ k : CtorSig, g = .ctor k → c.fnCover k.name ws = none :=
  fun _ hg => OvlLaws.fnCover_none_of_not_fnOvl (not_fnOvl_of_confinedGen h hg) ws

variable (hI : I ⊧ᴵP Γ c) [hO : OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI htr

/-- **A generator applied to values' elements builds a value's element**, at arguments no function
overload of the generator covers (`hnf`: covered, the application is a function's value, which
need not be a value's): a constructor or an
overloading symbol the element of the normal form of the application (`norm_gs`), an injection
the element of the injected value (through Cons-Coh where the argument is itself an injection),
an open generator the element of its parameter graph's value (`ΓDomains`), none where the graph
has no value. `ΓDomains` writes that graph at the head `symApp` applies and the no-junk sentence at
the generator's own head; the two are one symbol where the decoder reads the generator's name as no instance
(`hite`). -/
theorem gen_value (hn : Model.NamesApartK c)
    (hite : ∀ k ∈ c.params, k.raw = true → instDecode? (c.symName k.sig.name) = none)
    {N : Srt} {g : Gen} (hgm : g ∈ c.gens N) {ws : List GroundTerm}
    (hws : c.sortsOf ws = some g.argSorts)
    (hnf : ∀ k : CtorSig, g = .ctor k → c.fnCover k.name ws = none) {m : M}
    (hm : GS I (c.sortName N) (Gen.toK c g) (ws.map (elemOf c I)) m) :
    ∃ v, c.sortOf v = some N ∧ elemOf c I v = m := by
  have sig : ∀ k : CtorSig, k ∈ c.ctorSigs ++ c.ovlSigs → k.result = N → g = .ctor k →
      ∃ v, c.sortOf v = some N ∧ elemOf c I v = m := by
    intro k hk hkr hg
    subst hg hkr
    have hks := knownSig_of_mem hn hk
    have hr := OvlLaws.ovlRank_le (c := c) k.name
    have hnf := hnf k rfl
    refine ⟨c.norm k.name ws, OvlLaws.sortOf_norm_known_ovlF (hO.hyp htr) (hO.hyp htr).fnFacts _ k hks hr ws hws hnf, ?_⟩
    exact ((norm_gs hI htr _ k hks hr ws hws hnf m).mp hm).symm
  rcases Model.mem_gens hgm with ⟨k, hk, hkr, rfl⟩ | ⟨o, ho, hor, rfl⟩ | ⟨a, hab, rfl⟩ | ⟨k, hk, hkr, hres, rfl⟩
  · exact sig k (List.mem_append_left _ hk) hkr rfl
  · exact sig o.sig (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩)) hor rfl
  rotate_left
  · -- an open generator k: its application is the parameter graph's value, or nothing
    subst hres
    have hd : (den c (.ctor k.sig.name ws)).interpret I KoreAML.val0 m :=
      (den_sig_gs hI (k := k.sig) rfl hws KoreAML.val0 m).mpr hm
    have hsa : KoreAML.den (symApp c k.sig.name (GroundTerm.koreList c ws)) = den c (.ctor k.sig.name ws) := by
      rw [symApp_noInst (hite k hk hkr)]; rfl
    have hax := sat_dom hI (Or.inr (Or.inl ⟨k, ws, hk, hws, rfl⟩))
    have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax KoreAML.val0 default) m
    rw [hsa] at hgr
    have h2 := hgr.mp hd
    cases hp : c.paramVal k.sig.name ws with
    | none => rw [hp] at h2; simp [Pattern.interpret] at h2
    | some v =>
      rw [hp] at h2
      obtain ⟨k', hk', hv⟩ := c.paramVal_sorted hp
      rw [Semantics.lookupParam_eq] at hk'
      have hk'm := List.mem_of_find?_eq_some hk'
      have hk'n : k'.sig.name = k.sig.name := by simpa using List.find?_some hk'
      have he : k'.sig = k.sig := hn.1 _ (kernel_param hk'm) _ (kernel_param hk) (by rw [hk'n])
      rw [he] at hv
      exact ⟨v, hv, (((elemOf_spec hI hv KoreAML.val0).1 m).mp h2).symm⟩
  · -- an injection from a subsort a
    obtain ⟨w, rfl, hw⟩ : ∃ w, ws = [w] ∧ c.sortOf w = some a := by
      cases ws with
      | nil => rw [show c.sortsOf [] = some [] from rfl] at hws; cases hws
      | cons w ws' =>
        obtain ⟨hw, hws'⟩ := OvlLaws.sortsOf_cons_iff.mp hws
        exact ⟨w, by rw [sortsOf_nil_eq hws'], hw⟩
    change GS I (c.sortName N) (.inj (c.sortName a)) [elemOf c I w] m at hm
    cases hni : w.isInj with
    | false =>
      have hv : c.sortOf (.inj a N w) = some N := OvlLaws.sortOf_inj_iff.mpr ⟨hab, hni, hw, rfl⟩
      exact ⟨_, hv, (((elemOf_spec hI hv KoreAML.val0).1 m).mp ((den_inj_gs hI hw KoreAML.val0 m).mpr hm)).symm⟩
    | true =>
      cases w with
      | inj a0 a' w0 =>
        obtain ⟨h1, hni0, hw0, rfl⟩ := OvlLaws.sortOf_inj_iff.mp hw
        have hx0 : InS I (c.sortName a0) (elemOf c I w0) := (inS_iff _).mp (elemOf_spec hI hw0 KoreAML.val0).2
        have hy : ∀ m, GS I (c.sortName a) (.inj (c.sortName a0)) [elemOf c I w0] m ↔ m = elemOf c I (.inj a0 a w0) :=
          fun m => by rw [← den_inj_gs hI hw0 KoreAML.val0 m]; exact (elemOf_spec hI hw KoreAML.val0).1 m
        have hm0 := (coh_gs hI h1 hab hx0 hy m).mp hm
        have hv : c.sortOf (.inj a0 N w0) = some N := OvlLaws.sortOf_inj_iff.mpr ⟨htr _ _ _ h1 hab, hni0, hw0, rfl⟩
        exact ⟨_, hv, (((elemOf_spec hI hv KoreAML.val0).1 m).mp ((den_inj_gs hI hw0 KoreAML.val0 m).mpr hm0)).symm⟩
      | _ => simp [GroundTerm.isInj] at hni

omit hI hO htr [Inhabited M] in
theorem noJunkItem_mem {N : Srt} (hN : N ∈ consSorts c) (hg : (c.gens N).isEmpty = false) :
    KoreAML.Cons.noJunkItem (c.sortName N) ((c.gens N).map (Gen.toK c)) ∈ consItemsK c := by
  unfold consItemsK
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨N, hN, List.mem_append_right _ (by simp only [hg]; exact List.mem_singleton_self _)⟩)))

omit hI in
/-- **Every element of a sort confined at depth k is a value's**, in a model of `Γc` of a definition
that reads a confined sort: at depth 0 Bool, by `boolClosed`; deeper, a constructor sort, whose
no-junk sentence makes each element a generator applied to elements of its argument sorts
(`noJunk_elim`); those are values' elements by the depth below, and the generator applied to
values' elements is a value's element (`gen_value`: no function overload covers the arguments,
because a confined sort's generator overloads no function, `fnCover_none_of_confinedGen`). From the
subsorts' transitivity, `OvlOK` and `NamesApartK`, and that the decoder reads no open generator's name as an instance
(`hite`, which `gen_value` reads). -/
theorem confinedAt_valueCl (hn : Model.NamesApartK c)
    (hite : ∀ k ∈ c.params, k.raw = true → instDecode? (c.symName k.sig.name) = none)
    (hr : c.readsConfined = true) (hI : I ⊧ᴵP Γc c) :
    ∀ (k : Nat) (s : Srt), c.confinedAt k s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hD := defOK hIΓ
  have base : ∀ s, c.confinedAt 0 s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := by
    intro s hs x hx
    simp only [Semantics.confinedAt, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨rfl, hl⟩ := hs
    have hb := hI (boolClosed c) (Or.inr ⟨hr, hl, rfl⟩) KoreAML.val0 x
    unfold boolClosed at hb
    rw [KoreAML.interp_included hD] at hb
    have hx' := hb x hx
    have ht : c.sortOf (.dv Srt.bool (.bool true)) = some Srt.bool := sortOf_dv.mpr ⟨rfl, rfl⟩
    have hf : c.sortOf (.dv Srt.bool (.bool false)) = some Srt.bool := sortOf_dv.mpr ⟨rfl, rfl⟩
    by_cases h1 : (den c (.dv Srt.bool (.bool true))).interpret I KoreAML.val0 x
    · exact ⟨_, ht, (((elemOf_spec hIΓ ht _).1 x).mp h1).symm⟩
    · simp only [Pattern.interpret] at hx'
      exact ⟨_, hf, (((elemOf_spec hIΓ hf _).1 x).mp (hx' h1)).symm⟩
  intro k
  induction k with
  | zero => exact base
  | succ k ih =>
    intro s hs x hx
    rw [Semantics.confinedAt.eq_2] at hs
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hs
    rcases hs with hs | ⟨⟨hN, hne⟩, hgs⟩
    · exact base s hs x hx
    obtain ⟨g', hg', xs, hxs, hm⟩ := noJunk_elim hD
      (sat_cons hIΓ (Or.inl ⟨_, noJunkItem_mem hN (by simpa using hne), rfl⟩)) hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    rw [toK_argSorts] at hxs
    have hlen := hxs.length
    rw [List.length_map] at hlen
    obtain ⟨ws, hws, rfl⟩ := values_of_elems (c := c) (I := I) g.argSorts xs hlen.symm (fun j y b hy hb =>
      ih b ((hgs g hg).1 b (List.mem_of_getElem? hb)) y (all2_map_get (R := fun s y => InS I s y) hxs hy hb))
    exact gen_value hIΓ htr hn hite hg hws (fnCover_none_of_confinedGen (hgs g hg).2 ws) hm


omit hI hO htr in
/-- `confinedAt_valueCl` for a semantics `coreOK` accepts. -/
theorem confinedAt_value (h : c.coreOK = true) (hr : c.readsConfined = true) (hI : I ⊧ᴵP Γc c) :
    ∀ (k : Nat) (s : Srt), c.confinedAt k s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  exact confinedAt_valueCl (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
    (Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.1)
    (fun k hk hkr => Semantics.raw_noInst_core_irs h hk hkr) hr hI

end

end Faithful

/-- **Every element of a confined sort is a value's**, in every model of `Γc` of a definition that
reads a confined sort (`confinedAt_value` at the depth `confined` reads). -/
theorem confined_value {c : Semantics} (h : c.coreOK = true) (hr : c.readsConfined = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γc c)
    {s : Srt} (hs : c.confined s = true) (ρ : Valuation M) (e : M)
    (he : (KoreAML.inhOf (sortP (c.sortName s))).interpret I ρ e) :
    ∃ v, c.sortOf v = some s ∧ ∀ m, (den c v).interpret I ρ m ↔ m = e := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨v, hv, rfl⟩ := confinedAt_value h hr hI _ s hs e ((inS_iff ρ).mp he)
  exact ⟨v, hv, (elemOf_spec hIΓ hv ρ).1⟩

namespace Faithful

/-- Values of each of the sorts `ss` give a list of values of those sorts. -/
theorem values_of_each {c : Semantics} : ∀ (ss : List Srt), (∀ b ∈ ss, ∃ w, c.sortOf w = some b) →
    ∃ ws, c.sortsOf ws = some ss
  | [], _ => ⟨[], rfl⟩
  | s :: ss, h => by
    obtain ⟨w, hw⟩ := h s (List.mem_cons_self ..)
    obtain ⟨ws, hws⟩ := values_of_each ss fun b hb => h b (List.mem_cons_of_mem _ hb)
    exact ⟨w :: ws, OvlLaws.sortsOf_cons_iff.mpr ⟨hw, hws⟩⟩

/-- A generator of N applied to values of its argument sorts that no function overload of it covers
(`hnf`: covered, the application has a value only where the function has one) gives a value of N: a constructor or
an overloading symbol its normal form, an injection the injected value (or the core of an injected
one, injected into N), an open generator the value the interpretation gives it there (`OpenTotal`:
its application is itself a value only where the interpretation leaves it raw), which has its
result sort (`paramVal_raw_sorted`). -/
theorem gen_hasValue {c : Semantics} [hO : OvlOK c] (hn : Model.NamesApartK c)
    (hopen : ∀ k ∈ c.params, k.raw = true → c.lookupParam k.sig.name = some k ∧ k.impl = none)
    (ht : OpenTotal c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {N : Srt} {g : Gen} (hgm : g ∈ c.gens N) {ws : List GroundTerm} (hws : c.sortsOf ws = some g.argSorts)
    (hnf : ∀ k : CtorSig, g = .ctor k → c.fnCover k.name ws = none) :
    ∃ v, c.sortOf v = some N := by
  have sig : ∀ k : CtorSig, k ∈ c.ctorSigs ++ c.ovlSigs → k.result = N → g = .ctor k →
      ∃ v, c.sortOf v = some N := by
    intro k hk hkr hg
    subst hg hkr
    exact ⟨_, OvlLaws.sortOf_norm_known_ovlF (hO.hyp htr) (hO.hyp htr).fnFacts _ k (knownSig_of_mem hn hk)
      (OvlLaws.ovlRank_le (c := c) k.name) ws hws (hnf k rfl)⟩
  rcases Model.mem_gens hgm with ⟨k, hk, hkr, rfl⟩ | ⟨o, ho, hor, rfl⟩ | ⟨a, hab, rfl⟩ | ⟨k, hk, hkr, hres, rfl⟩
  · exact sig k (List.mem_append_left _ hk) hkr rfl
  · exact sig o.sig (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩)) hor rfl
  rotate_left
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht k hk hkr ws hws)
    exact ⟨v, hres ▸ ((paramVal_raw_sorted (hopen k hk hkr).1 hkr (hopen k hk hkr).2).mp hv).2⟩
  · obtain ⟨w, hw⟩ : ∃ w, c.sortOf w = some a := by
      cases ws with
      | nil => rw [show c.sortsOf [] = some [] from rfl] at hws; cases hws
      | cons w ws' => exact ⟨w, (OvlLaws.sortsOf_cons_iff.mp hws).1⟩
    cases hni : w.isInj with
    | false => exact ⟨_, OvlLaws.sortOf_inj_iff.mpr ⟨hab, hni, hw, rfl⟩⟩
    | true =>
      cases w with
      | inj a0 a' w0 =>
        obtain ⟨h1, hni0, hw0, rfl⟩ := OvlLaws.sortOf_inj_iff.mp hw
        exact ⟨_, OvlLaws.sortOf_inj_iff.mpr ⟨htr _ _ _ h1 hab, hni0, hw0, rfl⟩⟩
      | _ => simp [GroundTerm.isInj] at hni

end Faithful

open Faithful in
/-- **A confined sort has a value**, where the interpretation gives each open generator a value at
every argument list of its sorts (`OpenTotal`; where no parameter is raw, `openTotal_of_plain`). -/
theorem confined_has_value {c : Semantics} (h : c.coreOK = true) {s : Srt}
    (hs : c.confined s = true) (ht : OpenTotal c) : ∃ v, c.sortOf v = some s := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have htr := (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
  have hn : Model.NamesApartK c :=
    Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.1
  have base : ∀ s, c.confinedAt 0 s = true → ∃ v, c.sortOf v = some s := by
    intro s hs
    simp only [Semantics.confinedAt, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨rfl, -⟩ := hs
    exact ⟨.dv Srt.bool (.bool true), sortOf_dv.mpr ⟨rfl, rfl⟩⟩
  suffices hk : ∀ k s, c.confinedAt k s = true → ∃ v, c.sortOf v = some s from hk _ s hs
  intro k
  induction k with
  | zero => exact base
  | succ k ih =>
    intro s hs
    rw [Semantics.confinedAt.eq_2] at hs
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at hs
    rcases hs with hs | ⟨⟨-, hne⟩, hgs⟩
    · exact base s hs
    obtain ⟨g, hg⟩ : ∃ g, g ∈ c.gens s := by
      cases hgl : c.gens s with
      | nil => rw [hgl] at hne; simp at hne
      | cons g _ => exact ⟨g, List.mem_cons_self ..⟩
    obtain ⟨ws, hws⟩ := values_of_each g.argSorts fun b hb => ih b ((hgs g hg).1 b hb)
    exact gen_hasValue hn (fun k hk hkr =>
      ⟨(Semantics.raw_lookup (Semantics.coreOK_parts h).2.2.2.2 hk hkr (Semantics.raw_of_core h hk hkr).2.2.1).1,
        (Semantics.raw_of_core h hk hkr).1⟩) ht htr hg hws
      (fnCover_none_of_confinedGen (hgs g hg).2 ws)

end KCore
