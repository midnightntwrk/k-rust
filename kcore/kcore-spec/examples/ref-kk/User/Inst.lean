/-
  The term kore.k evaluates in place of a term of the object semantics under a substitution.

  `Inst d σ tm t`: `t` is the form `encTerm d tm` gives `tm`, with each variable `i` replaced by
  `enc (σ i)`. The replacement is `instF` (User.HelpTerms) over `bindOfSubst σ`, the binding whose
  entry for `i` is the encoding of `σ`'s value of `i`: `lookF i (bindOfSubst σ)` is
  `(σ.lookup i).map enc` (`lookF_bindOfSubst_eq_kin`). It has no value at a variable `σ` does not
  bind, and none at a form with no equation of kore.k's `inst` (an alias), so where `Inst` holds,
  `t` is the whole instance.

  `inst_Inst`: where kore.k's `inst` over a binding `B` gives `t` at `tm`'s form, and `B`
  represents `σ` on `varOccs tm` (what `B` gives each variable of `tm` is the encoding of what `σ`
  gives it), `Inst d σ tm t`. `instF` reads a binding only at the form's variables, and from a
  binding that gives each of them the same entry it gives the same result (`instF_mono_kin`); the
  form's variables are the term's (`encTerm_among_kin`).
-/
import User.HelpTerms
import KcoreSpec.KKMatchTotal

set_option autoImplicit false

namespace KCore.KK

/-! ## The definition -/

/-- `t` is `encTerm d tm` with each variable `i` replaced by `enc (σ i)`. -/
def Inst (d : Semantics) (σ : Subst) (tm : Term) (t : T) : Prop :=
  ∃ p, encTerm d tm = some p ∧ instF p (bindOfSubst σ) = some t

/-- The entry of `bindOfSubst σ` for a variable is the encoding of `σ`'s value of it. -/
theorem lookF_bindOfSubst_eq_kin (σ : Subst) (i : Nat) :
    lookF (i : Int) (bindOfSubst σ) = (σ.lookup i).map enc := by
  cases h : σ.lookup i with
  | some w => exact lookF_bindOfSubst_of h
  | none =>
    cases h' : lookF (i : Int) (bindOfSubst σ) with
    | none => rfl
    | some u =>
      obtain ⟨j, w, hj, hw, -⟩ := lookF_bindOfSubst h'
      rw [Int.natCast_inj.mp hj] at h
      rw [h] at hw; cases hw

/-- `bindOfSubst σ` has no entry at a negative number. -/
theorem lookF_bindOfSubst_neg_kin (σ : Subst) {x : Int} (hx : x < 0) :
    lookF x (bindOfSubst σ) = none := by
  cases h : lookF x (bindOfSubst σ) with
  | none => rfl
  | some u =>
    obtain ⟨j, w, rfl, -, -⟩ := lookF_bindOfSubst h
    omega

/-! ## `instF` reads a binding at the form's variables only -/

/-- `B'` gives each of the variables `xs` what `B` gives it. -/
def ExtOn_kin (xs : List Int) (B B' : Bind) : Prop :=
  ∀ x ∈ xs, ∀ u, lookF x B = some u → lookF x B' = some u

theorem ExtOn_kin.left {xs ys : List Int} {B B' : Bind} (h : ExtOn_kin (xs ++ ys) B B') :
    ExtOn_kin xs B B' :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem ExtOn_kin.right {xs ys : List Int} {B B' : Bind} (h : ExtOn_kin (xs ++ ys) B B') :
    ExtOn_kin ys B B' :=
  fun x hx => h x (List.mem_append_right _ hx)

/-- `instTs` at a list each of whose terms `inst` carries from `B` to `B'`. -/
theorem instTsF_mono_of_kin : ∀ (ts : List T),
    (∀ a ∈ ts, ∀ {B B' : Bind} {u : T}, ExtOn_kin (tvarsF a) B B' → instF a B = some u →
      instF a B' = some u) →
    ∀ {B B' : Bind} {us : List T}, ExtOn_kin (tvarsLF ts) B B' → instTsF ts B = some us →
      instTsF ts B' = some us
  | [], _, B, B', us, _, h => by rw [instTsF] at h ⊢; exact h
  | t :: ts, ih, B, B', us, he, h => by
    rw [tvarsLF] at he
    rw [instTsF] at h ⊢
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us', hus, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ih t (List.mem_cons_self ..) he.left hu, Option.bind_some,
      instTsF_mono_of_kin ts (fun a ha => ih a (List.mem_cons_of_mem _ ha)) he.right hus]
    rfl

/-- **`inst` reads a binding at the form's variables.** Where `B'` gives each variable of `p` what
`B` gives it, `inst(p, B')` is `inst(p, B)` wherever the latter has a value. -/
theorem instF_mono_kin (p : T) : ∀ {B B' : Bind} {t : T}, ExtOn_kin (tvarsF p) B B' →
    instF p B = some t → instF p B' = some t := by
  induction p using tInd_kkc with
  | hap f as ih =>
    intro B B' t he h
    rw [tvarsF] at he
    rw [instF] at h ⊢
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [instTsF_mono_of_kin as ih he hus]; rfl
  | hiv i => intro B B' t _ h; rw [instF] at h ⊢; exact h
  | hbv b => intro B B' t _ h; rw [instF] at h ⊢; exact h
  | htk s x => intro B B' t _ h; rw [instF] at h ⊢; exact h
  | hij a b u ih =>
    intro B B' t he h
    rw [tvarsF] at he
    rw [instF] at h ⊢
    obtain ⟨u', hu, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ih he hu]; rfl
  | hvr x =>
    intro B B' t he h
    rw [instF] at h ⊢
    exact he x (by simp [tvarsF]) t h
  | has q i _ => intro B B' t _ h; rw [instF] at h; cases h
  | hhk o as ih =>
    intro B B' t he h
    rw [tvarsF] at he
    rw [instF] at h ⊢
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [instTsF_mono_of_kin as ih he hus]; rfl
  | hbot => intro B B' t _ h; rw [instF] at h; cases h
  | hcb k c ps ih =>
    intro B B' t he h
    rw [tvarsF] at he
    rw [instF] at h ⊢
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [instTsF_mono_of_kin ps ih he hus]; rfl
  | hco k c es _ => intro B B' t _ h; rw [instF] at h; cases h
  | hen u e ihu ihe =>
    intro B B' t he h
    rw [tvarsF] at he
    rw [instF] at h ⊢
    obtain ⟨u', hu, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ihu he.left hu, Option.bind_some, ihe he.right he']; rfl
  | hkv a v iha ihv =>
    intro B B' t he h
    rw [tvarsF] at he
    rw [instF] at h ⊢
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v', hv, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [iha he.left ha, Option.bind_some, ihv he.right hv]; rfl
  | hel x ih =>
    intro B B' t he h
    rw [tvarsF] at he
    rw [instF] at h ⊢
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ih he hx]; rfl

/-! ## The variables of a term's form are the term's -/

/-- Each of `xs` is one of the variables `V`. -/
def Among_kin (xs : List Int) (V : List Nat) : Prop := ∀ x ∈ xs, ∃ i ∈ V, x = (i : Int)

theorem Among_kin.nil (V : List Nat) : Among_kin [] V := fun _ h => nomatch h

theorem Among_kin.append {xs ys : List Int} {V : List Nat} (h1 : Among_kin xs V)
    (h2 : Among_kin ys V) : Among_kin (xs ++ ys) V := fun x hx =>
  (List.mem_append.mp hx).elim (h1 x) (h2 x)

theorem Among_kin.mono {xs : List Int} {V W : List Nat} (h : Among_kin xs V)
    (hVW : ∀ i ∈ V, i ∈ W) : Among_kin xs W := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := h x hx
  exact ⟨i, hVW i hi, rfl⟩

theorem among_tvarsLF_kin {qs : List T} {V : List Nat} :
    Among_kin (tvarsLF qs) V ↔ ∀ q ∈ qs, Among_kin (tvarsF q) V := by
  constructor
  · intro h q hq x hx
    exact h x (mem_tvarsLF_kct.mpr ⟨q, hq, hx⟩)
  · intro h x hx
    obtain ⟨q, hq, hxq⟩ := mem_tvarsLF_kct.mp hx
    exact h q hq x hxq

theorem mem_orderParts_kin {k : Kind} {ps : List T} {q : T} (h : q ∈ orderParts k ps) : q ∈ ps := by
  unfold orderParts at h
  split at h
  · exact h
  · rcases List.mem_append.mp h with h | h
    · exact (List.mem_filter.mp h).1
    · exact (List.mem_filter.mp h).1

section
variable {c : Semantics}

/-- `readApp`'s form holds only variables its arguments' forms or parts hold. -/
theorem readApp_among_kin {f : Sym} {args parts : Option (List T)} {q : T} {V : List Nat}
    (hargs : ∀ qs, args = some qs → Among_kin (tvarsLF qs) V)
    (hparts : ∀ ps, parts = some ps → Among_kin (tvarsLF ps) V)
    (h : readApp c f args parts = some q) : Among_kin (tvarsF q) V := by
  unfold readApp at h
  split at h
  · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [tvarsF]; exact hargs qs hqs
  · split at h
    · obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [tvarsF, among_tvarsLF_kin]
      exact fun x hx => among_tvarsLF_kin.mp (hparts ps hps) x (mem_orderParts_kin hx)
    · split at h
      · split at h
        · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [tvarsF]; exact hargs qs hqs
        · obtain ⟨qs, hqs, h'⟩ := Option.bind_eq_some_iff.mp h
          unfold derivedHook at h'
          split at h'
          · cases h'
            simp only [tvarsF, tvarsLF, List.append_nil]
            exact hargs qs hqs
          · cases h'
      · split at h
        · cases h
        · split at h
          · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
            rw [tvarsF]; exact hargs qs hqs
          · cases h

/-- What the induction gives of a term: its form, and its parts as a concatenation's argument,
hold only its variables. -/
def VarsOf_kin (c : Semantics) (t : Term) : Prop :=
  (∀ q, encTerm c t = some q → Among_kin (tvarsF q) (varOccs t)) ∧
    ∀ k s qs, encPartWith c encLit k s t = some qs → Among_kin (tvarsLF qs) (varOccs t)

theorem encTermsWith_among_kin : ∀ {ts : List Term}, (∀ t ∈ ts, VarsOf_kin c t) → ∀ {qs : List T},
    encTermsWith c encLit ts = some qs → Among_kin (tvarsLF qs) (varOccsList ts)
  | [], _, qs, h => by rw [encTerms_nil_kmf c h, tvarsLF]; exact Among_kin.nil _
  | t :: ts, ih, qs, h => by
    obtain ⟨q, qs', h1, h2, rfl⟩ := encTerms_cons_kmf c h
    rw [tvarsLF, varOccsList]
    exact Among_kin.append
      (((ih t (by simp)).1 q h1).mono fun i hi => List.mem_append_left _ hi)
      ((encTermsWith_among_kin (fun x hx => ih x (by simp [hx])) h2).mono
        fun i hi => List.mem_append_right _ hi)

theorem encCollWith_among_kin {ts : List Term} (ih : ∀ t ∈ ts, VarsOf_kin c t) (k : Kind) (s : Srt)
    (r : CRole) {ps : List T} (h : encCollWith c encLit k s r ts = some ps) :
    Among_kin (tvarsLF ps) (varOccsList ts) := by
  rcases ts with _ | ⟨x, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
  · simp only [encCollWith] at h
    split at h
    · cases h; rw [tvarsLF]; exact Among_kin.nil _
    · cases h
  · simp only [encCollWith] at h
    split at h
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [varOccsList, List.append_nil, tvarsLF, tvarsF]
      exact (ih x (by simp)).1 p hp
    · cases h
  · have ha := ih x (by simp)
    have hv := ih v (by simp)
    have hl : ∀ i ∈ varOccs x, i ∈ varOccsList [x, v] := fun i hi => by
      simp only [varOccsList, List.append_nil, List.mem_append]; exact .inl hi
    have hr : ∀ i ∈ varOccs v, i ∈ varOccsList [x, v] := fun i hi => by
      simp only [varOccsList, List.append_nil, List.mem_append]; exact .inr hi
    simp only [encCollWith] at h
    split at h
    · split at h
      · rename_i p q' hp hq
        cases h
        simp only [tvarsLF, tvarsF, List.append_nil]
        exact Among_kin.append ((ha.1 p hp).mono hl) ((hv.1 q' hq).mono hr)
      · cases h
    · split at h
      · split at h
        · rename_i p q' hp hq
          cases h
          rw [among_tvarsLF_kin]
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact (among_tvarsLF_kin.mp (ha.2 k s p hp) y hy).mono hl
          · exact (among_tvarsLF_kin.mp (hv.2 k s q' hq) y hy).mono hr
        · cases h
      · cases h
  · simp only [encCollWith] at h; cases h

/-- **The form of a term holds only the term's variables.** -/
theorem varsOf_kin (t : Term) : VarsOf_kin c t := by
  induction t using termInd_kel with
  | hvar i =>
    have hv : Among_kin [(i : Int)] (varOccs (.var i)) := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨i, by simp [varOccs], rfl⟩
    refine ⟨fun q hq => ?_, fun k s qs hq => ?_⟩
    · rw [encTerm_var_kmf] at hq; cases hq; rw [tvarsF]; exact hv
    · simp only [encPartWith, Option.some.injEq] at hq
      subst hq; simp only [tvarsLF, tvarsF, List.append_nil]; exact hv
  | hdv s l =>
    have hl : ∀ q, encLit s l = some q → tvarsF q = [] := by
      intro q hq
      unfold encLit encLitWith at hq
      split at hq <;> first | (cases hq; rfl) | cases hq
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_dv_kmf] at hq; rw [hl q hq]; exact Among_kin.nil _
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [tvarsLF, hl p hp, List.append_nil]; exact Among_kin.nil _
  | hinj a b t ih =>
    have e : varOccs (.inj a b t) = varOccs t := by rw [varOccs]
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_inj_kmf] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [tvarsF, e]; exact ih.1 p hp
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [tvarsLF, tvarsF, List.append_nil]; rw [e]
      exact ih.1 p hp
  | has t i ih =>
    have hl : ∀ j ∈ varOccs t, j ∈ varOccs (.as t i) := fun j hj => by
      rw [varOccs]; exact List.mem_append_left _ hj
    have hi : Among_kin [(i : Int)] (varOccs (.as t i)) := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact ⟨i, by rw [varOccs]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_as_kmf] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [tvarsF]; exact Among_kin.append ((ih.1 p hp).mono hl) hi
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [tvarsLF, tvarsF, List.append_nil]
      exact Among_kin.append ((ih.1 p hp).mono hl) hi
  | happ f ts ih =>
    have e : varOccs (.app f ts) = varOccsList ts := by rw [varOccs]
    have hargs : ∀ qs, encTermsWith c encLit ts = some qs → Among_kin (tvarsLF qs) (varOccsList ts) :=
      fun qs h => encTermsWith_among_kin ih h
    have hcoll : ∀ k' s' r ps, encCollWith c encLit k' s' r ts = some ps →
        Among_kin (tvarsLF ps) (varOccsList ts) :=
      fun k' s' r ps h => encCollWith_among_kin ih k' s' r h
    have hparts : ∀ ps, ((collSymOf c f).bind fun (k', s', r) => encCollWith c encLit k' s' r ts) =
        some ps → Among_kin (tvarsLF ps) (varOccsList ts) := by
      intro ps h
      obtain ⟨⟨k', s', r⟩, -, h'⟩ := Option.bind_eq_some_iff.mp h
      exact hcoll k' s' r ps h'
    unfold VarsOf_kin
    rw [e]
    refine ⟨fun q hq => ?_, fun k₀ s₀ qs hq => ?_⟩
    · rw [encTerm_app_kmf] at hq
      exact readApp_among_kin hargs hparts hq
    · simp only [encPartWith] at hq
      split at hq
      · split at hq
        · exact hcoll _ _ _ _ hq
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
          simp only [tvarsLF, List.append_nil]
          exact readApp_among_kin hargs (fun ps h => hcoll _ _ _ ps h) hp
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
        simp only [tvarsLF, List.append_nil]
        exact readApp_among_kin hargs hparts hp

/-- Each variable of the form `encTerm c t` is a variable of `t`. -/
theorem encTerm_among_kin {t : Term} {q : T} (h : encTerm c t = some q) :
    Among_kin (tvarsF q) (varOccs t) :=
  (varsOf_kin t).1 q h

end

/-! ## `inst` gives the instance -/

/-- **`inst` gives an `Inst` term, on the form's variables.** Where `encTerm d tm` is `p`, what `B`
gives each variable of `p` is the encoding of what `σ` gives it, and kore.k's `inst(p, B)` is `t`:
`t` is `tm`'s instance under `σ`. -/
theorem inst_Inst_tvars_kin {d : Semantics} {σ : Subst} {tm : Term} {p t : T} {B : Bind}
    (h : encTerm d tm = some p)
    (hB : ∀ x ∈ tvarsF p, ∀ u, lookF x B = some u →
      ∃ (i : Nat) (w : GroundTerm), x = (i : Int) ∧ σ.lookup i = some w ∧ u = enc w)
    (ht : instF p B = some t) : Inst d σ tm t := by
  refine ⟨p, h, instF_mono_kin p (fun x hx u hu => ?_) ht⟩
  obtain ⟨i, w, rfl, hw, rfl⟩ := hB x hx u hu
  exact lookF_bindOfSubst_of hw

/-- `inst` gives an `Inst` term where `B` agrees with `σ` (what `B` gives any variable is the
encoding of what `σ` gives it). -/
theorem inst_Inst_agree_kin {d : Semantics} {σ : Subst} {tm : Term} {p t : T} {B : Bind}
    (h : encTerm d tm = some p) (hB : BindAgree B σ) (ht : instF p B = some t) : Inst d σ tm t :=
  inst_Inst_tvars_kin h (fun x _ u hu => hB x u hu) ht

/-- **`inst` gives an `Inst` term.** Where `encTerm d tm` is `p`, `B`
represents `σ` on `varOccs tm` (what `B` gives each variable of `tm` is the encoding of what `σ`
gives it), and kore.k's `inst(p, B)` is `t`: `t` is `tm`'s instance under `σ`. -/
theorem inst_Inst {d : Semantics} {σ : Subst} {tm : Term} {p t : T} {B : Bind}
    (h : encTerm d tm = some p)
    (hB : ∀ i ∈ varOccs tm, ∀ u, lookF (i : Int) B = some u → ∃ w, σ.lookup i = some w ∧ u = enc w)
    (ht : instF p B = some t) : Inst d σ tm t := by
  refine inst_Inst_tvars_kin h (fun x hx u hu => ?_) ht
  obtain ⟨i, hi, rfl⟩ := encTerm_among_kin h x hx
  obtain ⟨w, hw, rfl⟩ := hB i hi u hu
  exact ⟨i, w, rfl, hw, rfl⟩

/-- At a term whose form is `p`, the instance is `inst(p, bindOfSubst σ)`. -/
theorem Inst_iff_kin {d : Semantics} {σ : Subst} {tm : Term} {p t : T} (h : encTerm d tm = some p) :
    Inst d σ tm t ↔ instF p (bindOfSubst σ) = some t := by
  constructor
  · rintro ⟨p', h', ht⟩
    rw [h] at h'; cases h'; exact ht
  · exact fun ht => ⟨p, h, ht⟩

/-- A term has at most one instance under `σ`. -/
theorem Inst.unique_kin {d : Semantics} {σ : Subst} {tm : Term} {t t' : T}
    (h : Inst d σ tm t) (h' : Inst d σ tm t') : t = t' := by
  obtain ⟨p, hp, ht⟩ := h
  obtain ⟨p', hp', ht'⟩ := h'
  rw [hp] at hp'; cases hp'
  rw [ht] at ht'; cases ht'; rfl

/-- The instance of a variable is the encoding of its value. -/
theorem Inst_var_iff_kin {d : Semantics} {σ : Subst} {i : Nat} {t : T} :
    Inst d σ (.var i) t ↔ ∃ w, σ.lookup i = some w ∧ t = enc w := by
  rw [Inst_iff_kin (encTerm_var_kmf d i), instF, lookF_bindOfSubst_eq_kin]
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    rw [hw]; rfl

/-! ## Checks -/

#check @Inst
#check @inst_Inst
#check @inst_Inst_tvars_kin
#check @inst_Inst_agree_kin
#check @encTerm_among_kin
#check @instF_mono_kin
#check @Inst_iff_kin
#check @Inst.unique_kin
#check @Inst_var_iff_kin

open Lean in
#eval show CoreM Unit from do
  for n in [``inst_Inst, ``inst_Inst_tvars_kin, ``inst_Inst_agree_kin, ``encTerm_among_kin, ``instF_mono_kin, ``Inst_iff_kin, ``Inst.unique_kin,
      ``Inst_var_iff_kin, ``lookF_bindOfSubst_eq_kin, ``lookF_bindOfSubst_neg_kin] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
