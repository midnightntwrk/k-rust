import KcoreSpec.KKEncLemmas

/-!
# `kore.k`'s order on encoded values, and the canonical form `enc` writes

`cmpF` is antisymmetric (`cmpF_swap`), takes the values -1, 0 and 1 only (`cmpF_range`) and is 0
between a term and itself (`cmpF_self`), on every term. It is 0 between two different terms of the
forms `tagF` ranks 6 and it ignores a collection's kind, so it is no order on all of `T`: its laws
hold on the terms `VT κ` describes, where each collection's kind is the one `κ` gives its sort
number and its members are entries of a map or elements of a set or list accordingly
(`cmpF_eq_zero_iff_vt`, `cmpF_trans_vt`). The encoding of a value sorted in a semantics `c` is such
a term at `κ := kindOf c` (`enc_vt`), so on encodings of values sorted in one semantics `cmpF` is
transitive (`cmpF_trans`), and 0 exactly between equal values where their literals have a `kore.k`
form (`cmpF_eq_zero_iff`).

`sortK` permutes its input (`sortK_perm`) and orders it by `ckeyF` where `ckeyF` is a strict total
order on its members (`sortK_sorted`); so `enc` writes every map and set of a value sorted in `c`
whose literals have a `kore.k` form strictly increasing by `ckeyF`, and no injection under an
injection (`enc_canonical`).
-/

set_option autoImplicit false

namespace KCore.KK
open GroundTerm

/-! ## Induction over terms, a list's members given at once -/

theorem tInd_kkc (P : T → Prop)
    (hap : ∀ f as, (∀ a ∈ as, P a) → P (.ap f as))
    (hiv : ∀ i, P (.iv i)) (hbv : ∀ b, P (.bv b)) (htk : ∀ s x, P (.tk s x))
    (hij : ∀ a b t, P t → P (.ij a b t)) (hvr : ∀ i, P (.vr i)) (has : ∀ p i, P p → P (.as p i))
    (hhk : ∀ o as, (∀ a ∈ as, P a) → P (.hk o as)) (hbot : P .bot)
    (hcb : ∀ k c ps, (∀ a ∈ ps, P a) → P (.cb k c ps))
    (hco : ∀ k c es, (∀ a ∈ es, P a) → P (.co k c es))
    (hen : ∀ t e, P t → P e → P (.en t e)) (hkv : ∀ a v, P a → P v → P (.kv a v))
    (hel : ∀ x, P x → P (.el x)) (t : T) : P t :=
  T.rec (motive_1 := P) (motive_2 := fun ts => ∀ t ∈ ts, P t) hap hiv hbv htk hij hvr has hhk hbot
    hcb hco hen hkv hel
    (fun _ h => nomatch h)
    (fun _ _ hx hxs y hy => match List.mem_cons.mp hy with
      | .inl h => h ▸ hx
      | .inr h => hxs y h) t

/-! ## `cmpIF`, `lexF` and `b2iF` -/

/-- The three values a comparison takes. -/
def R3_kkc (x : Int) : Prop := x = -1 ∨ x = 0 ∨ x = 1

theorem cmpIF_swap_kkc (x y : Int) : cmpIF y x = -cmpIF x y := by
  unfold cmpIF
  by_cases h1 : x < y
  · have : ¬ y < x := by omega
    have : ¬ y = x := by omega
    simp [*]
  · by_cases h2 : x = y
    · subst h2; simp
    · have : y < x := by omega
      have : ¬ y = x := by omega
      simp [*]

theorem cmpIF_r3_kkc (x y : Int) : R3_kkc (cmpIF x y) := by
  unfold cmpIF R3_kkc; split
  · simp
  · split <;> simp

theorem cmpIF_self_kkc (x : Int) : cmpIF x x = 0 := by simp [cmpIF]

theorem cmpIF_eq_zero_kkc {x y : Int} : cmpIF x y = 0 ↔ x = y := by
  unfold cmpIF; split
  · constructor
    · intro h; cases h
    · intro h; omega
  · split <;> simp_all

theorem cmpIF_eq_neg_kkc {x y : Int} : cmpIF x y = -1 ↔ x < y := by
  unfold cmpIF; split
  · simp_all
  · split
    · simp_all
    · constructor
      · intro h; cases h
      · intro h; omega

theorem lexF_neg_kkc (x y : Int) : lexF (-x) (-y) = -lexF x y := by
  unfold lexF; by_cases h : x = 0 <;> simp [h]

theorem lexF_r3_kkc {x y : Int} (hx : R3_kkc x) (hy : R3_kkc y) : R3_kkc (lexF x y) := by
  unfold lexF; split
  · exact hy
  · exact hx

theorem lexF_eq_zero_kkc {x y : Int} : lexF x y = 0 ↔ x = 0 ∧ y = 0 := by
  unfold lexF; by_cases h : x = 0 <;> simp [h]

theorem lexF_eq_neg_kkc {x y : Int} : lexF x y = -1 ↔ x = -1 ∨ (x = 0 ∧ y = -1) := by
  unfold lexF; by_cases h : x = 0 <;> simp [h]

theorem b2iF_inj_kkc {a b : Bool} (h : b2iF a = b2iF b) : a = b := by
  cases a <;> cases b <;> simp_all [b2iF]

/-! ## The order on code-point sequences -/

theorem lexLt_irrefl_kkc : ∀ x : List Char, KStr.lexLt x x = false
  | [] => rfl
  | a :: x => by simp [KStr.lexLt, lexLt_irrefl_kkc x]

theorem lexLt_asymm_kkc : ∀ {x y : List Char}, KStr.lexLt x y = true → KStr.lexLt y x = false
  | [], [], h => by simp [KStr.lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [KStr.lexLt] at h
  | a :: x, b :: y, h => by
    simp only [KStr.lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · have : ¬ b.toNat < a.toNat := by omega
      have : ¬ b.toNat = a.toNat := by omega
      simp [*]
    · have := lexLt_asymm_kkc h2
      simp [h1, this]

theorem lexLt_total_kkc : ∀ {x y : List Char}, KStr.lexLt x y = false → KStr.lexLt y x = false → x = y
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [KStr.lexLt] at h
  | _ :: _, [], _, h => by simp [KStr.lexLt] at h
  | a :: x, b :: y, h1, h2 => by
    simp only [KStr.lexLt, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
      at h1 h2
    have hab : a.toNat = b.toNat := by omega
    have hx : KStr.lexLt x y = false := by
      rcases h1.2 with h | h
      · exact absurd hab h
      · exact h
    have hy : KStr.lexLt y x = false := by
      rcases h2.2 with h | h
      · exact absurd hab.symm h
      · exact h
    rw [Char.toNat_inj.mp hab, lexLt_total_kkc hx hy]

theorem lexLt_trans_kkc : ∀ {x y z : List Char}, KStr.lexLt x y = true → KStr.lexLt y z = true →
    KStr.lexLt x z = true
  | [], [], _, h, _ => by simp [KStr.lexLt] at h
  | [], _ :: _, [], _, h => by simp [KStr.lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [KStr.lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [KStr.lexLt] at h
  | a :: x, b :: y, c :: z, h1, h2 => by
    simp only [KStr.lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr ⟨by omega, lexLt_trans_kkc h1' h2'⟩

/-- `cmpF` on two tokens' texts. -/
def scmpF_kkc (x y : String) : Int :=
  cmpIF (b2iF (KStr.lexLt y.toList x.toList)) (b2iF (KStr.lexLt x.toList y.toList))

theorem scmpF_swap_kkc (x y : String) : scmpF_kkc y x = -scmpF_kkc x y := by
  unfold scmpF_kkc; rw [cmpIF_swap_kkc]

theorem scmpF_r3_kkc (x y : String) : R3_kkc (scmpF_kkc x y) := cmpIF_r3_kkc _ _

theorem scmpF_eq_zero_kkc {x y : String} : scmpF_kkc x y = 0 ↔ x = y := by
  unfold scmpF_kkc
  rw [cmpIF_eq_zero_kkc]
  constructor
  · intro h
    have h' := b2iF_inj_kkc h
    cases h1 : KStr.lexLt y.toList x.toList with
    | true =>
      rw [h1] at h'
      exact absurd h'.symm (by rw [lexLt_asymm_kkc h1]; decide)
    | false =>
      rw [h1] at h'
      exact String.toList_injective (lexLt_total_kkc h'.symm h1)
  · rintro rfl; rfl

theorem scmpF_eq_neg_kkc {x y : String} :
    scmpF_kkc x y = -1 ↔ KStr.lexLt x.toList y.toList = true := by
  unfold scmpF_kkc
  rw [cmpIF_eq_neg_kkc]
  constructor
  · intro h
    cases h1 : KStr.lexLt x.toList y.toList
    · rw [h1] at h; cases h2 : KStr.lexLt y.toList x.toList <;> simp [b2iF, h2] at h
    · rfl
  · intro h
    rw [h, lexLt_asymm_kkc h]; decide

/-! ## The laws on every term -/

/-- The constructor of a term. -/
def form_kkc : T → Nat
  | .ap .. => 0 | .iv _ => 1 | .bv _ => 2 | .tk .. => 3 | .ij .. => 4 | .vr _ => 5 | .as .. => 6
  | .hk .. => 7 | .bot => 8 | .cb .. => 9 | .co .. => 10 | .en .. => 11 | .kv .. => 12 | .el _ => 13

/-- Two terms of different constructors compare by `tagF`. -/
theorem cmpF_of_form_ne_kkc {t u : T} (h : form_kkc t ≠ form_kkc u) :
    cmpF t u = cmpIF (tagF t) (tagF u) := by
  cases t <;> cases u <;> first | exact absurd rfl h | simp only [cmpF]

theorem cmpF_tk_kkc (s t : Int) (x y : String) :
    cmpF (.tk s x) (.tk t y) = lexF (cmpIF s t) (scmpF_kkc x y) := by
  simp only [cmpF, scmpF_kkc]

theorem cmpF_swap_of_form_kkc {t u : T} (h : form_kkc t ≠ form_kkc u) : cmpF u t = -cmpF t u := by
  rw [cmpF_of_form_ne_kkc h, cmpF_of_form_ne_kkc (Ne.symm h), cmpIF_swap_kkc]

theorem cmpTsF_swap_kkc : ∀ {as bs : List T}, (∀ a ∈ as, ∀ u, cmpF u a = -cmpF a u) →
    cmpTsF bs as = -cmpTsF as bs
  | [], [], _ => by simp [cmpTsF]
  | [], _ :: _, _ => by simp [cmpTsF]
  | _ :: _, [], _ => by simp [cmpTsF]
  | a :: as, b :: bs, h => by
    simp only [cmpTsF]
    rw [h a (List.mem_cons_self ..), cmpTsF_swap_kkc (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      lexF_neg_kkc]

/-- `cmpF` is antisymmetric on every term. -/
theorem cmpF_swap (t u : T) : cmpF u t = -cmpF t u := by
  induction t using tInd_kkc generalizing u with
  | hap f as ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_swap_kkc _ _) | skip
    simp only [cmpF]; rw [cmpIF_swap_kkc, cmpTsF_swap_kkc ih, lexF_neg_kkc]
  | hiv i => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | hbv b => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | htk s x =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_swap_kkc _ _) | skip
    rw [cmpF_tk_kkc, cmpF_tk_kkc, cmpIF_swap_kkc, scmpF_swap_kkc, lexF_neg_kkc]
  | hij a b t ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_swap_kkc _ _) | skip
    simp only [cmpF]; rw [cmpIF_swap_kkc a, cmpIF_swap_kkc b, ih, lexF_neg_kkc, lexF_neg_kkc]
  | hvr i => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | has p i ih => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | hhk o as ih => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | hbot => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | hcb k c ps ih => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | hco k c es ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_swap_kkc _ _) | skip
    simp only [cmpF]; rw [cmpIF_swap_kkc, cmpTsF_swap_kkc ih, lexF_neg_kkc]
  | hen t e iht ihe => cases u <;> (simp only [cmpF]; exact cmpIF_swap_kkc _ _)
  | hkv a v iha ihv =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_swap_kkc _ _) | skip
    simp only [cmpF]; rw [iha, ihv, lexF_neg_kkc]
  | hel x ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_swap_kkc _ _) | skip
    simp only [cmpF]; rw [ih]

theorem cmpTsF_r3_kkc : ∀ {as bs : List T}, (∀ a ∈ as, ∀ u, R3_kkc (cmpF a u)) → R3_kkc (cmpTsF as bs)
  | [], [], _ => by simp [cmpTsF, R3_kkc]
  | [], _ :: _, _ => by simp [cmpTsF, R3_kkc]
  | _ :: _, [], _ => by simp [cmpTsF, R3_kkc]
  | a :: as, b :: bs, h => by
    simp only [cmpTsF]
    exact lexF_r3_kkc (h a (List.mem_cons_self ..) b)
      (cmpTsF_r3_kkc fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `cmpF` takes the values -1, 0 and 1 only. -/
theorem cmpF_range (t u : T) : cmpF t u = -1 ∨ cmpF t u = 0 ∨ cmpF t u = 1 := by
  show R3_kkc _
  induction t using tInd_kkc generalizing u with
  | hap f as ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_r3_kkc _ _) | skip
    simp only [cmpF]; exact lexF_r3_kkc (cmpIF_r3_kkc _ _) (cmpTsF_r3_kkc ih)
  | htk s x =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_r3_kkc _ _) | skip
    rw [cmpF_tk_kkc]; exact lexF_r3_kkc (cmpIF_r3_kkc _ _) (scmpF_r3_kkc _ _)
  | hij a b t ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_r3_kkc _ _) | skip
    simp only [cmpF]
    exact lexF_r3_kkc (cmpIF_r3_kkc _ _) (lexF_r3_kkc (cmpIF_r3_kkc _ _) (ih _))
  | hco k c es ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_r3_kkc _ _) | skip
    simp only [cmpF]; exact lexF_r3_kkc (cmpIF_r3_kkc _ _) (cmpTsF_r3_kkc ih)
  | hkv a v iha ihv =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_r3_kkc _ _) | skip
    simp only [cmpF]; exact lexF_r3_kkc (iha _) (ihv _)
  | hel x ih =>
    cases u <;> first | (simp only [cmpF]; exact cmpIF_r3_kkc _ _) | skip
    simp only [cmpF]; exact ih _
  | _ =>
    cases u <;> (simp only [cmpF]; exact cmpIF_r3_kkc _ _)

theorem cmpTsF_self_kkc : ∀ {as : List T}, (∀ a ∈ as, cmpF a a = 0) → cmpTsF as as = 0
  | [], _ => by simp [cmpTsF]
  | a :: as, h => by
    simp only [cmpTsF]
    rw [h a (List.mem_cons_self ..), cmpTsF_self_kkc fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- A term is equal to itself in `cmpF`. -/
theorem cmpF_self (t : T) : cmpF t t = 0 := by
  induction t using tInd_kkc with
  | hap f as ih => simp only [cmpF, cmpIF_self_kkc, cmpTsF_self_kkc ih]; rfl
  | hiv i => simp only [cmpF, cmpIF_self_kkc]
  | hbv b => simp only [cmpF, cmpIF_self_kkc]
  | htk s x => rw [cmpF_tk_kkc, cmpIF_self_kkc, scmpF_eq_zero_kkc.mpr rfl]; rfl
  | hij a b t ih => simp only [cmpF, cmpIF_self_kkc, ih]; rfl
  | hco k c es ih => simp only [cmpF, cmpIF_self_kkc, cmpTsF_self_kkc ih]; rfl
  | hkv a v iha ihv => simp only [cmpF, iha, ihv]; rfl
  | hel x ih => simp only [cmpF, ih]
  | _ => simp only [cmpF]; exact cmpIF_self_kkc _

/-! ## `tagF` and the order between forms -/

theorem tag_of_form_kkc {t u : T} (h : form_kkc t = form_kkc u) : tagF t = tagF u := by
  cases t <;> cases u <;> simp only [form_kkc] at h <;> first | rfl | exact absurd h (by decide)

theorem tag_eq_of_cmpF_zero_kkc {t u : T} (h : cmpF t u = 0) : tagF t = tagF u := by
  by_cases hf : form_kkc t = form_kkc u
  · exact tag_of_form_kkc hf
  · rw [cmpF_of_form_ne_kkc hf, cmpIF_eq_zero_kkc] at h; exact h

theorem tag_le_of_cmpF_neg_kkc {t u : T} (h : cmpF t u = -1) : tagF t ≤ tagF u := by
  by_cases hf : form_kkc t = form_kkc u
  · exact Int.le_of_eq (tag_of_form_kkc hf)
  · rw [cmpF_of_form_ne_kkc hf, cmpIF_eq_neg_kkc] at h; exact Int.le_of_lt h

theorem cmpF_neg_of_tag_lt_kkc {t u : T} (h : tagF t < tagF u) : cmpF t u = -1 := by
  have hf : form_kkc t ≠ form_kkc u := fun hf => by rw [tag_of_form_kkc hf] at h; exact Int.lt_irrefl _ h
  rw [cmpF_of_form_ne_kkc hf, cmpIF_eq_neg_kkc]; exact h

/-! ## The terms on which `cmpF` is an order -/

/-- The terms `enc` writes, where `κ` gives each collection sort number its kind. `EncShape κ none t`:
`t` is a value (an `iv`, `bv`, `tk`, `bot`, `ap`, `ij`, or a `co` whose kind is `κ` of its sort
number); `EncShape κ (some k) e`: `e` is a member of a collection of kind `k`, an entry `kv` of a
map or an element `el` of a set or a list. -/
inductive EncShape (κ : Int → Kind) : Option Kind → T → Prop
  | iv (i : Int) : EncShape κ none (.iv i)
  | bv (b : Bool) : EncShape κ none (.bv b)
  | tk (s : Int) (x : String) : EncShape κ none (.tk s x)
  | bot : EncShape κ none .bot
  | ap (f : Int) (as : List T) : (∀ a ∈ as, EncShape κ none a) → EncShape κ none (.ap f as)
  | ij (a b : Int) (t : T) : EncShape κ none t → EncShape κ none (.ij a b t)
  | co (k : Kind) (c : Int) (es : List T) : κ c = k → (∀ e ∈ es, EncShape κ (some k) e) →
      EncShape κ none (.co k c es)
  | kv (a v : T) : EncShape κ none a → EncShape κ none v → EncShape κ (some .map) (.kv a v)
  | el (k : Kind) (x : T) : k ≠ .map → EncShape κ none x → EncShape κ (some k) (.el x)

/-- Two values of one `tagF` have one constructor. -/
theorem shape_form_kkc {κ : Int → Kind} {t u : T} (ht : EncShape κ none t) (hu : EncShape κ none u)
    (h : tagF t = tagF u) : form_kkc t = form_kkc u := by
  cases ht <;> cases hu <;> simp only [tagF] at h <;> first | rfl | exact absurd h (by decide)

theorem cmpTsF_eq_zero_kkc : ∀ {as bs : List T}, (∀ a ∈ as, ∀ b ∈ bs, cmpF a b = 0 → a = b) →
    cmpTsF as bs = 0 → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [cmpTsF] at h
  | _ :: _, [], _, h => by simp [cmpTsF] at h
  | a :: as, b :: bs, hz, h => by
    simp only [cmpTsF, lexF_eq_zero_kkc] at h
    rw [hz a (List.mem_cons_self ..) b (List.mem_cons_self ..) h.1,
      cmpTsF_eq_zero_kkc (fun x hx y hy => hz x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) h.2]

/-- On terms of one shape, `cmpF` is 0 only between equal terms. -/
theorem cmpF_eq_zero_shape {κ : Int → Kind} {o : Option Kind} {t u : T} (ht : EncShape κ o t)
    (hu : EncShape κ o u) (h : cmpF t u = 0) : t = u := by
  induction ht generalizing u with
  | iv i =>
    have hf := shape_form_kkc (.iv i) hu (tag_eq_of_cmpF_zero_kkc h)
    cases hu <;> simp only [form_kkc] at hf <;> try exact absurd hf (by decide)
    simp only [cmpF, cmpIF_eq_zero_kkc] at h; rw [h]
  | bv b =>
    have hf := shape_form_kkc (.bv b) hu (tag_eq_of_cmpF_zero_kkc h)
    cases hu <;> simp only [form_kkc] at hf <;> try exact absurd hf (by decide)
    simp only [cmpF, cmpIF_eq_zero_kkc] at h; rw [b2iF_inj_kkc h]
  | tk s x =>
    have hf := shape_form_kkc (.tk s x) hu (tag_eq_of_cmpF_zero_kkc h)
    cases hu <;> simp only [form_kkc] at hf <;> try exact absurd hf (by decide)
    rw [cmpF_tk_kkc, lexF_eq_zero_kkc, cmpIF_eq_zero_kkc, scmpF_eq_zero_kkc] at h
    rw [h.1, h.2]
  | bot =>
    have hf := shape_form_kkc .bot hu (tag_eq_of_cmpF_zero_kkc h)
    cases hu <;> simp only [form_kkc] at hf <;> try exact absurd hf (by decide)
    rfl
  | ap f as has ih =>
    have hf := shape_form_kkc (.ap f as has) hu (tag_eq_of_cmpF_zero_kkc h)
    cases hu with
    | ap g bs hbs =>
      simp only [cmpF, lexF_eq_zero_kkc, cmpIF_eq_zero_kkc] at h
      rw [h.1, cmpTsF_eq_zero_kkc (fun a ha b hb => ih a ha (hbs b hb)) h.2]
    | _ => simp only [form_kkc] at hf; exact absurd hf (by decide)
  | ij a b t ht' ih =>
    have hf := shape_form_kkc (.ij a b t ht') hu (tag_eq_of_cmpF_zero_kkc h)
    cases hu with
    | ij c e u hu' =>
      simp only [cmpF, lexF_eq_zero_kkc, cmpIF_eq_zero_kkc] at h
      rw [h.1, h.2.1, ih hu' h.2.2]
    | _ => simp only [form_kkc] at hf; exact absurd hf (by decide)
  | co k c es hk hes ih =>
    have hf := shape_form_kkc (.co k c es hk hes) hu (tag_eq_of_cmpF_zero_kkc h)
    cases hu with
    | co k' d fs hk' hfs =>
      simp only [cmpF, lexF_eq_zero_kkc, cmpIF_eq_zero_kkc] at h
      obtain ⟨rfl, h2⟩ := h
      have : k = k' := hk.symm.trans hk'
      subst this
      rw [cmpTsF_eq_zero_kkc (fun a ha b hb => ih a ha (hfs b hb)) h2]
    | _ => simp only [form_kkc] at hf; exact absurd hf (by decide)
  | kv a v ha hv iha ihv =>
    cases hu with
    | kv b w hb hw =>
      simp only [cmpF, lexF_eq_zero_kkc] at h
      rw [iha hb h.1, ihv hw h.2]
    | el k x hk _ => exact absurd rfl hk
  | el k x hk hx ih =>
    cases hu with
    | kv b w hb hw => exact absurd rfl hk
    | el k' y _ hy =>
      simp only [cmpF] at h
      rw [ih hy h]

/-- On terms of one shape, `cmpF` is 0 exactly between equal terms. -/
theorem cmpF_eq_zero_iff_shape {κ : Int → Kind} {o : Option Kind} {t u : T} (ht : EncShape κ o t)
    (hu : EncShape κ o u) : cmpF t u = 0 ↔ t = u :=
  ⟨cmpF_eq_zero_shape ht hu, fun h => h ▸ cmpF_self t⟩

theorem cmpIF_trans_kkc {x y z : Int} (h1 : cmpIF x y = -1) (h2 : cmpIF y z = -1) : cmpIF x z = -1 := by
  rw [cmpIF_eq_neg_kkc] at *; omega

theorem cmpTsF_trans_kkc : ∀ {as bs cs : List T},
    (∀ a ∈ as, ∀ b ∈ bs, cmpF a b = 0 → a = b) → (∀ b ∈ bs, ∀ c ∈ cs, cmpF b c = 0 → b = c) →
    (∀ a ∈ as, ∀ b ∈ bs, ∀ c ∈ cs, cmpF a b = -1 → cmpF b c = -1 → cmpF a c = -1) →
    cmpTsF as bs = -1 → cmpTsF bs cs = -1 → cmpTsF as cs = -1
  | [], [], _, _, _, _, h, _ => by simp [cmpTsF] at h
  | [], _ :: _, [], _, _, _, _, h => by simp [cmpTsF] at h
  | [], _ :: _, _ :: _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, h, _ => by simp [cmpTsF] at h
  | _ :: _, _ :: _, [], _, _, _, _, h => by simp [cmpTsF] at h
  | a :: as, b :: bs, c :: cs, hz1, hz2, htr, h1, h2 => by
    simp only [cmpTsF, lexF_eq_neg_kkc] at h1 h2 ⊢
    have ha := List.mem_cons_self (a := a) (l := as)
    have hb := List.mem_cons_self (a := b) (l := bs)
    have hc := List.mem_cons_self (a := c) (l := cs)
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact .inl (htr a ha b hb c hc h1 h2)
    · rw [← hz2 b hb c hc h2]; exact .inl h1
    · rw [hz1 a ha b hb h1]; exact .inl h2
    · rw [hz1 a ha b hb h1, hz2 b hb c hc h2, cmpF_self]
      refine .inr ⟨rfl, cmpTsF_trans_kkc ?_ ?_ ?_ h1' h2'⟩
      · exact fun x hx y hy => hz1 x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      · exact fun x hx y hy => hz2 x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      · exact fun x hx y hy z hz => htr x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) z
          (List.mem_cons_of_mem _ hz)

/-- `lexF`'s order is transitive where the first comparison is an order whose 0 is equality. -/
theorem lexF_trans_kkc {α : Type} (cmp : α → α → Int) {p q r : α} {X Y Z : Int}
    (hz1 : cmp p q = 0 → p = q) (hz2 : cmp q r = 0 → q = r) (hself : cmp p p = 0)
    (htr : cmp p q = -1 → cmp q r = -1 → cmp p r = -1)
    (hrest : p = q → q = r → X = -1 → Y = -1 → Z = -1)
    (h1 : lexF (cmp p q) X = -1) (h2 : lexF (cmp q r) Y = -1) : lexF (cmp p r) Z = -1 := by
  rw [lexF_eq_neg_kkc] at h1 h2 ⊢
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact .inl (htr h1 h2)
  · rw [← hz2 h2]; exact .inl h1
  · rw [hz1 h1]; exact .inl h2
  · have e1 := hz1 h1
    have e2 := hz2 h2
    subst e1; subst e2
    exact .inr ⟨hself, hrest rfl rfl h1' h2'⟩

theorem lexF_trans_int_kkc {p q r : Int} {X Y Z : Int} (hrest : p = q → q = r → X = -1 → Y = -1 → Z = -1)
    (h1 : lexF (cmpIF p q) X = -1) (h2 : lexF (cmpIF q r) Y = -1) : lexF (cmpIF p r) Z = -1 :=
  lexF_trans_kkc cmpIF cmpIF_eq_zero_kkc.mp cmpIF_eq_zero_kkc.mp (cmpIF_self_kkc _) cmpIF_trans_kkc
    hrest h1 h2

/-- Three values in `cmpF`'s order below one another: the first is below the third, or all three
have one constructor. -/
theorem cmpF_trans_or_form_kkc {κ : Int → Kind} {t u w : T} (ht : EncShape κ none t)
    (hu : EncShape κ none u) (hw : EncShape κ none w) (h1 : cmpF t u = -1) (h2 : cmpF u w = -1) :
    cmpF t w = -1 ∨ (form_kkc t = form_kkc u ∧ form_kkc u = form_kkc w) := by
  by_cases hlt : tagF t < tagF w
  · exact .inl (cmpF_neg_of_tag_lt_kkc hlt)
  have e1 := tag_le_of_cmpF_neg_kkc h1
  have e2 := tag_le_of_cmpF_neg_kkc h2
  exact .inr ⟨shape_form_kkc ht hu (by omega), shape_form_kkc hu hw (by omega)⟩

/-- On terms of one shape, `cmpF`'s order is transitive. -/
theorem cmpF_trans_shape {κ : Int → Kind} {o : Option Kind} {t u w : T} (ht : EncShape κ o t)
    (hu : EncShape κ o u) (hw : EncShape κ o w) (h1 : cmpF t u = -1) (h2 : cmpF u w = -1) :
    cmpF t w = -1 := by
  induction ht generalizing u w with
  | iv i =>
    rcases cmpF_trans_or_form_kkc (.iv i) hu hw h1 h2 with h | ⟨f1, f2⟩
    · exact h
    cases hu <;> simp only [form_kkc] at f1 <;> try exact absurd f1 (by decide)
    cases hw <;> simp only [form_kkc] at f2 <;> try exact absurd f2 (by decide)
    simp only [cmpF] at h1 h2 ⊢; exact cmpIF_trans_kkc h1 h2
  | bv b =>
    rcases cmpF_trans_or_form_kkc (.bv b) hu hw h1 h2 with h | ⟨f1, f2⟩
    · exact h
    cases hu <;> simp only [form_kkc] at f1 <;> try exact absurd f1 (by decide)
    cases hw <;> simp only [form_kkc] at f2 <;> try exact absurd f2 (by decide)
    simp only [cmpF] at h1 h2 ⊢; exact cmpIF_trans_kkc h1 h2
  | tk s x =>
    rcases cmpF_trans_or_form_kkc (.tk s x) hu hw h1 h2 with h | ⟨f1, f2⟩
    · exact h
    cases hu <;> simp only [form_kkc] at f1 <;> try exact absurd f1 (by decide)
    cases hw <;> simp only [form_kkc] at f2 <;> try exact absurd f2 (by decide)
    rw [cmpF_tk_kkc] at h1 h2 ⊢
    refine lexF_trans_int_kkc (fun _ _ e1 e2 => ?_) h1 h2
    rw [scmpF_eq_neg_kkc] at e1 e2 ⊢; exact lexLt_trans_kkc e1 e2
  | bot =>
    rcases cmpF_trans_or_form_kkc .bot hu hw h1 h2 with h | ⟨f1, f2⟩
    · exact h
    cases hu <;> simp only [form_kkc] at f1 <;> try exact absurd f1 (by decide)
    rw [cmpF_self] at h1; cases h1
  | ap f as has ih =>
    rcases cmpF_trans_or_form_kkc (.ap f as has) hu hw h1 h2 with h | ⟨f1, f2⟩
    · exact h
    cases hu with
    | ap g bs hbs =>
      cases hw with
      | ap g' cs hcs =>
        simp only [cmpF] at h1 h2 ⊢
        refine lexF_trans_int_kkc (fun _ _ e1 e2 => ?_) h1 h2
        exact cmpTsF_trans_kkc (fun a ha b hb => cmpF_eq_zero_shape (has a ha) (hbs b hb))
          (fun b hb c hc => cmpF_eq_zero_shape (hbs b hb) (hcs c hc))
          (fun a ha b hb c hc => ih a ha (hbs b hb) (hcs c hc)) e1 e2
      | _ => simp only [form_kkc] at f2; exact absurd f2 (by decide)
    | _ => simp only [form_kkc] at f1; exact absurd f1 (by decide)
  | ij a b t ht' ih =>
    rcases cmpF_trans_or_form_kkc (.ij a b t ht') hu hw h1 h2 with h | ⟨f1, f2⟩
    · exact h
    cases hu with
    | ij c e u hu' =>
      cases hw with
      | ij c' e' w hw' =>
        simp only [cmpF] at h1 h2 ⊢
        refine lexF_trans_int_kkc (fun _ _ e1 e2 => ?_) h1 h2
        exact lexF_trans_int_kkc (fun _ _ e1 e2 => ih hu' hw' e1 e2) e1 e2
      | _ => simp only [form_kkc] at f2; exact absurd f2 (by decide)
    | _ => simp only [form_kkc] at f1; exact absurd f1 (by decide)
  | co k c es hk hes ih =>
    rcases cmpF_trans_or_form_kkc (.co k c es hk hes) hu hw h1 h2 with h | ⟨f1, f2⟩
    · exact h
    cases hu with
    | co k' d fs hk' hfs =>
      cases hw with
      | co k'' e gs hk'' hgs =>
        simp only [cmpF] at h1 h2 ⊢
        refine lexF_trans_int_kkc (fun e1 e2 r1 r2 => ?_) h1 h2
        subst e1; subst e2
        have : k' = k := hk'.symm.trans hk
        subst this
        have : k'' = k' := hk''.symm.trans hk'
        subst this
        exact cmpTsF_trans_kkc (fun a ha b hb => cmpF_eq_zero_shape (hes a ha) (hfs b hb))
          (fun b hb c hc => cmpF_eq_zero_shape (hfs b hb) (hgs c hc))
          (fun a ha b hb c hc => ih a ha (hfs b hb) (hgs c hc)) r1 r2
      | _ => simp only [form_kkc] at f2; exact absurd f2 (by decide)
    | _ => simp only [form_kkc] at f1; exact absurd f1 (by decide)
  | kv a v ha hv iha ihv =>
    cases hu with
    | el k x hk _ => exact absurd rfl hk
    | kv b x hb hx =>
      cases hw with
      | el k y hk _ => exact absurd rfl hk
      | kv c y hc hy =>
        simp only [cmpF] at h1 h2 ⊢
        exact lexF_trans_kkc cmpF (cmpF_eq_zero_shape ha hb) (cmpF_eq_zero_shape hb hc) (cmpF_self _)
          (iha hb hc) (fun _ _ e1 e2 => ihv hx hy e1 e2) h1 h2
  | el k x hk hx ih =>
    cases hu with
    | kv b x hb hx => exact absurd rfl hk
    | el _ y _ hy =>
      cases hw with
      | kv c z hc hz => exact absurd rfl hk
      | el _ z _ hz => simp only [cmpF] at h1 h2 ⊢; exact ih hy hz h1 h2

/-! ## The encodings of the values sorted in one semantics have one shape -/

/-- The kind `enc` writes for a value of the collection sort numbered `n` in `c`: a map's for a map
or a range map, a set's, a list's. -/
def encKind (c : Semantics) (n : Int) : Kind :=
  match c.collOf n.toNat with
  | some k => match k.kind with
    | .set => .set
    | .list => .list
    | _ => .map
  | none => .map

theorem sortOf_set_inv_kkc {c : Semantics} {s' : Srt} {es : List GroundTerm} {s : Srt}
    (h : c.sortOf (.set s' es) = some s) :
    ∃ k ss, c.collOf s' = some k ∧ k.kind = .set ∧ elemsSorted es = true ∧ c.sortsOf es = some ss := by
  simp only [Semantics.sortOf] at h
  split at h
  · rename_i k ss hk hss
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨k, ss, hk, hc.1.1, hc.1.2, hss⟩
    · cases h
  · cases h

theorem sortOf_list_inv_kkc {c : Semantics} {s' : Srt} {es : List GroundTerm} {s : Srt}
    (h : c.sortOf (.list s' es) = some s) :
    ∃ k ss, c.collOf s' = some k ∧ k.kind = .list ∧ c.sortsOf es = some ss := by
  simp only [Semantics.sortOf] at h
  split at h
  · rename_i k ss hk hss
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨k, ss, hk, hc.1, hss⟩
    · cases h
  · cases h

/-- A literal is written `iv`, `bv`, `tk` or `bot`. -/
theorem enc_dv_cases_kkc (s : Srt) (l : Lit) : (∃ i, enc (.dv s l) = .iv i) ∨
    (∃ b, enc (.dv s l) = .bv b) ∨ (∃ t x, enc (.dv s l) = .tk t x) ∨ enc (.dv s l) = .bot := by
  cases l with
  | tok x => exact .inr (.inr (.inl ⟨s, x, by simp only [enc]⟩))
  | int i =>
    by_cases h : s = Srt.int
    · subst h; exact .inl ⟨i, by simp only [enc]⟩
    · refine .inr (.inr (.inr ?_)); rw [enc.eq_6] <;> simp_all
  | bool b =>
    by_cases h : s = Srt.bool
    · subst h; exact .inr (.inl ⟨b, by simp only [enc]⟩)
    · refine .inr (.inr (.inr ?_)); rw [enc.eq_6] <;> simp_all
  | float p e b => refine .inr (.inr (.inr ?_)); rw [enc.eq_6] <;> simp_all

/-- The encoding of a value sorted in `c` has the shape `encKind c` describes. -/
theorem enc_shape {c : Semantics} {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    EncShape (encKind c) none (enc v) := by
  have hL : ∀ {vs : List GroundTerm} {ss : List Srt}, (∀ v ∈ vs, ∀ s, c.sortOf v = some s →
      EncShape (encKind c) none (enc v)) → c.sortsOf vs = some ss →
      ∀ v ∈ vs, EncShape (encKind c) none (enc v) := by
    intro vs ss ih h v hv
    obtain ⟨s', -, h'⟩ := sortsOf_mem_kel h v hv
    exact ih v hv s' h'
  induction v using gtInd_kel generalizing s with
  | hctor f vs ih =>
    obtain ⟨ss, hss⟩ := c.sortsOf_of_sortOf_ctor hv
    simp only [enc, encTs_eq_map]
    refine .ap _ _ fun a ha => ?_
    obtain ⟨v, hv', rfl⟩ := List.mem_map.mp ha
    exact hL ih hss v hv'
  | hinj a b t ih =>
    obtain ⟨-, -, ht, -⟩ := sortOf_inj_kel hv
    exact .ij _ _ _ (ih ht)
  | hdv s' l =>
    rcases enc_dv_cases_kkc s' l with ⟨i, h⟩ | ⟨b, h⟩ | ⟨t, x, h⟩ | h <;> rw [h]
    · exact .iv _
    · exact .bv _
    · exact .tk _ _
    · exact .bot
  | hmap s' es ih =>
    obtain ⟨k, vs, hk, -, hks, he, -⟩ := c.sortOf_map_inv hv
    simp only [enc, encKvs_eq_map]
    refine .co _ _ _ ?_ fun e he' => ?_
    · simp only [encKind, Int.toNat_natCast, hk]
      revert hks; cases k.kind <;> intro hks <;> first | rfl | cases hks
    · rw [mem_sortK] at he'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
      have := entriesOK_mem_kel he x hx
      exact .kv _ _ ((ih x hx).1 this.1) ((ih x hx).2 this.2)
  | hset s' es ih =>
    obtain ⟨k, ss, hk, hkind, -, hss⟩ := sortOf_set_inv_kkc hv
    simp only [enc, encEls_eq_map]
    refine .co _ _ _ ?_ fun e he' => ?_
    · simp only [encKind, Int.toNat_natCast, hk, hkind]
    · rw [mem_sortK] at he'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
      exact .el _ _ (by decide) (hL ih hss x hx)
  | hlist s' es ih =>
    obtain ⟨k, ss, hk, hkind, hss⟩ := sortOf_list_inv_kkc hv
    simp only [enc, encEls_eq_map]
    refine .co _ _ _ ?_ fun e he' => ?_
    · simp only [encKind, Int.toNat_natCast, hk, hkind]
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
      exact .el _ _ (by decide) (hL ih hss x hx)

/-- On the encodings of values sorted in one semantics, `cmpF`'s order is transitive. -/
theorem cmpF_trans {c : Semantics} {u v w : GroundTerm} {s₁ s₂ s₃ : Srt}
    (hu : c.sortOf u = some s₁) (hv : c.sortOf v = some s₂) (hw : c.sortOf w = some s₃)
    (h1 : cmpF (enc u) (enc v) = -1) (h2 : cmpF (enc v) (enc w) = -1) : cmpF (enc u) (enc w) = -1 :=
  cmpF_trans_shape (enc_shape hu) (enc_shape hv) (enc_shape hw) h1 h2

/-- On the encodings of values sorted in one semantics whose literals have a `kore.k` form, `cmpF`
is 0 exactly between equal values. -/
theorem cmpF_eq_zero_iff {c : Semantics} {v w : GroundTerm} {s s' : Srt}
    (hv : c.sortOf v = some s) (hw : c.sortOf w = some s') (lv : litsV v = true)
    (lw : litsV w = true) : cmpF (enc v) (enc w) = 0 ↔ v = w := by
  rw [cmpF_eq_zero_iff_shape (enc_shape hv) (enc_shape hw)]
  exact ⟨enc_inj hv hw lv lw, congrArg enc⟩

/-! ## `sortK` -/

theorem insK_perm_kkc (e : T) : ∀ fs : List T, (insK e fs).Perm (e :: fs)
  | [] => .refl _
  | f :: fs => by
    unfold insK
    split
    · exact .refl _
    · exact ((insK_perm_kkc e fs).cons f).trans (.swap e f fs)

theorem foldl_insK_perm_kkc : ∀ (L acc : List T),
    (L.foldl (fun acc e => insK e acc) acc).Perm (acc ++ L)
  | [], acc => by simp
  | e :: L, acc => by
    simp only [List.foldl_cons]
    refine (foldl_insK_perm_kkc L _).trans ?_
    exact ((insK_perm_kkc e acc).append_right L).trans List.perm_middle.symm

/-- `sortK` permutes its input. -/
theorem sortK_perm (L : List T) : (sortK L).Perm L := by
  unfold sortK; simpa using foldl_insK_perm_kkc L []

theorem ckeyF_any_kkc {e f : T} : (ckeyF e f).any (· < 0) = true ↔ ckeyF e f = some (-1) := by
  unfold ckeyF
  split
  · rename_i a _ b _
    simp only [Option.any_some, decide_eq_true_eq, Option.some.injEq]
    rcases cmpF_range a b with h | h | h <;> rw [h] <;> decide
  · rename_i x y
    simp only [Option.any_some, decide_eq_true_eq, Option.some.injEq]
    rcases cmpF_range x y with h | h | h <;> rw [h] <;> decide
  · simp

theorem insK_sorted_kkc {S : T → Prop}
    (htr : ∀ a b e, S a → S b → S e → ckeyF a b = some (-1) → ckeyF b e = some (-1) →
      ckeyF a e = some (-1))
    (htot : ∀ a b, S a → S b → a ≠ b → ckeyF a b = some (-1) ∨ ckeyF b a = some (-1))
    {e : T} (he : S e) : ∀ {fs : List T}, (∀ f ∈ fs, S f) → e ∉ fs →
      fs.Pairwise (fun a b => ckeyF a b = some (-1)) →
      (insK e fs).Pairwise fun a b => ckeyF a b = some (-1)
  | [], _, _, _ => List.pairwise_singleton _ _
  | f :: fs, hS, hn, hp => by
    unfold insK
    split
    · rename_i hlt
      rw [ckeyF_any_kkc] at hlt
      refine List.Pairwise.cons (fun g hg => ?_) hp
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hlt
      · exact htr e f g he (hS f (List.mem_cons_self ..)) (hS g (List.mem_cons_of_mem _ hg)) hlt
          (List.rel_of_pairwise_cons hp hg)
    · rename_i hlt
      rw [ckeyF_any_kkc] at hlt
      have hfe : ckeyF f e = some (-1) := by
        rcases htot e f he (hS f (List.mem_cons_self ..))
          (fun h => hn (h ▸ List.mem_cons_self ..)) with h | h
        · exact absurd h hlt
        · exact h
      rw [List.pairwise_cons] at hp
      refine List.Pairwise.cons (fun g hg => ?_)
        (insK_sorted_kkc htr htot he (fun g hg => hS g (List.mem_cons_of_mem _ hg))
          (fun h => hn (List.mem_cons_of_mem _ h)) hp.2)
      rcases mem_insK.mp hg with rfl | hg
      · exact hfe
      · exact hp.1 g hg

/-- `sortK` orders its input by `ckeyF` where `ckeyF` is a strict total order on its members. -/
theorem sortK_sorted {L : List T} (hnd : L.Nodup)
    (htr : ∀ a ∈ L, ∀ b ∈ L, ∀ e ∈ L, ckeyF a b = some (-1) → ckeyF b e = some (-1) →
      ckeyF a e = some (-1))
    (htot : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ckeyF a b = some (-1) ∨ ckeyF b a = some (-1)) :
    (sortK L).Pairwise fun a b => ckeyF a b = some (-1) := by
  have key : ∀ (R acc : List T), (∀ x ∈ acc, x ∈ L) → (∀ x ∈ R, x ∈ L) → (acc ++ R).Nodup →
      acc.Pairwise (fun a b => ckeyF a b = some (-1)) →
      (R.foldl (fun acc e => insK e acc) acc).Pairwise fun a b => ckeyF a b = some (-1) := by
    intro R
    induction R with
    | nil => intro acc _ _ _ h; exact h
    | cons e R ih =>
      intro acc hacc hR hnd' hp
      simp only [List.foldl_cons]
      have he : e ∈ L := hR e (List.mem_cons_self ..)
      have hne : e ∉ acc := by
        intro h
        have := (List.perm_middle.nodup_iff).mp hnd'
        exact (List.nodup_cons.mp this).1 (List.mem_append_left _ h)
      refine ih _ (fun x hx => ?_) (fun x hx => hR x (List.mem_cons_of_mem _ hx)) ?_
        (insK_sorted_kkc (S := (· ∈ L)) (fun a b e ha hb he => htr a ha b hb e he)
          (fun a b ha hb => htot a ha b hb) he hacc hne hp)
      · rcases mem_insK.mp hx with rfl | hx
        · exact he
        · exact hacc x hx
      · exact (((insK_perm_kkc e acc).append_right R).trans List.perm_middle.symm).nodup_iff.mpr hnd'
  exact key L [] (fun _ h => nomatch h) (fun _ h => h) (by simpa using hnd) .nil

/-- The members of a list strictly increasing by a key whose encoding has one shape, mapped to
members whose `ckeyF` is `cmpF` of the keys' encodings: `sortK` orders them strictly. -/
theorem sortK_sorted_keyed_kkc {α : Type} {κ : Int → Kind} {es : List α} (g key : α → T)
    (hnd : es.Nodup) (hck : ∀ a ∈ es, ∀ b ∈ es, ckeyF (g a) (g b) = some (cmpF (key a) (key b)))
    (hsh : ∀ a ∈ es, EncShape κ none (key a)) (hinj : ∀ a ∈ es, ∀ b ∈ es, key a = key b → a = b) :
    (sortK (es.map g)).Pairwise fun a b => ckeyF a b = some (-1) := by
  have hg : ∀ a ∈ es, ∀ b ∈ es, g a = g b → a = b := by
    intro a ha b hb h
    have h1 := hck a ha b hb
    rw [h, hck b hb b hb, cmpF_self, Option.some.injEq] at h1
    exact hinj a ha b hb (cmpF_eq_zero_shape (hsh a ha) (hsh b hb) h1.symm)
  refine sortK_sorted ?_ ?_ ?_
  · exact List.pairwise_map.mpr (hnd.imp_of_mem fun ha hb hne he => hne (hg _ ha _ hb he))
  · intro x hx y hy z hz h1 h2
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
    rw [hck a ha b hb, Option.some.injEq] at h1
    rw [hck b hb e he, Option.some.injEq] at h2
    rw [hck a ha e he, cmpF_trans_shape (hsh a ha) (hsh b hb) (hsh e he) h1 h2]
  · intro x hx y hy hne
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    rw [hck a ha b hb, hck b hb a ha, Option.some.injEq, Option.some.injEq, cmpF_swap (key a)]
    rcases cmpF_range (key a) (key b) with h | h | h
    · exact .inl h
    · exact absurd (congrArg g (hinj a ha b hb (cmpF_eq_zero_shape (hsh a ha) (hsh b hb) h))) hne
    · exact .inr (by rw [h])

/-! ## The canonical form -/

/-- An injection. -/
def isIjT_kkc : T → Bool
  | .ij .. => true
  | _ => false

mutual
/-- The canonical form `kore.k` keeps its terms in: the members of every map and set strictly
increasing by `ckeyF` (so no key twice in a map and no element twice in a set; a list keeps its
order), and no injection directly under an injection. -/
def Canon : T → Prop
  | .ap _ as => CanonL as
  | .hk _ as => CanonL as
  | .cb _ _ ps => CanonL ps
  | .co k _ es => (k ≠ .list → es.Pairwise fun a b => ckeyF a b = some (-1)) ∧ CanonL es
  | .ij _ _ t => isIjT_kkc t = false ∧ Canon t
  | .as t _ => Canon t
  | .el t => Canon t
  | .kv a v => Canon a ∧ Canon v
  | .en t e => Canon t ∧ Canon e
  | .iv _ | .bv _ | .tk _ _ | .vr _ | .bot => True
  termination_by structural t => t
def CanonL : List T → Prop
  | [] => True
  | t :: ts => Canon t ∧ CanonL ts
  termination_by structural ts => ts
end

theorem canonL_iff_kkc : ∀ {ts : List T}, CanonL ts ↔ ∀ t ∈ ts, Canon t
  | [] => by simp [CanonL]
  | t :: ts => by simp [CanonL, canonL_iff_kkc (ts := ts)]

theorem pairwise_total_kkc {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : R a b ∨ R b a := by
  induction h with
  | nil => exact nomatch ha
  | @cons x l hx _ ih =>
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1; exact .inl (hx b h2)
    · subst h2; exact .inr (hx a h1)
    · exact ih h1 h2

theorem enc_isIj_kkc {t : GroundTerm} (h : t.isInj = false) : isIjT_kkc (enc t) = false := by
  cases t with
  | inj => simp [GroundTerm.isInj] at h
  | dv s l => rcases enc_dv_cases_kkc s l with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | h <;> rw [h] <;> rfl
  | _ => simp only [enc]; rfl

/-- `enc` writes a value sorted in `c` whose literals have a `kore.k` form in canonical form. -/
theorem enc_canonical {c : Semantics} {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (lv : litsV v = true) : Canon (enc v) := by
  induction v using gtInd_kel generalizing s with
  | hctor f vs ih =>
    obtain ⟨ss, hss⟩ := c.sortsOf_of_sortOf_ctor hv
    simp only [litsV, litsVL_iff] at lv
    simp only [enc, Canon, canonL_iff_kkc, encTs_eq_map, List.mem_map]
    rintro _ ⟨v, hv', rfl⟩
    obtain ⟨s', -, h'⟩ := sortsOf_mem_kel hss v hv'
    exact ih v hv' h' (lv v hv')
  | hinj a b t ih =>
    obtain ⟨-, hi, ht, -⟩ := sortOf_inj_kel hv
    simp only [litsV] at lv
    simp only [enc, Canon]
    exact ⟨enc_isIj_kkc hi, ih ht lv⟩
  | hdv s' l =>
    rcases enc_dv_cases_kkc s' l with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | h <;> rw [h] <;> simp only [Canon]
  | hmap s' es ih =>
    obtain ⟨k, vs, -, -, hks, he⟩ := sortOf_map_kel hv
    simp only [litsV, litsVE_iff] at lv
    have hp := keysSorted_pairwise_kel hks
    simp only [enc, Canon, encKvs_eq_map, canonL_iff_kkc, mem_sortK, List.mem_map]
    refine ⟨fun _ => ?_, ?_⟩
    · refine sortK_sorted_keyed_kkc (κ := encKind c) (fun e => .kv (enc e.1) (enc e.2))
        (fun e => enc e.1) ?_ (fun _ _ _ _ => rfl) (fun e he' => enc_shape (entriesOK_mem_kel he e he').1)
        (fun e he₁ e' he₂ h => ?_)
      · exact hp.imp_of_mem fun ha hb hlt heq => by
          subst heq; rw [GroundTerm.cmp_refl] at hlt; cases hlt
      · have h1 := enc_inj (entriesOK_mem_kel he e he₁).1 (entriesOK_mem_kel he e' he₂).1 (lv e he₁).1
          (lv e' he₂).1 h
        refine Classical.byContradiction fun hne => ?_
        rcases pairwise_total_kkc hp he₁ he₂ hne with hlt | hlt <;>
          rw [h1, GroundTerm.cmp_refl] at hlt <;> cases hlt
    · rintro _ ⟨e, he', rfl⟩
      have := entriesOK_mem_kel he e he'
      exact ⟨(ih e he').1 this.1 (lv e he').1, (ih e he').2 this.2 (lv e he').2⟩
  | hset s' es ih =>
    obtain ⟨k, ss, -, hks, hss, -⟩ := sortOf_set_kel hv
    simp only [litsV, litsVL_iff] at lv
    have hp := elemsSorted_iff.mp hks
    have hS : ∀ v ∈ es, ∃ s, c.sortOf v = some s := fun v hv =>
      let ⟨s, _, h⟩ := sortsOf_mem_kel hss v hv; ⟨s, h⟩
    simp only [enc, Canon, encEls_eq_map, canonL_iff_kkc, mem_sortK, List.mem_map]
    refine ⟨fun _ => ?_, ?_⟩
    · refine sortK_sorted_keyed_kkc (κ := encKind c) (fun v => .el (enc v)) enc ?_
        (fun _ _ _ _ => rfl) (fun v hv => let ⟨_, h⟩ := hS v hv; enc_shape h) (fun v hv w hw h => ?_)
      · exact hp.imp_of_mem fun ha hb hlt heq => by
          subst heq; rw [GroundTerm.cmp_refl] at hlt; cases hlt
      · obtain ⟨_, h1⟩ := hS v hv
        obtain ⟨_, h2⟩ := hS w hw
        exact enc_inj h1 h2 (lv v hv) (lv w hw) h
    · rintro _ ⟨v, hv', rfl⟩
      obtain ⟨_, h1⟩ := hS v hv'
      exact ih v hv' h1 (lv v hv')
  | hlist s' es ih =>
    obtain ⟨k, ss, -, hss, -⟩ := sortOf_list_kel hv
    simp only [litsV, litsVL_iff] at lv
    simp only [enc, Canon, encEls_eq_map, canonL_iff_kkc, List.mem_map]
    refine ⟨fun h => absurd rfl h, ?_⟩
    rintro _ ⟨v, hv', rfl⟩
    obtain ⟨s', -, h'⟩ := sortsOf_mem_kel hss v hv'
    exact ih v hv' h' (lv v hv')

end KCore.KK
