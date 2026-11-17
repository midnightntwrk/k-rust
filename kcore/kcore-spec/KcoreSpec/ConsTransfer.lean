/-
  The patterns whose interpretation in the extension of a model (`extModel`, ConsExtModel.lean) is
  fixed by their interpretation in the model: the class `OwnSorted`, and the lemma that the
  extension satisfies an `OwnSorted` premise exactly when the model does (`transfer`,
  `transfer_back`).

  A pattern of the class has a kind, which says what its interpretation in the extension is, at a
  valuation that gives the listed element variables old elements and the listed set variables sets
  with the same old elements (`Rel`):
  - `ex`: the old elements the model gives it, and no added element (a term over symbols outside
    `D`, a sort outside `D`, a sorted connective, `μ`);
  - `hd`: the old elements the model gives it, and added elements whose application to an old
    element is empty (`⊤_`, a literal's `dv` symbol, `⌈_⌉{s,_}` at a sort outside `D`);
  - `old`: the old elements the model gives it, whatever added elements it has (a set variable,
    `⟦Sort⟧`);
  - `co`: the old elements the model gives it, and every added element (the negation of an `ex`
    pattern, an implication from one);
  - `pred`: everything or nothing in both, the same in both (definedness, equality, membership,
    inclusion, and their connectives).
  The quantifiers of the class are the sorted ones, at a sort of kind `ex`: such a sort has no
  added element, so the quantifier ranges over the same elements in both.

  A premise `guards → body` whose guards put each free variable in a sort of kind `ex` and whose
  body is of kind `pred` or `co` holds in the extension where it holds in the model (`transfer`):
  at an added element a guard fails. The converse holds for a body of any kind (`transfer_back`).

  A sentence `axiom{R} \equals{S, R}(l, r)` is not of the class: its sort variable `R` also ranges
  over the detached sort names. `transfer_equation` carries it: in the model, at `R := S`, the
  sentence gives that `l` and `r` agree on `S`, and then `⌈¬(l ↔ r)⌉{S,R}` is empty at every `R`.
  `transfer_trAxiom_equals` is that lemma at the translation (`trAxiom`) of such a sentence.

  Not of the class, by shape: an unsorted quantifier (the definedness schema, the step closure's
  `∀y`); a variable guarded by `⟦Sort⟧` (`dvArityAll`, the two items of `⌈_⌉{s,s'}`, the sort
  variable `R` of a function equation, whose connectives are all at `R`); a quantifier over
  `⟦Sort⟧` (a sort constant's item). The detached sort names are added elements of `⟦Sort⟧`, so
  these range over added elements.
-/
import KcoreSpec.ConsExtModel

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort)

/-- What the interpretation of a pattern in the extension is, given its interpretation in the
model (`Inv`). -/
inductive OwnKind where
  | ex
  | hd
  | old
  | co
  | pred

/-- A symbol that has no added element unless it is detached: a sort constant, a symbol of the
definition, next, a string, a marker. -/
def plainSym : KoreAML.Sym → Prop
  | .sort _ | .symbol _ | .next | .str _ | .untranslated _ => True
  | _ => False

/-- `k'` says less than `k`. -/
def OwnKind.le : OwnKind → OwnKind → Prop
  | .ex, .hd | .ex, .old | .hd, .old | .co, .old | .pred, .old => True
  | _, _ => False

/-- **The class.** `OwnSorted D V W k φ`: `φ` is of kind `k`, with its free element variables
among `V` and its free set variables among `W`. -/
inductive OwnSorted (D : KoreAML.Sym → Prop) : List EVar → List SVar → OwnKind → KoreAML.P → Prop
  | evar {V W x} : x ∈ V → OwnSorted D V W .ex (.evar x)
  | svar {V W X} : X ∈ W → OwnSorted D V W .old (.svar X)
  | bot {V W} : OwnSorted D V W .ex ⊥
  | botP {V W} : OwnSorted D V W .pred ⊥
  | sym {V W σ} : plainSym σ → ¬ D σ → OwnSorted D V W .ex (.symbol σ)
  | inh {V W} : OwnSorted D V W .hd (.symbol .inh)
  | dv {V W} (l : String) : OwnSorted D V W .hd (.symbol (.dv l))
  | ceil {V W s} : OwnSorted D V W .ex s → OwnSorted D V W .hd (.symbol .ceil ⬝ s)
  | sorts {V W} : OwnSorted D V W .old KoreAML.sortsDomain
  | appH {V W φ ψ} : OwnSorted D V W .hd φ → OwnSorted D V W .ex ψ → OwnSorted D V W .ex (φ ⬝ ψ)
  | appE {V W φ ψ} : OwnSorted D V W .ex φ → OwnSorted D V W .old ψ → OwnSorted D V W .ex (φ ⬝ ψ)
  | defined {V W k φ} : k = .ex ∨ k = .pred → OwnSorted D V W k φ → OwnSorted D V W .pred ⌈φ⌉
  | impEO {V W φ ψ} : OwnSorted D V W .ex φ → OwnSorted D V W .old ψ → OwnSorted D V W .co (φ ⇒ ψ)
  | impOU {V W φ ψ} : OwnSorted D V W .old φ → OwnSorted D V W .co ψ → OwnSorted D V W .co (φ ⇒ ψ)
  | impUE {V W φ ψ} : OwnSorted D V W .co φ → OwnSorted D V W .ex ψ → OwnSorted D V W .ex (φ ⇒ ψ)
  | impPP {V W φ ψ} : OwnSorted D V W .pred φ → OwnSorted D V W .pred ψ → OwnSorted D V W .pred (φ ⇒ ψ)
  | impOO {V W φ ψ} : OwnSorted D V W .old φ → OwnSorted D V W .old ψ → OwnSorted D V W .old (φ ⇒ ψ)
  | sEx {V V' W k x s φ} : OwnSorted D V' W .ex s → (∀ y ∈ V', y ∈ V ∧ y ≠ x) →
      k = .ex ∨ k = .pred ∨ k = .old → OwnSorted D (x :: V) W k φ →
      OwnSorted D V W k (KoreAML.sExists x s φ)
  | mu {V W X φ} : OwnSorted D V (X :: W) .ex φ → OwnSorted D V W .ex (.mu X φ)
  | weak {V W k k' φ} : OwnKind.le k k' → OwnSorted D V W k φ → OwnSorted D V W k' φ

namespace OwnSorted
variable {D : KoreAML.Sym → Prop} {V : List EVar} {W : List SVar} {φ ψ s s' : KoreAML.P}

/-- More variables may be listed. -/
theorem mono {k : OwnKind} (h : OwnSorted D V W k φ) : ∀ {V2 : List EVar} {W2 : List SVar},
    (∀ x ∈ V, x ∈ V2) → (∀ X ∈ W, X ∈ W2) → OwnSorted D V2 W2 k φ := by
  induction h with
  | evar hx => intro _ _ hV _; exact .evar (hV _ hx)
  | svar hX => intro _ _ _ hW; exact .svar (hW _ hX)
  | bot => intro _ _ _ _; exact .bot
  | botP => intro _ _ _ _; exact .botP
  | sym hp hσ => intro _ _ _ _; exact .sym hp hσ
  | inh => intro _ _ _ _; exact .inh
  | dv l => intro _ _ _ _; exact .dv l
  | ceil _ ih => intro _ _ hV hW; exact .ceil (ih hV hW)
  | sorts => intro _ _ _ _; exact .sorts
  | appH _ _ ih1 ih2 => intro _ _ hV hW; exact .appH (ih1 hV hW) (ih2 hV hW)
  | appE _ _ ih1 ih2 => intro _ _ hV hW; exact .appE (ih1 hV hW) (ih2 hV hW)
  | defined hk _ ih => intro _ _ hV hW; exact .defined hk (ih hV hW)
  | impEO _ _ ih1 ih2 => intro _ _ hV hW; exact .impEO (ih1 hV hW) (ih2 hV hW)
  | impOU _ _ ih1 ih2 => intro _ _ hV hW; exact .impOU (ih1 hV hW) (ih2 hV hW)
  | impUE _ _ ih1 ih2 => intro _ _ hV hW; exact .impUE (ih1 hV hW) (ih2 hV hW)
  | impPP _ _ ih1 ih2 => intro _ _ hV hW; exact .impPP (ih1 hV hW) (ih2 hV hW)
  | impOO _ _ ih1 ih2 => intro _ _ hV hW; exact .impOO (ih1 hV hW) (ih2 hV hW)
  | sEx _ hV' hk _ ihs ih =>
    intro _ _ hV hW
    refine .sEx (ihs (fun _ h => h) hW) (fun y hy => ⟨hV _ (hV' y hy).1, (hV' y hy).2⟩) hk (ih (fun y hy => ?_) hW)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hV _ hy)
  | mu _ ih =>
    intro _ _ hV hW
    refine .mu (ih hV fun Y hY => ?_)
    rcases List.mem_cons.mp hY with rfl | hY
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hW _ hY)
  | weak hk _ ih => intro _ _ hV hW; exact .weak hk (ih hV hW)

/-- A sort constant outside `D`. -/
theorem sortC {n : String} (h : ¬ D (.sort n)) : OwnSorted D V W .ex (KoreAML.sym (.sort n)) := .sym trivial h
/-- A symbol of the definition outside `D`. -/
theorem symC {n : String} (h : ¬ D (.symbol n)) : OwnSorted D V W .ex (KoreAML.sym (.symbol n)) := .sym trivial h

theorem toOld {k : OwnKind} (h : OwnSorted D V W k φ) : OwnSorted D V W .old φ := by
  cases k with
  | old => exact h
  | ex => exact .weak (k := .ex) trivial h
  | hd => exact .weak (k := .hd) trivial h
  | co => exact .weak (k := .co) trivial h
  | pred => exact .weak (k := .pred) trivial h

theorem neg_ex (h : OwnSorted D V W .ex φ) : OwnSorted D V W .co (∼φ) := .impEO h (toOld .bot)
theorem neg_co (h : OwnSorted D V W .co φ) : OwnSorted D V W .ex (∼φ) := .impUE h .bot
theorem neg_pred (h : OwnSorted D V W .pred φ) : OwnSorted D V W .pred (∼φ) := .impPP h .botP
theorem neg_old (h : OwnSorted D V W .old φ) : OwnSorted D V W .old (∼φ) := .impOO h (toOld .bot)

theorem top_pred : OwnSorted D V W .pred (⊤ : KoreAML.P) := neg_pred .botP

theorem conj_ex_old (h1 : OwnSorted D V W .ex φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .ex (φ ⋀ ψ) := neg_co (.impEO (neg_co (neg_ex h1)) (neg_old h2))
theorem conj_old_ex (h1 : OwnSorted D V W .old φ) (h2 : OwnSorted D V W .ex ψ) :
    OwnSorted D V W .ex (φ ⋀ ψ) := neg_co (.impOU (neg_old (neg_old h1)) (neg_ex h2))
theorem conj_co (h1 : OwnSorted D V W .co φ) (h2 : OwnSorted D V W .co ψ) :
    OwnSorted D V W .co (φ ⋀ ψ) := neg_ex (.impUE (neg_ex (neg_co h1)) (neg_co h2))
theorem conj_pred (h1 : OwnSorted D V W .pred φ) (h2 : OwnSorted D V W .pred ψ) :
    OwnSorted D V W .pred (φ ⋀ ψ) := neg_pred (.impPP (neg_pred (neg_pred h1)) (neg_pred h2))
theorem conj_old (h1 : OwnSorted D V W .old φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .old (φ ⋀ ψ) := neg_old (.impOO (neg_old (neg_old h1)) (neg_old h2))

theorem disj_ex (h1 : OwnSorted D V W .ex φ) (h2 : OwnSorted D V W .ex ψ) :
    OwnSorted D V W .ex (φ ⋁ ψ) := .impUE (neg_ex h1) h2
theorem disj_pred (h1 : OwnSorted D V W .pred φ) (h2 : OwnSorted D V W .pred ψ) :
    OwnSorted D V W .pred (φ ⋁ ψ) := .impPP (neg_pred h1) h2
theorem disj_old (h1 : OwnSorted D V W .old φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .old (φ ⋁ ψ) := .impOO (neg_old h1) h2

theorem total_co (h : OwnSorted D V W .co φ) : OwnSorted D V W .pred ⌊φ⌋ :=
  neg_pred (.defined (.inl rfl) (neg_co h))
theorem total_pred (h : OwnSorted D V W .pred φ) : OwnSorted D V W .pred ⌊φ⌋ :=
  neg_pred (.defined (.inr rfl) (neg_pred h))

/-- Equality of two patterns without added elements. -/
theorem equal_ex (h1 : OwnSorted D V W .ex φ) (h2 : OwnSorted D V W .ex ψ) :
    OwnSorted D V W .pred (φ ≡ ψ) :=
  total_co (conj_co (.impEO h1 (toOld h2)) (.impEO h2 (toOld h1)))
theorem equal_pred (h1 : OwnSorted D V W .pred φ) (h2 : OwnSorted D V W .pred ψ) :
    OwnSorted D V W .pred (φ ≡ ψ) :=
  total_pred (conj_pred (.impPP h1 h2) (.impPP h2 h1))

/-- Membership of a listed variable. -/
theorem member {x : EVar} (hx : x ∈ V) (h : OwnSorted D V W .old φ) : OwnSorted D V W .pred (x ∈∈ φ) :=
  .defined (.inl rfl) (conj_ex_old (.evar hx) h)

/-- Inclusion of a pattern without added elements. -/
theorem included (h1 : OwnSorted D V W .ex φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .pred (φ ⊆⊆ ψ) := total_co (.impEO h1 h2)

theorem notEqual_ex (h1 : OwnSorted D V W .ex φ) (h2 : OwnSorted D V W .ex ψ) :
    OwnSorted D V W .pred (KoreAML.notEqual φ ψ) := neg_pred (equal_ex h1 h2)

/-- The inhabitants of a sort without added elements. -/
theorem inhOf (h : OwnSorted D V W .ex s) : OwnSorted D V W .ex (KoreAML.inhOf s) := .appH .inh h

theorem sNot (hs : OwnSorted D V W .ex s) (h : OwnSorted D V W .old φ) :
    OwnSorted D V W .ex (KoreAML.sNot s φ) := conj_old_ex (neg_old h) (inhOf hs)
theorem sAnd (h1 : OwnSorted D V W .ex φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .ex (KoreAML.sAnd φ ψ) := conj_ex_old h1 h2
theorem sOr (hs : OwnSorted D V W .ex s) (h1 : OwnSorted D V W .old φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .ex (KoreAML.sOr s φ ψ) := sNot hs (toOld (sAnd (sNot hs h1) (toOld (sNot hs h2))))
theorem sImp (hs : OwnSorted D V W .ex s) (h1 : OwnSorted D V W .old φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .ex (KoreAML.sImp s φ ψ) := sOr hs (toOld (sNot hs h1)) h2
theorem sIff (hs : OwnSorted D V W .ex s) (h1 : OwnSorted D V W .old φ) (h2 : OwnSorted D V W .old ψ) :
    OwnSorted D V W .ex (KoreAML.sIff s φ ψ) := sAnd (sImp hs h1 h2) (toOld (sImp hs h2 h1))
theorem sCeil (hs : OwnSorted D V W .ex s) (hs' : OwnSorted D V W .ex s') (h : OwnSorted D V W .old φ) :
    OwnSorted D V W .ex (KoreAML.sCeil s s' φ) := .appE (.appH (.ceil hs) hs') h
theorem sFloor (hs : OwnSorted D V W .ex s) (hs' : OwnSorted D V W .ex s') (h : OwnSorted D V W .old φ) :
    OwnSorted D V W .ex (KoreAML.sFloor s s' φ) := sNot hs' (toOld (sCeil hs hs' (toOld (sNot hs h))))
theorem sEquals (hs : OwnSorted D V W .ex s) (hs' : OwnSorted D V W .ex s') (h1 : OwnSorted D V W .old φ)
    (h2 : OwnSorted D V W .old ψ) : OwnSorted D V W .ex (KoreAML.sEquals s s' φ ψ) :=
  sFloor hs hs' (toOld (sIff hs h1 h2))
theorem sIn (hs : OwnSorted D V W .ex s) (hs' : OwnSorted D V W .ex s') (h1 : OwnSorted D V W .old φ)
    (h2 : OwnSorted D V W .old ψ) : OwnSorted D V W .ex (KoreAML.sIn s s' φ ψ) :=
  sCeil hs hs' (conj_old h1 h2)
theorem sNext (hn : ¬ D .next) (h : OwnSorted D V W .old φ) : OwnSorted D V W .ex (KoreAML.sNext φ) :=
  .appE (.sym trivial hn) h

/-- A symbol applied to arguments. -/
theorem appList : ∀ {args : List KoreAML.P} {hd : KoreAML.P}, OwnSorted D V W .ex hd →
    (∀ a ∈ args, OwnSorted D V W .old a) → OwnSorted D V W .ex (KoreAML.appList hd args) := by
  intro args
  induction args with
  | nil => intro hd h _; exact h
  | cons a as ih =>
    intro hd h ha
    exact ih (.appE h (ha a (List.mem_cons_self ..))) (fun b hb => ha b (List.mem_cons_of_mem _ hb))

theorem conjList_pred : ∀ {ws : List KoreAML.P}, (∀ w ∈ ws, OwnSorted D V W .pred w) →
    OwnSorted D V W .pred (KoreAML.conjList ws)
  | [], _ => top_pred
  | [w], h => h w (List.mem_cons_self ..)
  | w :: w' :: ws, h => conj_pred (h w (List.mem_cons_self ..))
      (conjList_pred (ws := w' :: ws) fun v hv => h v (List.mem_cons_of_mem _ hv))

/-- A guarded body: the guards are predicates. -/
theorem guarded {k : OwnKind} {ws : List KoreAML.P} (hw : ∀ w ∈ ws, OwnSorted D V W .pred w)
    (hk : k = .pred ∨ k = .co) (h : OwnSorted D V W k φ) : OwnSorted D V W k (KoreAML.guarded ws φ) := by
  cases ws with
  | nil => exact h
  | cons w ws =>
    rcases hk with rfl | rfl
    · exact .impPP (conjList_pred hw) h
    · exact .impOU (toOld (conjList_pred hw)) h

end OwnSorted

/-! ## The interpretation in the extension -/

section
variable (c : Semantics) (D : KoreAML.Sym → Prop) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M)

/-- What kind `k` says of a set `A` of the model and a set `A'` of the extension. -/
def Inv (k : OwnKind) (A : M → Prop) (A' : Ext M → Prop) : Prop :=
  (∀ m, A' (.inl m) ↔ A m) ∧
  match k with
  | .ex => ∀ n, ¬ A' (.inr n)
  | .hd => ∀ n, A' (.inr n) → ∀ b x, ¬ (extModel c D I).evalApp (.inr n) (.inl b) x
  | .old => True
  | .co => ∀ n, A' (.inr n)
  | .pred => ((∀ m, A m) ∨ (∀ m, ¬ A m)) ∧ ∀ n, (A' (.inr n) ↔ ∀ m, A m)

/-- The valuation `e'` of the extension gives the variables of `V` the old elements `e` gives
them, and the set variables of `W` sets with the old elements `e` gives them. -/
def Rel (V : List EVar) (W : List SVar) (e : Valuation M) (e' : Valuation (Ext M)) : Prop :=
  (∀ x ∈ V, e'.evalEvar x = .inl (e.evalEvar x)) ∧ ∀ X ∈ W, ∀ m, e'.evalSvar X (.inl m) ↔ e.evalSvar X m

variable {c D I}

theorem Inv.congr {k : OwnKind} {A B : M → Prop} {A' B' : Ext M → Prop} (h : Inv c D I k A A')
    (h1 : ∀ m, A m ↔ B m) (h2 : ∀ x, A' x ↔ B' x) : Inv c D I k B B' := by
  have e1 : A = B := funext fun m => propext (h1 m)
  have e2 : A' = B' := funext fun x => propext (h2 x)
  rw [← e1, ← e2]; exact h

theorem Inv.weak {k k' : OwnKind} {A : M → Prop} {A' : Ext M → Prop} (hk : OwnKind.le k k')
    (h : Inv c D I k A A') : Inv c D I k' A A' := by
  cases k <;> cases k' <;> first | exact hk.elim | exact ⟨h.1, trivial⟩ | skip
  exact ⟨h.1, fun n hn => absurd hn (h.2 n)⟩

theorem app_inl_inr {a : M} {n : Added M} {x : Ext M} : ¬ (extModel c D I).evalApp (.inl a) (.inr n) x := by
  intro h; cases n <;> exact h

theorem app_inl_inl_inr {a b : M} {n : Added M} : ¬ (extModel c D I).evalApp (.inl a) (.inl b) (.inr n) :=
  fun h => h

/-- A symbol outside `D` holds of the old elements it held of. -/
theorem sym_old {σ : KoreAML.Sym} (hσ : ¬ D σ) (m : M) :
    (extModel c D I).evalSymb σ (.inl m) ↔ I.evalSymb σ m :=
  (ext_embeds c D I).2.1 σ hσ m

theorem inv_sym {σ : KoreAML.Sym} (hp : plainSym σ) (hσ : ¬ D σ) :
    Inv c D I .ex (I.evalSymb σ) ((extModel c D I).evalSymb σ) := by
  refine ⟨sym_old hσ, fun n h => ?_⟩
  cases n with
  | srt nm => exact hσ (h.2 ▸ h.1)
  | lit l => have h' : σ = .dv l := h; subst h'; exact hp
  | val v => obtain ⟨k, hk, rfl, _⟩ := h; exact hσ hk.2
  | hk f vs => obtain ⟨k, hk, rfl, _⟩ := h; exact hσ hk.2
  | dfn => have h' : σ = .defined := h; subst h'; exact hp
  | inh => have h' : σ = .inh := h; subst h'; exact hp
  | sorts => have h' : σ = .sortSort := h; subst h'; exact hp
  | ceil => have h' : σ = .ceil := h; subst h'; exact hp
  | ceil1 _ => exact h
  | ceil2 _ _ => exact h

/-- The added elements of a symbol that is no sort constant and no symbol of the definition. -/
theorem sym_new {σ : KoreAML.Sym} (hp : ¬ plainSym σ) {n : Added M}
    (h : (extModel c D I).evalSymb σ (.inr n)) :
    (σ = .defined ∧ n = .dfn) ∨ (σ = .inh ∧ n = .inh) ∨ (σ = .sortSort ∧ n = .sorts) ∨
    (σ = .ceil ∧ n = .ceil) ∨ ∃ l, σ = .dv l ∧ n = .lit l := by
  cases n with
  | srt nm => have h' : σ = .sort nm := h.2; subst h'; exact absurd trivial hp
  | lit l => exact .inr (.inr (.inr (.inr ⟨l, h, rfl⟩)))
  | val v => obtain ⟨k, hk, rfl, _⟩ := h; exact absurd trivial hp
  | hk f vs => obtain ⟨k, hk, rfl, _⟩ := h; exact absurd trivial hp
  | dfn => exact .inl ⟨h, rfl⟩
  | inh => exact .inr (.inl ⟨h, rfl⟩)
  | sorts => exact .inr (.inr (.inl ⟨h, rfl⟩))
  | ceil => exact .inr (.inr (.inr (.inl ⟨h, rfl⟩)))
  | ceil1 _ => exact h.elim
  | ceil2 _ _ => exact h.elim

theorem inv_inh (hσ : ¬ D .inh) : Inv c D I .hd (I.evalSymb .inh) ((extModel c D I).evalSymb .inh) := by
  refine ⟨sym_old hσ, fun n h b x hx => ?_⟩
  rcases sym_new (σ := .inh) (fun h => h) h with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ <;>
    first | exact hx | cases h

theorem inv_dv (l : String) (hσ : ¬ D (.dv l)) :
    Inv c D I .hd (I.evalSymb (.dv l)) ((extModel c D I).evalSymb (.dv l)) := by
  refine ⟨sym_old hσ, fun n h b x hx => ?_⟩
  rcases sym_new (σ := .dv l) (fun h => h) h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, rfl⟩ <;>
    first | exact hx | cases h

/-- Application of a head to a pattern without added elements. -/
theorem inv_app_hd {A B : M → Prop} {A' B' : Ext M → Prop} (hA : Inv c D I .hd A A') (hB : Inv c D I .ex B B') :
    Inv c D I .ex (fun m => ∃ a b, A a ∧ B b ∧ I.evalApp a b m)
      (fun x => ∃ a b, A' a ∧ B' b ∧ (extModel c D I).evalApp a b x) := by
  refine ⟨fun m => ⟨?_, ?_⟩, fun n => ?_⟩
  · rintro ⟨a, b, ha, hb, h⟩
    cases b with
    | inr nb => exact absurd hb (hB.2 nb)
    | inl b0 =>
      cases a with
      | inl a0 => exact ⟨a0, b0, (hA.1 a0).mp ha, (hB.1 b0).mp hb, h⟩
      | inr na => exact absurd h (hA.2 na ha b0 _)
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨.inl a, .inl b, (hA.1 a).mpr ha, (hB.1 b).mpr hb, h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    cases b with
    | inr nb => exact absurd hb (hB.2 nb)
    | inl b0 =>
      cases a with
      | inl a0 => exact h
      | inr na => exact absurd h (hA.2 na ha b0 _)

/-- Application of a pattern without added elements. -/
theorem inv_app_ex {A B : M → Prop} {A' B' : Ext M → Prop} (hA : Inv c D I .ex A A') (hB : Inv c D I .old B B') :
    Inv c D I .ex (fun m => ∃ a b, A a ∧ B b ∧ I.evalApp a b m)
      (fun x => ∃ a b, A' a ∧ B' b ∧ (extModel c D I).evalApp a b x) := by
  refine ⟨fun m => ⟨?_, ?_⟩, fun n => ?_⟩
  · rintro ⟨a, b, ha, hb, h⟩
    cases a with
    | inr na => exact absurd ha (hA.2 na)
    | inl a0 =>
      cases b with
      | inl b0 => exact ⟨a0, b0, (hA.1 a0).mp ha, (hB.1 b0).mp hb, h⟩
      | inr nb => exact absurd h app_inl_inr
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨.inl a, .inl b, (hA.1 a).mpr ha, (hB.1 b).mpr hb, h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    cases a with
    | inr na => exact absurd ha (hA.2 na)
    | inl a0 =>
      cases b with
      | inl b0 => exact h
      | inr nb => exact absurd h app_inl_inr

/-- `⌈_⌉{s,_}` at a sort without added elements. -/
theorem inv_ceil (hσ : ¬ D .ceil) {S : M → Prop} {S' : Ext M → Prop} (hS : Inv c D I .ex S S') :
    Inv c D I .hd (fun m => ∃ a b, I.evalSymb .ceil a ∧ S b ∧ I.evalApp a b m)
      (fun x => ∃ a b, (extModel c D I).evalSymb .ceil a ∧ S' b ∧ (extModel c D I).evalApp a b x) := by
  refine ⟨fun m => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨a, b, ha, hb, h⟩
    cases b with
    | inr nb => exact absurd hb (hS.2 nb)
    | inl b0 =>
      cases a with
      | inl a0 => exact ⟨a0, b0, (sym_old hσ a0).mp ha, (hS.1 b0).mp hb, h⟩
      | inr na =>
        rcases sym_new (σ := .ceil) (fun h => h) ha with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨_, h', _⟩ <;>
          first | cases h' | cases h
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨.inl a, .inl b, (sym_old hσ a).mpr ha, (hS.1 b).mpr hb, h⟩
  · rintro n ⟨a, b, ha, hb, h⟩ b1 x hx
    cases b with
    | inr nb => exact absurd hb (hS.2 nb)
    | inl b0 =>
      cases a with
      | inl a0 => exact h
      | inr na =>
        rcases sym_new (σ := .ceil) (fun h => h) ha with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨_, h', _⟩ <;>
          first | cases h' | (cases h; exact hx)

/-- `⟦Sort⟧`: the old sorts, and the detached sort names. -/
theorem inv_sorts (h1 : ¬ D .inh) (h2 : ¬ D .sortSort) :
    Inv c D I .old (fun m => ∃ a b, I.evalSymb .inh a ∧ I.evalSymb .sortSort b ∧ I.evalApp a b m)
      (fun x => ∃ a b, (extModel c D I).evalSymb .inh a ∧ (extModel c D I).evalSymb .sortSort b ∧
        (extModel c D I).evalApp a b x) := by
  refine ⟨fun m => ⟨?_, ?_⟩, trivial⟩
  · rintro ⟨a, b, ha, hb, h⟩
    cases a with
    | inl a0 =>
      cases b with
      | inl b0 => exact ⟨a0, b0, (sym_old h1 a0).mp ha, (sym_old h2 b0).mp hb, h⟩
      | inr nb => exact absurd h app_inl_inr
    | inr na =>
      rcases sym_new (σ := .inh) (fun h => h) ha with ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
        first | cases h' | skip
      cases b with
      | inl b0 => exact h.elim
      | inr nb =>
        rcases sym_new (σ := .sortSort) (fun h => h) hb with ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
          first | cases h' | skip
        obtain ⟨_, _, h⟩ := h
        cases h
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨.inl a, .inl b, (sym_old h1 a).mpr ha, (sym_old h2 b).mpr hb, h⟩

/-- Definedness of a pattern that has an element in the extension exactly when it has one in the
model. -/
theorem inv_defined (hσ : ¬ D .defined) (hI : DefOK I) {A : M → Prop} {A' : Ext M → Prop}
    (hold : ∀ m, A' (.inl m) ↔ A m) (hne : (∃ x, A' x) → ∃ m, A m) :
    Inv c D I .pred (fun m => ∃ a b, I.evalSymb .defined a ∧ A b ∧ I.evalApp a b m)
      (fun x => ∃ a b, (extModel c D I).evalSymb .defined a ∧ A' b ∧ (extModel c D I).evalApp a b x) := by
  have full : (∃ m, A m) → ∀ m, ∃ a b, I.evalSymb .defined a ∧ A b ∧ I.evalApp a b m := by
    rintro ⟨b, hb⟩ m
    obtain ⟨d, hd, happ⟩ := hI b m
    exact ⟨d, b, hd, hb, happ⟩
  refine ⟨fun m => ⟨?_, ?_⟩, ?_, fun n => ⟨?_, ?_⟩⟩
  · rintro ⟨a, b, ha, hb, h⟩
    cases a with
    | inl a0 =>
      cases b with
      | inl b0 => exact ⟨a0, b0, (sym_old hσ a0).mp ha, (hold b0).mp hb, h⟩
      | inr nb => exact absurd h app_inl_inr
    | inr na => exact full (hne ⟨b, hb⟩) m
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨.inl a, .inl b, (sym_old hσ a).mpr ha, (hold b).mpr hb, h⟩
  · by_cases hA : ∃ m, A m
    · exact .inl (full hA)
    · exact .inr fun m ⟨_, b, _, hb, _⟩ => hA ⟨b, hb⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact full (hne ⟨b, hb⟩)
  · intro h
    obtain ⟨_, b, _, hb, _⟩ := h default
    exact ⟨.inr .dfn, .inl b, rfl, (hold b).mpr hb, trivial⟩

/-- A sorted quantifier at a sort without added elements. -/
theorem inv_sEx {k : OwnKind} (hk : k = .ex ∨ k = .pred ∨ k = .old) {G : M → Prop} {F : M → M → Prop}
    {G' : Ext M → Prop} {F' : Ext M → Ext M → Prop} (hG1 : ∀ n, ¬ G' (.inr n)) (hG2 : ∀ a, G' (.inl a) ↔ G a)
    (hF : ∀ a, Inv c D I k (F a) (F' (.inl a))) :
    Inv c D I k (fun m => ∃ a, G a ∧ F a m) (fun x => ∃ a', G' a' ∧ F' a' x) := by
  have hold : ∀ m, (∃ a', G' a' ∧ F' a' (.inl m)) ↔ ∃ a, G a ∧ F a m := fun m => by
    constructor
    · rintro ⟨a', hg, hf⟩
      cases a' with
      | inl a => exact ⟨a, (hG2 a).mp hg, ((hF a).1 m).mp hf⟩
      | inr n => exact absurd hg (hG1 n)
    · rintro ⟨a, hg, hf⟩
      exact ⟨.inl a, (hG2 a).mpr hg, ((hF a).1 m).mpr hf⟩
  rcases hk with rfl | rfl | rfl
  · refine ⟨hold, ?_⟩
    rintro n ⟨a', hg, hf⟩
    cases a' with
    | inl a => exact (hF a).2 n hf
    | inr n' => exact hG1 n' hg
  · refine ⟨hold, ?_, fun n => ⟨?_, ?_⟩⟩
    · by_cases h : ∃ a, G a ∧ ∀ m, F a m
      · obtain ⟨a, hg, hf⟩ := h
        exact .inl fun m => ⟨a, hg, hf m⟩
      · refine .inr ?_
        rintro m ⟨a, hg, hf⟩
        rcases (hF a).2.1 with hall | hnone
        · exact h ⟨a, hg, hall⟩
        · exact hnone m hf
    · rintro ⟨a', hg, hf⟩ m
      cases a' with
      | inl a => exact ⟨a, (hG2 a).mp hg, ((hF a).2.2 n).mp hf m⟩
      | inr n' => exact absurd hg (hG1 n')
    · intro h
      obtain ⟨a, hg, hf⟩ := h default
      rcases (hF a).2.1 with hall | hnone
      · exact ⟨.inl a, (hG2 a).mpr hg, ((hF a).2.2 n).mpr hall⟩
      · exact absurd hf (hnone default)
  · exact ⟨hold, trivial⟩

/-- A least fixed point of a body without added elements. -/
theorem inv_mu {F : (M → Prop) → M → Prop} {F' : (Ext M → Prop) → Ext M → Prop}
    (hF : ∀ (B : M → Prop) (B' : Ext M → Prop), (∀ m, B' (.inl m) ↔ B m) → Inv c D I .ex (F B) (F' B')) :
    Inv c D I .ex (fun m => ∀ B : M → Prop, (∀ m, F B m → B m) → B m)
      (fun x => ∀ B' : Ext M → Prop, (∀ x, F' B' x → B' x) → B' x) := by
  refine ⟨fun m => ⟨fun h B hB => ?_, fun h B' hB' => ?_⟩, fun n h => ?_⟩
  · have hi := hF B (fun x => ∃ m, x = .inl m ∧ B m)
      (fun m => ⟨fun ⟨_, e, h⟩ => Sum.inl.inj e ▸ h, fun h => ⟨m, rfl, h⟩⟩)
    obtain ⟨m', e, hm'⟩ := h (fun x => ∃ m, x = .inl m ∧ B m) (fun x hx => by
      cases x with
      | inl m => exact ⟨m, rfl, hB m ((hi.1 m).mp hx)⟩
      | inr n => exact absurd hx (hi.2 n))
    exact Sum.inl.inj e ▸ hm'
  · have hi := hF (fun m => B' (.inl m)) B' (fun _ => Iff.rfl)
    exact h (fun m => B' (.inl m)) (fun m hm => hB' _ ((hi.1 m).mpr hm))
  · have hi := hF (fun _ => True) (fun x => ∃ m, x = .inl m) (fun m => ⟨fun _ => trivial, fun _ => ⟨m, rfl⟩⟩)
    obtain ⟨_, e⟩ := h (fun x => ∃ m, x = .inl m) (fun x hx => by
      cases x with
      | inl m => exact ⟨m, rfl⟩
      | inr n => exact absurd hx (hi.2 n))
    cases e

omit [Inhabited M] in
theorem interp_sExists' {N : Type} {J : Interpretation KoreAML.Sym N} (hJ : DefOK J) {e : Valuation N}
    {x : EVar} {s φ : KoreAML.P} {m : N} :
    (KoreAML.sExists x s φ).interpret J e m ↔
      ∃ a, (KoreAML.inhOf s).interpret J ⟨Function.update e.evalEvar x a, e.evalSvar⟩ a ∧
        φ.interpret J ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m := by
  rw [KoreAML.interp_sExists]
  constructor
  · rintro ⟨a, h1, h2⟩
    rw [KoreAML.interp_member hJ] at h1
    exact ⟨a, by simpa using h1, h2⟩
  · rintro ⟨a, h1, h2⟩
    refine ⟨a, ?_, h2⟩
    rw [KoreAML.interp_member hJ]
    simpa using h1

/-- **The interpretation of a pattern of the class in the extension**, at related valuations. -/
theorem transfer_rel (hD : ∀ σ, D σ → plainSym σ) (hI : DefOK I) {V : List EVar} {W : List SVar} {k : OwnKind}
    {φ : KoreAML.P} (h : OwnSorted D V W k φ) :
    ∀ (e : Valuation M) (e' : Valuation (Ext M)), Rel V W e e' →
      Inv c D I k (φ.interpret I e) (φ.interpret (extModel c D I) e') := by
  have nD : ∀ {σ}, ¬ plainSym σ → ¬ D σ := fun hp hσ => hp (hD _ hσ)
  induction h with
  | evar hx =>
    intro e e' hr
    refine ⟨fun m => ?_, fun n hn => ?_⟩
    · show Sum.inl m = e'.evalEvar _ ↔ m = e.evalEvar _
      rw [hr.1 _ hx]
      exact ⟨fun h => Sum.inl.inj h, fun h => h ▸ rfl⟩
    · have hn' : Sum.inr n = e'.evalEvar _ := hn
      rw [hr.1 _ hx] at hn'
      cases hn'
  | svar hX => intro e e' hr; exact ⟨hr.2 _ hX, trivial⟩
  | bot => intro e e' _; exact ⟨fun _ => Iff.rfl, fun _ h => h⟩
  | botP =>
    intro e e' _
    exact ⟨fun _ => Iff.rfl, .inr fun _ h => h, fun _ => ⟨fun h => h.elim, fun h => h default⟩⟩
  | sym hp hσ => intro e e' _; exact inv_sym hp hσ
  | inh => intro e e' _; exact inv_inh (nD (σ := .inh) fun h => h)
  | dv l => intro e e' _; exact inv_dv l (nD (σ := .dv l) fun h => h)
  | ceil _ ih => intro e e' hr; exact inv_ceil (nD (σ := .ceil) fun h => h) (ih e e' hr)
  | sorts => intro e e' _; exact inv_sorts (nD (σ := .inh) fun h => h) (nD (σ := .sortSort) fun h => h)
  | appH _ _ ih1 ih2 => intro e e' hr; exact inv_app_hd (ih1 e e' hr) (ih2 e e' hr)
  | appE _ _ ih1 ih2 => intro e e' hr; exact inv_app_ex (ih1 e e' hr) (ih2 e e' hr)
  | defined hk _ ih =>
    intro e e' hr
    have hi := ih e e' hr
    refine inv_defined (nD (σ := .defined) fun h => h) hI hi.1 ?_
    rintro ⟨x, hx⟩
    cases x with
    | inl m => exact ⟨m, (hi.1 m).mp hx⟩
    | inr n =>
      rcases hk with rfl | rfl
      · exact absurd hx (hi.2 n)
      · exact ⟨default, (hi.2.2 n).mp hx default⟩
  | impEO _ _ ih1 ih2 =>
    intro e e' hr
    have h1 := ih1 e e' hr
    have h2 := ih2 e e' hr
    exact ⟨fun m => by simp only [Pattern.interpret]; rw [h1.1 m, h2.1 m],
      fun n hn => absurd hn (h1.2 n)⟩
  | impOU _ _ ih1 ih2 =>
    intro e e' hr
    have h1 := ih1 e e' hr
    have h2 := ih2 e e' hr
    exact ⟨fun m => by simp only [Pattern.interpret]; rw [h1.1 m, h2.1 m], fun n _ => h2.2 n⟩
  | impUE _ _ ih1 ih2 =>
    intro e e' hr
    have h1 := ih1 e e' hr
    have h2 := ih2 e e' hr
    exact ⟨fun m => by simp only [Pattern.interpret]; rw [h1.1 m, h2.1 m],
      fun n hn => h2.2 n (hn (h1.2 n))⟩
  | impPP _ _ ih1 ih2 =>
    intro e e' hr
    have h1 := ih1 e e' hr
    have h2 := ih2 e e' hr
    refine ⟨fun m => by simp only [Pattern.interpret]; rw [h1.1 m, h2.1 m], ?_, fun n => ?_⟩
    · rcases h2.2.1 with hall | hnone
      · exact .inl fun m _ => hall m
      · rcases h1.2.1 with hall1 | hnone1
        · exact .inr fun m hm => hnone m (hm (hall1 m))
        · exact .inl fun m hm => absurd hm (hnone1 m)
    · show (_ → _) ↔ ∀ m, (_ → _)
      rw [h1.2.2 n, h2.2.2 n]
      constructor
      · intro h m hm
        rcases h1.2.1 with hall1 | hnone1
        · exact h hall1 m
        · exact absurd hm (hnone1 m)
      · intro h hall1 m
        exact h m (hall1 m)
  | impOO _ _ ih1 ih2 =>
    intro e e' hr
    have h1 := ih1 e e' hr
    have h2 := ih2 e e' hr
    exact ⟨fun m => by simp only [Pattern.interpret]; rw [h1.1 m, h2.1 m], trivial⟩
  | @sEx V V' W k x s φ _ hV' hk _ ihs ihφ =>
    intro e e' hr
    have hG : ∀ a a', Inv c D I .ex
        ((KoreAML.inhOf s).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩)
        ((KoreAML.inhOf s).interpret (extModel c D I) ⟨Function.update e'.evalEvar x a', e'.evalSvar⟩) :=
      fun a a' => inv_app_hd (inv_inh (nD (σ := .inh) fun h => h)) (ihs _ _ ⟨fun y hy => by
        have := hV' y hy
        show Function.update e'.evalEvar x a' y = .inl (Function.update e.evalEvar x a y)
        rw [Function.update_noteq this.2, Function.update_noteq this.2]
        exact hr.1 y this.1, hr.2⟩)
    refine Inv.congr (inv_sEx hk (G := fun a => (KoreAML.inhOf s).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ a)
      (F := fun a => φ.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩)
      (G' := fun a' => (KoreAML.inhOf s).interpret (extModel c D I) ⟨Function.update e'.evalEvar x a', e'.evalSvar⟩ a')
      (F' := fun a' => φ.interpret (extModel c D I) ⟨Function.update e'.evalEvar x a', e'.evalSvar⟩)
      (fun n => (hG default (.inr n)).2 n) (fun a => (hG a (.inl a)).1 a) (fun a => ihφ _ _ ⟨fun y hy => ?_, hr.2⟩))
      (fun m => (interp_sExists' hI).symm) (fun m => (interp_sExists' (ext_defOK c D I)).symm)
    show Function.update e'.evalEvar x (.inl a) y = .inl (Function.update e.evalEvar x a y)
    by_cases hy' : y = x
    · subst hy'; rw [Function.update_same, Function.update_same]
    · rw [Function.update_noteq hy', Function.update_noteq hy']
      rcases List.mem_cons.mp hy with h | h
      · exact absurd h hy'
      · exact hr.1 y h
  | @mu V W X φ _ ih =>
    intro e e' hr
    refine inv_mu (F := fun B => φ.interpret I ⟨e.evalEvar, Function.update e.evalSvar X B⟩)
      (F' := fun B' => φ.interpret (extModel c D I) ⟨e'.evalEvar, Function.update e'.evalSvar X B'⟩)
      (fun B B' hB => ih _ _ ⟨hr.1, fun Y hY m => ?_⟩)
    show Function.update e'.evalSvar X (B' : Set (Ext M)) Y (.inl m) ↔ Function.update e.evalSvar X (B : Set M) Y m
    by_cases hY' : Y = X
    · subst hY'
      have h1 : Function.update e'.evalSvar Y (B' : Set (Ext M)) Y = B' := Function.update_same ..
      have h2 : Function.update e.evalSvar Y (B : Set M) Y = B := Function.update_same ..
      rw [h1, h2]; exact hB m
    · have h1 : Function.update e'.evalSvar X (B' : Set (Ext M)) Y = e'.evalSvar Y := Function.update_noteq hY' ..
      have h2 : Function.update e.evalSvar X (B : Set M) Y = e.evalSvar Y := Function.update_noteq hY' ..
      rw [h1, h2]
      rcases List.mem_cons.mp hY with h | h
      · exact absurd h hY'
      · exact hr.2 Y h m
  | weak hk _ ih => intro e e' hr; exact (ih e e' hr).weak hk

/-! ## Premises -/

omit [Inhabited M] in
theorem conjList_iff {N : Type} {J : Interpretation KoreAML.Sym N} {e : Valuation N} {m : N}
    {ws : List KoreAML.P} : (KoreAML.conjList ws).interpret J e m ↔ ∀ w ∈ ws, w.interpret J e m := by
  induction ws with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => KoreAML.interp_conjList fun _ h => absurd h List.not_mem_nil⟩
  | cons w ws ih =>
    cases ws with
    | nil =>
      exact ⟨fun h v hv => by rcases List.mem_cons.mp hv with rfl | hv; exact h; exact absurd hv List.not_mem_nil,
        fun h => h w (List.mem_cons_self ..)⟩
    | cons w' ws' =>
      unfold KoreAML.conjList
      rw [interpret_conj, ih]
      exact ⟨fun h v hv => by rcases List.mem_cons.mp hv with rfl | hv; exact h.1; exact h.2 v hv,
        fun h => ⟨h w (List.mem_cons_self ..), fun v hv => h v (List.mem_cons_of_mem _ hv)⟩⟩

omit [Inhabited M] in
theorem guarded_iff {N : Type} {J : Interpretation KoreAML.Sym N} {e : Valuation N} {m : N}
    {ws : List KoreAML.P} {φ : KoreAML.P} :
    (KoreAML.guarded ws φ).interpret J e m ↔ ((∀ w ∈ ws, w.interpret J e m) → φ.interpret J e m) := by
  cases ws with
  | nil => exact ⟨fun h _ => h, fun h => h fun _ hw => absurd hw List.not_mem_nil⟩
  | cons w ws =>
    show (KoreAML.conjList (w :: ws) ⇒ φ).interpret J e m ↔ _
    rw [interpret_impl, conjList_iff]

/-- The old part of a valuation of the extension. -/
def pullVal (e' : Valuation (Ext M)) : Valuation M :=
  ⟨fun x => match e'.evalEvar x with
    | .inl m => m
    | .inr _ => default,
   fun X m => e'.evalSvar X (.inl m)⟩

/-- A valuation of the model, in the extension. -/
def liftVal (e : Valuation M) : Valuation (Ext M) :=
  ⟨fun x => .inl (e.evalEvar x), fun X x => ∃ m, x = .inl m ∧ e.evalSvar X m⟩

omit [Inhabited M] in
theorem rel_lift (V : List EVar) (W : List SVar) (e : Valuation M) : Rel V W e (liftVal e) :=
  ⟨fun _ _ => rfl, fun _ _ m => ⟨fun ⟨_, h1, h2⟩ => Sum.inl.inj h1 ▸ h2, fun h => ⟨m, rfl, h⟩⟩⟩

omit [Inhabited M] in
theorem rel_nil (e : Valuation M) (e' : Valuation (Ext M)) : Rel [] [] e e' :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem nil_sub {α : Type} {p : α → Prop} : ∀ x ∈ ([] : List α), p x := fun _ h => absurd h List.not_mem_nil

/-- The guards `x ∈ ⟦s⟧` of the pairs `gs`. -/
def memGs (gs : List (EVar × KoreAML.P)) : List KoreAML.P := gs.map fun p => p.1 ∈∈ KoreAML.inhOf p.2

section
variable (hD : ∀ σ, D σ → plainSym σ) (hI : DefOK I) {gs : List (EVar × KoreAML.P)}
  (hs : ∀ p ∈ gs, OwnSorted D [] [] .ex p.2)
include hD hI hs

/-- Where the guards hold in the extension, the guarded variables have old elements, in their
sorts. -/
theorem guards_old {e' : Valuation (Ext M)} {pt : Ext M}
    (hw : ∀ w ∈ memGs gs, w.interpret (extModel c D I) e' pt) (e0 : Valuation M) :
    ∀ p ∈ gs, ∃ m, e'.evalEvar p.1 = .inl m ∧ (KoreAML.inhOf p.2).interpret I e0 m := by
  intro p hp
  have h := hw _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [KoreAML.interp_member (ext_defOK c D I)] at h
  have hi : Inv c D I .ex ((KoreAML.inhOf p.2).interpret I e0) ((KoreAML.inhOf p.2).interpret (extModel c D I) e') :=
    inv_app_hd (inv_inh fun hσ => (hD _ hσ : plainSym .inh)) (transfer_rel (c := c) hD hI (hs p hp) e0 e' (rel_nil _ _))
  cases hx : e'.evalEvar p.1 with
  | inl m => rw [hx] at h; exact ⟨m, rfl, (hi.1 m).mp h⟩
  | inr n => rw [hx] at h; exact absurd h (hi.2 n)

/-- **Transfer.** A guarded premise of the class that the model satisfies holds in the extension. -/
theorem transfer {body : KoreAML.P} {k : OwnKind} (hb : OwnSorted D (gs.map (·.1)) [] k body)
    (hk : k = .pred ∨ k = .co) (h : I ⊧ᴵ KoreAML.guarded (memGs gs) body) :
    extModel c D I ⊧ᴵ KoreAML.guarded (memGs gs) body := by
  intro e' pt
  rw [guarded_iff]
  intro hw
  have hold := guards_old hD hI hs hw (pullVal e')
  have hval : ∀ p ∈ gs, e'.evalEvar p.1 = .inl ((pullVal e').evalEvar p.1) := fun p hp => by
    obtain ⟨m, hm, _⟩ := hold p hp
    show _ = Sum.inl (match e'.evalEvar p.1 with | .inl m => m | .inr _ => default)
    rw [hm]
  have hrel : Rel (gs.map (·.1)) [] (pullVal e') e' :=
    ⟨fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hval p hp, nil_sub⟩
  have hbody : ∀ m, body.interpret I (pullVal e') m := fun m =>
    guarded_iff.mp (h (pullVal e') m) fun w hw' => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
      rw [KoreAML.interp_member hI]
      obtain ⟨m0, hm0, hin⟩ := hold p hp
      have := hval p hp
      rw [hm0] at this
      rw [← Sum.inl.inj this]
      exact hin
  have hinv := transfer_rel (c := c) hD hI hb (pullVal e') e' hrel
  rcases hk with rfl | rfl
  · cases pt with
    | inl m => exact (hinv.1 m).mpr (hbody m)
    | inr n => exact (hinv.2.2 n).mpr hbody
  · cases pt with
    | inl m => exact (hinv.1 m).mpr (hbody m)
    | inr n => exact hinv.2 n

/-- **Transfer, back.** A guarded premise of the class, of any kind, that the extension satisfies
holds in the model. -/
theorem transfer_back {body : KoreAML.P} {k : OwnKind} (hb : OwnSorted D (gs.map (·.1)) [] k body)
    (h : extModel c D I ⊧ᴵ KoreAML.guarded (memGs gs) body) : I ⊧ᴵ KoreAML.guarded (memGs gs) body := by
  intro e m
  rw [guarded_iff]
  intro hw
  have h1 := guarded_iff.mp (h (liftVal e) (.inl m)) fun w hw' => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
    rw [KoreAML.interp_member (ext_defOK c D I)]
    have hi : Inv c D I .ex ((KoreAML.inhOf p.2).interpret I e)
        ((KoreAML.inhOf p.2).interpret (extModel c D I) (liftVal e)) :=
      inv_app_hd (inv_inh fun hσ => (hD _ hσ : plainSym .inh)) (transfer_rel (c := c) hD hI (hs p hp) e _ (rel_lift _ _ e))
    have h2 := hw _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [KoreAML.interp_member hI] at h2
    exact (hi.1 _).mpr h2
  exact ((transfer_rel (c := c) hD hI hb e _ (rel_lift _ _ e)).1 m).mp h1

/-- **Transfer of a sentence `axiom{R} \equals{S, R}(l, r)`**, whose sort variable `R` ranges over
the detached sort names too: the extension satisfies it where the model does, for a model of
`ceilDefItem` in which `S` is a sort. -/
theorem transfer_equation (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) {R : EVar} {S L Rr : KoreAML.P}
    (hR : R ∉ gs.map (·.1)) (hS : OwnSorted D [] [] .ex S)
    (hSs : ∃ σ, IsSort I σ ∧ ∀ (e : Valuation M) (a : M), S.interpret I e a ↔ a = σ)
    (hL : OwnSorted D (gs.map (·.1)) [] .old L) (hRr : OwnSorted D (gs.map (·.1)) [] .old Rr)
    (h : I ⊧ᴵ KoreAML.guarded (KoreAML.sortGuard R :: memGs gs)
      (KoreAML.sEquals S (.evar R) L Rr ≡ KoreAML.inhOf (.evar R))) :
    extModel c D I ⊧ᴵ KoreAML.guarded (KoreAML.sortGuard R :: memGs gs)
      (KoreAML.sEquals S (.evar R) L Rr ≡ KoreAML.inhOf (.evar R)) := by
  obtain ⟨σ, hσ, hSσ⟩ := hSs
  intro e' pt
  rw [guarded_iff]
  intro hw
  have hwg : ∀ w ∈ memGs gs, w.interpret (extModel c D I) e' pt := fun w hw' => hw w (List.mem_cons_of_mem _ hw')
  cases hRv : e'.evalEvar R with
  | inl r =>
    -- every variable has an old element: the sentence is of the class
    have hold := guards_old hD hI hs hwg (pullVal e')
    have hval : ∀ x ∈ R :: gs.map (·.1), e'.evalEvar x = .inl ((pullVal e').evalEvar x) := fun x hx => by
      show _ = Sum.inl (match e'.evalEvar x with | .inl m => m | .inr _ => default)
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hRv]
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨m, hm, _⟩ := hold p hp
        rw [hm]
    have hcls : OwnSorted D (R :: gs.map (·.1)) [] .pred (KoreAML.guarded (KoreAML.sortGuard R :: memGs gs)
        (KoreAML.sEquals S (.evar R) L Rr ≡ KoreAML.inhOf (.evar R))) := by
      have sub : ∀ x ∈ gs.map (·.1), x ∈ R :: gs.map (·.1) := fun x hx => List.mem_cons_of_mem _ hx
      refine .guarded (fun w hw' => ?_) (.inl rfl) (.equal_ex
        (.sEquals (hS.mono nil_sub nil_sub) (.evar (List.mem_cons_self ..))
          (hL.mono sub fun _ h => h) (hRr.mono sub fun _ h => h))
        (.inhOf (.evar (List.mem_cons_self ..))))
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact .member (List.mem_cons_self ..) .sorts
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
        exact .member (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (((hs p hp).mono nil_sub nil_sub).inhOf.toOld)
    have hinv := transfer_rel (c := c) hD hI hcls (pullVal e') e' ⟨hval, nil_sub⟩
    have hfull : ∀ m, (KoreAML.guarded (KoreAML.sortGuard R :: memGs gs)
        (KoreAML.sEquals S (.evar R) L Rr ≡ KoreAML.inhOf (.evar R))).interpret I (pullVal e') m := h (pullVal e')
    have hpt : (KoreAML.guarded (KoreAML.sortGuard R :: memGs gs)
        (KoreAML.sEquals S (.evar R) L Rr ≡ KoreAML.inhOf (.evar R))).interpret (extModel c D I) e' pt := by
      cases pt with
      | inl m => exact (hinv.1 m).mpr (hfull m)
      | inr n => exact (hinv.2.2 n).mpr hfull
    exact guarded_iff.mp hpt hw
  | inr n =>
    -- `R` is a detached sort's name: `l` and `r` agree on `S` in the model, so in the extension
    let e : Valuation M := ⟨fun x => if x = R then σ else (pullVal e').evalEvar x, (pullVal e').evalSvar⟩
    have heR : e.evalEvar R = σ := by show (if R = R then σ else _) = σ; simp
    have hold := guards_old hD hI hs hwg e
    have hval : ∀ p ∈ gs, e'.evalEvar p.1 = .inl (e.evalEvar p.1) := fun p hp => by
      have hne : p.1 ≠ R := fun hh => hR (hh ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨m, hm, _⟩ := hold p hp
      show _ = Sum.inl (if p.1 = R then σ else match e'.evalEvar p.1 with | .inl m => m | .inr _ => default)
      simp only [hne, ↓reduceIte, hm]
    have hrel : Rel (gs.map (·.1)) [] e e' :=
      ⟨fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hval p hp, nil_sub⟩
    have hRσ : ∀ a, (Pattern.evar R : KoreAML.P).interpret I e a ↔ a = σ := fun a => by
      rw [KoreAML.interp_evar, heR]
    have hI1 := guarded_iff.mp (h e default) fun w hw' => by
      rcases List.mem_cons.mp hw' with rfl | hw'
      · unfold KoreAML.sortGuard
        rw [KoreAML.interp_member hI, KoreAML.interp_sortsDomain, heR]
        exact hσ
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
        rw [KoreAML.interp_member hI]
        obtain ⟨m0, hm0, hin⟩ := hold p hp
        have := hval p hp
        rw [hm0] at this
        rw [← Sum.inl.inj this]
        exact hin
    rw [KoreAML.interp_equal hI] at hI1
    have hLR : ∀ b, Inh I σ b → (L.interpret I e b ↔ Rr.interpret I e b) := fun b hb =>
      ((KoreAML.interp_sEquals hI hc (hSσ e) hRσ hσ hσ b).mp
        ((hI1 b).mpr ((KoreAML.interp_inhOf_of hRσ).mpr hb))).2 b hb
    have hΨ : ∀ b, ¬ (KoreAML.sNot S (KoreAML.sIff S L Rr)).interpret I e b := fun b hb => by
      rw [KoreAML.interp_sNot, KoreAML.interp_sIff] at hb
      exact hb.1 ⟨hb.2, hLR b ((KoreAML.interp_inhOf_of (hSσ e)).mp hb.2)⟩
    have hcls : OwnSorted D (gs.map (·.1)) [] .ex (KoreAML.sNot S (KoreAML.sIff S L Rr)) :=
      .sNot (hS.mono nil_sub nil_sub)
        (.toOld (.sIff (hS.mono nil_sub nil_sub) hL hRr))
    have hinv := transfer_rel (c := c) hD hI hcls e e' hrel
    have hΨ' : ∀ x, ¬ (KoreAML.sNot S (KoreAML.sIff S L Rr)).interpret (extModel c D I) e' x := fun x hx => by
      cases x with
      | inl b => exact hΨ b ((hinv.1 b).mp hx)
      | inr n' => exact hinv.2 n' hx
    rw [KoreAML.interp_equal (ext_defOK c D I)]
    intro x
    unfold KoreAML.sEquals KoreAML.sFloor
    rw [KoreAML.interp_sNot]
    refine ⟨fun hx => hx.2, fun hx => ⟨fun hc' => ?_, hx⟩⟩
    rw [KoreAML.interp_sCeil_raw] at hc'
    obtain ⟨_, _, y, _, _, hy, _⟩ := hc'
    exact hΨ' y hy

end

end

end KCore.Cons
