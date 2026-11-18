/-
  The equations of the cell tree's initializers and of the counter's getter, at the value models:
  symbols the semantics does not number, of any arity, whose equations' right sides apply one
  another down the cell tree.

  - **Several arguments (`collectApp`, `partialsOf`).** A name `n` of arity `ar n` applied to its
    arguments one at a time: its head applied to fewer than `ar n` elements is the head with them
    collected (`.app (.sym n) args`), and at `ar n` of them, all values, the partial function
    `G n` at their values. Where no symbol resolves to the name, the value model gives no element
    of that form but from the definedness element (`spare_partials`), so the patch of `patch` at
    them is invisible to every rooted pattern that names none of the names.
  - **Constants (`initPatch`).** A symbol without arguments is its own element, not an
    application, so a name of arity 0 is patched in the interpretation of the symbols: it denotes
    the value `G n []`, or nothing. A pattern that names none of the names denotes what it denotes
    in the value model (`initPatch_interpret`, by `interpret_symb_congr` and `patch_interpret`).
  - **The model (`model_with_inits_step`).** For a semantics `coreOK` accepts under `FnHyp`, and
    names that are no symbol's of the semantics (nor `inj` or `Lblite`): one model of the theory,
    whose steps at configurations are `Step`'s, in which every value denotes its own element and
    the name `n` applied to values `ws` of length `ar n` denotes exactly the value `G n ws`, and
    nothing where `G n ws` is `none` (`InitModel`).
  - **Down the tree.** In such a model a right side's denotation is computed from its arguments'
    (`DenV`: exactly a value; `DenE`: nothing): a constructor or `inj` over arguments that denote
    values denotes the value they build (`InitModel.ctor`, `InitModel.inj`), an interpreted symbol
    at values its graph's value or nothing (`InitModel.hookV`, `InitModel.hookE`, from the
    theory's graph premise), a name of `N` `G`'s value or nothing (`InitModel.name`,
    `InitModel.name_none`), and an application with an argument that denotes nothing denotes
    nothing (`DenE.app`). An equation holds where both sides denote the same value
    (`InitModel.eqn`), and where both denote nothing (`InitModel.eqn_none`, a right side with no
    value). So an initializer's equation `L(x̄) = t` holds at values `ws` where `G L ws` is the
    value `t` has at `ws` with the initializers below read through `G`, and nothing where `t` has
    none: `G` is defined by recursion on the cell tree, bottom up. A right side that denotes a
    value satisfies the `functional` axiom `∃x:s. x = t` (`InitModel.functional`).

  The statements are at the value models, as `model_with_eqns`'.
-/
import KcoreSpec.GenEqsWalk

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

open Faithful.Model

/-! ## Interpretations that agree on the symbols a pattern names -/

/-- **Two interpretations with the same application denote the same at a pattern where they
agree on its symbols.** -/
theorem interpret_symb_congr {M : Type} (I J : Interpretation KoreAML.Sym M) (happ : I.evalApp = J.evalApp) :
    ∀ (φ : KoreAML.P), (∀ σ ∈ psyms φ, I.evalSymb σ = J.evalSymb σ) →
      ∀ ρ : Valuation M, φ.interpret I ρ = φ.interpret J ρ
  | .evar _, _, _ => rfl
  | .svar _, _, _ => rfl
  | .bottom, _, _ => rfl
  | .symbol σ, h, _ => h σ (by simp [psyms])
  | .implication a b, h, ρ => by
    simp only [psyms, List.mem_append] at h
    have iha := interpret_symb_congr I J happ a (fun σ hσ => h σ (.inl hσ)) ρ
    have ihb := interpret_symb_congr I J happ b (fun σ hσ => h σ (.inr hσ)) ρ
    show (fun m => a.interpret I ρ m → b.interpret I ρ m) = (fun m => a.interpret J ρ m → b.interpret J ρ m)
    rw [iha, ihb]
  | .application a b, h, ρ => by
    simp only [psyms, List.mem_append] at h
    have iha := interpret_symb_congr I J happ a (fun σ hσ => h σ (.inl hσ)) ρ
    have ihb := interpret_symb_congr I J happ b (fun σ hσ => h σ (.inr hσ)) ρ
    funext m
    simp only [Pattern.interpret, iha, ihb, happ]
  | .existential x a, h, ρ => by
    have ih := interpret_symb_congr I J happ a h
    funext m
    simp only [Pattern.interpret, ih]
  | .mu X a, h, ρ => by
    have ih := interpret_symb_congr I J happ a h
    funext m
    simp only [Pattern.interpret, ih]

/-! ## Names no symbol resolves to -/

/-- No symbol resolves to the name `n` at any arguments: it is neither `inj`'s nor `Lblite`'s, and
no symbol of `kernelSyms` has it. -/
def unresolvedB (c : Semantics) (n : String) : Bool :=
  n != "inj" && n != "Lblite" && (resolve c n []).isNone

theorem resolve_none {c : Semantics} {n : String} (h : unresolvedB c n = true) (args : List Elem) :
    resolve c n args = none := by
  simp only [unresolvedB, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨-, hl⟩, hr⟩ := h
  have he : ∀ as : List Elem, resolve c n as = ((kernelSyms c).find? fun k => c.symName k.name == n).map (·, 0) := by
    intro as
    unfold resolve
    split
    · exact absurd rfl hl
    · rfl
  rw [he]; rw [he] at hr; exact hr

theorem spareSymB_of_unresolved {c : Semantics} {n : String} (h : unresolvedB c n = true) : spareSymB c n = true := by
  have hi : n ≠ "inj" := by
    simp only [unresolvedB, Bool.and_eq_true, bne_iff_ne] at h; exact h.1.1
  simp only [spareSymB, resolve_none h [], Bool.and_true]
  exact bne_iff_ne.mpr hi

/-- A name no symbol bears, other than `inj` and `Lblite`, is unresolved. -/
theorem unresolvedB_of_unnumbered (c : Semantics) {n : String}
    (hn : (regSymNames ++ c.symNames).contains n = false) (he : n ≠ "") (hi : n ≠ "inj") (hl : n ≠ "Lblite") :
    unresolvedB c n = true := by
  have hres : resolve c n [] = none := by
    unfold resolve
    split
    · rename_i h; cases h
    · rw [Option.map_eq_none_iff, List.find?_eq_none]
      intro k _ hk
      exact symName_ne_of_unnumbered c hn he k.name (beq_iff_eq.mp hk)
  simp only [unresolvedB, hres, Option.isNone_none, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨hi, hl⟩

/-! ## The partial applications of the names, in the value model -/

/-- A symbol holds of an application element only at no arguments. -/
theorem evalSymb_nil {c : Semantics} {τ : KoreAML.Sym} {h : Head} {args : List Elem}
    (hx : evalSymb c τ (.app h args)) : args = [] := by
  cases τ with
  | defined => have h' : Elem.app h args = .app .defined [] := hx; cases h'; rfl
  | inh => have h' : Elem.app h args = .app .inh [] := hx; cases h'; rfl
  | sortSort => have h' : Elem.app h args = .app .sortSort [] := hx; cases h'; rfl
  | ceil => have h' : Elem.app h args = .app .ceil [] := hx; cases h'; rfl
  | next => have h' : Elem.app h args = .app .next [] := hx; cases h'; rfl
  | dv l => have h' : Elem.app h args = .app (.dv l) [] := hx; cases h'; rfl
  | sort n => obtain ⟨s, -, hs⟩ := hx; cases hs
  | str _ => exact hx.elim
  | untranslated _ => exact hx.elim
  | symbol m =>
    by_cases hm : m = "inj"
    · subst hm
      have h' : Elem.app h args = .app .inj [] := hx
      cases h'; rfl
    · rw [evalSymb_symbol hm] at hx
      generalize resolve c m [] = r at hx
      rcases r with _ | ⟨k, _ | i⟩
      · cases hx; rfl
      · have hx' := (ite_mem _ _ _).mp hx
        by_cases hk : k.args = []
        · simp only [hk, ↓reduceIte] at hx'
          obtain ⟨v, hv⟩ := result_val hx'
          cases hv
        · simp only [hk, ↓reduceIte] at hx'
          cases hx'; rfl
      · cases hx; rfl

/-- The head of a name applied to arguments is given by `symAt` only for that name, and only where
a symbol resolves to it or it is `Lblite`. -/
theorem symAt_sym {c : Semantics} {m n : String} {as args : List Elem}
    (hx : symAt c m as (.app (.sym n) args)) (ha : as ≠ []) : n = m ∧ ((resolve c m as).isSome ∨ m = "Lblite") := by
  unfold symAt at hx
  cases hr : resolve c m as with
  | none =>
    rw [hr] at hx
    have hx' := (ite_mem _ _ _).mp hx
    simp only [ha, ↓reduceIte] at hx'
    split at hx'
    · cases hx'; exact ⟨rfl, .inr rfl⟩
    · rename_i hneg
      exact (cast (congrFun (symAt.match_3.eq_2 (fun _ _ => Set Elem) m as
        (fun _ => fun x => x = Elem.app (.sym m) as) (fun _ _ => fun _ => False) hneg) (Elem.app (.sym n) args)) hx').elim
  | some kp =>
    obtain ⟨k, p⟩ := kp
    rw [hr] at hx
    refine ⟨?_, .inl rfl⟩
    have hx' := (ite_mem _ _ _).mp hx
    by_cases hl : as.length < p + k.args.length
    · simp only [hl, ↓reduceIte] at hx'
      injection hx' with h1 _
      injection h1
    · simp only [hl, ↓reduceIte] at hx'
      have hx2 := (ite_mem _ _ _).mp hx'
      by_cases hl2 : as.length = p + k.args.length
      · simp only [hl2, ↓reduceIte] at hx2
        generalize vals (List.drop p as) = o at hx2
        rcases o with _ | vs
        · exact hx2.elim
        · obtain ⟨v, hv⟩ := result_val hx2
          cases hv
      · simp only [hl2, ↓reduceIte] at hx2

/-- **Application gives the head of an unresolved name at arguments only from the definedness
element.** -/
theorem evalApp_partial {c : Semantics} {T : GroundTerm → GroundTerm → Prop} {a b : Elem} {n : String}
    {args : List Elem} (hn : unresolvedB c n = true) (hx : evalApp_T c T a b (.app (.sym n) args)) :
    a = .app .defined [] := by
  rcases a with v | s | ⟨hd, as⟩
  · exact False.elim hx
  · exact False.elim hx
  · cases hd with
    | sym m =>
      have hx' : symAt c m (as ++ [b]) (.app (.sym n) args) := hx
      obtain ⟨rfl, hr | hl⟩ := symAt_sym hx' (by simp)
      · rw [resolve_none hn] at hr; cases hr
      · simp only [unresolvedB, hl, bne_self_eq_false, Bool.and_false, Bool.false_and] at hn
        cases hn
    | defined =>
      rcases as with _ | ⟨_, _⟩
      · rfl
      · exact False.elim hx
    | sortSort => rcases as with _ | ⟨_, _⟩ <;> exact False.elim hx
    | next => rcases as with _ | ⟨_, _⟩ <;> exact False.elim hx
    | inh =>
      rcases as with _ | ⟨_, _⟩
      · rcases b with _ | _ | ⟨hb, bargs⟩
        · exact False.elim hx
        · exact False.elim hx
        · cases hb <;> rcases bargs with _ | ⟨_, _⟩ <;>
            first | exact False.elim hx | (obtain ⟨_, -, hs⟩ := hx; cases hs)
      · exact False.elim hx
    | dv l =>
      rcases as with _ | ⟨_, _⟩
      · rcases b with _ | _ | _
        · exact False.elim hx
        · obtain ⟨_, hs, -⟩ := hx
          cases hs
        · exact False.elim hx
      · exact False.elim hx
    | ceil =>
      rcases as with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, as⟩⟩⟩
      · cases hx
      · cases hx
      · rcases a2 with _ | _ | _ <;> exact False.elim hx
      · rcases a2 with _ | _ | _ <;> exact False.elim hx
    | inj =>
      rcases as with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, as⟩⟩⟩
      · cases hx
      · cases hx
      · rcases a1 with _ | _ | _ <;> rcases a2 with _ | _ | _ <;> rcases b with _ | _ | _ <;>
          first | exact False.elim hx | cases hx
      · rcases a1 with _ | _ | _ <;> rcases a2 with _ | _ | _ <;> rcases b with _ | _ | _ <;>
          exact False.elim hx

/-- The heads of the names `N` applied to any elements. -/
def partialsOf (N : String → Prop) : Elem → Prop := fun x => ∃ n args, N n ∧ x = .app (.sym n) args

/-- **The partial applications of unresolved names are spare for those names' symbols** in the
value model at any transition. -/
theorem spare_partials (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop)
    (hN : ∀ n, N n → unresolvedB c n = true) :
    Spare (stdI_T c T) (partialsOf N) (namesOf N) (Elem.app .defined []) :=
  ⟨fun _ _ ⟨n, args, hn, he⟩ h => by
      subst he
      have := evalSymb_nil h
      subst this
      exact ⟨n, hn, evalSymb_head h⟩,
    fun _ h => evalSymb_head h,
    fun _ _ _ ⟨n, _, hn, he⟩ h => by subst he; exact evalApp_partial (hN n hn) h,
    fun _ _ h => evalApp_head h⟩

/-! ## The patched value model -/

/-- The application of the names `N` at their partial elements: the arguments are collected until
there are `ar n` of them, and then the name's head applied to them is `G n` at their values. -/
def collectApp (ar : String → Nat) (G : String → List GroundTerm → Option GroundTerm) : Elem → Elem → Set Elem :=
  fun a b m => ∃ n args, a = .app (.sym n) args ∧
    ((args.length + 1 < ar n ∧ m = .app (.sym n) (args ++ [b])) ∨
      (args.length + 1 = ar n ∧ ∃ ws v, vals (args ++ [b]) = some ws ∧ G n ws = some v ∧ m = .val v))

/-- **The value model at `T` with the names `N` given meanings**: a name of arity 0 denotes the
value `G n []`, or nothing; the head of a name of positive arity applied to `ar n` values is
`G n` at them (`collectApp`). The other symbols, and application elsewhere, are the value
model's. -/
def initPatch (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop) (ar : String → Nat)
    (G : String → List GroundTerm → Option GroundTerm) : Interpretation KoreAML.Sym Elem :=
  ⟨fun τ x => (∃ n, N n ∧ ar n = 0 ∧ τ = .symbol n ∧ ∃ v, G n [] = some v ∧ x = .val v) ∨
      ((∀ n, N n → ar n = 0 → τ ≠ .symbol n) ∧ evalSymb c τ x),
    (patch (stdI_T c T) (partialsOf N) (collectApp ar G)).evalApp⟩

section Patched

variable (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : String → Prop) (ar : String → Nat)
  (G : String → List GroundTerm → Option GroundTerm)

/-- **A rooted pattern that names none of `N` denotes in the patched value model what it denotes in
the value model.** -/
theorem initPatch_interpret (hN : ∀ n, N n → unresolvedB c n = true) {φ : KoreAML.P} (hr : rootedB φ = true)
    (hn : ∀ n, N n → KoreAML.Sym.symbol n ∉ psyms φ) (ρ : Valuation Elem) :
    φ.interpret (initPatch c T N ar G) ρ = φ.interpret (stdI_T c T) ρ := by
  rw [interpret_symb_congr (initPatch c T N ar G) (patch (stdI_T c T) (partialsOf N) (collectApp ar G)) rfl φ ?_ ρ]
  · exact patch_interpret (spare_partials c T N hN) _ φ hr (fun _ hτ ⟨n, hN', he⟩ => hn n hN' (he ▸ hτ)) ρ
  · intro σ hσ
    funext x
    apply propext
    show ((∃ n, N n ∧ ar n = 0 ∧ σ = .symbol n ∧ ∃ v, G n [] = some v ∧ x = .val v) ∨
      ((∀ n, N n → ar n = 0 → σ ≠ .symbol n) ∧ evalSymb c σ x)) ↔ evalSymb c σ x
    have hne : ∀ n, N n → ar n = 0 → σ ≠ .symbol n := fun n hN' _ he => hn n hN' (he ▸ hσ)
    constructor
    · rintro (⟨n, hN', h0, he, -⟩ | ⟨-, hx⟩)
      · exact absurd he (hne n hN' h0)
      · exact hx
    · exact fun hx => .inr ⟨hne, hx⟩

/-- **The patched value model is a model of the theory wherever the value model is**, for names no
premise names. -/
theorem initPatch_model (hN : ∀ n, N n → unresolvedB c n = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ)
    (hI : stdI_T c T ⊧ᴵP (Γc c ∪ Γstep c)) : initPatch c T N ar G ⊧ᴵP (Γc c ∪ Γstep c) := by
  intro φ hφ ρ m
  show φ.interpret (initPatch c T N ar G) ρ m
  rw [initPatch_interpret c T N ar G hN (rooted_of_decided c (rootedListsB_holds c) φ hφ)
    (fun n hn => hfree n hn φ hφ) ρ]
  exact hI φ hφ ρ m

/-- **The patched value model has the value model's steps.** -/
theorem initPatch_step (hN : ∀ n, N n → unresolvedB c n = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) (x y : Config c) :
    (initPatch c T N ar G ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) ↔
      (stdI_T c T ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hr : rootedB (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)) = true := by
    simp [KoreAML.sNext, KoreAML.sym, Pattern.negation, rooted_val]
  have hn : ∀ n, N n → KoreAML.Sym.symbol n ∉ psyms (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)) := by
    intro n hN'
    simp [KoreAML.sNext, KoreAML.sym, psyms, val_unnamed (hfree n hN') x.property,
      val_unnamed (hfree n hN') y.property]
  constructor
  · intro h ρ m
    have := h ρ m
    rwa [show (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)).interpret (initPatch c T N ar G) ρ = _ from
      initPatch_interpret c T N ar G hN hr hn ρ] at this
  · intro h ρ m
    show (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)).interpret (initPatch c T N ar G) ρ m
    rw [initPatch_interpret c T N ar G hN hr hn ρ]
    exact h ρ m

theorem vals_map_val : ∀ ws : List GroundTerm, vals (ws.map Elem.val) = some ws
  | [] => rfl
  | w :: ws => by simp [vals, vals_map_val ws]

/-- The head of a name of `N` of positive arity, applied to elements `args` and then to `bs`,
`ar n` of them in all and `bs` not empty: `G n` at their values. -/
theorem appE_collect (hN : ∀ n, N n → unresolvedB c n = true) {n : String} (hn : N n) :
    ∀ (bs args : List Elem) (m : Elem), bs ≠ [] → args.length + bs.length = ar n →
      (AppE (initPatch c T N ar G) (.app (.sym n) args) bs m ↔
        ∃ ws v, vals (args ++ bs) = some ws ∧ G n ws = some v ∧ m = .val v)
  | [], _, _, h, _ => absurd rfl h
  | b :: bs, args, m, _, hl => by
    have hP : partialsOf N (.app (.sym n) args) := ⟨n, args, hn, rfl⟩
    have happ : ∀ x, (initPatch c T N ar G).evalApp (.app (.sym n) args) b x ↔ collectApp ar G (.app (.sym n) args) b x := by
      intro x
      show ((partialsOf N (.app (.sym n) args) ∧ collectApp ar G _ b x) ∨
        (¬ partialsOf N (.app (.sym n) args) ∧ _)) ↔ _
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · exact absurd hP h
      · exact fun h => .inl ⟨hP, h⟩
    have hcol : ∀ x, collectApp ar G (.app (.sym n) args) b x ↔
        ((args.length + 1 < ar n ∧ x = .app (.sym n) (args ++ [b])) ∨
          (args.length + 1 = ar n ∧ ∃ ws v, vals (args ++ [b]) = some ws ∧ G n ws = some v ∧ x = .val v)) := by
      intro x
      constructor
      · rintro ⟨n', args', he, h⟩
        injection he with h1 h2
        injection h1 with h1
        subst h1; subst h2
        exact h
      · exact fun h => ⟨n, args, rfl, h⟩
    cases bs with
    | nil =>
      simp only [List.length_cons, List.length_nil] at hl
      show (∃ a', (initPatch c T N ar G).evalApp _ b a' ∧ m = a') ↔ _
      constructor
      · rintro ⟨a', ha', hm⟩
        rcases (hcol a').mp ((happ a').mp ha') with ⟨hlt, -⟩ | ⟨-, h⟩
        · omega
        · rw [hm]; exact h
      · intro h
        exact ⟨m, (happ m).mpr ((hcol m).mpr (.inr ⟨hl, h⟩)), rfl⟩
    | cons b' bs' =>
      simp only [List.length_cons] at hl
      have hlt : args.length + 1 < ar n := by omega
      have ih := appE_collect hN hn (b' :: bs') (args ++ [b]) m (by simp) (by simp; omega)
      show (∃ a', (initPatch c T N ar G).evalApp _ b a' ∧ AppE _ a' (b' :: bs') m) ↔ _
      rw [show args ++ b :: b' :: bs' = (args ++ [b]) ++ b' :: bs' by simp]
      constructor
      · rintro ⟨a', ha', hm⟩
        rcases (hcol a').mp ((happ a').mp ha') with ⟨-, rfl⟩ | ⟨he, -⟩
        · exact ih.mp hm
        · omega
      · intro h
        exact ⟨_, (happ _).mpr ((hcol _).mpr (.inl ⟨hlt, rfl⟩)), ih.mpr h⟩

/-- **A name of `N` applied to values denotes `G n` at them**: exactly the value `G n ws`, or
nothing, in the patched value model, at `ar n` values of a sort, where every value denotes its
own element in the value model (`DenGoalT`). At arity 0 the name is a constant. -/
theorem initPatch_apps (hN : ∀ n, N n → unresolvedB c n = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ)
    (hden : AtT.DenGoalT c T) {n : String} (hn : N n) {ws : List GroundTerm} (hl : ws.length = ar n)
    (hws : ∀ w ∈ ws, ∃ s, c.sortOf w = some s) (ρ : Valuation Elem) (m : Elem) :
    (KoreAML.appList (symP n) (ws.map (den c))).interpret (initPatch c T N ar G) ρ m ↔
      ∃ v, G n ws = some v ∧ m = .val v := by
  cases ws with
  | nil =>
    show (∃ n', N n' ∧ ar n' = 0 ∧ KoreAML.Sym.symbol n = .symbol n' ∧ ∃ v, G n' [] = some v ∧ m = .val v) ∨
      ((∀ n', N n' → ar n' = 0 → KoreAML.Sym.symbol n ≠ .symbol n') ∧ evalSymb c (.symbol n) m) ↔ _
    constructor
    · rintro (⟨n', -, -, he, hv⟩ | ⟨hne, -⟩)
      · injection he with he; subst he; exact hv
      · exact absurd rfl (hne n hn hl.symm)
    · intro hv
      exact .inl ⟨n, hn, hl.symm, rfl, hv⟩
  | cons w ws' =>
    have hall : All2 (fun φ x => ∀ m, φ.interpret (initPatch c T N ar G) ρ m ↔ m = x)
        ((w :: ws').map (den c)) ((w :: ws').map Elem.val) := by
      have : ∀ us : List GroundTerm, (∀ u ∈ us, ∃ s, c.sortOf u = some s) →
          All2 (fun φ x => ∀ m, φ.interpret (initPatch c T N ar G) ρ m ↔ m = x) (us.map (den c)) (us.map Elem.val) := by
        intro us
        induction us with
        | nil => exact fun _ => .nil
        | cons u us ih =>
          intro hu
          obtain ⟨s, hs⟩ := hu u (List.mem_cons_self ..)
          refine .cons (fun m => ?_) (ih fun u' hu' => hu u' (List.mem_cons_of_mem _ hu'))
          rw [initPatch_interpret c T N ar G hN (rooted_val c u) (fun k hk => val_unnamed (hfree k hk) hs) ρ]
          exact hden u s hs ρ m
      exact this _ hws
    rw [interp_appList_sing _ _ _ hall]
    have hsym : ∀ a, (symP n).interpret (initPatch c T N ar G) ρ a ↔ a = .app (.sym n) [] := by
      intro a
      show ((∃ n', N n' ∧ ar n' = 0 ∧ KoreAML.Sym.symbol n = .symbol n' ∧ ∃ v, G n' [] = some v ∧ a = .val v) ∨
        ((∀ n', N n' → ar n' = 0 → KoreAML.Sym.symbol n ≠ .symbol n') ∧ evalSymb c (.symbol n) a)) ↔ _
      have hpos : ar n ≠ 0 := by rw [← hl]; simp
      rw [← evalSymb_spare (spareSymB_of_unresolved (hN n hn)) a]
      constructor
      · rintro (⟨n', -, h0, he, -⟩ | ⟨-, h⟩)
        · injection he with he; subst he; exact absurd h0 hpos
        · exact h
      · intro h
        refine .inr ⟨fun n' _ h0 he => ?_, h⟩
        injection he with he; subst he; exact hpos h0
    constructor
    · rintro ⟨a, ha, happ⟩
      rw [(hsym a).mp ha] at happ
      obtain ⟨us, v, hus, hg, rfl⟩ := (appE_collect c T N ar G hN hn _ [] m (by simp)
        (by simpa using hl)).mp happ
      rw [List.nil_append, vals_map_val] at hus
      cases hus
      exact ⟨v, hg, rfl⟩
    · rintro ⟨v, hg, rfl⟩
      refine ⟨_, (hsym _).mpr rfl, (appE_collect c T N ar G hN hn _ [] _ (by simp) (by simpa using hl)).mpr
        ⟨w :: ws', v, ?_, hg, rfl⟩⟩
      rw [List.nil_append, vals_map_val]

end Patched

/-! ## Equations by denotation, and denotations down a right side -/

section Den

variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **An equation holds in a model with definedness where both sides denote the same elements at
every valuation.** -/
theorem eqn_of_den (hD : KoreAML.DefOK I) {φ ψ : KoreAML.P}
    (h : ∀ ρ m, φ.interpret I ρ m ↔ ψ.interpret I ρ m) : I ⊧ᴵ (φ ≡ ψ) := by
  intro ρ m
  rw [KoreAML.interp_equal hD]
  exact fun a => h ρ a

/-- **An equation that holds denotes the same elements on both sides**, in a model with
definedness. -/
theorem den_of_eqn (hD : KoreAML.DefOK I) {φ ψ : KoreAML.P} (h : I ⊧ᴵ (φ ≡ ψ)) (ρ : Valuation M) (m : M) :
    φ.interpret I ρ m ↔ ψ.interpret I ρ m := by
  have h1 := h ρ m
  rw [KoreAML.interp_equal hD] at h1
  exact h1 m

/-- **An application denotes what its parts' denotations give**: heads and arguments that denote
the same elements pairwise give the same elements. -/
theorem appList_congr {ρ : Valuation M} : ∀ (φs ψs : List KoreAML.P) (h h' : KoreAML.P),
    (∀ m, h.interpret I ρ m ↔ h'.interpret I ρ m) →
    All2 (fun φ ψ => ∀ m, φ.interpret I ρ m ↔ ψ.interpret I ρ m) φs ψs →
    ∀ m, (KoreAML.appList h φs).interpret I ρ m ↔ (KoreAML.appList h' ψs).interpret I ρ m
  | [], [], _, _, hh, .nil, m => hh m
  | φ :: φs, ψ :: ψs, h, h', hh, .cons h1 hs, m => by
    refine appList_congr φs ψs (h ⬝ φ) (h' ⬝ ψ) (fun m => ?_) hs m
    rw [interpret_app, interpret_app]
    constructor
    · rintro ⟨a, b, ha, hb, happ⟩; exact ⟨a, b, (hh a).mp ha, (h1 b).mp hb, happ⟩
    · rintro ⟨a, b, ha, hb, happ⟩; exact ⟨a, b, (hh a).mpr ha, (h1 b).mpr hb, happ⟩

/-- **An application with an argument that denotes nothing denotes nothing.** -/
theorem appList_empty {ρ : Valuation M} : ∀ (φs : List KoreAML.P) (h : KoreAML.P),
    (∃ φ ∈ φs, ∀ m, ¬ φ.interpret I ρ m) → ∀ m, ¬ (KoreAML.appList h φs).interpret I ρ m := by
  intro φs h he m hm
  rw [interp_appList] at hm
  obtain ⟨-, -, bs, hbs, -⟩ := hm
  obtain ⟨φ, hφ, hn⟩ := he
  clear h m
  induction hbs with
  | nil => cases hφ
  | cons hb _ ih =>
    rcases List.mem_cons.mp hφ with rfl | hφ'
    · exact hn _ hb
    · exact ih hφ'

end Den

theorem koreList_den (c : Semantics) : ∀ ws : List GroundTerm,
    (GroundTerm.koreList c ws).map (KoreAML.tr ⟨[], []⟩) = ws.map (den c)
  | [] => by rw [GroundTerm.koreList]; rfl
  | w :: ws => by rw [GroundTerm.koreList, List.map_cons, List.map_cons, koreList_den c ws]; rfl

/-- Arguments that each denote what a value's denotation does, against the values' denotations. -/
theorem all2_den_map {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M} {ρ : Valuation M} :
    ∀ {ψs : List KoreAML.P} {ws : List GroundTerm},
    All2 (fun ψ w => ∀ m, ψ.interpret I ρ m ↔ (den c w).interpret I ρ m) ψs ws →
    All2 (fun φ ψ => ∀ m, φ.interpret I ρ m ↔ ψ.interpret I ρ m) ψs (ws.map (den c))
  | _, _, .nil => .nil
  | _, _, .cons h1 hs => .cons h1 (all2_den_map hs)

section DenC

variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A constructor over arguments that denote values denotes the value they build**: it is the
value's own denotation, `den c (.ctor f ws)`. -/
theorem ctor_den (f : Sym) {ψs : List KoreAML.P} {ws : List GroundTerm} {ρ : Valuation M}
    (h : All2 (fun ψ w => ∀ m, ψ.interpret I ρ m ↔ (den c w).interpret I ρ m) ψs ws) (m : M) :
    (KoreAML.appList (symP (c.symName f)) ψs).interpret I ρ m ↔ (den c (.ctor f ws)).interpret I ρ m := by
  rw [den_ctor, trArgs_appList, koreList_den]
  exact appList_congr ψs (ws.map (den c)) _ _ (fun _ => Iff.rfl) (all2_den_map h) m

/-- **`inj` over an argument that denotes a value denotes the injected value.** -/
theorem inj_den (a b : Srt) {ψ : KoreAML.P} {w : GroundTerm} {ρ : Valuation M}
    (h : ∀ m, ψ.interpret I ρ m ↔ (den c w).interpret I ρ m) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b), ψ]).interpret I ρ m ↔
      (den c (.inj a b w)).interpret I ρ m := by
  rw [den_inj]
  exact appList_congr _ _ _ _ (fun _ => Iff.rfl) (.cons (fun _ => Iff.rfl) (.cons (fun _ => Iff.rfl) (.cons h .nil))) m

/-- The denotation of an interpreted symbol's application at values, as `ΓDomains` writes its
graph, for a symbol that is not `ite` at a sort. -/
theorem symApp_den {f : Sym} (hf : iteSort? (c.symName f) = none) (vs : List GroundTerm) :
    KoreAML.den (symApp c f (GroundTerm.koreList c vs)) = KoreAML.appList (symP (c.symName f)) (vs.map (den c)) := by
  unfold symApp
  rw [hf]
  unfold KoreAML.den
  rw [KoreAML.tr_app0, trArgs_appList, koreList_den]
  rfl

/-- **An interpreted symbol at values denotes its graph's value, or nothing**, in a model of the
theory with definedness: the theory states the graph at values (`ΓDomains`). -/
theorem hook_den (hI : I ⊧ᴵP (Γc c ∪ Γstep c)) (hD : KoreAML.DefOK I) {k : CtorSig} (hk : k ∈ hookSigs)
    (hf : iteSort? (c.symName k.name) = none) {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args)
    {r : Option GroundTerm} (hr : hook k.name vs = some r) (hsil : r = none → silent k.name vs = false)
    (ρ : Valuation M) (m : M) :
    (KoreAML.appList (symP (c.symName k.name)) (vs.map (den c))).interpret I ρ m ↔
      (match r with
        | some v => den c v
        | none => ⊥).interpret I ρ m := by
  rw [← symApp_den hf vs]
  refine den_of_eqn hD (hI _ ?_) ρ m
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, r, hk, hvs, hr, hsil, rfl⟩)))))))

end DenC

/-! ## Models in which the names denote `G`, and right sides read down the tree -/

/-- The model `model_with_inits_step` gives: a model of the theory in which every value of a sort
denotes its own element, and the name `n` of `N` applied to `ar n` values of a sort denotes exactly
the value `G n ws`, or nothing. -/
structure InitModel (c : Semantics) (N : String → Prop) (ar : String → Nat)
    (G : String → List GroundTerm → Option GroundTerm) (I : Interpretation KoreAML.Sym Elem) : Prop where
  sat : I ⊧ᴵP (Γc c ∪ Γstep c)
  vals : ∀ (v : GroundTerm) (s : Srt), c.sortOf v = some s → ∀ ρ m, (den c v).interpret I ρ m ↔ m = .val v
  names : ∀ n, N n → ∀ ws : List GroundTerm, ws.length = ar n → (∀ w ∈ ws, ∃ s, c.sortOf w = some s) → ∀ ρ m,
    (KoreAML.appList (symP n) (ws.map (den c))).interpret I ρ m ↔ ∃ v, G n ws = some v ∧ m = .val v

/-- The pattern denotes exactly the value `w`, a value of a sort, at every valuation. -/
def DenV (c : Semantics) (I : Interpretation KoreAML.Sym Elem) (ψ : KoreAML.P) (w : GroundTerm) : Prop :=
  (∃ s, c.sortOf w = some s) ∧ ∀ ρ m, ψ.interpret I ρ m ↔ m = .val w

/-- The pattern denotes nothing, at every valuation. -/
def DenE (I : Interpretation KoreAML.Sym Elem) (ψ : KoreAML.P) : Prop := ∀ ρ m, ¬ ψ.interpret I ρ m

/-- **An application with an argument that denotes nothing denotes nothing.** -/
theorem DenE.app {I : Interpretation KoreAML.Sym Elem} (h : KoreAML.P) {ψs : List KoreAML.P}
    (he : ∃ ψ ∈ ψs, DenE I ψ) : DenE I (KoreAML.appList h ψs) := fun ρ m => by
  obtain ⟨ψ, hψ, hn⟩ := he
  exact appList_empty ψs h ⟨ψ, hψ, hn ρ⟩ m

namespace InitModel

variable {c : Semantics} {N : String → Prop} {ar : String → Nat} {G : String → List GroundTerm → Option GroundTerm}
  {I : Interpretation KoreAML.Sym Elem} (hM : InitModel c N ar G I)
include hM

theorem defOK : KoreAML.DefOK I := Faithful.defOK (fun φ hφ => hM.sat φ (Or.inl (Or.inl hφ)))

/-- A value of a sort denotes itself. -/
theorem val {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) : DenV c I (den c v) v :=
  ⟨⟨s, hv⟩, hM.vals v s hv⟩

theorem all2_den : ∀ {ψs : List KoreAML.P} {ws : List GroundTerm}, All2 (DenV c I) ψs ws → ∀ ρ,
    All2 (fun ψ w => ∀ m, ψ.interpret I ρ m ↔ (den c w).interpret I ρ m) ψs ws
  | _, _, .nil, _ => .nil
  | _, _, .cons ⟨⟨s, hs⟩, h⟩ hs', ρ => .cons (fun m => (h ρ m).trans (hM.vals _ s hs ρ m).symm) (all2_den hs' ρ)

omit hM in
theorem all2_sorted : ∀ {ψs : List KoreAML.P} {ws : List GroundTerm}, All2 (DenV c I) ψs ws →
    ∀ w ∈ ws, ∃ s, c.sortOf w = some s
  | _, _, .nil, _, hw => by cases hw
  | _, _, .cons ⟨hs, _⟩ hs', w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact hs
    · exact all2_sorted hs' w hw'

/-- **A constructor over arguments that denote values denotes the value they build.** -/
theorem ctor {f : Sym} {ψs : List KoreAML.P} {ws : List GroundTerm} (h : All2 (DenV c I) ψs ws) {s : Srt}
    (hs : c.sortOf (.ctor f ws) = some s) : DenV c I (KoreAML.appList (symP (c.symName f)) ψs) (.ctor f ws) :=
  ⟨⟨s, hs⟩, fun ρ m => (ctor_den f (hM.all2_den h ρ) m).trans (hM.vals _ s hs ρ m)⟩

/-- **`inj` over an argument that denotes a value denotes the injected value.** -/
theorem inj (a b : Srt) {ψ : KoreAML.P} {w : GroundTerm} (h : DenV c I ψ w) {s : Srt}
    (hs : c.sortOf (.inj a b w) = some s) :
    DenV c I (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b), ψ]) (.inj a b w) := by
  refine ⟨⟨s, hs⟩, fun ρ m => (inj_den a b (fun m => ?_) m).trans (hM.vals _ s hs ρ m)⟩
  obtain ⟨⟨s', hs'⟩, h'⟩ := h
  exact (h' ρ m).trans (hM.vals w s' hs' ρ m).symm

/-- **A name of `N` over arguments that denote values denotes `G`'s value at them.** -/
theorem name {n : String} (hn : N n) {ψs : List KoreAML.P} {ws : List GroundTerm} (h : All2 (DenV c I) ψs ws)
    (hl : ws.length = ar n) {v : GroundTerm} (hg : G n ws = some v) {s : Srt} (hs : c.sortOf v = some s) :
    DenV c I (KoreAML.appList (symP n) ψs) v := by
  refine ⟨⟨s, hs⟩, fun ρ m => ?_⟩
  rw [appList_congr ψs (ws.map (den c)) _ _ (fun _ => Iff.rfl) (all2_den_map (hM.all2_den h ρ)) m, hM.names n hn ws hl (all2_sorted h) ρ m, hg]
  simp

/-- **A name of `N` over arguments that denote values where `G` has no value denotes nothing.** -/
theorem name_none {n : String} (hn : N n) {ψs : List KoreAML.P} {ws : List GroundTerm} (h : All2 (DenV c I) ψs ws)
    (hl : ws.length = ar n) (hg : G n ws = none) : DenE I (KoreAML.appList (symP n) ψs) := by
  intro ρ m
  rw [appList_congr ψs (ws.map (den c)) _ _ (fun _ => Iff.rfl) (all2_den_map (hM.all2_den h ρ)) m, hM.names n hn ws hl (all2_sorted h) ρ m, hg]
  simp

/-- **An interpreted symbol over arguments that denote values denotes its graph's value.** -/
theorem hookV {k : CtorSig} (hk : k ∈ hookSigs) (hf : iteSort? (c.symName k.name) = none) {ψs : List KoreAML.P}
    {vs : List GroundTerm} (h : All2 (DenV c I) ψs vs) (hvs : c.sortsOf vs = some k.args) {v : GroundTerm}
    (hr : hook k.name vs = some (some v)) {s : Srt} (hs : c.sortOf v = some s) :
    DenV c I (KoreAML.appList (symP (c.symName k.name)) ψs) v := by
  refine ⟨⟨s, hs⟩, fun ρ m => ?_⟩
  rw [appList_congr ψs (vs.map (den c)) _ _ (fun _ => Iff.rfl) (all2_den_map (hM.all2_den h ρ)) m,
    hook_den hM.sat hM.defOK hk hf hvs hr (fun h => by cases h) ρ m]
  exact hM.vals v s hs ρ m

/-- **An interpreted symbol over arguments that denote values where its graph has none denotes
nothing**, at a point the text is not silent at. -/
theorem hookE {k : CtorSig} (hk : k ∈ hookSigs) (hf : iteSort? (c.symName k.name) = none) {ψs : List KoreAML.P}
    {vs : List GroundTerm} (h : All2 (DenV c I) ψs vs) (hvs : c.sortsOf vs = some k.args)
    (hr : hook k.name vs = some none) (hsil : silent k.name vs = false) :
    DenE I (KoreAML.appList (symP (c.symName k.name)) ψs) := by
  intro ρ m
  rw [appList_congr ψs (vs.map (den c)) _ _ (fun _ => Iff.rfl) (all2_den_map (hM.all2_den h ρ)) m,
    hook_den hM.sat hM.defOK hk hf hvs hr (fun _ => hsil) ρ m]
  exact id

/-- **An equation whose sides denote the same value holds.** -/
theorem eqn {φ ψ : KoreAML.P} {v : GroundTerm} (h1 : DenV c I φ v) (h2 : DenV c I ψ v) : I ⊧ᴵ (φ ≡ ψ) :=
  eqn_of_den hM.defOK fun ρ m => (h1.2 ρ m).trans (h2.2 ρ m).symm

/-- **An equation whose sides both denote nothing holds**: the equation of a right side with no
value. -/
theorem eqn_none {φ ψ : KoreAML.P} (h1 : DenE I φ) (h2 : DenE I ψ) : I ⊧ᴵ (φ ≡ ψ) :=
  eqn_of_den hM.defOK fun ρ m => ⟨fun h => (h1 ρ m h).elim, fun h => (h2 ρ m h).elim⟩

/-- **A pattern that denotes a value has exactly one value**: the `functional` axiom `∃x:s. x = φ`
holds at the value's sort, as the theory states the value an element of it. -/
theorem functional {φ : KoreAML.P} {v : GroundTerm} {s : Srt} (h : DenV c I φ v) (hs : c.sortOf v = some s)
    (x : EVar) : I ⊧ᴵ KoreAML.sExists x (KoreAML.Cons.sortP (c.sortName s)) (.evar x ≡ φ) := by
  have hD := hM.defOK
  have hΓ := hM.sat _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨v, s, hs, rfl⟩))))))))))
  intro ρ m
  obtain ⟨a, ha, he⟩ := KoreAML.interp_sExists.mp (hΓ ρ m)
  rw [KoreAML.interp_equal hD] at he
  have hav : a = .val v := (hM.vals v s hs _ a).mp ((he a).mpr (by simp))
  subst hav
  rw [KoreAML.interp_member hD] at ha
  refine KoreAML.interp_sExists.mpr ⟨.val v, ?_, ?_⟩
  · rw [KoreAML.interp_member hD]
    simp only [Function.update_same] at ha ⊢
    exact ha
  · rw [KoreAML.interp_equal hD]
    intro b
    rw [KoreAML.interp_evar, h.2]
    simp

end InitModel

/-! ## The model -/

/-- **The theory with the equations of symbols it does not name, of any arity, has a model with
the semantics' steps.** For a semantics that `coreOK` accepts under `FnHyp`, names `N` that are no
symbol's of the semantics (nor `inj` or `Lblite`), arities `ar` and partial functions `G n` on
lists of values: an interpretation that satisfies `Γc c` with the step's closure, in which every
value of a sort denotes its own element and the name `n` applied to `ar n` values `ws` of a sort
denotes exactly `G n ws`, nothing where that is `none` (a name of arity 0 is a constant)
(`InitModel`), and whose steps at configurations are `Step`'s. -/
theorem model_with_inits_step (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (N : String → Prop)
    (ar : String → Nat) (G : String → List GroundTerm → Option GroundTerm)
    (hN : ∀ n, N n → (regSymNames ++ c.symNames).contains n = false ∧ n ≠ "" ∧ n ≠ "inj" ∧ n ≠ "Lblite") :
    ∃ I : Interpretation KoreAML.Sym Elem, InitModel c N ar G I ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hu : ∀ n, N n → unresolvedB c n = true := fun n hn =>
    let ⟨h1, h2, h3, h4⟩ := hN n hn; unresolvedB_of_unnumbered c h1 h2 h3 h4
  have hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ := fun n hn =>
    nameFree_of_decided c [n] h (nameFreeB_of_unnumbered c [n] fun m hm => by
      rw [List.mem_singleton.mp hm]; exact hN n hn) n (List.mem_singleton_self _)
  have hm := hypModel_of_fnHyp h hf
  have hfd := (fnModel_of_fnHyp h hf).1
  have hrules := Semantics.ruleFactsHeld_of_core h
  have hsr : ∀ r ∈ c.rules, c.ruleSorted r = true := fun r hr => (hrules r hr).1
  let T : Config c → Config c → Prop := Step c
  have hI : stdI_T c (liftT_ex c T) ⊧ᴵP (Γc c ∪ Γstep c) := by
    refine stdI_T_model_heldCEx c hm (clausePreDecided_of_fnHyp h hf) (clausePostDecided_of_fnHypCEx (Semantics.coreOKEx_of_coreOK h) hf) hf.2.2.2.2.2 hrules (liftT_ex c T) ?_ ?_ ?_
    · intro x y hx hy hT
      obtain ⟨r, σ, hb⟩ := step_iff_by.mp (hT hx hy)
      exact ⟨r, σ, stepVBy_of_stepBy hfd hb⟩
    · intro r σ x y hb _ hx hy
      exact step_iff_by.mpr ⟨r, σ, stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb⟩
    · intro r σ x y hb _
      exact ⟨y, σ, fun _ _ => rfl, hb, fun hx hy =>
        step_iff_by.mpr ⟨r, σ, stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb⟩⟩
  have hden := AtT.denGoal (T := liftT_ex c T) hm
  refine ⟨initPatch c (liftT_ex c T) N ar G, ⟨initPatch_model c _ N ar G hu hfree hI, fun v s hv ρ m => ?_,
    fun n hn ws hl hws ρ m => initPatch_apps c _ N ar G hu hfree hden hn hl hws ρ m⟩, fun x y => ?_⟩
  · rw [initPatch_interpret c _ N ar G hu (rooted_val c v) (fun k hk => val_unnamed (hfree k hk) hv) ρ]
    exact hden v s hv ρ m
  · rw [initPatch_step c _ N ar G hu hfree x y]
    exact (liftT_ex_iff T x y).symm.trans (step_iff_stdI_T c hm _ x y)

end GenEqs

end KCore
