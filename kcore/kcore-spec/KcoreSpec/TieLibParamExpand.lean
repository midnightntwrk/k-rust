/-
  An interpretation changed at names Γ lacks stays a model of the theory, with the same steps.

  No premise of `Γc c ∪ Γstep c` applies a symbol other than `inj` and the names of Γ's heads
  (`GHComplete.premise_symbol_names`, under `coreOK`), and a pattern's denotation reads only the
  symbols it holds (`GenEqs.interpret_symb_congr`). So an interpretation with the same
  application, and the same meaning at every symbol other than the `.symbol n` whose name `n` is
  neither `inj` nor the name of one of `gammaHeads c` (`AgreeAtHeads`), satisfies every premise
  another does.

  - `agree_premise`: one premise, at every valuation.
  - `agree_step`: the step patterns `den x ⇒ ∼ •(den y)` at configurations; a value's denotation
    applies no name Γ lacks (`val_unnamed`).
  - `expand_lacked`: the statement at `c.withHooks H`, for every hook interpretation H, with
    agreement at `gammaHeads c`: the model and its steps carry over.
  - `expand_lacked_sentences`: a choice at the names Γ lacks that makes sentences `S` hold gives a
    model of `Γc ∪ Γstep ∪ S` with the same steps. That is the case without gained elements of the
    expansion condition (E) for a library parameter Γ lacks (owed-sentence rule item 7): (E) asks
    that every model of Γ extend, possibly gaining elements, to a model of Γ and of the lacked
    symbols' sentences that is elementary for Γ's language at the model's elements. On the same
    carrier with the same application, agreement at Γ's heads already makes every pattern over
    Γ's symbols denote what it denoted.

  - `agree_updAt`: an interpretation changed at one name Γ lacks (`lackedNameB`) agrees with it.

  The agreement keeps the interpretation's carrier and its application. A sentence of a lacked
  symbol of positive arity is therefore met only by a choice of elements of the carrier whose
  applications denote what the sentence asks. Γ states the existence of no such element, and
  nothing here gives one in every model of Γ.

  **One model where the lacked symbols denote given values** (`model_lacked`): for a semantics
  `coreOK` accepts under `FnHyp` and signatures `ls` of symbols whose names Γ lacks
  (`lackedNameB`) and that resolve to no symbol, and any partial function `G` on values of their
  argument sorts with values of their result sorts: one model of `Γc ∪ Γstep` whose steps at
  configurations are `Step`'s, in which each symbol of `ls` applied to values denotes `G`'s value
  or nothing (`LibEv.LackedDen`), the value model with the names patched
  (`GenEqs.model_with_inits_arm`). `LibEv.FnEqn.entailedLk_reg` and `LibEv.functionalLk` then read
  a library sentence applying them at values in it.
-/
import KcoreSpec.TieHeadsComplete
import KcoreSpec.GenEqsInit
import KcoreSpec.FnObligations
import KcoreSpec.LibEvLacked
import KcoreSpec.GenEqsInitArm

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace TieLibParam

/-- The symbol `σ` is one a premise of the theory may apply: it is no `.symbol n` other than `inj`
and the names of Γ's heads. -/
def GammaSym (c : Semantics) (σ : KoreAML.Sym) : Prop :=
  ∀ n, σ = .symbol n → n = "inj" ∨ n ∈ (gammaHeads c).map (·.1)

/-- **`I'` agrees with `I` at Γ's heads**: the same application, and the same meaning at every
symbol `GammaSym` admits (every symbol that is not a `.symbol n` named by none of `gammaHeads c`
nor `inj`). `I'` may differ from `I` only at the names Γ lacks. -/
structure AgreeAtHeads (c : Semantics) {M : Type} (I I' : Interpretation KoreAML.Sym M) : Prop where
  app : I'.evalApp = I.evalApp
  syms : ∀ σ, GammaSym c σ → I'.evalSymb σ = I.evalSymb σ

/-- Every symbol of a premise is one `GammaSym` admits, under `coreOK`. -/
theorem premise_gammaSym {c : Semantics} (h : c.coreOK = true) {φ : KoreAML.P} (hφ : (Γc c ∪ Γstep c) φ) :
    ∀ σ ∈ psyms φ, GammaSym c σ := by
  intro σ hσ n hn
  subst hn
  rcases GHComplete.premise_symbol_names c h φ hφ n hσ with hi | ⟨k, hk, he⟩
  · exact .inl hi
  · refine .inr (List.mem_map.mpr ⟨gammaHead c k.name, ?_, he.symm⟩)
    exact List.mem_append_left _ (List.mem_map_of_mem hk)

/-- A name `GammaSym` refuses is applied by no premise. -/
theorem lacked_free {c : Semantics} (h : c.coreOK = true) {n : String} (hn : ¬ GammaSym c (.symbol n)) :
    ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ :=
  fun _ hφ hm => hn (premise_gammaSym h hφ _ hm)

section Agree

variable {c : Semantics} {M : Type} {I I' : Interpretation KoreAML.Sym M}

/-- **A premise denotes the same under interpretations that agree at Γ's heads**, at every
valuation. -/
theorem agree_premise (h : c.coreOK = true) (hA : AgreeAtHeads c I I') {φ : KoreAML.P}
    (hφ : (Γc c ∪ Γstep c) φ) (ρ : Valuation M) : φ.interpret I' ρ = φ.interpret I ρ :=
  GenEqs.interpret_symb_congr I' I hA.app φ (fun σ hσ => hA.syms σ (premise_gammaSym h hφ σ hσ)) ρ

/-- **The theory's models are closed under agreement at Γ's heads.** -/
theorem agree_sat (h : c.coreOK = true) (hA : AgreeAtHeads c I I') (hI : I ⊧ᴵP (Γc c ∪ Γstep c)) :
    I' ⊧ᴵP (Γc c ∪ Γstep c) := by
  intro φ hφ ρ m
  show φ.interpret I' ρ m
  rw [agree_premise h hA hφ ρ]
  exact hI φ hφ ρ m

/-- The step pattern at two values of sorts holds only symbols `GammaSym` admits. -/
theorem step_gammaSym (h : c.coreOK = true) {v w : GroundTerm} {s t : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some t) : ∀ σ ∈ psyms (den c v ⇒ ∼ KoreAML.sNext (den c w)), GammaSym c σ := by
  intro σ hσ n hn
  subst hn
  refine Classical.byContradiction fun hn => ?_
  have hfree := lacked_free h (fun hg => hn (hg n rfl))
  simp [KoreAML.sNext, KoreAML.sym, psyms, GenEqs.val_unnamed hfree hv,
    GenEqs.val_unnamed hfree hw] at hσ

/-- **The steps at configurations are the same under interpretations that agree at Γ's heads.** -/
theorem agree_step (h : c.coreOK = true) (hA : AgreeAtHeads c I I') (x y : Config c) :
    (I' ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) ↔
      (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have he : ∀ ρ, (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)).interpret I' ρ =
      (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)).interpret I ρ := fun ρ =>
    GenEqs.interpret_symb_congr I' I hA.app _
      (fun σ hσ => hA.syms σ (step_gammaSym h x.property y.property σ hσ)) ρ
  constructor
  · intro h' ρ m; have := h' ρ m; rwa [he ρ] at this
  · intro h' ρ m; show (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)).interpret I' ρ m; rw [he ρ]; exact h' ρ m

end Agree

/-- Γ's heads do not depend on the hook interpretation. -/
theorem gammaHeads_withHooks (c : Semantics) (H : HookParams) : gammaHeads (c.withHooks H) = gammaHeads c := rfl

/-- **An interpretation changed at the names Γ lacks stays a model, with the same steps.** For a
semantics `coreOK` accepts and every hook interpretation H: if `I` satisfies
`Γc (c.withHooks H) ∪ Γstep (c.withHooks H)`, every `I'` that agrees with `I` at Γ's heads
(`gammaHeads c`: the same application, and the same meaning at every symbol but the `.symbol n`
named by no head of Γ nor `inj`) satisfies it too, and its steps at configurations are `I`'s. -/
theorem expand_lacked (c : Semantics) (h : c.coreOK = true) (H : HookParams) {M : Type}
    (I I' : Interpretation KoreAML.Sym M) (hI : I ⊧ᴵP (Γc (c.withHooks H) ∪ Γstep (c.withHooks H)))
    (hA : AgreeAtHeads c I I') :
    (I' ⊧ᴵP (Γc (c.withHooks H) ∪ Γstep (c.withHooks H))) ∧
      ∀ x y : Config (c.withHooks H),
        ((I' ⊧ᴵ (den (c.withHooks H) x.val ⇒ ∼ KoreAML.sNext (den (c.withHooks H) y.val))) ↔
          (I ⊧ᴵ (den (c.withHooks H) x.val ⇒ ∼ KoreAML.sNext (den (c.withHooks H) y.val)))) := by
  have h' : (c.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c H).trans h
  have hA' : AgreeAtHeads (c.withHooks H) I I' := ⟨hA.app, fun σ hσ => hA.syms σ (by
    rw [GammaSym, gammaHeads_withHooks] at hσ; exact hσ)⟩
  exact ⟨agree_sat h' hA' hI, agree_step h' hA'⟩

/-- **A choice at the lacked names that makes the sentences `S` hold is a model of the theory with
`S`, with the same steps**: where a model `I` has such a choice on its own carrier, the case
without gained elements of the expansion condition (E), the theory together with the sentences of
the lacked names has a model with `I`'s steps. -/
theorem expand_lacked_sentences (c : Semantics) (h : c.coreOK = true) (H : HookParams) {M : Type}
    (I I' : Interpretation KoreAML.Sym M) (S : Premises KoreAML.Sym)
    (hI : I ⊧ᴵP (Γc (c.withHooks H) ∪ Γstep (c.withHooks H))) (hA : AgreeAtHeads c I I') (hS : I' ⊧ᴵP S) :
    (I' ⊧ᴵP (Γc (c.withHooks H) ∪ Γstep (c.withHooks H) ∪ S)) ∧
      ∀ x y : Config (c.withHooks H),
        ((I' ⊧ᴵ (den (c.withHooks H) x.val ⇒ ∼ KoreAML.sNext (den (c.withHooks H) y.val))) ↔
          (I ⊧ᴵ (den (c.withHooks H) x.val ⇒ ∼ KoreAML.sNext (den (c.withHooks H) y.val)))) := by
  obtain ⟨h1, h2⟩ := expand_lacked c h H I I' hI hA
  refine ⟨fun φ hφ => ?_, h2⟩
  rcases hφ with hφ | hφ
  · exact h1 φ hφ
  · exact hS φ hφ

/-! ## One model where the lacked symbols denote given values -/

/-- The name is one Γ lacks: neither `inj` nor the name of one of Γ's heads. -/
def lackedNameB (c : Semantics) (n : String) : Bool :=
  n != "inj" && !((gammaHeads c).map (·.1)).contains n

theorem not_gammaSym_of_lackedNameB {c : Semantics} {n : String} (h : lackedNameB c n = true) :
    ¬ GammaSym c (.symbol n) := by
  intro hg
  simp only [lackedNameB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  rcases hg n rfl with hi | hm
  · exact h.1 hi
  · have := List.contains_iff_mem.mpr hm
    rw [h.2] at this
    cases this

/-- `I` with the name `n` given the meaning `S`, its application kept. -/
def updAt {M : Type} (I : Interpretation KoreAML.Sym M) (n : String) (S : Set M) : Interpretation KoreAML.Sym M :=
  ⟨fun σ => if σ = .symbol n then S else I.evalSymb σ, I.evalApp⟩

/-- **An interpretation changed at one name Γ lacks agrees with it at Γ's heads.** -/
theorem agree_updAt {c : Semantics} {M : Type} (I : Interpretation KoreAML.Sym M) {n : String}
    (hn : lackedNameB c n = true) (S : Set M) : AgreeAtHeads c I (updAt I n S) := by
  refine ⟨rfl, fun σ hσ => ?_⟩
  show (if σ = .symbol n then S else I.evalSymb σ) = I.evalSymb σ
  have hne : σ ≠ .symbol n := by
    rintro rfl
    exact not_gammaSym_of_lackedNameB hn hσ
  simp only [hne, ↓reduceIte]

/-- The first signature of `ls` under the name `n`. -/
def sigNamed (c : Semantics) (ls : List CtorSig) (n : String) : Option CtorSig :=
  ls.find? fun k => c.symName k.name == n

/-- `G` read by name: the first signature of `ls` under the name gives the symbol. -/
def byName (c : Semantics) (ls : List CtorSig) (G : Sym → List GroundTerm → Option GroundTerm) :
    String → List GroundTerm → Option GroundTerm := fun n ws =>
  match sigNamed c ls n with
  | some k => G k.name ws
  | none => none

/-- The arity of a name: its first signature's. -/
def arNamed (c : Semantics) (ls : List CtorSig) (n : String) : Nat :=
  match sigNamed c ls n with
  | some k => k.args.length
  | none => 0

theorem sortsOf_each_lk {c : Semantics} : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss →
    ∀ w ∈ ws, ∃ s, c.sortOf w = some s
  | [], _, _, _, hw => by cases hw
  | w :: ws, ss, h, u, hu => by
    obtain ⟨s, ss', h1, h2, -⟩ := sortsOf_cons.mp h
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact ⟨s, h1⟩
    · exact sortsOf_each_lk h2 u hu'

/-- **One model of the theory, with `Step`'s steps, in which the symbols of `ls` denote `G` at
values.** For a semantics `coreOK` accepts under `FnHyp`, signatures `ls` each the first of `ls`
under its name, whose names Γ lacks, resolve to no symbol and decode to no instance, and a
partial function `G` whose values at values of a symbol's argument sorts are of its result sort. -/
theorem model_lacked (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (ls : List CtorSig)
    (G : Sym → List GroundTerm → Option GroundTerm)
    (hls : ∀ k ∈ ls, sigNamed c ls (c.symName k.name) = some k ∧ lackedNameB c (c.symName k.name) = true ∧
      GenEqs.unresolvedB c (c.symName k.name) = true ∧ instDecode? (c.symName k.name) = none)
    (hG : ∀ k ∈ ls, ∀ ws, c.sortsOf ws = some k.args → ∀ v, G k.name ws = some v → c.sortOf v = some k.result) :
    ∃ I : Interpretation KoreAML.Sym Faithful.Model.Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ∧
      LibEv.LackedDen c ls G I := by
  let N : String → Prop := fun n => ∃ k ∈ ls, c.symName k.name = n
  obtain ⟨I, hM, hstep⟩ := GenEqs.model_with_inits_arm c h hf N (arNamed c ls) (byName c ls G) (by
    rintro n ⟨k, hk, rfl⟩
    obtain ⟨-, hl, hu, -⟩ := hls k hk
    exact ⟨lacked_free h (not_gammaSym_of_lackedNameB hl), hu⟩)
  refine ⟨I, hM.sat, hstep, fun k hk ws hws => ⟨fun e m => ?_, hG k hk ws hws⟩⟩
  obtain ⟨hfirst, -, -, hite⟩ := hls k hk
  rw [GenEqs.symApp_den hite ws]
  have hlen : ws.length = arNamed c ls (c.symName k.name) := by
    rw [arNamed, hfirst]; exact Faithful.sortsOf_length hws
  rw [hM.names _ ⟨k, hk, rfl⟩ ws hlen (sortsOf_each_lk hws) e m]
  have hg : byName c ls G (c.symName k.name) ws = G k.name ws := by rw [byName, hfirst]
  rw [hg]
  cases hv : G k.name ws with
  | none => simp [Faithful.Res]
  | some v =>
    have hs := hG k hk ws hws v hv
    show (∃ v', some v = some v' ∧ m = .val v') ↔ (den c v).interpret I e m
    rw [hM.vals v k.result hs e m]
    simp

end TieLibParam

end KCore
