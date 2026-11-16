/-
  KCore. The cut identity on KoreAML patterns: a pattern φ in a context built of applications is
  the context at a fresh element variable x, under `∃x` with x in φ.

  - `cut_sem`: in every interpretation, `C[φ]` is the union of `C[a]` over the elements a of φ.
  - `cut_identity`: `∃x. (C[x] ∧ ⌈x ∧ φ⌉)` is `C[φ]` where `⌈_⌉` is definedness (`DefOK`).
  - `cut_sorted`: at KORE's sorted `\exists{S'}(x:S, \and{S'}(C[x], \in{S,S'}(x, φ)))`, the same
    where every element of φ is in the sort S and every element of `C[φ]` in S';
    `cut_sorted_only_if`: without them it fails (at the empty context the sorted cut puts every
    element of φ in S and in S').
  - `mem_and`, `mem_or`, `mem_not`: membership of one element of S distributes over the sorted
    `\and`, `\or` and `\not`.
-/
import KcoreSpec.FaithfulTr

set_option autoImplicit false

namespace KoreAML

open ML

variable {M : Type} {I : Interpretation Sym M}

/-- A context built of applications: a hole, an application whose function part holds the hole, or
one whose argument holds it. `σ(φ₁, …, φₙ)` is `σ ⬝ φ₁ ⬝ … ⬝ φₙ`, so a KORE context of nested
applications (injections and sort arguments included) is one of these. -/
inductive CutCtx where
  | hole
  | fn (C : CutCtx) (ψ : P)
  | arg (ψ : P) (C : CutCtx)

def CutCtx.fill : CutCtx → P → P
  | .hole, φ => φ
  | .fn C ψ, φ => C.fill φ ⬝ ψ
  | .arg ψ C, φ => ψ ⬝ C.fill φ

/-- The pattern does not read the element variable x in I. -/
def NoReadCut (I : Interpretation Sym M) (x : EVar) (ψ : P) : Prop :=
  ∀ (e : Valuation M) (a m : M),
    ψ.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m ↔ ψ.interpret I e m

/-- No pattern beside the hole reads x. -/
def CutCtx.Fresh (I : Interpretation Sym M) (x : EVar) : CutCtx → Prop
  | .hole => True
  | .fn C ψ => C.Fresh I x ∧ NoReadCut I x ψ
  | .arg ψ C => NoReadCut I x ψ ∧ C.Fresh I x

/-- **The cut identity, as sets**: in every interpretation, `C[φ]` is the union of `C[a]` over the
elements a of φ. No hypothesis on I, on φ or on the number of elements of φ. -/
theorem cut_sem (x : EVar) (φ : P) : ∀ (C : CutCtx), C.Fresh I x → ∀ (e : Valuation M) (m : M),
    (C.fill φ).interpret I e m ↔
      ∃ a, φ.interpret I e a ∧
        (C.fill (.evar x)).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m
  | .hole, _, e, m => by
    constructor
    · intro h
      refine ⟨m, h, ?_⟩
      show m = Function.update e.evalEvar x m x
      simp
    · rintro ⟨a, ha, hm⟩
      have : m = Function.update e.evalEvar x a x := hm
      simp at this
      rw [this]; exact ha
  | .fn C ψ, hC, e, m => by
    show (C.fill φ ⬝ ψ).interpret I e m ↔ ∃ a, _ ∧ (C.fill (.evar x) ⬝ ψ).interpret I _ m
    rw [interp_app]
    constructor
    · rintro ⟨p, b, hp, hb, hpb⟩
      obtain ⟨a, ha, hpa⟩ := (cut_sem x φ C hC.1 e p).mp hp
      exact ⟨a, ha, interp_app.mpr ⟨p, b, hpa, (hC.2 e a b).mpr hb, hpb⟩⟩
    · rintro ⟨a, ha, hm⟩
      obtain ⟨p, b, hpa, hb, hpb⟩ := interp_app.mp hm
      exact ⟨p, b, (cut_sem x φ C hC.1 e p).mpr ⟨a, ha, hpa⟩, (hC.2 e a b).mp hb, hpb⟩
  | .arg ψ C, hC, e, m => by
    show (ψ ⬝ C.fill φ).interpret I e m ↔ ∃ a, _ ∧ (ψ ⬝ C.fill (.evar x)).interpret I _ m
    rw [interp_app]
    constructor
    · rintro ⟨p, b, hp, hb, hpb⟩
      obtain ⟨a, ha, hba⟩ := (cut_sem x φ C hC.2 e b).mp hb
      exact ⟨a, ha, interp_app.mpr ⟨p, b, (hC.1 e a p).mpr hp, hba, hpb⟩⟩
    · rintro ⟨a, ha, hm⟩
      obtain ⟨p, b, hp, hba, hpb⟩ := interp_app.mp hm
      exact ⟨p, b, (hC.1 e a p).mp hp, (cut_sem x φ C hC.2 e b).mpr ⟨a, ha, hba⟩, hpb⟩

/-- **The cut identity, as a pattern without sorts**: `∃x. (C[x] ∧ ⌈x ∧ φ⌉)` is `C[φ]`, where
definedness is definedness and φ does not read x. -/
theorem cut_identity (hD : DefOK I) (x : EVar) (φ : P) (hφ : NoReadCut I x φ)
    (C : CutCtx) (hC : C.Fresh I x) (e : Valuation M) (m : M) :
    (∃∃ x (C.fill (.evar x) ⋀ ⌈(Pattern.evar x : P) ⋀ φ⌉)).interpret I e m ↔
      (C.fill φ).interpret I e m := by
  rw [cut_sem x φ C hC e m, ML.interpret_exists]
  constructor
  · rintro ⟨a, ha⟩
    rw [ML.interpret_conj, interp_defined hD] at ha
    obtain ⟨hC', b, hb⟩ := ha
    rw [ML.interpret_conj] at hb
    have hba : b = Function.update e.evalEvar x a x := hb.1
    simp at hba
    exact ⟨a, by rw [← hba]; exact (hφ e a b).mp hb.2, hC'⟩
  · rintro ⟨a, ha, hC'⟩
    refine ⟨a, ?_⟩
    rw [ML.interpret_conj, interp_defined hD]
    refine ⟨hC', a, ?_⟩
    rw [ML.interpret_conj]
    refine ⟨?_, (hφ e a a).mpr ha⟩
    show a = Function.update e.evalEvar x a x
    simp

/-- **The cut identity at KORE's sorted connectives**: `\exists{S'}(x:S, \and{S'}(C[x], \in{S,S'}(x, φ)))`
is `C[φ]`, where S and S' denote sorts, every element of φ is in S and every element of `C[φ]` is
in S'. The two inclusions are not consequences of the interpretation alone: see the
`cut_sorted_only_if`. -/
theorem cut_sorted [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (x : EVar) (φ S S' : P) (hφ : NoReadCut I x φ) (hSx : NoReadCut I x S) (hS'x : NoReadCut I x S')
    (C : CutCtx) (hC : C.Fresh I x) (e : Valuation M) {σ σ' : M}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hS' : ∀ a, S'.interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hφs : ∀ a, φ.interpret I e a → Inh I σ a)
    (hCs : ∀ m, (C.fill φ).interpret I e m → Inh I σ' m) (m : M) :
    (sExists x S (sAnd (C.fill (.evar x)) (sIn S S' (.evar x) φ))).interpret I e m ↔
      (C.fill φ).interpret I e m := by
  rw [cut_sem x φ C hC e m, interp_sExists]
  have hSu : ∀ a b, S.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ :=
    fun a b => (hSx e a b).trans (hS b)
  have hS'u : ∀ a b, S'.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ' :=
    fun a b => (hS'x e a b).trans (hS' b)
  constructor
  · rintro ⟨a, hxa, hand⟩
    rw [interp_sAnd] at hand
    obtain ⟨hC', hin⟩ := hand
    rw [interp_member hD, interp_inhOf_of (hSu a)] at hxa
    have hxs : ∀ b, (Pattern.evar x : P).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b →
        Inh I σ b := fun b hb => by
      have hb' : b = Function.update e.evalEvar x a x := hb
      rw [hb']; exact hxa
    rw [interp_sIn hD hc (hSu a) (hS'u a) hσ hσ' hxs] at hin
    obtain ⟨⟨b, hb1, hb2⟩, -⟩ := hin
    have hba : b = Function.update e.evalEvar x a x := hb1
    simp at hba
    exact ⟨a, by rw [← hba]; exact (hφ e a b).mp hb2, hC'⟩
  · rintro ⟨a, ha, hC'⟩
    have hxa : Inh I σ (Function.update e.evalEvar x a x) := by simpa using hφs a ha
    have hxs : ∀ b, (Pattern.evar x : P).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b →
        Inh I σ b := fun b hb => by
      have hb' : b = Function.update e.evalEvar x a x := hb
      rw [hb']; exact hxa
    refine ⟨a, ?_, ?_⟩
    · rw [interp_member hD, interp_inhOf_of (hSu a)]; exact hxa
    · rw [interp_sAnd, interp_sIn hD hc (hSu a) (hS'u a) hσ hσ' hxs]
      refine ⟨hC', ⟨a, ?_, (hφ e a a).mpr ha⟩, hCs m ((cut_sem x φ C hC e m).mpr ⟨a, ha, hC'⟩)⟩
      show a = Function.update e.evalEvar x a x
      simp

/-- **The sorted form states more than the set identity**: at the empty context, if the sorted cut
is φ then every element of φ is in S and in S'. So an interpretation with an element of φ outside S
is a counter-example to the sorted identity; `hφs` and `hCs` of `cut_sorted` are needed. -/
theorem cut_sorted_only_if [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (x : EVar) (φ S S' : P) (hSx : NoReadCut I x S) (hS'x : NoReadCut I x S')
    (e : Valuation M) {σ σ' : M}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hS' : ∀ a, S'.interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (h : ∀ m, (sExists x S (sAnd (CutCtx.hole.fill (.evar x))
      (sIn S S' (.evar x) φ))).interpret I e m ↔ (CutCtx.hole.fill φ).interpret I e m) :
    ∀ a, φ.interpret I e a → Inh I σ a ∧ Inh I σ' a := by
  intro m hm
  have hSu : ∀ a b, S.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ :=
    fun a b => (hSx e a b).trans (hS b)
  have hS'u : ∀ a b, S'.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b ↔ b = σ' :=
    fun a b => (hS'x e a b).trans (hS' b)
  obtain ⟨a, hxa, hand⟩ := interp_sExists.mp ((h m).mpr hm)
  rw [interp_sAnd] at hand
  obtain ⟨hC', hin⟩ := hand
  rw [interp_member hD, interp_inhOf_of (hSu a)] at hxa
  have hxs : ∀ b, (Pattern.evar x : P).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ b →
      Inh I σ b := fun b hb => by
    have hb' : b = Function.update e.evalEvar x a x := hb
    rw [hb']; exact hxa
  rw [interp_sIn hD hc (hSu a) (hS'u a) hσ hσ' hxs] at hin
  have hma : m = Function.update e.evalEvar x a x := hC'
  exact ⟨by rw [hma]; exact hxa, hin.2⟩

/-! ### Membership of one element distributes over the connectives

What ties `post := or (mem Z a) (mem Z b)` to `Z ∈ \or(a, b)` and
`pre := not (and (mem Z a) (mem Z G))` to `Z ∈ \not(\and(a, G))`: at an element x of S and an
element m of S'. -/

section Mem
variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
  {e : Valuation M} {S S' : P} {σ σ' : M}
  (hS : ∀ a, S.interpret I e a ↔ a = σ) (hS' : ∀ a, S'.interpret I e a ↔ a = σ')
  (hσ : IsSort I σ) (hσ' : IsSort I σ')
  (x : EVar) (hx : Inh I σ (e.evalEvar x))
include hD hc hS hS' hσ hσ' hx

theorem mem_iff_cut (φ : P) (m : M) :
    (sIn S S' (.evar x) φ).interpret I e m ↔ φ.interpret I e (e.evalEvar x) ∧ Inh I σ' m := by
  have hxs : ∀ b, (Pattern.evar x : P).interpret I e b → Inh I σ b := fun b hb => by
    have hb' : b = e.evalEvar x := hb
    rw [hb']; exact hx
  rw [interp_sIn hD hc hS hS' hσ hσ' hxs]
  constructor
  · rintro ⟨⟨a, (ha : a = e.evalEvar x), hφ⟩, hm⟩; exact ⟨ha ▸ hφ, hm⟩
  · rintro ⟨hφ, hm⟩; exact ⟨⟨_, (rfl : e.evalEvar x = e.evalEvar x), hφ⟩, hm⟩

theorem mem_or (φ ψ : P) (m : M) :
    (sIn S S' (.evar x) (sOr S φ ψ)).interpret I e m ↔
      (sOr S' (sIn S S' (.evar x) φ) (sIn S S' (.evar x) ψ)).interpret I e m := by
  rw [mem_iff_cut hD hc hS hS' hσ hσ' x hx, interp_sOr, interp_sOr,
    mem_iff_cut hD hc hS hS' hσ hσ' x hx, mem_iff_cut hD hc hS hS' hσ hσ' x hx,
    interp_inhOf_of hS, interp_inhOf_of hS']
  constructor
  · rintro ⟨⟨-, h | h⟩, hm⟩
    · exact ⟨hm, .inl ⟨h, hm⟩⟩
    · exact ⟨hm, .inr ⟨h, hm⟩⟩
  · rintro ⟨hm, h | h⟩
    · exact ⟨⟨hx, .inl h.1⟩, hm⟩
    · exact ⟨⟨hx, .inr h.1⟩, hm⟩

theorem mem_and (φ ψ : P) (m : M) :
    (sIn S S' (.evar x) (sAnd φ ψ)).interpret I e m ↔
      (sAnd (sIn S S' (.evar x) φ) (sIn S S' (.evar x) ψ)).interpret I e m := by
  rw [mem_iff_cut hD hc hS hS' hσ hσ' x hx, interp_sAnd, interp_sAnd,
    mem_iff_cut hD hc hS hS' hσ hσ' x hx, mem_iff_cut hD hc hS hS' hσ hσ' x hx]
  exact ⟨fun ⟨⟨h1, h2⟩, hm⟩ => ⟨⟨h1, hm⟩, ⟨h2, hm⟩⟩, fun ⟨⟨h1, hm⟩, ⟨h2, _⟩⟩ => ⟨⟨h1, h2⟩, hm⟩⟩

theorem mem_not (φ : P) (m : M) :
    (sIn S S' (.evar x) (sNot S φ)).interpret I e m ↔
      (sNot S' (sIn S S' (.evar x) φ)).interpret I e m := by
  rw [mem_iff_cut hD hc hS hS' hσ hσ' x hx, interp_sNot, interp_sNot,
    mem_iff_cut hD hc hS hS' hσ hσ' x hx, interp_inhOf_of hS, interp_inhOf_of hS']
  exact ⟨fun ⟨⟨hn, _⟩, hm⟩ => ⟨fun h => hn h.1, hm⟩, fun ⟨hn, hm⟩ => ⟨⟨fun h => hn ⟨h, hm⟩, hx⟩, hm⟩⟩

end Mem

/-! ## The translation of a KORE application context

A KORE context of nested applications (injections are applications of `inj` with two sort
arguments) translates to a `CutCtx`: at each layer the side patterns are the head with its sort
arguments and the arguments before the hole, then the arguments after it, each translated. -/

/-- A KORE application context: the hole, or an application `h{ss}(pre, C, post)` with the hole in
the argument after `pre`. -/
inductive KoreCutCtx where
  | hole
  | app (h : Kore.SymbolIdent) (ss : List Kore.KSort) (pre : List Kore.Pattern) (C : KoreCutCtx)
      (post : List Kore.Pattern)

def KoreCutCtx.fill : KoreCutCtx → Kore.Pattern → Kore.Pattern
  | .hole, φ => φ
  | .app h ss pre C post, φ => .app h ss (pre ++ C.fill φ :: post)

/-- No head on the path to the hole is one of `ctx`'s aliases (whose applications `tr` does not
translate). -/
def KoreCutCtx.noAlias (ctx : Ctx) : KoreCutCtx → Bool
  | .hole => true
  | .app h _ _ C _ => !ctx.aliases.contains h.ident.name && C.noAlias ctx

/-- `C` with the patterns `ψs` applied after it, left to right. -/
def CutCtx.fns : CutCtx → List P → CutCtx
  | C, [] => C
  | C, ψ :: ψs => CutCtx.fns (.fn C ψ) ψs

/-- The context of AML applications that `tr ctx` makes of a KORE application context. -/
def KoreCutCtx.toCut (ctx : Ctx) : KoreCutCtx → CutCtx
  | .hole => .hole
  | .app h ss pre C post =>
    (CutCtx.arg (trArgs ctx (trSortApp ctx.vars (sym (.symbol h.ident.name)) ss) pre)
      (C.toCut ctx)).fns (post.map (tr ctx))

theorem CutCtx.fill_fns_trArgs (ctx : Ctx) (χ : P) :
    ∀ (post : List Kore.Pattern) (C : CutCtx),
      (C.fns (post.map (tr ctx))).fill χ = trArgs ctx (C.fill χ) post
  | [], C => by rw [List.map_nil, CutCtx.fns, trArgs_nil]
  | q :: qs, C => by
    rw [List.map_cons, CutCtx.fns, CutCtx.fill_fns_trArgs ctx χ qs, trArgs_cons]; rfl

theorem trArgs_append_cut (ctx : Ctx) : ∀ (pre : List Kore.Pattern) (acc : P) (p : Kore.Pattern)
    (post : List Kore.Pattern),
    trArgs ctx acc (pre ++ p :: post) = trArgs ctx (trArgs ctx acc pre ⬝ tr ctx p) post
  | [], acc, p, post => by rw [List.nil_append, trArgs_cons, trArgs_nil]
  | q :: qs, acc, p, post => by
    rw [List.cons_append, trArgs_cons, trArgs_cons, trArgs_append_cut ctx qs]

/-- **`tr` of a KORE application context is a `CutCtx`**: where no head on the path to the hole is
an alias, `tr ctx (K[φ])` is `(K.toCut ctx)[tr ctx φ]`, so `cut_sem`, `cut_identity` and
`cut_sorted` apply to the translation. -/
theorem tr_cutCtx (ctx : Ctx) (φ : Kore.Pattern) :
    ∀ (K : KoreCutCtx), K.noAlias ctx = true → tr ctx (K.fill φ) = (K.toCut ctx).fill (tr ctx φ)
  | .hole, _ => rfl
  | .app h ss pre C post, hK => by
    simp only [KoreCutCtx.noAlias, Bool.and_eq_true, Bool.not_eq_true'] at hK
    rw [KoreCutCtx.fill, tr]
    split
    · simp_all
    · rw [trArgs_append_cut, tr_cutCtx ctx φ C hK.2, KoreCutCtx.toCut, CutCtx.fill_fns_trArgs]
      rfl

/-- The side patterns of `K.toCut ctx` do not read x: at each layer the head with the arguments
before the hole, and each argument after it. -/
def KoreCutCtx.SidesNoRead (I : Interpretation Sym M) (ctx : Ctx) (x : EVar) : KoreCutCtx → Prop
  | .hole => True
  | .app h ss pre C post =>
    NoReadCut I x (trArgs ctx (trSortApp ctx.vars (sym (.symbol h.ident.name)) ss) pre) ∧
      (∀ q ∈ post, NoReadCut I x (tr ctx q)) ∧ C.SidesNoRead I ctx x

theorem CutCtx.fresh_fns {x : EVar} : ∀ (ψs : List P) (C : CutCtx), C.Fresh I x →
    (∀ ψ ∈ ψs, NoReadCut I x ψ) → (C.fns ψs).Fresh I x
  | [], _, hC, _ => hC
  | ψ :: ψs, C, hC, h =>
    CutCtx.fresh_fns ψs (.fn C ψ) ⟨hC, h ψ (List.mem_cons_self ..)⟩
      (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))

theorem KoreCutCtx.toCut_fresh {ctx : Ctx} {x : EVar} :
    ∀ (K : KoreCutCtx), K.SidesNoRead I ctx x → (K.toCut ctx).Fresh I x
  | .hole, _ => trivial
  | .app _ _ _ C _, ⟨h1, h2, h3⟩ =>
    CutCtx.fresh_fns _ _ ⟨h1, KoreCutCtx.toCut_fresh C h3⟩ (fun ψ hψ => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hψ
      exact h2 q hq)

/-- A closed pattern reads no variable. -/
theorem NoReadCut.of_closed {ψ : P} (h : Closed ψ) (x : EVar) : NoReadCut I x ψ :=
  fun e _ m => h.interp _ e m

end KoreAML
