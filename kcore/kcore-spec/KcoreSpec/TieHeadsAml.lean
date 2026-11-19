/-
  The heads of the premises Γ builds directly as AML patterns, not as the translation of a KORE
  text: each applies only heads of Γ (`gammaHeadsP`), read by `headsP`.

  - The signature (`ΓSig`): every symbol's arity at the head `Term.kore` applies it at
    (`symArityItem`), and items that apply no symbol at all.
  - The constructors (`ΓCons`) under `coreOK`: each generator of a constructor sort is a symbol of
    Γ whose name the decoder reads as no instance, or the injection from a subsort; an overloading
    generator's covers and lifts are injections between sorts one below the other; the
    coherence triangles compose pairs of `subsorts`, which is transitive; the no-junk and law
    sentences are translations of KORE texts whose heads are such.
  - The collections (`ΓColls`, `collNoJunk`) under `coreOK`: a collection's unit, element and
    concatenation are symbols of Γ named plainly.
  - Bool's closure (`boolClosed`): domain values only.
-/
import KcoreSpec.TieHeadsWalk

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace KCore

open ML Faithful

namespace GHAml

open KoreAML (P)
open GHWalk

variable (c : Semantics)

/-- Every head the pattern applies is one of Γ's, as the translation writes them. -/
def InGH (φ : P) : Prop := ∀ h ∈ headsP φ, h ∈ gammaHeadsP c

variable {c}

/-! ## Connectives -/

theorem inGH_of_nil {φ : P} (h : headsA [] φ = []) : InGH c φ := by
  intro x hx; rw [headsP_def, h] at hx; cases hx

theorem inGH_of_eq {φ ψ : P} (h : headsA [] φ = headsA [] ψ) (hψ : InGH c ψ) : InGH c φ := by
  intro x hx; rw [headsP_def, h] at hx; exact hψ x hx

theorem inGH_of_append {φ a b : P} (h : headsA [] φ = headsA [] a ++ headsA [] b) (ha : InGH c a)
    (hb : InGH c b) : InGH c φ := by
  intro x hx
  rw [headsP_def, h, List.mem_append] at hx
  rcases hx with hx | hx
  · exact ha x hx
  · exact hb x hx

theorem inGH_imp {a b : P} (ha : InGH c a) (hb : InGH c b) : InGH c (a ⇒ b) :=
  inGH_of_append (headsA_imp [] a b) ha hb
theorem inGH_neg {a : P} (ha : InGH c a) : InGH c (∼a) := inGH_of_eq (headsA_neg [] a) ha
theorem inGH_and {a b : P} (ha : InGH c a) (hb : InGH c b) : InGH c (a ⋀ b) :=
  inGH_of_append (headsA_and [] a b) ha hb
theorem inGH_or {a b : P} (ha : InGH c a) (hb : InGH c b) : InGH c (a ⋁ b) :=
  inGH_of_append (headsA_or [] a b) ha hb
theorem inGH_eq {a b : P} (ha : InGH c a) (hb : InGH c b) : InGH c (a ≡ b) := by
  refine inGH_of_append (b := b ⋁ a) ((headsA_eq [] a b).trans ?_) (inGH_or ha hb) (inGH_or hb ha)
  rw [← headsA_or [] a b, ← headsA_or [] b a]
theorem inGH_member (x : EVar) {a : P} (ha : InGH c a) : InGH c (x ∈∈ a) := inGH_of_eq (headsA_member [] x a) ha
theorem inGH_included {a b : P} (ha : InGH c a) (hb : InGH c b) : InGH c (a ⊆⊆ b) :=
  inGH_of_append (headsA_included [] a b) ha hb
theorem inGH_forall (x : EVar) {a : P} (ha : InGH c a) : InGH c (∀∀ x a) := inGH_of_eq (headsA_forall [] x a) ha
theorem inGH_ex (x : EVar) {a : P} (ha : InGH c a) : InGH c (∃∃ x a) := inGH_of_eq (headsA_ex [] x a) ha
theorem inGH_mu (X : SVar) {a : P} (ha : InGH c a) : InGH c (.mu X a) := inGH_of_eq (headsA_mu [] X a) ha
theorem inGH_ceilD {a : P} (ha : InGH c a) : InGH c ⌈a⌉ := inGH_of_eq (headsA_ceilD [] a) ha
theorem inGH_inhOf {s : P} (hs : InGH c s) : InGH c (KoreAML.inhOf s) := inGH_of_eq (headsA_inhOf [] s) hs

theorem inGH_evar (x : EVar) : InGH c (.evar x) := inGH_of_nil rfl
theorem inGH_svar (X : SVar) : InGH c (.svar X) := inGH_of_nil rfl
theorem inGH_bot : InGH c (⊥ : P) := inGH_of_nil rfl
theorem inGH_top : InGH c (⊤ : P) := inGH_of_nil (by simp [Pattern.top, Pattern.negation])
theorem inGH_sortSym (n : String) : InGH c (KoreAML.sym (.sort n)) := inGH_of_nil rfl
theorem inGH_sortP (n : String) : InGH c (sortP n) := inGH_of_nil rfl
theorem inGH_sortSort : InGH c (KoreAML.sym .sortSort) := inGH_of_nil rfl
theorem inGH_trSort (t : KoreAML.VarTable) (s : Kore.KSort) : InGH c (KoreAML.trSort t s) :=
  inGH_of_nil (headsA_trSort t s [])

theorem inGH_conjList : ∀ (l : List P), (∀ φ ∈ l, InGH c φ) → InGH c (KoreAML.conjList l)
  | [], _ => inGH_top
  | [φ], h => h φ (List.mem_singleton_self _)
  | φ :: ψ :: l, h => inGH_and (h φ (List.mem_cons_self ..))
      (inGH_conjList (ψ :: l) fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem inGH_disjList : ∀ (l : List P), (∀ φ ∈ l, InGH c φ) → InGH c (KoreAML.disjList l)
  | [], _ => inGH_bot
  | [φ], h => h φ (List.mem_singleton_self _)
  | φ :: ψ :: l, h => inGH_or (h φ (List.mem_cons_self ..))
      (inGH_disjList (ψ :: l) fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem inGH_guarded {gs : List P} {φ : P} (hg : ∀ g ∈ gs, InGH c g) (hφ : InGH c φ) :
    InGH c (KoreAML.guarded gs φ) := by
  cases gs with
  | nil => exact hφ
  | cons g gs => exact inGH_imp (inGH_conjList _ hg) hφ

theorem inGH_sExists (x : EVar) {s φ : P} (hs : InGH c s) (hφ : InGH c φ) : InGH c (KoreAML.sExists x s φ) :=
  inGH_ex x (inGH_and (inGH_member x (inGH_inhOf hs)) hφ)

theorem inGH_notEqual {a b : P} (ha : InGH c a) (hb : InGH c b) : InGH c (KoreAML.notEqual a b) :=
  inGH_neg (inGH_eq ha hb)

theorem inGH_sNext {a : P} (ha : InGH c a) : InGH c (KoreAML.sNext a) :=
  inGH_of_eq (by simp [KoreAML.sNext, KoreAML.sym]) ha

theorem inGH_sCeil {s s' a : P} (hs : InGH c s) (hs' : InGH c s') (ha : InGH c a) :
    InGH c (KoreAML.sCeil s s' a) := by
  intro x hx
  simp only [KoreAML.sCeil, KoreAML.sym, headsP_def, headsA_app, headsA_ceil, List.nil_append,
    List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact hs x hx
  · exact hs' x hx
  · exact ha x hx

theorem inGH_sortGuard (x : EVar) : InGH c (KoreAML.sortGuard x) :=
  inGH_member x (inGH_inhOf inGH_sortSort)

/-! ## Chains -/

/-- The pattern is no sort: its chain does not start at a sort symbol. -/
theorem sortArgB_evar (x : EVar) : sortArgB (.evar x : P) = false := rfl
theorem sortArgB_svar (X : SVar) : sortArgB (.svar X : P) = false := rfl
theorem sortArgB_inhOf (s : P) : sortArgB (KoreAML.inhOf s) = false := rfl
theorem sortArgB_sortP (n : String) : sortArgB (sortP n) = true := rfl
theorem sortArgB_chain (n : String) (xs : List P) :
    sortArgB (KoreAML.appList (KoreAML.sym (.symbol n)) xs) = false := sortArgB_symbol n xs

/-- **A chain from a symbol at a head of Γ.** The chain `n ss xs`, the sorts `ss` holding no head
and the first of `xs` no sort, applies `(n, ss)` and the heads of `xs`. -/
theorem inGH_chain {n : String} {ss xs : List P} (hs : ∀ s ∈ ss, sortArgB s = true ∧ headsA [] s = [])
    (hx : ∀ y ∈ xs.head?, sortArgB y = false) (hn : (n, ss) ∈ gammaHeadsP c) (hxs : ∀ x ∈ xs, InGH c x) :
    InGH c (KoreAML.appList (KoreAML.sym (.symbol n)) (ss ++ xs)) := by
  intro h hh
  rcases headsP_chain n ss xs hs hx h hh with rfl | ⟨x, hx', hh⟩
  · exact hn
  · exact hxs x hx' h hh

/-- A chain from a symbol applied at no sort. -/
theorem inGH_plain {n : String} {xs : List P} (hx : ∀ y ∈ xs.head?, sortArgB y = false)
    (hn : (n, []) ∈ gammaHeadsP c) (hxs : ∀ x ∈ xs, InGH c x) :
    InGH c (KoreAML.appList (KoreAML.sym (.symbol n)) xs) :=
  inGH_chain (ss := []) (fun _ h => absurd h List.not_mem_nil) hx hn hxs

/-- `inj{A,B}(φ)` at a head of Γ. -/
theorem inGH_inj {A B : String} {φ : P} (hn : ("inj", [sortP A, sortP B]) ∈ gammaHeadsP c)
    (hφ' : sortArgB φ = false) (hφ : InGH c φ) :
    InGH c (KoreAML.appList (KoreAML.sym (.symbol "inj")) [sortP A, sortP B, φ]) :=
  inGH_chain (ss := [sortP A, sortP B]) (xs := [φ])
    (fun s hs => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact ⟨rfl, rfl⟩)
    (fun y hy => by cases hy; exact hφ') hn (fun x hx => by cases List.mem_singleton.mp hx; exact hφ)

theorem consSortP_eq (n : String) : KoreAML.Cons.sortP n = sortP n := rfl

/-! ## Γ's heads -/

/-- A symbol of Γ is applied at the head `symApp` writes for it, at its sorts. -/
theorem inst_memP_irs {k : CtorSig} (hk : k ∈ kernelSyms c) {h : String} {xs : List String}
    (hw : ∀ ps, symApp c k.name ps = .app ⟨⟨h⟩⟩ (xs.map KoreAML.srt) ps) :
    (h, xs.map sortP) ∈ gammaHeadsP c := by
  have : headP [] (gammaHead c k.name) = (h, xs.map sortP) := by
    rw [gammaHead_of_symApp hw]
    simp only [headP, List.map_map]
    congr 1
  rw [← this]
  exact List.mem_map_of_mem (List.mem_append_left _ (List.mem_map_of_mem hk))

/-- A symbol of Γ whose name the decoder reads as no instance is applied at no sort. -/
theorem plain_memP {k : CtorSig} (hk : k ∈ kernelSyms c) (hi : instDecode? (c.symName k.name) = none) :
    (c.symName k.name, []) ∈ gammaHeadsP c :=
  inst_memP_irs (xs := []) hk (fun _ => symApp_noInst hi)

/-- The injection at a pair of `subsorts`. -/
theorem inj_memP {a b : Srt} (h : (a, b) ∈ c.subsorts) :
    ("inj", [sortP (c.sortName a), sortP (c.sortName b)]) ∈ gammaHeadsP c := by
  have : headP [] ("inj", [KoreAML.srt (c.sortName a), KoreAML.srt (c.sortName b)]) =
      ("inj", [sortP (c.sortName a), sortP (c.sortName b)]) := by
    simp only [headP, List.map_cons, List.map_nil, trSort_srtG]; rfl
  rw [← this]
  exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_map_of_mem (f := fun (p : Srt × Srt) =>
    ("inj", [KoreAML.srt (c.sortName p.1), KoreAML.srt (c.sortName p.2)])) h))

theorem ks_ctor {k : CtorSig} (h : k ∈ c.ctorSigs) : k ∈ kernelSyms c := by
  unfold kernelSyms; simp [h]
theorem ks_fn {fn : Fn} (h : fn ∈ c.allFns) : fn.sig ∈ kernelSyms c := by
  unfold kernelSyms; simp only [List.mem_append, List.mem_map]; exact .inl (.inl (.inl (.inr ⟨fn, h, rfl⟩)))
theorem ks_param {k : ParamSig} (h : k ∈ c.params) : k.sig ∈ kernelSyms c := by
  unfold kernelSyms; simp only [List.mem_append, List.mem_map]; exact .inl (.inl (.inr ⟨k, h, rfl⟩))
theorem ks_hook {k : CtorSig} (h : k ∈ hookSigs) : k ∈ kernelSyms c := by
  unfold kernelSyms; simp [h]
theorem ks_ovl {k : CtorSig} (h : k ∈ c.ovlSigs) : k ∈ kernelSyms c := by
  unfold kernelSyms; simp [h]

/-- Closes `InGH c φ` for a pattern built from connectives, variables, sorts and the symbols that
are no symbol of the signature (definedness, inhabitants, ceilings, next, domain values). -/
macro "ghv_close" : tactic => `(tactic| repeat (first
  | exact inGH_evar _ | exact inGH_svar _ | exact inGH_bot | exact inGH_sortSym _ | exact inGH_sortP _
  | exact inGH_sortSort | exact inGH_trSort _ _ | exact inGH_of_nil rfl
  | apply inGH_ceilD | apply inGH_inhOf | apply inGH_sCeil | apply inGH_sNext
  | apply inGH_imp | apply inGH_ex | apply inGH_mu))

/-! ## The signature -/

/-- **Every symbol's arity item applies the symbol at its head of Γ**, `gammaHead`. -/
theorem symArityItem_inGH {k : CtorSig} (hk : k ∈ kernelSyms c) : InGH c (symArityItem c k).pat := by
  obtain ⟨h, xs, -, hw⟩ := symApp_head c k.name
  rw [symArityItem_of_symApp hw, instHeadP_appList_irs, ← appList_append]
  refine inGH_included ?_ (inGH_inhOf (inGH_sortP _))
  refine inGH_chain (fun s hs => ?_) ?_ (inst_memP_irs hk hw) ?_
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hs; exact ⟨rfl, rfl⟩
  · intro y hy
    cases hargs : k.args with
    | nil => rw [hargs] at hy; cases hy
    | cons a as => rw [hargs] at hy; cases hy; rfl
  · intro x hx
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
    exact inGH_inhOf (inGH_sortP _)

theorem definedness_inGH (x : EVar) : InGH c (@definedness KoreAML.Sym _ x) :=
  inGH_forall x (inGH_ceilD (inGH_evar x))

/-- **The signature's items apply Γ's heads only.** -/
theorem sigItems_inGH : ∀ it ∈ sigItems c, InGH c it.pat := by
  intro it hit
  simp only [sigItems, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hit
  rcases hit with (((rfl | ⟨s, -, rfl⟩) | ⟨k, hk, rfl⟩) | (rfl | rfl | rfl))
  · exact definedness_inGH _
  · simp only [KoreAML.sortConstantItem, sortDeclOf, KoreAML.paramTable, List.map_nil, KoreAML.appList]
    ghv_close
  · exact symArityItem_inGH hk
  · simp only [KoreAML.ceilArityItem]; ghv_close
  · simp only [KoreAML.ceilDefItem]; ghv_close
  · simp only [KoreAML.nextArityItem, srtOf, KoreAML.srt, KoreAML.sortVarsOf, KoreAML.sortVarsOfList,
      List.eraseDups_nil, List.map_nil, KoreAML.guarded]
    ghv_close

/-- A domain value's arity applies no symbol. -/
theorem dvArityItem_inGH (lit : String) : InGH c (KoreAML.dvArityItem lit).pat := by
  simp only [KoreAML.dvArityItem]; ghv_close

/-- The premises of a list of items whose patterns apply Γ's heads only apply Γ's heads only. -/
theorem itemsPremises_inGH {its : List KoreAML.Item} (h : ∀ it ∈ its, InGH c it.pat) :
    ∀ φ, KoreAML.itemsPremises its φ → InGH c φ := by
  rintro φ (⟨it, hit, rfl⟩ | ⟨x, rfl⟩)
  · exact h it hit
  · exact definedness_inGH x

/-- **The signature applies Γ's heads only.** -/
theorem ΓSig_inGH : ∀ φ, ΓSig c φ → InGH c φ := by
  rintro φ (h | ⟨lit, rfl⟩)
  · exact itemsPremises_inGH sigItems_inGH φ h
  · exact dvArityItem_inGH lit

/-! ## Translated sentences -/

theorem guardOf_inGH (t : KoreAML.VarTable) (k : KoreAML.VarKey) : InGH c (KoreAML.guardOf t k) := by
  cases k with
  | sortVar _ => exact inGH_sortGuard _
  | evar _ s => exact inGH_member _ (inGH_inhOf (inGH_trSort t s))
  | svar _ s => exact inGH_included (inGH_svar _) (inGH_inhOf (inGH_trSort t s))

/-- **A translated sentence applies Γ's heads only where its KORE pattern does**: the guards and
the sort of the sentence apply no symbol. -/
theorem trAxiom_inGH (decls : List KoreAML.SymbolDecl) (aliases : List String) (ad : KoreAML.AxiomDecl)
    (hp : ∀ h ∈ appHeadsOf ad.ax.pattern, h ∈ gammaHeads c) : InGH c (KoreAML.trAxiom decls aliases ad).pat := by
  unfold KoreAML.trAxiom
  refine inGH_imp (inGH_conjList _ fun g hg => ?_) (inGH_eq (headsP_tr_gamma c _ _ hp) ?_)
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
    exact guardOf_inGH _ k
  · split
    · exact inGH_inhOf (inGH_trSort _ _)
    · exact inGH_of_nil rfl

/-! ## Bool's closure -/

/-- **Bool's closure applies no symbol**: it holds domain values only. -/
theorem boolClosed_inGH : InGH c (boolClosed c) :=
  inGH_included (inGH_inhOf (inGH_sortP _))
    (inGH_or (headsP_tr_gamma c _ _ (by simp [GroundTerm.kore, appHeadsOf]))
      (headsP_tr_gamma c _ _ (by simp [GroundTerm.kore, appHeadsOf])))

theorem Γcl_inGH : ∀ φ, Γcl c φ → InGH c φ := by
  rintro φ ⟨-, -, rfl⟩; exact boolClosed_inGH

/-! ## The constructors' items, at heads given -/

/-- A head of Γ, as the KORE of the semantics writes it: a symbol of Γ named plainly. -/
theorem plain_mem {k : CtorSig} (hk : k ∈ kernelSyms c) (hi : instDecode? (c.symName k.name) = none) :
    (c.symName k.name, []) ∈ gammaHeads c := by
  have : gammaHead c k.name = (c.symName k.name, []) := gammaHead_noInst hi
  rw [← this]; exact List.mem_append_left _ (List.mem_map_of_mem hk)

/-- The injection at a pair of `subsorts`, as the KORE writes it. -/
theorem inj_mem {a b : Srt} (h : (a, b) ∈ c.subsorts) :
    ("inj", [KoreAML.srt (c.sortName a), KoreAML.srt (c.sortName b)]) ∈ gammaHeads c :=
  List.mem_append_right _ (List.mem_map_of_mem (f := fun (p : Srt × Srt) =>
    ("inj", [KoreAML.srt (c.sortName p.1), KoreAML.srt (c.sortName p.2)])) h)

/-- A generator of the sort `N` at a head of Γ: a symbol of Γ named plainly, or the injection from
a sort below `N`. -/
def GenS (c : Semantics) (N : Srt) : Gen → Prop
  | .ctor k => k ∈ kernelSyms c ∧ instDecode? (c.symName k.name) = none
  | .inj a => (a, N) ∈ c.subsorts

theorem head_evars (xs : List EVar) : ∀ y ∈ (xs.map Pattern.evar : List P).head?, sortArgB y = false := by
  intro y hy
  cases xs with
  | nil => cases hy
  | cons x xs => cases hy; rfl

theorem inGH_evars (xs : List EVar) : ∀ x ∈ (xs.map Pattern.evar : List P), InGH c x := by
  intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact inGH_evar y

/-- A generator applied to variables applies its head only. -/
theorem genPat_inGH {N : Srt} {g : Gen} (hg : GenS c N g) (xs : List EVar) :
    InGH c (KoreAML.Cons.genPat (c.sortName N) (Gen.toK c g) (xs.map .evar)) := by
  cases g with
  | ctor k => exact inGH_plain (head_evars xs) (plain_memP hg.1 hg.2) (inGH_evars xs)
  | inj a =>
    show InGH c (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      ([sortP (c.sortName a), sortP (c.sortName N)] ++ xs.map .evar))
    refine inGH_chain (fun s hs => ?_) (head_evars xs) (inj_memP hg) (inGH_evars xs)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem memGuards_inGH (vs : List EVar) (ss : List String) :
    ∀ g ∈ KoreAML.Cons.memGuards vs ss, InGH c g := by
  intro g hg
  obtain ⟨⟨x, s⟩, -, rfl⟩ := List.mem_map.mp hg
  exact inGH_member x (inGH_inhOf (inGH_sortSym _))

theorem inGH_guarded_app {gs gs' : List P} {φ : P} (hg : ∀ g ∈ gs, InGH c g) (hg' : ∀ g ∈ gs', InGH c g)
    (hφ : InGH c φ) : InGH c (KoreAML.guarded (gs ++ gs') φ) :=
  inGH_guarded (fun g h => (List.mem_append.mp h).elim (hg g) (hg' g)) hφ

/-- The covers `covs` of arguments of the sorts `bs` are, where they differ, sorts below them. -/
def CovS (c : Semantics) (bs : List String) (covs : List (List String)) : Prop :=
  ∀ as ∈ covs, ∀ A B, (A, B) ∈ as.zip bs → A ≠ B → ("inj", [sortP A, sortP B]) ∈ gammaHeadsP c

theorem covS_nil (bs : List String) : CovS c bs [] := fun _ h => absurd h List.not_mem_nil

theorem uncoveredP_inGH {bs : List String} {covs : List (List String)} (h : CovS c bs covs)
    (x : List EVar) (z : EVar) : InGH c (KoreAML.Cons.uncoveredP bs covs x z) := by
  unfold KoreAML.Cons.uncoveredP
  refine inGH_conjList _ fun d hd => ?_
  obtain ⟨as, has, rfl⟩ := List.mem_map.mp hd
  refine inGH_disjList _ fun e he => ?_
  obtain ⟨⟨⟨A, B⟩, xi⟩, hm, he⟩ := List.mem_filterMap.mp he
  by_cases hne : (A == B) = true
  · simp only [hne, ite_true] at he; cases he
  · simp only [hne, Bool.false_eq_true, ite_false, Option.some.injEq] at he
    subst he
    have hAB : A ≠ B := fun h' => hne (by rw [h']; exact beq_self_eq_true B)
    exact inGH_neg (inGH_sExists z (inGH_sortSym _) (inGH_eq (inGH_evar _)
      (inGH_inj (h as has A B (List.of_mem_zip hm).1 hAB) rfl (inGH_evar _))))

theorem funItem_inGH {N : Srt} {g : Gen} (hg : GenS c N g) :
    InGH c (KoreAML.Cons.funItem (c.sortName N) (Gen.toK c g)).pat :=
  inGH_guarded (memGuards_inGH _ _) (inGH_sExists _ (inGH_sortSym _) (inGH_eq (genPat_inGH hg _) (inGH_evar _)))

theorem funUncItem_inGH {N : Srt} {g : Gen} (hg : GenS c N g) {covs : List (List String)}
    (hc : CovS c (Gen.toK c g).argSorts covs) :
    InGH c (KoreAML.Cons.funUncItem (c.sortName N) (Gen.toK c g) covs).pat :=
  inGH_guarded_app (memGuards_inGH _ _) (fun u hu => by
      cases List.mem_singleton.mp hu; exact uncoveredP_inGH hc _ _)
    (inGH_sExists _ (inGH_sortSym _) (inGH_eq (genPat_inGH hg _) (inGH_evar _)))

theorem eqs_inGH (xy : List (EVar × EVar)) :
    InGH c (KoreAML.conjList (xy.map fun (a, b) => (.evar a ≡ .evar b : P))) :=
  inGH_conjList _ fun e he => by
    obtain ⟨⟨a, b⟩, -, rfl⟩ := List.mem_map.mp he; exact inGH_eq (inGH_evar a) (inGH_evar b)

theorem injItem_inGH {N : Srt} {g : Gen} (hg : GenS c N g) :
    InGH c (KoreAML.Cons.injItem (c.sortName N) (Gen.toK c g)).pat :=
  inGH_guarded_app (memGuards_inGH _ _) (memGuards_inGH _ _)
    (inGH_imp (inGH_eq (genPat_inGH hg _) (genPat_inGH hg _)) (eqs_inGH _))

theorem injUncItem_inGH {N : Srt} {g : Gen} (hg : GenS c N g) {covs : List (List String)}
    (hc : CovS c (Gen.toK c g).argSorts covs) :
    InGH c (KoreAML.Cons.injUncItem (c.sortName N) (Gen.toK c g) covs).pat :=
  inGH_guarded_app (fun u hu => (List.mem_append.mp hu).elim (memGuards_inGH _ _ u) (memGuards_inGH _ _ u))
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact uncoveredP_inGH hc _ _)
    (inGH_imp (inGH_eq (genPat_inGH hg _) (genPat_inGH hg _)) (eqs_inGH _))

theorem distItem_inGH {N : Srt} {g g' : Gen} (hg : GenS c N g) (hg' : GenS c N g') :
    InGH c (KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')).pat :=
  inGH_guarded_app (memGuards_inGH _ _) (memGuards_inGH _ _)
    (inGH_notEqual (genPat_inGH hg _) (genPat_inGH hg' _))

theorem distUncItem_inGH {N : Srt} {g g' : Gen} (hg : GenS c N g) (hg' : GenS c N g')
    {ug ug' : Option (List (List String))}
    (hu : ∀ covs, ug = some covs → CovS c (Gen.toK c g).argSorts covs)
    (hu' : ∀ covs, ug' = some covs → CovS c (Gen.toK c g').argSorts covs) :
    InGH c (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') ug ug').pat := by
  unfold KoreAML.Cons.distUncItem
  refine inGH_guarded (fun u hu0 => ?_) (inGH_notEqual (genPat_inGH hg _) (genPat_inGH hg' _))
  simp only [List.mem_append] at hu0
  rcases hu0 with ((hu0 | hu0) | hu0) | hu0
  · exact memGuards_inGH _ _ u hu0
  · exact memGuards_inGH _ _ u hu0
  · cases hug : ug with
    | none => rw [hug] at hu0; cases hu0
    | some covs => rw [hug] at hu0; cases List.mem_singleton.mp hu0; exact uncoveredP_inGH (hu covs hug) _ _
  · cases hug : ug' with
    | none => rw [hug] at hu0; cases hu0
    | some covs => rw [hug] at hu0; cases List.mem_singleton.mp hu0; exact uncoveredP_inGH (hu' covs hug) _ _

theorem distLbItem_inGH {N a b : Srt} (ha : (a, N) ∈ c.subsorts) (hb : (b, N) ∈ c.subsorts) {lbs : List Srt}
    (hl : ∀ C ∈ lbs, (C, a) ∈ c.subsorts ∧ (C, b) ∈ c.subsorts) :
    InGH c (distLbItem (c.sortName N) (c.sortName a) (c.sortName b) (lbs.map c.sortName)).pat := by
  simp only [distLbItem]
  refine inGH_guarded (fun u hu => ?_) (inGH_imp (inGH_eq (inGH_inj (inj_memP ha) rfl (inGH_evar _))
    (inGH_inj (inj_memP hb) rfl (inGH_evar _))) (inGH_disjList _ fun d hd => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact inGH_member _ (inGH_inhOf (inGH_sortP _))
  · simp only [List.map_map, List.mem_map, Function.comp_def] at hd
    obtain ⟨C, hC, rfl⟩ := hd
    exact inGH_sExists _ (inGH_sortP _) (inGH_and
      (inGH_eq (inGH_evar _) (inGH_inj (inj_memP (hl C hC).1) rfl (inGH_evar _)))
      (inGH_eq (inGH_evar _) (inGH_inj (inj_memP (hl C hC).2) rfl (inGH_evar _))))

theorem cohItem_inGH {a b e : Srt} (hab : (a, b) ∈ c.subsorts) (hbe : (b, e) ∈ c.subsorts)
    (hae : (a, e) ∈ c.subsorts) :
    InGH c (KoreAML.Cons.cohItem (c.sortName a) (c.sortName b) (c.sortName e)).pat := by
  simp only [KoreAML.Cons.cohItem]
  exact inGH_guarded (fun u hu => by cases List.mem_singleton.mp hu; exact inGH_member _ (inGH_inhOf (inGH_sortSym _)))
    (inGH_eq (inGH_inj (inj_memP hbe) (sortArgB_chain _ _) (inGH_inj (inj_memP hab) rfl (inGH_evar _)))
      (inGH_inj (inj_memP hae) rfl (inGH_evar _)))

/-- `liftP A B φ` of an overload equation, at sorts one below the other where their names differ. -/
theorem inGH_lift {A B : Srt} {φ : P} (h : c.sortName A ≠ c.sortName B → (A, B) ∈ c.subsorts)
    (hφ' : sortArgB φ = false) (hφ : InGH c φ) :
    InGH c (if (c.sortName A == c.sortName B) = true then φ else
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName A),
        KoreAML.Cons.sortP (c.sortName B), φ]) := by
  split
  · exact hφ
  · rename_i hne
    exact inGH_inj (inj_memP (h fun h' => hne (by rw [h']; exact beq_self_eq_true _))) hφ' hφ

theorem sortArgB_lift (A B : String) (φ : P) (hφ' : sortArgB φ = false) :
    sortArgB (if (A == B) = true then φ else
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ]) = false := by
  split
  · exact hφ'
  · exact sortArgB_chain _ _

/-- An overload equation of `f` over `g`, both symbols of Γ named plainly, whose lifts are between
sorts one below the other. -/
theorem ovlEqItem_inGH {f g : CtorSig} (hf : f ∈ kernelSyms c) (hfi : instDecode? (c.symName f.name) = none)
    (hg : g ∈ kernelSyms c) (hgi : instDecode? (c.symName g.name) = none)
    (hargs : ∀ A B, (A, B) ∈ g.args.zip f.args → c.sortName A ≠ c.sortName B → (A, B) ∈ c.subsorts)
    (hres : c.sortName g.result ≠ c.sortName f.result → (g.result, f.result) ∈ c.subsorts) :
    InGH c (KoreAML.Cons.ovlEqItem (KCore.toK c f) (KCore.toK c g)).pat := by
  unfold KoreAML.Cons.ovlEqItem
  refine inGH_guarded (memGuards_inGH _ _) (inGH_eq (inGH_plain ?_ (plain_memP hf hfi) ?_)
    (inGH_lift hres (sortArgB_chain _ _) (inGH_plain (head_evars _) (plain_memP hg hgi) (inGH_evars _))))
  · intro y hy
    simp only [KCore.toK] at hy
    simp only [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hy
    obtain ⟨⟨⟨A, B⟩, xi⟩, -, rfl⟩ := hy
    exact sortArgB_lift _ _ _ rfl
  · intro y hy
    simp only [KCore.toK, List.zip_map, List.mem_map] at hy
    obtain ⟨⟨⟨A', B'⟩, xi⟩, hm, rfl⟩ := hy
    obtain ⟨⟨A, B⟩, hAB, he⟩ := List.mem_map.mp (List.of_mem_zip hm).1
    simp only [Prod.map, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact inGH_lift (hargs A B hAB) rfl (inGH_evar _)

/-! ## Translated constructor sentences -/

theorem appHeadsOfList_vars (xs : List Kore.EVar) : appHeadsOfList (KoreAML.vars xs) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show appHeadsOfList (Kore.Pattern.var (.evar x) :: KoreAML.vars xs) = []
    rw [appHeadsOfList, ih]; rfl

theorem appHeadsOf_existsAll (s : Kore.KSort) (body : Kore.Pattern) :
    ∀ bs : List Kore.EVar, appHeadsOf (KoreAML.existsAll s bs body) = appHeadsOf body
  | [] => rfl
  | b :: bs => by
    show appHeadsOf (.exist s b (KoreAML.existsAll s bs body)) = _
    rw [appHeadsOf, appHeadsOf_existsAll s body bs]

/-- The heads of the no-junk disjuncts of the generators `gs` of `N`: each generator's head. -/
theorem noJunkDisjuncts_heads (N : String) (Q : String × List Kore.KSort → Prop) :
    ∀ (gs : List KoreAML.Gen) (seen : List (String × List String)),
    (∀ g ∈ gs, match g with
      | .ctor k => Q (k.name, [])
      | .inj a => Q ("inj", [KoreAML.srt a, KoreAML.srt N])) →
    ∀ h ∈ appHeadsOfList (KoreAML.noJunkDisjuncts N seen gs), Q h
  | [], _, _, h, hh => by simp [KoreAML.noJunkDisjuncts, appHeadsOfList, appHeadsOf] at hh
  | .ctor k :: gs, seen, hg, h, hh => by
    simp only [KoreAML.noJunkDisjuncts, appHeadsOfList, List.mem_append] at hh
    rcases hh with hh | hh
    · rw [appHeadsOf_existsAll] at hh
      simp only [KoreAML.ap, appHeadsOf, appHeadsOfList_vars, List.mem_singleton] at hh
      subst hh
      exact hg _ (List.mem_cons_self ..)
    · exact noJunkDisjuncts_heads N Q gs _ (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) h hh
  | .inj a :: gs, seen, hg, h, hh => by
    simp only [KoreAML.noJunkDisjuncts, appHeadsOfList, List.mem_append] at hh
    rcases hh with hh | hh
    · simp only [appHeadsOf, KoreAML.injP, appHeadsOfList, List.append_nil, List.mem_singleton] at hh
      subst hh
      exact hg _ (List.mem_cons_self ..)
    · exact noJunkDisjuncts_heads N Q gs _ (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) h hh

/-- **The no-junk sentence of a sort whose generators are at heads of Γ** applies those only. -/
theorem noJunkItem_inGH {N : Srt} {gs : List Gen} (hg : ∀ g ∈ gs, GenS c N g) :
    InGH c (KoreAML.Cons.noJunkItem (c.sortName N) (gs.map (Gen.toK c))).pat := by
  show InGH c (KoreAML.trAxiom [] [] ⟨0, "kernel", KoreAML.Cons.noJunkAx _ _⟩).pat
  refine trAxiom_inGH _ _ _ fun h hh => ?_
  simp only [KoreAML.Cons.noJunkAx, appHeadsOf] at hh
  refine noJunkDisjuncts_heads _ (· ∈ gammaHeads c) _ [] (fun g' hg' => ?_) h hh
  obtain ⟨g, hg0, rfl⟩ := List.mem_map.mp hg'
  cases g with
  | ctor k => exact plain_mem (hg _ hg0).1 (hg _ hg0).2
  | inj a => exact inj_mem (hg _ hg0)

/-! ## What `coreOK` says of the generators -/

theorem namesNumbered_of_core (h : c.coreOK = true) : namesNumbered c = true := by
  have := (Semantics.coreOK_parts h).2.1
  simp only [Semantics.faithCoreOK, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := this
  exact h1

theorem collsOK_of_core (h : c.coreOK = true) : collsOK c = true := by
  have := (Semantics.coreOK_parts h).2.1
  simp only [Semantics.faithCoreOK, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := this
  exact h4

/-- A constructor is named plainly. -/
theorem ctor_ite (h : c.coreOK = true) {k : CtorSig} (hk : k ∈ c.ctorSigs) : instDecode? (c.symName k.name) = none := by
  have := namesNumbered_of_core h
  simp only [namesNumbered, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1.1 k hk

/-- A symbol that an overloading symbol overloads is named plainly. -/
theorem over_ite (h : c.coreOK = true) {o : OvlSig} (ho : o ∈ c.ovls) {g : Sym} (hg : g ∈ o.over) :
    instDecode? (c.symName g) = none := by
  have := namesNumbered_of_core h
  simp only [namesNumbered, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1.2 o ho g hg

/-- What `overloadsOK` says of each overloading symbol: `lookupOvl` finds it under its name, it
is named plainly, and each signature it overloads has argument and result sorts at most its own. -/
theorem ovl_at (hok : c.overloadsOK = true) {o : OvlSig} (ho : o ∈ c.ovls) :
    c.lookupOvl o.sig.name = some o ∧ instDecode? (c.symName o.sig.name) = none ∧
      ∀ kg ∈ c.ovlOver o, c.ovlPairOK o kg = true := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
  have hok := ((Bool.and_eq_true _ _).mp hok).1
  simp only [List.all_eq_true] at hok
  have hoi := hok (o, i) (List.mem_zipIdx_iff_getElem?.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, List.all_eq_true] at hoi
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, -⟩, -⟩, -⟩, h7⟩, -⟩, -⟩ := hoi
  exact ⟨h2, h3, h7⟩

theorem ovlSig_ite (h : c.coreOK = true) {k : CtorSig} (hk : k ∈ c.ovlSigs) : instDecode? (c.symName k.name) = none := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hk
  exact (ovl_at (Semantics.coreOK_ovls h) ho).2.1

/-- Every generator of a sort is at a head of Γ: a constructor, an overloading symbol or an open
generator (a raw parameter) is a symbol of Γ named plainly; an injection is from a subsort. -/
theorem gens_ok (h : c.coreOK = true) {N : Srt} {g : Gen} (hg : g ∈ c.gens N) : GenS c N g := by
  simp only [Semantics.gens, List.mem_append, List.mem_map, List.mem_filter] at hg
  rcases hg with ((⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩) | ⟨k, ⟨⟨p, ⟨hp, hr⟩, rfl⟩, -⟩, rfl⟩) | ⟨a, ha, rfl⟩
  · exact ⟨ks_ctor hk, ctor_ite h hk⟩
  · exact ⟨ks_ovl hk, ovlSig_ite h hk⟩
  · exact ⟨ks_param hp, Semantics.raw_noInst_core_irs h hp hr⟩
  · rw [mem_sortBy] at ha
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_filter, beq_iff_eq] at hab
    show (a', N) ∈ c.subsorts
    rw [← hab.2]; exact hab.1

/-- The covers of an overloading generator, as `consItemsK` reads them. -/
def ovlArgsG (c : Semantics) (g : Gen) : Option (List (List String)) :=
  match g with
  | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o => (c.ovlOver o).map fun kg => kg.args.map c.sortName
    else none
  | .inj _ => none

/-- A sort pair `le` relates whose names differ is a pair of `subsorts`. -/
theorem sub_of_le_names {A B : Srt} (hle : c.le A B = true) (hn : c.sortName A ≠ c.sortName B) :
    (A, B) ∈ c.subsorts :=
  OvlLaws.mem_of_le hle fun h' => hn (by rw [h'])

/-- The pairs of the zip of two lists of sorts, under the names, where `ovlPairOK` relates them. -/
theorem zip_names_sub {o : OvlSig} {kg : CtorSig} (hp : c.ovlPairOK o kg = true) :
    ∀ A B, (A, B) ∈ kg.args.zip o.sig.args → c.sortName A ≠ c.sortName B → (A, B) ∈ c.subsorts := by
  intro A B hm hn
  simp only [Semantics.ovlPairOK, Bool.and_eq_true, List.all_eq_true] at hp
  exact sub_of_le_names (hp.1.2 (A, B) hm) hn

/-- An overloading generator's covers are of sorts below its argument sorts. -/
theorem ovlArgs_cov (h : c.coreOK = true) {N : Srt} {g : Gen} (hg : g ∈ c.gens N) :
    ∀ covs, ovlArgsG c g = some covs → CovS c (Gen.toK c g).argSorts covs := by
  intro covs hcov
  cases g with
  | inj a => cases hcov
  | ctor k =>
    simp only [ovlArgsG] at hcov
    split at hcov
    · rename_i hiso
      obtain ⟨o, hlo, rfl⟩ := Option.map_eq_some_iff.mp hcov
      obtain ⟨hct, -, hpar, -, -⟩ := c.isOvl_parts hiso
      have hok := Semantics.coreOK_ovls h
      -- the generator is the overloading symbol's own signature
      have hko : k = o.sig := by
        simp only [Semantics.gens, List.mem_append, List.mem_map, List.mem_filter] at hg
        rcases hg with ((⟨k', ⟨hk', -⟩, he⟩ | ⟨k', ⟨hk', -⟩, he⟩) | ⟨k', ⟨⟨p, ⟨hp, -⟩, rfl⟩, -⟩, he⟩) | ⟨a, -, he⟩
        · cases he
          have : (lookupSig c.ctorSigs k.name).isSome = true := by
            rw [lookupSig_eq, List.find?_isSome]; exact ⟨k, hk', beq_self_eq_true _⟩
          simp [Semantics.isCtor, this] at hct
        · cases he
          obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hk'
          have := (ovl_at hok ho').1
          rw [hlo] at this; cases this; rfl
        · cases he
          have : (c.lookupParam p.sig.name).isSome = true := by
            rw [Semantics.lookupParam_eq, List.find?_isSome]; exact ⟨p, hp, beq_self_eq_true _⟩
          simp [Semantics.isParam, this] at hpar
        · cases he
      subst hko
      have ho := (OvlLaws.ovl_parts hok hlo).1
      intro as has A B hAB hne
      obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp has
      simp only [Gen.toK, KoreAML.Gen.argSorts, KCore.toK, List.zip_map, List.mem_map, Prod.map,
        Prod.mk.injEq] at hAB
      obtain ⟨⟨A', B'⟩, hm, rfl, rfl⟩ := hAB
      have hsub := zip_names_sub ((ovl_at hok ho).2.2 kg hkg) A' B' hm hne
      exact inj_memP hsub
    · cases hcov

theorem covS_getD (h : c.coreOK = true) {N : Srt} {g : Gen} (hg : g ∈ c.gens N) :
    CovS c (Gen.toK c g).argSorts ((ovlArgsG c g).getD []) := by
  cases hc : ovlArgsG c g with
  | none => exact covS_nil _
  | some covs => exact ovlArgs_cov h hg covs hc

theorem mem_pairs_ghv {α : Type} : ∀ {l : List α} {a b : α}, (a, b) ∈ pairs l → a ∈ l ∧ b ∈ l
  | [], _, _, h => by simp [pairs] at h
  | x :: xs, a, b, h => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨y, hy, rfl, rfl⟩ | h
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hy⟩
    · have := mem_pairs_ghv h; exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

theorem lowerBounds_sub {a b C : Srt} (h : C ∈ c.lowerBounds a b) :
    (C, a) ∈ c.subsorts ∧ (C, b) ∈ c.subsorts := by
  simp only [Semantics.lowerBounds, mem_sortBy, List.mem_filter, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.2

/-- A signature an overloading symbol overloads is a symbol of Γ named plainly. -/
theorem over_ok (h : c.coreOK = true) {o : OvlSig} (ho : o ∈ c.ovls) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) :
    kg ∈ kernelSyms c ∧ instDecode? (c.symName kg.name) = none := by
  have hok := Semantics.coreOK_ovls h
  obtain ⟨g, -, hg⟩ := List.mem_filterMap.mp hkg
  rcases List.mem_append.mp (lookupSig_spec hg).1 with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact ⟨ks_ctor hm, ctor_ite h hm⟩
    · exact ⟨ks_ovl hm, ovlSig_ite h hm⟩
  · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hm
    exact ⟨ks_fn (List.mem_append_left _ hfn), over_ite h ho (OvlLaws.mem_ovlOver hkg)⟩

/-- **The constructors' items apply Γ's heads only**, under `coreOK`. -/
theorem consItemsK_inGH (h : c.coreOK = true) : ∀ it ∈ consItemsK c, InGH c it.pat := by
  intro it hit
  have hok := Semantics.coreOK_ovls h
  simp only [consItemsK, List.mem_append] at hit
  rcases hit with ((hps | hcoh) | hov) | hlaw
  · obtain ⟨N, -, hit⟩ := List.mem_flatMap.mp hps
    simp only [List.mem_append] at hit
    rcases hit with ((hf | hi) | hd) | hnj
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      have hg0 := (List.mem_filter.mp hg).1
      split
      · exact funUncItem_inGH (gens_ok h hg0) (covS_getD h hg0)
      · exact funItem_inGH (gens_ok h hg0)
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
      have hg0 := (List.mem_filter.mp (List.mem_filter.mp hg).1).1
      split
      · exact injUncItem_inGH (gens_ok h hg0) (covS_getD h hg0)
      · exact injItem_inGH (gens_ok h hg0)
    · obtain ⟨⟨g, g'⟩, hgg, hit⟩ := List.mem_flatMap.mp hd
      obtain ⟨hg, hg'⟩ := mem_pairs_ghv hgg
      have hg0 := (List.mem_filter.mp hg).1
      have hg0' := (List.mem_filter.mp hg').1
      have hgen : ∀ it ∈ (if c.distGuarded g g' = true then
          [KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsG c g) (ovlArgsG c g')]
          else [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')]), InGH c it.pat := by
        intro it hit
        split at hit
        · cases List.mem_singleton.mp hit
          exact distUncItem_inGH (gens_ok h hg0) (gens_ok h hg0') (ovlArgs_cov h hg0) (ovlArgs_cov h hg0')
        · cases List.mem_singleton.mp hit
          exact distItem_inGH (gens_ok h hg0) (gens_ok h hg0')
      cases g with
      | ctor k => cases g' with
        | ctor k' => exact hgen it hit
        | inj b => exact hgen it hit
      | inj a => cases g' with
        | ctor k' => exact hgen it hit
        | inj b =>
          simp only at hit
          split at hit
          · cases hit
          · split at hit
            · cases List.mem_singleton.mp hit
              exact distItem_inGH (gens_ok h hg0) (gens_ok h hg0')
            · cases List.mem_singleton.mp hit
              exact distLbItem_inGH (gens_ok h hg0) (gens_ok h hg0') fun C hC => lowerBounds_sub hC
    · split at hnj
      · cases hnj
      · cases List.mem_singleton.mp hnj
        exact noJunkItem_inGH fun g hg => gens_ok h hg
  · obtain ⟨⟨a, b⟩, hab, hit⟩ := List.mem_flatMap.mp hcoh
    obtain ⟨⟨b', e⟩, hbe, rfl⟩ := List.mem_map.mp hit
    simp only [List.mem_filter, beq_iff_eq] at hbe
    obtain ⟨hbe, rfl⟩ := hbe
    have hp := Semantics.coreOK_parts h
    exact cohItem_inGH hab hbe (NamesApart.subsorts_trans_of hp.2.2.2.2 hp.1 a b' e hab hbe)
  · obtain ⟨o, ho, hit⟩ := List.mem_flatMap.mp hov
    obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp hit
    have hpo := (ovl_at hok ho).2.2 kg hkg
    have hkgo := over_ok h ho hkg
    refine ovlEqItem_inGH (ks_ovl (List.mem_map_of_mem ho)) (ovl_at hok ho).2.1 hkgo.1 hkgo.2
      (zip_names_sub hpo) fun hn => ?_
    simp only [Semantics.ovlPairOK, Bool.and_eq_true] at hpo
    exact sub_of_le_names hpo.2 hn
  · obtain ⟨k, hk, hit⟩ := List.mem_flatMap.mp hlaw
    split at hit
    · rename_i hr
      have hm := plain_mem (ks_param hk) (Semantics.raw_noInst_core_irs h hk hr)
      rcases List.mem_append.mp hit with hit | hit
      · split at hit
        · cases List.mem_singleton.mp hit
          exact trAxiom_inGH _ _ _ (by simp [assocAxK, appHeadsOf, appHeadsOfList, KoreAML.ap, KoreAML.ev, hm])
        · cases hit
      · split at hit
        · cases List.mem_singleton.mp hit
          exact trAxiom_inGH _ _ _ (by simp [idemAxK, appHeadsOf, appHeadsOfList, KoreAML.ap, KoreAML.ev, hm])
        · cases hit
    · cases hit

/-- **The constructors apply Γ's heads only**, under `coreOK`. -/
theorem ΓCons_inGH (h : c.coreOK = true) : ∀ φ, ΓCons c φ → InGH c φ :=
  itemsPremises_inGH (consItemsK_inGH h)

/-! ## The collections -/

/-- The library's collections' unit, element and concatenation are interpreted hooked symbols of
the registry, named plainly. -/
theorem builtinColls_reg : ∀ k ∈ builtinColls, ∀ f ∈ [k.unit, k.elem, k.concat],
    (f < nRegSyms ∧ instDecode? (regSymNames.getD f "") = none) ∧ hookSigs.any (·.name == f) = true := by
  decide +kernel

/-- **A collection's unit, element and concatenation are symbols of Γ named plainly**, under
`coreOK`: the library's are interpreted hooked symbols; a definition's own are parameter symbols
(`collSymsOK`). -/
theorem collSyms_ks (h : c.coreOK = true) {k : CollSig} (hk : k ∈ c.allColls) :
    ∀ f ∈ [k.unit, k.elem, k.concat], ∃ k' ∈ kernelSyms c, k'.name = f ∧ instDecode? (c.symName f) = none := by
  intro f hf
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨⟨hr, hi⟩, ha⟩ := builtinColls_reg k hk f hf
    obtain ⟨s, hs, hn⟩ := List.any_eq_true.mp ha
    have hn : s.name = f := beq_iff_eq.mp hn
    exact ⟨s, ks_hook hs, hn, Faithful.noInst_reg_irs hr hi⟩
  · have hck := List.all_eq_true.mp (by
      have := collsOK_of_core h
      simp only [collsOK, Bool.and_eq_true] at this
      exact this.1) k hk
    simp only [collSymsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hck
    obtain ⟨⟨⟨⟨⟨-, hite⟩, hu⟩, he⟩, hc⟩, -⟩ := hck
    have hi : instDecode? (c.symName f) = none := by
      have := hite f hf
      simp only [Option.isNone_iff_eq_none] at this
      exact this.2
    have hp : ∀ p : ParamSig, c.lookupParam f = some p →
        ∃ k' ∈ kernelSyms c, k'.name = f ∧ instDecode? (c.symName f) = none := by
      intro p hp
      rw [Semantics.lookupParam_eq] at hp
      exact ⟨p.sig, ks_param (List.mem_of_find?_eq_some hp), by simpa using List.find?_some hp, hi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact hp _ hu
    · exact hp _ he
    · exact hp _ hc

theorem collSyms_ok (h : c.coreOK = true) {k : CollSig} (hk : k ∈ c.allColls) :
    ∀ f ∈ [k.unit, k.elem, k.concat], (c.symName f, []) ∈ gammaHeadsP c := by
  intro f hf
  obtain ⟨k', hk', rfl, hi⟩ := collSyms_ks h hk f hf
  exact plain_memP hk' hi

section Coll
variable {k : CollSig} (hS : ∀ f ∈ [k.unit, k.elem, k.concat], (c.symName f, []) ∈ gammaHeadsP c)
include hS

theorem inGH_collU : InGH c (collU c k) :=
  inGH_plain (xs := []) (fun _ h => by cases h) (hS _ (List.mem_cons_self ..)) (fun _ h => by cases h)

theorem inGH_collE {a b : P} (ha' : sortArgB a = false) (ha : InGH c a) (hb : InGH c b) :
    InGH c (collE c k a b) :=
  inGH_plain (xs := [a, b]) (fun y hy => by cases hy; exact ha')
    (hS _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb)

theorem inGH_collC {a b : P} (ha' : sortArgB a = false) (ha : InGH c a) (hb : InGH c b) :
    InGH c (collC c k a b) :=
  inGH_plain (xs := [a, b]) (fun y hy => by cases hy; exact ha')
    (hS _ (by simp)) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb)

theorem inGH_collI {a : P} (ha' : sortArgB a = false) (ha : InGH c a) : InGH c (collI c k a) :=
  inGH_plain (xs := [a]) (fun y hy => by cases hy; exact ha')
    (hS _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (fun x hx => by
      cases List.mem_singleton.mp hx; exact ha)

end Coll

theorem inGH_guarded' {gs : List P} {φ : P} (hg : InGH c (KoreAML.conjList gs)) (hφ : InGH c φ) :
    InGH c (KoreAML.guarded gs φ) := by
  cases gs with
  | nil => exact hφ
  | cons g gs => exact inGH_imp hg hφ

theorem inGH_conjCons {a : P} {l : List P} (ha : InGH c a) (hl : InGH c (KoreAML.conjList l)) :
    InGH c (KoreAML.conjList (a :: l)) := by
  cases l with
  | nil => exact ha
  | cons b l => exact inGH_and ha hl

theorem inGH_conjNil : InGH c (KoreAML.conjList []) := inGH_top

theorem inGH_inSort (x : EVar) (s : Srt) : InGH c (x ∈∈ inSort c s) := inGH_member x (inGH_inhOf (inGH_sortP _))

/-- Closes `InGH c φ` for a collection's axiom, given the collection's symbols at heads of Γ: each
step matches the head of the pattern syntactically. -/
macro "ghv_coll " h:term : tactic => `(tactic| repeat (first
  | with_reducible exact inGH_evar _ | with_reducible exact inGH_svar _ | with_reducible exact inGH_inSort _ _
  | with_reducible exact inGH_conjNil
  | with_reducible exact inGH_collU $h | with_reducible apply inGH_collE $h | with_reducible apply inGH_collC $h
  | with_reducible apply inGH_collI $h
  | with_reducible apply inGH_guarded' | with_reducible apply inGH_conjCons | with_reducible apply inGH_sExists
  | with_reducible exact inGH_sortP _
  | with_reducible apply inGH_eq | with_reducible apply inGH_and | with_reducible apply inGH_or
  | with_reducible apply inGH_neg | with_reducible apply inGH_ceilD | with_reducible apply inGH_imp
  | rfl))

/-- **No junk in a collection sort applies Γ's heads only**, under `coreOK`. -/
theorem collNoJunk_inGH (h : c.coreOK = true) {k : CollSig} (hk : k ∈ c.allColls) : InGH c (collNoJunk c k) := by
  have hS := collSyms_ok h hk
  have hel : ∀ φ, φ = (match k.kind with
    | .map | .rangeMap => KoreAML.appList (symP (c.symName k.elem))
        [KoreAML.inhOf (sortP (c.sortName k.key)), KoreAML.inhOf (sortP (c.sortName (valSort k)))]
    | _ => KoreAML.appList (symP (c.symName k.elem)) [KoreAML.inhOf (sortP (c.sortName k.key))]) →
      InGH c φ ∧ sortArgB φ = false := by
    rintro φ rfl
    split
    · exact ⟨inGH_collE hS rfl (inGH_inhOf (inGH_sortP _)) (inGH_inhOf (inGH_sortP _)), sortArgB_chain _ _⟩
    · exact ⟨inGH_collE hS rfl (inGH_inhOf (inGH_sortP _)) (inGH_inhOf (inGH_sortP _)), sortArgB_chain _ _⟩
    · exact ⟨inGH_collI hS rfl (inGH_inhOf (inGH_sortP _)), sortArgB_chain _ _⟩
  obtain ⟨h1, h2⟩ := hel _ rfl
  exact inGH_included (inGH_inhOf (inGH_sortP _)) (inGH_mu _ (inGH_or (inGH_collU hS) (inGH_collC hS h2 h1 (inGH_svar _))))

section CollAx
variable {k : CollSig} (hS : ∀ f ∈ [k.unit, k.elem, k.concat], (c.symName f, []) ∈ gammaHeadsP c)
include hS

theorem mapUnitSplitAx_inGH : InGH c (mapUnitSplitAx c k) := by
  simp only [mapUnitSplitAx]; ghv_coll hS

theorem mapElemNotUnitAx_inGH : InGH c (mapElemNotUnitAx c k) := by
  simp only [mapElemNotUnitAx]; ghv_coll hS

theorem mapElemAtomAx_inGH : InGH c (mapElemAtomAx c k) := by
  simp only [mapElemAtomAx]; ghv_coll hS

theorem mapDecompAx_inGH : InGH c (mapDecompAx c k) := by
  simp only [mapDecompAx]; ghv_coll hS

theorem setUnitSplitAx_inGH : InGH c (setUnitSplitAx c k) := by
  simp only [setUnitSplitAx]; ghv_coll hS

theorem setElemNotUnitAx_inGH : InGH c (setElemNotUnitAx c k) := by
  simp only [setElemNotUnitAx]; ghv_coll hS

theorem setElemAtomAx_inGH : InGH c (setElemAtomAx c k) := by
  simp only [setElemAtomAx]; ghv_coll hS

theorem setDecompAx_inGH : InGH c (setDecompAx c k) := by
  simp only [setDecompAx]; ghv_coll hS

theorem listUnitSplitAx_inGH : InGH c (listUnitSplitAx c k) := by
  simp only [listUnitSplitAx]; ghv_coll hS

theorem listElemNotUnitAx_inGH : InGH c (listElemNotUnitAx c k) := by
  simp only [listElemNotUnitAx]; ghv_coll hS

theorem listElemAtomAx_inGH : InGH c (listElemAtomAx c k) := by
  simp only [listElemAtomAx]; ghv_coll hS

theorem listElemAtomBackAx_inGH : InGH c (listElemAtomBackAx c k) := by
  simp only [listElemAtomBackAx]; ghv_coll hS

theorem listDecompAx_inGH : InGH c (listDecompAx c k) := by
  simp only [listDecompAx]; ghv_coll hS

end CollAx

/-- **A collection's axioms apply Γ's heads only**, under `coreOK`. -/
theorem collAxioms_inGH (h : c.coreOK = true) {k : CollSig} (hk : k ∈ c.allColls) :
    ∀ φ ∈ collAxioms c k, InGH c φ := by
  have hS := collSyms_ok h hk
  intro φ hφ
  unfold collAxioms at hφ
  split at hφ
  · simp only [mapCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact mapUnitSplitAx_inGH hS
    · exact mapElemNotUnitAx_inGH hS
    · exact mapElemAtomAx_inGH hS
    · exact mapDecompAx_inGH hS
  · simp only [setCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact setUnitSplitAx_inGH hS
    · exact setElemNotUnitAx_inGH hS
    · exact setElemAtomAx_inGH hS
    · exact setDecompAx_inGH hS
  · simp only [listCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact listUnitSplitAx_inGH hS
    · exact listElemNotUnitAx_inGH hS
    · exact listElemAtomAx_inGH hS
    · exact listElemAtomBackAx_inGH hS
    · exact listDecompAx_inGH hS
  · cases hφ

/-- **The collections apply Γ's heads only**, under `coreOK`. -/
theorem ΓColls_inGH (h : c.coreOK = true) : ∀ φ, ΓColls c φ → InGH c φ := by
  rintro φ ⟨k, hk, hφ⟩; exact collAxioms_inGH h hk φ hφ

end GHAml

end KCore
