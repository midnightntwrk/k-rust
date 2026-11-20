/-
  KCore, outside the cone: `TieRuleCut.rightDefined_of_Γ` for a right side that also holds
  injections.

  `TieRuleCut.builtB` reads a pattern built of variables and of constructors applied without sort
  arguments. A rule's right side holds its term in the `k` cell under `inj{S, KItem}`, a symbol
  with two sort arguments, which is a generator of KItem with a Cons-Fun item of its own
  (`KoreAML.Cons.funItem "KItem" (.inj S)`).

  - `builtGB gs fT p s`: `p` is of the sort named `s` and is built of the element variables of `fT`
    and of applications of the generators of `gs` (`KoreAML.Gen`: a constructor, without sort
    arguments, or the injection `inj{A, s}` from the sort named A) to arguments built so.
  - `builtGB_one`: such a pattern denotes one element of its sort where the guards of `fT` hold and
    each generator of `gs` has its Cons-Fun item.
  - `rightDefined_of_funsG`, `funsInGB`, `rightDefined_of_ΓG`: so `⌈r ∧ ⊤⌉` holds in every model of
    Γ, of every element of the rule's sort, where the guards of the variables hold.
  - `rightDefined_top`: the same at an element of `\top` of the rule's sort.
  - `inj_inh`: every element of `inj{A, N}(p)` is in N where every element of `p` is in A, from the
    injection's Cons-Fun item; `funsInGB_cons`: the items `funsInGB` finds are of `ΓCons`.
  - `built_inh`: every element of a built pattern is in its sort, in a model of Γ.
  - `equals_top`: an element of a `requires` `\equals{s, C}` at the rule's sort C is one of
    `\top{C}`, so `rightDefined_top` reads a left side with a `requires` too.
  - Not read: a domain value, a function call, a connective, a set variable.
-/
import KcoreSpec.TieRuleCut

set_option autoImplicit false

namespace KCore

namespace TieRuleCutG

open ML Faithful KoreAML

/-- The head `h` with the sort arguments `ss` is the generator `g` of the sort named `s`. -/
def headGB (g : KoreAML.Gen) (h : Kore.SymbolIdent) (ss : List Kore.KSort) (s : String) : Bool :=
  match g with
  | .ctor k => decide (ss = []) && decide (h.ident.name = k.name)
  | .inj A => decide (h.ident.name = "inj") && decide (ss = [srt A, srt s])

mutual
/-- `p` is of the sort named `s` and is built of the element variables of `fT` and of applications
of the generators of `gs` (each with the name of the sort its Cons-Fun item is of) to arguments
built so, of the generator's argument sorts. -/
def builtGB (gs : List (String × KoreAML.Gen)) (fT : List VarKey) : Kore.Pattern → String → Bool
  | .var (.evar x), s => decide (x.sort = srt s) && fT.contains (evarKey x)
  | .app h ss ps, s =>
    match gs.find? (fun g => g.1 == s && headGB g.2 h ss s) with
    | some g => builtGArgsB gs fT ps g.2.argSorts
    | none => false
  | _, _ => false
  termination_by structural p => p
def builtGArgsB (gs : List (String × KoreAML.Gen)) (fT : List VarKey) : List Kore.Pattern → List String → Bool
  | [], [] => true
  | p :: ps, s :: ss => builtGB gs fT p s && builtGArgsB gs fT ps ss
  | _, _ => false
  termination_by structural ps => ps
end

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- The translation of a generator's head with its sort arguments is the generator's head. -/
theorem headGB_tr {g : KoreAML.Gen} {h : Kore.SymbolIdent} {ss : List Kore.KSort} {s : String}
    (hh : headGB g h ss s = true) (t : VarTable) :
    trSortApp t (sym (.symbol h.ident.name)) ss = genHead s g := by
  cases g with
  | ctor k =>
    simp only [headGB, Bool.and_eq_true, decide_eq_true_eq] at hh
    rw [hh.1, hh.2]; rfl
  | inj A =>
    simp only [headGB, Bool.and_eq_true, decide_eq_true_eq] at hh
    rw [hh.1, hh.2]
    simp only [trSortApp, trSort_srt, genHead, appList, KoreAML.Cons.sortP]

variable {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {t : VarTable}
  {e : Valuation M} {m0 : M}

mutual
/-- A pattern with `builtGB` denotes one element, of its sort, where the guards of `fT` hold and
each generator of `gs` has its Cons-Fun item. -/
theorem builtGB_one (hD : DefOK I) (hgs : ∀ g ∈ gs, I ⊧ᴵ (KoreAML.Cons.funItem g.1 g.2).pat)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m0) :
    ∀ (p : Kore.Pattern) (s : String), builtGB gs fT p s = true → TieRuleCut.OneIn I e s (tr ⟨t, []⟩ p)
  | .var (.evar x), s, h => by
    rw [builtGB, Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 := (TieRuleLhs.guard_evarKey hD).mp (hg _ (List.contains_iff_mem.mp h.2))
    rw [h.1, trSort_srt] at h1
    refine ⟨_, (inS_iff e).mp h1, fun m => ?_⟩
    rw [TieRuleCut.tr_evarCut, interp_evar]
  | .app hd ss ps, s, h => by
    cases hf : gs.find? (fun g => g.1 == s && headGB g.2 hd ss s) with
    | none => simp [builtGB, hf] at h
    | some g =>
      simp only [builtGB, hf] at h
      have hmem := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      rw [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨xs, hall, hl, hxs⟩ := builtGArgsB_one hD hgs hg ps g.2.argSorts h
      obtain ⟨y, hy, hyu⟩ := fun_at hD (hgs g hmem) hl hxs
      refine ⟨y, hp.1 ▸ hy, fun m => ?_⟩
      rw [TieFRRead.tr_app, TieFRRead.trArgs_iff, ← hyu m, headGB_tr hp.2 t, hp.1]
      unfold GS
      constructor
      · rintro ⟨a, ha, bs, hbs, happ⟩
        rw [(TieRuleCut.all2_one hall bs).mp hbs] at happ
        exact ⟨a, ((genHead_closed _ _).interp e _ a).mp ha, happ⟩
      · rintro ⟨a, ha, happ⟩
        exact ⟨a, ((genHead_closed _ _).interp e _ a).mpr ha, xs, (TieRuleCut.all2_one hall xs).mpr rfl, happ⟩
  | .var (.svar _), _, h => by simp [builtGB] at h
  | .string _, _, h => by simp [builtGB] at h
theorem builtGArgsB_one (hD : DefOK I) (hgs : ∀ g ∈ gs, I ⊧ᴵ (KoreAML.Cons.funItem g.1 g.2).pat)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m0) :
    ∀ (ps : List Kore.Pattern) (ss : List String), builtGArgsB gs fT ps ss = true →
      ∃ xs : List M, All2 (fun p x => ∀ m, (tr ⟨t, []⟩ p).interpret I e m ↔ m = x) ps xs ∧
        xs.length = ss.length ∧ ∀ (i : Nat) x s, xs[i]? = some x → ss[i]? = some s → InS I s x
  | [], [], _ => ⟨[], .nil, rfl, fun i x s hx _ => by simp at hx⟩
  | p :: ps, s :: ss, h => by
    rw [builtGArgsB, Bool.and_eq_true] at h
    obtain ⟨y, hy, hyu⟩ := builtGB_one hD hgs hg p s h.1
    obtain ⟨xs, hall, hl, hxs⟩ := builtGArgsB_one hD hgs hg ps ss h.2
    refine ⟨y :: xs, .cons hyu hall, by simp [hl], fun i x s' hx hs => ?_⟩
    cases i with
    | zero => simp at hx hs; rw [← hx, ← hs]; exact hy
    | succ i => simp at hx hs; exact hxs i x s' hx hs
  | [], _ :: _, h => by simp [builtGArgsB] at h
  | _ :: _, [], h => by simp [builtGArgsB] at h
end

/-- **The right side of a rule is defined, from Cons-Fun.** In a model of definedness where each
generator of `gs` has its Cons-Fun item, at a valuation where the guards of `fT` hold, the right
side `\and{s}(r, \top{s}())` with `r` built of the variables of `fT` and the generators of `gs`
(`builtGB`) holds one element of the sort `s`, so `⌈r ∧ ⊤⌉` holds of every element of `s`. -/
theorem rightDefined_of_funsG (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (hgs : ∀ g ∈ gs, I ⊧ᴵ (KoreAML.Cons.funItem g.1 g.2).pat) {s : String} {r : Kore.Pattern}
    (hb : builtGB gs fT r s = true) {σ : M} (hS : ∀ a, I.evalSymb (.sort ("Sort" ++ s)) a ↔ a = σ)
    (hσ : IsSort I σ) (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m0) (a : M)
    (ha : (inhOf (trSort t (srt s))).interpret I e a) :
    (tr ⟨t, []⟩ (.ceil (srt s) (srt s) (.and (srt s) [r, .top (srt s)]))).interpret I e a := by
  obtain ⟨y, hy, hyu⟩ := builtGB_one hD hgs hg r s hb
  have hS' : ∀ (e' : Valuation M) b, (trSort t (srt s)).interpret I e' b ↔ b = σ := fun e' b => by
    rw [trSort_srt, interp_sym]; exact hS b
  have hyσ : Inh I σ y := (interp_inhOf_of (hS' e)).mp (by rw [trSort_srt]; exact (inS_iff e).mpr hy)
  have hT : ∀ φ, tr ⟨t, []⟩ (.ceil (srt s) (srt s) φ) =
      sCeil (trSort t (srt s)) (trSort t (srt s)) (tr ⟨t, []⟩ φ) := fun φ => by rw [tr]
  have htop : ∀ b, (tr ⟨t, []⟩ (.top (srt s))).interpret I e b ↔ Inh I σ b := fun b => by
    have h1 : tr ⟨t, []⟩ (.top (srt s)) = sTop (trSort t (srt s)) := by rw [tr]
    rw [h1, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of (hS' e)]
  rw [hT, interp_sCeil hD hc (hS' e) (hS' e) hσ hσ (fun b hb' =>
    (htop b).mp ((interp_and (List.cons_ne_nil _ _)).mp hb' _ (List.mem_cons_of_mem _ List.mem_cons_self)))]
  refine ⟨⟨y, (interp_and (List.cons_ne_nil _ _)).mpr fun p hp => ?_⟩, (interp_inhOf_of (hS' e)).mp ha⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact (hyu y).mpr rfl
  · rw [List.mem_singleton.mp hp]; exact (htop y).mpr hyσ

end

/-- Γ of `c` has the Cons-Fun item of each generator of `gs`, of the sort named beside it. -/
def funsInGB (c : Semantics) (gs : List (String × KoreAML.Gen)) : Bool :=
  gs.all fun g => (consItemsK c).any fun it => decide (it.pat = (KoreAML.Cons.funItem g.1 g.2).pat)

kernel_rfl funsInGB_withHooks : ∀ (c : Semantics) (H : HookParams) (gs : List (String × KoreAML.Gen)),
  funsInGB (c.withHooks H) gs = funsInGB c gs

/-- **The right side of a rule is defined, in a model of Γ.** For a right side
`\and{N}(r, \top{N}())` whose `r` is built of the variables of `fT` and of generators (constructors
and injections) whose Cons-Fun items Γ has (`funsInGB`, `builtGB`): where the guards of `fT` hold,
`⌈r ∧ ⊤⌉` holds of every element of the sort N. -/
theorem rightDefined_of_ΓG {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics} [OvlOK c]
    (hI : I ⊧ᴵP Γ c) {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {t : VarTable} {N : Srt}
    {r : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length) (hin : funsInGB c gs = true)
    (hb : builtGB gs fT r (c.sortName N) = true) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m) (a : M)
    (ha : (inhOf (trSort t (srtOf c N))).interpret I e a) :
    (tr ⟨t, []⟩ (.ceil (srtOf c N) (srtOf c N) (.and (srtOf c N) [r, .top (srtOf c N)]))).interpret I e a := by
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI hN
  refine rightDefined_of_funsG (defOK hI) (sat_sigItem hI sig_ceilDef) (fun g hg' => ?_) hb hσ1 hσ2 hg a ha
  obtain ⟨it, hit, hpat⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin g hg')
  rw [← of_decide_eq_true hpat]
  exact sat_cons hI (Or.inl ⟨it, hit, rfl⟩)

/-- **`⌈r ∧ ⊤⌉` of every element of `\top` of the rule's sort**, the form a rule's left side holds
it in: in a model of Γ, where the guards of `fT` hold, at an element of `\top{s}()`, `s` the name
of a sort of the definition. -/
theorem rightDefined_top {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics} [OvlOK c]
    (hI : I ⊧ᴵP Γ c) {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {t : VarTable} {N : Srt} {s : String}
    {r : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length) (hs : c.sortName N = s)
    (hin : funsInGB c gs = true) (hb : builtGB gs fT r s = true) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m) (a : M)
    (ha : (tr ⟨t, []⟩ (.top (srt s))).interpret I e a) :
    (tr ⟨t, []⟩ (.ceil (srt s) (srt s) (.and (srt s) [r, .top (srt s)]))).interpret I e a := by
  subst hs
  have h2 : tr ⟨t, []⟩ (.top (srt (c.sortName N))) = sTop (trSort t (srt (c.sortName N))) := by rw [tr]
  rw [h2, interp_sTop (defOK hI) (by rw [trSort_srt]; rfl)] at ha
  exact rightDefined_of_ΓG hI hN hin hb e m hg a ha

/-- Each generator of `gs` has its Cons-Fun item among Γ's constructor items. -/
theorem funsInGB_cons {c : Semantics} {gs : List (String × KoreAML.Gen)} (hin : funsInGB c gs = true)
    {g : String × KoreAML.Gen} (hg : g ∈ gs) : ΓCons c (KoreAML.Cons.funItem g.1 g.2).pat := by
  obtain ⟨it, hit, hpat⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin g hg)
  exact Or.inl ⟨it, hit, of_decide_eq_true hpat⟩

/-- **Every element of `inj{A, N}(p)` is in N**, in a model of definedness and of the injection's
Cons-Fun item, where every element of `p` is in A: the injection of an element of A is one element
of N. -/
theorem inj_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {A N : String}
    (hf : I ⊧ᴵ (KoreAML.Cons.funItem N (.inj A)).pat) {t : VarTable} {e : Valuation M} {p : Kore.Pattern}
    (hp : ∀ b, (tr ⟨t, []⟩ p).interpret I e b → (inhOf (trSort t (srt A))).interpret I e b) (a : M)
    (ha : (tr ⟨t, []⟩ (injP A N p)).interpret I e a) : (inhOf (trSort t (srt N))).interpret I e a := by
  rw [trSort_srt]
  refine (inS_iff (s := N) e).mpr ?_
  unfold injP at ha
  rw [TieFRRead.tr_app, TieFRRead.trArgs_iff] at ha
  obtain ⟨h, hh, bs, hbs, happ⟩ := ha
  obtain ⟨b, rfl, hb⟩ : ∃ b, bs = [b] ∧ (tr ⟨t, []⟩ p).interpret I e b := by
    cases hbs with
    | cons hb hr => cases hr; exact ⟨_, rfl, hb⟩
  rw [headGB_tr (g := .inj A) (h := ⟨⟨"inj"⟩⟩) (s := N) (by simp [headGB]) t] at hh
  have hbA : InS I A b := (inS_iff (s := A) e).mp (by have h1 := hp _ hb; rwa [trSort_srt] at h1)
  obtain ⟨y, hy, hyu⟩ := fun_at hD hf (xs := [b]) rfl (fun i x s hx hs => by
    cases i with
    | zero =>
      have hx' : b = x := by simpa using hx
      have hs' : A = s := by simpa [KoreAML.Gen.argSorts] using hs
      rw [← hx', ← hs']; exact hbA
    | succ i => simp at hx)
  have hgs : GS I N (.inj A) [b] a := ⟨h, ((genHead_closed _ _).interp e _ h).mp hh, happ⟩
  rw [(hyu a).mp hgs]; exact hy

/-- **Every element of a built pattern is in its sort**, in a model of Γ where the guards of `fT`
hold. -/
theorem built_inh {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics}
    (hI : I ⊧ᴵP Γ c) {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {t : VarTable} {s : String}
    {p : Kore.Pattern} (hin : funsInGB c gs = true) (hb : builtGB gs fT p s = true) (e : Valuation M) (m : M)
    (hg : ∀ k ∈ fT, (guardOf t k).interpret I e m) (a : M) (ha : (tr ⟨t, []⟩ p).interpret I e a) :
    (inhOf (trSort t (srt s))).interpret I e a := by
  obtain ⟨y, hy, hyu⟩ := builtGB_one (defOK hI) (fun g hg' => sat_cons hI (funsInGB_cons hin hg')) hg p s hb
  rw [trSort_srt, (hyu a).mp ha]
  exact (inS_iff (s := s) e).mpr hy

/-- **An element of `\equals{s, s'}(φ, ψ)` is one of `\top{s'}()`**, in a model of Γ, `s` and `s'`
names of sorts of the definition: a `requires` at the rule's sort keeps the elements of the left
side in that sort, as `\top` does. -/
theorem equals_top {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics} [OvlOK c]
    (hI : I ⊧ᴵP Γ c) {N N' : Srt} {s s' : String} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hN' : N' < nRegSorts + c.sortNames.length) (hs' : c.sortName N' = s')
    {t : VarTable} {e : Valuation M} {φ ψ : Kore.Pattern} {a : M}
    (h : (tr ⟨t, []⟩ (.equals (srt s) (srt s') φ ψ)).interpret I e a) :
    (tr ⟨t, []⟩ (.top (srt s'))).interpret I e a := by
  subst hs hs'
  have hD := defOK hI
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI hN
  obtain ⟨σ', hσ1', hσ2'⟩ := sortSing hI hN'
  have hS : ∀ b, (trSort t (srt (c.sortName N))).interpret I e b ↔ b = σ := fun b => by
    rw [trSort_srt, interp_sym]; exact hσ1 b
  have hS' : ∀ b, (trSort t (srt (c.sortName N'))).interpret I e b ↔ b = σ' := fun b => by
    rw [trSort_srt, interp_sym]; exact hσ1' b
  have h' : (sEquals (trSort t (srt (c.sortName N))) (trSort t (srt (c.sortName N')))
      (tr ⟨t, []⟩ φ) (tr ⟨t, []⟩ ψ)).interpret I e a := by
    rw [tr] at h; exact h
  have h2 : tr ⟨t, []⟩ (.top (srt (c.sortName N'))) = sTop (trSort t (srt (c.sortName N'))) := by rw [tr]
  rw [h2, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of hS']
  exact ((interp_sEquals hD (sat_sigItem hI sig_ceilDef) hS hS' hσ2 hσ2' a).mp h').1

end TieRuleCutG

end KCore
