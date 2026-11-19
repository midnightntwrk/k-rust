/-
  The constructor sentences of a function-overloaded symbol against Γ's items at uncovered
  arguments (KcoreSpec/TieOvlFn.lean), kernel-checked on two texts. Run from the package root:
  `lake env lean -j1 test/TieOvlFn.lean`.

  - `Lhs`: `f2-examples/e5-ovl-fun-lhs.kompile.kore`. `capGas : Gas → Gas` overloads the function
    `capN : N → N`, N < Gas; Gas has the constructor `inf` beside it. The text states `capGas`'s
    `functional` sentence (axiom 81), its same-constructor sentence (82), the different-constructors
    sentence of `capGas` and `inf` (83), `inf`'s `functional` sentence (89) and the overload axiom
    (139, with the injection on its right side).
  - `Keep`: `f2-examples/e5-ovl-fun-keep-run.kompile.kore`. The same symbols with `capN : N → Gas`:
    the overload axiom (110) has no injection on its right side.

  On each: the three predicates accept their sentence and no other sentence of the user module
  (`*_checked`, `*_only`); `tieOvlEqB` accepts the overload axiom (`ovleq_checked`); and the
  weaker lemmas at the literal generators, for every interpretation and every interpretation of
  the hooks' parameters (`fun_weaker`, `inj_weaker`, `dist_weaker`, the last from `capGas`'s
  `functional` sentence and from `inf`'s).

  On `Lhs`, the hypotheses of the weaker lemmas:
  - in every model of Γ, at every interpretation of the hooks' parameters, `TieOvlFnBase` and the
    arities of `capGas` and `inf` hold (`base_arity_Γ`, from Γ's signature items: G-sort, G-ceil-def,
    G-arity, and the value `.K` of K), so the three sentences alone give Γ's three items
    (`weaker_Γ`);
  - non-vacuity: a term model of Gas (`TermModel`: `inf` is `gas 0`, `capGas(gas n)` is
    `gas (n + 1)`) meets `TieOvlFnBase`, both arities and the sentences 81, 82, 83 and 89
    (`TermModel.nonvacuous`), the sentences from Cons-Fun, Cons-Inj and Cons-Dist of the two
    generators there; the weaker lemmas fire on it (`TermModel.nonvacuous_weaker`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieOvlFnTest

open KCore ML Faithful KoreAML

/-- Gas. -/
def gasS : Srt := 32
/-- `capGas : Gas → Gas`, the overloading symbol. -/
def capGas : Gen := .ctor ⟨392, [32], 32⟩
/-- `inf : Gas`. -/
def inf : Gen := .ctor ⟨388, [], 32⟩

namespace Lhs

definition_of defn from "f2-examples/e5-ovl-fun-lhs.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-lhs.kompile.kore" module "E5-OVL-FUN-LHS"

noncomputable abbrev c : Semantics := defn.sem

theorem names : c.sortName gasS = "Gas" ∧ c.fnOvl capGas = true ∧ c.fnOvl inf = false ∧
    (Gen.toK c capGas, Gen.toK c inf) =
      (.ctor ⟨"LblcapGas", ["Gas"], "Gas"⟩, .ctor ⟨"Lblinf", [], "Gas"⟩) := by decide +kernel

theorem fun_checked : tieOvlFnFunAtB c gasS capGas U.ax81.ax = true := by decide +kernel
theorem inj_checked : tieOvlFnInjAtB c gasS capGas U.ax82.ax = true := by decide +kernel
theorem dist_checked : tieOvlFnDistAtB c gasS capGas inf U.ax83.ax = true := by decide +kernel
theorem capGas_fun_checked : tieOvlFnFunShapeB c gasS (Gen.toK c capGas) U.ax81.ax = true := by decide +kernel
theorem inf_fun_checked : tieOvlFnFunShapeB c gasS (Gen.toK c inf) U.ax89.ax = true := by decide +kernel

theorem fun_only : (U.all.filter fun ad => tieOvlFnFunB c ad.ax).map (·.index) = [81] := by decide +kernel
theorem inj_only : (U.all.filter fun ad => tieOvlFnInjB c ad.ax).map (·.index) = [82] := by decide +kernel
theorem dist_only : (U.all.filter fun ad => tieOvlFnDistB c ad.ax).map (·.index) = [83] := by decide +kernel

/-- None of the three is a sentence Γ's constructor items entail in the form `tieConsB` reads. -/
theorem not_cons : [U.ax81, U.ax82, U.ax83].all (fun ad => !tieConsB c ad.ax) = true := by decide +kernel

/-- The overload axiom, with the injection on its right side. -/
theorem ovleq_checked : tieOvlEqB c U.ax139.ax = true := by decide +kernel

section
variable {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M)

/-- `capGas`'s `functional` sentence gives Cons-Fun at uncovered arguments. -/
theorem fun_weaker (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c capGas))
    (hs : I ⊧ᴵ (trAxiom [] [] U.ax81).pat) (covs : List (List String)) :
    I ⊧ᴵ (Cons.funUncItem (c.sortName gasS) (Gen.toK c capGas) covs).pat :=
  tieOvlFnFun_weaker fun_checked hB hA hs covs

/-- `capGas`'s same-constructor sentence, with its `functional` sentence, gives Cons-Inj at
uncovered arguments. -/
theorem inj_weaker (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c capGas))
    (hsf : I ⊧ᴵ (trAxiom [] [] U.ax81).pat) (hs : I ⊧ᴵ (trAxiom [] [] U.ax82).pat) (covs : List (List String)) :
    I ⊧ᴵ (Cons.injUncItem (c.sortName gasS) (Gen.toK c capGas) covs).pat :=
  tieOvlFnInj_weaker fun_checked inj_checked hB hA hsf hs covs

/-- The different-constructors sentence of `capGas` and `inf`, with `capGas`'s `functional`
sentence, gives Cons-Dist at uncovered arguments. -/
theorem dist_weaker (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c capGas))
    (hsf : I ⊧ᴵ (trAxiom [] [] U.ax81).pat) (hs : I ⊧ᴵ (trAxiom [] [] U.ax83).pat)
    (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c capGas) (Gen.toK c inf) ug ug').pat) ∧
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c inf) (Gen.toK c capGas) ug' ug).pat) :=
  tieOvlFnDist_weaker (.inl rfl) capGas_fun_checked dist_checked hB hA hsf hs ug ug'

/-- The same from `inf`'s `functional` sentence in place of `capGas`'s. -/
theorem dist_weaker_inf (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c inf))
    (hsf : I ⊧ᴵ (trAxiom [] [] U.ax89).pat) (hs : I ⊧ᴵ (trAxiom [] [] U.ax83).pat)
    (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c capGas) (Gen.toK c inf) ug ug').pat) ∧
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c inf) (Gen.toK c capGas) ug' ug).pat) :=
  tieOvlFnDist_weaker (.inr rfl) inf_fun_checked dist_checked hB hA hsf hs ug ug'

end

/-- Γ holds the three items at every interpretation of the hooks' parameters. -/
theorem items (H : HookParams) :
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.funUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) capGas) ((ovlArgsOf (c.withHooks H) capGas).getD [])).pat) ∧
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.injUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) capGas) ((ovlArgsOf (c.withHooks H) capGas).getD [])).pat) ∧
    ((∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.distUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) capGas) (Gen.toK (c.withHooks H) inf) (ovlArgsOf (c.withHooks H) capGas)
      (ovlArgsOf (c.withHooks H) inf)).pat) ∨
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.distUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) inf) (Gen.toK (c.withHooks H) capGas) (ovlArgsOf (c.withHooks H) inf)
      (ovlArgsOf (c.withHooks H) capGas)).pat)) :=
  ⟨tieOvlFnFun_item_withHooks fun_checked H, tieOvlFnInj_item_withHooks inj_checked H,
    tieOvlFnDist_item_withHooks dist_checked H⟩

/-- The overloads the items name: `capGas` is covered at the lifts of N. -/
theorem covs : ovlArgsOf c capGas = some [["N"]] ∧ ovlArgsOf c inf = none := by decide +kernel

/-! ### In a model of Γ the hypotheses hold -/

/-- `capGas` and `inf` are symbols of `kernelSyms` of result Gas, at their names. -/
theorem arity_checked : tieOvlFnArityB c gasS capGas = true ∧ tieOvlFnArityB c gasS inf = true := by
  decide +kernel

theorem gas_numbered : gasS < nRegSorts + c.sortNames.length := by decide +kernel

/-- `TieOvlFnBase` and the arities in every model of Γ, at every interpretation of the hooks'
parameters. -/
theorem base_arity_Γ {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (H : HookParams)
    (hI : I ⊧ᴵP Γ (c.withHooks H)) :
    TieOvlFnBase I ((c.withHooks H).sortName gasS) ∧
    TieOvlFnArity I ((c.withHooks H).sortName gasS) (Gen.toK (c.withHooks H) capGas) ∧
    TieOvlFnArity I ((c.withHooks H).sortName gasS) (Gen.toK (c.withHooks H) inf) :=
  ⟨tieOvlFnBase_of_Γ_dotk hI gas_numbered,
    tieOvlFnArity_of_ΓB hI ((tieOvlFnArityB_withHooks c H _ _).trans arity_checked.1),
    tieOvlFnArity_of_ΓB hI ((tieOvlFnArityB_withHooks c H _ _).trans arity_checked.2)⟩

/-- In a model of Γ, at every interpretation of the hooks' parameters, the three sentences give
Γ's three items at uncovered arguments, with no other hypothesis. -/
theorem weaker_Γ {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (H : HookParams)
    (hI : I ⊧ᴵP Γ (c.withHooks H))
    (h81 : I ⊧ᴵ (trAxiom [] [] U.ax81).pat) (h82 : I ⊧ᴵ (trAxiom [] [] U.ax82).pat)
    (h83 : I ⊧ᴵ (trAxiom [] [] U.ax83).pat) (covs : List (List String)) (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (Cons.funUncItem ((c.withHooks H).sortName gasS) (Gen.toK (c.withHooks H) capGas) covs).pat) ∧
    (I ⊧ᴵ (Cons.injUncItem ((c.withHooks H).sortName gasS) (Gen.toK (c.withHooks H) capGas) covs).pat) ∧
    (I ⊧ᴵ (Cons.distUncItem ((c.withHooks H).sortName gasS) (Gen.toK (c.withHooks H) capGas)
      (Gen.toK (c.withHooks H) inf) ug ug').pat) := by
  have hf := (tieOvlFnFunAtB_withHooks c H _ _ _).trans fun_checked
  have hA := (tieOvlFnArityB_withHooks c H _ _).trans arity_checked.1
  refine ⟨tieOvlFnFun_weaker_Γ hI hf gas_numbered hA h81 covs,
    tieOvlFnInj_weaker_Γ hI hf ((tieOvlFnInjAtB_withHooks c H _ _ _).trans inj_checked) gas_numbered hA h81 h82 covs,
    (tieOvlFnDist_weaker_Γ hI (gf := capGas) (.inl rfl) (by
        simp only [tieOvlFnFunAtB, Bool.and_eq_true] at hf; exact hf.1.2)
      ((tieOvlFnDistAtB_withHooks c H _ _ _ _).trans dist_checked) gas_numbered hA h81 h83 ug ug').1⟩

/-! ### Non-vacuity: a term model of Gas -/

theorem inj_shape : tieOvlFnInjShapeB c gasS (Gen.toK c capGas) U.ax82.ax = true := by decide +kernel
theorem dist_shape : tieOvlFnDistShapeB c gasS (Gen.toK c capGas) (Gen.toK c inf) U.ax83.ax = true := by
  decide +kernel

namespace TermModel

/-- The carrier: the elements `gas n` of Gas (`inf` is `gas 0` and `capGas(gas n)` is
`gas (n + 1)`: the terms `inf` and `capGas` build), the sort Gas, the element of the sort of
sorts, the heads `⌈_⌉`, `⊤_` and `capGas`, and the partial applications of ceiling. -/
inductive E where
  | gas (n : Nat)
  | srt
  | sorts
  | dfd
  | inh
  | cap
  | ceil0
  | ceil1
  | ceil2

instance : Inhabited E := ⟨.gas 0⟩

/-- The symbols: Gas is the one sort, `Lblinf` denotes `gas 0`. -/
def symb : KoreAML.Sym → Set E
  | .defined => fun m => m = .dfd
  | .inh => fun m => m = .inh
  | .sortSort => fun m => m = .sorts
  | .sort n => fun m => n = "SortGas" ∧ m = .srt
  | .symbol n => fun m => (n = "LblcapGas" ∧ m = .cap) ∨ (n = "Lblinf" ∧ m = .gas 0)
  | .ceil => fun m => m = .ceil0
  | _ => fun _ => False

/-- Application: `⌈_⌉` holds everything; `⊤_` of Gas is the `gas n`, of the sort of sorts Gas;
`capGas` adds one; `⌈_⌉{Gas,Gas}` of anything is Gas. -/
def app : E → E → Set E
  | .dfd, _ => fun _ => True
  | .inh, .srt => fun m => ∃ n, m = .gas n
  | .inh, .sorts => fun m => m = .srt
  | .cap, .gas n => fun m => m = .gas (n + 1)
  | .ceil0, .srt => fun m => m = .ceil1
  | .ceil1, .srt => fun m => m = .ceil2
  | .ceil2, _ => fun m => ∃ n, m = .gas n
  | _, _ => fun _ => False

def I : Interpretation KoreAML.Sym E := ⟨symb, app⟩

theorem inh_iff {σ m : E} : Inh I σ m ↔ (σ = .srt ∧ ∃ n, m = .gas n) ∨ (σ = .sorts ∧ m = .srt) := by
  constructor
  · rintro ⟨i, hi, h⟩
    change i = .inh at hi
    subst hi
    change app .inh σ m at h
    cases σ with
    | srt => exact .inl ⟨rfl, h⟩
    | sorts => exact .inr ⟨rfl, h⟩
    | gas _ => exact (h : False).elim
    | dfd => exact (h : False).elim
    | inh => exact (h : False).elim
    | cap => exact (h : False).elim
    | ceil0 => exact (h : False).elim
    | ceil1 => exact (h : False).elim
    | ceil2 => exact (h : False).elim
  · rintro (⟨rfl, h⟩ | ⟨rfl, rfl⟩)
    · exact ⟨.inh, rfl, h⟩
    · exact ⟨.inh, rfl, rfl⟩

theorem isSort_iff {σ : E} : IsSort I σ ↔ σ = .srt := by
  constructor
  · rintro ⟨s0, hs0, h⟩
    change s0 = .sorts at hs0
    subst hs0
    rcases inh_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
    · cases h1
    · exact h2
  · rintro rfl
    exact ⟨.sorts, rfl, inh_iff.mpr (.inr ⟨rfl, rfl⟩)⟩

theorem defOK : DefOK I := fun _ _ => ⟨.dfd, rfl, trivial⟩

theorem sortGas (b : E) : I.evalSymb (.sort ("Sort" ++ "Gas")) b ↔ b = .srt :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem inS_gas {m : E} : InS I "Gas" m ↔ ∃ n, m = .gas n := by
  unfold InS
  rw [interp_inhOf_of (S := Cons.sortP "Gas") (σ := .srt) sortGas, inh_iff]
  simp

theorem ceil : I ⊧ᴵ ceilDefItem.pat := by
  intro e m
  unfold ceilDefItem
  dsimp only
  refine tieOvlFn_guarded_intro fun hg => ?_
  have h1 := hg _ (List.mem_cons_self ..)
  have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold sortGuard at h1 h2
  rw [interp_member defOK, interp_sortsDomain, isSort_iff] at h1 h2
  rw [interp_equal defOK]
  intro a
  rw [interp_sCeil_raw, interp_inhOf]
  constructor
  · rintro ⟨σ, σ', x, hσ, hσ', -, b, ⟨b', ⟨h, hh, hb'⟩, hb⟩, ha⟩
    rw [interp_evar] at hσ hσ'
    change h = .ceil0 at hh
    subst hh
    rw [hσ, h1] at hb'
    change b' = .ceil1 at hb'
    subst hb'
    rw [hσ', h2] at hb
    change b = .ceil2 at hb
    subst hb
    exact ⟨.srt, by rw [interp_evar, h2], inh_iff.mpr (.inl ⟨rfl, ha⟩)⟩
  · rintro ⟨σ', hσ', ha⟩
    rw [interp_evar, h2] at hσ'
    subst hσ'
    rcases inh_iff.mp ha with ⟨-, ha⟩ | ⟨h3, -⟩
    · exact ⟨.srt, .srt, e.evalEvar ⟨3⟩, by rw [interp_evar, h1], by rw [interp_evar, h2], rfl,
        .ceil2, ⟨.ceil1, ⟨.ceil0, rfl, rfl⟩, rfl⟩, ha⟩
    · cases h3

/-- `capGas` as the KORE generator. -/
abbrev capK : KoreAML.Gen := .ctor ⟨"LblcapGas", ["Gas"], "Gas"⟩
/-- `inf` as the KORE generator. -/
abbrev infK : KoreAML.Gen := .ctor ⟨"Lblinf", [], "Gas"⟩

theorem gs_cap {x m : E} : GS I "Gas" capK [x] m ↔ app .cap x m := by
  constructor
  · rintro ⟨a, ha, a', hx, rfl⟩
    rcases ha with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hx
    · exact absurd h (by decide)
  · intro h
    exact ⟨.cap, .inl ⟨rfl, rfl⟩, m, h, rfl⟩

theorem gs_inf {m : E} : GS I "Gas" infK [] m ↔ m = .gas 0 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨h, -⟩ | ⟨-, rfl⟩
    · exact absurd h (by decide)
    · rfl
  · rintro rfl
    exact ⟨.gas 0, .inr ⟨rfl, rfl⟩, rfl⟩

theorem one {xs : List E} (hl : xs.length = 1)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → ["Gas"][i]? = some s → InS I s x) : ∃ n, xs = [.gas n] := by
  rcases xs with _ | ⟨x, _ | ⟨_, _⟩⟩
  · simp at hl
  · obtain ⟨n, rfl⟩ := inS_gas.mp (hxs 0 x "Gas" rfl rfl)
    exact ⟨n, rfl⟩
  · simp at hl

theorem base : TieOvlFnBase I "Gas" :=
  ⟨defOK, ceil, ⟨.srt, sortGas, isSort_iff.mpr rfl⟩, ⟨.srt, .gas 0, isSort_iff.mpr rfl, inh_iff.mpr (.inl ⟨rfl, 0, rfl⟩)⟩⟩

theorem arity_cap : TieOvlFnArity I "Gas" capK := by
  intro xs hl hxs m hm
  obtain ⟨n, rfl⟩ := one hl hxs
  exact inS_gas.mpr ⟨n + 1, gs_cap.mp hm⟩

theorem arity_inf : TieOvlFnArity I "Gas" infK := fun xs hl _ m hm => by
  cases xs with
  | nil => exact inS_gas.mpr ⟨0, gs_inf.mp hm⟩
  | cons _ _ => exact absurd (hl.trans (rfl : infK.argSorts.length = 0)) (Nat.succ_ne_zero _)

theorem fun_cap : I ⊧ᴵ (Cons.funItem "Gas" capK).pat :=
  tieOvlFn_funItem_intro defOK fun xs hl hxs => by
    obtain ⟨n, rfl⟩ := one hl hxs
    exact ⟨.gas (n + 1), inS_gas.mpr ⟨n + 1, rfl⟩, fun m => gs_cap⟩

theorem fun_inf : I ⊧ᴵ (Cons.funItem "Gas" infK).pat :=
  tieOvlFn_funItem_intro defOK fun xs hl _ => by
    cases xs with
    | nil => exact ⟨.gas 0, inS_gas.mpr ⟨0, rfl⟩, fun m => gs_inf⟩
    | cons _ _ => exact absurd (hl.trans (rfl : infK.argSorts.length = 0)) (Nat.succ_ne_zero _)

theorem inj_cap : I ⊧ᴵ (Cons.injItem "Gas" capK).pat :=
  tieOvlFn_injItem_intro defOK fun xs ys hl hl' hxs hys heq => by
    obtain ⟨n, rfl⟩ := one hl hxs
    obtain ⟨k, rfl⟩ := one hl' hys
    have h := (heq (.gas (n + 1))).mp (gs_cap.mpr rfl)
    have h' : E.gas (n + 1) = .gas (k + 1) := gs_cap.mp h
    cases h'
    rfl

theorem dist_cap_inf : I ⊧ᴵ (Cons.distItem "Gas" capK infK).pat :=
  tieOvlFn_distItem_intro defOK fun xs ys hl hl' hxs _ heq => by
    obtain ⟨n, rfl⟩ := one hl hxs
    cases ys with
    | nil => exact nomatch gs_inf.mp ((heq (.gas (n + 1))).mp (gs_cap.mpr rfl))
    | cons _ _ => exact absurd (hl'.trans (rfl : infK.argSorts.length = 0)) (Nat.succ_ne_zero _)

theorem toK : c.sortName gasS = "Gas" ∧ Gen.toK c capGas = capK ∧ Gen.toK c inf = infK := by decide +kernel

/-- **The term model meets `TieOvlFnBase`, both arities and the four sentences of the text**
(`capGas`'s `functional`, same-constructor and different-constructors sentences, and `inf`'s
`functional` sentence): the hypotheses of the weaker lemmas are met together. -/
theorem nonvacuous :
    TieOvlFnBase I (c.sortName gasS) ∧ TieOvlFnArity I (c.sortName gasS) (Gen.toK c capGas) ∧
    TieOvlFnArity I (c.sortName gasS) (Gen.toK c inf) ∧
    (I ⊧ᴵ (trAxiom [] [] U.ax81).pat) ∧ (I ⊧ᴵ (trAxiom [] [] U.ax82).pat) ∧
    (I ⊧ᴵ (trAxiom [] [] U.ax83).pat) ∧ (I ⊧ᴵ (trAxiom [] [] U.ax89).pat) := by
  obtain ⟨h1, h2, h3⟩ := toK
  have hB : TieOvlFnBase I (c.sortName gasS) := by rw [h1]; exact base
  have fc : I ⊧ᴵ (Cons.funItem (c.sortName gasS) (Gen.toK c capGas)).pat := by rw [h1, h2]; exact fun_cap
  have fi : I ⊧ᴵ (Cons.funItem (c.sortName gasS) (Gen.toK c inf)).pat := by rw [h1, h3]; exact fun_inf
  have ic : I ⊧ᴵ (Cons.injItem (c.sortName gasS) (Gen.toK c capGas)).pat := by rw [h1, h2]; exact inj_cap
  have dc : I ⊧ᴵ (Cons.distItem (c.sortName gasS) (Gen.toK c capGas) (Gen.toK c inf)).pat := by
    rw [h1, h2, h3]; exact dist_cap_inf
  refine ⟨hB, by rw [h1, h2]; exact arity_cap, by rw [h1, h3]; exact arity_inf,
    tieOvlFnFun_sent_of capGas_fun_checked hB fc, tieOvlFnInj_sent_of inj_shape defOK fc ic,
    tieOvlFnDist_sent_of dist_shape defOK fc fi (.inl dc), tieOvlFnFun_sent_of inf_fun_checked hB fi⟩

/-- The weaker lemmas fire on the term model, from the sentences alone. -/
theorem nonvacuous_weaker (covs : List (List String)) (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (Cons.funUncItem (c.sortName gasS) (Gen.toK c capGas) covs).pat) ∧
    (I ⊧ᴵ (Cons.injUncItem (c.sortName gasS) (Gen.toK c capGas) covs).pat) ∧
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c capGas) (Gen.toK c inf) ug ug').pat) :=
  let ⟨hB, hA, _, h81, h82, h83, _⟩ := nonvacuous
  ⟨fun_weaker I hB hA h81 covs, inj_weaker I hB hA h81 h82 covs, (dist_weaker I hB hA h81 h83 ug ug').1⟩

end TermModel

end Lhs

namespace Keep

definition_of defn from "f2-examples/e5-ovl-fun-keep-run.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-keep-run.kompile.kore" module "E5-OVL-FUN-KEEP-RUN"

noncomputable abbrev c : Semantics := defn.sem

theorem names : c.sortName gasS = "Gas" ∧ c.fnOvl capGas = true ∧ c.fnOvl inf = false ∧
    (Gen.toK c capGas, Gen.toK c inf) =
      (.ctor ⟨"LblcapGas", ["Gas"], "Gas"⟩, .ctor ⟨"Lblinf", [], "Gas"⟩) := by decide +kernel

theorem fun_checked : tieOvlFnFunAtB c gasS capGas U.ax58.ax = true := by decide +kernel
theorem inj_checked : tieOvlFnInjAtB c gasS capGas U.ax59.ax = true := by decide +kernel
theorem dist_checked : tieOvlFnDistAtB c gasS capGas inf U.ax60.ax = true := by decide +kernel

theorem fun_only : (U.all.filter fun ad => tieOvlFnFunB c ad.ax).map (·.index) = [58] := by decide +kernel
theorem inj_only : (U.all.filter fun ad => tieOvlFnInjB c ad.ax).map (·.index) = [59] := by decide +kernel
theorem dist_only : (U.all.filter fun ad => tieOvlFnDistB c ad.ax).map (·.index) = [60] := by decide +kernel

/-- The overload axiom in the result-keeping form: no injection on its right side. -/
theorem ovleq_checked : tieOvlEqB c U.ax110.ax = true := by decide +kernel

/-- The predicates at every interpretation of the hooks' parameters. -/
theorem checked_withHooks (H : HookParams) : tieOvlFnFunB (c.withHooks H) U.ax58.ax = true ∧
    tieOvlFnInjB (c.withHooks H) U.ax59.ax = true ∧ tieOvlFnDistB (c.withHooks H) U.ax60.ax = true :=
  ⟨(tieOvlFnFunB_withHooks c H _).trans (by decide +kernel), (tieOvlFnInjB_withHooks c H _).trans (by decide +kernel),
    (tieOvlFnDistB_withHooks c H _).trans (by decide +kernel)⟩

end Keep

end KCore.TieOvlFnTest

#print axioms KCore.Faithful.tieOvlFnFun_at
#print axioms KCore.Faithful.tieOvlFnInj_at
#print axioms KCore.Faithful.tieOvlFnDist_at
#print axioms KCore.Faithful.tieOvlFnFun_weaker
#print axioms KCore.Faithful.tieOvlFnInj_weaker
#print axioms KCore.Faithful.tieOvlFnDist_weaker
#print axioms KCore.Faithful.tieOvlFnBase_of_Γ
#print axioms KCore.Faithful.tieOvlFnFunB_withHooks
#print axioms KCore.Faithful.tieOvlFnInjB_withHooks
#print axioms KCore.Faithful.tieOvlFnDistB_withHooks
#print axioms KCore.Faithful.tieOvlFnFun_item_withHooks
#print axioms KCore.Faithful.tieOvlFnInj_item_withHooks
#print axioms KCore.Faithful.tieOvlFnDist_item_withHooks
#print axioms KCore.TieOvlFnTest.Lhs.fun_checked
#print axioms KCore.TieOvlFnTest.Lhs.fun_only
#print axioms KCore.TieOvlFnTest.Lhs.inj_only
#print axioms KCore.TieOvlFnTest.Lhs.dist_only
#print axioms KCore.TieOvlFnTest.Lhs.not_cons
#print axioms KCore.TieOvlFnTest.Lhs.ovleq_checked
#print axioms KCore.TieOvlFnTest.Lhs.fun_weaker
#print axioms KCore.TieOvlFnTest.Lhs.inj_weaker
#print axioms KCore.TieOvlFnTest.Lhs.dist_weaker
#print axioms KCore.TieOvlFnTest.Lhs.dist_weaker_inf
#print axioms KCore.TieOvlFnTest.Lhs.items
#print axioms KCore.TieOvlFnTest.Lhs.covs
#print axioms KCore.TieOvlFnTest.Keep.fun_only
#print axioms KCore.TieOvlFnTest.Keep.inj_only
#print axioms KCore.TieOvlFnTest.Keep.dist_only
#print axioms KCore.TieOvlFnTest.Keep.ovleq_checked
#print axioms KCore.TieOvlFnTest.Keep.checked_withHooks
#print axioms KCore.Faithful.tieOvlFnArity_of_Γ
#print axioms KCore.Faithful.tieOvlFnArity_of_ΓB
#print axioms KCore.Faithful.tieOvlFnArityB_withHooks
#print axioms KCore.Faithful.tieOvlFn_dotk_sortOf
#print axioms KCore.Faithful.tieOvlFnInh_of_Γ
#print axioms KCore.Faithful.tieOvlFnBase_of_Γ_dotk
#print axioms KCore.Faithful.tieOvlFnFun_weaker_Γ
#print axioms KCore.Faithful.tieOvlFnInj_weaker_Γ
#print axioms KCore.Faithful.tieOvlFnDist_weaker_Γ
#print axioms KCore.Faithful.tieOvlFnFun_sent_of_funItem
#print axioms KCore.Faithful.tieOvlFnFun_sent_of
#print axioms KCore.Faithful.tieOvlFnFun_sent_iff
#print axioms KCore.Faithful.tieOvlFnInj_sent_of
#print axioms KCore.Faithful.tieOvlFnDist_sent_of
#print axioms KCore.TieOvlFnTest.Lhs.arity_checked
#print axioms KCore.TieOvlFnTest.Lhs.base_arity_Γ
#print axioms KCore.TieOvlFnTest.Lhs.weaker_Γ
#print axioms KCore.TieOvlFnTest.Lhs.TermModel.ceil
#print axioms KCore.TieOvlFnTest.Lhs.TermModel.nonvacuous
#print axioms KCore.TieOvlFnTest.Lhs.TermModel.nonvacuous_weaker
