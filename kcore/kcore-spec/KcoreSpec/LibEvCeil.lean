/-
  KCore, checked layer: the library's definedness lemmas over set variables are refuted at values,
  and hold at sets of at most one value.

  A set variable ranges over every set of values of its sort (`SetVarsAtValues`); an application
  at sets denotes the values of the symbol at each choice of one value per argument (`LibEv.svDen`).
  The lemmas below state a definedness condition of a symbol in terms of a test of one argument.
  At a set of two values that argument's test denotes both `true` and `false` where the
  application is defined at one of them, so the right side does not hold where the left side does:
  Γ refutes each lemma at a valuation at values (`SvEqn.refuted_at`). At sets of at most one value
  the condition is exactly the symbol's definedness: the companion holds (`SvEqn.entailed_one`).

  - `ceilIntEqn f g` (domains.md 1392 to 1396, K 7.1.337):
    `#Ceil(f(@I1, @I2)) => {g(@I2, 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)`, for `/Int`,
    `%Int`, `modInt` with `=/=Int`, `>>Int`, `<<Int` with `>=Int`. `ceilInt_refuted_at`: at
    `@I1 = {p}`, `@I2 = {q, z}` where `f(p, q)` has a value and `g(z, 0)` is `false`;
    `ceilInt_one`: where `f(x, y)` has a value exactly where `g(y, 0)` is `true`.
  - `ceilMapEqn`, the lemma kompile generates for `_Map_`:
    `#Ceil(@K0 |-> @K1 @Rest) => {@K0 in_keys(@Rest) #Equals false} #And #Ceil(@K1)`.
    `ceilMap_refuted_at`: at `@Rest` a map without the key `k` and one with it; `ceilMap_one`.
-/
import KcoreSpec.LibEvSetVar
import KcoreSpec.LibEvInt
import KcoreSpec.LibEvFnLib

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-! ## `#Ceil(f(@I1, @I2)) => {g(@I2, 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)` -/

/-- The definedness lemma of the Int symbol `f` by the test `g` of its second argument against 0. -/
def ceilIntEqn (f g : Sym) : SvEqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int)],
    .ceil Srt.int (.app f [.var 0, .var 1]),
    .and (.and (.eq Srt.bool (.app g [.var 1, intT 0]) (.dv Srt.bool (.bool true))) (.ceil Srt.int (.var 0)))
      (.ceil Srt.int (.var 1)), []⟩

theorem ceilInt_apart {c : Semantics} (h : c.coreOK = true) (f g : Sym) :
    (ceilIntEqn f g).lhs.Apart c ∧ (ceilIntEqn f g).rhs.Apart c := by
  haveI : OvlOK c := ovlOK_of_core h
  exact ⟨trivial, ⟨⟨apart_of_distinct bool_distinct, trivial⟩, trivial⟩⟩

/-- **The lemma is refuted at values**: where `f(p, q)` has a value and `g(z, 0)` is `false`, in
every model of `Γ c` it fails at `@I1 = {p}`, `@I2 = {q, z}`: the left side holds and `g(@I2, 0)`
denotes `false`, which is not `true`. -/
theorem ceilInt_refuted_at {c : Semantics} (h : c.coreOK = true) (f g : Sym) (hr : (ceilIntEqn f g).regular = true)
    (ht : (ceilIntEqn f g).typed c = true) (p q z : Int) (hf : ∃ r, c.hv f [int p, int q] = some r)
    (hg : c.hv g [int z, int 0] = some (bool false)) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (ceilIntEqn f g).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  refine SvEqn.refuted_at h _ hr ht (ceilInt_apart h f g)
    (fun i v => (i = 0 ∧ v = int p) ∨ (i = 1 ∧ (v = int q ∨ v = int z))) ?_ (fun _ h => nomatch h) ?_ ad hp hsv hI
  · intro i x hx v hv
    have hx' : x.2 = Srt.int := by
      match i, hx with
      | 0, hx => cases hx; rfl
      | 1, hx => cases hx; rfl
    rw [hx']
    rcases hv with ⟨-, rfl⟩ | ⟨-, rfl | rfl⟩ <;> rfl
  · obtain ⟨r, hr⟩ := hf
    intro hiff
    have hL : (ceilIntEqn f g).lhs.Holds c
        (fun i v => (i = 0 ∧ v = int p) ∨ (i = 1 ∧ (v = int q ∨ v = int z))) :=
      ⟨r, [int p, int q], ⟨int p, [int q], rfl, Or.inl ⟨rfl, rfl⟩, int q, [], rfl, Or.inr ⟨rfl, Or.inl rfl⟩, rfl⟩, hr⟩
    obtain ⟨⟨heq, -⟩, -⟩ := hiff.mp hL
    have := (heq (bool false)).mp ⟨[int z, int 0], ⟨int z, [int 0], rfl, Or.inr ⟨rfl, Or.inr rfl⟩, int 0, [], rfl,
      rfl, rfl⟩, hg⟩
    exact absurd this (by simp [svVals, bool])

/-- **The companion**: where `f(x, y)` has a value exactly where `g(y, 0)` is `true`, the lemma holds at every valuation at values whose set variables hold at
most one element. -/
theorem ceilInt_one {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (f g : Sym)
    (hr : (ceilIntEqn f g).regular = true) (ht : (ceilIntEqn f g).typed c = true)
    (hfg : ∀ x y, (∃ r, c.hv f [int x, int y] = some r) ↔ c.hv g [int y, int 0] = some (bool true))
    (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (ceilIntEqn f g).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    SvAtMostOne c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI : OvlOK c := ovlOK_of_core h
  have hint : apartSort c Srt.int = true := apart_of_distinct int_distinct
  refine SvEqn.entailed_one h _ hr ht (ceilInt_apart h f g)
    (fun x hx => by
      simp only [ceilIntEqn, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact hint) ?_ ad hp hsv
  intro ρ hρ hone
  have hI0 : ∀ v, ρ 0 v → ∃ x, v = int x := fun v hv => shape_int hs (hρ 0 _ rfl v hv)
  have hI1 : ∀ v, ρ 1 v → ∃ x, v = int x := fun v hv => shape_int hs (hρ 1 _ rfl v hv)
  simp only [ceilIntEqn, SvPred.Holds, svVals, svValsList, intT]
  constructor
  · rintro ⟨r, _, ⟨x, _, rfl, hx, _, _, rfl, hy, rfl⟩, hfr⟩
    rename_i y
    obtain ⟨x', rfl⟩ := hI0 x hx
    obtain ⟨y', rfl⟩ := hI1 y hy
    have hgy := (hfg x' y').mp ⟨r, hfr⟩
    refine ⟨⟨fun v => ⟨?_, ?_⟩, _, hx⟩, int y', hy⟩
    · rintro ⟨_, ⟨y0, _, rfl, hy0, _, _, rfl, rfl, rfl⟩, hgv⟩
      have hgv' : c.hv g [y0, int 0] = some v := hgv
      rw [hone 1 y0 (int y') hy0 hy, hgy] at hgv'
      cases hgv'; rfl
    · rintro rfl
      exact ⟨[int y', int 0], ⟨int y', [int 0], rfl, hy, int 0, [], rfl, rfl, rfl⟩, hgy⟩
  · rintro ⟨⟨heq, x, hx⟩, -⟩
    obtain ⟨_, ⟨y, _, rfl, hy, _, _, rfl, rfl, rfl⟩, hgv⟩ := (heq _).mpr rfl
    obtain ⟨x', rfl⟩ := hI0 x hx
    obtain ⟨y', rfl⟩ := hI1 y hy
    obtain ⟨r, hfr⟩ := (hfg x' y').mpr hgv
    exact ⟨r, [int x', int y'], ⟨int x', [int y'], rfl, hx, int y', [], rfl, hy, rfl⟩, hfr⟩

/-! ### The five Int symbols: where each is defined -/

section
variable {c : Semantics}

/-- Off the keys of `silentTable`, where `hook` states no value Γ's value is none. -/
theorem ceil_hv_none {f : Sym} (hf : silentKey f = false) {vs : List GroundTerm} (hh : hook f vs = some none) :
    c.hv f vs = none := by
  unfold Semantics.hv; rw [Semantics.hookRes_of_notKey hf, hh]; rfl

/-- A t-division or modulus `f` (`nonzero`) at `x`, `y` has a value exactly where `y =/=Int 0`. -/
theorem ceil_fg_nonzero {f : Sym} (hf : silentKey f = false) (op : Int → Int → Int)
    (hh : ∀ x y, hook f [int x, int y] = some (nonzero y (op x y))) (x y : Int) :
    (∃ r, c.hv f [int x, int y] = some r) ↔ c.hv intNe [int y, int 0] = some (bool true) := by
  rw [hv_intNe]
  by_cases hy : y = 0
  · subst hy
    rw [ceil_hv_none hf (by rw [hh]; rfl)]
    simp [bool]
  · rw [hv_of_value (v := int (op x y)) (by rw [hh, nonzero]; simp only [hy, ↓reduceIte])]
    simp [hy]

/-- A shift `f` at `x`, `n` has a value exactly where `n >=Int 0`. -/
theorem ceil_fg_shift {f : Sym} (hf : silentKey f = false) (op : Int → Int → Int)
    (hh : ∀ x n, hook f [int x, int n] = some (if n < 0 then none else some (int (op x n)))) (x y : Int) :
    (∃ r, c.hv f [int x, int y] = some r) ↔ c.hv intGe [int y, int 0] = some (bool true) := by
  rw [fhv_intGe]
  by_cases hy : y < 0
  · rw [ceil_hv_none hf (by rw [hh]; simp only [hy, ↓reduceIte])]
    simp [bool]; omega
  · rw [hv_of_value (v := int (op x y)) (by rw [hh]; simp only [hy, ↓reduceIte])]
    simp [bool]; omega

theorem ceil_fg_tmod (x y : Int) :
    (∃ r, c.hv intTMod [int x, int y] = some r) ↔ c.hv intNe [int y, int 0] = some (bool true) :=
  ceil_fg_nonzero (by decide +kernel) Int.tmod (fun _ _ => rfl) x y
theorem ceil_fg_tdiv (x y : Int) :
    (∃ r, c.hv intTDiv [int x, int y] = some r) ↔ c.hv intNe [int y, int 0] = some (bool true) :=
  ceil_fg_nonzero (by decide +kernel) Int.tdiv (fun _ _ => rfl) x y
theorem ceil_fg_emod (x y : Int) :
    (∃ r, c.hv intEMod [int x, int y] = some r) ↔ c.hv intNe [int y, int 0] = some (bool true) :=
  ceil_fg_nonzero (by decide +kernel) Int.emod (fun _ _ => rfl) x y
theorem ceil_fg_shr (x y : Int) :
    (∃ r, c.hv intShr [int x, int y] = some r) ↔ c.hv intGe [int y, int 0] = some (bool true) :=
  ceil_fg_shift (by decide +kernel) (fun x n => x.fdiv (2 ^ n.toNat)) (fun _ _ => rfl) x y
theorem ceil_fg_shl (x y : Int) :
    (∃ r, c.hv intShl [int x, int y] = some r) ↔ c.hv intGe [int y, int 0] = some (bool true) :=
  ceil_fg_shift (by decide +kernel) (fun x n => x * 2 ^ n.toNat) (fun _ _ => rfl) x y

end

/-! ## `#Ceil(@K0 |-> @K1 @Rest) => {@K0 in_keys(@Rest) #Equals false} #And #Ceil(@K1)` -/

/-- The definedness lemma kompile generates for `_Map_` at a map of one entry and a rest. -/
def ceilMapEqn : SvEqn :=
  ⟨[("VarK0", Srt.kitem), ("VarK1", Srt.kitem), ("VarRest", Srt.map)],
    .ceil Srt.map (.app mapConcat [.app mapElem [.var 0, .var 1], .var 2]),
    .and (.eq Srt.bool (.app mapInKeys [.var 0, .var 2]) (.dv Srt.bool (.bool false)))
      (.and .top (.ceil Srt.kitem (.var 1))), []⟩

theorem ceilMap_apart {c : Semantics} (h : c.coreOK = true) :
    ceilMapEqn.lhs.Apart c ∧ ceilMapEqn.rhs.Apart c := by
  haveI : OvlOK c := ovlOK_of_core h
  exact ⟨trivial, ⟨apart_of_distinct bool_distinct, trivial, trivial⟩⟩

section
variable {c : Semantics}

theorem ceilMap_hv_elem (k v : GroundTerm) : c.hv mapElem [k, v] = some (.map Srt.map [(k, v)]) := hv_of_value rfl

theorem ceilMap_hv_concat (k v : GroundTerm) (s : Srt) (m : Entries) :
    c.hv mapConcat [.map Srt.map [(k, v)], .map s m] =
      (if hasKey k m then none else some (.map Srt.map (insertE k v m))) := by
  unfold Semantics.hv
  rw [Semantics.hookRes_of_notKey (by decide +kernel)]
  show (some ((union [(k, v)] m).map (GroundTerm.map Srt.map))).join = _
  simp only [union, Option.bind_some, addNew, Option.join_some]
  split <;> rfl

theorem ceilMap_hv_inKeys (k : GroundTerm) (s : Srt) (m : Entries) :
    c.hv mapInKeys [k, .map s m] = some (bool (hasKey k m)) := hv_of_value rfl

end

/-- **The lemma is refuted at values**: in every model of `Γ c`, at `@K0 = {k}`, `@K1 = {v}` and
`@Rest` the maps `m0` without the key `k` and `m1` with it, the left side holds (`k |-> v` and `m0`
have a union) and `@K0 in_keys(@Rest)` denotes `true`, which is not `false`. -/
theorem ceilMap_refuted_at {c : Semantics} (h : c.coreOK = true) (hr : ceilMapEqn.regular = true)
    (ht : ceilMapEqn.typed c = true) (k v : GroundTerm) (m0 m1 : Entries)
    (hk : c.sortOf k = some Srt.kitem) (hv : c.sortOf v = some Srt.kitem)
    (hm0 : c.sortOf (.map Srt.map m0) = some Srt.map) (hm1 : c.sortOf (.map Srt.map m1) = some Srt.map)
    (h0 : hasKey k m0 = false) (h1 : hasKey k m1 = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ceilMapEqn.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  refine SvEqn.refuted_at h _ hr ht (ceilMap_apart h)
    (fun i (w : GroundTerm) => (i = 0 ∧ w = k) ∨ (i = 1 ∧ w = v) ∨ (i = 2 ∧ (w = .map Srt.map m0 ∨ w = .map Srt.map m1)))
    ?_ (fun _ h => nomatch h) ?_ ad hp hsv hI
  · intro i x hx w hw
    match i, hx with
    | 0, hx => cases hx; rcases hw with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> first | exact hk | cases h'
    | 1, hx => cases hx; rcases hw with ⟨h', -⟩ | ⟨-, rfl⟩ | ⟨h', -⟩ <;> first | exact hv | cases h'
    | 2, hx =>
      cases hx
      rcases hw with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, rfl | rfl⟩
      · cases h'
      · cases h'
      · exact hm0
      · exact hm1
  · intro hiff
    have hL : ceilMapEqn.lhs.Holds c
        (fun i (w : GroundTerm) => (i = 0 ∧ w = k) ∨ (i = 1 ∧ w = v) ∨ (i = 2 ∧ (w = .map Srt.map m0 ∨ w = .map Srt.map m1))) := by
      refine ⟨.map Srt.map (insertE k v m0), [.map Srt.map [(k, v)], .map Srt.map m0],
        ⟨.map Srt.map [(k, v)], [.map Srt.map m0], rfl,
          ⟨[k, v], ⟨k, [v], rfl, Or.inl ⟨rfl, rfl⟩, v, [], rfl, Or.inr (Or.inl ⟨rfl, rfl⟩), rfl⟩, ceilMap_hv_elem k v⟩,
          .map Srt.map m0, [], rfl, Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩), rfl⟩, ?_⟩
      rw [ceilMap_hv_concat, h0]; rfl
    obtain ⟨heq, -⟩ := hiff.mp hL
    have := (heq (bool true)).mp ⟨[k, .map Srt.map m1], ⟨k, [.map Srt.map m1], rfl, Or.inl ⟨rfl, rfl⟩,
      .map Srt.map m1, [], rfl, Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩), rfl⟩, by rw [ceilMap_hv_inKeys, h1]⟩
    exact absurd this (by simp [svVals, bool])

/-- **The companion**: at sets of at most one value the lemma holds, in every semantics whose Map
values are maps (`shapesOK`): `k |-> v` and a map `m` have a union exactly where `k` is no key of
`m`. -/
theorem ceilMap_one {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (hr : ceilMapEqn.regular = true) (ht : ceilMapEqn.typed c = true) (hkap : apartSort c Srt.map = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = ceilMapEqn.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    SvAtMostOne c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI : OvlOK c := ovlOK_of_core h
  have hki : apartSort c Srt.kitem = true := by simp [apartSort]
  refine SvEqn.entailed_one h _ hr ht (ceilMap_apart h)
    (fun x hx => by
      simp only [ceilMapEqn, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hki
      · exact hki
      · exact hkap) ?_ ad hp hsv
  intro ρ hρ hone
  have hR : ∀ w, ρ 2 w → ∃ es, w = .map Srt.map es := fun w hw => shape_map hs (hρ 2 _ rfl w hw)
  simp only [ceilMapEqn, SvPred.Holds, svVals, svValsList]
  constructor
  · rintro ⟨r, _, ⟨_, _, rfl, ⟨_, ⟨k, _, rfl, hk, w, _, rfl, hw, rfl⟩, he⟩, mr, _, rfl, hm, rfl⟩, hc⟩
    rw [ceilMap_hv_elem] at he
    cases he
    obtain ⟨m, rfl⟩ := hR mr hm
    rw [ceilMap_hv_concat] at hc
    have hnk : hasKey k m = false := by
      cases hh : hasKey k m with
      | false => rfl
      | true => rw [hh] at hc; cases hc
    refine ⟨fun b => ⟨?_, ?_⟩, trivial, w, hw⟩
    · rintro ⟨_, ⟨k', _, rfl, hk', m', _, rfl, hm', rfl⟩, hb⟩
      rw [hone 0 k' k hk' hk, hone 2 m' _ hm' hm, ceilMap_hv_inKeys, hnk] at hb
      cases hb; rfl
    · rintro rfl
      exact ⟨[k, .map Srt.map m], ⟨k, [.map Srt.map m], rfl, hk, .map Srt.map m, [], rfl, hm, rfl⟩,
        by rw [ceilMap_hv_inKeys, hnk]; rfl⟩
  · rintro ⟨heq, -, w, hw⟩
    obtain ⟨_, ⟨k, _, rfl, hk, mr, _, rfl, hm, rfl⟩, hb⟩ := (heq _).mpr rfl
    obtain ⟨m, rfl⟩ := hR mr hm
    rw [ceilMap_hv_inKeys] at hb
    have hnk : hasKey k m = false := by
      cases hh : hasKey k m with
      | false => rfl
      | true => rw [hh] at hb; cases hb
    refine ⟨.map Srt.map (insertE k w m), [.map Srt.map [(k, w)], .map Srt.map m],
      ⟨.map Srt.map [(k, w)], [.map Srt.map m], rfl,
        ⟨[k, w], ⟨k, [w], rfl, hk, w, [], rfl, hw, rfl⟩, ceilMap_hv_elem k w⟩,
        .map Srt.map m, [], rfl, hm, rfl⟩, ?_⟩
    rw [ceilMap_hv_concat, hnk]; rfl

end LibEv

end KCore
