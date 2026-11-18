/-
  KCore, checked layer: the eight Bool predicate sentences over set variables are entailed at sets
  of values (`EntailsAtSetValues`), for every semantics meeting `coreOK` whose Bool values are
  literals (`shapesOK`) and every interpretation.

  domains.md 1176 to 1179 and 1181 to 1184 (K 7.1.337, BOOL-KORE):

    {true #Equals notBool @B} => {false #Equals @B}       {notBool @B #Equals true} => {@B #Equals false}
    {false #Equals notBool @B} => {true #Equals @B}       {notBool @B #Equals false} => {@B #Equals true}
    {true #Equals @B1 andBool @B2} => {true #Equals @B1} #And {true #Equals @B2}     (and the flip)
    {false #Equals @B1 orBool @B2} => {false #Equals @B1} #And {false #Equals @B2}   (and the flip)

  At a set `B` of Bool values, `notBool @B` denotes the negations of its members, so it is the one
  value `b` exactly where `B` is the one value `!b`: both sides hold at the same sets, the empty set
  and the set of both values among them. `@B1 andBool @B2` denotes the conjunctions of a member of
  each; it is `true` alone exactly where each set is `true` alone (an empty set gives no value).
  `orBool` at `false` is the dual.

  - `boolNotSet b flip`: the four `notBool` sentences (`b` the literal, `flip` the literal first);
    `boolNotSet_ev`.
  - `boolBinSet f b flip`: `andBool` at `true` and `orBool` at `false`; `boolBinSet_ev`.
-/
import KcoreSpec.LibEvSetVar
import KcoreSpec.LibEvFnLib
import KcoreSpec.LibEvFnBoolInt

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The Bool literal `b` as a term. -/
def bsLit (b : Bool) : Term := .dv Srt.bool (.bool b)

/-- `\equals{SortBool, Q0}(t, u)`, the two sides exchanged where `flip`. -/
def bsEq (flip : Bool) (t u : Term) : SvPred :=
  if flip then .eq Srt.bool u t else .eq Srt.bool t u

/-- `{notBool @B #Equals b} => {@B #Equals !b}`, each literal first where `flip`. -/
def boolNotSet (b flip : Bool) : SvEqn :=
  ⟨[("VarB", Srt.bool)], bsEq flip (.app boolNot [.var 0]) (bsLit b), bsEq flip (.var 0) (bsLit !b), []⟩

/-- `{f(@B1, @B2) #Equals b} => {@B1 #Equals b} #And {@B2 #Equals b}`, each literal first where
`flip`. -/
def boolBinSet (f : Sym) (b flip : Bool) : SvEqn :=
  ⟨[("VarB1", Srt.bool), ("VarB2", Srt.bool)], bsEq flip (.app f [.var 0, .var 1]) (bsLit b),
    .and (bsEq flip (.var 0) (bsLit b)) (bsEq flip (.var 1) (bsLit b)), []⟩

theorem bsEq_holds (c : Semantics) (ρ : Nat → GroundTerm → Prop) (flip : Bool) (t u : Term) :
    (bsEq flip t u).Holds c ρ ↔ ∀ v, svVals c ρ t v ↔ svVals c ρ u v := by
  cases flip
  · rfl
  · show (∀ v, svVals c ρ u v ↔ svVals c ρ t v) ↔ _
    exact forall_congr' fun v => Iff.comm

theorem bsEq_apart {c : Semantics} (h : c.coreOK = true) (flip : Bool) (t u : Term) : (bsEq flip t u).Apart c := by
  haveI : OvlOK c := ovlOK_of_core h
  cases flip <;> exact apart_of_distinct bool_distinct

theorem bs_bool_inj {a b : Bool} : bool a = bool b ↔ a = b := by
  cases a <;> cases b <;> simp [bool]

/-- **The `notBool` sentences hold at every set of values.** -/
theorem boolNotSet_holds {c : Semantics} (hs : c.shapesOK = true) (b flip : Bool) :
    (boolNotSet b flip).Holds c (fun _ => True) := by
  intro ρ hρ _
  have hB : ∀ v, ρ 0 v → ∃ x, v = bool x := fun v hv => shape_bool hs (hρ 0 _ rfl v hv)
  simp only [boolNotSet, bsEq_holds, svVals, svValsList, bsLit]
  constructor
  · intro hl v
    constructor
    · intro hv
      obtain ⟨x, rfl⟩ := hB v hv
      have := (hl (bool !x)).mp ⟨[bool x], ⟨bool x, [], rfl, hv, rfl⟩, fhv_boolNot x⟩
      have hx : (!x) = b := bs_bool_inj.mp this
      show bool x = bool !b
      rw [← hx, Bool.not_not]
    · rintro rfl
      obtain ⟨_, ⟨w, _, rfl, hw, rfl⟩, hnw⟩ := (hl (bool b)).mpr rfl
      obtain ⟨x, rfl⟩ := hB w hw
      rw [fhv_boolNot] at hnw
      have hx : (!x) = b := bs_bool_inj.mp (Option.some.inj hnw)
      rw [← hx, Bool.not_not]; exact hw
  · intro hr v
    constructor
    · rintro ⟨_, ⟨w, _, rfl, hw, rfl⟩, hnw⟩
      obtain ⟨x, rfl⟩ := hB w hw
      rw [fhv_boolNot] at hnw
      cases hnw
      have hx : x = !b := bs_bool_inj.mp ((hr _).mp hw)
      show bool (!x) = bool b
      rw [hx, Bool.not_not]
    · rintro rfl
      have hw := (hr (bool !b)).mpr rfl
      exact ⟨[bool !b], ⟨bool !b, [], rfl, hw, rfl⟩, by rw [fhv_boolNot, Bool.not_not]; rfl⟩

/-- **`andBool` at `true` and `orBool` at `false` hold at every set of values**: for a symbol whose
value at two Bools is `b` exactly where both are `b`. -/
theorem boolBinSet_holds {c : Semantics} (hs : c.shapesOK = true) (f : Sym) (op : Bool → Bool → Bool)
    (hf : ∀ x y, c.hv f [bool x, bool y] = some (bool (op x y))) (b : Bool)
    (hop : ∀ x y, op x y = b ↔ x = b ∧ y = b) (flip : Bool) :
    (boolBinSet f b flip).Holds c (fun _ => True) := by
  intro ρ hρ _
  have hB0 : ∀ v, ρ 0 v → ∃ x, v = bool x := fun v hv => shape_bool hs (hρ 0 _ rfl v hv)
  have hB1 : ∀ v, ρ 1 v → ∃ x, v = bool x := fun v hv => shape_bool hs (hρ 1 _ rfl v hv)
  simp only [boolBinSet, bsEq_holds, SvPred.Holds, svVals, svValsList, bsLit]
  constructor
  · intro hl
    -- the image holds `b`, so each set has a member
    obtain ⟨_, ⟨x0, _, rfl, hx0, y0, _, rfl, hy0, rfl⟩, hxy⟩ := (hl (bool b)).mpr rfl
    -- every member of each set is `b`
    have hall : ∀ x y, ρ 0 (bool x) → ρ 1 (bool y) → x = b ∧ y = b := fun x y hx hy =>
      (hop x y).mp (bs_bool_inj.mp ((hl _).mp ⟨[bool x, bool y], ⟨bool x, [bool y], rfl, hx, bool y, [], rfl, hy, rfl⟩,
        hf x y⟩))
    obtain ⟨x0', rfl⟩ := hB0 x0 hx0
    obtain ⟨y0', rfl⟩ := hB1 y0 hy0
    have hb0 := hall x0' y0' hx0 hy0
    refine ⟨fun v => ⟨fun hv => ?_, ?_⟩, fun v => ⟨fun hv => ?_, ?_⟩⟩
    · obtain ⟨x, rfl⟩ := hB0 v hv
      rw [(hall x y0' hv hy0).1]; rfl
    · rintro rfl; rw [← hb0.1]; exact hx0
    · obtain ⟨y, rfl⟩ := hB1 v hv
      rw [(hall x0' y hx0 hv).2]; rfl
    · rintro rfl; rw [← hb0.2]; exact hy0
  · rintro ⟨h0, h1⟩ v
    constructor
    · rintro ⟨_, ⟨x, _, rfl, hx, y, _, rfl, hy, rfl⟩, hxy⟩
      have ex : x = bool b := (h0 x).mp hx
      have ey : y = bool b := (h1 y).mp hy
      subst ex ey
      rw [hf] at hxy
      cases hxy
      rw [(hop b b).mpr ⟨rfl, rfl⟩]; rfl
    · rintro rfl
      exact ⟨[bool b, bool b], ⟨bool b, [bool b], rfl, (h0 _).mpr rfl, bool b, [], rfl, (h1 _).mpr rfl, rfl⟩,
        by rw [hf, (hop b b).mpr ⟨rfl, rfl⟩]; rfl⟩

/-- **domains.md 1176 to 1179** are entailed at set values. -/
theorem boolNotSet_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (b flip : Bool)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = (boolNotSet b flip).patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) : EntailsAtSetValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  SvEqn.entailed h (boolNotSet b flip) (by cases b <;> cases flip <;> decide +kernel) (by cases b <;> cases flip <;> rfl)
    ⟨bsEq_apart h _ _ _, bsEq_apart h _ _ _⟩ (boolNotSet_holds hs b flip) ad hp hsv

/-- **domains.md 1181, 1182** (`andBool` at `true`) are entailed at set values. -/
theorem boolAndSet_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (flip : Bool)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = (boolBinSet boolAnd true flip).patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) : EntailsAtSetValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  SvEqn.entailed h (boolBinSet boolAnd true flip) (by cases flip <;> decide +kernel) (by cases flip <;> rfl)
    ⟨bsEq_apart h _ _ _, bsEq_apart h _ _ _, bsEq_apart h _ _ _⟩
    (boolBinSet_holds hs boolAnd (· && ·) fhv_boolAnd true (fun x y => by cases x <;> cases y <;> simp) flip)
    ad hp hsv

/-- **domains.md 1183, 1184** (`orBool` at `false`) are entailed at set values. -/
theorem boolOrSet_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (flip : Bool)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = (boolBinSet boolOr false flip).patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) : EntailsAtSetValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  SvEqn.entailed h (boolBinSet boolOr false flip) (by cases flip <;> decide +kernel) (by cases flip <;> rfl)
    ⟨bsEq_apart h _ _ _, bsEq_apart h _ _ _, bsEq_apart h _ _ _⟩
    (boolBinSet_holds hs boolOr (· || ·) fhv_boolOr false (fun x y => by cases x <;> cases y <;> simp) flip)
    ad hp hsv

end LibEv

end KCore
