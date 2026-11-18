/-
  KCore. The associativity of a parameter that a registry hook implements, at values, from the
  hook's computation.

  The reader takes the `[assoc]` axiom of a parameter symbol f as a law of `Presentation.laws`,
  stated at values under `FnLaws` and owed (`Parse.fnLawHead`). Where a registry hook implements f
  the law is a statement about the hook's function. Here it holds, under every interpretation, for
  the hooks of `assocIntHooks` at Int:

  - `assocIntOp g`: the integer operation the table `intHooks` gives the hook g (`hook_assocInt`,
    by the table's entry), associative for each hook of the list (`assocIntOp_assoc`);
  - `paramVal_intHook`: the parameter's value at two Ints is the hook's;
  - `hookAssocLaw_sides`: the one result of each side of the law;
  - `hookAssoc_lawAt`: `LawAt c (Parse.hookAssocLawOf f)`.

  Of another hook the law may be false: of a parameter `INT.sub` implements it is
  (`intSub_not_lawAt`, at (1, 1, 1): (1 - 1) - 1 = -1 and 1 - (1 - 1) = 1). The reader reads both
  texts alike; the law is owed, and a text whose law is false has no tie.
-/
import KcoreSpec.Parse
import KcoreSpec.Faithful
import KcoreSpec.LazySound

set_option autoImplicit false

namespace KCore

open Parse (hookAssocLawOf)

/-- Registry hooks whose function is associative on Int: the sum, the product, the smaller and the
larger of two integers (`intHooks`). -/
def assocIntHooks : List Sym := [intAdd, intMul, intMin, intMax]

/-- The parameter is implemented by a hook of `assocIntHooks` at Int itself: two Int arguments and
an Int result. -/
def assocIntHookParam (k : ParamSig) : Bool :=
  !k.raw && k.sig.args == [Srt.int, Srt.int] && k.sig.result == Srt.int && k.impl.any assocIntHooks.contains

/-- The integer operation of a hook of `assocIntHooks`. -/
def assocIntOp (g : Sym) : Int → Int → Int :=
  if g = intAdd then (· + ·) else if g = intMul then (· * ·) else if g = intMin then min else max

theorem assocIntOp_assoc (g : Sym) (x y z : Int) :
    assocIntOp g (assocIntOp g x y) z = assocIntOp g x (assocIntOp g y z) := by
  unfold assocIntOp
  split
  · exact Int.add_assoc x y z
  · split
    · exact Int.mul_assoc x y z
    · split
      · exact Int.min_assoc x y z
      · exact Int.max_assoc x y z

/-- A hook of `assocIntHooks` computes `assocIntOp` at two Ints: its entry of `intHooks`. -/
theorem hook_assocInt {g : Sym} (hg : assocIntHooks.contains g = true) (x y : Int) :
    hook g [int x, int y] = some (some (int (assocIntOp g x y))) := by
  simp only [assocIntHooks, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> rfl

/-- No hook of `assocIntHooks` has a silent point. -/
theorem assocIntHooks_plain {g : Sym} (hg : assocIntHooks.contains g = true) : silentKey g = false := by
  simp only [assocIntHooks, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> decide

/-- **The parameter's value is the hook's**: a parameter of result sort Int that the registry hook
g implements has, at two Ints where g gives an Int and has no silent point, that Int, under every
interpretation. -/
theorem paramVal_intHook {c : Semantics} {f : Sym} {k : ParamSig} {g : Sym} (hp : c.lookupParam f = some k)
    (hi : k.impl = some g) (hres : k.sig.result = Srt.int) (hs : silentKey g = false) {x y r : Int}
    (hh : hook g [int x, int y] = some (some (int r))) : c.paramVal f [int x, int y] = some (int r) := by
  unfold Semantics.paramVal
  rw [hp]; dsimp only; rw [hi]; dsimp only
  have hargs : c.libArgs g [int x, int y] = [int x, int y] := by
    simp [Semantics.libArgs, int, GroundTerm.toLib]
  have hso : c.sortOf (.dv Srt.int (.int r)) = some Srt.int := sortOf_int (c := c) _
  rw [hargs, Semantics.hookRes_of_notKey hs, hh, hres]
  simp [int, GroundTerm.asSort, Option.filter, hso]

/-- The results of a parameter symbol applied to two terms: the parameter's value at the terms'
results, nothing where one has none. -/
theorem evalParam2_iff {c : Semantics} {f : Sym} (hc : c.isCtor f = false) (hh : isHook f = false)
    (hpm : c.isParam f = true) (ho : c.isOvl f = false) {σ : Subst} {t u : Term} {r : Option GroundTerm} :
    EvalTerm c σ (.app f [t, u]) r ↔
      ∃ a b, EvalTerm c σ t a ∧ EvalTerm c σ u b ∧ r = (allSome [a, b]).bind (c.paramVal f) := by
  constructor
  · intro h
    cases h with
    | ctor h _ => rw [hc] at h; cases h
    | hook _ hhk _ _ _ => rw [hh] at hhk; cases hhk
    | param _ _ _ hts hr =>
      cases hts with
      | cons ha hts =>
        cases hts with
        | cons hb hts => cases hts; exact ⟨_, _, ha, hb, hr⟩
    | call _ _ _ _ _ hp => rw [hpm] at hp; cases hp
    | callUndef _ _ _ _ hp => rw [hpm] at hp; cases hp
    | ovl _ ho' _ _ => rw [ho] at ho'; cases ho'
    | ovlFn _ ho' _ _ _ _ _ => rw [ho] at ho'; cases ho'
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact .param hc hh hpm (.cons ha (.cons hb .nil)) rfl

theorem evalVar_iff {c : Semantics} {σ : Subst} {i : Nat} {r : Option GroundTerm} :
    EvalTerm c σ (.var i) r ↔ r = σ.lookup i :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .var⟩

/-- **The two sides of the associativity law of a parameter a hook implements**: where the hook g
gives the Int `op x y` at every two Ints and has no silent point, under a substitution of the Ints
x, y, z the left side `f(f(x, y), z)` has the one result `op (op x y) z` and the right side
`f(x, f(y, z))` the one result `op x (op y z)`, under every interpretation. -/
theorem hookAssocLaw_sides {c : Semantics} {f : Sym} {k : ParamSig} {g : Sym}
    (hp : c.lookupParam f = some k) (hi : k.impl = some g) (hres : k.sig.result = Srt.int)
    (hsk : silentKey g = false) {op : Int → Int → Int}
    (hop : ∀ x y : Int, hook g [int x, int y] = some (some (int (op x y))))
    (hc : c.isCtor f = false) (hh : isHook f = false) (ho : c.isOvl f = false)
    {σ : Subst} {x y z : Int} (hx : σ.lookup 0 = some (int x)) (hy : σ.lookup 1 = some (int y))
    (hz : σ.lookup 2 = some (int z)) (r : Option GroundTerm) :
    (EvalTerm c σ (hookAssocLawOf f).lhs r ↔ r = some (int (op (op x y) z))) ∧
    (EvalTerm c σ (hookAssocLawOf f).rhs r ↔ r = some (int (op x (op y z)))) := by
  have hval : ∀ a b : Int, c.paramVal f [int a, int b] = some (int (op a b)) :=
    fun a b => paramVal_intHook hp hi hres hsk (hop a b)
  have hpm : c.isParam f = true := by unfold Semantics.isParam; rw [hp]; rfl
  constructor
  · simp only [hookAssocLawOf, evalParam2_iff hc hh hpm ho, evalVar_iff, hx, hy, hz]
    constructor
    · rintro ⟨a, b, ⟨a', b', rfl, rfl, rfl⟩, rfl, rfl⟩
      simp [allSome, hval]
    · rintro rfl
      exact ⟨_, _, ⟨_, _, rfl, rfl, rfl⟩, rfl, by simp [allSome, hval]⟩
  · simp only [hookAssocLawOf, evalParam2_iff hc hh hpm ho, evalVar_iff, hx, hy, hz]
    constructor
    · rintro ⟨a, b, rfl, ⟨a', b', rfl, rfl, rfl⟩, rfl⟩
      simp [allSome, hval]
    · rintro rfl
      exact ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, by simp [allSome, hval]⟩

/-- **The associativity of a parameter that a hook of `assocIntHooks` implements at Int holds at
values, under every interpretation**: both sides of `f(f(x, y), z) = f(x, f(y, z))` have the one
result the hook's operation gives, which is associative. The parameter is asked to be no
constructor, no interpreted hook and no overloading symbol. -/
theorem hookAssoc_lawAt {c : Semantics} (hs : c.shapesOK = true) {f : Sym} {k : ParamSig}
    (hp : c.lookupParam f = some k) (hk : assocIntHookParam k = true)
    (hc : c.isCtor f = false) (hh : isHook f = false) (ho : c.isOvl f = false) :
    LawAt c (hookAssocLawOf f) := by
  simp only [assocIntHookParam, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.any_eq_true] at hk
  obtain ⟨⟨⟨-, -⟩, hres⟩, g, hi, hg⟩ := hk
  intro σ hσ r
  obtain ⟨vx, hx, hsx⟩ := hσ 0 Srt.int rfl
  obtain ⟨vy, hy, hsy⟩ := hσ 1 Srt.int rfl
  obtain ⟨vz, hz, hsz⟩ := hσ 2 Srt.int rfl
  obtain ⟨x, rfl⟩ := shape_int hs hsx
  obtain ⟨y, rfl⟩ := shape_int hs hsy
  obtain ⟨z, rfl⟩ := shape_int hs hsz
  obtain ⟨hl, hr⟩ := hookAssocLaw_sides hp hi hres (assocIntHooks_plain hg) (hook_assocInt hg) hc hh ho hx hy hz r
  rw [hl, hr, assocIntOp_assoc]

/-- **The associativity of a parameter that `INT.sub` implements at Int is false at values, under
every interpretation**: at (1, 1, 1) the left side is `(1 - 1) - 1 = -1` and the right side
`1 - (1 - 1) = 1`. -/
theorem intSub_not_lawAt {c : Semantics} {f : Sym} {k : ParamSig}
    (hp : c.lookupParam f = some k) (hi : k.impl = some intSub) (hres : k.sig.result = Srt.int)
    (hc : c.isCtor f = false) (hh : isHook f = false) (ho : c.isOvl f = false) :
    ¬ LawAt c (hookAssocLawOf f) := by
  intro h
  let σ : Subst := [(0, int 1), (1, int 1), (2, int 1)]
  have hσ : c.WellSorted [Srt.int, Srt.int, Srt.int] σ := by
    intro i s hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
    | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
    | 2, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
    | n + 3, hi => simp at hi
  obtain ⟨hl, hr⟩ := hookAssocLaw_sides (σ := σ) (x := 1) (y := 1) (z := 1) hp hi hres (by decide)
    (op := fun x y => x - y) (fun _ _ => rfl) hc hh ho rfl rfl rfl (some (int (1 - 1 - 1)))
  have := hr.mp ((h σ hσ _).mp (hl.mpr rfl))
  simp [int] at this

end KCore
