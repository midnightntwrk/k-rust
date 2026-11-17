/-
  The union tie (KcoreSpec/TieUnion.lean) at two alternatives.
  Run from the package root: `lake env lean -j1 test/TieUnion.lean`.

  - `shape2`, `alt2`, `none2`: the sentence and the three equations of two alternatives, as written
    out (`rfl`).
  - The instance, the shape of `h(X) => f(X) #Or g(X)` with no condition (`E := ⊤`, `prem := ⊤`):
    `F := h ⬝ x`, the alternatives `f ⬝ x` and `g ⬝ x`, the functional sentence's variable y not
    free in F (`y_fresh`, kernel). `inst_alt1`, `inst_alt2`, `inst_none`: the sentence with the
    functional sentence entails each of the three equations; `inst_text`: the three entail the
    sentence.
  - `two_elements`: without the bound on F the first equation does not follow. In the
    interpretation over `Bool` whose every application is every element (so `⌈_⌉` is definedness and
    `h ⬝ x`, `f ⬝ x`, `g ⬝ x` each hold both elements) with `f ⬝ x` replaced by the variable x, the
    sentence `⊤ → h ⬝ x = x ∨ g ⬝ x` holds and `⊤ ∧ ⌈x⌉ ∧ ⌈⊤⌉ → h ⬝ x = x` does not.
-/
import KcoreSpec

set_option autoImplicit false

namespace KoreAML.TieUnionTest

open ML KoreAML KoreAML.TieUnion

theorem shape2 (prem F a1 E1 a2 E2 : P) :
    unionSentence prem F [(a1, E1), (a2, E2)] = (prem ⇒ (F ≡ (a1 ⋀ ⌈E1⌉) ⋁ (a2 ⋀ ⌈E2⌉))) := rfl
theorem alt2 (prem F a E : P) : altClause prem F (a, E) = ((prem ⋀ (⌈a⌉ ⋀ ⌈E⌉)) ⇒ (F ≡ a)) := rfl
theorem none2 (prem F a1 E1 a2 E2 : P) :
    noneClause prem F [(a1, E1), (a2, E2)] =
      ((prem ⋀ (∼(⌈a1⌉ ⋀ ⌈E1⌉) ⋀ ∼(⌈a2⌉ ⋀ ⌈E2⌉))) ⇒ (F ≡ ⊥)) := rfl

/-! ## The instance -/

def x : EVar := ⟨0⟩
def y : EVar := ⟨1⟩
def F : P := sym (.symbol "Lblh") ⬝ .evar x
def a1 : P := sym (.symbol "Lblf") ⬝ .evar x
def a2 : P := sym (.symbol "Lblg") ⬝ .evar x
def alts : List (P × P) := [(a1, ⊤), (a2, ⊤)]

theorem y_fresh : F.isFreeEvar y = false := by decide +kernel

theorem inst_alt1 : TextSide y ⊤ F alts ⊧ ((⊤ ⋀ (⌈a1⌉ ⋀ ⌈(⊤ : P)⌉)) ⇒ (F ≡ a1)) :=
  text_entails_alt y_fresh (x := (a1, ⊤)) (List.mem_cons_self ..)
theorem inst_alt2 : TextSide y ⊤ F alts ⊧ ((⊤ ⋀ (⌈a2⌉ ⋀ ⌈(⊤ : P)⌉)) ⇒ (F ≡ a2)) :=
  text_entails_alt y_fresh (x := (a2, ⊤)) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem inst_none : TextSide y ⊤ F alts ⊧
    ((⊤ ⋀ (∼(⌈a1⌉ ⋀ ⌈(⊤ : P)⌉) ⋀ ∼(⌈a2⌉ ⋀ ⌈(⊤ : P)⌉))) ⇒ (F ≡ ⊥)) :=
  text_entails_none
theorem inst_text : SplitSide ⊤ F alts ⊧ (⊤ ⇒ (F ≡ (a1 ⋀ ⌈(⊤ : P)⌉) ⋁ (a2 ⋀ ⌈(⊤ : P)⌉))) :=
  split_entails_text

/-! ## Without the bound on F -/

/-- Every symbol is every element, and every application is every element. -/
def allI : Interpretation Sym Bool := { evalSymb := fun _ _ => True, evalApp := fun _ _ _ => True }

theorem allI_def : DefOK allI := fun _ _ => ⟨true, trivial, trivial⟩

def e0 : Valuation Bool := ⟨fun _ => true, fun _ _ => False⟩

/-- The sentence holds at the alternatives x and `g ⬝ x`, F holding both elements, and the equation
of the alternative x does not: F is not the one element of x. -/
theorem two_elements :
    (unionSentence ⊤ F [(.evar x, ⊤), (a2, ⊤)]).interpret allI e0 true ∧
      ¬ (altClause ⊤ F (.evar x, ⊤)).interpret allI e0 true := by
  have happ : ∀ (s : Sym) (b : Bool), (sym s ⬝ Pattern.evar x : P).interpret allI e0 b := fun s b =>
    (interpret_app).mpr ⟨true, true, trivial, rfl, trivial⟩
  have htop : ∀ b : Bool, (⊤ : P).interpret allI e0 b := fun b => by simp
  constructor
  · rw [interp_unionSentence allI_def]
    intro _ a
    exact ⟨fun _ => ⟨(a2, ⊤), List.mem_cons_of_mem _ (List.mem_cons_self ..), happ _ a, true, htop true⟩,
      fun _ => happ _ a⟩
  · rw [interp_altClause allI_def]
    intro h
    have := (h (htop true) ⟨true, rfl⟩ ⟨true, htop true⟩ false).mp (happ _ false)
    have h2 : false = e0.evalEvar x := (interp_evar (I := allI) (e := e0) (x := x)).mp this
    cases h2

end KoreAML.TieUnionTest

/-- info: 'KoreAML.TieUnion.text_entails_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieUnion.text_entails_alt
/-- info: 'KoreAML.TieUnion.text_entails_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieUnion.text_entails_none
/-- info: 'KoreAML.TieUnion.split_entails_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieUnion.split_entails_text
/-- info: 'KoreAML.TieUnionTest.two_elements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KoreAML.TieUnionTest.two_elements
