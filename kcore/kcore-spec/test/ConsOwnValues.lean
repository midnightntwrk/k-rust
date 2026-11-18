/-
  The values of the sorts outside the detached names, in a model of the theory without them
  (KcoreSpec/ConsOwnValues.lean): the statements exist as stated and depend on no axiom but
  `propext`, `Classical.choice` and `Quot.sound`. Run from the package root:
  `lake env lean test/ConsOwnValues.lean`.
-/
import KcoreSpec.ConsOwnValues

open KCore KCore.Cons ML Faithful

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) (hs : DetachedB.sOK c ss ks s = true) (e : Valuation M) :
    ∃ a, (∀ m, (den c v).interpret I e m ↔ m = a) ∧ (KoreAML.inhOf (sortP (c.sortName s))).interpret I e a :=
  own_single hd hI hv hs e

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {v w : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) (hs : DetachedB.sOK c ss ks s = true) (e : Valuation M)
    (h : ∀ m, (den c v).interpret I e m ↔ (den c w).interpret I e m) : v = w :=
  own_apart hd hI hg htr hv hw hs e h

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    ∃ x, ElemOf c (DetachedB.names c ss ks) I v x :=
  elemOf_total hd hI hv

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {v w : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) {x : Ext M} (h1 : ElemOf c (DetachedB.names c ss ks) I v x)
    (h2 : ElemOf c (DetachedB.names c ss ks) I w x) : v = w :=
  elemOf_inj hd hI hg htr hv hw h1 h2

/-- info: 'KCore.Cons.own_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.own_single
/-- info: 'KCore.Cons.own_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.own_apart
/-- info: 'KCore.Cons.elemOf_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.elemOf_total
/-- info: 'KCore.Cons.elemOf_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.elemOf_inj

/-- Where `_==K_` is none of the names, its graph at values of K holds in the model, and distinct
values of a sort outside the names are distinct elements whatever the parameters are. -/
example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    (hk : DetachedB.kOK c ss ks kEq = true) {u u' : GroundTerm} (hu : c.sortOf u = some Srt.k)
    (hu' : c.sortOf u' = some Srt.k) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c kEq (GroundTerm.koreList c [u, u']))).interpret I e m ↔
      (den c (bool (GroundTerm.cmp u u' == .eq))).interpret I e m :=
  eqK_den_own hd hI hk hu hu' e m

/-- info: 'KCore.Cons.values_apart_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.values_apart_own

/-- Distinct values of KItem or of a sort below KItem are distinct elements by Map's distinctness,
with Map among the sorts outside the names, which the decided check gives. -/
example {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {O : Srt → Prop}
    (hI : OwnVals c I O) [OvlOK c] (hg : genWf c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hOm : O Srt.map) {s : Srt} (hs : s = Srt.kitem ∨ s ∈ c.sortsBelowKItem) (hO : O s)
    {v w : GroundTerm} (hv : c.sortOf v = some s) (hw : c.sortOf w = some s)
    (he : elemOf c I v = elemOf c I w) : v = w :=
  map_apart_own hI hg htr hOm hs hO hv hw he

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true) :
    DetachedB.sOK c ss ks Srt.map = true :=
  map_sOK_of_decided hd

/-- info: 'KCore.Cons.map_apart_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Cons.map_apart_own
