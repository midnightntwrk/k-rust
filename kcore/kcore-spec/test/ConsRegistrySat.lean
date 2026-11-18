/-
  The registry family in the extension of a model of the theory without it
  (KcoreSpec/ConsRegistrySat.lean): the statements exist as stated and depend on no axiom but
  `propext`, `Classical.choice` and `Quot.sound`. Run from the package root:
  `lake env lean test/ConsRegistrySat.lean`.
-/
import KcoreSpec.ConsRegistrySat

open KCore KCore.Cons ML Faithful

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hm : Model.HypModelCore c) (hV : ValElems c D I)
    (hax : ∀ k ∈ builtinColls, D (.sort ("Sort" ++ c.sortName k.sort)) → collAxioms c k = [])
    (hnj : ∀ k ∈ builtinColls, k.sort < nRegSorts → D (.sort ("Sort" ++ c.sortName k.sort)) →
      extModel c D I ⊧ᴵ collNoJunk c k)
    {φ : KoreAML.P} (h : RegistryItem c D φ) : extModel c D I ⊧ᴵ φ :=
  sat_registry_of hm hV hax hnj h

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hm : Model.HypModelCore c) {s : Srt} {lit : Lit} (hv : c.sortOf (.dv s lit) = some s)
    (hs : DSort c D s) (e : Valuation (Ext M)) (x : Ext M) :
    (den c (.dv s lit)).interpret (extModel c D I) e x ↔ x = .inr (.val (.dv s lit)) :=
  ext_den_dvDet hm hv hs e x

#check @sat_registry_decided
#check @valElems_of_decided
#check @sat_registry_arity
#check @sat_registry_graph
#check @sat_registry_fallback
#check @sat_registry_value
#check @sat_registry_distinct

#print axioms sat_registry_of
#print axioms sat_registry_decided
#print axioms valElems_of_decided
#print axioms ext_den_dvDet

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    (hm : Model.HypModelCore c) (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hra : (∀ p ∈ c.params, p.raw = false) ∨ DetachedB.kOK c ss ks kEq = true) {φ : KoreAML.P} (h : RegistryItem c (DetachedB.names c ss ks) φ) :
    extModel c (DetachedB.names c ss ks) I ⊧ᴵ φ :=
  sat_registry hd hI hm hg htr hra h

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    (hm : Model.HypModelCore c) (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hra : (∀ p ∈ c.params, p.raw = false) ∨ DetachedB.kOK c ss ks kEq = true) {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (e : Valuation (Ext M)) (x : Ext M) :
    (den c v).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔ ElemOf c (DetachedB.names c ss ks) I v x :=
  den_val_rs hd hI hm hg htr hra v hv e x

example {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
    {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hs : DSort c (DetachedB.names c ss ks) s) :
    (∃ lit, v = .dv s lit) ∨
      (s = Srt.rangeMap ∧ c.collOf s = some (builtinColl .rangeMap) ∧ ∃ es, v = .map s es ∧
        rangesOK es = true ∧ ∀ e ∈ es, c.sortOf e.1 = some Srt.range ∧ c.sortOf e.2 = some Srt.kitem) :=
  detVal_shape_rs hd hv hs

/-- info: 'KCore.Cons.sat_registry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_registry
/-- info: 'KCore.Cons.valElems_decided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms valElems_decided
/-- info: 'KCore.Cons.noJunk_rm_rs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noJunk_rm_rs
