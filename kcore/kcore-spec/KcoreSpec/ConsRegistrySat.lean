/-
  The extension of a model (`extModel`, ConsExtModel.lean) satisfies the registry family
  (`RegistryItem`, RegistryOwn.lean). Here: the sort constant of a detached sort
  (`sat_registry_sortConst`), the first of the family's seven kinds.
-/
import KcoreSpec.ConsTransfer

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful

variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The sort constant of a detached sort holds in the extension**: the sort's name denotes one
element, the added one, and it is a sort. -/
theorem sat_registry_sortConst {s : Srt} (hs : D (.sort ("Sort" ++ c.sortName s))) :
    extModel c D I ⊧ᴵ (KoreAML.sortConstantItem (sortDeclOf c s)).pat := by
  intro e' pt
  show (KoreAML.sExists ⟨1⟩ (KoreAML.sym .sortSort)
    (KoreAML.sym (.sort ("Sort" ++ c.sortName s)) ≡ .evar ⟨1⟩)).interpret (extModel c D I) e' pt
  rw [interp_sExists' (ext_defOK c D I)]
  refine ⟨.inr (.srt ("Sort" ++ c.sortName s)), ⟨.inr .inh, .inr .sorts, rfl, rfl, _, hs, rfl⟩, ?_⟩
  rw [KoreAML.interp_equal (ext_defOK c D I)]
  intro a
  rw [KoreAML.interp_evar]
  show (extModel c D I).evalSymb (.sort ("Sort" ++ c.sortName s)) a ↔
    a = Function.update e'.evalEvar ⟨1⟩ (.inr (.srt ("Sort" ++ c.sortName s))) ⟨1⟩
  rw [Function.update_same]
  exact ext_sortName c D I hs a

end KCore.Cons
