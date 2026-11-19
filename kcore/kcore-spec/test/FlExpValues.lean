/-
  The expectations (C7 form (a)) of the four function-law fixtures, each a value derived for every
  interpretation H from the premise set `TiePair.Pre (cH H) T`, where `T` is the text's function
  sentences as written (`trS`, the translation of the sentence; `shape`: each of Γ's equations is
  its sentence's translation, so `T` is Γ's equation items up to the indices of variables), Γ's
  rule items (none: no text here has a rule) and the families of the reading (`TiePair.Families`:
  the signature, the constructors, the domains with the registry hooks' graphs, the collections,
  the fallback). The law sentences are not among the premises and nothing is stated of them.
  Run from the package root: `lake env lean -j1 test/FlExpValues.lean`. Every statement is on the
  literal `defn` of `f2-examples/FIXTURE.kompile.kore`; nothing reads `Parse.parse` or `emit`.

  - `Assoc` (e2-fn-assoc, `rule pl(A, B) => A +Int B`): `pl_1_2`: `pl(1, 2) = 3`.
  - `Idem` (e2-fn-idem, `rule pm(A, B) => maxInt(A, B)`): `pm_1_2`: `pm(1, 2) = 2`.
  - `Unit` (e2-fn-assoc-unit, `rule zero => 0`, `rule pu(A, B) => A +Int B`): `pu_1_zero`:
    `pu(1, zero()) = 1`, from `zero() = 0` (`zero_0`) and `pu(1, 0) = 1` (`pu_1_0`): equality is a
    congruence of application in every model of definedness (`app2_congr_flx`).
  - `HookAssoc` (rdr-hook-assoc, `plus(Int, Int) [function, total, hook(INT.add), assoc]`):
    `plus_1_2`: `plus(1, 2) = 3`. `plus` has no equation: it is a parameter the registry's `INT.add`
    implements, and the value is Γ's graph of the parameter (`ParamSchema.gamma_param`, in `ΓDomains`), the
    hook's sum at two Ints (`paramVal_intHook`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FlExpValues

open KCore ML Faithful KoreAML

/-- The translation of an application of a symbol to two arguments is the head applied to the
translations of the two, whatever the head. -/
theorem symApp2_flx (c : Semantics) (f : Sym) (a : Kore.Pattern) :
    ∃ A : P, ∀ b : Kore.Pattern, KoreAML.den (symApp c f [a, b]) = A ⬝ KoreAML.den a ⬝ KoreAML.den b := by
  unfold symApp
  split
  · exact ⟨_, fun b => by unfold KoreAML.den; rw [TieFRRead.tr_app, trArgs_two]⟩
  · exact ⟨_, fun b => by unfold KoreAML.den; rw [TieFRRead.tr_app, trArgs_two]⟩

/-- A model of `TiePair.Pre c T` satisfies definedness. -/
theorem defOK_pre_flx {c : Semantics} {T : List P} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP TiePair.Pre c T) : DefOK I :=
  TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))

/-- **Equality is a congruence of application, at the second argument**, in every model of the
premises, which satisfy definedness. -/
theorem app2_congr_flx {c : Semantics} {T : List P} {A X Z V R : P}
    (h0 : TiePair.Pre c T ⊧ (Z ≡ V)) (h1 : TiePair.Pre c T ⊧ (A ⬝ X ⬝ V ≡ R)) :
    TiePair.Pre c T ⊧ (A ⬝ X ⬝ Z ≡ R) := by
  intro M _ I hI e m
  have hd := defOK_pre_flx hI
  rw [interp_equal hd]
  intro a
  rw [← (interp_equal hd).mp (h1 hI e m) a]
  exact interp_app_congr (fun _ => Iff.rfl) (fun b => (interp_equal hd).mp (h0 hI e m) b) a

/-! ## e2-fn-assoc -/

namespace Assoc

kore_term kore from "f2-examples/e2-fn-assoc.kompile.kore"
definition_of defn from "f2-examples/e2-fn-assoc.kompile.kore"
user_axioms U from "f2-examples/e2-fn-assoc.kompile.kore" module "E2-FN-ASSOC"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The text sentences of Γ's 28 equations, in `fnItems`'s order (`pl`'s, sentence 240, first). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax240, U.ax219, U.ax227, U.ax226, U.ax225, U.ax224, U.ax231, U.ax230, U.ax233, U.ax232,
   U.ax229, U.ax228, U.ax208, U.ax207, U.ax218, U.ax217, U.ax214, U.ax213, U.ax216, U.ax215,
   U.ax221, U.ax220, U.ax223, U.ax222, U.ax210, U.ax209, U.ax212, U.ax211]

/-- The function sentences as written. -/
noncomputable def writtenPats : List P := fnText.map (trS · |>.pat)

set_option maxHeartbeats 1000000 in
/-- **Each of Γ's equations is its sentence's translation** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) writtenPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) writtenPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The premises: the function sentences as written, Γ's rule items (none) and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) writtenPats

def pl : Sym := 384

theorem names : c.symName pl = "Lblpl" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn pl = some fn := rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hfnH (H : HookParams) : (cH H).lookupFn pl = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem hvs : c.sortsOf [int 1, int 2] = some fn.args := by decide +kernel
theorem hvsH (H : HookParams) : (cH H).sortsOf [int 1, int 2] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs

theorem eval_pl (H : HookParams) : Eval (cH H) pl [int 1, int 2] (some (int 3)) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn hvs (n := 10) (by decide +kernel)

/-- **`pl(1, 2) = 3`, derived from the sentences as written**, for every H. -/
theorem pl_1_2 (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) pl [int 1, int 2] ≡ den (cH H) (int 3)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_pl H) (hfnH H) (hvsH H)

end Assoc

/-! ## e2-fn-idem -/

namespace Idem

kore_term kore from "f2-examples/e2-fn-idem.kompile.kore"
definition_of defn from "f2-examples/e2-fn-idem.kompile.kore"
user_axioms U from "f2-examples/e2-fn-idem.kompile.kore" module "E2-FN-IDEM"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The text sentences of Γ's 28 equations, in `fnItems`'s order (`pm`'s, sentence 240, first). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax240, U.ax219, U.ax227, U.ax226, U.ax225, U.ax224, U.ax231, U.ax230, U.ax233, U.ax232,
   U.ax229, U.ax228, U.ax208, U.ax207, U.ax218, U.ax217, U.ax214, U.ax213, U.ax216, U.ax215,
   U.ax221, U.ax220, U.ax223, U.ax222, U.ax210, U.ax209, U.ax212, U.ax211]

/-- The function sentences as written. -/
noncomputable def writtenPats : List P := fnText.map (trS · |>.pat)

set_option maxHeartbeats 1000000 in
/-- **Each of Γ's equations is its sentence's translation** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) writtenPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) writtenPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The premises: the function sentences as written, Γ's rule items (none) and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) writtenPats

def pm : Sym := 384

theorem names : c.symName pm = "Lblpm" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn pm = some fn := rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hfnH (H : HookParams) : (cH H).lookupFn pm = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem hvs : c.sortsOf [int 1, int 2] = some fn.args := by decide +kernel
theorem hvsH (H : HookParams) : (cH H).sortsOf [int 1, int 2] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs

theorem eval_pm (H : HookParams) : Eval (cH H) pm [int 1, int 2] (some (int 2)) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn hvs (n := 10) (by decide +kernel)

/-- **`pm(1, 2) = 2`, derived from the sentences as written**, for every H. -/
theorem pm_1_2 (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) pm [int 1, int 2] ≡ den (cH H) (int 2)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_pm H) (hfnH H) (hvsH H)

end Idem

/-! ## e2-fn-assoc-unit -/

namespace Unit

kore_term kore from "f2-examples/e2-fn-assoc-unit.kompile.kore"
definition_of defn from "f2-examples/e2-fn-assoc-unit.kompile.kore"
user_axioms U from "f2-examples/e2-fn-assoc-unit.kompile.kore" module "E2-FN-ASSOC-UNIT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The text sentences of Γ's 29 equations, in `fnItems`'s order (`pu`'s, sentence 256, and
`zero`'s, sentence 259, first). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax256, U.ax259, U.ax222, U.ax230, U.ax229, U.ax228, U.ax227, U.ax234, U.ax233, U.ax236,
   U.ax235, U.ax232, U.ax231, U.ax211, U.ax210, U.ax221, U.ax220, U.ax217, U.ax216, U.ax219,
   U.ax218, U.ax224, U.ax223, U.ax226, U.ax225, U.ax213, U.ax212, U.ax215, U.ax214]

/-- The function sentences as written. -/
noncomputable def writtenPats : List P := fnText.map (trS · |>.pat)

set_option maxHeartbeats 1000000 in
/-- **Each of Γ's equations is its sentence's translation** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) writtenPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) writtenPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The premises: the function sentences as written, Γ's rule items (none) and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) writtenPats

def pu : Sym := 384
def zero : Sym := 385

theorem names : c.symName pu = "Lblpu" ∧ c.symName zero = "Lblzero" := by decide +kernel

noncomputable abbrev fnPu : Fn := c.fns[0]'(by decide +kernel)
noncomputable abbrev fnZero : Fn := c.fns[1]'(by decide +kernel)

theorem hfnPu : c.lookupFn pu = some fnPu := rfl
theorem hfnZero : c.lookupFn zero = some fnZero := rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hfnPuH (H : HookParams) : (cH H).lookupFn pu = some fnPu := by
  rw [Semantics.lookupFn_withHooks]; exact hfnPu
theorem hfnZeroH (H : HookParams) : (cH H).lookupFn zero = some fnZero := by
  rw [Semantics.lookupFn_withHooks]; exact hfnZero
theorem hvsPu : c.sortsOf [int 1, int 0] = some fnPu.args := by decide +kernel
theorem hvsZero : c.sortsOf [] = some fnZero.args := by decide +kernel
theorem hvsPuH (H : HookParams) : (cH H).sortsOf [int 1, int 0] = some fnPu.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvsPu
theorem hvsZeroH (H : HookParams) : (cH H).sortsOf [] = some fnZero.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvsZero

theorem eval_pu (H : HookParams) : Eval (cH H) pu [int 1, int 0] (some (int 1)) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfnPu hvsPu (n := 10) (by decide +kernel)

theorem eval_zero (H : HookParams) : Eval (cH H) zero [] (some (int 0)) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfnZero hvsZero (n := 10) (by decide +kernel)

/-- `zero() = 0`, derived from the sentences as written, for every H. -/
theorem zero_0 (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) zero [] ≡ den (cH H) (int 0)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_zero H) (hfnZeroH H) (hvsZeroH H)

/-- `pu(1, 0) = 1`, derived from the sentences as written, for every H. -/
theorem pu_1_0 (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) pu [int 1, int 0] ≡ den (cH H) (int 1)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_pu H) (hfnPuH H) (hvsPuH H)

/-- **`pu(1, zero()) = 1`, derived from the sentences as written**, for every H: the application
of `pu` to `1` and to the application `zero()`, as Γ writes applications. -/
theorem pu_1_zero (H : HookParams) :
    Pre H ⊧ (KoreAML.den (symApp (cH H) pu [(int 1).kore (cH H), symApp (cH H) zero []]) ≡ den (cH H) (int 1)) := by
  obtain ⟨A, hA⟩ := symApp2_flx (cH H) pu ((int 1).kore (cH H))
  have h0 : Pre H ⊧ (KoreAML.den (symApp (cH H) zero []) ≡ KoreAML.den ((int 0).kore (cH H))) := zero_0 H
  have h1 : Pre H ⊧ (A ⬝ KoreAML.den ((int 1).kore (cH H)) ⬝ KoreAML.den ((int 0).kore (cH H)) ≡ den (cH H) (int 1)) := by
    rw [← hA]; exact pu_1_0 H
  rw [hA]
  intro M _ I hI
  exact app2_congr_flx h0 h1 hI

end Unit

/-! ## rdr-hook-assoc -/

namespace HookAssoc

kore_term kore from "f2-examples/rdr-hook-assoc.kompile.kore"
definition_of defn from "f2-examples/rdr-hook-assoc.kompile.kore"
user_axioms U from "f2-examples/rdr-hook-assoc.kompile.kore" module "RDR-HOOK-ASSOC"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The text sentences of Γ's 27 equations (the sort predicates'; `plus` has none), in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax219, U.ax227, U.ax226, U.ax225, U.ax224, U.ax231, U.ax230, U.ax233, U.ax232, U.ax229,
   U.ax228, U.ax208, U.ax207, U.ax218, U.ax217, U.ax214, U.ax213, U.ax216, U.ax215, U.ax221,
   U.ax220, U.ax223, U.ax222, U.ax210, U.ax209, U.ax212, U.ax211]

/-- The function sentences as written. -/
noncomputable def writtenPats : List P := fnText.map (trS · |>.pat)

set_option maxHeartbeats 1000000 in
/-- **Each of Γ's equations is its sentence's translation** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) writtenPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) writtenPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The premises: the function sentences as written, Γ's rule items (none) and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) writtenPats

def plus : Sym := 384

theorem names : c.symName plus = "Lblplus" := by decide +kernel

/-- `plus` is a parameter of two Ints and result sort Int that the registry's `INT.add` implements. -/
theorem param : (c.lookupParam plus).any (fun k => k.impl == some intAdd && k.sig.result == Srt.int &&
    k.sig.args == [Srt.int, Srt.int] && k.sig.name == plus) = true := by decide +kernel

theorem anySome_flx {α : Type} {o : Option α} {p : α → Bool} (h : o.any p = true) : ∃ a, o = some a ∧ p a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- **`plus(1, 2) = 3`, derived from the premises**, for every H: Γ's graph of the parameter
(`gamma_param`, a family of the reading) at two Ints, where the hook's sum is 3. -/
theorem plus_1_2 (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) plus [int 1, int 2] ≡ den (cH H) (int 3)) := by
  obtain ⟨k, hk, hk'⟩ := anySome_flx param
  simp only [Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨⟨⟨hi, hres⟩, hargs⟩, hname⟩ := hk'
  have hkH : (cH H).lookupParam plus = some k := hk
  have hmem : k ∈ (cH H).params := by
    have h := hkH
    rw [Semantics.lookupParam_eq] at h; exact List.mem_of_find?_eq_some h
  have hvs : (cH H).sortsOf [int 1, int 2] = some k.sig.args := by
    rw [Semantics.sortsOf_withHooks _ _ noRaw, hargs]; decide +kernel
  have hpv : (cH H).paramVal plus [int 1, int 2] = some (int 3) :=
    paramVal_intHook hkH hi hres (by decide) (by decide +kernel)
  have hg := ParamSchema.gamma_param (cH H) hmem hvs
  rw [hname, hpv] at hg
  have hΓ : Γ (cH H) ⊧ (TiePair.app (cH H) plus [int 1, int 2] ≡ den (cH H) (int 3)) := by
    intro M _ I hI; exact hI _ hg
  intro M _ I hI
  exact TiePair.cut (shapeH H) hΓ hI

end HookAssoc

end KCore.FlExpValues

#check @KCore.FlExpValues.Assoc.pl_1_2
#check @KCore.FlExpValues.Idem.pm_1_2
#check @KCore.FlExpValues.Unit.pu_1_zero
#check @KCore.FlExpValues.HookAssoc.plus_1_2
#print axioms KCore.FlExpValues.Assoc.pl_1_2
#print axioms KCore.FlExpValues.Idem.pm_1_2
#print axioms KCore.FlExpValues.Unit.zero_0
#print axioms KCore.FlExpValues.Unit.pu_1_0
#print axioms KCore.FlExpValues.Unit.pu_1_zero
#print axioms KCore.FlExpValues.HookAssoc.plus_1_2
