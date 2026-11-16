/-
  The cut identity (KcoreSpec/CutIdentity.lean), each lemma at one interpretation: the value model
  `stdI c` of the reader's semantics for `f2-examples/ovlsub.kompile.kore`. Run from the package
  root: `lake env lean -j1 test/CutIdentity.lean`.

  The valuation `e0` gives y the sort element of Bool and every other element variable the value
  `true`. S is y, so S denotes Bool's element; φ is `⊤_S` (the elements of Bool); the contexts put
  the hole under an application beside S. Every hypothesis is discharged: definedness and
  `ceilDefItem` by the value model, the sorts by `isSort_iff`, `true` in Bool by `decide +kernel`.
-/
import KcoreSpec

set_option autoImplicit false

open KCore Faithful Model KoreAML ML

namespace CutIdentityTest

definition_of defn from "f2-examples/ovlsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def x : EVar := ⟨100⟩
def y : EVar := ⟨101⟩
def bTrue : Elem := .val (.dv Srt.bool (.bool true))
def σB : Elem := .srt Srt.bool
noncomputable def e0 : Valuation Elem := ⟨fun v => if v = y then σB else bTrue, fun _ _ => False⟩
def S : KoreAML.P := .evar y
def φ : KoreAML.P := inhOf S

theorem bool_facts : Srt.bool < nRegSorts + c.sortNames.length ∧
    c.sortOf (.dv Srt.bool (.bool true)) = some Srt.bool := by
  decide +kernel

theorem hS : ∀ a, S.interpret (stdI c) e0 a ↔ a = σB := fun a => by
  show a = e0.evalEvar y ↔ _
  simp [e0]

theorem hσ : IsSort (stdI c) σB := (isSort_iff _).mpr ⟨Srt.bool, List.mem_range.mpr bool_facts.1, rfl⟩

theorem hx : Inh (stdI c) σB (e0.evalEvar x) := by
  have : e0.evalEvar x = bTrue := by simp [e0, x, y]
  rw [this]
  exact (inh_srt Srt.bool bTrue).mpr bool_facts.2

theorem noRead_S : NoReadCut (stdI c) x S := fun e a m => by
  show m = Function.update e.evalEvar x a y ↔ m = e.evalEvar y
  rw [Function.update_noteq (by simp [x, y])]

theorem noRead_φ : NoReadCut (stdI c) x φ := fun e a m => by
  unfold φ
  rw [interp_inhOf, interp_inhOf]
  exact exists_congr fun σ => and_congr_left' (noRead_S e a σ)

theorem hφs : ∀ a, φ.interpret (stdI c) e0 a → Inh (stdI c) σB a := fun _ h => (interp_inhOf_of hS).mp h

/-- The hole under an application, S beside it on either side. -/
def C₁ : CutCtx := .fn .hole S
def C₂ : CutCtx := .arg S .hole
theorem fresh₁ : C₁.Fresh (stdI c) x := ⟨trivial, noRead_S⟩
theorem fresh₂ : C₂.Fresh (stdI c) x := ⟨noRead_S, trivial⟩

example (m : Elem) := cut_sem x φ C₁ fresh₁ e0 m
example (m : Elem) := cut_sem x φ C₂ fresh₂ e0 m
example (m : Elem) := cut_identity defOK_std x φ noRead_φ C₁ fresh₁ e0 m
example (m : Elem) := cut_sorted defOK_std sat_ceilDef x φ S S noRead_φ noRead_S noRead_S .hole trivial e0
  hS hS hσ hσ hφs hφs m
example := cut_sorted_only_if defOK_std sat_ceilDef x φ S S noRead_S noRead_S e0 hS hS hσ hσ
  (fun m => cut_sorted defOK_std sat_ceilDef x φ S S noRead_φ noRead_S noRead_S .hole trivial e0
    hS hS hσ hσ hφs hφs m)
example (m : Elem) := mem_and defOK_std sat_ceilDef hS hS hσ hσ x hx φ S m
example (m : Elem) := mem_or defOK_std sat_ceilDef hS hS hσ hσ x hx φ S m
example (m : Elem) := mem_not defOK_std sat_ceilDef hS hS hσ hσ x hx φ m

/-- info: 'KoreAML.cut_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cut_sorted

/-! ### `tr` of a nested KORE application context

`<k>(kseq(inj{Int,KItem}(\dv{Int}("1")), kseq(inj{Bool,KItem}(HOLE), dotk())))`: four layers, an
injection at the hole, an argument before the hole and one after it. The context `kctx` has the
variable table of the filled pattern and the aliases ovlsub's text declares. -/

abbrev sB : Kore.KSort := .ctor ⟨⟨"SortBool"⟩⟩ []
abbrev sI : Kore.KSort := .ctor ⟨⟨"SortInt"⟩⟩ []
abbrev sKI : Kore.KSort := .ctor ⟨⟨"SortKItem"⟩⟩ []
def one : Kore.Pattern := .app ⟨⟨"inj"⟩⟩ [sI, sKI] [.dv sI "1"]
def dotk : Kore.Pattern := .app ⟨⟨"dotk"⟩⟩ [] []
def K : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"kseq"⟩⟩ [] [one]
      (.app ⟨⟨"kseq"⟩⟩ [] [] (.app ⟨⟨"inj"⟩⟩ [sB, sKI] [] .hole []) [dotk]) []) []
def φK : Kore.Pattern := .dv sB "true"
def kctx : Ctx :=
  { vars := tableOf [] (K.fill φK), aliases := ["weakExistsFinally", "weakAlwaysFinally", "allPathGlobally"] }

theorem K_noAlias : K.noAlias kctx = true := by decide +kernel

theorem tr_K : tr kctx (K.fill φK) = (K.toCut kctx).fill (tr kctx φK) := tr_cutCtx kctx φK K K_noAlias

theorem one_ground : KGround one :=
  .app (by simp) (fun p hp => by simp at hp; subst hp; exact .dv)
theorem dotk_ground : KGround dotk := .app (by simp) (by simp)

theorem head_noRead (h : Kore.SymbolIdent) (ss : List Kore.KSort) (pre : List Kore.Pattern)
    (hs : ∀ s ∈ ss, ∃ C, s = .ctor C []) (hp : ∀ p ∈ pre, KGround p) :
    NoReadCut (stdI c) x (trArgs kctx (trSortApp kctx.vars (sym (.symbol h.ident.name)) ss) pre) :=
  NoReadCut.of_closed (trArgs_closed (trSortApp_closed (Closed.sym _) hs)
    (fun p hp' => (hp p hp').closed kctx)) x

theorem K_sides : K.SidesNoRead (stdI c) kctx x :=
  ⟨head_noRead _ _ _ (by simp) (by simp),
   by simp,
   head_noRead _ _ _ (by simp) (by simp [one_ground]),
   by simp,
   head_noRead _ _ _ (by simp) (by simp),
   by simpa using NoReadCut.of_closed (dotk_ground.closed kctx) x,
   head_noRead _ _ _ (by simp) (by simp),
   by simp,
   trivial⟩

/-- `cut_sem` at the translation of the filled context. -/
example (m : Elem) : (tr kctx (K.fill φK)).interpret (stdI c) e0 m ↔
    ∃ a, (tr kctx φK).interpret (stdI c) e0 a ∧
      ((K.toCut kctx).fill (.evar x)).interpret (stdI c) ⟨Function.update e0.evalEvar x a, e0.evalSvar⟩ m := by
  rw [tr_K]; exact cut_sem x _ _ (KoreCutCtx.toCut_fresh K K_sides) e0 m

/-- `cut_identity` at the translation of the filled context. -/
example (m : Elem) :
    (∃∃ x ((K.toCut kctx).fill (.evar x) ⋀ ⌈(Pattern.evar x : KoreAML.P) ⋀ tr kctx φK⌉)).interpret (stdI c) e0 m ↔
      (tr kctx (K.fill φK)).interpret (stdI c) e0 m := by
  rw [tr_K]
  exact cut_identity defOK_std x _ (NoReadCut.of_closed (KGround.dv.closed kctx) x) _
    (KoreCutCtx.toCut_fresh K K_sides) e0 m

/-- info: 'KoreAML.tr_cutCtx' depends on axioms: [propext] -/
#guard_msgs in #print axioms tr_cutCtx

end CutIdentityTest
