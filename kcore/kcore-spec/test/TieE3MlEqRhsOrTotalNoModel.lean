/-
  Fixture e3-ml-eq-rhs-or-total (`test/constructs/fixtures/e3-ml-eq-rhs-or-total`): `rule f(X) => X`,
  `rule g(X) => 0 -Int X`, `rule h(X) => f(X) #Or g(X)`, f, g and h `[function, total]` over Int. The text
  is `f2-examples/mleqort.kompile.kore`; sentence numbers are `AxiomDecl.index`: 207 is h's equation
  `h(X0) = f(X) ∨ g(X)` (with `X0 ∈ X`), 80 h's functional sentence `∃Val. Val = h(K0)`, 203 f's
  equation `f(X0) = X`, 205 g's `g(X0) = 0 -Int X`. Run from the package root:
  `lake env lean -j1 test/TieE3MlEqRhsOrTotalNoModel.lean`. Every statement is on the literals `kore`
  and `defn`, for every interpretation H.

  - The text has no model (C7 form (r), `no_model`): the premise set `Pre H` is the four sentences as
    the text writes them, with the signature and the domains of the reading (`ΓSig`: definedness and
    the sorts; `ΓDomains`: each Int value one element of Int, the graph of `_-Int_` at `[0, 1]`,
    distinct Int values distinct elements). Read at X0 = X = 1 (`valAt`, `eqn_read`): f(1) is 1 (203),
    g(1) is the value of `0 -Int 1`, which the graph makes -1 (205); 207 puts both in h(1); 80 makes
    h(1) one element of Int (`fnl_read`); and 1 and -1 are distinct elements. No other item of Γ is
    used.
  - The reading has no model either (`gamma_no_model`, `inconsistent`): Γ's clauses of h
    (`orAsCases`: h(X) = f(X) where f(X) is defined, h(X) = g(X) where g(X) is) both apply at 1, so
    h(1) is the element of f(1) and that of g(1), 1 and -1 (`eqn_readG` on Γ's items, `gAx`).
-/
import KcoreSpec
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace KCore.TieE3MlEqRhsOrTotalNoModel
open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/mleqort.kompile.kore"
definition_of defn from "f2-examples/mleqort.kompile.kore"
user_axioms U from "f2-examples/mleqort.kompile.kore" module "E3-ML-EQ-RHS-OR-TOTAL"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

def sI : Kore.KSort := srt "Int"
def vX0 : Kore.Pattern := ev "X0" sI
def vX : Kore.Pattern := ev "VarX" sI
def kX0 : VarKey := .evar "X0" sI
def kX : VarKey := .evar "VarX" sI
/-- The premise every equation of the text writes: `\top ∧ (X0 ∈ VarX ∧ \top)`. -/
def premP : Kore.Pattern := .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in sI KoreAML.R vX0 vX, .top KoreAML.R]]
/-- An equation `prem → F(X0) = rhs ∧ \top` over Int. -/
def eqnP (f : String) (rhs : Kore.Pattern) : Kore.Pattern :=
  .implies KoreAML.R premP (.equals sI KoreAML.R (ap f [vX0]) (.and sI [rhs, .top sI]))

theorem s203 : U.ax203.ax.pattern = eqnP "Lblf" vX := by decide +kernel
theorem s205 : U.ax205.ax.pattern = eqnP "Lblg" (ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vX]) := by decide +kernel
theorem s207 : U.ax207.ax.pattern = eqnP "Lblh" (.or sI [ap "Lblf" [vX], ap "Lblg" [vX]]) := by decide +kernel
theorem s80 : U.ax80.ax.pattern = .exist KoreAML.R (evar "Val" sI) (.equals sI KoreAML.R (ev "Val" sI) (ap "Lblh" [ev "K0" sI])) := by
  decide +kernel
theorem sv : U.ax80.ax.sortVars = [KoreAML.Rv] ∧ U.ax203.ax.sortVars = [KoreAML.Rv] ∧ U.ax205.ax.sortVars = [KoreAML.Rv] ∧
    U.ax207.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem trS_plain : (trS U.ax80).pat = (trAxiom [] [] U.ax80).pat ∧ (trS U.ax203).pat = (trAxiom [] [] U.ax203).pat ∧
    (trS U.ax205).pat = (trAxiom [] [] U.ax205).pat ∧ (trS U.ax207).pat = (trAxiom [] [] U.ax207).pat := by decide +kernel

theorem free_eqn : (U.ax203.ax.sortVars.map sortVarKey ++ freeOf [] U.ax203.ax.pattern).eraseDups = [.sortVar "R", kX0, kX] ∧
    (U.ax205.ax.sortVars.map sortVarKey ++ freeOf [] U.ax205.ax.pattern).eraseDups = [.sortVar "R", kX0, kX] ∧
    (U.ax207.ax.sortVars.map sortVarKey ++ freeOf [] U.ax207.ax.pattern).eraseDups = [.sortVar "R", kX0, kX] := by
  decide +kernel
/-- The table's numbering: the sort variable R is 1, X0 is 2, VarX is 3. -/
def TabOK (t : VarTable) : Prop := t.ev (.sortVar "R") = ⟨1⟩ ∧ t.ev kX0 = ⟨2⟩ ∧ t.ev kX = ⟨3⟩
theorem tab_eqn : TabOK (tableOf U.ax203.ax.sortVars U.ax203.ax.pattern) ∧
    TabOK (tableOf U.ax205.ax.sortVars U.ax205.ax.pattern) ∧ TabOK (tableOf U.ax207.ax.sortVars U.ax207.ax.pattern) := by
  unfold TabOK; decide +kernel

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The valuation the refutation reads the sentences at: the sort variable R (variable 1) is Int,
every other element variable the element m1. -/
def valAt (σI m1 : M) : Valuation M := ⟨Function.update (fun _ => m1) ⟨1⟩ σI, KoreAML.val0.evalSvar⟩

theorem valAt_1 (σI m1 : M) : (valAt σI m1).evalEvar ⟨1⟩ = σI := by
  simp [valAt]
theorem valAt_ne (σI m1 : M) {x : EVar} (h : x ≠ ⟨1⟩) : (valAt σI m1).evalEvar x = m1 := by
  simp [valAt, Function.update_noteq h]

/-- **An equation of the text read at `valAt`**: where X0 and VarX are the element m1 of Int, the
sentence `prem → f(X0) = rhs ∧ \top` makes `f(X0)` and `rhs` agree on Int. -/
theorem eqn_read (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M}
    (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI2 : IsSort I σI) {ad : AxiomDecl} {f : String}
    {rhs : Kore.Pattern} (hp : ad.ax.pattern = eqnP f rhs)
    (hfree : (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups = [.sortVar "R", kX0, kX])
    (htab : TabOK (tableOf ad.ax.sortVars ad.ax.pattern))
    (hT : I ⊧ᴵ (trAxiom [] [] ad).pat) (m1 : M) (hm1 : Inh I σI m1) (b : M) (hb : Inh I σI b) :
    ((sym (.symbol f) ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b ↔
      (tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, []⟩ rhs).interpret I (valAt σI m1) b) := by
  have h := hT (valAt σI m1) m1
  unfold trAxiom at h
  dsimp only at h
  rw [hfree] at h
  generalize ht : tableOf ad.ax.sortVars ad.ax.pattern = t at h htab ⊢
  obtain ⟨h1, h2, h3⟩ := htab
  rw [hp] at h
  rw [interpret_impl] at h
  have hS : ∀ b, (trSort t sI).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h2v : (valAt σI m1).evalEvar (t.ev kX0) = m1 := by rw [h2]; exact valAt_ne σI m1 (by decide)
  have h3v : (valAt σI m1).evalEvar (t.ev kX) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hg : (conjList ([VarKey.sortVar "R", kX0, kX].map (guardOf t))).interpret I (valAt σI m1) m1 := by
    simp only [List.map, conjList, interpret_conj]
    refine ⟨(interp_guard_sortVar hD).mpr (by rw [h1, valAt_1]; exact hσI2), ?_, ?_⟩
    · exact (interp_guard_evar hD).mpr (by rw [show (VarKey.evar "X0" sI) = kX0 from rfl, h2v]; exact (interp_inhOf_of hS).mpr hm1)
    · exact (interp_guard_evar hD).mpr (by rw [show (VarKey.evar "VarX" sI) = kX from rfl, h3v]; exact (interp_inhOf_of hS).mpr hm1)
  have h4 := (interp_equal hD).mp (h hg) m1
  unfold eqnP at h4
  simp only [sortOf] at h4
  have h5 := h4.mpr ((interp_inhOf_of hRv).mpr hm1)
  rw [KoreAML.tr, interp_sImp] at h5
  have hprem : (tr ⟨t, []⟩ premP).interpret I (valAt σI m1) m1 := by
    have hvx0 : tr ⟨t, []⟩ vX0 = .evar (t.ev kX0) := rfl
    have hvx : tr ⟨t, []⟩ vX = .evar (t.ev kX) := rfl
    have htop : (tr ⟨t, []⟩ (.top KoreAML.R)).interpret I (valAt σI m1) m1 := by
      rw [KoreAML.tr, interp_sTop hD (by rw [trSort_R, h1]; rfl), interp_inhOf_of hRv]; exact hm1
    unfold premP
    rw [interp_and (List.cons_ne_nil _ _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨htop, ?_⟩
    rw [interp_and (List.cons_ne_nil _ _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, htop⟩
    rw [KoreAML.tr, hvx0, hvx]
    exact (interp_sIn_evar_svin hD hc hS hRv hσI2 hσI2 (by rw [h2v]; exact hm1) m1).mpr ⟨h2v.trans h3v.symm, hm1⟩
  have h6 := h5.2 hprem
  rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hσI2] at h6
  have h7 := h6.2 b hb
  have hF : tr ⟨t, []⟩ (ap f [vX0]) = sym (.symbol f) ⬝ .evar ⟨2⟩ := by
    unfold ap vX0 ev; rw [tr_app0, trArgs_cons, trArgs_nil, KoreAML.tr]; rw [show evarKey (evar "X0" sI) = kX0 from rfl, h2]
  rw [hF, interp_and (List.cons_ne_nil _ _)] at h7
  rw [h7]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [KoreAML.tr, interp_sTop hD (by unfold sI; rw [trSort_srt]; rfl), interp_inhOf_of hS]
  exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩

/-- The premise `\top ∧ (X0 ∈ V ∧ \top)` with the variable V named n. -/
def premPn (n : String) : Kore.Pattern :=
  .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in sI KoreAML.R vX0 (ev n sI), .top KoreAML.R]]

/-- The table's numbering with the second variable named n. -/
def TabOKn (n : String) (t : VarTable) : Prop := t.ev (.sortVar "R") = ⟨1⟩ ∧ t.ev kX0 = ⟨2⟩ ∧ t.ev (.evar n sI) = ⟨3⟩

/-- `premPn n` holds at `valAt` and m1. -/
theorem premPn_at (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M}
    (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI2 : IsSort I σI) (n : String) {t : VarTable}
    (htab : TabOKn n t) (m1 : M) (hm1 : Inh I σI m1) : (tr ⟨t, []⟩ (premPn n)).interpret I (valAt σI m1) m1 := by
  obtain ⟨h1, h2, h3⟩ := htab
  have hS : ∀ b, (trSort t sI).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h2v : (valAt σI m1).evalEvar (t.ev kX0) = m1 := by rw [h2]; exact valAt_ne σI m1 (by decide)
  have h3v : (valAt σI m1).evalEvar (t.ev (.evar n sI)) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hvx0 : tr ⟨t, []⟩ vX0 = .evar (t.ev kX0) := rfl
  have hvx : tr ⟨t, []⟩ (ev n sI) = .evar (t.ev (.evar n sI)) := rfl
  have htop : (tr ⟨t, []⟩ (.top KoreAML.R)).interpret I (valAt σI m1) m1 := by
    rw [KoreAML.tr, interp_sTop hD (by rw [trSort_R, h1]; rfl), interp_inhOf_of hRv]; exact hm1
  unfold premPn
  rw [interp_and (List.cons_ne_nil _ _)]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨htop, ?_⟩
  rw [interp_and (List.cons_ne_nil _ _)]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, htop⟩
  rw [KoreAML.tr, hvx0, hvx]
  exact (interp_sIn_evar_svin hD hc hS hRv hσI2 hσI2 (by rw [h2v]; exact hm1) m1).mpr ⟨h2v.trans h3v.symm, hm1⟩

/-- **An equation `prem → f(X0) = rhs ∧ \top` read at `valAt`**, its second variable named n,
where its premise holds there. -/
theorem eqn_readG (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M}
    (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI2 : IsSort I σI) (n : String) {ad : Kore.Axiom} {f : String}
    {prem rhs : Kore.Pattern}
    (hp : ad.pattern = .implies KoreAML.R prem (.equals sI KoreAML.R (ap f [vX0]) (.and sI [rhs, .top sI])))
    (hfree : (ad.sortVars.map sortVarKey ++ freeOf [] ad.pattern).eraseDups = [.sortVar "R", kX0, .evar n sI])
    (htab : TabOKn n (tableOf ad.sortVars ad.pattern))
    (hT : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ad⟩).pat) (m1 : M) (hm1 : Inh I σI m1)
    (hprem : (tr ⟨tableOf ad.sortVars ad.pattern, []⟩ prem).interpret I (valAt σI m1) m1) (b : M) (hb : Inh I σI b) :
    ((sym (.symbol f) ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b ↔
      (tr ⟨tableOf ad.sortVars ad.pattern, []⟩ rhs).interpret I (valAt σI m1) b) := by
  have h := hT (valAt σI m1) m1
  unfold trAxiom at h
  dsimp only at h
  rw [hfree] at h
  generalize ht : tableOf ad.sortVars ad.pattern = t at h htab hprem ⊢
  obtain ⟨h1, h2, h3⟩ := htab
  rw [hp] at h
  rw [interpret_impl] at h
  have hS : ∀ b, (trSort t sI).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h2v : (valAt σI m1).evalEvar (t.ev kX0) = m1 := by rw [h2]; exact valAt_ne σI m1 (by decide)
  have h3v : (valAt σI m1).evalEvar (t.ev (.evar n sI)) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hg : (conjList ([VarKey.sortVar "R", kX0, .evar n sI].map (guardOf t))).interpret I (valAt σI m1) m1 := by
    simp only [List.map, conjList, interpret_conj]
    refine ⟨(interp_guard_sortVar hD).mpr (by rw [h1, valAt_1]; exact hσI2), ?_, ?_⟩
    · exact (interp_guard_evar hD).mpr (by rw [show (VarKey.evar "X0" sI) = kX0 from rfl, h2v]; exact (interp_inhOf_of hS).mpr hm1)
    · exact (interp_guard_evar hD).mpr (by rw [h3v]; exact (interp_inhOf_of hS).mpr hm1)
  have h4 := (interp_equal hD).mp (h hg) m1
  simp only [sortOf] at h4
  have h5 := h4.mpr ((interp_inhOf_of hRv).mpr hm1)
  rw [KoreAML.tr, interp_sImp] at h5
  have h6 := h5.2 hprem
  rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hσI2] at h6
  have h7 := h6.2 b hb
  have hF : tr ⟨t, []⟩ (ap f [vX0]) = sym (.symbol f) ⬝ .evar ⟨2⟩ := by
    unfold ap vX0 ev; rw [tr_app0, trArgs_cons, trArgs_nil, KoreAML.tr]; rw [show evarKey (evar "X0" sI) = kX0 from rfl, h2]
  rw [hF, interp_and (List.cons_ne_nil _ _)] at h7
  rw [h7]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [KoreAML.tr, interp_sTop hD (by unfold sI; rw [trSort_srt]; rfl), interp_inhOf_of hS]
  exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩

theorem free80 : (U.ax80.ax.sortVars.map sortVarKey ++ freeOf [] U.ax80.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K0" sI] := by decide +kernel
theorem tab80 : (tableOf U.ax80.ax.sortVars U.ax80.ax.pattern).ev (.sortVar "R") = ⟨1⟩ ∧
    (tableOf U.ax80.ax.sortVars U.ax80.ax.pattern).ev (.evar "Val" sI) = ⟨2⟩ ∧
    (tableOf U.ax80.ax.sortVars U.ax80.ax.pattern).ev (.evar "K0" sI) = ⟨3⟩ := by decide +kernel

/-- **h's functional sentence (80) read at `valAt`**: `h(m1)` is one element of Int. -/
theorem fnl_read (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σI : M}
    (hσI1 : ∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) (hσI2 : IsSort I σI)
    (hT : I ⊧ᴵ (trAxiom [] [] U.ax80).pat) (m1 : M) (hm1 : Inh I σI m1) :
    ∃ y, ∀ b, Inh I σI b → ((sym (.symbol "Lblh") ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b ↔ b = y) := by
  have h := hT (valAt σI m1) m1
  unfold trAxiom at h
  dsimp only at h
  rw [free80] at h
  generalize ht : tableOf U.ax80.ax.sortVars U.ax80.ax.pattern = t at h
  have htab := tab80
  rw [ht] at htab
  obtain ⟨h1, h2, h3⟩ := htab
  rw [s80] at h
  rw [interpret_impl] at h
  have hS : ∀ (e : Valuation M) b, (trSort t sI).interpret I e b ↔ b = σI := fun _ b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h3v : (valAt σI m1).evalEvar (t.ev (.evar "K0" sI)) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hg : (conjList ([VarKey.sortVar "R", .evar "K0" sI].map (guardOf t))).interpret I (valAt σI m1) m1 := by
    simp only [List.map, conjList, interpret_conj]
    refine ⟨(interp_guard_sortVar hD).mpr (by rw [h1, valAt_1]; exact hσI2), ?_⟩
    exact (interp_guard_evar hD).mpr (by rw [h3v]; exact (interp_inhOf_of (hS _)).mpr hm1)
  have h4 := (interp_equal hD).mp (h hg) m1
  simp only [sortOf] at h4
  have h5 := h4.mpr ((interp_inhOf_of hRv).mpr hm1)
  rw [KoreAML.tr, interp_sExists] at h5
  obtain ⟨y, -, h6⟩ := h5
  rw [show evarKey (evar "Val" sI) = VarKey.evar "Val" sI from rfl, h2] at h6
  generalize he' : (⟨Function.update (valAt σI m1).evalEvar ⟨2⟩ y, (valAt σI m1).evalSvar⟩ : Valuation M) = e' at h6
  have he'1 : e'.evalEvar ⟨1⟩ = σI := by
    rw [← he']; dsimp only; rw [Function.update_noteq (by decide), valAt_1]
  have he'2 : e'.evalEvar ⟨2⟩ = y := by
    rw [← he']; dsimp only; rw [Function.update_same]
  have he'3 : e'.evalEvar ⟨3⟩ = m1 := by
    rw [← he']; dsimp only; rw [Function.update_noteq (by decide), valAt_ne σI m1 (by decide)]
  have hR' : ∀ b, (trSort t KoreAML.R).interpret I e' b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, he'1]
  rw [KoreAML.tr, interp_sEquals hD hc (hS e') hR' hσI2 hσI2] at h6
  refine ⟨y, fun b hb => ?_⟩
  have h7 := h6.2 b hb
  have hv : tr ⟨t, []⟩ (ev "Val" sI) = .evar ⟨2⟩ := by unfold ev; rw [KoreAML.tr, show evarKey (evar "Val" sI) = VarKey.evar "Val" sI from rfl, h2]
  have hF : tr ⟨t, []⟩ (ap "Lblh" [ev "K0" sI]) = sym (.symbol "Lblh") ⬝ .evar ⟨3⟩ := by
    unfold ap ev; rw [tr_app0, trArgs_cons, trArgs_nil, KoreAML.tr, show evarKey (evar "K0" sI) = VarKey.evar "K0" sI from rfl, h3]
  rw [hv, hF, interp_evar, he'2] at h7
  refine (interp_app_congr (e := valAt σI m1) (e' := e') (φ := sym (.symbol "Lblh")) (φ' := sym (.symbol "Lblh"))
    (ψ := .evar ⟨2⟩) (ψ' := .evar ⟨3⟩) (fun _ => Iff.rfl) (fun m => ?_) b).trans h7.symm
  rw [interp_evar, interp_evar, he'3, valAt_ne σI m1 (by decide)]
end

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_distinct (H : HookParams) : (distinctSorts (cH H)).contains Srt.int = true := by
  unfold distinctSorts
  exact List.contains_iff_mem.mpr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_cons_self ..)))))

/-- **The premises the refutation uses**: sentences 207 (`h(X) = f(X) ∨ g(X)`), 80 (h is
functional), 203 (`f(X) = X`) and 205 (`g(X) = 0 -Int X`) as the text writes them, with the
signature and the domains of the reading (the graph of `_-Int_` at `[0, 1]`, each Int value one
element of Int, distinct Int values distinct elements), for every H. No other item of Γ. -/
noncomputable def Pre (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts [(trS U.ax207).pat, (trS U.ax80).pat, (trS U.ax203).pat, (trS U.ax205).pat] ∪ ΓSig (cH H) ∪ ΓDomains (cH H)

/-- **The text's sentences have no model, for every H** (C7 form (r)): at X = 1, f(1) is 1 (203)
and g(1) is `0 -Int 1`, which the graph of `_-Int_` makes -1 (205); 207 puts both in h(1), and 80
makes h(1) one element of Int; the values 1 and -1 of Int are distinct elements. -/
theorem no_model (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Pre H := by
  rintro ⟨M, _, I, hI⟩
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inl (Or.inr hφ))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  have hT : ∀ φ ∈ [(trS U.ax207).pat, (trS U.ax80).pat, (trS U.ax203).pat, (trS U.ax205).pat], I ⊧ᴵ φ :=
    fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl hφ)))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
  rw [int_name] at hσI1
  have hSI : ∀ (e : Valuation M) b, (sortP "Int").interpret I e b ↔ b = σI := fun _ b => hσI1 b
  -- the elements of 1 and -1
  obtain ⟨m1, hm1d, hm1s⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int 1) = some Srt.int from rfl) KoreAML.val0
  obtain ⟨mN, hmNd, hmNs⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int (0 - 1)) = some Srt.int from rfl) KoreAML.val0
  rw [int_name] at hm1s hmNs
  have hm1 : Inh I σI m1 := (interp_inhOf_of (hSI _)).mp hm1s
  have hmN : Inh I σI mN := (interp_inhOf_of (hSI _)).mp hmNs
  let e := valAt σI m1
  have hden1 : ∀ b, (den (cH H) (KCore.int 1)).interpret I e b ↔ b = m1 := fun b =>
    ((den_closed (cH H) (KCore.int 1)).interp e KoreAML.val0 b).trans (hm1d b)
  have hdenN : ∀ b, (den (cH H) (KCore.int (0 - 1))).interpret I e b ↔ b = mN := fun b =>
    ((den_closed (cH H) (KCore.int (0 - 1))).interp e KoreAML.val0 b).trans (hmNd b)
  have hev : ∀ n : Nat, n ≠ 1 → e.evalEvar ⟨n⟩ = m1 := fun n hn => valAt_ne σI m1 (fun h => hn (by cases h; rfl))
  -- 203: f(1) is 1
  have hA := eqn_read hD hc hσI1 hσI2 s203 free_eqn.1 tab_eqn.1 (by rw [← trS_plain.2.1]; exact hT _ (by simp)) m1 hm1
  -- 205: g(1) is -1
  have hB := eqn_read hD hc hσI1 hσI2 s205 free_eqn.2.1 tab_eqn.2.1 (by rw [← trS_plain.2.2.1]; exact hT _ (by simp)) m1 hm1
  -- 207: h(1) holds f(1) and g(1)
  have hC := eqn_read hD hc hσI1 hσI2 s207 free_eqn.2.2 tab_eqn.2.2 (by rw [← trS_plain.2.2.2]; exact hT _ (by simp)) m1 hm1
  -- 80: h(1) is one element of Int
  obtain ⟨y, hy⟩ := fnl_read hD hc hσI1 hσI2 (by rw [← trS_plain.1]; exact hT _ (by simp)) m1 hm1
  have t3 := tab_eqn.1.2.2
  have t3' := tab_eqn.2.1.2.2
  have t3'' := tab_eqn.2.2.2.2
  have hvX : ∀ t : VarTable, t.ev kX = ⟨3⟩ → tr ⟨t, []⟩ vX = .evar ⟨3⟩ := fun t h => by
    unfold vX ev; rw [KoreAML.tr, show evarKey (evar "VarX" sI) = kX from rfl, h]
  -- f(X0) and f(VarX) agree at e (X0 and VarX are both m1)
  have hsw : ∀ (g : String) b, (sym (.symbol g) ⬝ .evar ⟨3⟩).interpret I e b ↔ (sym (.symbol g) ⬝ .evar ⟨2⟩).interpret I e b :=
    fun g b => interp_app_congr (fun _ => Iff.rfl) (fun m => by rw [interp_evar, interp_evar, hev 3 (by decide), hev 2 (by decide)]) b
  have hfm1 : (sym (.symbol "Lblf") ⬝ .evar ⟨2⟩).interpret I e m1 := by
    refine (hA m1 hm1).mpr ?_
    rw [hvX _ t3, interp_evar]; exact (hev 3 (by decide)).symm
  have hgmN : (sym (.symbol "Lblg") ⬝ .evar ⟨2⟩).interpret I e mN := by
    refine (hB mN hmN).mpr ?_
    -- the graph of `_-Int_` at [0, 1]
    have hgraph := hDom _ (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int 0, KCore.int 1], some (KCore.int (0 - 1)),
      by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
    have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
    have h1 : tr ⟨tableOf U.ax205.ax.sortVars U.ax205.ax.pattern, []⟩ (ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vX]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt"))) ⬝ .evar ⟨3⟩ := by
      unfold ap; rw [tr_app0, trArgs_cons, trArgs_cons, trArgs_nil, hvX _ t3']; rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 1])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int 0)) ⬝ den (cH H) (KCore.int 1) := by
      rw [symApp_noInst (c := cH H) (f := intSub) (by rw [(sub_name H).1]; exact (sub_name H).2), (sub_name H).1]; rfl
    rw [h1]
    have h3 := (hg2 mN).mpr ((hdenN mN).mpr rfl)
    rw [h2] at h3
    refine (interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => by rw [den_int0]) m)
      (fun m => ?_) mN).mpr h3
    rw [interp_evar, hev 3 (by decide), hden1]
  have hor : ∀ b, Inh I σI b → ((sym (.symbol "Lblf") ⬝ .evar ⟨2⟩).interpret I e b ∨
      (sym (.symbol "Lblg") ⬝ .evar ⟨2⟩).interpret I e b) → (sym (.symbol "Lblh") ⬝ .evar ⟨2⟩).interpret I e b := by
    intro b hb h
    refine (hC b hb).mpr ?_
    have ht : tr ⟨tableOf U.ax207.ax.sortVars U.ax207.ax.pattern, []⟩ (.or sI [ap "Lblf" [vX], ap "Lblg" [vX]]) =
        sOr (trSort (tableOf U.ax207.ax.sortVars U.ax207.ax.pattern) sI)
          (sym (.symbol "Lblf") ⬝ .evar ⟨3⟩) (sym (.symbol "Lblg") ⬝ .evar ⟨3⟩) := by
      rw [KoreAML.tr]; simp only [trOrList]; unfold ap; rw [tr_app0, tr_app0, trArgs_cons, trArgs_cons, trArgs_nil, trArgs_nil, hvX _ t3'']
    rw [ht, interp_sOr]
    refine ⟨(interp_inhOf_of (S := trSort _ sI) (fun b => by unfold sI; rw [trSort_srt]; exact hσI1 b)).mpr hb, ?_⟩
    rcases h with h | h
    · exact Or.inl ((hsw _ b).mpr h)
    · exact Or.inr ((hsw _ b).mpr h)
  have e1 : m1 = y := (hy m1 hm1).mp (hor m1 hm1 (Or.inl hfm1))
  have e2 : mN = y := (hy mN hmN).mp (hor mN hmN (Or.inr hgmN))
  -- 1 and -1 are distinct elements of Int
  have hax := hDom _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.int 1, KCore.int (0 - 1), Srt.int, int_distinct H, rfl, rfl,
    by decide, rfl⟩))))
  have := hax e m1
  rw [interpret_neg, interpret_conj] at this
  exact this ⟨(hden1 m1).mpr rfl, (hdenN m1).mpr (e1.trans e2.symm)⟩

/-! ## Γ has no model either -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

def vV : Kore.Pattern := ev "VarV0" sI
/-- Γ's equations of f, g and h's first two clauses (`orAsCases`: h(X) = f(X) where f(X) is
defined, h(X) = g(X) where g(X) is). -/
noncomputable def gAx (k : Nat) : Kore.Axiom := (fnAxioms c).getD k ⟨[], .top KoreAML.R, []⟩
def premC (a : String) : Kore.Pattern := .and KoreAML.R [premPn "VarV0", .ceil sI KoreAML.R (ap a [vV])]
theorem gAx_shape :
    (gAx 0).pattern = .implies KoreAML.R (premPn "VarV0") (.equals sI KoreAML.R (ap "Lblf" [vX0]) (.and sI [vV, .top sI])) ∧
    (gAx 1).pattern = .implies KoreAML.R (premPn "VarV0") (.equals sI KoreAML.R (ap "Lblg" [vX0])
      (.and sI [ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vV], .top sI])) ∧
    (gAx 2).pattern = .implies KoreAML.R (premC "Lblf") (.equals sI KoreAML.R (ap "Lblh" [vX0]) (.and sI [ap "Lblf" [vV], .top sI])) ∧
    (gAx 3).pattern = .implies KoreAML.R (premC "Lblg") (.equals sI KoreAML.R (ap "Lblh" [vX0]) (.and sI [ap "Lblg" [vV], .top sI])) := by
  decide +kernel
theorem gAx_free : ∀ k ∈ [0, 1, 2, 3], ((gAx k).sortVars.map sortVarKey ++ freeOf [] (gAx k).pattern).eraseDups =
    [.sortVar "R", kX0, .evar "VarV0" sI] := by decide +kernel
theorem gAx_tab : ∀ k ∈ [0, 1, 2, 3], TabOKn "VarV0" (tableOf (gAx k).sortVars (gAx k).pattern) := by
  unfold TabOKn; decide +kernel
theorem fnAx_len : 3 < (fnAxioms c).length := by decide +kernel
theorem gAx_mem (k : Nat) (hk : k ∈ [0, 1, 2, 3]) : gAx k ∈ fnAxioms c := by
  have hk' : k < (fnAxioms c).length := by
    have : k ≤ 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    exact Nat.lt_of_le_of_lt this fnAx_len
  unfold gAx
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  exact List.getElem_mem hk'

theorem gAx_sat (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (k : Nat) (hk : k ∈ [0, 1, 2, 3]) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", gAx k⟩).pat :=
  hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨_, by rw [fnItems_withHooks, fnItems_eq]; exact List.mem_map_of_mem (gAx_mem k hk), rfl⟩))))

/-- **Γ has no model, for every H**: at X = 1, Γ's clause of h for the alternative f(X) makes h(1)
the element of f(1), which f's equation makes 1, and its clause for g(X) makes h(1) the element of
g(1), which g's equation and the graph of `_-Int_` make -1: both alternatives are defined there, and
1 and -1 are distinct elements of Int. -/
theorem gamma_no_model (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : False := by
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
  rw [int_name] at hσI1
  have hSI : ∀ (e : Valuation M) b, (sortP "Int").interpret I e b ↔ b = σI := fun _ b => hσI1 b
  obtain ⟨m1, hm1d, hm1s⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int 1) = some Srt.int from rfl) KoreAML.val0
  obtain ⟨mN, hmNd, hmNs⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int (0 - 1)) = some Srt.int from rfl) KoreAML.val0
  rw [int_name] at hm1s hmNs
  have hm1 : Inh I σI m1 := (interp_inhOf_of (hSI _)).mp hm1s
  have hmN : Inh I σI mN := (interp_inhOf_of (hSI _)).mp hmNs
  let e := valAt σI m1
  have hden1 : ∀ b, (den (cH H) (KCore.int 1)).interpret I e b ↔ b = m1 := fun b =>
    ((den_closed (cH H) (KCore.int 1)).interp e KoreAML.val0 b).trans (hm1d b)
  have hdenN : ∀ b, (den (cH H) (KCore.int (0 - 1))).interpret I e b ↔ b = mN := fun b =>
    ((den_closed (cH H) (KCore.int (0 - 1))).interp e KoreAML.val0 b).trans (hmNd b)
  have hev : ∀ n : Nat, n ≠ 1 → e.evalEvar ⟨n⟩ = m1 := fun n hn => valAt_ne σI m1 (fun h => hn (by cases h; rfl))
  have hvV : ∀ t : VarTable, t.ev (.evar "VarV0" sI) = ⟨3⟩ → tr ⟨t, []⟩ vV = .evar ⟨3⟩ := fun t h => by
    unfold vV ev; rw [KoreAML.tr, show evarKey (evar "VarV0" sI) = VarKey.evar "VarV0" sI from rfl, h]
  have hsw : ∀ (g : String) b, (sym (.symbol g) ⬝ .evar ⟨3⟩).interpret I e b ↔ (sym (.symbol g) ⬝ .evar ⟨2⟩).interpret I e b :=
    fun g b => interp_app_congr (fun _ => Iff.rfl) (fun m => by rw [interp_evar, interp_evar, hev 3 (by decide), hev 2 (by decide)]) b
  have hap : ∀ (g : String) (t : VarTable), t.ev (.evar "VarV0" sI) = ⟨3⟩ →
      tr ⟨t, []⟩ (ap g [vV]) = sym (.symbol g) ⬝ .evar ⟨3⟩ := fun g t h => by
    unfold ap; rw [tr_app0, trArgs_cons, trArgs_nil, hvV t h]
  have hm : ∀ k (hk : k ∈ [0, 1, 2, 3]), TabOKn "VarV0" (tableOf (gAx k).sortVars (gAx k).pattern) := gAx_tab
  have hS : ∀ t : VarTable, ∀ b, (trSort t sI).interpret I e b ↔ b = σI := fun t b => by
    unfold sI; rw [trSort_srt]; exact hσI1 b
  -- f(1) is 1
  have hA := eqn_readG hD hc hσI1 hσI2 "VarV0" gAx_shape.1 (gAx_free 0 (by decide)) (hm 0 (by decide)) (gAx_sat H hI 0 (by decide)) m1 hm1
    (premPn_at hD hc hσI1 hσI2 "VarV0" (hm 0 (by decide)) m1 hm1)
  have hf : ∀ b, Inh I σI b → ((sym (.symbol "Lblf") ⬝ .evar ⟨2⟩).interpret I e b ↔ b = m1) := fun b hb => by
    rw [hA b hb, hvV _ (hm 0 (by decide)).2.2, interp_evar, hev 3 (by decide)]
  -- g(1) is -1
  have hB := eqn_readG hD hc hσI1 hσI2 "VarV0" gAx_shape.2.1 (gAx_free 1 (by decide)) (hm 1 (by decide)) (gAx_sat H hI 1 (by decide)) m1 hm1
    (premPn_at hD hc hσI1 hσI2 "VarV0" (hm 1 (by decide)) m1 hm1)
  have hgmN : (sym (.symbol "Lblg") ⬝ .evar ⟨2⟩).interpret I e mN := by
    refine (hB mN hmN).mpr ?_
    have hgraph := hDom _ (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int 0, KCore.int 1], some (KCore.int (0 - 1)),
      by decide +kernel, rfl, rfl, fun h => absurd h (by decide), rfl⟩)
    have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
    have h1 : tr ⟨tableOf (gAx 1).sortVars (gAx 1).pattern, []⟩ (ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vV]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt"))) ⬝ .evar ⟨3⟩ := by
      unfold ap; rw [tr_app0, trArgs_cons, trArgs_cons, trArgs_nil, hvV _ (hm 1 (by decide)).2.2]; rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 1])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int 0)) ⬝ den (cH H) (KCore.int 1) := by
      rw [symApp_noInst (c := cH H) (f := intSub) (by rw [(sub_name H).1]; exact (sub_name H).2), (sub_name H).1]; rfl
    rw [h1]
    have h3 := (hg2 mN).mpr ((hdenN mN).mpr rfl)
    rw [h2] at h3
    refine (interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => by rw [den_int0]) m)
      (fun m => ?_) mN).mpr h3
    rw [interp_evar, hev 3 (by decide), hden1]
  -- the premise of a clause of h: f(V0), resp. g(V0), has an element of Int
  have hprem : ∀ (a : String) (k : Nat) (hk : k ∈ [0, 1, 2, 3]), (∃ x, Inh I σI x ∧ (sym (.symbol a) ⬝ .evar ⟨2⟩).interpret I e x) →
      (tr ⟨tableOf (gAx k).sortVars (gAx k).pattern, []⟩ (premC a)).interpret I e m1 := by
    intro a k hk ⟨x, hx, hax⟩
    have ht := hm k hk
    unfold premC
    rw [interp_and (List.cons_ne_nil _ _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨premPn_at hD hc hσI1 hσI2 "VarV0" ht m1 hm1, ?_⟩
    have hRv : ∀ b, (trSort (tableOf (gAx k).sortVars (gAx k).pattern) KoreAML.R).interpret I e b ↔ b = σI := fun b => by
      rw [trSort_R, KoreAML.interp_evar, ht.1, valAt_1]
    rw [KoreAML.tr, hap a _ ht.2.2]
    exact interp_sCeil_raw.mpr ⟨σI, σI, x, (hS _ σI).mpr rfl, (hRv σI).mpr rfl, (hsw a x).mpr hax,
      (ceilE_of hD hc hσI2 hσI2 hx m1).mpr hm1⟩
  have hC0 := eqn_readG hD hc hσI1 hσI2 "VarV0" gAx_shape.2.2.1 (gAx_free 2 (by decide)) (hm 2 (by decide)) (gAx_sat H hI 2 (by decide)) m1 hm1
    (hprem "Lblf" 2 (by decide) ⟨m1, hm1, (hf m1 hm1).mpr rfl⟩)
  have hC1 := eqn_readG hD hc hσI1 hσI2 "VarV0" gAx_shape.2.2.2 (gAx_free 3 (by decide)) (hm 3 (by decide)) (gAx_sat H hI 3 (by decide)) m1 hm1
    (hprem "Lblg" 3 (by decide) ⟨mN, hmN, hgmN⟩)
  -- h(1) holds 1 (its clause for f) and so g(1) holds 1 (its clause for g)
  have hh1 : (sym (.symbol "Lblh") ⬝ .evar ⟨2⟩).interpret I e m1 := by
    rw [hC0 m1 hm1, hap _ _ (hm 2 (by decide)).2.2, hsw]; exact (hf m1 hm1).mpr rfl
  have hg1 : (sym (.symbol "Lblg") ⬝ .evar ⟨2⟩).interpret I e m1 := by
    rw [← hsw, ← hap _ _ (hm 3 (by decide)).2.2, ← hC1 m1 hm1]; exact hh1
  -- g(1) is one element: the value of `0 -Int 1`
  have hgN : ∀ b, Inh I σI b → (sym (.symbol "Lblg") ⬝ .evar ⟨2⟩).interpret I e b → b = mN := by
    intro b hb hgb
    have h0 := (hB b hb).mp hgb
    have h1 : tr ⟨tableOf (gAx 1).sortVars (gAx 1).pattern, []⟩ (ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vV]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt"))) ⬝ .evar ⟨3⟩ := by
      unfold ap; rw [tr_app0, trArgs_cons, trArgs_cons, trArgs_nil, hvV _ (hm 1 (by decide)).2.2]; rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int 1])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int 0)) ⬝ den (cH H) (KCore.int 1) := by
      rw [symApp_noInst (c := cH H) (f := intSub) (by rw [(sub_name H).1]; exact (sub_name H).2), (sub_name H).1]; rfl
    have hgraph := hDom _ (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int 0, KCore.int 1], some (KCore.int (0 - 1)),
      by decide +kernel, rfl, rfl, fun h => absurd h (by decide), rfl⟩)
    have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
    rw [h1] at h0
    have h3 : ((KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int 0)) ⬝ den (cH H) (KCore.int 1)).interpret I e b :=
      (interp_app_congr (φ' := KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int 0))
        (ψ' := den (cH H) (KCore.int 1))
        (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => by rw [den_int0]) m)
        (fun m => by rw [interp_evar, hev 3 (by decide), hden1]) b).mp h0
    rw [← h2] at h3
    exact (hdenN b).mp ((hg2 b).mp h3)
  have e12 : m1 = mN := hgN m1 hm1 hg1
  have hax := hDom _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨KCore.int 1, KCore.int (0 - 1), Srt.int, int_distinct H, rfl, rfl,
    by decide, rfl⟩))))
  have := hax e m1
  rw [interpret_neg, interpret_conj] at this
  exact this ⟨(hden1 m1).mpr rfl, (hdenN m1).mpr e12⟩

/-- **The reading has no model either, for every H**: `Γc` with the step's closure is
inconsistent. -/
theorem inconsistent (H : HookParams) : ¬ Consistent (cH H) := by
  rintro ⟨M, _, I, hI⟩
  exact gamma_no_model H fun φ hφ => hI φ (Or.inl (Or.inl hφ))


end KCore.TieE3MlEqRhsOrTotalNoModel

#print axioms KCore.TieE3MlEqRhsOrTotalNoModel.no_model
#print axioms KCore.TieE3MlEqRhsOrTotalNoModel.inconsistent
