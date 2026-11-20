/-
  Fixture e3-ml-eq-rhs-or-nest (`test/constructs/fixtures/e3-ml-eq-rhs-or-nest`): `rule f(X) => X`,
  `rule g(X) => X +Int 0`, `rule k(X) => X +Int 1`,
  `rule h(X) => (k(f(X) #Or g(X)) #Or #Bottom) #And {X *Int X >=Int 0 #Equals true}`, f, g, k and h
  `[function, total]` over Int. The text is `f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore`; sentence
  numbers are `AxiomDecl.index`: 204 is f's equation, 206 g's, 241 k's, 208 h's. Run from the package
  root: `lake env lean -j1 test/TieFrOrNestValue.lean`. Every statement is on the literal `kore`
  and `defn`, for every interpretation H.

  - `h_value`, for every H and every Int n: the premise set `Pre H` entails that the elements of Int
    in `h(n)` are exactly those of `n + 1`. `Pre H` is the four equations as the text writes them,
    with the signature and the domains of the reading (`ΓSig`: definedness, the item of `⌈_⌉`, the
    sorts Int and Bool; `ΓDomains`: the value n one element of Int, and the graphs of `_+Int_` at
    `[n, 0]` and `[n, 1]`, of `_*Int_` at `[n, n]` and of `_>=Int_` at `[n * n, 0]`, which no
    sentence of the text states). No other item of Γ is read, and no functional sentence.
    Read at X0 = X = n (`valAt`, `eqn_read`): f(n) is n (204); g(n) is `n +Int 0`, which the graph
    makes n (206); so `f(X) ∨ g(X)` is the one element n and `k(f(X) ∨ g(X))` is k(n), which is
    `n +Int 1` (241); `X *Int X >=Int 0` is `true` by the two graphs and `n * n ≥ 0`, so the
    predicate holds; 208 then gives h(n) the elements of Int of `n + 1`.
    The statement is of the elements of Int: an equation of the text is `\equals{Int, R}`, which
    compares its sides on Int only.
  - `h_value_at`: the same in a model of `Pre H`.
-/
import KcoreSpec
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace KCore.TieFrOrNestValue
open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore" module "E3-ML-EQ-RHS-OR-NEST"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

def sI : Kore.KSort := srt "Int"
def sB : Kore.KSort := srt "Bool"
def vX0 : Kore.Pattern := ev "X0" sI
def vX : Kore.Pattern := ev "VarX" sI
def kX0 : VarKey := .evar "X0" sI
def kX : VarKey := .evar "VarX" sI
/-- The premise every equation of the text writes: `\top ∧ (X0 ∈ VarX ∧ \top)`. -/
def premP : Kore.Pattern := .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in sI KoreAML.R vX0 vX, .top KoreAML.R]]
/-- An equation `prem → F(X0) = rhs ∧ \top` over Int. -/
def eqnP (f : String) (rhs : Kore.Pattern) : Kore.Pattern :=
  .implies KoreAML.R premP (.equals sI KoreAML.R (ap f [vX0]) (.and sI [rhs, .top sI]))

def plusN : String := "Lbl'UndsPlus'Int'Unds'"
def mulN : String := "Lbl'UndsStar'Int'Unds'"
def geN : String := "Lbl'Unds-GT-Eqls'Int'Unds'"
/-- `k(f(X) ∨ g(X)) ∨ ⊥`. -/
def orK : Kore.Pattern := .or sI [ap "Lblk" [.or sI [ap "Lblf" [vX], ap "Lblg" [vX]]], .bottom sI]
/-- `{X *Int X >=Int 0 #Equals true}`. -/
def eqK : Kore.Pattern := .equals sB sI (ap geN [ap mulN [vX, vX], .dv sI "0"]) (.dv sB "true")

theorem sF : U.ax204.ax.pattern = eqnP "Lblf" vX := by decide +kernel
theorem sG : U.ax206.ax.pattern = eqnP "Lblg" (ap plusN [vX, .dv sI "0"]) := by decide +kernel
theorem sK : U.ax241.ax.pattern = eqnP "Lblk" (ap plusN [vX, .dv sI "1"]) := by decide +kernel
theorem s208 : U.ax208.ax.pattern = eqnP "Lblh" (.and sI [orK, eqK]) := by decide +kernel
theorem trS_plain : (trS U.ax204).pat = (trAxiom [] [] U.ax204).pat ∧ (trS U.ax206).pat = (trAxiom [] [] U.ax206).pat ∧
    (trS U.ax241).pat = (trAxiom [] [] U.ax241).pat ∧ (trS U.ax208).pat = (trAxiom [] [] U.ax208).pat := by decide +kernel

theorem free_eqn : ∀ ad ∈ [U.ax204, U.ax206, U.ax241, U.ax208],
    (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups = [.sortVar "R", kX0, kX] := by
  decide +kernel
/-- The table's numbering: the sort variable R is 1, X0 is 2, VarX is 3. -/
def TabOK (t : VarTable) : Prop := t.ev (.sortVar "R") = ⟨1⟩ ∧ t.ev kX0 = ⟨2⟩ ∧ t.ev kX = ⟨3⟩
theorem tab_eqn : ∀ ad ∈ [U.ax204, U.ax206, U.ax241, U.ax208], TabOK (tableOf ad.ax.sortVars ad.ax.pattern) := by
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
/-- The graph of an interpreted symbol of two Int arguments at values, in a model of the domains. -/
theorem graph2 (H : HookParams) (hD : DefOK I) (hDom : I ⊧ᴵP ΓDomains (cH H)) {f : Sym} {nm : String} {res : Srt}
    (hnm : (cH H).symName f = nm ∧ instDecode? nm = none) (hk : (⟨f, [Srt.int, Srt.int], res⟩ : CtorSig) ∈ hookSigs)
    (x y : Int) {r : GroundTerm} (hh : hook f [KCore.int x, KCore.int y] = some (some r)) (e : Valuation M) (m : M) :
    ((sym (.symbol nm) ⬝ den (cH H) (KCore.int x)) ⬝ den (cH H) (KCore.int y)).interpret I e m ↔
      (den (cH H) r).interpret I e m := by
  have hgraph := hDom _ (Or.inl ⟨⟨f, [Srt.int, Srt.int], res⟩, [KCore.int x, KCore.int y], some r, hk,
    rmS_sortsOf_cons.mpr ⟨sortOf_int x, rmS_sortsOf_cons.mpr ⟨sortOf_int y, rfl⟩⟩, hh, fun h => absurd h (by simp), rfl⟩)
  have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
  have h2 : KoreAML.den (symApp (cH H) f (GroundTerm.koreList (cH H) [KCore.int x, KCore.int y])) =
      (sym (.symbol nm) ⬝ den (cH H) (KCore.int x)) ⬝ den (cH H) (KCore.int y) := by
    rw [symApp_noInst (c := cH H) (f := f) (by rw [hnm.1]; exact hnm.2), hnm.1]; rfl
  rw [← h2]; exact hg2 m

end

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem bool_name (H : HookParams) : (cH H).sortName Srt.bool = "Bool" := (by decide +kernel : c.sortName Srt.bool = "Bool")
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem bool_numbered (H : HookParams) : Srt.bool < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.bool < nRegSorts + c.sortNames.length)
theorem hook_names (H : HookParams) :
    ((cH H).symName intAdd = plusN ∧ instDecode? plusN = none) ∧ ((cH H).symName intMul = mulN ∧ instDecode? mulN = none) ∧
      ((cH H).symName intGe = geN ∧ instDecode? geN = none) :=
  (by decide +kernel : (c.symName intAdd = plusN ∧ instDecode? plusN = none) ∧ (c.symName intMul = mulN ∧ instDecode? mulN = none) ∧
      (c.symName intGe = geN ∧ instDecode? geN = none))
theorem hook_sigs : (⟨intAdd, [Srt.int, Srt.int], Srt.int⟩ : CtorSig) ∈ hookSigs ∧
    (⟨intMul, [Srt.int, Srt.int], Srt.int⟩ : CtorSig) ∈ hookSigs ∧ (⟨intGe, [Srt.int, Srt.int], Srt.bool⟩ : CtorSig) ∈ hookSigs := by
  decide +kernel
theorem den_lits (H : HookParams) :
    den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") ∧
    den (cH H) (KCore.int 1) = KoreAML.sym (.dv "1") ⬝ KoreAML.sym (.sort "SortInt") ∧
    den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.int 0) = _ ∧ den c (KCore.int 1) = _ ∧ den c (KCore.bool true) = _; decide +kernel

/-- The translations of the right sides, over each sentence's table. -/
theorem tr_rhs :
    tr ⟨tableOf U.ax204.ax.sortVars U.ax204.ax.pattern, []⟩ vX = .evar ⟨3⟩ ∧
    tr ⟨tableOf U.ax206.ax.sortVars U.ax206.ax.pattern, []⟩ (ap plusN [vX, .dv sI "0"]) =
      (sym (.symbol plusN) ⬝ .evar ⟨3⟩) ⬝ (sym (.dv "0") ⬝ sym (.sort "SortInt")) ∧
    tr ⟨tableOf U.ax241.ax.sortVars U.ax241.ax.pattern, []⟩ (ap plusN [vX, .dv sI "1"]) =
      (sym (.symbol plusN) ⬝ .evar ⟨3⟩) ⬝ (sym (.dv "1") ⬝ sym (.sort "SortInt")) ∧
    tr ⟨tableOf U.ax208.ax.sortVars U.ax208.ax.pattern, []⟩ orK =
      sOr (sym (.sort "SortInt"))
        (sym (.symbol "Lblk") ⬝ sOr (sym (.sort "SortInt")) (sym (.symbol "Lblf") ⬝ .evar ⟨3⟩) (sym (.symbol "Lblg") ⬝ .evar ⟨3⟩))
        (tr ⟨tableOf U.ax208.ax.sortVars U.ax208.ax.pattern, []⟩ (.bottom sI)) ∧
    tr ⟨tableOf U.ax208.ax.sortVars U.ax208.ax.pattern, []⟩ eqK =
      sEquals (sym (.sort "SortBool")) (sym (.sort "SortInt"))
        ((sym (.symbol geN) ⬝ ((sym (.symbol mulN) ⬝ .evar ⟨3⟩) ⬝ .evar ⟨3⟩)) ⬝ (sym (.dv "0") ⬝ sym (.sort "SortInt")))
        (sym (.dv "true") ⬝ sym (.sort "SortBool")) := by
  decide +kernel

/-- **The premises**: the equations of f (204), g (206), k (241) and h (208) as the text writes
them, with the signature and the domains of the reading, for every H. No other item of Γ. -/
noncomputable def Pre (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts [(trS U.ax208).pat, (trS U.ax204).pat, (trS U.ax206).pat, (trS U.ax241).pat] ∪ ΓSig (cH H) ∪ ΓDomains (cH H)

/-- **h(n) in a model of `Pre H`**: an element of Int is in `h(n)` exactly where it is in `n + 1`,
for every H and n. -/
theorem h_value_at (H : HookParams) (n : Int) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Pre H) (e' : Valuation M) (b : M) (hb : (inhOf (sortP "Int")).interpret I e' b) :
    ((sym (.symbol "Lblh") ⬝ den (cH H) (KCore.int n)).interpret I e' b ↔
      (den (cH H) (KCore.int (n + 1))).interpret I e' b) := by
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inl (Or.inr hφ))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  have hT : ∀ φ ∈ [(trS U.ax208).pat, (trS U.ax204).pat, (trS U.ax206).pat, (trS U.ax241).pat], I ⊧ᴵ φ :=
    fun φ hφ => hI φ (Or.inl (Or.inl (Or.inl hφ)))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
  rw [int_name] at hσI1
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (bool_numbered H)
  rw [bool_name] at hσB1
  have hSI : ∀ (e : Valuation M) b, (sortP "Int").interpret I e b ↔ b = σI := fun _ b => hσI1 b
  have hbI : Inh I σI b := (interp_inhOf_of (hSI _)).mp hb
  -- the element of n
  obtain ⟨m, hmd, hms⟩ := TieRhs.den_single_dom hD hDom (sortOf_int (c := cH H) n) KoreAML.val0
  rw [int_name] at hms
  have hm : Inh I σI m := (interp_inhOf_of (hSI _)).mp hms
  let e := valAt σI m
  have hden : ∀ (e₀ : Valuation M) a, (den (cH H) (KCore.int n)).interpret I e₀ a ↔ a = m := fun e₀ a =>
    ((den_closed (cH H) (KCore.int n)).interp e₀ KoreAML.val0 a).trans (hmd a)
  have hev : ∀ k : Nat, k ≠ 1 → e.evalEvar ⟨k⟩ = m := fun k hk => valAt_ne σI m (fun h => hk (by cases h; rfl))
  have hx3 : ∀ a, (Pattern.evar ⟨3⟩ : P).interpret I e a ↔ (den (cH H) (KCore.int n)).interpret I e a := fun a => by
    rw [interp_evar, hev 3 (by decide), hden]
  obtain ⟨⟨hnA, hnM, hnG⟩, hkA, hkM, hkG⟩ := And.intro (hook_names H) hook_sigs
  obtain ⟨hd0, hd1, hdT⟩ := den_lits H
  obtain ⟨trF, trG, trK, trO, trE⟩ := tr_rhs
  -- 204: f(n) is n
  have hA := eqn_read hD hc hσI1 hσI2 sF (free_eqn _ (.head _)) (tab_eqn _ (.head _))
    (by rw [← trS_plain.1]; exact hT _ (.tail _ (.head _))) m hm
  -- 206: g(n) is n +Int 0
  have hB := eqn_read hD hc hσI1 hσI2 sG (free_eqn _ (.tail _ (.head _))) (tab_eqn _ (.tail _ (.head _)))
    (by rw [← trS_plain.2.1]; exact hT _ (.tail _ (.tail _ (.head _)))) m hm
  -- 241: k(n) is n +Int 1
  have hK := eqn_read hD hc hσI1 hσI2 sK (free_eqn _ (.tail _ (.tail _ (.head _)))) (tab_eqn _ (.tail _ (.tail _ (.head _))))
    (by rw [← trS_plain.2.2.1]; exact hT _ (.tail _ (.tail _ (.tail _ (.head _))))) m hm
  -- 208
  have hH := eqn_read hD hc hσI1 hσI2 s208 (free_eqn _ (.tail _ (.tail _ (.tail _ (.head _))))) (tab_eqn _ (.tail _ (.tail _ (.tail _ (.head _)))))
    (by rw [← trS_plain.2.2.2]; exact hT _ (.head _)) m hm
  have hsw : ∀ (g : String) a, (sym (.symbol g) ⬝ .evar ⟨3⟩).interpret I e a ↔ (sym (.symbol g) ⬝ .evar ⟨2⟩).interpret I e a :=
    fun g a => interp_app_congr (fun _ => Iff.rfl) (fun x => by rw [interp_evar, interp_evar, hev 3 (by decide), hev 2 (by decide)]) a
  have hf : ∀ a, Inh I σI a → ((sym (.symbol "Lblf") ⬝ .evar ⟨2⟩).interpret I e a ↔ a = m) := fun a ha => by
    rw [hA a ha, trF, interp_evar, hev 3 (by decide)]
  have hg : ∀ a, Inh I σI a → ((sym (.symbol "Lblg") ⬝ .evar ⟨2⟩).interpret I e a ↔ a = m) := fun a ha => by
    rw [hB a ha, trG, ← hd0]
    rw [interp_app_congr (fun x => interp_app_congr (fun _ => Iff.rfl) hx3 x) (fun _ => Iff.rfl) a,
      graph2 H hD hDom hnA hkA n 0 (r := KCore.int (n + 0)) rfl e a, Int.add_zero, hden]
  have hk : ∀ a, Inh I σI a → ((sym (.symbol "Lblk") ⬝ .evar ⟨2⟩).interpret I e a ↔
      (den (cH H) (KCore.int (n + 1))).interpret I e a) := fun a ha => by
    rw [hK a ha, trK, ← hd1]
    rw [interp_app_congr (fun x => interp_app_congr (fun _ => Iff.rfl) hx3 x) (fun _ => Iff.rfl) a,
      graph2 H hD hDom hnA hkA n 1 (r := KCore.int (n + 1)) rfl e a]
  have hSIe : ∀ a, (sym (.sort "SortInt") : P).interpret I e a ↔ a = σI := fun a => hσI1 a
  have hSBe : ∀ a, (sym (.sort "SortBool") : P).interpret I e a ↔ a = σB := fun a => hσB1 a
  -- `f(X) ∨ g(X)` is the element of n
  have hor : ∀ a, (sOr (sym (.sort "SortInt")) (sym (.symbol "Lblf") ⬝ .evar ⟨3⟩) (sym (.symbol "Lblg") ⬝ .evar ⟨3⟩)).interpret I e a ↔
      (Pattern.evar ⟨2⟩ : P).interpret I e a := fun a => by
    rw [interp_sOr, interp_inhOf_of hSIe, hsw, hsw, interp_evar, hev 2 (by decide)]
    constructor
    · rintro ⟨ha, h | h⟩
      · exact (hf a ha).mp h
      · exact (hg a ha).mp h
    · rintro rfl; exact ⟨hm, Or.inl ((hf _ hm).mpr rfl)⟩
  have hnn : n * n ≥ 0 := by
    rcases Int.le_total 0 n with h | h
    · exact Int.mul_nonneg h h
    · exact Int.mul_nonneg_of_nonpos_of_nonpos h h
  -- the predicate holds
  have hpred : (tr ⟨tableOf U.ax208.ax.sortVars U.ax208.ax.pattern, []⟩ eqK).interpret I e b := by
    rw [trE, interp_sEquals hD hc hSBe hSIe hσB2 hσI2]
    refine ⟨hbI, fun a _ => ?_⟩
    rw [← hd0, ← hdT]
    have hmul : ∀ x, ((sym (.symbol mulN) ⬝ .evar ⟨3⟩) ⬝ .evar ⟨3⟩).interpret I e x ↔
        (den (cH H) (KCore.int (n * n))).interpret I e x := fun x => by
      rw [interp_app_congr (fun x => interp_app_congr (fun _ => Iff.rfl) hx3 x) hx3 x,
        graph2 H hD hDom hnM hkM n n (r := KCore.int (n * n)) rfl e x]
    rw [interp_app_congr (fun x => interp_app_congr (fun _ => Iff.rfl) hmul x) (fun _ => Iff.rfl) a,
      graph2 H hD hDom hnG hkG (n * n) 0 (r := KCore.bool (decide (n * n ≥ 0))) rfl e a,
      decide_eq_true hnn]
  -- h(n)
  have hh : (sym (.symbol "Lblh") ⬝ .evar ⟨2⟩).interpret I e b ↔ (den (cH H) (KCore.int (n + 1))).interpret I e b := by
    rw [hH b hbI, interp_and (List.cons_ne_nil _ _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [trO, interp_sOr, interp_inhOf_of hSIe, TieFRRead.tr_bottom_iff hD,
      interp_app_congr (fun _ => Iff.rfl) hor b, hk b hbI]
    exact ⟨fun h => h.1.2.resolve_right id, fun h => ⟨⟨hbI, Or.inl h⟩, hpred⟩⟩
  rw [(den_closed (cH H) (KCore.int (n + 1))).interp e' e b, ← hh]
  have hx2 : ∀ x, (den (cH H) (KCore.int n)).interpret I e' x ↔ (Pattern.evar ⟨2⟩ : P).interpret I e x := fun x =>
    (hden e' x).trans (by rw [interp_evar, hev 2 (by decide)])
  have hx1 : ∀ x, (sym (.symbol "Lblh") : P).interpret I e' x ↔ (sym (.symbol "Lblh") : P).interpret I e x :=
    fun _ => Iff.rfl
  exact interp_app_congr hx1 hx2 b

/-- **h(n) from the sentences**, for every H and n: `Pre H` entails that the elements of Int in
`h(n)` are those of `n + 1`. -/
theorem h_value (H : HookParams) (n : Int) :
    Pre H ⊧ ((sym (.symbol "Lblh") ⬝ den (cH H) (KCore.int n)) ⋀ inhOf (sortP "Int") ≡
      (den (cH H) (KCore.int (n + 1)) ⋀ inhOf (sortP "Int"))) := by
  intro M _ I hI e m
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  rw [KoreAML.interp_equal hD]
  intro a
  rw [interpret_conj, interpret_conj]
  exact ⟨fun h => ⟨(h_value_at H n hI e a h.2).mp h.1, h.2⟩, fun h => ⟨(h_value_at H n hI e a h.2).mpr h.1, h.2⟩⟩

end KCore.TieFrOrNestValue

#check @KCore.TieFrOrNestValue.h_value_at
#check @KCore.TieFrOrNestValue.h_value
/-- info: 'KCore.TieFrOrNestValue.h_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFrOrNestValue.h_value
