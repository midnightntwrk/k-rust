/-
  The tie (C14) of the reading `projectionDomainAsClause` on its construct fixture kore-projapp:
  krust's text of `f2-examples/projapp.k` (`<k> run(X) => done(project:Int(X)) </k>`), which holds
  for every sort X the selector-domain axiom of `project:X`,
  `⌈project:X(K)⌉ = ∃V:X. K = kseq(inj{X,KItem}(V), dotk)`. `project:Int` is the one projection a
  sentence applies: it is a function with the text's equation (sentence 178,
  `X0 ∈ kseq(inj(V), dotk) → project:Int(X0) = V`) and the clause read from its selector-domain
  axiom (sentence 179), `project:Int(K) = project:Int(K) ensures false`, of priority 200. Run from
  the package root: `lake env lean -j1 test/NoteProjDom.lean`. Every statement is on the literal
  `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree_parts` (constructors, functions, hooks,
  collections); `attrsAgree` itself is false here (`prios_read_clause`): the read clause's
  priority, 200, is stated by no equation of the text whose left side applies `project:Int` (the
  selector-domain axiom's left side is a `\ceil`). `account`: the function equations, the
  selector-domain axiom of `project:Int` and the constructor sentences are sentences of the user
  module, apart, with the count of the rest; the 13 other selector-domain axioms are about
  projections that are no symbol of the definition (`other_domains`), so they have no direction,
  as a sentence applying a symbol Γ lacks.

  Layer 2. Γ's item of the read clause (`g1`, item 1) is
  `¬(∃V:Int. X0 ∈ kseq(inj(V), dotk)) ∧ X0 ∈ W → project:Int(X0) = project:Int(W) ∧ ⌈false = true⌉`.
  **W1** (`w1`): the selector-domain axiom, with the signature, entails it, for every H: where X0
  is no injected Int in `kseq(…, dotk)`, the axiom's right side holds nothing, so
  `project:Int(X0)` holds no element of Int, and the item's two sides agree there. The other
  function equations (the projection's equation 178 and the sort predicates') are Γ's items
  (`shape`, `fns_entailed`, `fns_from_text`). Constructor sentences: `cons_entailed`. `consistent`
  is not derived: the deciders name `project:Int`'s termination (`dec_named`).

  The expectations (C7 form (a)), from `Pre H` (the function equations as written, Γ's item `g1`
  in the place of the selector-domain axiom, which entails it by `w1`, and the families; its
  model, through `Consistent`, waits on `project:Int`'s termination): `proj_5`, `project:Int(kseq(inj(5), dotk)) = 5`, from sentence 178 as
  written; `proj_dotk`, `project:Int(.K)` has no value, through the reading (the read clause).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteProjDom

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/projapp.kore"
definition_of defn from "f2-examples/projapp.kore"
user_axioms U from "f2-examples/projapp.kore" module "PROJAPP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "PROJAPP")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` on constructors, functions, hooks and collection
symbols. -/
theorem defs_attrsAgree_parts : AttrsAgree.ctors kore c = true ∧ AttrsAgree.fns kore c = true ∧
    AttrsAgree.hooks kore c = true ∧ AttrsAgree.colls kore c = true := by decide +kernel

/-- `attrsAgree` is false on this text by its priorities: `project:Int`'s clauses have the
priorities 50 (its equation) and 200 (the clause read from the selector-domain axiom), and the
text's equations whose left side applies `project:Int` state 50 only. -/
theorem prios_read_clause : AttrsAgree.prios kore defn = false ∧ attrsAgree kore defn = false ∧
    (c.allFns.filter (c.symName ·.label == "Lblproject'Coln'Int")).map (·.clauses.map (·.prio)) = [[50, 200]] := by
  decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's 31 equations, in `fnItems`'s order: `project:Int`'s equation (178)
and its selector-domain axiom (179), then the sort predicates' (`TiePair.fnTextOf` finds no
sentence of priority 200 whose left side applies `project:Int`, so the list is written out). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax178, U.ax179, U.ax139, U.ax140, U.ax141, U.ax142, U.ax143, U.ax259, U.ax260, U.ax254, U.ax255,
   U.ax247, U.ax248, U.ax137, U.ax138, U.ax181, U.ax182, U.ax293, U.ax294, U.ax295, U.ax296, U.ax297,
   U.ax298, U.ax299, U.ax300, U.ax289, U.ax290, U.ax291, U.ax292, U.ax264, U.ax265]

theorem fnText_length : fnText.length = 31 := rfl
theorem gammaPats_length : (TiePair.gammaPats c).length = 31 := by decide +kernel

/-! ### The read clause -/

/-- Γ's axiom of item 1, the clause read from the selector-domain axiom. -/
noncomputable def a1 : Kore.Axiom := ((TiePair.fnAxioms c)[1]?).getD ⟨[], .top KoreAML.R, []⟩
theorem a1_at : (TiePair.fnAxioms c)[1]? = some a1 := by decide +kernel
noncomputable def g1 : P := (trAxiom [] [] ⟨0, "kernel", a1⟩).pat
theorem g1_at : (TiePair.gammaPats c)[1]? = some g1 := TiePair.gammaPats_at a1_at

/-- `project:Int(t)`. -/
def projE (t : Kore.Pattern) : Kore.Pattern := ap "Lblproject'Coln'Int" [t]
/-- `kseq(inj{Int,KItem}(t), dotk)`. -/
def asKI (t : Kore.Pattern) : Kore.Pattern := kseq1 (injP "Int" "KItem" t)

def x0 : Kore.EVar := KoreAML.evar "X0" (srt "K")
def v0i : Kore.EVar := KoreAML.evar "VarV0" (srt "Int")
def v0k : Kore.EVar := KoreAML.evar "VarV0" (srt "K")
def si : Kore.EVar := KoreAML.evar "SelectorInput" (srt "K")
def vk : Kore.EVar := KoreAML.evar "VarK" (srt "Int")

/-- The pattern of `a1`, as `Γ` writes the clause `project:Int(W) = project:Int(W) ensures false`
of priority 200 below the projection's equation of priority 50. -/
def a1Pat : Kore.Pattern :=
  .implies KoreAML.R
    (.and KoreAML.R [.not KoreAML.R (.or KoreAML.R [.exist KoreAML.R v0i (.and KoreAML.R [.top KoreAML.R,
        .and KoreAML.R [.in (srt "K") KoreAML.R (.var (.evar x0)) (asKI (.var (.evar v0i))), .top KoreAML.R]]),
        .bottom KoreAML.R]),
      .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in (srt "K") KoreAML.R (.var (.evar x0)) (.var (.evar v0k)),
        .top KoreAML.R]]])
    (.equals (srt "Int") KoreAML.R (projE (.var (.evar x0)))
      (.and (srt "Int") [projE (.var (.evar v0k)), .equals (srt "Bool") (srt "Int") (.dv (srt "Bool") "false")
        (.dv (srt "Bool") "true")]))

/-- The pattern of the selector-domain axiom of `project:Int`, sentence 179. -/
def domPat : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals KoreAML.R KoreAML.R (.ceil (srt "Int") KoreAML.R (projE (.var (.evar si))))
      (.exist KoreAML.R vk (.equals (srt "K") KoreAML.R (.var (.evar si)) (asKI (.var (.evar vk))))))

kernel_rfl a1_pattern : a1.pattern = a1Pat
kernel_rfl dom_pattern : U.ax179.ax.pattern = domPat

/-- The two variable tables. -/
noncomputable abbrev t1 : VarTable := tableOf a1.sortVars a1.pattern
noncomputable abbrev tS : VarTable := tableOf U.ax179.ax.sortVars U.ax179.ax.pattern

theorem free1 : (a1.sortVars.map sortVarKey ++ freeOf [] a1.pattern).eraseDups =
    [.sortVar "R", evarKey x0, evarKey v0k] := by decide +kernel
theorem freeS : (U.ax179.ax.sortVars.map sortVarKey ++ freeOf [] U.ax179.ax.pattern).eraseDups =
    [.sortVar "R", evarKey si] := by decide +kernel

/-- `project:Int` applied to the variable `i`, as `tr` writes it. -/
def projP (i : EVar) : P := sym (.symbol "Lblproject'Coln'Int") ⬝ .evar i
/-- `kseq(inj{Int,KItem}(i), dotk)`, as `tr` writes it. -/
def kiP (i : EVar) : P :=
  sym (.symbol "kseq") ⬝ (sym (.symbol "inj") ⬝ sym (.sort "SortInt") ⬝ sym (.sort "SortKItem") ⬝ .evar i) ⬝
    sym (.symbol "dotk")

def sInt : P := sym (.sort "SortInt")
def sK : P := sym (.sort "SortK")

theorem tr1_eq : tr ⟨t1, []⟩ a1.pattern =
    sImp (.evar (t1.ev (.sortVar "R")))
      (sAnd (sNot (.evar (t1.ev (.sortVar "R"))) (sOr (.evar (t1.ev (.sortVar "R")))
          (sExists (t1.ev (evarKey v0i)) sInt (sAnd (sTop (.evar (t1.ev (.sortVar "R"))))
            (sAnd (sIn sK (.evar (t1.ev (.sortVar "R"))) (.evar (t1.ev (evarKey x0))) (kiP (t1.ev (evarKey v0i))))
              (sTop (.evar (t1.ev (.sortVar "R")))))))
          (sBot (.evar (t1.ev (.sortVar "R"))))))
        (sAnd (sTop (.evar (t1.ev (.sortVar "R"))))
          (sAnd (sIn sK (.evar (t1.ev (.sortVar "R"))) (.evar (t1.ev (evarKey x0))) (.evar (t1.ev (evarKey v0k))))
            (sTop (.evar (t1.ev (.sortVar "R")))))))
      (sEquals sInt (.evar (t1.ev (.sortVar "R"))) (projP (t1.ev (evarKey x0)))
        (sAnd (projP (t1.ev (evarKey v0k)))
          (sEquals (sym (.sort "SortBool")) sInt (sym (.dv "false") ⬝ sym (.sort "SortBool"))
            (sym (.dv "true") ⬝ sym (.sort "SortBool"))))) := by
  decide +kernel

theorem trS_eq : tr ⟨tS, kore.aliasNames⟩ U.ax179.ax.pattern =
    sImp (.evar (tS.ev (.sortVar "R"))) (sTop (.evar (tS.ev (.sortVar "R"))))
      (sEquals (.evar (tS.ev (.sortVar "R"))) (.evar (tS.ev (.sortVar "R")))
        (sCeil sInt (.evar (tS.ev (.sortVar "R"))) (projP (tS.ev (evarKey si))))
        (sExists (tS.ev (evarKey vk)) sInt
          (sEquals sK (.evar (tS.ev (.sortVar "R"))) (.evar (tS.ev (evarKey si))) (kiP (tS.ev (evarKey vk)))))) := by
  decide +kernel

theorem sort1 : sortOf [] a1.pattern = some KoreAML.R := by rw [a1_pattern]; rfl
theorem sortS : sortOf kore.symbolDecls U.ax179.ax.pattern = some KoreAML.R := by rw [dom_pattern]; rfl

theorem apart1 : t1.ev (.sortVar "R") ≠ t1.ev (evarKey v0i) ∧ t1.ev (evarKey x0) ≠ t1.ev (evarKey v0i) := by
  decide +kernel
theorem apartS : tS.ev (.sortVar "R") ≠ tS.ev (evarKey si) ∧ tS.ev (evarKey vk) ≠ tS.ev (.sortVar "R") ∧
    tS.ev (evarKey vk) ≠ tS.ev (evarKey si) := by
  decide +kernel

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

theorem projP_iff {e e' : Valuation M} {i j : EVar} (h : e.evalEvar i = e'.evalEvar j) (b : M) :
    (projP i).interpret I e b ↔ (projP j).interpret I e' b := by
  unfold projP; simp only [interp_app, interp_sym, interp_evar, h]

theorem kiP_iff {e e' : Valuation M} {i j : EVar} (h : e.evalEvar i = e'.evalEvar j) (b : M) :
    (kiP i).interpret I e b ↔ (kiP j).interpret I e' b := by
  unfold kiP; simp only [interp_app, interp_sym, interp_evar, h]

theorem sInt_closed (e e' : Valuation M) (a : M) : sInt.interpret I e a ↔ sInt.interpret I e' a := Iff.rfl
theorem sK_closed (e e' : Valuation M) (a : M) : sK.interpret I e a ↔ sK.interpret I e' a := Iff.rfl

end

theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem k_numbered (H : HookParams) : Srt.k < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.k < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem k_name (H : HookParams) : (cH H).sortName Srt.k = "K" := (by decide +kernel : c.sortName Srt.k = "K")

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- **W1 for the read clause**: the selector-domain axiom (sentence 179), with the signature,
entails Γ's item of the clause read from it, for every H. Where the premise holds, X0 is W and no
injected Int in `kseq(…, dotk)` is X0; at an element of Int that `project:Int(X0)` held, the
axiom's left side `⌈project:Int(X0)⌉` would hold, so its right side would give a V of Int with
X0 = `kseq(inj(V), dotk)`, which the premise excludes. So `project:Int(X0)` holds no element of Int,
and the two sides of the item's equation agree on Int. -/
theorem w1 (H : HookParams) : (TiePair.Texts [(trS U.ax179).pat] ∪ ΓSig (cH H)) ⊧ g1 := by
  intro M _ I hI
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ (trS U.ax179).pat := hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSig (int_numbered H)
  obtain ⟨σK, hσK1, hσK2⟩ := TieRhs.sortSing_sig hD hSig (k_numbered H)
  rw [int_name] at hσI1
  rw [k_name] at hσK1
  have hInt : ∀ (e : Valuation M) a, sInt.interpret I e a ↔ a = σI := fun _ a => hσI1 a
  have hK : ∀ (e : Valuation M) a, sK.interpret I e a ↔ a = σK := fun _ a => hσK1 a
  unfold g1
  refine tieAxiom_intro hD fun e hg x => ?_
  rw [free1] at hg
  have hR : IsSort I (e.evalEvar (t1.ev (.sortVar "R"))) :=
    (interp_guard_sortVar hD).mp (hg _ (List.mem_cons_self ..) default)
  generalize hσR : e.evalEvar (t1.ev (.sortVar "R")) = σR at hR
  have hRv : ∀ a, (Pattern.evar (t1.ev (.sortVar "R")) : P).interpret I e a ↔ a = σR := fun a => by
    rw [interp_evar, hσR]
  have hx0 : Inh I σK (e.evalEvar (t1.ev (evarKey x0))) := by
    have h := hg (evarKey x0) (by simp) default
    change ((t1.ev (evarKey x0)) ∈∈ inhOf (trSort t1 x0.sort) : P).interpret I e default at h
    rw [interp_member hD, show x0.sort = srt "K" from rfl, trSort_srt] at h
    exact (interp_inhOf_of (hK e)).mp h
  rw [sort1]
  dsimp only
  rw [tr1_eq, trSort_R, interp_sImp]
  refine ⟨fun h => h.1, fun hx => ⟨hx, fun hprem => ?_⟩⟩
  have hxR : Inh I σR x := (interp_inhOf_of hRv).mp hx
  rw [interp_sAnd, interp_sNot] at hprem
  obtain ⟨⟨hnor, -⟩, hrest⟩ := hprem
  rw [interp_sAnd, interp_sAnd] at hrest
  obtain ⟨-, hin, -⟩ := hrest
  rw [interp_sIn hD hc (hK e) hRv hσK2 hR (fun a ha => by rw [interp_evar] at ha; rw [ha]; exact hx0)] at hin
  obtain ⟨⟨w, hw1, hw2⟩, -⟩ := hin
  rw [interp_evar] at hw1 hw2
  -- `project:Int(X0)` holds no element of Int
  have noProj : ∀ a, Inh I σI a → ¬ (projP (t1.ev (evarKey x0))).interpret I e a := by
    intro a ha hp
    let xv := e.evalEvar (t1.ev (evarKey x0))
    let e' : Valuation M := ⟨fun i => if i = tS.ev (evarKey si) then xv else σR, e.evalSvar⟩
    have he'R : e'.evalEvar (tS.ev (.sortVar "R")) = σR := by
      show (if tS.ev (.sortVar "R") = tS.ev (evarKey si) then xv else σR) = σR
      rw [if_neg apartS.1]
    have he'S : e'.evalEvar (tS.ev (evarKey si)) = xv := by
      show (if tS.ev (evarKey si) = tS.ev (evarKey si) then xv else σR) = xv
      rw [if_pos rfl]
    have hRS : ∀ a, (Pattern.evar (tS.ev (.sortVar "R")) : P).interpret I e' a ↔ a = σR := fun a => by
      rw [interp_evar, he'R]
    have hgS : ∀ k ∈ (U.ax179.ax.sortVars.map sortVarKey ++ freeOf [] U.ax179.ax.pattern).eraseDups, ∀ m,
        (guardOf tS k).interpret I e' m := by
      rw [freeS]
      intro k hk m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [interp_guard_sortVar hD, he'R]; exact hR
      · change ((tS.ev (evarKey si)) ∈∈ inhOf (trSort tS si.sort) : P).interpret I e' m
        rw [interp_member hD, show si.sort = srt "K" from rfl, trSort_srt, he'S]
        exact (interp_inhOf_of (hK e')).mpr hx0
    have hax := trAxiom_at hD hT e' hgS x
    rw [sortS] at hax
    dsimp only at hax
    rw [trS_eq, trSort_R, interp_sImp] at hax
    have hx' : (inhOf (Pattern.evar (tS.ev (.sortVar "R")))).interpret I e' x := (interp_inhOf_of hRS).mpr hxR
    have heq := (hax.mpr hx').2 ((interp_sTop hD isFree_R x).mpr hx')
    rw [interp_sEquals hD hc hRS hRS hR hR] at heq
    have hceil : (sCeil sInt (Pattern.evar (tS.ev (.sortVar "R"))) (projP (tS.ev (evarKey si)))).interpret I e' x :=
      interp_sCeil_raw.mpr ⟨σI, σR, a, (hInt e' σI).mpr rfl, (hRS σR).mpr rfl,
        (projP_iff he'S.symm a).mp hp, (ceilE_of hD hc hσI2 hR ha x).mpr hxR⟩
    have hex := (heq.2 x hxR).mp hceil
    rw [interp_sExists] at hex
    obtain ⟨v, hv1, hv2⟩ := hex
    rw [interp_member hD] at hv1
    simp only [Function.update_same] at hv1
    have hvI : Inh I σI v := (interp_inhOf_of (hInt _)).mp hv1
    have hRS' : ∀ a, (Pattern.evar (tS.ev (.sortVar "R")) : P).interpret I
        ⟨Function.update e'.evalEvar (tS.ev (evarKey vk)) v, e'.evalSvar⟩ a ↔ a = σR := fun a => by
      rw [interp_evar]; simp only [Function.update_noteq apartS.2.1.symm, he'R]
    rw [interp_sEquals hD hc (hK _) hRS' hσK2 hR] at hv2
    have hk := (hv2.2 xv hx0).mp (by
      rw [interp_evar]; simp only [Function.update_noteq apartS.2.2.symm, he'S])
    -- the premise excludes this V
    apply hnor
    rw [interp_sOr]
    refine ⟨hx, Or.inl ?_⟩
    rw [interp_sExists]
    refine ⟨v, ?_, ?_⟩
    · rw [interp_member hD]; simp only [Function.update_same]; exact (interp_inhOf_of (hInt _)).mpr hvI
    · have hR1' : ∀ a, (Pattern.evar (t1.ev (.sortVar "R")) : P).interpret I
          ⟨Function.update e.evalEvar (t1.ev (evarKey v0i)) v, e.evalSvar⟩ a ↔ a = σR := fun a => by
        rw [interp_evar]; simp only [Function.update_noteq apart1.1, hσR]
      have hxR' : (inhOf (Pattern.evar (t1.ev (.sortVar "R")))).interpret I
          ⟨Function.update e.evalEvar (t1.ev (evarKey v0i)) v, e.evalSvar⟩ x := (interp_inhOf_of hR1').mpr hxR
      rw [interp_sAnd, interp_sAnd]
      refine ⟨(interp_sTop hD isFree_R x).mpr hxR', ?_, (interp_sTop hD isFree_R x).mpr hxR'⟩
      rw [interp_sIn hD hc (hK _) hR1' hσK2 hR (fun a ha => by
        rw [interp_evar] at ha; simp only [Function.update_noteq apart1.2] at ha; rw [ha]; exact hx0)]
      refine ⟨⟨xv, by rw [interp_evar]; exact (Function.update_noteq apart1.2 v e.evalEvar).symm, ?_⟩, hxR⟩
      exact (kiP_iff (by simp only [Function.update_same]) _).mpr hk
  rw [interp_sEquals hD hc (hInt e) hRv hσI2 hR]
  refine ⟨hxR, fun a ha => ⟨fun hp => absurd hp (noProj a ha), fun h => ?_⟩⟩
  rw [interp_sAnd] at h
  exact (projP_iff (hw2.symm.trans hw1) a).mp h.1

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and Γ's
item `g1` in the place of the selector-domain axiom (C7 (ii)). -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 1 g1

/-- **Each of Γ's equations is the translation of its text sentence**, but item 1, set to Γ's item
(kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The selector-domain axiom is not Γ's item pattern for pattern. -/
theorem g1_differs : g1 ≠ (trS U.ax179).pat := by decide +kernel

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ≠ 1) :
    textPats[j]? = some (trS ad).pat := by
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm hn), List.getElem?_map, hj]
  rfl

/-- **E for the function equations other than the selector-domain axiom**: Γ entails each, for
every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad → j ≠ 1 →
    Γ (cH H) ⊧ (trS ad).pat :=
  fun j ad hj hn => TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn))

/-- **The converse for `fnItems`**: each item is a consequence of its text sentence, the j-th of
`fnText`, with the signature: item 1 by `w1`, the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ ((TiePair.Texts [(trS ad).pat] ∪ ΓSig (cH H)) ⊧ it.pat) := by
  intro j it hj
  have hg : (TiePair.gammaPats c)[j]? = some it.pat := by
    rw [← TiePair.gammaPats_withHooks c H]
    unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
  by_cases h1 : j = 1
  · subst h1
    rw [g1_at] at hg
    exact ⟨U.ax179, rfl, (Option.some.inj hg) ▸ w1 H⟩
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  cases hf : fnText[j]? with
  | none =>
    have : j < 31 := by
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hg
      rw [gammaPats_length] at hlt; exact hlt
    rw [List.getElem?_eq_none_iff, fnText_length] at hf; omega
  | some ad =>
    rw [textPats_of hf h1] at ht
    cases ht
    exact ⟨ad, rfl, fun {M} _ {I} hI => hent (fun φ hφ => hI φ (Or.inl hφ))⟩

/-! ## The constructor sentences -/

noncomputable def consText : List AxiomDecl := U.all.filter fun ad => tieConsB c ad.ax

theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.mem_filter.mp had).2) ad.index ad.module hI

/-! ## The account -/

/-- The 13 other selector-domain axioms, of the projections of Bool, K, KItem, List, Set, Map,
Cmd and the cell sorts. -/
noncomputable def otherDomains : List AxiomDecl :=
  [U.ax129, U.ax132, U.ax135, U.ax245, U.ax252, U.ax257, U.ax262, U.ax269, U.ax275, U.ax278, U.ax281,
   U.ax284, U.ax287]

/-- The head of a selector-domain axiom's `\ceil`. -/
def domHead : Kore.Pattern → Option String
  | .implies _ (.top _) (.equals _ _ (.ceil _ _ (.app h _ _)) _) => some h.ident.name
  | _ => none

/-- **The 13 other selector-domain axioms are about projections that are no symbol of the
definition**: each is a selector-domain axiom (its left side a `\ceil` of a projection), and no
symbol of Γ has its projection's name, so they have no direction, as the sentences that apply a
symbol Γ lacks. -/
theorem other_domains : otherDomains.all (fun ad => match domHead ad.ax.pattern with
    | some n => (n.startsWith "Lblproject'Coln'") && (kernelSyms c).all (c.symName ·.name != n)
    | none => false) = true := by
  decide +kernel

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index)

/-- **The account**: the function equations (the selector-domain axiom 179 among them) and the
constructor sentences are sentences of the user module, each once and none in both classes, the 13
other selector-domain axioms none of them, with the sizes of the classes and of the rest. -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧ (otherDomains.map (·.index)).all (fun i => !tiedIdx.contains i) = true ∧
    (fnText.length, consText.length, otherDomains.length, U.all.length - tiedIdx.length) = (31, 32, 13, 235) := by
  decide +kernel

/-! ## The facts the deciders leave -/

def projInt : Sym := 387

theorem names : c.symName projInt = "Lblproject'Coln'Int" := by decide +kernel

noncomputable abbrev fnP : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn projInt = some fnP := rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hfnH (H : HookParams) : (cH H).lookupFn projInt = some fnP := by rw [Semantics.lookupFn_withHooks]; exact hfn

def kInt (n : Int) : GroundTerm := .ctor kseq [injNormal Srt.int Srt.kitem (int n), .ctor dotk []]
def dotK : GroundTerm := .ctor dotk []

theorem hvsH (H : HookParams) (v : GroundTerm) (hv : c.sortOf v = some Srt.k) :
    (cH H).sortsOf [v] = some fnP.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]
  have ha : fnP.args = [Srt.k] := by decide +kernel
  rw [ha]; exact OvlLaws.sortsOf_cons_iff.mpr ⟨hv, sortsOf_nil⟩

theorem eval_of {v : GroundTerm} {k : Nat} {r : Option GroundTerm} (hv : c.sortOf v = some Srt.k)
    (h : Cert.evalFC c k projInt [v] = some r) (H : HookParams) : Eval (cH H) projInt [v] r :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn
    (by rw [show fnP.args = [Srt.k] by decide +kernel]; exact OvlLaws.sortsOf_cons_iff.mpr ⟨hv, sortsOf_nil⟩) h

/-- The one fact the deciders leave: `project:Int`'s termination is named
(`decObligationsL`), since the read clause's right side is `project:Int(K)` itself, a call no
argument shows smaller (the clause decides with its `ensures` false and never evaluates it). So
`FnHyp`, and with it `Consistent`, are not derived here. -/
theorem dec_named : c.decObligationsL = [projInt] ∧ c.rankObligations [387] = [] ∧ c.agreeObligationsI = [] ∧
    c.matchObligationsL = ([] : List (Nat × Nat)) ∧ c.totalObligationsRP [387] [] = [] := by
  decide +kernel

/-! ## The expectations (C7 form (a)) -/

/-- The premises of the derivations: the function sentences as written, Γ's item `g1` in the
place of the selector-domain axiom (which entails it with the signature, `w1`), Γ's rule items and
the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

noncomputable abbrev projAt (H : HookParams) (v : GroundTerm) : P := TiePair.app (cH H) projInt [v]

/-- **`project:Int(kseq(inj(5), dotk)) = 5`, derived from `Pre`**, for every H: from sentence 178
as written. -/
theorem proj_5 (H : HookParams) : Pre H ⊧ (projAt H (kInt 5) ≡ den (cH H) (int 5)) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (by decide +kernel) (k := 10) (by decide +kernel) H) (hfnH H)
    (hvsH H _ (by decide +kernel))

/-- **`project:Int(.K)` has no value, derived from `Pre`**, for every H: through the reading (the
clause read from the selector-domain axiom decides at `.K`, its `ensures` false). -/
theorem proj_dotk (H : HookParams) : Pre H ⊧ (projAt H dotK ≡ ⊥) :=
  TiePair.noValue (shapeH H) (coreOKH H) (hokH H) (eval_of (by decide +kernel) (k := 10) (by decide +kernel) H) (hfnH H)
    (hvsH H _ (by decide +kernel))

end KCore.NoteProjDom

#print axioms KCore.NoteProjDom.wf_defn
#print axioms KCore.NoteProjDom.defs_attrsAgree_parts
#print axioms KCore.NoteProjDom.prios_read_clause
#print axioms KCore.NoteProjDom.account
#print axioms KCore.NoteProjDom.other_domains
#print axioms KCore.NoteProjDom.shape
#print axioms KCore.NoteProjDom.w1
#print axioms KCore.NoteProjDom.fns_entailed
#print axioms KCore.NoteProjDom.fns_from_text
#print axioms KCore.NoteProjDom.cons_entailed
#print axioms KCore.NoteProjDom.dec_named
#print axioms KCore.NoteProjDom.proj_5
#print axioms KCore.NoteProjDom.proj_dotk
