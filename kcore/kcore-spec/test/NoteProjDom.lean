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
  selector-domain axiom's left side is a `\ceil`). `AttrsAgree.priosBut` with `project:Int`'s
  clause at position 1 (the read clause, Γ's item 1: `read_clause_item`) left out of the clause side
  and no sentence left out is true (`priosBut_read`); the clause left out is tied to its sentence,
  the selector-domain axiom 179, by `w1` and `dom_entailed` (class *equal*; `read_clause_tie`).
  `account`: the function equations, the selector-domain axiom of `project:Int` and the
  constructor sentences are sentences of the user module, apart, with the count of the rest; the
  13 other selector-domain axioms are about projections that are no symbol of the definition
  (`other_domains`), so they have no direction, as a sentence applying a symbol Γ lacks.

  Layer 2. Γ's item of the read clause (`g1`, item 1) is
  `¬(∃V:Int. X0 ∈ kseq(inj(V), dotk)) ∧ X0 ∈ W → project:Int(X0) = project:Int(W) ∧ ⌈false = true⌉`.
  **W1** (`w1`): the selector-domain axiom, with the signature, entails it, for every H: where X0
  is no injected Int in `kseq(…, dotk)`, the axiom's right side holds nothing, so
  `project:Int(X0)` holds no element of Int, and the item's two sides agree there. **E**
  (`dom_entailed`): Γ entails the selector-domain axiom, for every H, so the class is *equal*: where
  `⌈project:Int(K)⌉` holds, `project:Int(K)` holds an element of Int (its arity, `proj_arity`), and
  were K no `kseq(inj(V), dotk)` the item `g1` would leave it none (its `ensures` false); so K is
  one, and `kseq(inj(V), dotk)` denotes one element (Cons-Fun, `GenEqs.projPat_fun`); conversely
  the projection's equation (sentence 178) gives `project:Int(kseq(inj(V), dotk)) = V`. The other
  function equations (the projection's equation 178 and the sort predicates') are Γ's items
  (`shape`, `fns_entailed`, `fns_from_text`). Constructor sentences: `cons_entailed`. The deciders
  name `project:Int`'s termination (`dec_named`), which holds for every H (`terminatesP`): at an
  element of K the projection's equation applies, or it fails and the read clause decides with its
  `ensures` false, its right side never evaluated. So `FnHyp` holds (`fnHypH`) and Γ with the step's
  closure has a model (`consistent`), and so has `Pre` (`pre_model`).

  The expectations (C7 form (a)), from `Pre H` (the function equations as written, Γ's item `g1`
  in the place of the selector-domain axiom, which entails it by `w1`, and the families; it has a
  model, `pre_model`): `proj_5`, `project:Int(kseq(inj(5), dotk)) = 5`, from sentence 178 as
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

/-- **With the read clause left out of the clause side, the priorities agree**: `prios` with
`project:Int`'s clause at position 1 (of priority 200) left out, and no sentence of the text left
out. The clause left out is tied to its sentence by `read_clause_tie`. -/
theorem priosBut_read : AttrsAgree.priosBut [] [("Lblproject'Coln'Int", 1)] kore defn = true := by
  decide +kernel

/-- The clause left out by `priosBut_read` is Γ's item 1: `project:Int` is the first function of
the definition, with the clauses of priorities 50 and 200, so Γ's items 0 and 1 are its clauses 0
and 1 (`fnItems` takes each function's clauses in order, one item each). -/
theorem read_clause_item :
    (c.allFns.head?.map fun f => (c.symName f.label, f.clauses.map (·.prio))) =
      some ("Lblproject'Coln'Int", [50, 200]) ∧
    (TiePair.clauseKeys c).take 2 = [("Lblproject'Coln'Int", 50), ("Lblproject'Coln'Int", 200)] := by
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

/-! ### E for the selector-domain axiom -/

/-- `project:Int`'s signature. -/
def kp : CtorSig := ⟨387, [Srt.k], Srt.int⟩

theorem kp_mem : kp ∈ kernelSyms c := by decide +kernel
theorem noInst_p : instDecode? (c.symName 387) = none := by decide +kernel
theorem name_p : c.symName 387 = "Lblproject'Coln'Int" := by decide +kernel

/-- **The arity of `project:Int` from `ΓSig`**: at an element of K it holds only elements of Int. -/
theorem proj_arity {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hS : I ⊧ᴵP ΓSig c) {e : Valuation M} {i : EVar} (hi : InS I "K" (e.evalEvar i)) {m : M}
    (hm : (projP i).interpret I e m) : InS I "Int" m := by
  have hit : I ⊧ᴵ (symArityItem c kp).pat := hS _ (Or.inl (Or.inl ⟨_, sig_arity kp_mem, rfl⟩))
  rw [symArityItem_noInst (k := kp) noInst_p, show kp.name = 387 from rfl, name_p] at hit
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  have hres : c.sortName kp.result = "Int" := by decide +kernel
  rw [hres] at hinc
  apply (inS_iff (I := I) (s := "Int") (a := m) KoreAML.val0).mp
  apply hinc
  unfold projP at hm
  obtain ⟨a, b, ha, hb, hab⟩ := interp_app.mp hm
  rw [interp_evar] at hb
  rw [interp_appList]
  refine ⟨a, ((Closed.sym _).interp e KoreAML.val0 a).mp ha, [b], ?_, ⟨m, hab, rfl⟩⟩
  have hn : c.sortName Srt.k = "K" := by decide +kernel
  simp only [kp, List.map_cons, List.map_nil, trSort_srt, hn]
  exact .cons ((inS_iff _).mpr (hb ▸ hi)) .nil

-- `kseq(inj{Int,KItem}(i), dotk)` as `tr` writes it is the projection's pattern of the library.
kernel_rfl kiP_eq : ∀ (H : HookParams) (i : EVar),
  kiP i = GenEqs.projInjPat (cH H) ((cH H).sortName Srt.int) (.evar i)

theorem int_sub (H : HookParams) : (Srt.int, Srt.kitem) ∈ (cH H).subsorts :=
  (by decide +kernel : (Srt.int, Srt.kitem) ∈ c.subsorts)
theorem k_cons (H : HookParams) : Srt.k ∈ consSorts (cH H) := (by decide +kernel : Srt.k ∈ consSorts c)
theorem kitem_cons (H : HookParams) : Srt.kitem ∈ consSorts (cH H) := (by decide +kernel : Srt.kitem ∈ consSorts c)

/-- `trS` of the selector-domain axiom is its translation without the text's declarations. -/
theorem trS179 : (trS U.ax179).pat = (trAxiom [] [] ⟨U.ax179.index, U.ax179.module, U.ax179.ax⟩).pat := by
  decide +kernel

theorem trS0_eq : tr ⟨tS, []⟩ U.ax179.ax.pattern =
    sImp (.evar (tS.ev (.sortVar "R"))) (sTop (.evar (tS.ev (.sortVar "R"))))
      (sEquals (.evar (tS.ev (.sortVar "R"))) (.evar (tS.ev (.sortVar "R")))
        (sCeil sInt (.evar (tS.ev (.sortVar "R"))) (projP (tS.ev (evarKey si))))
        (sExists (tS.ev (evarKey vk)) sInt
          (sEquals sK (.evar (tS.ev (.sortVar "R"))) (.evar (tS.ev (evarKey si))) (kiP (tS.ev (evarKey vk)))))) := by
  decide +kernel

theorem sortS0 : sortOf [] U.ax179.ax.pattern = some KoreAML.R := by rw [dom_pattern]; rfl

/-- The projection's equation, sentence 178. -/
noncomputable abbrev t0 : VarTable := tableOf U.ax178.ax.sortVars U.ax178.ax.pattern

theorem free0 : (U.ax178.ax.sortVars.map sortVarKey ++ freeOf [] U.ax178.ax.pattern).eraseDups =
    [.sortVar "R", evarKey x0, evarKey vk] := by decide +kernel

theorem tr0_eq : tr ⟨t0, kore.aliasNames⟩ U.ax178.ax.pattern =
    sImp (.evar (t0.ev (.sortVar "R")))
      (sAnd (sTop (.evar (t0.ev (.sortVar "R"))))
        (sAnd (sIn sK (.evar (t0.ev (.sortVar "R"))) (.evar (t0.ev (evarKey x0))) (kiP (t0.ev (evarKey vk))))
          (sTop (.evar (t0.ev (.sortVar "R"))))))
      (sEquals sInt (.evar (t0.ev (.sortVar "R"))) (projP (t0.ev (evarKey x0)))
        (sAnd (.evar (t0.ev (evarKey vk))) (sTop sInt))) := by
  decide +kernel

theorem sort0 : sortOf kore.symbolDecls U.ax178.ax.pattern = some KoreAML.R := by decide +kernel

theorem apart0 : t0.ev (.sortVar "R") ≠ t0.ev (evarKey x0) ∧ t0.ev (.sortVar "R") ≠ t0.ev (evarKey vk) ∧
    t0.ev (evarKey x0) ≠ t0.ev (evarKey vk) := by decide +kernel
theorem apart1R : t1.ev (.sortVar "R") ≠ t1.ev (evarKey x0) ∧ t1.ev (.sortVar "R") ≠ t1.ev (evarKey v0k) := by
  decide +kernel

theorem ensF_tr : tr ⟨t1, []⟩ (TieRhs.ensFalse (srt "Int")) =
    sEquals (sym (.sort "SortBool")) sInt (sym (.dv "false") ⬝ sym (.sort "SortBool"))
      (sym (.dv "true") ⬝ sym (.sort "SortBool")) := by
  decide +kernel

theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem den_false (H : HookParams) : den (cH H) (KCore.bool false) = KoreAML.sym (.dv "false") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool false) = _; decide +kernel
theorem den_true (H : HookParams) : den (cH H) (KCore.bool true) = KoreAML.sym (.dv "true") ⬝ KoreAML.sym (.sort "SortBool") := by
  show den c (KCore.bool true) = _; decide +kernel

theorem g1_mem : g1 ∈ textPats := by
  unfold textPats
  exact List.mem_of_getElem? (List.getElem?_set_self (by rw [List.length_map, fnText_length]; decide))

/-- **E for the selector-domain axiom**: Γ entails sentence 179, for every H. Where
`⌈project:Int(K)⌉` holds, `project:Int(K)` holds an element of Int (its arity); were K no
`kseq(inj(V), dotk)` with V of Int, Γ's item of the read clause (`g1`) would leave
`project:Int(K)` no element of Int (its `ensures` is false: `false` and `true` are two elements);
so K is one, and `kseq(inj(V), dotk)` denotes one element (Cons-Fun of `kseq`, `inj`, `dotk`), K.
Conversely, where K is `kseq(inj(V), dotk)`, the projection's equation (sentence 178) gives
`project:Int(K) = V`, defined. -/
theorem dom_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax179).pat := by
  intro M _ I hI
  have hD : DefOK I := defOK hI
  have hSigH : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hSig : I ⊧ᴵP ΓSig c := fun φ hφ => sat_sig hI (by unfold ΓSig at hφ ⊢; rw [sigItems_withHooks]; exact hφ)
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  have h178 : I ⊧ᴵ (trS U.ax178).pat := fns_entailed H 0 U.ax178 rfl (by decide) hI
  have hg1 : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a1⟩).pat := TiePair.entailed (shapeH H) g1 g1_mem hI
  have hc : I ⊧ᴵ ceilDefItem.pat := hSigH _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := TieRhs.sortSing_sig hD hSigH (int_numbered H)
  obtain ⟨σK, hσK1, hσK2⟩ := TieRhs.sortSing_sig hD hSigH (k_numbered H)
  rw [int_name] at hσI1
  rw [k_name] at hσK1
  have hInt : ∀ (e : Valuation M) a, sInt.interpret I e a ↔ a = σI := fun _ a => hσI1 a
  have hK : ∀ (e : Valuation M) a, sK.interpret I e a ↔ a = σK := fun _ a => hσK1 a
  have inK : ∀ a, InS I "K" a ↔ Inh I σK a := fun a =>
    (inS_iff (I := I) (s := "K") (a := a) KoreAML.val0).symm.trans (interp_inhOf_of (hK KoreAML.val0))
  have inI : ∀ a, InS I "Int" a ↔ Inh I σI a := fun a =>
    (inS_iff (I := I) (s := "Int") (a := a) KoreAML.val0).symm.trans (interp_inhOf_of (hInt KoreAML.val0))
  rw [trS179]
  refine tieAxiom_intro hD fun e hg x => ?_
  rw [freeS] at hg
  have hR : IsSort I (e.evalEvar (tS.ev (.sortVar "R"))) :=
    (interp_guard_sortVar hD).mp (hg _ (List.mem_cons_self ..) default)
  generalize hσR : e.evalEvar (tS.ev (.sortVar "R")) = σR at hR
  have hRv : ∀ a, (Pattern.evar (tS.ev (.sortVar "R")) : P).interpret I e a ↔ a = σR := fun a => by
    rw [interp_evar, hσR]
  have hs : Inh I σK (e.evalEvar (tS.ev (evarKey si))) := by
    have h := hg (evarKey si) (by simp) default
    change ((tS.ev (evarKey si)) ∈∈ inhOf (trSort tS si.sort) : P).interpret I e default at h
    rw [interp_member hD, show si.sort = srt "K" from rfl, trSort_srt] at h
    exact (interp_inhOf_of (hK e)).mp h
  generalize hsv : e.evalEvar (tS.ev (evarKey si)) = s at hs
  rw [sortS0]
  dsimp only
  rw [trS0_eq, trSort_R, interp_sImp]
  refine ⟨fun h => h.1, fun hx => ⟨hx, fun _ => ?_⟩⟩
  have hxR : Inh I σR x := (interp_inhOf_of hRv).mp hx
  rw [interp_sEquals hD hc hRv hRv hR hR]
  refine ⟨hxR, fun y hyR => ⟨fun hceil => ?_, fun hex => ?_⟩⟩
  · -- `⌈project:Int(K)⌉` gives K's form
    obtain ⟨σ1, σ2, a, -, -, hpa, -⟩ := interp_sCeil_raw.mp hceil
    have haI : Inh I σI a :=
      (inI a).mp (proj_arity hD hSig (i := tS.ev (evarKey si)) (by rw [hsv]; exact (inK s).mpr hs) hpa)
    by_cases hno : ∃ w, Inh I σI w ∧ (kiP (tS.ev (evarKey vk))).interpret I
        ⟨Function.update e.evalEvar (tS.ev (evarKey vk)) w, e.evalSvar⟩ s
    · obtain ⟨w, hwI, hkw⟩ := hno
      rw [interp_sExists]
      refine ⟨w, ?_, ?_⟩
      · rw [interp_member hD]; simp only [Function.update_same]; exact (interp_inhOf_of (hInt _)).mpr hwI
      · have hRS' : ∀ a, (Pattern.evar (tS.ev (.sortVar "R")) : P).interpret I
            ⟨Function.update e.evalEvar (tS.ev (evarKey vk)) w, e.evalSvar⟩ a ↔ a = σR := fun a => by
          rw [interp_evar]; simp only [Function.update_noteq apartS.2.1.symm, hσR]
        rw [interp_sEquals hD hc (hK _) hRS' hσK2 hR]
        have hwS : InS I ((cH H).sortName Srt.int) w := by rw [int_name]; exact (inI w).mpr hwI
        obtain ⟨y0, -, hy0⟩ := GenEqs.projPat_fun hI (int_sub H) (k_cons H) (kitem_cons H)
          (e := ⟨Function.update e.evalEvar (tS.ev (evarKey vk)) w, e.evalSvar⟩)
          (φ := .evar (tS.ev (evarKey vk))) (v := w)
          (fun m => by rw [interp_evar]; simp only [Function.update_same]) hwS
        have hs0 := (hy0 s).mp (by rw [← kiP_eq H]; exact hkw)
        refine ⟨hyR, fun k _ => ⟨fun hks => ?_, fun hkk => ?_⟩⟩
        · rw [interp_evar] at hks; simp only [Function.update_noteq apartS.2.2.symm, hsv] at hks
          rw [hks]; exact hkw
        · have hk0 := (hy0 k).mp (by rw [← kiP_eq H]; exact hkk)
          rw [interp_evar]; simp only [Function.update_noteq apartS.2.2.symm, hsv]
          rw [hk0, hs0]
    · -- otherwise Γ's item of the read clause leaves `project:Int(K)` no element of Int
      exfalso
      let e1 : Valuation M := ⟨fun i => if i = t1.ev (.sortVar "R") then σR else s, e.evalSvar⟩
      have e1R : e1.evalEvar (t1.ev (.sortVar "R")) = σR := by
        show (if t1.ev (.sortVar "R") = t1.ev (.sortVar "R") then σR else s) = σR
        rw [if_pos rfl]
      have e1X : e1.evalEvar (t1.ev (evarKey x0)) = s := by
        show (if t1.ev (evarKey x0) = t1.ev (.sortVar "R") then σR else s) = s
        rw [if_neg apart1R.1.symm]
      have e1V : e1.evalEvar (t1.ev (evarKey v0k)) = s := by
        show (if t1.ev (evarKey v0k) = t1.ev (.sortVar "R") then σR else s) = s
        rw [if_neg apart1R.2.symm]
      have hR1 : ∀ a, (Pattern.evar (t1.ev (.sortVar "R")) : P).interpret I e1 a ↔ a = σR := fun a => by
        rw [interp_evar, e1R]
      have hg1g : ∀ k ∈ (a1.sortVars.map sortVarKey ++ freeOf [] a1.pattern).eraseDups, ∀ m,
          (guardOf t1 k).interpret I e1 m := by
        rw [free1]
        intro k hk m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · rw [interp_guard_sortVar hD, e1R]; exact hR
        · change ((t1.ev (evarKey x0)) ∈∈ inhOf (trSort t1 x0.sort) : P).interpret I e1 m
          rw [interp_member hD, show x0.sort = srt "K" from rfl, trSort_srt, e1X]
          exact (interp_inhOf_of (hK e1)).mpr hs
        · change ((t1.ev (evarKey v0k)) ∈∈ inhOf (trSort t1 v0k.sort) : P).interpret I e1 m
          rw [interp_member hD, show v0k.sort = srt "K" from rfl, trSort_srt, e1V]
          exact (interp_inhOf_of (hK e1)).mpr hs
      have hax := trAxiom_at hD hg1 e1 hg1g y
      rw [sort1] at hax
      dsimp only at hax
      rw [tr1_eq, trSort_R, interp_sImp] at hax
      have hy1 : (inhOf (Pattern.evar (t1.ev (.sortVar "R")))).interpret I e1 y := (interp_inhOf_of hR1).mpr hyR
      have hconc := (hax.mpr hy1).2 (by
        rw [interp_sAnd, interp_sNot]
        refine ⟨⟨fun hor => ?_, hy1⟩, ?_⟩
        · rw [interp_sOr] at hor
          rcases hor.2 with hex | hbot
          · rw [interp_sExists] at hex
            obtain ⟨w, hw1, hw2⟩ := hex
            rw [interp_member hD] at hw1
            simp only [Function.update_same] at hw1
            have hwI : Inh I σI w := (interp_inhOf_of (hInt _)).mp hw1
            have hR1' : ∀ a, (Pattern.evar (t1.ev (.sortVar "R")) : P).interpret I
                ⟨Function.update e1.evalEvar (t1.ev (evarKey v0i)) w, e1.evalSvar⟩ a ↔ a = σR := fun a => by
              rw [interp_evar]; simp only [Function.update_noteq apart1.1, e1R]
            rw [interp_sAnd, interp_sAnd] at hw2
            obtain ⟨-, hin, -⟩ := hw2
            rw [interp_sIn hD hc (hK _) hR1' hσK2 hR (fun b hb => by
              rw [interp_evar] at hb; simp only [Function.update_noteq apart1.2, e1X] at hb; rw [hb]; exact hs)] at hin
            obtain ⟨⟨k, hk1, hk2⟩, -⟩ := hin
            rw [interp_evar] at hk1; simp only [Function.update_noteq apart1.2, e1X] at hk1
            rw [hk1] at hk2
            exact hno ⟨w, hwI, (kiP_iff (by simp only [Function.update_same]) s).mp hk2⟩
          · unfold sBot at hbot
            rw [interp_sNot] at hbot
            exact hbot.1 ((interp_sTop hD isFree_R y).mpr hbot.2)
        · rw [interp_sAnd, interp_sAnd]
          refine ⟨(interp_sTop hD isFree_R y).mpr hy1, ?_, (interp_sTop hD isFree_R y).mpr hy1⟩
          rw [interp_sIn hD hc (hK e1) hR1 hσK2 hR (fun b hb => by rw [interp_evar, e1X] at hb; rw [hb]; exact hs)]
          exact ⟨⟨s, by rw [interp_evar, e1X], by rw [interp_evar, e1V]⟩, hyR⟩)
      rw [interp_sEquals hD hc (hInt e1) hR1 hσI2 hR] at hconc
      have hboth := (hconc.2 a haI).mp ((projP_iff (by rw [e1X, hsv]) a).mpr hpa)
      rw [interp_sAnd] at hboth
      exact TieRhs.ensFalse_empty hD hSigH hDom (sortOf_false H) (sortOf_true H) (den_false H) (den_true H)
        (t := t1) (s := srt "Int") (e := e1) (fun a => by rw [trSort_srt]; exact hσI1 a) hσI2 a
        (by rw [ensF_tr]; exact hboth.2)
  · -- K's form gives `⌈project:Int(K)⌉`, by the projection's equation
    rw [interp_sExists] at hex
    obtain ⟨v, hv1, hv2⟩ := hex
    rw [interp_member hD] at hv1
    simp only [Function.update_same] at hv1
    have hvI : Inh I σI v := (interp_inhOf_of (hInt _)).mp hv1
    have hRS' : ∀ a, (Pattern.evar (tS.ev (.sortVar "R")) : P).interpret I
        ⟨Function.update e.evalEvar (tS.ev (evarKey vk)) v, e.evalSvar⟩ a ↔ a = σR := fun a => by
      rw [interp_evar]; simp only [Function.update_noteq apartS.2.1.symm, hσR]
    rw [interp_sEquals hD hc (hK _) hRS' hσK2 hR] at hv2
    have hki := (hv2.2 s hs).mp (by
      rw [interp_evar]; simp only [Function.update_noteq apartS.2.2.symm, hsv])
    let e0 : Valuation M := ⟨fun i => if i = t0.ev (.sortVar "R") then σR else
      if i = t0.ev (evarKey x0) then s else v, e.evalSvar⟩
    have e0R : e0.evalEvar (t0.ev (.sortVar "R")) = σR := by
      show (if t0.ev (.sortVar "R") = t0.ev (.sortVar "R") then σR else
        if t0.ev (.sortVar "R") = t0.ev (evarKey x0) then s else v) = σR
      rw [if_pos rfl]
    have e0X : e0.evalEvar (t0.ev (evarKey x0)) = s := by
      show (if t0.ev (evarKey x0) = t0.ev (.sortVar "R") then σR else
        if t0.ev (evarKey x0) = t0.ev (evarKey x0) then s else v) = s
      rw [if_neg apart0.1.symm, if_pos rfl]
    have e0V : e0.evalEvar (t0.ev (evarKey vk)) = v := by
      show (if t0.ev (evarKey vk) = t0.ev (.sortVar "R") then σR else
        if t0.ev (evarKey vk) = t0.ev (evarKey x0) then s else v) = v
      rw [if_neg apart0.2.1.symm, if_neg apart0.2.2.symm]
    have hR0 : ∀ a, (Pattern.evar (t0.ev (.sortVar "R")) : P).interpret I e0 a ↔ a = σR := fun a => by
      rw [interp_evar, e0R]
    have hg0 : ∀ k ∈ (U.ax178.ax.sortVars.map sortVarKey ++ freeOf [] U.ax178.ax.pattern).eraseDups, ∀ m,
        (guardOf t0 k).interpret I e0 m := by
      rw [free0]
      intro k hk m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · rw [interp_guard_sortVar hD, e0R]; exact hR
      · change ((t0.ev (evarKey x0)) ∈∈ inhOf (trSort t0 x0.sort) : P).interpret I e0 m
        rw [interp_member hD, show x0.sort = srt "K" from rfl, trSort_srt, e0X]
        exact (interp_inhOf_of (hK e0)).mpr hs
      · change ((t0.ev (evarKey vk)) ∈∈ inhOf (trSort t0 vk.sort) : P).interpret I e0 m
        rw [interp_member hD, show vk.sort = srt "Int" from rfl, trSort_srt, e0V]
        exact (interp_inhOf_of (hInt e0)).mpr hvI
    have hax := trAxiom_at hD h178 e0 hg0 y
    rw [sort0] at hax
    dsimp only at hax
    rw [tr0_eq, trSort_R, interp_sImp] at hax
    have hy0 : (inhOf (Pattern.evar (t0.ev (.sortVar "R")))).interpret I e0 y := (interp_inhOf_of hR0).mpr hyR
    have hconc := (hax.mpr hy0).2 (by
      rw [interp_sAnd, interp_sAnd]
      refine ⟨(interp_sTop hD isFree_R y).mpr hy0, ?_, (interp_sTop hD isFree_R y).mpr hy0⟩
      rw [interp_sIn hD hc (hK e0) hR0 hσK2 hR (fun b hb => by rw [interp_evar, e0X] at hb; rw [hb]; exact hs)]
      exact ⟨⟨s, by rw [interp_evar, e0X], (kiP_iff (by rw [e0V]; simp only [Function.update_same]) s).mpr hki⟩, hyR⟩)
    rw [interp_sEquals hD hc (hInt e0) hR0 hσI2 hR] at hconc
    have hpv := (hconc.2 v hvI).mpr (by
      rw [interp_sAnd, interp_evar, e0V]
      exact ⟨rfl, (interp_sTop hD rfl v).mpr ((interp_inhOf_of (hInt e0)).mpr hvI)⟩)
    exact interp_sCeil_raw.mpr ⟨σI, σR, v, (hInt e σI).mpr rfl, (hRv σR).mpr rfl,
      (projP_iff (by rw [e0X, hsv]) v).mp hpv, (ceilE_of hD hc hσI2 hR hvI y).mpr hyR⟩

/-- **The clause `priosBut_read` leaves out is tied to its sentence**, for every H: Γ's item 1
(`g1_at`, the read clause by `read_clause_item`) follows from the selector-domain axiom 179 with the
signature (`w1`), and Γ entails that axiom (`dom_entailed`). -/
theorem read_clause_tie (H : HookParams) : (TiePair.gammaPats c)[1]? = some g1 ∧
    ((TiePair.Texts [(trS U.ax179).pat] ∪ ΓSig (cH H)) ⊧ g1) ∧ (Γ (cH H) ⊧ (trS U.ax179).pat) :=
  ⟨g1_at, w1 H, dom_entailed H⟩

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
argument shows smaller (the clause decides with its `ensures` false and never evaluates it);
`terminatesP` proves it. -/
theorem dec_named : c.decObligationsL = [projInt] ∧ c.rankObligations [387] = [] ∧ c.agreeObligationsI = [] ∧
    c.matchObligationsL = ([] : List (Nat × Nat)) ∧ c.totalObligationsRP [387] [] = [] := by
  decide +kernel

/-! ## `project:Int` terminates -/

/-- `project:Int(kseq(inj{Int,KItem}(V), dotk)) => V`, the projection's equation (priority 50). -/
def clV : Clause :=
  { vars := [Srt.int], pats := [.app kseq [.inj Srt.int Srt.kitem (.var 0), .app dotk []]], req := none,
    rhs := .var 0, ens := none, prio := 50 }
/-- `project:Int(K) => project:Int(K) ensures false`, the clause read from the selector-domain
axiom (priority 200). -/
def clK : Clause :=
  { vars := [Srt.k], pats := [.var 0], req := none, rhs := .app projInt [.var 0],
    ens := some (.dv Srt.bool (.bool false)), prio := 200 }

kernel_rfl clauses_eq : fnP.clauses = [clV, clK]
theorem args_eq : fnP.args = [Srt.k] := by decide +kernel
theorem clV_left : clV.leftVars = [0] := by decide +kernel

theorem prio_cases {P : Clause → Prop} (hV : P clV) (hK : P clK) : ∀ cl ∈ fnP.clauses, P cl := by
  intro cl hcl
  rw [clauses_eq] at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · exact hV
  · exact hK

/-- **`project:Int` terminates**, under every H: at an element v of K, either the projection's
equation applies (its result is the injected Int), or it fails and the clause read from the
selector-domain axiom decides with its `ensures` false, so `project:Int(v)` has no value; its
right side, the call `project:Int(v)`, is never evaluated. -/
theorem terminatesP (H : HookParams) : Terminates (cH H) projInt := by
  intro fn hfn' vs hvs
  have e : fn = fnP := Option.some.inj (hfn'.symm.trans (hfnH H))
  subst e
  rw [args_eq] at hvs
  obtain ⟨v, rest, rfl⟩ : ∃ v rest, vs = v :: rest := by
    cases vs with
    | nil => simp [Semantics.sortsOf] at hvs
    | cons v rest => exact ⟨v, rest, rfl⟩
  obtain ⟨hv, hrest⟩ := OvlLaws.sortsOf_cons_iff.mp hvs
  obtain rfl := sortsOf_nil_eq hrest
  have hmemV : clV ∈ fnP.clauses := by rw [clauses_eq]; exact List.mem_cons_self
  have hmemK : clK ∈ fnP.clauses := by rw [clauses_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self
  by_cases hm : ∃ σ, (cH H).WellSortedAt clV.vars clV.leftVars σ ∧ PatVals (cH H) σ clV.pats [v]
  · obtain ⟨σ, hws, hpv⟩ := hm
    have hσ : (cH H).WellSorted clV.vars σ := fun i s hs => by
      have hi : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hs).1
        simp [clV] at this; omega
      subst hi
      exact hws 0 (by rw [clV_left]; exact List.mem_singleton_self _) s hs
    exact ⟨_, Eval.clause (hfnH H) hmemV hσ hpv (fun t h => by cases h) .top
      (prio_cases (P := fun cl' => cl'.aside = false → cl'.prio < clV.prio → Fails (cH H) [v] cl')
        (fun _ h => absurd h (by decide)) (fun _ h => absurd h (by decide)))
      rfl EvalTerm.var (fun t h => by cases h) .top⟩
  · have hfail : Fails (cH H) [v] clV := .intro fun σ hws hpv => absurd ⟨σ, hws, hpv⟩ hm
    have hσ : (cH H).WellSorted clK.vars [(0, v)] := fun i s hs => by
      have hi : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hs).1
        simp [clK] at this; omega
      subst hi
      simp only [clK, List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      exact ⟨v, rfl, hv⟩
    exact ⟨none, Eval.ensFails (t := .dv Srt.bool (.bool false)) (hfnH H) hmemK hσ
      (.cons (.var rfl) .nil) (fun t h => by cases h) .top
      (prio_cases (P := fun cl' => cl'.aside = false → cl'.prio < clK.prio → Fails (cH H) [v] cl')
        (fun _ _ => hfail) (fun _ h => absurd h (by decide)))
      rfl rfl EvalTerm.dv (by simp [KCore.bool])⟩

/-- **The facts the deciders leave of `FnHyp`**, under every H: the one named, `project:Int`'s
termination (`terminatesP`). -/
theorem obl (H : HookParams) : FnObligations (cH H) [387] [] := by
  obtain ⟨hd, hr, ha, hm, ht⟩ := dec_named
  have hpl : (cH H).plain = true := by rw [Semantics.plain_withHooks]; decide +kernel
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun p hp => ?_,
    openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts hpl).1 r hr))
      (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts hpl).2.1 fn hfn cl hcl)),
    openLaws_of_plain (Semantics.plain_parts hpl).2.2⟩
  · rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, hr, hd,
      List.nil_append, List.mem_singleton] at hf
    subst hf
    exact terminatesP H
  · rw [Semantics.totalObligationsRP_withHooks, ht] at hf; cases hf
  · rw [Det.Semantics.agreeObligationsI_withHooks, ha] at hf; cases hf
  · rw [Det.Semantics.matchObligationsL_withHooks, hm] at hp; cases hp

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectations (C7 form (a)) -/

/-- The premises of the derivations: the function sentences as written, Γ's item `g1` in the
place of the selector-domain axiom (which entails it with the signature, `w1`), Γ's rule items and
the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

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
#print axioms KCore.NoteProjDom.priosBut_read
#print axioms KCore.NoteProjDom.read_clause_item
#print axioms KCore.NoteProjDom.read_clause_tie
#print axioms KCore.NoteProjDom.account
#print axioms KCore.NoteProjDom.other_domains
#print axioms KCore.NoteProjDom.shape
#print axioms KCore.NoteProjDom.w1
#print axioms KCore.NoteProjDom.fns_entailed
#print axioms KCore.NoteProjDom.fns_from_text
#print axioms KCore.NoteProjDom.proj_arity
#print axioms KCore.NoteProjDom.dom_entailed
#print axioms KCore.NoteProjDom.cons_entailed
#print axioms KCore.NoteProjDom.dec_named
#print axioms KCore.NoteProjDom.terminatesP
#print axioms KCore.NoteProjDom.consistent
#print axioms KCore.NoteProjDom.pre_model
#print axioms KCore.NoteProjDom.proj_5
#print axioms KCore.NoteProjDom.proj_dotk
