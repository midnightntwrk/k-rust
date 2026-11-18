/-
  The tie (C14) of the reading of a user's equation of a generated sort predicate, on its construct
  fixture rdr-pred-rule: K 7.1.337 kompile's text of `test/constructs/fixtures/rdr-pred-rule/
  rdr-pred-rule.k` (`syntax Foo ::= "a" | pair(Foo, Foo)`, `rule isFoo(pair(_, _)) => true`). The
  text states three equations of `isFoo`: the generated `isFoo(kseq(inj{Foo,KItem}(F), dotk)) = true`
  (sentence 145), the user's `isFoo(kseq(inj{Foo,KItem}(pair(G0, G1)), dotk)) = true` (146), and
  kompile's `isFoo(K) = false [owise]` (144), whose exclusion names the user's pattern and the
  generated one. The definition holds `isFoo` as a sort predicate (`Semantics.sortPreds`) with two
  clauses, of priorities 50 and 200; the reader reads 146 as an instance of the clause of 50 at a
  constructor pattern (`Parse.predInstOK`) and 144 as the clause of 200 whose exclusion also names
  that instance (`Parse.predOwiseInstOK`): neither is an item of Γ. Run from the package root:
  `lake env lean -j1 test/NotePredInst.lean`. Every statement is on the literal `defn`, for every
  interpretation H.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree_parts` (constructors, functions, hooks,
  collections); `attrsAgree` itself is false (`prios_user_eqn`): the text states the priorities
  [200, 50, 50] for `isFoo` and the definition's clauses [50, 200], sentence 146 being an equation
  of `isFoo` that the definition holds as no clause. `priosBut` is `prios` with sentences of the
  text left out by index: with 146 left out it is true (`priosBut_user`), with nothing left out it
  is `prios` (`priosBut_nil`). What is left out is tied by its own theorem: Γ entails 146
  (`inst146_entailed`). `account`: the function equations (Γ's 29 items' sentences and 146) and the
  constructor sentences are sentences of the user module, apart, with the count of the rest.

  Layer 2. The function equations (`fnText`, written out: the sentence of each of Γ's 29 items in
  `fnItems`'s order; for item 27, `isFoo`'s clause of 50, `TiePair.fnTextOf` would pick 145 only by
  its place before 146): items 0 to 27 are the translations of their sentences (`shape`,
  `fns_entailed`, `fns_from_text`). Item 28, `isFoo`'s clause of 200, negates the generated
  exclusion only; sentence 144 negates the user's pattern too:
  - **144 entailed** (`owise144_entailed`): its translation is the item of
    `GenEqs.owiseWith` with the disjuncts [the user's pattern, the generated exclusion]
    (`w144_item`), which Γ entails for every H (`GenEqs.owiseWith_entailed`: negating more
    disjuncts narrows the premise). The reader accepts 144 (`owise144_read`), the case
    `GenEqs.predOwiseInst_entailed` states for every semantics.
  - **Item 28 from the text** (`w1`): sentence 144 with the signature entails item 28, for every H:
    an element of `kseq(inj{Foo,KItem}(pair(G0, G1)), dotk)` is one of
    `kseq(inj{Foo,KItem}(F), dotk)` for an F of Foo, since `pair` of elements of Foo is in Foo (its
    arity, `pair_arity`), so where the generated disjunct fails the user's fails too
    (`GenEqs.owi_sat_wider`).
  - **146 entailed** (`inst146_entailed`): the reader's instance (`inst146`) at the literal, through
    `GenEqs.predInst_entailed`; its translation is the item of the instance's clause equation
    (`items146`).
  Constructor sentences: `cons_entailed`. `consistent` for every H (the deciders name nothing).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NotePredInst

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rdr-pred-rule.kompile.kore"
definition_of defn from "f2-examples/rdr-pred-rule.kompile.kore"
user_axioms U from "f2-examples/rdr-pred-rule.kompile.kore" module "RDR-PRED-RULE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "RDR-PRED-RULE")

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

/-- `attrsAgree` is false on this text by its priorities: the text's equations of `isFoo` state
200, 50, 50 (sentences 144, 145, 146) and `isFoo`'s clauses have 50 and 200. -/
theorem prios_user_eqn : AttrsAgree.prios kore defn = false ∧ attrsAgree kore defn = false ∧
    (AttrsAgree.eqnsOf kore "LblisFoo").map (AttrsAgree.prioOf ·.attributes) = [200, 50, 50] ∧
    (c.allFns.filter (c.symName ·.label == "LblisFoo")).map (·.clauses.map (·.prio)) = [[50, 200]] := by
  decide +kernel

/-- `AttrsAgree.prios` with the sentences of the text whose index (`AxiomDecl.index`) is in `out`
left out of the text side: the rules' priorities as `prios` reads them, and for each function the
priorities the remaining equations of the text state against its clauses'. -/
def priosBut (out : List Nat) (k : Kore.Definition) (d : Definition) : Bool :=
  let c := d.sem
  let axs := k.axiomDecls.map (·.ax)
  let kept := (k.axiomDecls.filter fun ad => !out.contains ad.index).map (·.ax)
  d.pres.rules.length == c.rules.length &&
  ((c.rules.zip d.pres.rules).all fun (r, rp) => AttrsAgree.rewritePrioOf k rp.info.uid == some r.prio) &&
  ((axs.filter (AttrsAgree.isRewrite ·.pattern)).all fun a =>
    d.pres.rules.any fun rp => AttrsAgree.uidOf a.attributes == some rp.info.uid) &&
  c.allFns.all fun f =>
    (((kept.filter fun a => AttrsAgree.eqnHeadIs (c.symName f.label) a.pattern && !AttrsAgree.isLaw a).filter
        (!AttrsAgree.has ·.attributes "simplification")).map (AttrsAgree.prioOf ·.attributes)).isPerm
      (f.clauses.map (·.prio))

/-- **With the user's sentence 146 left out, the priorities agree.** -/
theorem priosBut_user : priosBut [U.ax146.index] kore defn = true := by decide +kernel

/-- With nothing left out, `priosBut` is `AttrsAgree.prios` on this text. -/
theorem priosBut_nil : priosBut [] kore defn = AttrsAgree.prios kore defn := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's 29 equations, in `fnItems`'s order: the sort predicates' clauses,
`isFoo`'s last (its clause of 50 from sentence 145, its clause of 200 from the `[owise]`
sentence 144). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax157, U.ax165, U.ax164, U.ax163, U.ax162, U.ax169, U.ax168, U.ax171, U.ax170, U.ax167, U.ax166,
   U.ax143, U.ax142, U.ax156, U.ax155, U.ax152, U.ax151, U.ax154, U.ax153, U.ax159, U.ax158, U.ax161,
   U.ax160, U.ax148, U.ax147, U.ax150, U.ax149, U.ax145, U.ax144]

theorem fnText_length : fnText.length = 29 := rfl
theorem gammaPats_length : (TiePair.gammaPats c).length = 29 := by decide +kernel

/-- Γ's axiom of item 28, `isFoo`'s clause of priority 200. -/
noncomputable def a28 : Kore.Axiom := ((TiePair.fnAxioms c)[28]?).getD ⟨[], .top KoreAML.R, []⟩
theorem a28_at : (TiePair.fnAxioms c)[28]? = some a28 := by decide +kernel
noncomputable def g28 : P := (trAxiom [] [] ⟨0, "kernel", a28⟩).pat
theorem g28_at : (TiePair.gammaPats c)[28]? = some g28 := TiePair.gammaPats_at a28_at

/-- The premise set's equations: each text sentence's translation, and Γ's item `g28` in the
place of sentence 144 (C7 (ii)). -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 28 g28

/-- **Each of Γ's equations is the translation of its text sentence**, but item 28, set to Γ's
item (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- Sentence 144 is not Γ's item pattern for pattern. -/
theorem g28_differs : g28 ≠ (trS U.ax144).pat := by decide +kernel

theorem textPats_of {j : Nat} {ad : AxiomDecl} (hj : fnText[j]? = some ad) (hn : j ≠ 28) :
    textPats[j]? = some (trS ad).pat := by
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm hn), List.getElem?_map, hj]
  rfl

/-- **E for the function equations other than 144**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad → j ≠ 28 →
    Γ (cH H) ⊧ (trS ad).pat :=
  fun j ad hj hn => TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (textPats_of hj hn))

/-! ## Sentence 146, the user's instance of `isFoo`'s clause of 50 -/

/-- The definition's names, as the reader numbers them. -/
noncomputable def N : Parse.Names := { sorts := c.sortNames, syms := c.symNames }

/-- Sentence 146 as the reader reads an equation. -/
noncomputable def e146 : Parse.RawEqn :=
  match Parse.rawEqn? U.ax146.ax with
  | some e => e
  | none => ⟨"", [], none, none, .top KoreAML.R, [], none, false⟩

/-- **The reader reads 146 as an instance of a clause of `isFoo` at a constructor pattern.** -/
theorem inst146 : Parse.predInstOK N "" c e146 = true := by decide +kernel

/-- 146 read as a clause, without an exclusion. -/
noncomputable def cl146 : Clause :=
  match Parse.clause? N "" e146 none with
  | .ok (cl, _) => cl
  | .error _ => { vars := [], pats := [], req := none, rhs := .var 0, ens := none }

theorem clause146 {cl : Clause} {cp : ClausePres} (h : Parse.clause? N "" e146 none = .ok (cl, cp)) : cl = cl146 := by
  unfold cl146; rw [h]

/-- The item of the instance's clause equation is the translation of 146, for the function of
`sortPreds` the reader names. -/
theorem items146 : ∀ fn ∈ c.sortPreds, c.symName fn.label = e146.fn →
    (kernelItems [prioEquation c fn cl146]).map (·.pat) = [(trS U.ax146).pat] := by decide +kernel

kernel_rfl predInstOK_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Parse.Names) (msrc : String) (e : Parse.RawEqn),
  Parse.predInstOK N msrc (c.withHooks H) e = Parse.predInstOK N msrc c e
kernel_rfl sortPreds_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).sortPreds = c.sortPreds
kernel_rfl symName_withHooks : ∀ (c : Semantics) (H : HookParams) (f : Sym), (c.withHooks H).symName f = c.symName f
kernel_rfl prioEquation_withHooks : ∀ (c : Semantics) (H : HookParams) (fn : Fn) (cl : Clause),
  prioEquation (c.withHooks H) fn cl = prioEquation c fn cl

/-- **Γ entails the user's sentence 146**, for every H (`GenEqs.predInst_entailed` at the reader's
instance `inst146`). -/
theorem inst146_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax146).pat := by
  obtain ⟨fn, hfn, hname, cl, cp, hcl, hent⟩ :=
    GenEqs.predInst_entailed (coreOKH H) (show Parse.predInstOK N "" (cH H) e146 = true by
      rw [predInstOK_withHooks]; exact inst146)
  rw [sortPreds_withHooks] at hfn
  rw [symName_withHooks] at hname
  rw [clause146 hcl, prioEquation_withHooks] at hent
  have hm := items146 fn hfn hname
  obtain ⟨it, hit, hpat⟩ : ∃ it ∈ kernelItems [prioEquation c fn cl146], it.pat = (trS U.ax146).pat := by
    cases hk : kernelItems [prioEquation c fn cl146] with
    | nil => rw [hk] at hm; cases hm
    | cons it rest =>
      rw [hk] at hm
      exact ⟨it, List.mem_cons_self .., (List.cons.inj hm).1⟩
  intro M _ I hI; rw [← hpat]; exact hent it hit hI

/-! ## Sentence 144, the `[owise]` equation -/

/-- `isFoo`, the last function of `sortPreds`. -/
noncomputable def fnFoo : Fn := c.sortPreds[14]'(by decide +kernel)
/-- `isFoo`'s clause of priority 200. -/
noncomputable def owc : Clause := fnFoo.clauses[1]'(by decide +kernel)

theorem fnFoo_name : c.symName fnFoo.label = "LblisFoo" ∧ owc.prio = 200 := by decide +kernel
theorem fnFoo_mem : fnFoo ∈ c.sortPreds := List.getElem_mem _
theorem owc_mem : owc ∈ fnFoo.clauses := List.getElem_mem _

/-- Γ's exclusions of the clauses before `isFoo`'s clause of 200: the one of the clause of 50. -/
noncomputable def exclG : List Kore.Pattern :=
  (lowerClauses fnFoo owc).map fun cl' => exclusion c fnFoo cl' (canonClausePres cl')

/-- The first disjunct of an `[owise]` equation's exclusion. -/
def firstDisj : Kore.Pattern → Kore.Pattern
  | .implies _ (.and _ [.not _ (.or _ [A, _]), _]) _ => A
  | p => p

/-- The disjunct of 144 that names the user's pattern,
`∃G0 G1. X0 ∈ kseq(inj{Foo,KItem}(pair(G0, G1)), dotk)`. -/
noncomputable def A144 : Kore.Pattern := firstDisj U.ax144.ax.pattern

/-- **144 is `isFoo`'s clause of 200 under the negation of the user's pattern and the generated
exclusion**: its translation is the item of `GenEqs.owiseWith` with those two disjuncts. -/
theorem w144_item : (kernelItems [GenEqs.owiseWith c fnFoo (A144 :: exclG) owc]).map (·.pat) =
    [(trS U.ax144).pat] := by decide +kernel

kernel_rfl allFns_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).allFns = c.allFns
kernel_rfl owiseWith_withHooks : ∀ (c : Semantics) (H : HookParams) (fn : Fn) (ds : List Kore.Pattern) (cl : Clause),
  GenEqs.owiseWith (c.withHooks H) fn ds cl = GenEqs.owiseWith c fn ds cl
kernel_rfl exclusion_withHooks : ∀ (c : Semantics) (H : HookParams) (fn : Fn) (cl : Clause) (cp : ClausePres),
  exclusion (c.withHooks H) fn cl cp = exclusion c fn cl cp

/-- **Γ entails the `[owise]` sentence 144**, for every H (`GenEqs.owiseWith_entailed`: the
generated exclusion is among its disjuncts). -/
theorem owise144_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax144).pat := by
  have hent := GenEqs.owiseWith_entailed (c := cH H) (ds := A144 :: exclG)
    (by rw [allFns_withHooks]; exact List.mem_append_right _ fnFoo_mem) owc_mem
    (GenEqs.owi_sortPreds_pre fnFoo_mem owc owc_mem) (Semantics.sortPreds_exs fnFoo_mem owc owc_mem)
    (fun cl' hcl' => by
      rw [exclusion_withHooks]
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem hcl'))
  rw [owiseWith_withHooks] at hent
  obtain ⟨it, hit, hpat⟩ : ∃ it ∈ kernelItems [GenEqs.owiseWith c fnFoo (A144 :: exclG) owc],
      it.pat = (trS U.ax144).pat := by
    have hm := w144_item
    cases hk : kernelItems [GenEqs.owiseWith c fnFoo (A144 :: exclG) owc] with
    | nil => rw [hk] at hm; cases hm
    | cons it rest =>
      rw [hk] at hm
      exact ⟨it, List.mem_cons_self .., (List.cons.inj hm).1⟩
  intro M _ I hI; rw [← hpat]; exact hent it hit hI

/-- The text's equations. -/
noncomputable def eqs : List Parse.RawEqn := U.all.filterMap fun ad => Parse.rawEqn? ad.ax
noncomputable def e144 : Parse.RawEqn :=
  match Parse.rawEqn? U.ax144.ax with
  | some e => e
  | none => ⟨"", [], none, none, .top KoreAML.R, [], none, false⟩

/-- The reader accepts 144 as the `[owise]` equation of `isFoo` whose exclusion also names the
instance 146 (`Parse.predOwiseInstOK`), the case `GenEqs.predOwiseInst_entailed` states for every
semantics. -/
theorem owise144_read : Parse.predOwiseInstOK N "" eqs c fnFoo e144 = true := by decide +kernel

/-! ## Item 28 from sentence 144 (W1)

Γ's item 28 is `GenEqs.owiseWith` with the generated exclusion alone (`a28_eq`); 144's translation
is the same with the user's pattern too (`w144_item`). The two premises differ by that disjunct:
where the generated disjunct fails the user's fails too, since `pair` of elements of Foo is in Foo
(`pair_arity`), so the text's premise is no narrower than the item's there
(`GenEqs.owi_sat_wider`). -/

/-- The axiom of an axiom sentence. -/
def axOf : Kore.Sentence → Kore.Axiom
  | .axiom a => a
  | _ => ⟨[], .top KoreAML.R, []⟩

/-- 144 as `owiseWith` writes it, and Γ's item 28. -/
noncomputable def aW : Kore.Axiom := axOf (GenEqs.owiseWith c fnFoo (A144 :: exclG) owc)
noncomputable def aG : Kore.Axiom := axOf (GenEqs.owiseWith c fnFoo exclG owc)

theorem a28_eq : a28 = aG := by decide +kernel

/-- The premise and conclusion of an implication. -/
def premOf : Kore.Pattern → Kore.Pattern
  | .implies _ p _ => p
  | p => p
def conclOf : Kore.Pattern → Kore.Pattern
  | .implies _ _ q => q
  | p => p
/-- The second conjunct of a two-conjunct `\and`. -/
def andSnd : Kore.Pattern → Kore.Pattern
  | .and _ [_, q] => q
  | p => p

/-- The generated exclusion, `∃V0:Foo. X0 ∈ kseq(inj{Foo,KItem}(V0), dotk)`. -/
noncomputable def exclE : Kore.Pattern := exclG.headD (.top KoreAML.R)
noncomputable def P0 : Kore.Pattern := andSnd (premOf aG.pattern)

kernel_rfl exclG_eq : exclG = [exclE]
kernel_rfl aG_pattern : aG.pattern = .implies KoreAML.R (.and KoreAML.R [.not KoreAML.R (anyOf [exclE]), P0])
  (conclOf aG.pattern)
kernel_rfl aW_pattern : aW.pattern = .implies KoreAML.R (.and KoreAML.R [.not KoreAML.R (anyOf [A144, exclE]), P0])
  (conclOf aG.pattern)
kernel_rfl aW_sortVars : aW.sortVars = aG.sortVars

theorem w144_trS : (trAxiom [] [] ⟨0, "kernel", aW⟩).pat = (trS U.ax144).pat := by decide +kernel

/-- The variable table of `aW`. -/
noncomputable abbrev tW : VarTable := tableOf aW.sortVars aW.pattern

def sFoo : P := sym (.sort "SortFoo")
def sK : P := sym (.sort "SortK")
/-- The sort variable `R` and the argument `X0` under `tW`. -/
def Rv : P := .evar ⟨1⟩
/-- `kseq(inj{Foo,KItem}(φ), dotk)`, as `tr` writes it. -/
def kpP (φ : P) : P :=
  sym (.symbol "kseq") ⬝ (sym (.symbol "inj") ⬝ sFoo ⬝ sym (.sort "SortKItem") ⬝ φ) ⬝ sym (.symbol "dotk")
/-- `pair(φ, ψ)`, as `tr` writes it. -/
def pairP (φ ψ : P) : P := sym (.symbol "Lblpair") ⬝ φ ⬝ ψ
/-- A disjunct's body: `⊤ ∧ (X0 ∈ Y ∧ ⊤)` at the sort `R`. -/
def bodyP (Y : P) : P := sAnd (sTop Rv) (sAnd (sIn sK Rv (.evar ⟨4⟩) Y) (sTop Rv))

theorem trA_eq : tr ⟨tW, []⟩ A144 =
    sExists ⟨2⟩ sFoo (sExists ⟨3⟩ sFoo (bodyP (kpP (pairP (.evar ⟨2⟩) (.evar ⟨3⟩))))) := by decide +kernel
theorem trE_eq : tr ⟨tW, []⟩ exclE = sExists ⟨5⟩ sFoo (bodyP (kpP (.evar ⟨5⟩))) := by decide +kernel

theorem hvarsW : ∀ k ∈ varsOf (.and KoreAML.R [.not KoreAML.R (anyOf [exclE]), P0]),
    k ∈ varsOf (.and KoreAML.R [.not KoreAML.R (anyOf [A144, exclE]), P0]) := by decide +kernel
theorem hfreeW : ∀ k ∈ freeOf [] (.and KoreAML.R [.not KoreAML.R (anyOf [A144, exclE]), P0]),
    k ∈ freeOf [] (.and KoreAML.R [.not KoreAML.R (anyOf [exclE]), P0]) := by decide +kernel

/-- The arity of `pair` (G-arity): `pair(⟦Foo⟧, ⟦Foo⟧) ⊆ ⟦Foo⟧`. -/
def pairArity : P := pairP (inhOf sFoo) (inhOf sFoo) ⊆⊆ inhOf sFoo

theorem pair_arity_sig : pairArity ∈ (sigItems c).map (·.pat) := by decide +kernel

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

theorem kpP_split {e : Valuation M} {φ : P} {b : M} (h : (kpP φ).interpret I e b) :
    ∃ x, φ.interpret I e x ∧ ∀ (e' : Valuation M) (ψ : P), ψ.interpret I e' x → (kpP ψ).interpret I e' b := by
  simp only [kpP, sym, Pattern.interpret] at h ⊢
  obtain ⟨a, d, ⟨k, z, hk, ⟨i, x, hi, hx, hiz⟩, hkz⟩, hd, hb⟩ := h
  exact ⟨x, hx, fun e' ψ hψ => ⟨a, d, ⟨k, z, hk, ⟨i, x, hi, hψ, hiz⟩, hkz⟩, hd, hb⟩⟩

theorem sTop_Rv (hD : DefOK I) {e e' : Valuation M} (h : e.evalEvar ⟨1⟩ = e'.evalEvar ⟨1⟩) (m : M) :
    (sTop Rv).interpret I e m → (sTop Rv).interpret I e' m := by
  rw [interp_sTop hD (by decide), interp_sTop hD (by decide)]
  simp only [inhOf, sym, Rv, Pattern.interpret, h]
  exact id

/-- `X0 ∈ Y` read at another valuation that gives `R` and `X0` the same elements, `Y` in `Y'`. -/
theorem sIn_X0 {e e' : Valuation M} (h1 : e.evalEvar ⟨1⟩ = e'.evalEvar ⟨1⟩) (h4 : e.evalEvar ⟨4⟩ = e'.evalEvar ⟨4⟩)
    {Y Y' : P} (hY : ∀ b, b = e.evalEvar ⟨4⟩ → Y.interpret I e b → Y'.interpret I e' b) (m : M) :
    (sIn sK Rv (.evar ⟨4⟩) Y).interpret I e m → (sIn sK Rv (.evar ⟨4⟩) Y').interpret I e' m := by
  unfold sIn sCeil
  simp only [sym, sK, Rv, interp_app, interp_sAnd]
  rintro ⟨a, b, ⟨a1, r, ha1, hr, happ1⟩, ⟨hb4, hbY⟩, happ⟩
  refine ⟨a, b, ⟨a1, r, ha1, ?_, happ1⟩, ⟨?_, hY b hb4 hbY⟩, happ⟩
  · show r = e'.evalEvar ⟨1⟩
    rw [← h1]; exact hr
  · show b = e'.evalEvar ⟨4⟩
    rw [← h4]; exact hb4

/-- **The user's pattern is inside the generated one**: in a model of definedness and of `pair`'s
arity, where 144's first disjunct holds under `tW`, the generated exclusion holds. -/
theorem A_sub_E (hD : DefOK I) (hpair : I ⊧ᴵ pairArity) {e : Valuation M} {m : M} :
    (tr ⟨tW, []⟩ A144).interpret I e m → (tr ⟨tW, []⟩ exclE).interpret I e m := by
  rw [trA_eq, trE_eq, interp_sExists]
  rintro ⟨g0v, hg0, h⟩
  rw [interp_sExists] at h
  obtain ⟨g1v, hg1, h⟩ := h
  rw [interp_member hD] at hg0 hg1
  generalize he1 : (⟨Function.update e.evalEvar ⟨2⟩ g0v, e.evalSvar⟩ : Valuation M) = e1 at hg0 hg1 h
  generalize he2 : (⟨Function.update e1.evalEvar ⟨3⟩ g1v, e1.evalSvar⟩ : Valuation M) = e2 at hg1 h
  have hv1 : e2.evalEvar ⟨1⟩ = e.evalEvar ⟨1⟩ := by
    rw [← he2, ← he1]; simp [Function.update_noteq]
  have hv4 : e2.evalEvar ⟨4⟩ = e.evalEvar ⟨4⟩ := by
    rw [← he2, ← he1]; simp [Function.update_noteq]
  have hv2 : e2.evalEvar ⟨2⟩ = g0v := by
    rw [← he2, ← he1]; simp [Function.update_noteq]
  have hv3 : e2.evalEvar ⟨3⟩ = g1v := by
    rw [← he2]; simp
  have hg0' : (inhOf sFoo).interpret I e2 g0v := by
    have : e1.evalEvar ⟨2⟩ = g0v := by rw [← he1]; simp
    rw [this] at hg0
    simpa only [inhOf, sFoo, sym, Pattern.interpret] using hg0
  have hg1' : (inhOf sFoo).interpret I e2 g1v := by
    have : e2.evalEvar ⟨3⟩ = g1v := hv3
    rw [this] at hg1
    simpa only [inhOf, sFoo, sym, Pattern.interpret] using hg1
  unfold bodyP at h
  rw [interp_sAnd, interp_sAnd] at h
  obtain ⟨hT1, hIn, hT2⟩ := h
  -- the element of `pair(G0, G1)` that X0's `kseq(inj(…), dotk)` holds
  have hIn' := hIn
  unfold sIn sCeil at hIn'
  simp only [sym, sK, Rv, interp_app, interp_sAnd] at hIn'
  obtain ⟨-, b, -, ⟨hb4, hbY⟩, -⟩ := hIn'
  obtain ⟨x, hx, hk⟩ := kpP_split hbY
  have hxFoo : (inhOf sFoo).interpret I e2 x := by
    have hinc := (interp_included hD).mp (hpair e2 x) x
    apply hinc
    simp only [pairP, interp_app] at hx ⊢
    obtain ⟨a, b', ⟨p, a', hp, ha', happ⟩, hb', happ'⟩ := hx
    refine ⟨a, b', ⟨p, a', hp, ?_, happ⟩, ?_, happ'⟩
    · have : a' = e2.evalEvar ⟨2⟩ := ha'
      rw [this, hv2]; exact hg0'
    · have : b' = e2.evalEvar ⟨3⟩ := hb'
      rw [this, hv3]; exact hg1'
  rw [interp_sExists]
  refine ⟨x, ?_, ?_⟩
  · rw [interp_member hD]; simp only [Function.update_same]
    simpa only [inhOf, sFoo, sym, Pattern.interpret] using hxFoo
  · unfold bodyP
    rw [interp_sAnd, interp_sAnd]
    have hw1 : e2.evalEvar ⟨1⟩ = (⟨Function.update e.evalEvar ⟨5⟩ x, e.evalSvar⟩ : Valuation M).evalEvar ⟨1⟩ := by
      rw [hv1]; simp [Function.update_noteq]
    have hw4 : e2.evalEvar ⟨4⟩ = (⟨Function.update e.evalEvar ⟨5⟩ x, e.evalSvar⟩ : Valuation M).evalEvar ⟨4⟩ := by
      rw [hv4]; simp [Function.update_noteq]
    refine ⟨sTop_Rv hD hw1 m hT1, sIn_X0 hw1 hw4 (fun b' hb' _ => ?_) m hIn, sTop_Rv hD hw1 m hT2⟩
    have hbb : b' = b := by rw [hb', ← hb4]
    rw [hbb]
    exact hk _ _ (show x = _ by simp)

end

/-- **W1 for item 28**: sentence 144, with the signature, entails Γ's item 28, for every H. Where
the item's premise holds, X0 is in no `kseq(inj{Foo,KItem}(F), dotk)` for an F of Foo; an element
of `kseq(inj{Foo,KItem}(pair(G0, G1)), dotk)` at G0, G1 of Foo is one of those (`A_sub_E`), so
144's premise holds too, and its conclusion is the item's. -/
theorem w1 (H : HookParams) : (TiePair.Texts [(trS U.ax144).pat] ∪ ΓSig (cH H)) ⊧ g28 := by
  intro M _ I hI
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hT : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", aW⟩).pat := by
    rw [w144_trS]; exact hI _ (Or.inl (Or.inl (List.mem_singleton_self _)))
  have hpair : I ⊧ᴵ pairArity := by
    obtain ⟨it, hit, hpat⟩ := List.mem_map.mp pair_arity_sig
    rw [← hpat]
    exact hI _ (Or.inr (Or.inl (Or.inl ⟨it, by rw [sigItems_withHooks]; exact hit, rfl⟩)))
  unfold g28
  rw [a28_eq]
  refine GenEqs.owi_sat_wider hD aW_sortVars aG_pattern aW_pattern hvarsW hfreeW ?_ hT
  intro e m b _ hb
  simp only [tr, trAndList] at hb ⊢
  rw [interp_sAnd, interp_sNot] at hb ⊢
  refine ⟨⟨fun hor => hb.1.1 ?_, hb.1.2⟩, hb.2⟩
  rw [GenEqs.owi_anyOf_iff hD] at hor ⊢
  obtain ⟨hR, x, hx, hxb⟩ := hor
  refine ⟨hR, exclE, List.mem_singleton_self _, ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact A_sub_E hD hpair hxb
  · rw [List.mem_singleton.mp hx] at hxb; exact hxb

/-- **The converse for `fnItems`**: each item is a consequence of its text sentence, the j-th of
`fnText`, with the signature: item 28 by `w1`, the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ ((TiePair.Texts [(trS ad).pat] ∪ ΓSig (cH H)) ⊧ it.pat) := by
  intro j it hj
  have hg : (TiePair.gammaPats c)[j]? = some it.pat := by
    rw [← TiePair.gammaPats_withHooks c H]
    unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
  by_cases h28 : j = 28
  · subst h28
    rw [g28_at] at hg
    exact ⟨U.ax144, rfl, (Option.some.inj hg) ▸ w1 H⟩
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  cases hf : fnText[j]? with
  | none =>
    have : j < 29 := by
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hg
      rw [gammaPats_length] at hlt; exact hlt
    rw [List.getElem?_eq_none_iff, fnText_length] at hf; omega
  | some ad =>
    rw [textPats_of hf h28] at ht
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

/-- The sentences tied here: the function equations (Γ's 29 items' sentences, then the user's
146) and the constructor sentences. -/
noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ [U.ax146.index] ++ consText.map (·.index)

/-- **The account**: the function equations (144 and 146 among them) and the constructor sentences
are sentences of the user module, each once and none in two classes, with the sizes of the
classes and of the rest. -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length + 1, consText.length, U.all.length - tiedIdx.length) = (30, 29, 127) := by
  decide +kernel

/-! ## Consistency for every H -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

end KCore.NotePredInst

#print axioms KCore.NotePredInst.wf_defn
#print axioms KCore.NotePredInst.coreOK
#print axioms KCore.NotePredInst.defs_attrsAgree_parts
#print axioms KCore.NotePredInst.prios_user_eqn
#print axioms KCore.NotePredInst.priosBut_user
#print axioms KCore.NotePredInst.priosBut_nil
#print axioms KCore.NotePredInst.shape
#print axioms KCore.NotePredInst.fns_entailed
#print axioms KCore.NotePredInst.fns_from_text
#print axioms KCore.NotePredInst.w1
#print axioms KCore.NotePredInst.inst146_entailed
#print axioms KCore.NotePredInst.owise144_entailed
#print axioms KCore.NotePredInst.owise144_read
#print axioms KCore.NotePredInst.cons_entailed
#print axioms KCore.NotePredInst.account
#print axioms KCore.NotePredInst.consistent
