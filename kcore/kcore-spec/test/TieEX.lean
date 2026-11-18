/-
  The tie of an equation with `\exists` over one Bool variable on its right side
  (KcoreSpec/TieEX.lean) on fixture `e3-eq-exists-bool-ml` (test/constructs/fixtures): its sentence
  246, `rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})` with f `total`, and f's
  functional sentence 162, against the three equations `Γ` states for the clauses `Parse.frClauses`
  gives the alternatives of the two instances. Run from the package root:
  `lake env lean -j1 test/TieEX.lean`.

  - `ax246`, `ax162`: the two sentences as kore.txt writes them (`//@ 246`, `//@ 162`), written out
    with the builders of Kore/Build.lean; `ax162_eq`: 162 is `Model.functionalAxiom c fFn`.
  - `fFn`: f with the clauses of the alternatives `xsOf true ++ xsOf false`: at the literal b, the
    term b with the condition `b = notBool(X)` (the body with b put for B: `B` is the term, the
    `\equals` conjunct the predicate). `frClauses_eqC` writes them as `pre := ⌈b⌉ ∧ b = notBool(X)`,
    `rhs := b`, and the last with `pre := ¬pre₁ ∧ ¬pre₂`, `ens := false`.
  - The shapes (kernel): the translated sentence is `eqnPat ws r prem Bool Ff ((∃B:Bool. body) ∧ ⊤)`
    (`text_shape`); `Γ`'s three items are `eqnPat` over the same guards with the premises
    `clauseQC` and `lastQC` (`gamma_shape`); the functional sentence is `fnlPat` of f applied to
    its variable K0 (`fnl_shape`).
  - What is read of the model: `NodeFacts c I` (definedness, the definedness symbols, every
    numbered sort a sort, each value one element of its sort, distinct values apart) and
    `boolClosed c`. Nothing about f or `notBool`. `Γcl c` does not hold `boolClosed c` here
    (`gammaC_plain`): `readsConfined` reads a clause's predicate only where it has a binder, and
    the patterns bind the clauses' one variable.
  - `gamma_of_text`: the sentence with f's functional sentence and `boolClosed` gives each of `Γ`'s
    three items.
  - `text_of_gamma`: `Γ`'s three items and `boolClosed` give the sentence, without the functional
    sentence; the last clause's right side `true ∧ ⌈false = true⌉` holds nothing because `false`
    and `true` are two elements of Bool (`NodeFacts.apart`).
  The instances' reading (`hbody`) and the conditions' (`hcond`) are proved here from the patterns:
  at B := the element y of the literal b, the body `B ∧ (B = notBool(X))` holds y exactly where y
  agrees with `notBool(X)` on Bool, which is the condition `b = notBool(X)`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.TieEXTest

open ML KoreAML KoreAML.TieFR KCore.TieEX
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-! ## The semantics: f with the clauses of its split -/

def Fs : Sym := nRegSyms + 4
def notX : Term := .app boolNot [.var 0]
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)

/-- The alternatives of the instance at the literal b: the term b, with the condition
`b = notBool(X)`. -/
def xsOf (b : Bool) : List (Term × List Cond) := [(litT b, [.equals Srt.bool (litT b) notX])]
def xsC : List (Term × List Cond) := xsOf true ++ xsOf false

/-- f, declared `total`, with the clauses of the split. -/
def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool, Parse.frClauses Srt.bool [Srt.bool] [.var 0] none 50 false xsC, true⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- `Γc c` is `Γ c`: no clause has a variable its patterns do not bind, nor a predicate with a
binder, so `readsConfined` is false and `Γcl c` holds no sentence. `boolClosed c`, which the tie
reads, is therefore a hypothesis on the model here, not a sentence of the theory. -/
theorem gammaC_plain : c.readsConfined = false ∧ c.litSort Srt.bool = true ∧ Faithful.Γc c = Faithful.Γ c :=
  ⟨by decide +kernel, by decide +kernel, Faithful.Γc_plain (by decide +kernel)⟩

/-! ## The text's two sentences -/

def bS : Kore.KSort := srt "Bool"

/-- The binder's body `B ∧ (B = notBool(X))`. -/
def bodyK : Kore.Pattern :=
  .and bS [ev "VarB" bS, .equals bS bS (ev "VarB" bS) (ap "LblnotBool'Unds'" [ev "VarX" bS])]

/-- Sentence 246: `X0 ∈ VarX → f(X0) = (∃B:Bool. B ∧ (B = notBool(X))) ∧ ⊤`. -/
def ax246 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (.and R [.top R, .and R [.in bS R (ev "X0" bS) (ev "VarX" bS), .top R]])
      (.equals bS R (ap "Lblf" [ev "X0" bS])
        (.and bS [.exist bS (evar "VarB" bS) bodyK, .top bS]))
    attributes := [] }

/-- Sentence 162: `∃Val. Val = f(K0)`. -/
def ax162 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .exist R (evar "Val" bS) (.equals bS R (.var (.evar (evar "Val" bS))) (ap "Lblf" [ev "K0" bS]))
    attributes := [attr "functional"] }

theorem ax162_eq : ax162 = Faithful.Model.functionalAxiom c fFn := by decide +kernel

def textItem : Item := trAxiom [] [] ⟨246, "E3-EQ-EXISTS-BOOL-ML", ax246⟩
def fnlItem : Item := Faithful.Model.functionalItem c fFn

/-! ## The shapes -/

def tbl : VarTable := tableOf ax246.sortVars ax246.pattern
def ctx : Ctx := ⟨tbl, []⟩
def ws : List P := guardsOf ax246
def r : EVar := tbl.ev (sortVarKey Rv)
def prem : P := tr ctx (.and R [.top R, .and R [.in bS R (ev "X0" bS) (ev "VarX" bS), .top R]])
def BoolP : P := trSort tbl bS
def Ff : P := tr ctx (ap "Lblf" [ev "X0" bS])
def xB : EVar := tbl.ev (evarKey (evar "VarB" bS))
def bodyT : P := tr ctx bodyK
def ensT : P := tr ctx (.top bS)
def notT : P := tr ctx (ap "LblnotBool'Unds'" [ev "VarX" bS])
def x0 : EVar := tbl.ev (evarKey (evar "X0" bS))

theorem text_shape : textItem.pat = eqnPat ws r prem BoolP Ff (sAnd (sExists xB TieFRRead.boolP bodyT) ensT) := by
  rw [textItem, trAxiom_eqnPat [] [] _ _ ax246 rfl rfl]
  decide +kernel

/-- The clauses' variables and the table of `Γ`'s items for f. -/
def vsC : List KoreAML.Var := Faithful.canonVars c [Srt.bool]
def tblG : VarTable := [.sortVar "R", .evar "X0" bS, .evar "VarV0" bS]

/-- The last clause's right side `true ∧ (false = true)`. -/
def BNG : P := sAnd (altPC c tblG vsC (litT true, [.equals Srt.bool (litT true) notX]))
  (tr ⟨tblG, []⟩ (reqPat (srtOf c Srt.bool) (some (Term.kore c vsC (Parse.boolT false)))))

/-- `Γ`'s items for f: the three clauses' equations, over the sentence's guards, variable of R and
application of f, with the premises `clauseQC` and `lastQC`. -/
theorem gamma_shape : (Faithful.kernelItems (Faithful.fnEquationsK c fFn)).map (·.pat) =
    [eqnPat ws r (clauseQC c tblG vsC Srt.bool prem (litT true, [.equals Srt.bool (litT true) notX])) BoolP Ff
       (sAnd (altPC c tblG vsC (litT true, [.equals Srt.bool (litT true) notX])) (sTop BoolP)),
     eqnPat ws r (clauseQC c tblG vsC Srt.bool prem (litT false, [.equals Srt.bool (litT false) notX])) BoolP Ff
       (sAnd (altPC c tblG vsC (litT false, [.equals Srt.bool (litT false) notX])) (sTop BoolP)),
     eqnPat ws r (lastQC c tblG vsC Srt.bool prem xsC) BoolP Ff BNG] := by decide +kernel

/-- The functional sentence: `∃v. v = f(K0)`, K0 the variable `k0`. -/
def tblF : VarTable := tableOf ax162.sortVars ax162.pattern
def rF : EVar := tblF.ev (sortVarKey Rv)
def vF : EVar := tblF.ev (evarKey (evar "Val" bS))
def k0 : EVar := tblF.ev (evarKey (evar "K0" bS))
def fHead : P := sym (.symbol "Lblf")
def tsF : List (EVar × EVar × P) := [(x0, k0, BoolP)]

theorem fnl_shape : fnlItem.pat =
    fnlPat (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF vF BoolP
      (appList fHead (tsF.map fun t => .evar t.2.1)) := by
  show (trAxiom [] [] ⟨0, "kernel", Faithful.Model.functionalAxiom c fFn⟩).pat = _
  rw [← ax162_eq, trAxiom_fnlPat [] [] 0 "kernel" ax162 (F := ap "Lblf" [ev "K0" bS]) (v := evar "Val" bS) rfl rfl]
  decide +kernel

/-- The facts of the indices and literals the lemmas read. -/
theorem idx_facts :
    Ff = appList fHead (tsF.map fun t => .evar t.1) ∧ (tsF.map (·.2.1)).Nodup ∧ rF ∉ tsF.map (·.2.1) ∧
      vF ∉ tsF.map (·.2.1) ∧ vF ≠ rF ∧ sortGuard r ∈ ws ∧ (x0 ∈∈ inhOf BoolP) ∈ ws ∧
      BoolP = TieFRRead.boolP ∧ tblG.ev (sortVarKey Rv) = r ∧
      bodyT = sAnd (.evar xB) (sEquals BoolP BoolP (.evar xB) notT) ∧ ensT = sTop BoolP ∧
      notT.isFreeEvar xB = false ∧ tr ⟨tblG, []⟩ (Term.kore c vsC notX) = notT ∧
      trSort tblG (srtOf c Srt.bool) = BoolP ∧ trSort tblG R = .evar r ∧
      (∀ b, altPC c tblG vsC (litT b, [.equals Srt.bool (litT b) notX]) = den c (bool b)) ∧
      (∀ b, tr ⟨tblG, []⟩ (Term.kore c vsC (litT b)) = den c (bool b)) ∧
      (∀ b, tr ⟨tblG, []⟩ (Cond.kore c vsC R (.equals Srt.bool (litT b) notX)) =
        sEquals BoolP (.evar r) (den c (bool b)) notT) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b => ?_, fun b => ?_, fun b => ?_⟩ <;>
    first | decide +kernel | (cases b <;> decide +kernel)

/-! ## In a model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A condition `t = u` at Bool, read: t and u agree on Bool. -/
def CG (I : Interpretation KoreAML.Sym M) (β : M) : Cond → Valuation M → Prop
  | .equals _ t u, e => ∀ z, Inh I β z →
      ((tr ⟨tblG, []⟩ (Term.kore c vsC t)).interpret I e z ↔ (tr ⟨tblG, []⟩ (Term.kore c vsC u)).interpret I e z)
  | _, _ => True

omit [Inhabited M] in
/-- Bool's sort, its reading, and the facts of the model `TieEX`'s lemmas read, from `NodeFacts`. -/
theorem bool_facts (F : HoldsShape.NodeFacts c I) :
    ∃ β, IsSort I β ∧ (∀ (e : Valuation M) a, BoolP.interpret I e a ↔ a = β) ∧ SortAt I BoolP β ∧
      (∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.bool)).interpret I e a ↔ a = β) := by
  obtain ⟨β, hβ, hβd⟩ := TieFRRead.boolDen_of F
  obtain ⟨-, -, -, -, -, -, -, hBP, -, -, -, -, -, hS, -⟩ := idx_facts
  have hd : ∀ (e : Valuation M) a, BoolP.interpret I e a ↔ a = β := fun e a => by rw [hBP]; exact hβd e a
  exact ⟨β, hβ, hd, ⟨hd, hβ, by rw [hBP]; rfl⟩, fun e a => by rw [hS]; exact hd e a⟩

/-- **The readings `TieEX` asks, proved from the patterns**: the alternatives lie in Bool, each
condition `b = notBool(X)` reads as `CG`, and the body at B := b's element with `⊤` holds the
alternative of b where its condition holds. -/
theorem readings_facts (F : HoldsShape.NodeFacts c I) {β : M} (hβ : IsSort I β)
    (hd : ∀ (e : Valuation M) a, BoolP.interpret I e a ↔ a = β) :
    (∀ e m, At I ws (tblG.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ a,
      (altPC c tblG vsC x).interpret I e a → Inh I β a) ∧
    (∀ e m, At I ws (tblG.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ p ∈ x.2,
      ((tr ⟨tblG, []⟩ (Cond.kore c vsC R p)).interpret I e m ↔ CG I β p e)) ∧
    (∀ e m, At I ws (tblG.ev (sortVarKey Rv)) e m → ∀ (b : Bool) (y : M),
      (den c (bool b)).interpret I e y → ∀ a, Inh I β a →
      (bodyT.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
        ∃ x ∈ xsOf b, (altPC c tblG vsC x).interpret I e a ∧ altGC (CG I β) x e)) := by
  obtain ⟨-, -, -, -, -, hr, -, hBP, hrG, hbody, hens, hfree, hnot, -, -, halt, hlit, hcnd⟩ := idx_facts
  have hD := F.defOK
  have hinB : ∀ (e : Valuation M) a, (inhOf BoolP).interpret I e a ↔ Inh I β a :=
    fun e a => interp_inhOf_of (hd e)
  -- the element of a literal, and that it is in Bool
  have hlitE : ∀ (b : Bool) (e : Valuation M), ∃ y, (∀ m, (den c (bool b)).interpret I e m ↔ m = y) ∧ Inh I β y := by
    intro b e
    obtain ⟨y, hy, hin⟩ := bool_lit F b e
    rw [← hBP, hinB] at hin
    exact ⟨y, hy, hin⟩
  have hmem : ∀ b, ∀ x ∈ xsOf b, x = (litT b, [.equals Srt.bool (litT b) notX]) := by
    intro b x hx; simpa [xsOf] using hx
  have hmemC : ∀ x ∈ xsOf true ++ xsOf false, ∃ b, x = (litT b, [.equals Srt.bool (litT b) notX]) := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact ⟨true, hmem true x h⟩
    · exact ⟨false, hmem false x h⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e m _ x hx a ha
    obtain ⟨b, rfl⟩ := hmemC x hx
    rw [halt] at ha
    obtain ⟨y, hy, hyβ⟩ := hlitE b e
    rw [(hy a).mp ha]; exact hyβ
  · intro e m hat x hx p hp
    rw [hrG] at hat
    obtain ⟨b, rfl⟩ := hmemC x hx
    simp only [List.mem_singleton] at hp
    subst hp
    have hrS := isSort_of_at hD hr hat
    rw [hcnd, interp_sEquals hD F.ceilDef (hd e) (fun _ => interp_evar) hβ hrS]
    show _ ↔ ∀ z, Inh I β z → ((tr ⟨tblG, []⟩ (Term.kore c vsC (litT b))).interpret I e z ↔
      (tr ⟨tblG, []⟩ (Term.kore c vsC notX)).interpret I e z)
    rw [hlit, hnot]
    exact ⟨fun h => h.2, fun h => ⟨hat.2, h⟩⟩
  · intro e m hat b y hy a ha
    obtain ⟨y0, hy0, -⟩ := hlitE b e
    have hyy : ∀ z, (den c (bool b)).interpret I e z ↔ z = y := fun z => by
      rw [hy0 z, (hy0 y).mp hy]
    have hnotU : ∀ z, notT.interpret I (updX e xB y) z ↔ notT.interpret I e z := fun z =>
      only_free_var_relevant _ _ _ _ (fun x hx => by
        have hxB : x ≠ xB := by rintro rfl; rw [hfree] at hx; cases hx
        exact Function.update_noteq hxB _ _) (fun _ _ => rfl) z
    have hdU : ∀ a', BoolP.interpret I (updX e xB y) a' ↔ a' = β := hd _
    rw [hbody, hens, interp_sAnd, interp_evar, interp_sEquals hD F.ceilDef hdU hdU hβ hβ,
      interp_sTop hD (by rw [hBP]; rfl), hinB]
    simp only [Function.update_same, interp_evar, hnotU]
    constructor
    · rintro ⟨⟨rfl, -, h⟩, -⟩
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
      · rw [halt]; exact (hyy a).mpr rfl
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        show ∀ z, Inh I β z → ((tr ⟨tblG, []⟩ (Term.kore c vsC (litT b))).interpret I e z ↔
          (tr ⟨tblG, []⟩ (Term.kore c vsC notX)).interpret I e z)
        rw [hlit, hnot]
        intro z hz
        rw [hyy z]
        exact h z hz
    · rintro ⟨x, hx, hxa, hxg⟩
      rw [hmem b x hx] at hxa hxg
      rw [halt] at hxa
      have hay := (hyy a).mp hxa
      refine ⟨⟨hay, ha, fun z hz => ?_⟩, ha⟩
      have := hxg _ (List.mem_singleton_self _)
      change ∀ z, Inh I β z → ((tr ⟨tblG, []⟩ (Term.kore c vsC (litT b))).interpret I e z ↔
          (tr ⟨tblG, []⟩ (Term.kore c vsC notX)).interpret I e z) at this
      rw [hlit, hnot] at this
      rw [← hyy z]
      exact this z hz

/-- **The sentence with f's functional sentence and `boolClosed` gives each of `Γ`'s three items
for f**, from `NodeFacts c I`. -/
theorem gamma_of_text (F : HoldsShape.NodeFacts c I) (hcl : I ⊧ᴵ Faithful.boolClosed c)
    (hT : I ⊧ᴵ textItem.pat) (hF : I ⊧ᴵ fnlItem.pat) :
    ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK c fFn), I ⊧ᴵ it.pat := by
  intro it hit
  have hmem : it.pat ∈ (Faithful.kernelItems (Faithful.fnEquationsK c fFn)).map (·.pat) :=
    List.mem_map.mpr ⟨it, hit, rfl⟩
  rw [gamma_shape] at hmem
  rw [text_shape] at hT
  rw [fnl_shape] at hF
  obtain ⟨β, hβ, hd, hSA, hσ⟩ := bool_facts F
  obtain ⟨hin, hcond, hbody⟩ := readings_facts F hβ hd
  obtain ⟨hFf, hnd, hrk, hvk, hvr, hr, hx0, hBP, hrG, -⟩ := idx_facts
  have hG := guardsOf_pred F.defOK ax246
  have hone : ∀ e m, At I ws r e m → ∃ y, Inh I β y ∧ ∀ a, Inh I β a → (Ff.interpret I e a ↔ a = y) := by
    intro e m hat
    rw [hFf]
    exact one_of_fnl F.defOK F.ceilDef hSA.den hSA.isSort hr hF (Closed.sym _) hnd hrk hvk hvr rfl
      (fun t ht => by
        simp only [tsF, List.mem_singleton] at ht
        subst ht
        exact ⟨hx0, by rw [hBP]; exact Closed.sym _⟩) hat
  have hT' := hT; have hone' := hone; have hr' := hr
  rw [← hrG] at hT' hone' hr'
  have hcl1 := fun (x : Term × List Cond) (hx : x ∈ xsOf true ++ xsOf false) =>
    ex_clause_of_text F hcl (tbl := tblG) (vs := vsC) (s := Srt.bool) (CG := CG I β)
      hSA hG hr' hσ hin hcond hbody hT' hone' hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> rw [h]
  · have := hcl1 _ (List.mem_cons_self ..); rwa [hrG] at this
  · have := hcl1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)); rwa [hrG] at this
  · have := ex_none_of_text F hcl (tbl := tblG) (vs := vsC) (s := Srt.bool) (CG := CG I β)
      hSA hG hr' hσ hin hcond hbody hT' hone' BNG
    rwa [hrG] at this

/-- **`Γ`'s three items for f and `boolClosed` give the sentence**, from `NodeFacts c I`, without
f's functional sentence. -/
theorem text_of_gamma (F : HoldsShape.NodeFacts c I) (hcl : I ⊧ᴵ Faithful.boolClosed c)
    (h : ∀ it ∈ Faithful.kernelItems (Faithful.fnEquationsK c fFn), I ⊧ᴵ it.pat) : I ⊧ᴵ textItem.pat := by
  have hs : ∀ φ ∈ (Faithful.kernelItems (Faithful.fnEquationsK c fFn)).map (·.pat), I ⊧ᴵ φ := by
    intro φ hφ
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hφ
    exact h it hit
  rw [gamma_shape] at hs
  rw [text_shape]
  obtain ⟨β, hβ, hd, hSA, hσ⟩ := bool_facts F
  obtain ⟨hin, hcond, hbody⟩ := readings_facts F hβ hd
  obtain ⟨-, -, -, -, -, hr, -, -, hrG, -⟩ := idx_facts
  have hr' := hr
  rw [← hrG] at hr'
  have hk : ∀ x ∈ xsOf true ++ xsOf false, I ⊧ᴵ eqnPat ws (tblG.ev (sortVarKey Rv))
      (clauseQC c tblG vsC Srt.bool prem x) BoolP Ff (sAnd (altPC c tblG vsC x) (sTop BoolP)) := by
    intro x hx
    rw [hrG]
    rcases List.mem_append.mp hx with hx | hx <;> simp only [xsOf, List.mem_singleton] at hx <;> subst hx
    · exact hs _ (List.mem_cons_self ..)
    · exact hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hn : I ⊧ᴵ eqnPat ws (tblG.ev (sortVarKey Rv)) (lastQC c tblG vsC Srt.bool prem (xsOf true ++ xsOf false))
      BoolP Ff BNG := by
    rw [hrG]
    exact hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have := ex_text_of_split F hcl (tbl := tblG) (vs := vsC) (s := Srt.bool) (CG := CG I β)
    (body := bodyT) (ensT := ensT) (xB := xB) (SR := srtOf c Srt.bool)
    hSA (guardsOf_pred F.defOK ax246) hr' hσ hσ hin hcond hbody hk hn
  rwa [hrG] at this

end

end KCore.TieEXTest

#check @KCore.TieEXTest.gamma_of_text
#check @KCore.TieEXTest.text_of_gamma
/-- info: 'KCore.TieEXTest.gamma_of_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEXTest.gamma_of_text
/-- info: 'KCore.TieEXTest.text_of_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEXTest.text_of_gamma
/-- info: 'KCore.TieEX.ex_clause_of_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEX.ex_clause_of_text
/-- info: 'KCore.TieEX.ex_none_of_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEX.ex_none_of_text
/-- info: 'KCore.TieEX.ex_text_of_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEX.ex_text_of_split
/-- info: 'KCore.TieEX.exists_bool_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEX.exists_bool_iff
