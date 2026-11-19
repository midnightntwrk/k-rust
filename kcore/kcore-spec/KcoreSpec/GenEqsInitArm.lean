/-
  The account's arm for the cell tree's initializers (`Parse.initEqnOK`, `Parse.initFunctionalOK`)
  against the model of GenEqsInit.lean: the partial functions `G` the names denote are read from
  the text's equations, and each equation the arm takes holds at values in that model.

  - **The right side at values (`armVal`).** A KORE right side, its variables given values (`σ`),
    is read three ways: a value (`some (some v)`), nothing (`some none`: a hook whose graph has no
    value there, or a name whose `G` has none, or an application with an argument that denotes
    nothing), or not read (`none`: any other symbol, a sort argument, a literal that is not a
    value's own text, a result of no sort). Variables, literals, `inj`, constructors of the
    semantics, interpreted hooks, the names, and a collection sort's unit at no argument (the
    empty collection, `armCollUnit`, whose KORE the unit applied to nothing is) are read. `inj{A, B}` over a value of `A` is its
    normalised injection into `B` (`injNormal`: over a value that is itself an injection, the
    inner value injected into `B`).
  - **What it reads holds (`armVal_sound`).** In a model `InitModel c N ar G`, the translation of
    the right side with its variables replaced by the values' KORE terms (`armSubst`) denotes the
    value read, or nothing: by `InitModel.ctor`, `injN`, `hookV`, `hookE`, `name`, `name_none`,
    `val` (the empty collection, `armCollUnit_den`),
    in a semantics with `coreOK` (`injN` reads the theory's injection coherence).
  - **`G` from the text (`armG`, `armG_fix`).** The names of `order` are given their equation's
    right side read through `G` itself, by recursion on the position in `order`, which lists every
    name before the names whose right side applies it (`armRankB`); the other names are given
    `base` (`armBase`: a sort's projection `projFn`, the getter the last argument of the top cell).
    At the bottom-up order the reading is a fixed point: `G L ws` is the right side's value at
    `ws` read through `G`.
  - **The names (`armNameB`, `armName_free`).** A name that is no symbol of the registry or of
    the semantics, or a sort's projection whose equation the arm for sort projections accepts
    (`predProjAcc`, which at a registry-numbered name decides that no premise names it): free of
    the theory and resolving to no symbol, so `model_with_inits_arm` patches it.
  - **The arm (`init_arm_eqn`, `init_arm_functional`).** For an equation `e` of the text that
    `initEqnOK` takes for the cell `x`: its patterns are distinct variables `xs` and it is the only
    equation of `L = x.initLabel c`, so `G L` is its right side's reading. At values `ws` of a sort
    where the right side is read, the equation `L(ws) = rhs[ws/xs]` holds, and `G L ws` is the
    reading. Where `initFunctionalOK` takes the `functional` axiom of `L` and the right side has a
    value at `ws`, the axiom's instance `∃y:s. y = L(ws)` holds.

  What acceptance gives and what reading adds: `initEqnOK` gives the equation's shape (distinct
  variable patterns, the only equation of its symbol, no condition) and which symbols its right
  side applies; it checks no sort or arity. Reading the right side at the values (`armVal` is not
  `none`) checks the rest: every symbol applied is a constructor, an interpreted hook, a name or a
collection sort's unit,
  at arguments of its sorts and arity.
-/
import KcoreSpec.GenEqsInit
import KcoreSpec.InjValue

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

open Faithful.Model

/-! ## Reading a right side at values -/

theorem if_neg_arm {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) : (if p then a else b) = b := by
  simp [h]

/-- The numbered sort of a KORE sort: the sort whose `KoreAML.srt` it is. -/
def armSrt (c : Semantics) (S : Kore.KSort) : Option Srt :=
  (kernelSorts c).find? fun s => decide (KoreAML.srt (c.sortName s) = S)

/-- The value a domain value is: the literal read at its sort, where the value's own KORE is the
text's (`GroundTerm.kore`) and the value has a sort. -/
def armDv (c : Semantics) (S : Kore.KSort) (text : String) : Option GroundTerm :=
  match armSrt c S with
  | some s => match Parse.lit? s text with
    | some l =>
      if decide ((GroundTerm.dv s l).kore c = .dv S text) && (c.sortOf (.dv s l)).isSome then some (.dv s l)
      else none
    | none => none
  | none => none

/-- The value `σ` gives the variable `x`, the first. -/
def armLookup (σ : List (Kore.EVar × GroundTerm)) (x : Kore.EVar) : Option GroundTerm :=
  (σ.find? fun p => decide (p.1 = x)).map (·.2)

/-- The variables paired with values, in order. -/
def armZip (xs : List Kore.EVar) (ws : List GroundTerm) : List (Kore.EVar × GroundTerm) := xs.zip ws

/-- Some argument denotes nothing. -/
def armEmpty : List (Option (Option GroundTerm)) → Bool
  | [] => false
  | some none :: _ => true
  | _ :: rs => armEmpty rs

/-- The arguments' values, where each has one. -/
def armWs : List (Option (Option GroundTerm)) → Option (List GroundTerm)
  | [] => some []
  | some (some w) :: rs => (armWs rs).map (w :: ·)
  | _ :: _ => none

/-- The empty collection of the collection sort of `k`, the value its unit `k.unit()` denotes
(`GroundTerm.kore` writes the empty collection as the unit applied to nothing). -/
def armCollUnit (k : CollSig) : GroundTerm :=
  match k.kind with
  | .map | .rangeMap => .map k.sort []
  | .set => .set k.sort []
  | .list => .list k.sort []

/-- The symbol named `h` at the values `ws`: a name (`isN`) at `ar h` of them, `G`'s value or
nothing; a constructor of `c`, the value it builds; an interpreted hook at arguments of its sorts,
its graph's value, or nothing where the graph has none and the text is not silent; the unit of a
collection sort of `c` (the collection sort's own, `collOf`) at no argument, the empty collection
where it has a sort. -/
def armHead (c : Semantics) (isN : String → Bool) (ar : String → Nat) (G : String → List GroundTerm → Option GroundTerm)
    (h : String) (ws : List GroundTerm) : Option (Option GroundTerm) :=
  if isN h then
    if ws.length = ar h then
      match G h ws with
      | some v => if (c.sortOf v).isSome then some (some v) else none
      | none => some none
    else none
  else match c.ctorSigs.find? (fun k => c.symName k.name == h) with
  | some k => if (c.sortOf (.ctor k.name ws)).isSome then some (some (.ctor k.name ws)) else none
  | none => match hookSigs.find? (fun k => c.symName k.name == h) with
    | some k =>
      if iteSort? h = none ∧ c.sortsOf ws = some k.args then
        match hook k.name ws with
        | some (some v) => if (c.sortOf v).isSome then some (some v) else none
        | some none => if silent k.name ws = false then some none else none
        | none => none
      else none
    | none => match c.colls.find? (fun k => c.symName k.unit == h) with
      | some k =>
        if ws.isEmpty && decide (c.collOf k.sort = some k) && (c.sortOf (armCollUnit k)).isSome then
          some (some (armCollUnit k))
        else none
      | none => none

/-- An application of the symbol named `h` to arguments read as `rs`: nothing where one denotes
nothing, else `armHead` at their values. -/
def armApp (c : Semantics) (isN : String → Bool) (ar : String → Nat) (G : String → List GroundTerm → Option GroundTerm)
    (h : String) (rs : List (Option (Option GroundTerm))) : Option (Option GroundTerm) :=
  if armEmpty rs then some none
  else match armWs rs with
    | some ws => armHead c isN ar G h ws
    | none => none

/-- `inj{A, B}` applied to one argument read as `r`: where `r` is a value of `A` and `A` a subsort
of `B`, its normalised injection into `B` (`injNormal`); nothing where `r` is nothing. -/
def armInj (c : Semantics) (ss : List Kore.KSort) (rs : List (Option (Option GroundTerm))) : Option (Option GroundTerm) :=
  match ss, rs with
  | [A, B], [r] => match armSrt c A, armSrt c B, r with
    | some a, some b, some (some w) =>
      if decide (c.sortOf w = some a) && c.subsorts.contains (a, b) then some (some (injNormal a b w)) else none
    | some _, some _, some none => some none
    | _, _, _ => none
  | _, _ => none

mutual
  /-- **The reading of a KORE right side at the values `σ` of its variables**: a value, nothing, or
  not read (`none`). -/
  def armVal (c : Semantics) (isN : String → Bool) (ar : String → Nat) (G : String → List GroundTerm → Option GroundTerm)
      (σ : List (Kore.EVar × GroundTerm)) : Kore.Pattern → Option (Option GroundTerm)
    | .var (.evar x) => (armLookup σ x).map some
    | .dv S text => (armDv c S text).map some
    | .app h ss ps =>
      if h.ident.name == "inj" then armInj c ss (armVals c isN ar G σ ps)
      else if ss.isEmpty then armApp c isN ar G h.ident.name (armVals c isN ar G σ ps)
      else none
    | _ => none
    termination_by structural p => p
  /-- `armVal` of each pattern. -/
  def armVals (c : Semantics) (isN : String → Bool) (ar : String → Nat) (G : String → List GroundTerm → Option GroundTerm)
      (σ : List (Kore.EVar × GroundTerm)) : List Kore.Pattern → List (Option (Option GroundTerm))
    | [] => []
    | p :: ps => armVal c isN ar G σ p :: armVals c isN ar G σ ps
    termination_by structural ps => ps
end

mutual
  /-- The pattern with its variables replaced by the KORE terms of the values `σ` gives them. -/
  def armSubst (c : Semantics) (σ : List (Kore.EVar × GroundTerm)) : Kore.Pattern → Kore.Pattern
    | .var (.evar x) => match armLookup σ x with
      | some w => w.kore c
      | none => .var (.evar x)
    | .app h ss ps => .app h ss (armSubsts c σ ps)
    | p => p
    termination_by structural p => p
  /-- `armSubst` of each pattern. -/
  def armSubsts (c : Semantics) (σ : List (Kore.EVar × GroundTerm)) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => armSubst c σ p :: armSubsts c σ ps
    termination_by structural ps => ps
end

mutual
  /-- The names of the symbols a pattern applies, through applications. -/
  def armHeads : Kore.Pattern → List String
    | .app h _ ps => h.ident.name :: armHeadsL ps
    | _ => []
    termination_by structural p => p
  def armHeadsL : List Kore.Pattern → List String
    | [] => []
    | p :: ps => armHeads p ++ armHeadsL ps
    termination_by structural ps => ps
end

mutual
  /-- The element variables of a pattern, through applications. -/
  def armVars : Kore.Pattern → List Kore.EVar
    | .var (.evar x) => [x]
    | .app _ _ ps => armVarsL ps
    | _ => []
    termination_by structural p => p
  def armVarsL : List Kore.Pattern → List Kore.EVar
    | [] => []
    | p :: ps => armVars p ++ armVarsL ps
    termination_by structural ps => ps
end

/-- The equation's left side: its symbol at its patterns. -/
def armLhs (e : Parse.RawEqn) : Kore.Pattern := .app ⟨⟨e.fn⟩⟩ [] e.pats

/-! ## What the reading reads holds -/

/-- The reading `r` holds of the pattern `ψ`: it denotes exactly the value, or nothing. -/
def ArmDen (c : Semantics) (I : Interpretation KoreAML.Sym Elem) : Option (Option GroundTerm) → KoreAML.P → Prop
  | some (some v), ψ => DenV c I ψ v
  | some none, ψ => DenE I ψ
  | none, _ => True

/-- `ArmDen` pairwise. -/
def ArmDens (c : Semantics) (I : Interpretation KoreAML.Sym Elem) :
    List (Option (Option GroundTerm)) → List KoreAML.P → Prop
  | [], [] => True
  | r :: rs, ψ :: ψs => ArmDen c I r ψ ∧ ArmDens c I rs ψs
  | _, _ => False

theorem armDens_ws {c : Semantics} {I : Interpretation KoreAML.Sym Elem} :
    ∀ {rs : List (Option (Option GroundTerm))} {ψs : List KoreAML.P}, ArmDens c I rs ψs →
      ∀ {ws : List GroundTerm}, armWs rs = some ws → All2 (DenV c I) ψs ws
  | [], [], _, ws, h => by cases h; exact .nil
  | some (some w) :: rs, ψ :: ψs, ⟨h1, hs⟩, ws, h => by
    simp only [armWs, Option.map_eq_some_iff] at h
    obtain ⟨ws', h', rfl⟩ := h
    exact .cons h1 (armDens_ws hs h')
  | some none :: _, _ :: _, _, _, h => by simp [armWs] at h
  | none :: _, _ :: _, _, _, h => by simp [armWs] at h
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

theorem armDens_empty {c : Semantics} {I : Interpretation KoreAML.Sym Elem} :
    ∀ {rs : List (Option (Option GroundTerm))} {ψs : List KoreAML.P}, ArmDens c I rs ψs →
      armEmpty rs = true → ∃ ψ ∈ ψs, DenE I ψ
  | [], [], _, h => by simp [armEmpty] at h
  | some none :: _, ψ :: _, ⟨h1, _⟩, _ => ⟨ψ, List.mem_cons_self .., h1⟩
  | some (some _) :: rs, _ :: ψs, ⟨_, hs⟩, h => by
    obtain ⟨ψ, hψ, he⟩ := armDens_empty (rs := rs) hs (by simpa [armEmpty] using h)
    exact ⟨ψ, List.mem_cons_of_mem _ hψ, he⟩
  | none :: rs, _ :: ψs, ⟨_, hs⟩, h => by
    obtain ⟨ψ, hψ, he⟩ := armDens_empty (rs := rs) hs (by simpa [armEmpty] using h)
    exact ⟨ψ, List.mem_cons_of_mem _ hψ, he⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem armSrt_spec {c : Semantics} {S : Kore.KSort} {a : Srt} (h : armSrt c S = some a) :
    S = KoreAML.srt (c.sortName a) := by
  have := List.find?_some h
  exact (of_decide_eq_true this).symm

/-- The translation of an application without sort arguments. -/
theorem armDen_app0 (h : Kore.SymbolIdent) (ps : List Kore.Pattern) :
    KoreAML.den (.app h [] ps) = KoreAML.appList (symP h.ident.name) (ps.map KoreAML.den) := by
  obtain ⟨⟨f⟩⟩ := h
  unfold KoreAML.den
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

theorem armSubsts_eq : ∀ (c : Semantics) (σ : List (Kore.EVar × GroundTerm)) (ps : List Kore.Pattern),
    armSubsts c σ ps = ps.map (armSubst c σ)
  | _, _, [] => by rw [armSubsts]; rfl
  | c, σ, p :: ps => by rw [armSubsts, armSubsts_eq c σ ps]; rfl

theorem armVals_eq (c : Semantics) (isN : String → Bool) (ar : String → Nat)
    (G : String → List GroundTerm → Option GroundTerm) (σ : List (Kore.EVar × GroundTerm)) :
    ∀ ps : List Kore.Pattern, armVals c isN ar G σ ps = ps.map (armVal c isN ar G σ)
  | [] => by rw [armVals]; rfl
  | p :: ps => by rw [armVals, armVals_eq c isN ar G σ ps]; rfl

/-- **An injection over a value of a subsort denotes its normalised injection** (`injNormal`), the
value itself an injection or not: the theory's injection coherence (`den_inj_gs`,
`den_injNormal_gs`). -/
theorem InitModel.injN {c : Semantics} {N : String → Prop} {ar : String → Nat}
    {G : String → List GroundTerm → Option GroundTerm} {I : Interpretation KoreAML.Sym Elem}
    (hM : InitModel c N ar G I) (hc : c.coreOK = true) {a b : Srt} {ψ : KoreAML.P} {w : GroundTerm}
    (h : DenV c I ψ w) (hw : c.sortOf w = some a) (hab : (a, b) ∈ c.subsorts) :
    DenV c I (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b), ψ]) (injNormal a b w) := by
  haveI : OvlOK c := ovlOK_of_core hc
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hM.sat φ (Or.inl (Or.inl hφ))
  have htr := CE.injValue_subsorts_trans hc
  have hs := sortOf_injNormal htr hab hw
  refine ⟨⟨b, hs⟩, fun ρ m => ?_⟩
  rw [inj_den a b (fun m => (h.2 ρ m).trans (hM.vals w a hw ρ m).symm) m]
  rw [Faithful.den_inj_gs hI hw ρ m, ← Faithful.den_injNormal_gs hI htr hab hw ρ m]
  exact hM.vals _ b hs ρ m

/-- **The empty collection's KORE is its unit applied to nothing**, where the collection sort of
`k` is `k`'s own. -/
theorem armCollUnit_den {c : Semantics} {k : CollSig} (hk : c.collOf k.sort = some k) :
    den c (armCollUnit k) = KoreAML.appList (symP (c.symName k.unit)) [] := by
  have hs : ∀ kd, c.collSig kd k.sort = k := fun kd => by unfold Semantics.collSig; rw [hk]; rfl
  unfold armCollUnit den
  cases k.kind <;>
    simp only [GroundTerm.kore, GroundTerm.koreEntries, GroundTerm.koreElems, hs, KoreAML.ap, armDen_app0,
      List.map_nil]

section Sound

variable {c : Semantics} {N : String → Prop} {ar : String → Nat} {G : String → List GroundTerm → Option GroundTerm}
  {I : Interpretation KoreAML.Sym Elem} (hM : InitModel c N ar G I) {isN : String → Bool}
  (hN : ∀ n, isN n = true → N n) {σ : List (Kore.EVar × GroundTerm)}
  (hσ : ∀ x w, armLookup σ x = some w → ∃ s, c.sortOf w = some s)
include hM hN

/-- **`armHead` holds** of the symbol applied to patterns that denote the values. -/
theorem armHead_sound {h : String} {ψs : List KoreAML.P} {ws : List GroundTerm} (hws : All2 (DenV c I) ψs ws) :
    ArmDen c I (armHead c isN ar G h ws) (KoreAML.appList (symP h) ψs) := by
  unfold armHead
  by_cases hn : isN h = true
  · rw [if_pos_walk hn]
    by_cases hl : ws.length = ar h
    · rw [if_pos_walk hl]
      cases hg : G h ws with
      | some v =>
        dsimp only
        by_cases hs : (c.sortOf v).isSome = true
        · rw [if_pos_walk hs]
          exact hM.name (hN h hn) hws hl hg (Option.some_get hs).symm
        · rw [if_neg_arm hs]; trivial
      | none => exact hM.name_none (hN h hn) hws hl hg
    · rw [if_neg_arm hl]; trivial
  · rw [if_neg_arm hn]
    cases hk : c.ctorSigs.find? (fun k => c.symName k.name == h) with
    | some k =>
      dsimp only
      have hkn : c.symName k.name = h := by have := List.find?_some hk; exact beq_iff_eq.mp this
      by_cases hs : (c.sortOf (.ctor k.name ws)).isSome = true
      · rw [if_pos_walk hs]
        have := hM.ctor (f := k.name) hws (Option.some_get hs).symm
        rwa [hkn] at this
      · rw [if_neg_arm hs]; trivial
    | none =>
      dsimp only
      cases hk' : hookSigs.find? (fun k => c.symName k.name == h) with
      | none =>
        dsimp only
        cases hu : c.colls.find? (fun k => c.symName k.unit == h) with
        | none => trivial
        | some k =>
          dsimp only
          have hkn : c.symName k.unit = h := by have := List.find?_some hu; exact beq_iff_eq.mp this
          by_cases hcu : (ws.isEmpty && decide (c.collOf k.sort = some k) && (c.sortOf (armCollUnit k)).isSome) = true
          · rw [if_pos_walk hcu]
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hcu
            obtain ⟨⟨rfl, hco⟩, hso⟩ := hcu
            cases hws
            have hd := hM.val (Option.some_get hso).symm
            rwa [armCollUnit_den hco, hkn] at hd
          · rw [if_neg_arm hcu]; trivial
      | some k =>
        dsimp only
        have hkn : c.symName k.name = h := by have := List.find?_some hk'; exact beq_iff_eq.mp this
        have hmem : k ∈ hookSigs := List.mem_of_find?_eq_some hk'
        by_cases hc : iteSort? h = none ∧ c.sortsOf ws = some k.args
        · rw [if_pos_walk hc]
          cases hr : hook k.name ws with
          | none => trivial
          | some r =>
            cases r with
            | some v =>
              dsimp only
              by_cases hs : (c.sortOf v).isSome = true
              · rw [if_pos_walk hs]
                have := hM.hookV_irs hmem hws hc.2 hr (Option.some_get hs).symm
                rwa [hkn] at this
              · rw [if_neg_arm hs]; trivial
            | none =>
              dsimp only
              by_cases hsil : silent k.name ws = false
              · rw [if_pos_walk hsil]
                have := hM.hookE_irs hmem hws hc.2 hr hsil
                rwa [hkn] at this
              · rw [if_neg_arm hsil]; trivial
        · rw [if_neg_arm hc]; trivial

/-- **`armApp` holds** of the symbol applied to patterns its reading `rs` holds of. -/
theorem armApp_sound {h : String} {rs : List (Option (Option GroundTerm))} {ψs : List KoreAML.P}
    (hrs : ArmDens c I rs ψs) : ArmDen c I (armApp c isN ar G h rs) (KoreAML.appList (symP h) ψs) := by
  unfold armApp
  by_cases he : armEmpty rs = true
  · rw [if_pos_walk he]
    exact DenE.app _ (armDens_empty hrs he)
  · rw [if_neg_arm he]
    cases hw : armWs rs with
    | none => trivial
    | some ws => exact armHead_sound hM hN (armDens_ws hrs hw)

omit hN in
/-- **`armInj` holds** of `inj` applied to patterns its reading holds of. -/
theorem armInj_sound (hc : c.coreOK = true) {ss : List Kore.KSort} {rs : List (Option (Option GroundTerm))} {ψs : List Kore.Pattern}
    (hrs : ArmDens c I rs (ψs.map KoreAML.den)) :
    ArmDen c I (armInj c ss rs) (KoreAML.den (.app ⟨⟨"inj"⟩⟩ ss ψs)) := by
  match ss, rs, ψs, hrs with
  | [A, B], [r], [p], hrs =>
    obtain ⟨ih, -⟩ := hrs
    cases hA : armSrt c A with
    | none => simp only [armInj, hA]; trivial
    | some a =>
      cases hB : armSrt c B with
      | none => simp only [armInj, hA, hB]; trivial
      | some b =>
        simp only [armInj, hA, hB]
        have hden : KoreAML.den (Kore.Pattern.app ⟨⟨"inj"⟩⟩ [A, B] [p]) =
            KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName a),
              KoreAML.Cons.sortP (c.sortName b), KoreAML.den p] := by
          rw [armSrt_spec hA, armSrt_spec hB]
          exact KoreAML.tr_injP (t := []) (c.sortName a) (c.sortName b) p
        rw [hden]
        cases r with
        | none => trivial
        | some r =>
          cases r with
          | some w =>
            dsimp only
            by_cases hs : (decide (c.sortOf w = some a) && c.subsorts.contains (a, b)) = true
            · rw [if_pos_walk hs]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
              exact hM.injN hc ih hs.1 (List.contains_iff_mem.mp hs.2)
            · rw [if_neg_arm hs]; trivial
          | none =>
            exact DenE.app _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ih⟩
  | [], _, _, _ => unfold armInj; trivial
  | [_], _, _, _ => unfold armInj; trivial
  | _ :: _ :: _ :: _, _, _, _ => unfold armInj; trivial
  | [_, _], [], _, _ => unfold armInj; trivial
  | [_, _], _ :: _ :: _, _, _ => unfold armInj; trivial

end Sound

mutual
  /-- **What the reading reads holds**: in the model, the right side with its variables replaced by
  the values' KORE terms denotes the value read, or nothing. -/
  theorem armVal_sound {c : Semantics} {N : String → Prop} {ar : String → Nat}
      {G : String → List GroundTerm → Option GroundTerm} {I : Interpretation KoreAML.Sym Elem}
      (hM : InitModel c N ar G I) (hc : c.coreOK = true) {isN : String → Bool} (hN : ∀ n, isN n = true → N n)
      {σ : List (Kore.EVar × GroundTerm)} (hσ : ∀ x w, armLookup σ x = some w → ∃ s, c.sortOf w = some s) :
      ∀ p : Kore.Pattern,
      ArmDen c I (armVal c isN ar G σ p) (KoreAML.den (armSubst c σ p))
    | .var (.evar x) => by
      rw [armVal, armSubst]
      cases hx : armLookup σ x with
      | none => trivial
      | some w =>
        obtain ⟨s, hs⟩ := hσ x w hx
        exact hM.val hs
    | .var (.svar _) => trivial
    | .dv S text => by
      show ArmDen c I ((armDv c S text).map some) (KoreAML.den (.dv S text))
      cases hd : armDv c S text with
      | none => trivial
      | some v =>
        unfold armDv at hd
        cases ha : armSrt c S with
        | none => rw [ha] at hd; cases hd
        | some s =>
          rw [ha] at hd
          dsimp only at hd
          cases hl : Parse.lit? s text with
          | none => rw [hl] at hd; cases hd
          | some l =>
            rw [hl] at hd
            dsimp only at hd
            by_cases hc : (decide ((GroundTerm.dv s l).kore c = .dv S text) && (c.sortOf (.dv s l)).isSome) = true
            · rw [if_pos_walk hc] at hd
              cases hd
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
              show DenV c I (KoreAML.den (.dv S text)) (.dv s l)
              rw [← hc.1]
              exact hM.val (Option.some_get hc.2).symm
            · rw [if_neg_arm hc] at hd; cases hd
    | .app h ss ps => by
      have ihs := armVals_sound hM hc hN hσ ps
      rw [armVal, armSubst]
      rw [armVals_eq, armSubsts_eq] at ihs ⊢
      by_cases hi : (h.ident.name == "inj") = true
      · rw [if_pos_walk hi]
        have hh : h = ⟨⟨"inj"⟩⟩ := by
          obtain ⟨⟨n⟩⟩ := h
          rw [beq_iff_eq] at hi
          cases hi; rfl
        rw [hh]
        exact armInj_sound hM hc ihs
      · rw [if_neg_arm hi]
        by_cases hs : ss.isEmpty = true
        · rw [if_pos_walk hs]
          have hs' : ss = [] := List.isEmpty_iff.mp hs
          subst hs'
          rw [armDen_app0]
          exact armApp_sound hM hN ihs
        · rw [if_neg_arm hs]; trivial
    | .string _ => trivial
    | .top _ => trivial
    | .bottom _ => trivial
    | .not _ _ => trivial
    | .and _ _ => trivial
    | .or _ _ => trivial
    | .implies _ _ _ => trivial
    | .iff _ _ _ => trivial
    | .exist _ _ _ => trivial
    | .forall _ _ _ => trivial
    | .mu _ _ => trivial
    | .nu _ _ => trivial
    | .ceil _ _ _ => trivial
    | .floor _ _ _ => trivial
    | .equals _ _ _ _ => trivial
    | .in _ _ _ _ => trivial
    | .next _ _ => trivial
    | .rewrites _ _ _ => trivial
    | .leftAssoc _ _ _ => trivial
    | .rightAssoc _ _ _ => trivial
    termination_by structural p => p
  theorem armVals_sound {c : Semantics} {N : String → Prop} {ar : String → Nat}
      {G : String → List GroundTerm → Option GroundTerm} {I : Interpretation KoreAML.Sym Elem}
      (hM : InitModel c N ar G I) (hc : c.coreOK = true) {isN : String → Bool} (hN : ∀ n, isN n = true → N n)
      {σ : List (Kore.EVar × GroundTerm)} (hσ : ∀ x w, armLookup σ x = some w → ∃ s, c.sortOf w = some s) :
      ∀ ps : List Kore.Pattern,
      ArmDens c I (armVals c isN ar G σ ps) ((armSubsts c σ ps).map KoreAML.den)
    | [] => by rw [armVals, armSubsts]; trivial
    | p :: ps => by
      rw [armVals, armSubsts]
      exact ⟨armVal_sound hM hc hN hσ p, armVals_sound hM hc hN hσ ps⟩
    termination_by structural ps => ps
end

/-! ## The reading reads only the names it applies and the variables it holds -/

theorem armHead_congr (c : Semantics) (isN : String → Bool) (ar : String → Nat)
    {G G' : String → List GroundTerm → Option GroundTerm} {h : String} (hG : G h = G' h) (ws : List GroundTerm) :
    armHead c isN ar G h ws = armHead c isN ar G' h ws := by
  unfold armHead; rw [hG]

theorem armApp_congr (c : Semantics) (isN : String → Bool) (ar : String → Nat)
    {G G' : String → List GroundTerm → Option GroundTerm} {h : String} (hG : G h = G' h)
    (rs : List (Option (Option GroundTerm))) : armApp c isN ar G h rs = armApp c isN ar G' h rs := by
  unfold armApp
  split
  · rfl
  · split
    · exact armHead_congr c isN ar hG _
    · rfl

mutual
  /-- **The reading of a pattern is the same under `G, σ` and `G', σ'` that agree on the names it
  applies and the variables it holds.** -/
  theorem armVal_congr (c : Semantics) (isN : String → Bool) (ar : String → Nat)
      {G G' : String → List GroundTerm → Option GroundTerm} {σ σ' : List (Kore.EVar × GroundTerm)} :
      ∀ p : Kore.Pattern, (∀ h ∈ armHeads p, G h = G' h) → (∀ x ∈ armVars p, armLookup σ x = armLookup σ' x) →
        armVal c isN ar G σ p = armVal c isN ar G' σ' p
    | .var (.evar x), _, hv => by
      rw [armVal, armVal, hv x (by rw [armVars]; exact List.mem_singleton_self _)]
    | .var (.svar _), _, _ => rfl
    | .dv _ _, _, _ => rfl
    | .app h ss ps, hh, hv => by
      have ih := armVals_congr c isN ar ps (fun g hg => hh g (by rw [armHeads]; exact List.mem_cons_of_mem _ hg))
        (fun x hx => hv x (by rw [armVars]; exact hx))
      have hG : G h.ident.name = G' h.ident.name := hh _ (by rw [armHeads]; exact List.mem_cons_self ..)
      rw [armVal, armVal, ih, armApp_congr c isN ar hG]
    | .string _, _, _ => rfl
    | .top _, _, _ => rfl
    | .bottom _, _, _ => rfl
    | .not _ _, _, _ => rfl
    | .and _ _, _, _ => rfl
    | .or _ _, _, _ => rfl
    | .implies _ _ _, _, _ => rfl
    | .iff _ _ _, _, _ => rfl
    | .exist _ _ _, _, _ => rfl
    | .forall _ _ _, _, _ => rfl
    | .mu _ _, _, _ => rfl
    | .nu _ _, _, _ => rfl
    | .ceil _ _ _, _, _ => rfl
    | .floor _ _ _, _, _ => rfl
    | .equals _ _ _ _, _, _ => rfl
    | .in _ _ _ _, _, _ => rfl
    | .next _ _, _, _ => rfl
    | .rewrites _ _ _, _, _ => rfl
    | .leftAssoc _ _ _, _, _ => rfl
    | .rightAssoc _ _ _, _, _ => rfl
    termination_by structural p => p
  theorem armVals_congr (c : Semantics) (isN : String → Bool) (ar : String → Nat)
      {G G' : String → List GroundTerm → Option GroundTerm} {σ σ' : List (Kore.EVar × GroundTerm)} :
      ∀ ps : List Kore.Pattern, (∀ h ∈ armHeadsL ps, G h = G' h) → (∀ x ∈ armVarsL ps, armLookup σ x = armLookup σ' x) →
        armVals c isN ar G σ ps = armVals c isN ar G' σ' ps
    | [], _, _ => by rw [armVals, armVals]
    | p :: ps, hh, hv => by
      rw [armVals, armVals,
        armVal_congr c isN ar p (fun h hm => hh h (by rw [armHeadsL]; exact List.mem_append_left _ hm))
          (fun x hm => hv x (by rw [armVarsL]; exact List.mem_append_left _ hm)),
        armVals_congr c isN ar ps (fun h hm => hh h (by rw [armHeadsL]; exact List.mem_append_right _ hm))
          (fun x hm => hv x (by rw [armVarsL]; exact List.mem_append_right _ hm))]
    termination_by structural ps => ps
end

/-! ## `G` from the text's equations -/

/-- The equation of the name `n` of `order`: the text's first equation of `n`. -/
def armLook (order : List String) (eqs : List Parse.RawEqn) (n : String) : Option Parse.RawEqn :=
  if order.contains n then eqs.find? (·.fn == n) else none

/-- **The names' partial functions, read from the text** (`k` the depth of the reading): a name
of `order` is its equation's right side read at the values of its patterns' variables, the names
it applies read one level down; another name is `base`. -/
def armG (c : Semantics) (isN : String → Bool) (ar : String → Nat) (order : List String) (eqs : List Parse.RawEqn)
    (base : String → List GroundTerm → Option GroundTerm) : Nat → String → List GroundTerm → Option GroundTerm
  | 0 => base
  | k + 1 => fun n ws => match armLook order eqs n with
    | some e => match Parse.distinctEVars? e.pats with
      | some xs => (armVal c isN ar (armG c isN ar order eqs base k) (armZip xs ws) e.rhs).join
      | none => none
    | none => base n ws

/-- Every name of `order` comes after the names of `order` its equation's right side applies. -/
def armRankB (order : List String) (eqs : List Parse.RawEqn) : Bool :=
  order.all fun n => match armLook order eqs n with
    | some e => (armHeads e.rhs).all fun h => !order.contains h || decide (order.idxOf h < order.idxOf n)
    | none => true

/-- The arity of a name: the number of patterns of its first equation, 1 where it has none. -/
def armAr (eqs : List Parse.RawEqn) (n : String) : Nat :=
  match eqs.find? (·.fn == n) with
  | some e => e.pats.length
  | none => 1

section Fix

variable (c : Semantics) (isN : String → Bool) (ar : String → Nat) (order : List String) (eqs : List Parse.RawEqn)
  (base : String → List GroundTerm → Option GroundTerm)

theorem armG_base {n : String} (hn : armLook order eqs n = none) :
    ∀ k, armG c isN ar order eqs base k n = base n
  | 0 => rfl
  | k + 1 => funext fun ws => by simp only [armG, hn]

theorem armRank_of {n : String} (hR : armRankB order eqs = true) {e : Parse.RawEqn} (he : armLook order eqs n = some e)
    {h : String} (hh : h ∈ armHeads e.rhs) (ho : order.contains h = true) : order.idxOf h < order.idxOf n := by
  have hn : order.contains n = true := by
    unfold armLook at he; split at he
    · assumption
    · cases he
  have := List.all_eq_true.mp hR n (List.contains_iff_mem.mp hn)
  rw [he] at this
  have := List.all_eq_true.mp this h hh
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  rcases this with h' | h'
  · rw [ho] at h'; cases h'
  · exact h'

theorem armLook_order {n : String} {e : Parse.RawEqn} (he : armLook order eqs n = some e) : order.contains n = true := by
  unfold armLook at he; split at he
  · assumption
  · cases he

/-- The readings at depths `j ≥ k` agree at a name at a position below `k`. -/
theorem armG_stable (hR : armRankB order eqs = true) :
    ∀ k n, order.idxOf n < k → ∀ j, k ≤ j → armG c isN ar order eqs base j n = armG c isN ar order eqs base k n
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, n, hn, j, hj => by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    funext ws
    simp only [armG]
    cases he : armLook order eqs n with
    | none => rfl
    | some e =>
      dsimp only
      cases hx : Parse.distinctEVars? e.pats with
      | none => rfl
      | some xs =>
        dsimp only
        rw [armVal_congr c isN ar e.rhs (G' := armG c isN ar order eqs base k) (σ' := armZip xs ws) ?_ (fun _ _ => rfl)]
        intro h hh
        cases hl : armLook order eqs h with
        | none => rw [armG_base c isN ar order eqs base hl, armG_base c isN ar order eqs base hl]
        | some _ =>
          have hlt := armRank_of order eqs hR he hh (armLook_order order eqs hl)
          exact armG_stable hR k h (by omega) j' (by omega)

/-- **At the depth of `order`'s length, `G` is a fixed point of the reading**: a name of `order`
is its equation's right side read through `G` itself. -/
theorem armG_fix (hR : armRankB order eqs = true) {n : String} {e : Parse.RawEqn}
    (he : armLook order eqs n = some e) {xs : List Kore.EVar} (hx : Parse.distinctEVars? e.pats = some xs)
    (ws : List GroundTerm) :
    armG c isN ar order eqs base order.length n ws =
      (armVal c isN ar (armG c isN ar order eqs base order.length) (armZip xs ws) e.rhs).join := by
  have hn := armLook_order order eqs he
  have hlt : order.idxOf n < order.length := List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp hn)
  obtain ⟨K, hK⟩ : ∃ K, order.length = K + 1 := ⟨order.length - 1, by omega⟩
  rw [hK]
  have hl : armG c isN ar order eqs base (K + 1) n ws =
      (armVal c isN ar (armG c isN ar order eqs base K) (armZip xs ws) e.rhs).join := by
    simp only [armG, he, hx]
  rw [hl, armVal_congr c isN ar e.rhs (G' := armG c isN ar order eqs base (K + 1)) (σ' := armZip xs ws) ?_ (fun _ _ => rfl)]
  intro h hh
  cases hl : armLook order eqs h with
  | none => rw [armG_base c isN ar order eqs base hl, armG_base c isN ar order eqs base hl]
  | some _ =>
    have hlt' := armRank_of order eqs hR he hh (armLook_order order eqs hl)
    exact (armG_stable c isN ar order eqs base hR K h (by omega) (K + 1) (by omega)).symm

end Fix

/-- The values the names outside `order` denote: a sort's projection as its equation defines it on
values (`project:K` the identity, `project:KItem` the item of `kseq(i, dotk)`, `project:X` for
another sort `projFn` at `X`), the counter's getter the last argument of the top cell (its
equation's pattern's). -/
def armBase (c : Semantics) (eqs : List Parse.RawEqn) : String → List GroundTerm → Option GroundTerm
  | n, [w] =>
    if n == Parse.getterName then
      match eqs.find? (·.fn == Parse.getterName) with
      | some e => match e.pats with
        | [.app _ _ args] => argFn topLabel (args.length - 1) w
        | _ => none
      | none => none
    else match KoreAML.Parse.dropPrefix? "Lblproject'Coln'" n with
      | some X =>
        if X == "K" then some w
        else if X == "KItem" then itemFn w
        else (armSrt c (KoreAML.srt X)).bind fun s => projFn c s w
      | none => none
  | _, _ => none

/-! ## The names -/

/-- The name is one the model may give a meaning: no symbol of the registry or of `c` (nor `""`,
`inj`, `Lblite`), or a sort's projection with an equation the arm for sort projections accepts
(`predProjAcc`). -/
def armNameB (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (c : Semantics) (n : String) : Bool :=
  (!(regSymNames ++ c.symNames).contains n && n != "" && n != "inj" && n != "Lblite") ||
  ((KoreAML.Parse.dropPrefix? "Lblproject'Coln'" n).isSome &&
    eqs.any fun e => e.fn == n && Parse.predProjAcc Nm msrc eqs c e)

/-- A sort's projection `armNameB` accepts through an equation of it that `predProjOK?` accepts,
the registry symbol `i` bearing its name, and the decided freeness of `i`. -/
theorem armNameB_of_proj {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics}
    {e : Parse.RawEqn} (he : e ∈ eqs) (hX : (KoreAML.Parse.dropPrefix? "Lblproject'Coln'" e.fn).isSome = true)
    (hp : Parse.predProjOK? Nm msrc eqs c e = some true) {i : Nat} (hi : regSymNames.idxOf? e.fn = some i)
    (hf : freeB c [i] = true) : armNameB Nm msrc eqs c e.fn = true := by
  unfold armNameB
  refine Bool.or_eq_true_iff.mpr (.inr ?_)
  rw [hX, Bool.true_and]
  refine List.any_eq_true.mpr ⟨e, he, ?_⟩
  simp only [beq_self_eq_true, Bool.true_and, Parse.predProjAcc, hp, Parse.regProjFree, hX, ↓reduceIte, hi, hf]

/-- **A name `armNameB` accepts is free of the theory and resolves to no symbol.** -/
theorem armName_free {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics}
    (hc : c.coreOK = true) {n : String} (h : armNameB Nm msrc eqs c n = true) :
    (∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) ∧ unresolvedB c n = true := by
  unfold armNameB at h
  rcases Bool.or_eq_true_iff.mp h with h1 | h2
  · simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h1
    obtain ⟨⟨⟨hu, he⟩, hi⟩, hl⟩ := h1
    exact ⟨nameFree_of_decided c [n] hc (nameFreeB_of_unnumbered c [n] fun m hm => by
        rw [List.mem_singleton.mp hm]; exact ⟨hu, he, hi, hl⟩) n (List.mem_singleton_self _),
      unresolvedB_of_unnumbered c hu he hi hl⟩
  · simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h2
    obtain ⟨hX, e, -, rfl, hp⟩ := h2
    have hfree := (sortProj_free_of_predProjAcc hp hX hc).1
    have hne : e.fn ≠ "inj" ∧ e.fn ≠ "Lblite" := by
      refine ⟨?_, ?_⟩ <;>
        · intro he; rw [he] at hX; revert hX; decide
    have hres : Faithful.Model.resolve c e.fn [] = none := by
      rw [Faithful.Model.resolve_nil, Option.map_eq_none_iff, List.find?_eq_none]
      intro k hk hn
      have he := beq_iff_eq.mp hn
      obtain ⟨φ, hφ, hm⟩ := kernelSym_named hk (by rw [he]; exact iteSort_none_of_proj hX)
      rw [he] at hm
      exact hfree φ hφ hm
    refine ⟨hfree, ?_⟩
    simp only [unresolvedB, hres, Option.isNone_none, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact hne

/-! ## The model -/

/-- **The theory with the equations of symbols it does not name has a model with the semantics'
steps**, for names each free of the theory and resolving to no symbol (`model_with_inits_step`
for names that are no symbol of the semantics; here also a registry-numbered projection no
premise names). -/
theorem model_with_inits_arm (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (N : String → Prop)
    (ar : String → Nat) (G : String → List GroundTerm → Option GroundTerm)
    (hN : ∀ n, N n → (∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) ∧ unresolvedB c n = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, InitModel c N ar G I ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hu : ∀ n, N n → unresolvedB c n = true := fun n hn => (hN n hn).2
  have hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ := fun n hn => (hN n hn).1
  have hm := hypModel_of_fnHyp h hf
  have hfd := (fnModel_of_fnHyp h hf).1
  have hrules := Semantics.ruleFactsHeld_of_core h
  have hsr : ∀ r ∈ c.rules, c.ruleSorted r = true := fun r hr => (hrules r hr).1
  let T : Config c → Config c → Prop := Step c
  have hI : stdI_T c (liftT_ex c T) ⊧ᴵP (Γc c ∪ Γstep c) := by
    refine stdI_T_model_heldCEx c hm (clausePreDecided_of_fnHyp h hf) (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp h) hf) hf.2.2.2.2.2 hrules (liftT_ex c T) ?_ ?_ ?_
    · intro x y hx hy hT
      obtain ⟨r, σ, hb⟩ := step_iff_by.mp (hT hx hy)
      exact ⟨r, σ, stepVBy_of_stepBy hfd hb⟩
    · intro r σ x y hb _ hx hy
      exact step_iff_by.mpr ⟨r, σ, stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb⟩
    · intro r σ x y hb _
      exact ⟨y, σ, fun _ _ => rfl, hb, fun hx hy =>
        step_iff_by.mpr ⟨r, σ, stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb⟩⟩
  have hden := AtT.denGoal (T := liftT_ex c T) hm
  refine ⟨initPatch c (liftT_ex c T) N ar G, ⟨initPatch_model c _ N ar G hu hfree hI, fun v s hv ρ m => ?_,
    fun n hn ws hl hws ρ m => initPatch_apps c _ N ar G hu hfree hden hn hl hws ρ m⟩, fun x y => ?_⟩
  · rw [initPatch_interpret c _ N ar G hu (rooted_val c v) (fun k hk => val_unnamed (hfree k hk) hv) ρ]
    exact hden v s hv ρ m
  · rw [initPatch_step c _ N ar G hu hfree x y]
    exact (liftT_ex_iff T x y).symm.trans (step_iff_stdI_T c hm _ x y)

/-- **The model of the names `armNameB` accepts**, with `G` read from the text (`armG` at the depth
of `order`) and the arities of the text's equations. -/
theorem model_of_arm (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (Nm : Parse.Names) (msrc : String)
    (eqs : List Parse.RawEqn) (names order : List String) (base : String → List GroundTerm → Option GroundTerm)
    (hnames : names.all (armNameB Nm msrc eqs c) = true) :
    ∃ I : Interpretation KoreAML.Sym Elem,
      InitModel c (fun n => names.contains n = true) (armAr eqs)
        (armG c names.contains (armAr eqs) order eqs base order.length) I ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  model_with_inits_arm c h hf _ _ _ fun n hn =>
    armName_free h (List.all_eq_true.mp hnames n (List.contains_iff_mem.mp hn))

/-! ## The arm's equations at values -/

theorem armLookup_cons_self (x : Kore.EVar) (w : GroundTerm) (σ : List (Kore.EVar × GroundTerm)) :
    armLookup ((x, w) :: σ) x = some w := by
  simp [armLookup]

theorem armLookup_cons_ne {x y : Kore.EVar} (hne : y ≠ x) (w : GroundTerm) (σ : List (Kore.EVar × GroundTerm)) :
    armLookup ((x, w) :: σ) y = armLookup σ y := by
  simp [armLookup, Ne.symm hne]

theorem armLookup_mem : ∀ {σ : List (Kore.EVar × GroundTerm)} {x : Kore.EVar} {w : GroundTerm},
    armLookup σ x = some w → (x, w) ∈ σ
  | [], _, _, h => by simp [armLookup] at h
  | (y, v) :: σ, x, w, h => by
    by_cases hxy : y = x
    · subst hxy
      rw [armLookup_cons_self] at h
      cases h
      exact List.mem_cons_self ..
    · rw [armLookup_cons_ne (Ne.symm hxy)] at h
      exact List.mem_cons_of_mem _ (armLookup_mem h)

theorem arm_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {ps : List α} {ys : List β}, ps.mapM f = some ys → All2 (fun p y => f p = some y) ps ys
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact .nil
  | p :: ps, ys, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    exact .cons hy (arm_mapM_some hys)

theorem armDistinct_spec {ps : List Kore.Pattern} {xs : List Kore.EVar}
    (h : Parse.distinctEVars? ps = some xs) :
    ps = xs.map (fun x => .var (.evar x)) ∧ Parse.evarsDistinct xs = true := by
  unfold Parse.distinctEVars? at h
  obtain ⟨ys, hys, h2⟩ := Option.bind_eq_some_iff.mp h
  have hd : Parse.evarsDistinct ys = true ∧ ys = xs := by
    by_cases hc : Parse.evarsDistinct ys = true
    · rw [if_pos_walk hc] at h2; exact ⟨hc, Option.some.inj h2⟩
    · rw [if_neg_arm hc] at h2; cases h2
  obtain ⟨hdis, rfl⟩ := hd
  refine ⟨?_, hdis⟩
  have hf := arm_mapM_some hys
  clear h hys h2 hdis
  induction hf with
  | nil => rfl
  | @cons p y ps' ys' hp _ ih =>
    rw [ih]
    have hpy : p = .var (.evar y) := by
      cases p with
      | var v =>
        cases v with
        | evar x => simp only [Option.some.injEq] at hp; rw [hp]
        | svar _ => simp at hp
      | _ => simp at hp
    rw [hpy]; rfl

/-- Variables, distinct, with the values `ws` substituted: the values' KORE terms. -/
theorem armSubsts_vars (c : Semantics) : ∀ {xs : List Kore.EVar} {ws : List GroundTerm},
    Parse.evarsDistinct xs = true → ws.length = xs.length →
      (xs.map (fun x => Kore.Pattern.var (.evar x))).map (armSubst c (armZip xs ws)) = ws.map (GroundTerm.kore c)
  | [], [], _, _ => rfl
  | x :: xs, w :: ws, hd, hl => by
    simp only [Parse.evarsDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
    obtain ⟨hx, hd⟩ := hd
    simp only [List.map_cons, armZip, List.zip_cons_cons]
    rw [armSubst, armLookup_cons_self]
    congr 1
    rw [← armSubsts_vars c hd (by simpa using hl)]
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    have hne : y ≠ x := by
      rintro rfl
      have : Parse.evarIn xs y = true := List.any_eq_true.mpr ⟨y, hy, decide_eq_true rfl⟩
      rw [hx] at this; cases this
    rw [armSubst, armSubst, armLookup_cons_ne hne]
    rfl
  | [], _ :: _, _, hl => by cases hl
  | _ :: _, [], _, hl => by cases hl

/-- The equation's left side at the values: its symbol applied to their denotations. -/
theorem armLhs_den (c : Semantics) {e : Parse.RawEqn} {xs : List Kore.EVar} (hx : Parse.distinctEVars? e.pats = some xs)
    {ws : List GroundTerm} (hl : ws.length = xs.length) :
    KoreAML.den (armSubst c (armZip xs ws) (armLhs e)) = KoreAML.appList (symP e.fn) (ws.map (den c)) := by
  obtain ⟨hp, hd⟩ := armDistinct_spec hx
  unfold armLhs
  rw [armSubst, armDen_app0, armSubsts_eq, hp, armSubsts_vars c hd hl, List.map_map]
  rfl

theorem armFind_of_unique {L : String} {e : Parse.RawEqn} (hf : e.fn = L) :
    ∀ {eqs : List Parse.RawEqn}, e ∈ eqs → (eqs.filter (·.fn == L)).length = 1 → eqs.find? (·.fn == L) = some e
  | [], he, _ => by cases he
  | a :: rest, he, h1 => by
    by_cases ha : (a.fn == L) = true
    · simp only [List.filter_cons, ha, ↓reduceIte, List.length_cons] at h1
      have hr : rest.filter (·.fn == L) = [] := List.eq_nil_of_length_eq_zero (by omega)
      rcases List.mem_cons.mp he with rfl | hm
      · simp [ha]
      · have : e ∈ rest.filter (·.fn == L) := List.mem_filter.mpr ⟨hm, by simp [hf]⟩
        rw [hr] at this; cases this
    · have ha' : (a.fn == L) = false := by simpa using ha
      simp only [List.filter_cons, ha', Bool.false_eq_true, ↓reduceIte] at h1
      rcases List.mem_cons.mp he with rfl | hm
      · exact absurd (by simp [hf]) ha
      · simp only [List.find?_cons, ha']
        exact armFind_of_unique hf hm h1

/-- What `initEqnOK` gives: the equation is of the initializer's symbol, the only one, and its
patterns are distinct variables. -/
theorem armInitEqnOK_parts {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics} {x : Cell}
    {e : Parse.RawEqn} (h : Parse.initEqnOK Nm msrc eqs c x e = true) :
    e.fn = x.initLabel c ∧ (eqs.filter (·.fn == x.initLabel c)).length = 1 ∧
      ∃ xs, Parse.distinctEVars? e.pats = some xs := by
  unfold Parse.initEqnOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hf, hl⟩, -⟩, -⟩, -⟩, -⟩, hm⟩ := h
  refine ⟨hf, hl, ?_⟩
  cases hx : Parse.distinctEVars? e.pats with
  | none => rw [hx] at hm; cases hm
  | some xs => exact ⟨xs, rfl⟩

/-- Values of a sort denote themselves, each. -/
theorem armVals_den {c : Semantics} {N : String → Prop} {ar : String → Nat}
    {G : String → List GroundTerm → Option GroundTerm} {I : Interpretation KoreAML.Sym Elem}
    (hM : InitModel c N ar G I) : ∀ {ws : List GroundTerm}, (∀ w ∈ ws, ∃ s, c.sortOf w = some s) →
      All2 (DenV c I) (ws.map (den c)) ws
  | [], _ => .nil
  | w :: _, hws =>
    have ⟨_, hs⟩ := hws w (List.mem_cons_self ..)
    .cons (hM.val hs) (armVals_den hM fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))

section Arm

variable {c : Semantics} {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {names order : List String}
  {base : String → List GroundTerm → Option GroundTerm} {I : Interpretation KoreAML.Sym Elem}

/-- The names' partial functions read from the text, at the depth of `order`. -/
abbrev armGOf (c : Semantics) (eqs : List Parse.RawEqn) (names order : List String)
    (base : String → List GroundTerm → Option GroundTerm) : String → List GroundTerm → Option GroundTerm :=
  armG c names.contains (armAr eqs) order eqs base order.length

/-- **An equation the arm takes holds at values where its right side is read.** For the cell `x`
of a name of `order`, an equation `e` of the text that `initEqnOK` takes, and values `ws` of a sort
for its patterns' variables `xs` at which its right side is read as `r`: `G` at `ws` is `r`, and
the equation `L(ws) = rhs[ws/xs]` holds in the model. -/
theorem init_arm_eqn (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order base) I)
    (hc : c.coreOK = true)
    (hR : armRankB order eqs = true) (hord : order.all names.contains = true)
    {x : Cell} {e : Parse.RawEqn} (he : e ∈ eqs) (hok : Parse.initEqnOK Nm msrc eqs c x e = true)
    (hL : order.contains (x.initLabel c) = true) :
    ∃ xs, Parse.distinctEVars? e.pats = some xs ∧
      ∀ ws : List GroundTerm, ws.length = xs.length → (∀ w ∈ ws, ∃ s, c.sortOf w = some s) →
        ∀ r, armVal c names.contains (armAr eqs) (armGOf c eqs names order base) (armZip xs ws) e.rhs = some r →
          armGOf c eqs names order base e.fn ws = r ∧
          (I ⊧ᴵ (KoreAML.den (armSubst c (armZip xs ws) (armLhs e)) ≡ KoreAML.den (armSubst c (armZip xs ws) e.rhs))) := by
  obtain ⟨hf, h1, xs, hx⟩ := armInitEqnOK_parts hok
  refine ⟨xs, hx, fun ws hl hws r hr => ?_⟩
  have hfind := armFind_of_unique hf he h1
  have hlook : armLook order eqs e.fn = some e := by
    unfold armLook; rw [hf, if_pos_walk hL, hfind]
  have hG : armGOf c eqs names order base e.fn ws = r := by
    rw [armGOf, armG_fix c _ _ order eqs base hR hlook hx ws, hr]; rfl
  refine ⟨hG, ?_⟩
  have hN : names.contains e.fn = true := by
    rw [hf]; exact List.all_eq_true.mp hord _ (List.contains_iff_mem.mp hL)
  have har : armAr eqs e.fn = ws.length := by
    unfold armAr; rw [← hf] at hfind; rw [hfind]
    show e.pats.length = ws.length
    rw [hl, (armDistinct_spec hx).1, List.length_map]
  have hσ : ∀ y w, armLookup (armZip xs ws) y = some w → ∃ s, c.sortOf w = some s :=
    fun _ w hy => hws w (List.of_mem_zip (armLookup_mem hy)).2
  have hs := armVal_sound hM hc (fun n hn => hn) hσ e.rhs
  rw [hr] at hs
  have hws' := armVals_den hM hws
  rw [armLhs_den c hx hl]
  cases r with
  | some v =>
    exact hM.eqn (hM.name hN hws' har.symm hG hs.1.choose_spec) hs
  | none =>
    exact hM.eqn_none (hM.name_none hN hws' har.symm hG) hs

/-- **The `functional` axiom the arm takes holds at values where its right side has a value.** For
the cell `x` of a name of `order` whose `functional` axiom `initFunctionalOK` takes (`funcs` the
text's `functional` symbols), the equation `e` it reads and values `ws` of a sort for its
patterns' variables at which the right side is read as the value `v`, of sort `s`: the axiom's
instance `∃y:s. y = L(ws)` holds. -/
theorem init_arm_functional
    (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order base) I)
    (hc : c.coreOK = true) (hR : armRankB order eqs = true) (hord : order.all names.contains = true)
    {funcs : List String} {x : Cell}
    (hok : Parse.initFunctionalOK Nm msrc eqs funcs c x = true) (hL : order.contains (x.initLabel c) = true) :
    ∃ e xs, eqs.find? (·.fn == x.initLabel c) = some e ∧ Parse.distinctEVars? e.pats = some xs ∧
      ∀ ws : List GroundTerm, ws.length = xs.length → (∀ w ∈ ws, ∃ s, c.sortOf w = some s) →
        ∀ v s, armVal c names.contains (armAr eqs) (armGOf c eqs names order base) (armZip xs ws) e.rhs = some (some v) →
          c.sortOf v = some s → ∀ y : EVar,
            I ⊧ᴵ KoreAML.sExists y (KoreAML.Cons.sortP (c.sortName s)) (.evar y ≡ KoreAML.den (armSubst c (armZip xs ws) (armLhs e))) := by
  unfold Parse.initFunctionalOK at hok
  cases hfe : eqs.find? (·.fn == x.initLabel c) with
  | none => rw [hfe] at hok; cases hok
  | some e =>
    rw [hfe] at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨xs, hx, hall⟩ := init_arm_eqn (base := base) hM hc hR hord (List.mem_of_find?_eq_some hfe) hok.1 hL
    refine ⟨e, xs, rfl, hx, fun ws hl hws v s hr hs y => ?_⟩
    obtain ⟨hG, -⟩ := hall ws hl hws _ hr
    have hf := (armInitEqnOK_parts hok.1).1
    have hN : names.contains e.fn = true := by
      rw [hf]; exact List.all_eq_true.mp hord _ (List.contains_iff_mem.mp hL)
    have hfind : eqs.find? (·.fn == e.fn) = some e := by rw [hf]; exact hfe
    have har : armAr eqs e.fn = ws.length := by
      unfold armAr; rw [hfind]
      show e.pats.length = ws.length
      rw [hl, (armDistinct_spec hx).1, List.length_map]
    have hws' := armVals_den hM hws
    rw [armLhs_den c hx hl]
    exact hM.functional (hM.name hN hws' har.symm hG hs) hs y

/-- The reading of the text's equation of `L` (its first) at the values `ws` of its patterns'
variables, `G` read from the text. -/
def armAt (c : Semantics) (eqs : List Parse.RawEqn) (names order : List String)
    (base : String → List GroundTerm → Option GroundTerm) (L : String) (ws : List GroundTerm) :
    Option (Option GroundTerm) :=
  match eqs.find? (·.fn == L) with
  | some e => match Parse.distinctEVars? e.pats with
    | some xs => armVal c names.contains (armAr eqs) (armGOf c eqs names order base) (armZip xs ws) e.rhs
    | none => none
  | none => none

/-- The arm takes the text's equation of `L` for the cell of the tree `cells` whose initializer
`L` is. -/
def armAccB (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (c : Semantics) (cells : List Cell)
    (L : String) : Bool :=
  match cells.find? (·.initLabel c == L), eqs.find? (·.fn == L) with
  | some x, some e => Parse.initEqnOK Nm msrc eqs c x e
  | _, _ => false

/-- **`init_arm_eqn` at the text's equation of `L`**: where the arm takes it and its right side is
read at the values `ws` (of a sort, as many as its patterns) as `r`, `G L ws` is `r` and the
equation `L(ws) = rhs[ws/xs]` holds. -/
theorem init_arm_at (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order base) I)
    (hc : c.coreOK = true)
    (hR : armRankB order eqs = true) (hord : order.all names.contains = true) {cells : List Cell} {L : String}
    (hacc : armAccB Nm msrc eqs c cells L = true) (hL : order.contains L = true) {ws : List GroundTerm}
    (hl : ws.length = armAr eqs L) (hws : ∀ w ∈ ws, ∃ s, c.sortOf w = some s) {r : Option GroundTerm}
    (hr : armAt c eqs names order base L ws = some r) :
    ∃ e xs, eqs.find? (·.fn == L) = some e ∧ Parse.distinctEVars? e.pats = some xs ∧
      armGOf c eqs names order base L ws = r ∧
      (I ⊧ᴵ (KoreAML.den (armSubst c (armZip xs ws) (armLhs e)) ≡ KoreAML.den (armSubst c (armZip xs ws) e.rhs))) := by
  unfold armAccB at hacc
  cases hx : cells.find? (·.initLabel c == L) with
  | none => rw [hx] at hacc; cases hacc
  | some x =>
    cases he : eqs.find? (·.fn == L) with
    | none => rw [hx, he] at hacc; cases hacc
    | some e =>
      rw [hx, he] at hacc
      have hxL : x.initLabel c = L := by have := List.find?_some hx; exact beq_iff_eq.mp this
      have heL : e.fn = L := by have := List.find?_some he; exact beq_iff_eq.mp this
      obtain ⟨xs, hxs, hall⟩ := init_arm_eqn (base := base) hM hc hR hord (List.mem_of_find?_eq_some he) hacc (hxL ▸ hL)
      have hlx : ws.length = xs.length := by
        rw [hl]; unfold armAr; rw [he]
        show e.pats.length = xs.length
        rw [(armDistinct_spec hxs).1, List.length_map]
      unfold armAt at hr
      rw [he] at hr
      dsimp only at hr
      rw [hxs] at hr
      obtain ⟨hG, hq⟩ := hall ws hlx hws r hr
      exact ⟨e, xs, rfl, hxs, heL ▸ hG, hq⟩

/-- **A name at values where `G` has a value denotes it**: `n(ws) = v` holds. -/
theorem arm_name_eqn (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order base) I)
    {n : String} (hn : names.contains n = true) {ws : List GroundTerm} (hl : ws.length = armAr eqs n)
    (hws : ∀ w ∈ ws, ∃ s, c.sortOf w = some s) {v : GroundTerm} (hg : armGOf c eqs names order base n ws = some v)
    {s : Srt} (hs : c.sortOf v = some s) :
    I ⊧ᴵ (KoreAML.appList (symP n) (ws.map (den c)) ≡ den c v) :=
  hM.eqn (hM.name hn (armVals_den hM hws) hl hg hs) (hM.val hs)

/-- **A name at values where `G` has no value denotes nothing**: `n(ws) = ⊥` holds. -/
theorem arm_name_none (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order base) I)
    {n : String} (hn : names.contains n = true) {ws : List GroundTerm} (hl : ws.length = armAr eqs n)
    (hws : ∀ w ∈ ws, ∃ s, c.sortOf w = some s) (hg : armGOf c eqs names order base n ws = none) :
    I ⊧ᴵ (KoreAML.appList (symP n) (ws.map (den c)) ≡ ⊥) :=
  hM.eqn_none (hM.name_none hn (armVals_den hM hws) hl hg) (fun _ _ h => h)

end Arm

end GenEqs

end KCore
