/-
  The fixtures of an equation with existential variables, each with what the text states, the
  clause `Parse.ceRead` reads from it and what `Semantics.clausePlainEx` says of that clause in the
  definition built from the text. Run from the package root:
  `lake env lean -j1 test/ExClauseFixtures.lean`.

  The kompiled texts are read from the cache `kfix.py` keeps (K 7.1.337 kompile's KORE), as
  test/ExClauseReader.lean reads them. `Parse.clausesBody` calls `ceRead` (CE's arm): `today` prints
  what the reader does with the text as it is.

  ## e3-eq-exists-int

  `rule h(X) => ?Z ensures ?Z *Int 2 ==Int X`. kompile rejects `?Z` on an equation (fixture
  `e3-eq-exists-int`, exit 113, "Cannot encode equations with existential variables to KORE"), so
  the text exists in the `#Exists` spelling only (`e3-eq-exists-int-ml`):
  `h(X) => #Exists Z:Int. (Z #And {(Z *Int 2 ==Int X) #Equals true})`.

  From the sentence: `h(x)` is the set of the elements z of Int with `(z *Int 2 ==Int x) = true`.
  Int is not confined, and the predicate equates Z with no term: `Z *Int 2 ==Int X` holds of an
  element the text does not name as well as of a value. So the function's elements are not
  decided by values, and the clause is one to refuse, the reason `existentialEquation`, the sort
  Int.

  - The clause read: `[X:Int, Z:Int]`, `exs [1]`, `rhs Z`, `post (Z *Int 2 ==Int X) = true`; it is
    the hand-built `Int.clZ` (`read is clZ: true`).
  - `clausePlainEx` is false of it in the built definition (Z not confined, `fixedExs` empty), and
    of `clZ` by the kernel on any semantics where Int is not confined (`Int.clZ_no`, at `Int.c`).
  - Today the reader reads the clause and refuses it `existentialEquation` at Int
    (`Parse.clauseRefusal`): no conjunct of the predicate equates Z with a term.

  ## e3-eq-exists-noens

  `rule f(_) => ?B`, f not `total`, no `ensures`. kompile rejects `?B` on an equation, so the text
  exists in the `#Exists` spelling (`e3-eq-exists-noens-ml`): `f(_) => #Exists B:Bool. B`.

  From the sentence: `f(x) = ∃B:Bool. B`, the set of every element of Bool. The text holds no
  `functional` sentence of f, so it allows `f(x)` to have two elements, the elements of `true` and
  of `false`; no clause can state that, and evaluation gives f no result there.

  - The clause read: `[_Gen0:Bool, B:Bool]`, `exs [1]`, `rhs B`, no `ensures`, `post ⊤`. It is the
    hand-built `Noens.clB` (`read is the hand-built clause`). Bool is confined, so
    `clausePlainEx` holds of it in the definition built from the text, and in `Noens.c`
    (`Noens.coreOK`; `Noens.plain`, `clausesPlain` through `Semantics.clausesPlain_iff_ex`).
  - No result (`Noens.no_result`, for any semantics in which `clB` is the only clause of a
    function, at an argument of Bool; `Noens.no_result_c` in `c`). The clause decides at `[x]`
    (`Noens.decides`) and its two instances give `true` and `false` (`Noens.instances`). So no
    value is given by every instance, and no instance gives nothing: neither `Eval.clauseEx` nor
    `Eval.exNone` applies, `clause` and `ensFails` ask for no existential variable, and `rest`
    asks the clause to fail.
  - The owed fact, that the clause has a result at each match where it decides
    (`MatchIndependent`'s second conjunct), is false here (`Noens.no_res`,
    `Noens.not_matchIndependent`), and so is `FnHyp` (`Noens.not_fnHyp`). The account lists the
    fact as owed (section "The account's lines" below) and does not say it holds. No `…_hyp`
    theorem is stated of this text without it.
  - `Γ` holds the text's sentence. In every model of `Γ c` the elements of `f(w)`, for `w` of
    Bool, are exactly the elements of Bool (`Noens.den_f`). In every model of `Γc c` this means
    two distinct elements, those of `true` and of `false` (`Noens.both`). So `Γ` does not state
    more than the text about f. That such a model exists is the text's own fact, read from its
    sentence. It is not kernel-checked: the library builds models from `Eval` under `FnHyp`, and
    `FnHyp` is false here.
  - Today the reader reads the sentence as that clause (`today read`).

  ## The account's lines for a clause holding existential variables

  `Parse.owedExsText` (KcoreSpec/Account.lean), which `kcore account` prints: for each clause with
  `exs` its match obligation, with the fact owed, and the statements stated only under it. No text
  is needed to reach the lines through the reader today (the fixtures' accounts print them), and `owed`
  prints them for the definition built from the patched text with the clause `ceRead` reads put
  in place of the patched one.
  - `e3-eq-exists-partial-ml`, `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`: one line,
    f's clause 0 with `VarB:Bool`; `matchObligationsL` names the clause (B is in no pattern, so the
    patterns do not fix the clause's variables).
  - `e3-eq-exists-noens-ml`, `f(_) => #Exists B:Bool. B`: the same line; the fact is false of
    this clause (its two instances give different values, so it has no result:
    `Noens.not_matchIndependent`), and the line does not say it holds.
  - The patched text itself, whose clauses hold no existential variable: no line.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

namespace ExClauseFixtures

/-! ## The harness -/

/-- The cache of kompiled fixture texts, as test/constructs/kfix.py names it. -/
def cacheDir : IO String := do
  let get := fun (n : String) => do
    match ← IO.getEnv n with
    | some d => pure (if d.isEmpty then none else some d)
    | none => pure none
  if let some d ← get "KCORE_KFIX_CACHE" then return d
  if let some d ← get "XDG_CACHE_HOME" then return s!"{d}/kcore-kfix"
  let home := (← get "HOME").getD "."
  return s!"{home}/.cache/kcore-kfix"

/-- The kompiled text of fixture `n`, its `BUILTIN/` and `FIXTURE/` paths restored to made-up
directories (as `kfix.py accounts` restores them before reading). -/
def load (n : String) : IO Kore.Definition := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  let some l := (t.splitOn "\n").find? (·.startsWith "definition.kore sha256: ")
    | throw (IO.userError s!"{n}: kompile.txt names no sha256")
  let sha := (l.splitOn ": ").getD 1 ""
  let raw ← IO.FS.readFile s!"{← cacheDir}/{sha}.kore"
  let raw := ((raw.replace "BUILTIN/" "/made-up-k/include/kframework/builtin/").replace "FIXTURE/" "/made-up-fx/").replace
    "FIXTURE" "/made-up-fx"
  match Kore.parseDefinition raw with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"{n}: KORE read error {e}")

/-- kompile's exit code on fixture `n`, from its record. -/
def kompileExit (n : String) : IO String := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  return ((t.splitOn "\n").find? (·.startsWith "exit: ")).getD "no exit line"

/-- The text with the right side of each equation of the functions `fns` replaced by the first
argument's variable where the sorts agree, else a literal, so that the definition is built and the
clauses read here can be put in it. -/
def patch (fns : List String) (k : Kore.Definition) : Kore.Definition :=
  let fix := fun (s : Kore.Sentence) => match s with
    | .axiom a => match rawEqn? a, a.pattern with
      | some e, .implies r prem (.equals s1 s2 l (.and s3 [_, en])) =>
        if fns.contains e.fn then
          let rs := (KoreAML.Parse.sortName? s1).getD ""
          let arg := e.pats.findSome? fun p => match p with | .var (.evar x) => some x | _ => none
          let rhs : Kore.Pattern := match arg with
            | some x => if KoreAML.Parse.sortName? x.sort == some rs then .var (.evar x)
                        else if rs == "Int" then .dv s1 "0" else .dv s1 "true"
            | none => if rs == "Int" then .dv s1 "0" else .dv s1 "true"
          Kore.Sentence.axiom { a with pattern := .implies r prem (.equals s1 s2 l (.and s3 [rhs, en])) }
        else s
      | _, _ => s
    | s => s
  match k.modules.reverse with
  | m :: rest => { k with modules := (({ m with sentences := m.sentences.map fix }) :: rest).reverse }
  | [] => k

/-- What the reader does with the text of fixture `n` as it is. -/
def today (n : String) : IO Unit := do
  match Parse.parse (← load n) with
  | .error r => IO.println s!"{n}: today refused {repr r.reason} ({r.detail})"
  | .ok _ => IO.println s!"{n}: today read"

/-- `ceRead` on the one equation of the function `fnName` of fixture `n`; the clause in the
definition built from the patched text, with `clausePlainEx`; and whether it is `expect` (the two
printed alike). -/
def run (n fnName : String) (expect : Clause) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    match Parse.parse (patch [fnName] k), S.eqs.filter (·.fn == fnName) with
    | .error r, _ => IO.println s!"{n}: patched text refused {repr r.reason} {r.detail}"
    | .ok d, [e] =>
      let c := d.sem
      match ceRead E.N e with
      | .error f => IO.println s!"{n} {fnName}: refused {repr f.reason} ({f.detail})"
      | .ok (cl, vs) =>
        IO.println s!"{n} {fnName}: vars {vs.map fun v => v.name ++ ":" ++ v.sort} exs {cl.exs}"
        IO.println s!"  sorts {cl.exs.map fun i => (cl.vars[i]?.map c.sortName).getD "?"}; confined {cl.exs.map fun i => (cl.vars[i]?.map c.confined).getD false}; fixedExs {cl.fixedExs c.confined c.hasValue}; clausePlainEx {c.clausePlainEx cl}"
        IO.println s!"  read is {if toString (repr cl) == toString (repr expect) then "the hand-built clause" else "not the hand-built clause"}"
    | .ok _, es => IO.println s!"{n} {fnName}: {es.length} equations"

/-- The account's lines on the clauses holding existential variables (`Parse.owedExsText`) for the
definition built from the patched text of fixture `n`, and for that definition with the clause
`ceRead` reads from the one equation of `fnName` in place of the patched one (its variables' names
in the presentation); with what `matchObligationsL` names there. -/
def owed (n fnName : String) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    match Parse.parse (patch [fnName] k), S.eqs.filter (·.fn == fnName) with
    | .error r, _ => IO.println s!"{n}: patched text refused {repr r.reason} {r.detail}"
    | .ok d, [e] =>
      match ceRead E.N e with
      | .error f => IO.println s!"{n} {fnName}: refused {repr f.reason} ({f.detail})"
      | .ok (cl, vs) =>
        let here := fun (g : Fn) => d.sem.symName g.label == fnName
        let fns := d.sem.fns.map fun g => if here g then { g with clauses := [cl] } else g
        let pfns := (withPres d.sem.fns d.pres.fns).map fun (g, gp) =>
          if here g then { gp with clauses := gp.clauses.map fun cp => { cp with names := vs.map (·.name) } } else gp
        let d' : Definition := { d with sem := { d.sem with fns }, pres := { d.pres with fns := pfns } }
        IO.println s!"{n}: patched text: {(owedExsText d id).length} lines; with the clause read for {fnName}:"
        for l in owedExsText d' id do IO.println l
        IO.println s!"  matchObligationsL {d'.sem.matchObligationsL.map fun (f, j) => (d'.sem.symName f, j)}"
    | .ok _, es => IO.println s!"{n} {fnName}: {es.length} equations"

/-! ## e3-eq-exists-int -/

namespace Int

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- `h(X) => Z` with `exs = [Z]` and `post := (Z *Int 2 ==Int X) = true`, X and Z of Int. -/
def clZ : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.bool (.app intEq [.app intMul [.var 1, .dv Srt.int (.int 2)], .var 0])
      (.dv Srt.bool (.bool true)) }

/-- A semantics with the cell sorts only: Int is not confined. -/
def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- Z is neither of a confined sort nor fixed by the predicate. -/
theorem clZ_no : c.clausePlainEx clZ = false ∧ c.confined Srt.int = false ∧
    clZ.fixedExs c.confined c.hasValue = [] ∧ clZ.fixedExs (fun _ => true) (fun _ => true) = [] := by
  decide +kernel

end Int

/--
info: e3-eq-exists-int: kompile exit: 113
e3-eq-exists-int-ml: kompile exit: 0
e3-eq-exists-int-ml Lblh: vars [X:Int, Z:Int] exs [1]
  sorts [Int]; confined [false]; fixedExs []; clausePlainEx false
  read is the hand-built clause
e3-eq-exists-int-ml: today refused KCore.Parse.RefusalReason.existentialEquation (VarZ:Int: an existential variable of the right side, of a sort the text leaves unconfined, that no conjunct of its predicate equates with a term: the function's value ranges over elements of Int that no value names)
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println s!"e3-eq-exists-int: kompile {← kompileExit "e3-eq-exists-int"}"
  IO.println s!"e3-eq-exists-int-ml: kompile {← kompileExit "e3-eq-exists-int-ml"}"
  run "e3-eq-exists-int-ml" "Lblh" Int.clZ
  today "e3-eq-exists-int-ml"

/-! ## The account's lines -/

/--
info: e3-eq-exists-partial-ml: patched text: 0 lines; with the clause read for Lblf:
clauses holding existential variables, each a match obligation (the package's match_named, Semantics.matchObligationsL; not a condition of wf: owed of each is MatchIndependent, that its instances are decided and give one result at each match where it decides): 1
      function Lblf, clause 0 at e3-eq-exists-partial-ml.k:4: MatchIndependent open, existential VarB:Bool
sound_hyp and complete_hyp (the package's sound_defn and complete_defn) are stated of this text only under these facts as hypotheses, each named with its function and clause (FnHyp's fourth conjunct; match_named of FnObligations)
  matchObligationsL [(Lblf, 0)]
e3-eq-exists-noens-ml: patched text: 0 lines; with the clause read for Lblf:
clauses holding existential variables, each a match obligation (the package's match_named, Semantics.matchObligationsL; not a condition of wf: owed of each is MatchIndependent, that its instances are decided and give one result at each match where it decides): 1
      function Lblf, clause 0 at e3-eq-exists-noens-ml.k:4: MatchIndependent open, existential VarB:Bool
sound_hyp and complete_hyp (the package's sound_defn and complete_defn) are stated of this text only under these facts as hypotheses, each named with its function and clause (FnHyp's fourth conjunct; match_named of FnObligations)
  matchObligationsL [(Lblf, 0)]
-/
#guard_msgs in
#eval show IO Unit from do
  owed "e3-eq-exists-partial-ml" "Lblf"
  owed "e3-eq-exists-noens-ml" "Lblf"

end ExClauseFixtures

/-- info: 'ExClauseFixtures.Int.clZ_no' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Int.clZ_no

/-! ## e3-eq-exists-noens -/

namespace ExClauseFixtures.Noens

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def fF : Sym := nRegSyms + 4

/-- `f(_) => B` with `exs = [B]`, no `ensures` and `post ⊤`, the argument and B of Bool. -/
def clB : Clause :=
  { vars := [Srt.bool, Srt.bool], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1] }

def fnF : Fn := { label := fF, args := [Srt.bool], result := Srt.bool, clauses := [clB] }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fnF]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem coreOK : c.coreOK = true := by decide +kernel
theorem plain : c.clausesPlain = true := Semantics.clausesPlain_iff_ex.mpr (by decide +kernel)
theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl

section Results

variable {d : Semantics}

/-- The variables of the clause that the right side does not bind and the left side does not hold:
B alone. -/
theorem exsFree_clB : clB.exsFree = [1] := by decide

/-- A substitution giving the argument and B values of Bool is well sorted for the clause. -/
theorem sortedB {σ : Subst} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.bool)
    (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some Srt.bool) : d.WellSorted clB.vars σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | i + 2, hs => simp [clB] at hs

/-- σ with B given `w`. -/
theorem lookup_setB (σ : Subst) (w : GroundTerm) {i : Nat} (hi : i ≠ 1) :
    ((1, w) :: σ).lookup i = σ.lookup i := by
  have : (i == 1) = false := by simpa using hi
  simp [List.lookup, this]

theorem agree_setB (σ : Subst) (w : GroundTerm) : AgreeOff clB.exsFree σ ((1, w) :: σ) := fun i hi =>
  lookup_setB σ w (fun h => hi (by rw [exsFree_clB, h]; exact List.mem_singleton_self _))

/-- An instance of the clause at a well-sorted σ gives B's value: its right-hand side is B, it has
no `ensures`, and its predicate is `⊤`. -/
theorem inst_iff {σ : Subst} {r : Option GroundTerm} (hσ : d.WellSorted clB.vars σ) :
    InstIs d σ clB r ↔ r = σ.lookup 1 := by
  obtain ⟨w, hw, -⟩ := hσ 1 Srt.bool rfl
  constructor
  · intro h
    cases h with
    | fails _ hf =>
      cases hf with
      | ens ht => cases ht
      | post hp => cases hp
      | rhs hr => cases (EvalTerm.var_inv (i := 1) hr).trans hw
    | gives hrhs _ _ => exact EvalTerm.var_inv hrhs
  · intro h
    rw [hw] at h; subst h
    exact .gives (hw ▸ .var) (fun _ ht => nomatch ht) .top

end Results

section NoResult

variable {d : Semantics}

/-- A value of Bool other than `v`. -/
def otherB (v : GroundTerm) : GroundTerm := if v = bool true then bool false else bool true

theorem otherB_ne (v : GroundTerm) : otherB v ≠ v := by
  unfold otherB
  split
  · next h => subst h; decide
  · next h => exact fun e => h e.symm

theorem otherB_sort (v : GroundTerm) : d.sortOf (otherB v) = some Srt.bool := by
  unfold otherB; split
  · exact rmS_sortOf_bool d false
  · exact rmS_sortOf_bool d true

/-- At a match giving the argument a value of Bool, the instances of the clause do not all give
the one value `v`: B given another value of Bool gives that one. -/
theorem not_all_some {σ : Subst} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.bool)
    (v : GroundTerm) : ¬ ∀ σ', AgreeOff clB.exsFree σ σ' → d.WellSorted clB.vars σ' → InstIs d σ' clB (some v) := by
  intro hall
  have h0' : ((1, otherB v) :: σ).lookup 0 = some x := (lookup_setB σ _ (by decide)).trans h0
  have hs := sortedB h0' hx (by simp [List.lookup]) (otherB_sort v)
  have := (inst_iff hs).mp (hall _ (agree_setB σ _) hs)
  simp [List.lookup] at this
  exact otherB_ne v this.symm

/-- No instance of the clause at a well-sorted σ gives nothing. -/
theorem not_inst_none {σ : Subst} (hσ : d.WellSorted clB.vars σ) : ¬ InstIs d σ clB none := fun h => by
  obtain ⟨w, hw, -⟩ := hσ 1 Srt.bool rfl
  have := (inst_iff hσ).mp h
  rw [hw] at this; cases this

/-- **No result**: at an argument of Bool, a function whose one clause is `clB` has no result:
the instances of the clause give `true` and `false`, so neither a value nor none is its result. -/
theorem no_result {f : Sym} {fn : Fn} (hfn : d.lookupFn f = some fn) (hcls : fn.clauses = [clB])
    {x : GroundTerm} (hx : d.sortOf x = some Srt.bool) (r : Option GroundTerm) : ¬ Eval d f [x] r := by
  intro h
  have hcl : ∀ {cl fn'}, d.lookupFn f = some fn' → cl ∈ fn'.clauses → cl = clB := fun h1 h2 => by
    rw [hfn] at h1; cases h1; rw [hcls] at h2; simpa using h2
  cases h with
  | clause hfn' hmem _ _ _ _ _ hex => obtain rfl := hcl hfn' hmem; cases hex
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    have hF := hnone clB (by rw [hcls]; exact List.mem_singleton_self _)
    cases hF with
    | intro hF =>
      have hs : d.WellSorted clB.vars [(1, x), (0, x)] := sortedB rfl hx rfl hx
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ hex => obtain rfl := hcl hfn' hmem; cases hex
  | clauseEx hfn' hmem _ hmatch _ _ _ _ _ _ _ hall =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hmatch
    cases hvs
    exact not_all_some (PatVal.var_inv hv) hx _ hall
  | exNone hfn' hmem _ _ _ _ _ _ hsome hall =>
    obtain rfl := hcl hfn' hmem
    obtain ⟨σ', ha, hs⟩ := hsome
    exact not_inst_none hs (hall σ' ha hs)

end NoResult

/-- **`f` has no result at `true` or `false` in `c`.** -/
theorem no_result_c (b : Bool) (r : Option GroundTerm) : ¬ Eval c fF [bool b] r :=
  no_result lookupF rfl (rmS_sortOf_bool c b) r

/-- The match giving the argument `x`. -/
def sx (x : GroundTerm) : Subst := [(0, x)]

/-- The clause decides at `[x]` under `sx x`, x of Bool: its pattern is a variable, it has no
`requires`, its predicate is `⊤`, and `f` has no other clause. -/
theorem decides {x : GroundTerm} (hx : c.sortOf x = some Srt.bool) : clB.Decides c fnF (sx x) [x] := by
  refine ⟨⟨fun i hi s hs => ?_, .cons (.var rfl) .nil, (fun _ ht => nomatch ht), .top⟩, fun cl' hcl' _ hlt => ?_⟩
  · have : i = 0 := by simp [Clause.univ, clB] at hi; omega
    subst this; cases hs; exact ⟨x, rfl, hx⟩
  · have : cl' = clB := by simpa [fnF] using hcl'
    subst this; exact absurd hlt (Nat.lt_irrefl _)

/-- **The two instances differ**: at the match `sx x`, the instance with B given `b` is well
sorted and gives `b`, for `b` each of `true` and `false`. -/
theorem instances {x : GroundTerm} (hx : c.sortOf x = some Srt.bool) (b : Bool) :
    AgreeOff clB.exsFree (sx x) ((1, bool b) :: sx x) ∧ c.WellSorted clB.vars ((1, bool b) :: sx x) ∧
      clB.Gives c ((1, bool b) :: sx x) (bool b) :=
  ⟨agree_setB _ _, sortedB rfl hx rfl (rmS_sortOf_bool c b), .var, (fun _ ht => nomatch ht), .top⟩

/-- **The clause has no result at a match giving the argument a value of Bool**: no value is given
by every instance, and none by none. -/
theorem no_res {σ : Subst} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : c.sortOf x = some Srt.bool)
    (r : Option GroundTerm) : ¬ clB.Res c σ r := by
  rintro (⟨hex, -⟩ | ⟨-, ⟨σ', v, -, -, -, hall, -⟩ | ⟨-, ⟨σ', ha, hs⟩, hall⟩⟩)
  · cases hex
  · exact not_all_some h0 hx v hall
  · exact not_inst_none hs (hall σ' ha hs)

/-- **The owed fact is false of the clause**: `MatchIndependent` asks a result at each match where
the clause decides, and at `[true]` there is none. -/
theorem not_matchIndependent : ¬ MatchIndependent c clB := fun h => by
  obtain ⟨r, hr⟩ := h.2 (by decide) fF fnF [bool true] (sx (bool true)) lookupF (List.mem_singleton_self _)
    (decides (rmS_sortOf_bool c true))
  exact no_res rfl (rmS_sortOf_bool c true) r hr

/-- **`FnHyp` is false of `c`**: `f` has no result at `[true]`, and its clause's owed fact fails. -/
theorem not_fnHyp : ¬ FnHyp c := fun h => by
  obtain ⟨r, hr⟩ := h.1 fnF (List.mem_singleton_self _) [bool true] (by decide +kernel)
  exact no_result_c true r hr

/-! ### `Γ`'s sentence: `f(x)` is every element of Bool -/

section Model

open Faithful Faithful.Model ML
open KoreAML (VarKey VarTable)

section Raw

variable {d : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The equation of a clause with existential variables and no clause of a smaller priority, read
in a model: the elements of `f(ws)` are the elements of the result sort in the right side. -/
theorem clause_rawEx_fxen (hI : I ⊧ᴵP Γ d) (hnn : NamesNumbered d) (hsc : SortCtx d) [OvlOK d]
    (hph : patHooksApart d = true) {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ' : Subst}
    (hfn : d.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hlow' : lowerClauses fn cl = [])
    (hws : d.sortsOf ws = some fn.args) (hσ' : d.WellSorted cl.vars σ') (hmatch : PatVals d σ' cl.pats ws)
    (hpats : sortsOfTerms d.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : d.condOK cl.vars cl.pre = true) (hokQ : d.condOK cl.vars cl.post = true)
    (hne : cl.exs ≠ []) (hlt : ∀ i ∈ cl.exs, i < cl.vars.length)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreq : cl.req = none) (hpre : cl.pre.isTop = true)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (e0 : Valuation M) :
    ∃ (tbl : VarTable) (e' : Valuation M), Agrees d I tbl (canonVars d cl.vars) σ' e' ∧
      (∀ i < cl.vars.length, canonKey d cl.vars i ∈ tbl) ∧
      (∀ k ∈ KoreAML.varsOf (clauseRhsBody d fn cl), k ∈ tbl) ∧
      ∀ m, (KoreAML.den (symApp d f (GroundTerm.koreList d ws))).interpret I e0 m ↔
        InS I (d.sortName fn.result) m ∧ (KoreAML.tr ⟨tbl, []⟩ (clauseRightEx d fn cl)).interpret I e' m := by
  have hfnm := (lookupFn_spec hfn).1
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => by rw [hreq] at ht; cases ht
  have hpatsN := Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfnm hcl hpats
  have hv := premise_varsCl (c := d) hpats hreqv
  have htr := hsc.trans
  have hmem := clauseEquation_mem (c := d) hcl hlow'
  unfold clauseEquation at hmem
  rw [clauseRhs_eqEx hne hlt] at hmem
  have hP : ∀ k, k ∈ KoreAML.varsOf (withPre d (canonVars d cl.vars) cl (clausePrem d fn cl)) →
      k ∈ KoreAML.varsOf (withPre d (canonVars d cl.vars) cl (clausePrem d fn cl)) := fun _ h => h
  have hVin := clause_keys_inAxEx (prem := withPre d (canonVars d cl.vars) cl (clausePrem d fn cl)) hpats hreqv hocc hP
  obtain ⟨tbl, e', hk, -, hag, hiff⟩ := eqn_atRightEx hI hnn hfn (eqn_item_mem hfnm hmem) hws hσ'
    (fun j s hj => HoldsShape.varsOf_withPre_prem (hv.1 j s hj)) hVin
    (fun k hk => freeOf_withPreCl hpreOK hpats hreqv hk)
    (fun k hk => freeOf_clauseRightEx hrhsv hensv hokQ hk)
    (fun tbl e σr m0 hk hag hX hRv hσr2 hm0 =>
        withPre_holdsCl (premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpatsN hag hX hRv hσr2 hm0
          (fun t ht => by rw [hreq] at ht; cases ht))
          hk (fun hpt => by rw [hpre] at hpt; cases hpt)) e0
  exact ⟨tbl, e', hag, fun i hi => hk _ (hVin i hi),
    fun k hk' => hk _ (varsOf_body_inAxEx (Model.varsOf_existsAll_bodyEx hk' _)), hiff⟩

end Raw

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The elements of `f(w)`. -/
def Fw (I : Interpretation KoreAML.Sym M) (w : GroundTerm) (m : M) : Prop :=
  (KoreAML.den (symApp c fF (GroundTerm.koreList c [w]))).interpret I KoreAML.val0 m

abbrev keyB : VarKey := canonKey c clB.vars 1

/-- The body `B ∧ ⊤` holds a Bool element exactly where it is B's element. -/
theorem body_read (hI : I ⊧ᴵP Γ c) {tbl : VarTable} {e : Valuation M} {m : M}
    (hm : InS I (c.sortName Srt.bool) m) :
    (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fnF clB)).interpret I e m ↔ m = e.evalEvar (tbl.ev keyB) := by
  haveI : OvlOK c := (hypSoundEx_of_coreEx (Semantics.coreOK_iff_ex.mp coreOK)).2.2.2.2.2.2.2.2
  have hD := defOK hI
  obtain ⟨σr, hσr1, -⟩ := sortSing hI (c := c) (s := Srt.bool) (by decide)
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.bool)).interpret I e b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  have hb : clauseRhsBody c fnF clB = .and (srtOf c Srt.bool)
      [Term.kore c (canonVars c clB.vars) (.var 1), reqPat (srtOf c Srt.bool) none] := rfl
  have htop : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c Srt.bool) none)).interpret I e m := by
    simp only [reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e) hσr1).mp ((inS_iff e).mpr hm)
  rw [hb, tr_and2, KoreAML.interp_sAnd, tr_var 1 m]
  exact ⟨fun h => h.1, fun h => ⟨h, htop⟩⟩

/-- **`Γ`'s sentence for `f`**: in a model of `Γ c`, the elements of `f(w)`, w of Bool, are the
elements of Bool: `f(x) = ∃B:Bool. B`, the text's sentence. -/
theorem den_f (hI : I ⊧ᴵP Γ c) {w : GroundTerm} (hw : c.sortOf w = some Srt.bool) (m : M) :
    Fw I w m ↔ InS I (c.sortName Srt.bool) m := by
  have h := Semantics.coreOK_iff_ex.mp coreOK
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (Semantics.ovlCase_of_coreEx h)
  have hD := defOK hI
  have hσ' : c.WellSorted clB.vars [(1, bool true), (0, w)] := sortedB rfl hw rfl (rmS_sortOf_bool c true)
  obtain ⟨tbl, e', -, hkeys, -, hiff⟩ := clause_rawEx_fxen hI hnn hsc hph (f := fF) (fn := fnF) (cl := clB)
    (ws := [w]) (σ' := [(1, bool true), (0, w)]) lookupF (List.mem_singleton_self _) (by decide)
    (by simp [Semantics.sortsOf, hw, fnF]) hσ' (.cons (.var rfl) .nil)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    KoreAML.val0
  refine (hiff m).trans ⟨fun h => h.1, fun hm => ⟨hm, ?_⟩⟩
  have hlt : ∀ i ∈ clB.exs, i < clB.vars.length := by decide
  have hndB := binders_nodupEx hkeys hlt (l := clB.exs) (by decide)
  have hsB := binders_sortEx (c := c) (vars := clB.vars) hlt
  have hsort : ∀ i ∈ clB.exs,
      ((canonVars c clB.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (clB.vars.getD i 0)) :=
    fun i hi => by rw [canonVars_getD c (hlt i hi)]; rfl
  obtain ⟨σr, hσr1, -⟩ := sortSing hI (c := c) (s := Srt.bool) (by decide)
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.bool)).interpret I e' b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  let e'' : Valuation M := ⟨Function.update e'.evalEvar (tbl.ev keyB) m, e'.evalSvar⟩
  have hB : e''.evalEvar (tbl.ev keyB) = m := Function.update_same _ _ _
  unfold clauseRightEx
  rw [tr_and2, KoreAML.interp_sAnd]
  refine ⟨existsAll_intro_at hD (clauseExBinders c clB) e' e'' _ hndB hsB (fun x hx => ?_) rfl
    (fun b hb n hn => ?_) ((body_read hI hm).mpr hB.symm), ?_⟩
  · exact Function.update_noteq (hx _ (List.mem_singleton_self _)) _ _
  · have hb1 : b = ((canonVars c clB.vars).getD 1 default).kore := by simpa [clauseExBinders, clB] using hb
    subst hb1
    rw [hsort 1 (by decide)] at hn
    rw [← srt_inj hn]
    exact hB ▸ hm
  · show (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c Srt.bool) none)).interpret I e' _
    simp only [reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl)]
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c Srt.bool))).interpret I e' _
    rw [KoreAML.interp_inhOf_of hS]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e') hσr1).mp ((inS_iff e').mpr hm)

/-- **Both elements**: in a model of `Γc c`, the elements of `true` and of `false` are elements of
`f(w)`, and they are two. -/
theorem both (hIc : I ⊧ᴵP Γc c) {w : GroundTerm} (hw : c.sortOf w = some Srt.bool) :
    Fw I w (elemOf c I (bool true)) ∧ Fw I w (elemOf c I (bool false)) ∧
      elemOf c I (bool true) ≠ elemOf c I (bool false) := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have ht := elemOf_spec hI (rmS_sortOf_bool c true) KoreAML.val0
  have hf := elemOf_spec hI (rmS_sortOf_bool c false) KoreAML.val0
  refine ⟨(den_f hI hw _).mpr ((inS_iff KoreAML.val0).mp ht.2), (den_f hI hw _).mpr ((inS_iff KoreAML.val0).mp hf.2),
    fun he => ?_⟩
  have F := HoldsShape.nodeFacts_of_core coreOK hIc
  have := F.apart (rmS_sortOf_bool c true) (rmS_sortOf_bool c false) KoreAML.val0 _ ((ht.1 _).mpr rfl)
    ((hf.1 _).mpr he)
  exact absurd this (by decide)

end Model

/-! ### Through the reader -/

/--
info: e3-eq-exists-noens-ml: kompile exit: 0
e3-eq-exists-noens-ml Lblf: vars ['Unds'Gen0:Bool, B:Bool] exs [1]
  sorts [Bool]; confined [true]; fixedExs []; clausePlainEx true
  read is the hand-built clause
e3-eq-exists-noens-ml: today read
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println s!"e3-eq-exists-noens-ml: kompile {← kompileExit "e3-eq-exists-noens-ml"}"
  run "e3-eq-exists-noens-ml" "Lblf" clB
  today "e3-eq-exists-noens-ml"

end ExClauseFixtures.Noens

/-- info: 'ExClauseFixtures.Noens.no_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.no_result
/-- info: 'ExClauseFixtures.Noens.no_result_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.no_result_c
/-- info: 'ExClauseFixtures.Noens.decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.decides
/-- info: 'ExClauseFixtures.Noens.instances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.instances
/-- info: 'ExClauseFixtures.Noens.no_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.no_res
/-- info: 'ExClauseFixtures.Noens.not_matchIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.not_matchIndependent
/-- info: 'ExClauseFixtures.Noens.not_fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.not_fnHyp
/-- info: 'ExClauseFixtures.Noens.den_f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.den_f
/-- info: 'ExClauseFixtures.Noens.both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.both
/-- info: 'ExClauseFixtures.Noens.coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.coreOK
/-- info: 'ExClauseFixtures.Noens.plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Noens.plain

/-! ## pred-rhs-top-cut: e3-ml-eq-rhs-not-ceil-and, the term's position cut at the top

`rule h(X) => X #And #Not(#Ceil(f(X) #And g(X)))` with `rule f(X) => X requires X >Int 0` and
`rule g(X) => 0 -Int X requires X <Int 5`.

From the sentences: `h(x)` is x where `f(x)` and `g(x)` have no common element, and empty where they
have one. At 0 < x < 5, `f(x) = x` and `g(x) = 0 - x`, which differ at x = 1, so `h(1) = 1`.

- The clause read (`read`, on the definition built from the text): `[X:Int, #Cut0:Int]`, `exs [1]`,
  `rhs #Cut0`, `post (#Cut0 ∈ X) ∧ ¬∃Z:Int. (⌈Z⌉ ∧ Z ∈ f(X) ∧ Z ∈ g(X))`, Z at the index 2 past
  the clause's variables (`Parse.ceilExCond` keeps the binder inside the predicate, `Parse.ceTopCut`
  cuts the term's position). `clausePlainEx` and `Cond.bound` of its `post` hold (`plainEx`).
- `h_1`: `h(1) = 1`, by `Eval.clauseEx` at #Cut0 := 1, every H: `f(1) = 1` and `g(1) = -1` have no
  common element, so the negated `\ceil` is true, and every other instance has `#Cut0 ∈ X` false.
- The hand-written variant whose g is f, `h(X) => X #And #Not(#Ceil(f(X) #And f(X)))` (`clTop fF`,
  in `cV`, the definition with h's clause replaced): at 0 < n, `f(n) = n` is a common element, so
  the negated `\ceil` is false at every instance and `h(n)` has the result none by `Eval.exNone`
  (`hV_none`, every H); `hsome`, the one well-sorted instance `Eval.exNone` asks, is #Cut0 := 0,
  a value of Int.
-/

namespace ExClauseFixtures.TopCut

open GroundTerm

definition_of defn from "f2-examples/e3-ml-eq-rhs-not-ceil-and.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def gS : Sym := 385
def hS : Sym := 386

/-- `f(X) => X requires X >Int 0`. -/
def clFf : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := some (.app intGt [.var 0, .dv Srt.int (.int 0)]),
    rhs := .var 0, ens := none }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clFf] }

/-- `g(X) => 0 -Int X requires X <Int 5`. -/
def clGg : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := some (.app intLt [.var 0, .dv Srt.int (.int 5)]),
    rhs := .app intSub [.dv Srt.int (.int 0), .var 0], ens := none }

def fnG : Fn := { label := gS, args := [Srt.int], result := Srt.int, clauses := [clGg] }

/-- `¬∃Z:Int. (⌈Z⌉ ∧ Z ∈ f(X) ∧ Z ∈ u(X))`, Z at the index 2. -/
def notCeilAnd (u : Sym) : Cond :=
  .not (.ex Srt.int (.and (.ceil Srt.int (.var 2))
    (.and (.mem Srt.int (.var 2) (.app fF [.var 0])) (.mem Srt.int (.var 2) (.app u [.var 0])))))

/-- `h(X) => X #And #Not(#Ceil(f(X) #And u(X)))`, read with the term's position the existential
variable #Cut0: `exs [1]`, `rhs #Cut0`, `post (#Cut0 ∈ X) ∧ ¬∃Z. (⌈Z⌉ ∧ Z ∈ f(X) ∧ Z ∈ u(X))`. -/
def clTop (u : Sym) : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .and (.mem Srt.int (.var 1) (.var 0)) (notCeilAnd u) }

def fnH : Fn := { label := hS, args := [Srt.int], result := Srt.int, clauses := [clTop gS] }

/-- **The reading**: the text's functions are `f`, `g` and `h`, each with its one clause. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

/-- #Cut0 is of the unconfined Int and fixed by `#Cut0 ∈ X`, and the kept binder is admitted. -/
theorem plainEx : c.clausePlainEx (clTop gS) = true ∧ Cond.bound c 2 (clTop gS).post = true ∧
    c.confined Srt.int = false := by decide +kernel

/-- The variant whose g is f: h's clause `clTop fF`. -/
def fnHV : Fn := { label := hS, args := [Srt.int], result := Srt.int, clauses := [clTop fF] }

/-- The text's definition with h's clause replaced by the variant's. -/
noncomputable def cV : Semantics := { c with fns := [fnF, fnG, fnHV] }

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn hS = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupFV : cV.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupHV : cV.lookupFn hS = some fnHV := by rw [Semantics.lookupFn_eq]; rfl
theorem ctors : c.isCtor intGt = false ∧ c.isCtor intLt = false ∧ c.isCtor intSub = false ∧
    c.isCtor fF = false ∧ c.isCtor gS = false := by decide +kernel
theorem fnsPlain : c.isParam fF = false ∧ c.isParam gS = false := by decide +kernel
theorem hooks : isHook intGt = true ∧ isHook intLt = true ∧ isHook intSub = true ∧ isHook fF = false ∧
    isHook gS = false := by decide +kernel

section Clauses

variable {d : Semantics} {σ : Subst}

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem holds_cast {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' :=
  e ▸ h

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem sameResult_self (v : GroundTerm) : sameResult (some v) (some v) = true := sameResult_some.mpr rfl

theorem sameResult_eq_some {r : Option GroundTerm} {v : GroundTerm} (h : sameResult r (some v) = true) :
    r = some v := by
  cases r with
  | none => cases h
  | some w => rw [sameResult_some.mp h]

theorem varOf {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) : EvalTerm d σ (.var i) (some v) := by
  rw [← h]; exact .var

theorem sorted1 {a : Srt} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a) :
    d.WellSorted [a] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp at hs

theorem sorted2 {a b : Srt} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some b) : d.WellSorted [a, b] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | i + 2, hs => simp at hs

theorem call_var {f : Sym} (hc : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    {i : Nat} {w : GroundTerm} (hl : σ.lookup i = some w) {r : Option GroundTerm} (h : Eval d f [w] r) :
    EvalTerm d σ (.app f [.var i]) r :=
  .call (vs := [w]) hc hh (.cons .var .nil) (by rw [hl]; rfl) h hp

theorem hookGt (n : Int) : d.hookRes intGt [int n, int 0] = some (some (bool (decide (n > 0)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intGt]; rfl)

theorem hookLt (n : Int) : d.hookRes intLt [int n, int 5] = some (some (bool (decide (n < 5)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intLt]; rfl)

theorem hookSub (n : Int) : d.hookRes intSub [int 0, int n] = some (some (int (0 - n))) :=
  Semantics.hookRes_of_value (by rw [hook_intSub]; rfl)

/-- **`f(n)` is n where 0 < n**, by its one clause. -/
theorem valueF (hgt : d.isCtor intGt = false) (hl : d.lookupFn fF = some fnF) {n : Int} (hn : 0 < n) :
    Eval d fF [int n] (some (int n)) :=
  .clause (fn := fnF) (cl := clFf) (σ := [(0, int n)]) hl (List.mem_singleton_self _)
    (sorted1 rfl (rmS_sortOf_int d n)) (.cons (.var rfl) .nil)
    (fun t ht => by
      cases ht
      exact .hook hgt hooks.1 (rs := [some (int n), some (int 0)]) (.cons .var (.cons .dv .nil))
        (fun vs hvs => by cases hvs; rw [hookGt, decide_eq_true (show n > 0 from hn)])
        (fun hn => by cases hn))
    .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => nomatch ht) .top

/-- **`g(n)` is `0 - n` where n < 5**, by its one clause. -/
theorem valueG (hlt5 : d.isCtor intLt = false) (hsub : d.isCtor intSub = false) (hl : d.lookupFn gS = some fnG)
    {n : Int} (hn : n < 5) : Eval d gS [int n] (some (int (0 - n))) :=
  .clause (fn := fnG) (cl := clGg) (σ := [(0, int n)]) hl (List.mem_singleton_self _)
    (sorted1 rfl (rmS_sortOf_int d n)) (.cons (.var rfl) .nil)
    (fun t ht => by
      cases ht
      exact .hook hlt5 hooks.2.1 (rs := [some (int n), some (int 5)]) (.cons .var (.cons .dv .nil))
        (fun vs hvs => by cases hvs; rw [hookLt, decide_eq_true hn])
        (fun hn => by cases hn))
    .top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl
    (.hook hsub hooks.2.2.1 (rs := [some (int 0), some (int n)]) (.cons .dv (.cons .var .nil))
      (fun vs hvs => by cases hvs; exact hookSub n) (fun hn => by cases hn))
    (fun t ht => nomatch ht) .top

/-- The truth value of the body `⌈Z⌉ ∧ Z ∈ f(X) ∧ Z ∈ u(X)` where Z has the value z and `f(X)`,
`u(X)` the results rf, ru. -/
def bodyVal (z rf ru : Option GroundTerm) : Bool :=
  z.isSome && ((z.isSome && sameResult z rf) && (z.isSome && sameResult z ru))

theorem bodyVal_true {z : GroundTerm} {rf ru : Option GroundTerm} :
    bodyVal (some z) rf ru = true ↔ sameResult (some z) rf = true ∧ sameResult (some z) ru = true := by
  simp [bodyVal]

/-- **The negated `\ceil` has a truth value**: true where no value of Int is both results, at any σ
giving X the value n, given the results of `f(n)` and `u(n)`. -/
theorem holds_notCeilAnd {u : Sym} (hfC : d.isCtor fF = false) (hfP : d.isParam fF = false)
    (huC : d.isCtor u = false) (huH : isHook u = false) (huP : d.isParam u = false)
    {n : Int} (h0 : σ.lookup 0 = some (int n)) {rf ru : Option GroundTerm}
    (hf : Eval d fF [int n] rf) (hu : Eval d u [int n] ru) (b : Bool)
    (hb : b = true ↔ ∃ z, d.sortOf z = some Srt.int ∧ sameResult (some z) rf = true ∧ sameResult (some z) ru = true) :
    Holds d 2 σ (notCeilAnd u) (!b) := by
  refine .not (.ex (fun σ' => bodyVal (σ'.lookup 2) rf ru) (fun σ' he => ?_) ?_)
  · have h0' : σ'.lookup 0 = some (int n) := (he.1 0 (by decide)).trans h0
    exact .and (.ceil .var) (.and (.mem .var (call_var hfC hooks.2.2.2.1 hfP h0' hf))
      (.mem .var (call_var huC huH huP h0' hu)))
  · rw [hb]
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      refine ⟨(2, z) :: σ, ⟨fun i hi => lkNe _ _ (by omega), fun j s hj => ?_⟩, ?_⟩
      · match j, hj with
        | 0, hj => cases hj; exact ⟨z, lkSelf _ _ _, hz⟩
        | j + 1, hj => simp at hj
      · show bodyVal (((2, z) :: σ : Subst).lookup 2) rf ru = true
        rw [lkSelf]; exact bodyVal_true.mpr ⟨h1, h2⟩
    · rintro ⟨σ', he, hg⟩
      have hg : bodyVal (σ'.lookup 2) rf ru = true := hg
      obtain ⟨z, hz2, hz⟩ := he.2 0 Srt.int rfl
      simp only [Nat.add_zero] at hz2
      rw [hz2] at hg
      exact ⟨z, hz, bodyVal_true.mp hg⟩

end Clauses

/-! ### The text: `h(1) = 1` -/

section Text

variable {d : Semantics} {σ : Subst}

/-- What a semantics must give for the text's three clauses to be read in it. -/
structure Reads (d : Semantics) : Prop where
  gt : d.isCtor intGt = false
  lt : d.isCtor intLt = false
  sub : d.isCtor intSub = false
  fC : d.isCtor fF = false
  fP : d.isParam fF = false
  gC : d.isCtor gS = false
  gP : d.isParam gS = false
  lookF : d.lookupFn fF = some fnF
  lookG : d.lookupFn gS = some fnG
  lookH : d.lookupFn hS = some fnH

/-- At X := 1 no value of Int is both `f(1) = 1` and `g(1) = -1`. -/
theorem post1 (hd : Reads d) (h0 : σ.lookup 0 = some (int 1)) :
    Holds d 2 σ (clTop gS).post
      (((σ.lookup 1).isSome && sameResult (σ.lookup 1) (some (int 1))) && !false) :=
  .and (.mem .var (varOf h0))
    (holds_notCeilAnd hd.fC hd.fP hd.gC hooks.2.2.2.2 hd.gP h0 (valueF hd.gt hd.lookF (by decide))
      (valueG hd.lt hd.sub hd.lookG (by decide)) false
      ⟨fun h => absurd h (by decide), fun ⟨_, _, h1, h2⟩ =>
        absurd ((sameResult_some.mp h1).symm.trans (sameResult_some.mp h2)) (by simp [int])⟩)

/-- **`h(1) = 1`**, by `Eval.clauseEx` at #Cut0 := 1: every other instance has `#Cut0 ∈ X` false. -/
theorem valueH1 (hd : Reads d) : Eval d hS [int 1] (some (int 1)) := by
  have hs : d.WellSorted (clTop gS).vars [(1, int 1), (0, int 1)] :=
    sorted2 rfl (rmS_sortOf_int d 1) rfl (rmS_sortOf_int d 1)
  refine .clauseEx (fn := fnH) (cl := clTop gS) (σ := [(1, int 1), (0, int 1)]) hd.lookH
    (List.mem_singleton_self _) hs (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (List.cons_ne_nil _ _) (varOf rfl) (fun t ht => nomatch ht)
    (holds_cast (post1 hd rfl) (by simp [List.lookup, sameResult_self])) (fun σ' ha _ => ?_)
  have h0 : σ'.lookup 0 = some (int 1) := ha 0 (by decide)
  cases hb : ((σ'.lookup 1).isSome && sameResult (σ'.lookup 1) (some (int 1))) with
  | true =>
    simp only [Bool.and_eq_true] at hb
    exact .gives (varOf (sameResult_eq_some hb.2)) (fun t ht => nomatch ht)
      (holds_cast (post1 hd h0) (by simp [hb]))
  | false =>
    exact .fails (post1 hd h0) (.post (holds_cast (post1 hd h0) (by simp [hb])))

end Text

/-! ### The variant whose g is f: no value at 0 < n -/

section Variant

variable {d : Semantics} {σ : Subst}

/-- At X := n, 0 < n, `f(n) = n` is a common element of `f(n)` and `f(n)`: the negated `\ceil` is
false. -/
theorem postV (hgt : d.isCtor intGt = false) (hfC : d.isCtor fF = false) (hfP : d.isParam fF = false)
    (hl : d.lookupFn fF = some fnF) {n : Int} (hn : 0 < n) (h0 : σ.lookup 0 = some (int n)) :
    Holds d 2 σ (clTop fF).post
      (((σ.lookup 1).isSome && sameResult (σ.lookup 1) (some (int n))) && !true) :=
  .and (.mem .var (varOf h0))
    (holds_notCeilAnd hfC hfP hfC hooks.2.2.2.1 hfP h0 (valueF hgt hl hn) (valueF hgt hl hn) true
      ⟨fun _ => ⟨int n, rmS_sortOf_int d n, sameResult_self _, sameResult_self _⟩, fun _ => rfl⟩)

/-- **The variant's `h(n)` is none at 0 < n**, by `Eval.exNone`: every instance has its `post`
false; the one instance asked to exist is #Cut0 := 0. -/
theorem noneHV (hgt : d.isCtor intGt = false) (hfC : d.isCtor fF = false) (hfP : d.isParam fF = false)
    (hl : d.lookupFn fF = some fnF) (hlH : d.lookupFn hS = some fnHV) {n : Int} (hn : 0 < n) :
    Eval d hS [int n] none := by
  have hs : d.WellSorted (clTop fF).vars [(1, int 0), (0, int n)] :=
    sorted2 rfl (rmS_sortOf_int d n) rfl (rmS_sortOf_int d 0)
  exact .exNone (fn := fnHV) (cl := clTop fF) (σ := [(1, int 0), (0, int n)]) hlH (List.mem_singleton_self _)
    (List.cons_ne_nil _ _) (hs.at _) (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnHV, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    ⟨_, fun _ _ => rfl, hs⟩
    (fun σ' ha _ => .fails (postV hgt hfC hfP hl hn (ha 0 (by decide)))
      (.post (holds_cast (postV hgt hfC hfP hl hn (ha 0 (by decide))) (by simp))))

end Variant

/-! ### The expectations, for every H -/

theorem reads (H : HookParams) : Reads (cH H) where
  gt := ctors.1
  lt := ctors.2.1
  sub := ctors.2.2.1
  fC := ctors.2.2.2.1
  fP := fnsPlain.1
  gC := ctors.2.2.2.2
  gP := fnsPlain.2
  lookF := by rw [Semantics.lookupFn_withHooks]; exact lookupF
  lookG := by rw [Semantics.lookupFn_withHooks]; exact lookupG
  lookH := by rw [Semantics.lookupFn_withHooks]; exact lookupH

/-- **`h(1) = 1`, for every H.** -/
theorem h_1 (H : HookParams) : Eval (cH H) hS [int 1] (some (int 1)) := valueH1 (reads H)

/-- **The variant's `h(n)` is none at 0 < n, for every H** (`h(X) => X #And #Not(#Ceil(f(X) #And
f(X)))`). -/
theorem hV_none (H : HookParams) {n : Int} (hn : 0 < n) : Eval (cV.withHooks H) hS [int n] none :=
  noneHV (d := cV.withHooks H) ctors.1 ctors.2.2.2.1 fnsPlain.1 (by rw [Semantics.lookupFn_withHooks]; exact lookupFV)
    (by rw [Semantics.lookupFn_withHooks]; exact lookupHV) hn

/-- **The variant's `h(1)` is none, for every H.** -/
theorem hV_1 (H : HookParams) : Eval (cV.withHooks H) hS [int 1] none := hV_none H (by decide)

end ExClauseFixtures.TopCut

/-- info: 'ExClauseFixtures.TopCut.read' does not depend on any axioms -/
#guard_msgs in #print axioms ExClauseFixtures.TopCut.read
/-- info: 'ExClauseFixtures.TopCut.h_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.TopCut.h_1
/-- info: 'ExClauseFixtures.TopCut.hV_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.TopCut.hV_none
