import KcoreSpec.KKEncDef
import KcoreSpec.Statements
import KcoreSpec.Parse

/-!
# The native check of `kore.k`'s `succs` (`kcore kk-native`)

The three statements of KKStatements.lean say that `kore.k`'s `succs`, evaluated at `K₀` on
`[embD E, emb (enc x)]`, gives the encodings of `x`'s `Step (d₀ d)` successors (`next L`), or
`stuck` where no rule applies. This module computes both sides on concrete texts, with the
executable evaluation `CExec`:

- `kk`: `CExec.evalF K₀ Exec.fuel succs [embD E, emb (enc x)]`, with `K` read from `kore.k`'s
  kompiled text by the reader (the same parse `definition_of` gives `RefKk.defn`), `E` from
  `encDef d` and `enc` of KKEnc.lean;
- the object side: `CExec.successorsN (d₀ d) Exec.fuel x`, with what a configuration without a
  successor is (no rule applies: every match's `requires` is `some false`; a rule applies; out of
  fuel).

The embeddings below are the ones of `examples/ref-kk/User/Emb.lean` (`KCore.KK.emb`, …), written
here so that the check runs natively in `kcore`; `User.NativeTie` in that package proves each one
equal to the package's, and `embNames` is the table of KORE names `emb_names` states there, which
`kk-native` checks against the text it reads.

`hookCase` compares one interpreted symbol of `hookCodes` with `kore.k`'s `strictHook` at its code,
at one argument list.
-/

set_option autoImplicit false

namespace KCore.KK.Native

/-! ## The embeddings of the mirrors -/

/-- kore.k's `Kind`. -/
def embK : Kind → GroundTerm
  | .map => .ctor 429 []
  | .set => .ctor 438 []
  | .list => .ctor 427 []

mutual
/-- A mirror term as a kore.k value of sort `Term`. -/
def emb : T → GroundTerm
  | .ap f as => .ctor 408 [.dv 3 (.int f), embTs as]
  | .iv i => .ctor 425 [.dv 3 (.int i)]
  | .bv b => .ctor 413 [.dv 2 (.bool b)]
  | .tk s x => .ctor 443 [.dv 3 (.int s), .dv 10 (.tok x)]
  | .ij a b t => .ctor 424 [.dv 3 (.int a), .dv 3 (.int b), emb t]
  | .vr i => .ctor 445 [.dv 3 (.int i)]
  | .as p i => .ctor 409 [emb p, .dv 3 (.int i)]
  | .hk o as => .ctor 423 [.dv 3 (.int o), embTs as]
  | .bot => .ctor 412 []
  | .cb k c ps => .ctor 414 [embK k, .dv 3 (.int c), embTs ps]
  | .co k c es => .ctor 416 [embK k, .dv 3 (.int c), embTs es]
  | .en t e => .ctor 420 [emb t, emb e]
  | .kv a v => .ctor 426 [emb a, emb v]
  | .el x => .ctor 419 [emb x]
  termination_by structural t => t
/-- Mirror terms as a kore.k `Ts`. -/
def embTs : List T → GroundTerm
  | [] => .ctor 406 []
  | t :: ts => .ctor 407 [emb t, embTs ts]
  termination_by structural ts => ts
end

/-- The subsort table as a kore.k `Subs`. -/
def embS : List (Int × Int) → GroundTerm
  | [] => .ctor 405 []
  | (a, b) :: r => .ctor 442 [.dv 3 (.int a), .dv 3 (.int b), embS r]

/-- A clause before the clauses `r`. -/
def embCl (cl : Cl) (r : GroundTerm) : GroundTerm :=
  .ctor 415 [.dv 3 (.int cl.prio), .dv 2 (.bool cl.owise), embTs cl.pats, emb cl.req, emb cl.rhs, r]

/-- Clauses as a kore.k `Clauses`. -/
def embCls : List Cl → GroundTerm
  | [] => .ctor 401 []
  | cl :: r => embCl cl (embCls r)

/-- Functions with their clauses as a kore.k `Fns`. -/
def embFns : List (Int × List Cl) → GroundTerm
  | [] => .ctor 402 []
  | (g, cs) :: r => .ctor 421 [.dv 3 (.int g), embCls cs, embFns r]

/-- A rule before the rules `r`. -/
def embRl (rl : Rl) (r : GroundTerm) : GroundTerm :=
  .ctor 436 [.dv 3 (.int rl.prio), .dv 2 (.bool rl.owise), emb rl.lhs, emb rl.req, emb rl.rhs, r]

/-- Rules as a kore.k `Rules`. -/
def embRls : List Rl → GroundTerm
  | [] => .ctor 404 []
  | rl :: r => embRl rl (embRls r)

/-- A mirror definition as a kore.k `Def`. -/
def embD (E : D) : GroundTerm := .ctor 417 [embS E.subs, embFns E.fns, embRls E.rules]

/-- A mirror step result as a kore.k `Step`. -/
def embSt : St → GroundTerm
  | .stuck => .ctor 441 []
  | .next ss => .ctor 430 [embTs ss]

/-! ## The symbols, by their KORE names -/

/-- The KORE name of each symbol number the embeddings write. -/
def embNames : List (Sym × String) :=
  [(401, "Lbl'Stop'Cls'Unds'KORE-SYNTAX'Unds'Clauses"),
   (402, "Lbl'Stop'Fns'Unds'KORE-SYNTAX'Unds'Fns"),
   (404, "Lbl'Stop'Rules'Unds'KORE-SYNTAX'Unds'Rules"),
   (405, "Lbl'Stop'Subs'Unds'KORE-SYNTAX'Unds'Subs"),
   (406, "Lbl'Stop'Ts'Unds'KORE-SYNTAX'Unds'Ts"),
   (407, "Lbl'UndsSClnUndsUnds'KORE-SYNTAX'Unds'Ts'Unds'Term'Unds'Ts"),
   (408, "Lblap'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Ts"),
   (409, "Lblas'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term'Unds'Int"),
   (412, "Lblbot'Unds'KORE-SYNTAX'Unds'Term"),
   (413, "Lblbv'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Bool"),
   (414, "Lblcb'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Kind'Unds'Int'Unds'Ts"),
   (415, "Lblcl'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Clauses'Unds'Int'Unds'Bool'Unds'Ts'Unds'Term'Unds'Term'Unds'Clauses"),
   (416, "Lblco'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Kind'Unds'Int'Unds'Ts"),
   (417, "Lbldef'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Def'Unds'Subs'Unds'Fns'Unds'Rules"),
   (419, "Lblel'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term"),
   (420, "Lblen'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term'Unds'Term"),
   (421, "Lblfn'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Fns'Unds'Int'Unds'Clauses'Unds'Fns"),
   (423, "Lblhk'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Ts"),
   (424, "Lblij'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Int'Unds'Term"),
   (425, "Lbliv'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int"),
   (426, "Lblkv'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term'Unds'Term"),
   (427, "Lbllist'Unds'KORE-SYNTAX'Unds'Kind"),
   (429, "Lblmap'Unds'KORE-SYNTAX'Unds'Kind"),
   (430, "Lblnext'LParUndsRParUnds'KORE'Unds'Step'Unds'Ts"),
   (436, "Lblrl'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Rules'Unds'Int'Unds'Bool'Unds'Term'Unds'Term'Unds'Term'Unds'Rules"),
   (438, "Lblset'Unds'KORE-SYNTAX'Unds'Kind"),
   (441, "Lblstuck'Unds'KORE'Unds'Step"),
   (442, "Lblsub'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Subs'Unds'Int'Unds'Int'Unds'Subs"),
   (443, "Lbltk'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'String"),
   (445, "Lblvr'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int")]

/-- `succs`, the step function the statements are about (symbol 510 of `RefKk.defn`). -/
def succsName : String := "Lblsuccs'LParUndsCommUndsRParUnds'KORE'Unds'Step'Unds'Def'Unds'Term"
/-- `strictHook(O, As)`: `bot` where an argument is `bot`, else `hookOp(O, As)`. -/
def strictHookName : String := "LblstrictHook'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Int'Unds'Ts"
/-- `hookOp(O, As)`: the operation of code `O`. -/
def hookOpName : String := "LblhookOp'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Int'Unds'Ts"

/-- A symbol's number in `c`, by its KORE name. -/
def symOf (c : Semantics) (n : String) : Option Sym :=
  match regSymNames.idxOf? n with
  | some i => some i
  | none => (c.symNames.idxOf? n).map (nRegSyms + ·)

/-- The numbers of `embNames` whose name in `c` is another. -/
def embNamesWrong (c : Semantics) : List Sym :=
  (embNames.filter fun (f, n) => c.symName f != n).map (·.1)

/-! ## The two sides at a configuration -/

/-- A `Ts` value as its list of terms (`.Ts`, `T ; Ts`); `fuel` bounds the length. -/
def tsList : Nat → GroundTerm → Option (List GroundTerm)
  | 0, _ => none
  | _ + 1, .ctor 406 [] => some []
  | n + 1, .ctor 407 [a, b] => (tsList n b).map (a :: ·)
  | _, _ => none

/-- What kore.k's `succs` gives: `stuck`, `next L` (the terms of `L`), no value, out of fuel, or a
value that is no `Step`. -/
inductive KkOut | stuck | next (ss : List GroundTerm) | undef | fuel | other (v : GroundTerm)

def kkOut : Option (Option GroundTerm) → KkOut
  | none => .fuel
  | some none => .undef
  | some (some (.ctor 441 [])) => .stuck
  | some (some (.ctor 430 [ts])) => match tsList 100000 ts with
    | some ss => .next ss
    | none => .other (.ctor 430 [ts])
  | some (some v) => .other v

/-- kore.k's `succs` at `E` and the configuration `x`, at `K₀` (`K0`, symbol `succs`). -/
def kkAt (K0 : Semantics) (succs : Sym) (E : D) (x : GroundTerm) : KkOut :=
  kkOut (CExec.evalF K0 Exec.fuel succs [embD E, emb (enc x)])

/-- What the object side gives at a configuration: successors; none, where no rule applies (every
match's `requires` is `some false`); none, where a rule applies; or out of fuel somewhere
(`CExec.outOfFuel`: the list is then no verdict). -/
inductive ObjOut | step (ys : List GroundTerm) | noRule | undef | fuel (ys : List GroundTerm)

def dedup (l : List GroundTerm) : List GroundTerm :=
  l.foldl (fun acc v => if acc.any (Exec.same · v) then acc else acc ++ [v]) []

def sameSet (a b : List GroundTerm) : Bool :=
  a.all (fun v => b.any (Exec.same v ·)) && b.all (fun v => a.any (Exec.same v ·))

def objAt (d0 : Semantics) (x : GroundTerm) : ObjOut :=
  let ys := dedup (CExec.successorsN d0 Exec.fuel x)
  if CExec.outOfFuel d0 Exec.fuel x then .fuel ys
  else if !ys.isEmpty then .step ys
  else if d0.rules.all fun r => (CExec.ruleMatches d0 Exec.fuel r x).all (·.2 == some false) then .noRule
  else .undef

/-- The verdict at a configuration: `agree` where `succs` gives `next` of the successors'
encodings as a set (`next []` where a rule applies and no successor exists) or `stuck` where no rule
applies; `no-verdict` where either side runs out of fuel (with whether `succs` gives the listed
successors); `differ` otherwise, with what each side gives. -/
def verdict (o : ObjOut) (k : KkOut) : String × String :=
  let ko : String := match k with
    | .stuck => "stuck" | .next ss => s!"next({ss.length})" | .undef => "undefined"
    | .fuel => "out-of-fuel" | .other _ => "not-a-Step"
  match o, k with
  | .fuel ys, _ =>
    let same := match k with
      | .next ss => if sameSet ss (ys.map (emb ∘ enc)) then ", the listed set" else ", another set"
      | _ => ""
    ("no-verdict", s!"object out of fuel, listed step({ys.length}); kk {ko}{same}")
  | _, .fuel => ("no-verdict", "kk out of fuel")
  | .step ys, .next ss =>
    if sameSet ss (ys.map (emb ∘ enc)) then ("agree", s!"next({ys.length})")
    else ("differ", s!"object step({ys.length}); kk {ko}, another set")
  | .step ys, _ => ("differ", s!"object step({ys.length}); kk {ko}")
  | .noRule, .stuck => ("agree", "stuck")
  | .noRule, _ => ("differ", s!"object no rule applies; kk {ko}")
  | .undef, .next [] => ("agree", "next(0), a rule applies")
  | .undef, _ => ("differ", s!"object a rule applies, no successor; kk {ko}")

/-! ## Interpreted symbols -/

/-- kore.k's `strictHook` at code `o` on the encoded arguments, against KCore's `hook f` at `d₀`
(`(d₀ d).hookRes f vs = hook f vs`), encoded with `encR`. `derivedHook`'s symbols (`=/=Bool`) are
compared through their nested form. -/
def hookCase (K0 : Semantics) (strict : Sym) (f : Sym) (vs : List GroundTerm) : Bool × String :=
  let want := emb (encR (hook f vs).join)
  let call := fun (o : Int) (as : GroundTerm) => CExec.evalF K0 Exec.fuel strict [.dv 3 (.int o), as]
  let got : Option (Option GroundTerm) := match opOf f, derivedHook f (encTs vs) with
    | some o, _ => call o (embTs (encTs vs))
    | none, some (.hk o₁ [.hk o₂ as]) => match call o₂ (embTs as) with
      | some (some w) => call o₁ (.ctor 407 [w, .ctor 406 []])
      | r => r
    | _, _ => none
  match got with
  | some (some w) => (Exec.same w want, if Exec.same w want then "agree" else "differ")
  | some none => (false, "kk undefined")
  | none => (false, "kk out of fuel")

/-- The codes written by a mirror term's `hk` nodes. -/
partial def hkCodes : T → List Int
  | .hk o as => o :: as.flatMap hkCodes
  | .ap _ as | .cb _ _ as | .co _ _ as => as.flatMap hkCodes
  | .ij _ _ t | .as t _ | .el t => hkCodes t
  | .en a b | .kv a b => hkCodes a ++ hkCodes b
  | _ => []

/-- The codes of the clauses of kore.k's `hookOp` whose first pattern is an Int literal. -/
def hookOpCodes (K : Semantics) (hookOp : Sym) : List Int :=
  match K.lookupFn hookOp with
  | none => []
  | some fn => fn.clauses.filterMap fun cl => match cl.pats with
    | .dv _ (.int o) :: _ => some o
    | _ => none

/-! ## Reading a configuration -/

/-- The reader's names of a semantics, for reading a ground pattern as a term. -/
def namesOf (c : Semantics) : Parse.Names :=
  { sorts := c.sortNames, syms := c.symNames, own := c.symNames.filter (regSymNames.contains ·) }

/-- A ground pattern as a value of `c`: read as a term without variables, then evaluated
(`CExec.evalT`). -/
def valueOf (c : Semantics) (p : Kore.Pattern) : Except String (Option GroundTerm) := do
  let (t, vs) ← (Parse.term (namesOf c) [] p).mapError fun f => s!"{repr f.reason} {f.detail}"
  unless vs.isEmpty do throw "a pattern with variables"
  match CExec.evalT c Exec.fuel [] t with
  | some v => pure v
  | none => throw "its evaluation runs out of fuel"

/-! ## Why a text is outside `encDef` -/

/-- The heads of the applications in a term. -/
partial def appHeads : Term → List Sym
  | .app f ts => f :: ts.flatMap appHeads
  | .inj _ _ t | .as t _ => appHeads t
  | _ => []

/-- The conditions of `encodable` that fail, each with the names it fails at where it is C2
(parameters without a collection form) or C3 (applied symbols with no reading). -/
def outsideWhy (d : Semantics) : List String :=
  let nm := fun (f : Sym) => d.symName f
  let params := (d.params.filter fun p => match p.impl.bind libCollOf, d.collOf p.sig.result with
    | some (kd, _, _), some k => kindOf k.kind != some kd
    | _, _ => true).map (nm ·.sig.name)
  let heads := ((lhsTerms d ++ rhsTerms d).flatMap appHeads).eraseDups.filter (fun f =>
    (readApp d f (some []) (some [])).isNone)
  let rows : List (String × Bool × List String) := [("ovls", ovlsOK d, ([] : List String)), ("params", paramsOK d, params), ("apps", appsOK d, heads.map nm),
   ("heads", headsOK d, []), ("lits", litsOK d, []), ("subsorts", subsortsOK d, []),
   ("colPats", colPatsOK d, []), ("as", asOK d, []), ("ens", ensOK d, []), ("shapes", shapesOK d, []),
   ("collForm", collFormOK d, [])]
  rows.filter (!·.2.1) |>.map fun (b, _, ns) => if ns.isEmpty then b else s!"{b} ({", ".intercalate ns})"

end KCore.KK.Native
