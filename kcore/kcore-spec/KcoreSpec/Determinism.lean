/-
  KCore, checked layer: a decidable condition under which a definition's `Step` is deterministic
  (`deterministic_of`).

  Two steps from x, by rules r and r' under σ and σ', give one successor when:
  - r and r' have different priorities: impossible, the step by the larger one requires that the
    smaller does not apply (`hprio`), and it does (no check);
  - r = r' (same index): its left-hand side's match fixes every variable of its right-hand side
    (`uniq`: constructor arguments and injections are injective on sorted values, and a map pattern
    `K |-> V M` whose key K is fixed by what came before fixes V and M, map keys being unique);
  - r ≠ r' with one priority: the pair is apart (`apart`): the two left-hand sides cannot denote one
    value (`meet` finds a clash: two constructors, two literals, an injection against a
    constructor, or injections whose possible source sorts are disjoint, `srcs`), or the
    `requires` of both, read over σ' (r's translated through the variables `meet` relates to r''s
    patterns), contain a literal that the sorts refute (`refutes`: `isS(kseq(inj{A,KItem}(t), dotk))`
    is decided by the source sorts of t's value), or two complementary literals (well-sorted, so
    their one value cannot be both).
-/
import KcoreSpec.StepIff
import KcoreSpec.TablesChecked

set_option autoImplicit false

namespace KCore.Det

open KCore KCore.Exec

/-! ## Sorts -/

/-- The sorts strictly below a. -/
def below (T : Tables) (a : Srt) : List Srt := T.below a

def leS (T : Tables) (s S : Srt) : Bool := T.le s S

/-- The possible source sorts of `injNormal a b w`, w the value of t (a pattern without `as`, or
a term), and whether the injected core is sorted: a variable of sort a may hold an injection from
a sort below a; an injection from a₁ into a passes its own sources; a constructor, a literal or a
map pattern symbol gives a value that is not an injection, so the source is a. `none`: unknown. -/
def srcs (c : Semantics) (T : Tables) (vars : List Srt) (a : Srt) : Term → Option (List Srt × Bool)
  | .var j => if vars[j]? == some a then some (a :: below T a, true) else none
  | .inj a₁ b₁ t => if b₁ == a then srcs c T vars a₁ t else none
  | .as t _ => srcs c T vars a t
  | .dv s l => some ([a], s == a && dvOK c.lib s l)
  | .app f _ => if T.isCtor f || patternHooks.contains f then some ([a], false) else none

/-! ## Two left-hand sides against each other -/

/-- A pattern without its outer `as`, and the variables they bind. -/
def peelQ : Term → Term × List Nat
  | .as t j => match peelQ t with
    | (u, js) => (u, j :: js)
  | .var i => (.var i, [])
  | .dv s l => (.dv s l, [])
  | .app f ts => (.app f ts, [])
  | .inj a b t => (.inj a b t, [])

/-- Meet p with q: q's outer `as` variables denote p's value; so does a variable q; otherwise `k`
meets p with q's core. -/
def meetQ (p q : Term) (k : Term → Option (List (Term × Term))) : Option (List (Term × Term)) :=
  match peelQ q with
  | (q₀, js) =>
    let pre := js.map fun j => (p, Term.var j)
    match q₀ with
    | .var j => some (pre ++ [(p, .var j)])
    | _ => (k q₀).map (pre ++ ·)

mutual
  /-- `none`: no value is denoted by p (under a well-sorted σ for r's variables `vs`) and by q
  (for r''s, `vs'`). `some C`: pairs of subpatterns that denote one value. -/
  def meet (c : Semantics) (T : Tables) (vs vs' : List Srt) : Term → Term → Option (List (Term × Term))
    | .as p i, q => (meet c T vs vs' p q).map ((.var i, q) :: ·)
    | .var i, q => some [(.var i, q)]
    | .dv s l, q => meetQ (.dv s l) q fun q₀ => match q₀ with
      | .dv s' l' => if s == s' && l == l' then some [] else none
      | .app g _ => if T.isCtor g then none else some []
      | .inj .. => none
      | _ => some []
    | .app f ps, q => meetQ (.app f ps) q fun q₀ => match q₀ with
      | .app g qs =>
        if f == g then (if T.isCtor f then meetList c T vs vs' ps qs else some [(.app f ps, q₀)])
        else if T.isCtor f && T.isCtor g then none else some [(.app f ps, q₀)]
      | .dv .. => if T.isCtor f then none else some []
      | .inj .. => if T.isCtor f || patternHooks.contains f then none else some []
      | _ => some []
    | .inj a b p, q => meetQ (.inj a b p) q fun q₀ => match q₀ with
      | .inj a' b' q' =>
        if b != b' then none
        else if a == a' then meet c T vs vs' p q'
        else match srcs c T vs a p, srcs c T vs' a' q' with
          | some (S, _), some (S', _) => if S.any S'.contains then some [(.inj a b p, q₀)] else none
          | _, _ => some [(.inj a b p, q₀)]
      | .dv .. => none
      | .app g _ => if T.isCtor g || patternHooks.contains g then none else some []
      | _ => some []
    termination_by structural p => p
  def meetList (c : Semantics) (T : Tables) (vs vs' : List Srt) : List Term → List Term → Option (List (Term × Term))
    | [], [] => some []
    | p :: ps, q :: qs => match meet c T vs vs' p q, meetList c T vs vs' ps qs with
      | some C, some D => some (C ++ D)
      | _, _ => none
    | _, _ => none
    termination_by structural ps => ps
end

mutual
  /-- A pattern as a term: `as` removed. -/
  def strip : Term → Term
    | .as t _ => strip t
    | .app f ts => .app f (stripList ts)
    | .inj a b t => .inj a b (strip t)
    | .var i => .var i
    | .dv s l => .dv s l
    termination_by structural t => t
  def stripList : List Term → List Term
    | [] => []
    | t :: ts => strip t :: stripList ts
    termination_by structural ts => ts
end

/-- r's variable i is denoted by r''s pattern q: the first such pair of `meet`. -/
def envOf (C : List (Term × Term)) (i : Nat) : Option Term :=
  (C.find? fun pq => match pq.1 with
    | .var j => j == i
    | _ => false).map (strip ·.2)

mutual
  /-- A term of r with its variables replaced by the terms `env` gives (over r''s variables). -/
  def tr (env : Nat → Option Term) : Term → Option Term
    | .var i => env i
    | .dv s l => some (.dv s l)
    | .app f ts => (trList env ts).map (.app f)
    | .inj a b t => (tr env t).map (.inj a b)
    | .as .. => none
    termination_by structural t => t
  def trList (env : Nat → Option Term) : List Term → Option (List Term)
    | [] => some []
    | t :: ts => match tr env t, trList env ts with
      | some u, some us => some (u :: us)
      | _, _ => none
    termination_by structural ts => ts
end

/-- The pattern `kseq(inj{S,KItem}(X₀), dotk)` of the sort predicate `isS`'s clause. -/
def kseqPat (S : Srt) : Term := .app kseq [.inj S Srt.kitem (.var 0), .app dotk []]

/-- The sort S of a generated sort predicate `isS` as kompile writes it, if `fn` is one: the clause
`isS(kseq(inj{S,KItem}(X₀:S), dotk)) = true` (no `ensures`) and, of a larger priority,
`isS(X₀:K) = false`, neither with a predicate (evaluation reads a clause's predicate, so a clause
with one applies at fewer arguments than its patterns say). -/
def sortPredOf (fn : Fn) : Option Srt :=
  match fn.clauses with
  | [cl, o] => match cl.vars with
    | [S] =>
      if Term.beqList cl.pats [kseqPat S] && cl.req.isNone && Term.beq cl.rhs (.dv Srt.bool (.bool true)) &&
          decide (cl.prio < o.prio) && o.vars == [Srt.k] && Term.beqList o.pats [.var 0] && o.req.isNone &&
          Term.beq o.rhs (.dv Srt.bool (.bool false)) && cl.ens.isNone && !cl.aside &&
          cl.pre.isTop && o.pre.isTop then some S else none
    | _ => none
  | _ => none

/-- The literal `A = b` is false under every well-sorted σ for `vs`: A is a sort predicate `isS`
applied to `kseq(inj{a,KItem}(t), dotk)`, and the sources of t's value are all below S (A is true;
the core must be sorted) or none is (A is false). -/
def refutes (c : Semantics) (T : Tables) (vs : List Srt) : Term × Bool → Bool
  | (.app f [.app kseq [.inj a Srt.kitem t, .app dotk []]], b) =>
    if isHook f || T.isCtor f || c.isParam f then false else
    match c.lookupFn f with
    | some fn => match sortPredOf fn, srcs c T vs a t with
      | some S, some (ss, sorted) =>
        if b then ss.all (!leS T · S) else sorted && ss.all (leS T · S)
      | _, _ => false
    | none => false
  | _ => false

/-- The literals r''s `requires` asserts. -/
def litsR (r' : Rule) : List (Term × Bool) :=
  match r'.req with
  | some t => lits t
  | none => []

/-- The literals r's `requires` asserts, translated to r''s variables (those it can translate). -/
def litsL (env : Nat → Option Term) (r : Rule) : List (Term × Bool) :=
  match r.req with
  | some t => (lits t).filterMap fun (A, b) => (tr env A).map (·, b)
  | none => []

/-- The fuel for evaluating a literal without variables. -/
def litFuel : Nat := 1000

mutual
  /-- A term of constructors, interpreted hooks without silent points (`silentKey`), literals,
  variables and injections: its value depends on no function's clauses, no parameter symbol and no
  interpretation's value at a silent point. -/
  def pureT (c : Semantics) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .inj _ _ t => pureT c t
    | .as _ _ => false
    | .app f ts => (c.isCtor f || (isHook f && !silentKey f)) && pureL c ts
    termination_by structural t => t
  def pureL (c : Semantics) : List Term → Bool
    | [] => true
    | t :: ts => pureT c t && pureL c ts
    termination_by structural ts => ts
end

/-- The literal `A = b`, A without variables, is false: A evaluates (at `litFuel`) to another value,
or is undefined (`0 >Int 0` is `false`, where `requires N >Int 0` meets a rule for `0`). Only a
pure A (`pureT`) is evaluated, and under the data's own interpretation of the parameters
(`withHooks HookParams.none`): a decided condition never evaluates a parameter (ARCHITECTURE.md
§3.3), so that it holds for every interpretation (Params.lean). A pure term's value is the same under
every interpretation (`evalT_pure`, DetSound.lean). -/
def groundRefutes (c : Semantics) (T : Tables) (vs : List Srt) : Term × Bool → Bool
  | (A, b) =>
    pureT c A && (varOccs A).isEmpty && sortOfTerm (c.rhsCtxT T (c.fns.map Fn.sig)) vs A == some Srt.bool &&
    match evalT (c.withHooks HookParams.none) litFuel [] A with
    | some (some w) => !same w (bool b)
    | some none => true
    | none => false

/-- No σ' (well-sorted for `vs`) makes all of L hold: one is refuted by the sorts or, without
variables, by evaluation, or two are complementary (one well-sorted term, true in one and false in
the other). -/
def clashes (c : Semantics) (T : Tables) (vs : List Srt) (L : List (Term × Bool)) : Bool :=
  L.any (refutes c T vs) || L.any (groundRefutes c T vs) || L.any fun (A, b) => L.any fun (A', b') =>
    b != b' && Term.beq A A' && sortOfTerm (c.rhsCtxT T (c.fns.map Fn.sig)) vs A == some Srt.bool

/-- Rules r and r' never both apply to one configuration. -/
def apart (c : Semantics) (T : Tables) (r r' : Rule) : Bool :=
  match meet c T r.vars r'.vars r.lhs r'.lhs with
  | none => true
  | some C => clashes c T r'.vars (litsL (envOf C) r ++ litsR r')

/-! ## One rule: its match fixes its right-hand side (`uniq`, DefinitionWf.lean) -/

def uniqOK (c : Semantics) (r : Rule) : Bool :=
  match uniq c [] r.lhs with
  | some D => (varOccs r.rhs).all D.contains
  | none => false

/-- Two rules with one left-hand side, one right-hand side and the same variables (whatever their
`requires` and `ensures`) step alike: a pair of them is joinable. -/
def sameRule (r r' : Rule) : Bool := r.vars == r'.vars && Term.beq r.lhs r'.lhs && Term.beq r.rhs r'.rhs

/-! ## Head keys: which pairs of rules need examining

Two rules that both apply to x have left-hand sides denoting x. At a position (a path of argument
indices from the root, an injection's argument being its index 0), a pattern may fix what x holds
there: a constructor, a literal, or an injection whose source sort is one of a list. Two rules
whose patterns fix different things at some position never both apply, so only pairs whose keys
are compatible at every position are examined by `apart`. An index of the rules by key (checked
once, `idxOK`) gives each rule its candidates, so the work is about the number of compatible pairs,
not the square of the number of rules. -/

/-- What a value holds at a position: a constructor, a literal, or an injection from a sort. -/
inductive Key where
  | sym (f : Sym)
  | lit (s : Srt) (l : Lit)
  | src (s : Srt)
  deriving Repr, Inhabited

/-- Equality of literals, by cases (the kernel evaluates it without unfolding a derived instance). -/
def litBeq : Lit → Lit → Bool
  | .int i, .int j => i == j
  | .bool a, .bool b => a == b
  | .tok s, .tok u => s == u
  | .float p e b, .float p' e' b' => p == p' && e == e' && b == b'
  | _, _ => false

def Key.beq : Key → Key → Bool
  | .sym f, .sym g => f == g
  | .lit s l, .lit s' l' => s == s' && litBeq l l'
  | .src s, .src s' => s == s'
  | _, _ => false

instance : BEq Key := ⟨Key.beq⟩

theorem litBeq_iff : ∀ l l' : Lit, litBeq l l' = true ↔ l = l'
  | .int _, .int _ | .bool _, .bool _ | .tok _, .tok _ | .float .., .float .. => by simp [litBeq, and_assoc]
  | .int _, .bool _ | .int _, .tok _ | .bool _, .int _ | .bool _, .tok _ | .tok _, .int _ | .tok _, .bool _
  | .int _, .float .. | .bool _, .float .. | .tok _, .float .. | .float .., .int _ | .float .., .bool _
  | .float .., .tok _ => by
    simp [litBeq]

theorem Key.beq_iff : ∀ k k' : Key, (k == k') = true ↔ k = k'
  | .sym _, .sym _ | .src _, .src _ => by simp [BEq.beq, Key.beq]
  | .lit _ _, .lit _ _ => by simp [BEq.beq, Key.beq, litBeq_iff]
  | .sym _, .lit _ _ | .sym _, .src _ | .lit _ _, .sym _ | .lit _ _, .src _ | .src _, .sym _ | .src _, .lit _ _ => by
    simp [BEq.beq, Key.beq]

instance : LawfulBEq Key where
  eq_of_beq h := (Key.beq_iff _ _).mp h
  rfl {k} := (Key.beq_iff k k).mpr rfl

mutual
  /-- The key of a value at a path. -/
  def vkey : GroundTerm → List Nat → Option Key
    | .ctor f _, [] => some (.sym f)
    | .ctor _ vs, i :: P => vkeyL vs i P
    | .inj s _ _, [] => some (.src s)
    | .inj _ _ w, 0 :: P => vkey w P
    | .dv s l, [] => some (.lit s l)
    | _, _ => none
    termination_by structural v => v
  def vkeyL : List GroundTerm → Nat → List Nat → Option Key
    | [], _, _ => none
    | v :: _, 0, P => vkey v P
    | _ :: vs, i + 1, P => vkeyL vs i P
    termination_by structural vs => vs
end

/-- The bound S that the literal (A, true) puts on the source sort of the injection `inj{a,b}(p)`,
named also by the variables `js` (`inj{a,b}(p) #as X`): A is `isS(kseq(u, dotk))` with `isS` a
generated sort predicate and u the injection, as `inj{a,KItem}(t)` with t the pattern p as a term
(`strip p`), or as one of the variables `js` (when b is KItem). -/
def litHit (a b : Srt) (p : Term) (js : List Nat) : Term → Bool
  | .inj a' b' t => a' == a && b' == Srt.kitem && Term.beq t (strip p)
  | .var j => b == Srt.kitem && js.contains j
  | _ => false

def litBound (c : Semantics) (a b : Srt) (p : Term) (js : List Nat) : Term × Bool → Option Srt
  | (.app f [.app kseq [u, .app dotk []]], true) =>
    if litHit a b p js u && !isHook f && !c.isCtor f && !c.isParam f then (c.lookupFn f).bind sortPredOf
    else none
  | _ => none

/-- The source sorts S keeps under the literals L (those below every bound L puts on them). -/
def refineSrcs (c : Semantics) (T : Tables) (a b : Srt) (p : Term) (js : List Nat) (L : List (Term × Bool)) (S : List Srt) :
    List Srt :=
  S.filter fun s => L.all fun l => match litBound c a b p js l with
    | some B => leS T s B
    | none => true

mutual
  /-- The keys a value denoted by the pattern may have at a path (`none`: any), for r's variables
  `vs` and the literals L of its `requires`. -/
  def pkeys (c : Semantics) (T : Tables) (vs : List Srt) (L : List (Term × Bool)) : Term → List Nat → Option (List Key)
    | .as p j, [] => pkeysAs c T vs L [j] p
    | .as p _, i :: P => pkeys c T vs L p (i :: P)
    | .app f _, [] => if T.isCtor f && !patternHooks.contains f then some [.sym f] else none
    | .app f ps, i :: P => if T.isCtor f && !patternHooks.contains f then pkeysL c T vs L ps i P else none
    | .dv s l, [] => some [.lit s l]
    | .inj a b p, [] => (srcs c T vs a p).map fun (S, _) => (refineSrcs c T a b p [] L S).map Key.src
    | .inj _ _ p, 0 :: P => pkeysI c T vs L p P
    | _, _ => none
    termination_by structural p => p
  /-- The keys at the root of a pattern named by the variables `js` (its `as`). -/
  def pkeysAs (c : Semantics) (T : Tables) (vs : List Srt) (L : List (Term × Bool)) (js : List Nat) : Term → Option (List Key)
    | .as p j => pkeysAs c T vs L (j :: js) p
    | .app f _ => if T.isCtor f && !patternHooks.contains f then some [.sym f] else none
    | .dv s l => some [.lit s l]
    | .inj a b p => (srcs c T vs a p).map fun (S, _) => (refineSrcs c T a b p js L S).map Key.src
    | .var _ => none
    termination_by structural p => p
  /-- The keys at a path below an injection of the pattern's value (the injection's argument, after
  injections of injections are flattened, `injNormal`). -/
  def pkeysI (c : Semantics) (T : Tables) (vs : List Srt) (L : List (Term × Bool)) : Term → List Nat → Option (List Key)
    | .as q _, P => pkeysI c T vs L q P
    | .inj _ _ q, P => pkeysI c T vs L q P
    | .app f _, [] => if T.isCtor f && !patternHooks.contains f then some [.sym f] else none
    | .app f ps, i :: P => if T.isCtor f && !patternHooks.contains f then pkeysL c T vs L ps i P else none
    | .dv s l, [] => some [.lit s l]
    | _, _ => none
    termination_by structural p => p
  def pkeysL (c : Semantics) (T : Tables) (vs : List Srt) (L : List (Term × Bool)) : List Term → Nat → List Nat → Option (List Key)
    | [], _, _ => none
    | p :: _, 0, P => pkeys c T vs L p P
    | _ :: ps, i + 1, P => pkeysL c T vs L ps i P
    termination_by structural ps => ps
end

/-- A rule's keys at each path. -/
def ruleKeys (c : Semantics) (T : Tables) (paths : List (List Nat)) (r : Rule) : List (Option (List Key)) :=
  paths.map (pkeys c T r.vars (litsR r) r.lhs)

/-- Keys compatible at every path: where both are known, some key is common. -/
def compat : List (Option (List Key)) → List (Option (List Key)) → Bool
  | some K :: ks, some K' :: ks' => K.any (K'.contains ·) && compat ks ks'
  | _ :: ks, _ :: ks' => compat ks ks'
  | _, _ => true

/-- An index of the rules by key: the paths, each rule's keys there, and for each path the rules
each key may hold (`buckets`) and the rules with no key there (`wild`); for each rule, the path whose
bucket gives its candidates (`probes`, any path where its keys are known; a choice, not checked).
Data the generator writes; `idxOK` checks it. -/
structure DetIndex where
  paths : List (List Nat)
  keys : List (List (Option (List Key)))
  buckets : List (List (Key × List Nat))
  wild : List (List Nat)
  probes : List Nat
  deriving Repr, Inhabited

namespace DetIndex

def bucket (ix : DetIndex) (p : Nat) (k : Key) : List Nat := ((ix.buckets[p]?).bind fun bs => bs.lookup k).getD []

def wildAt (ix : DetIndex) (p : Nat) : List Nat := (ix.wild[p]?).getD []

/-- The rules rule i, with keys ks, may share a configuration with: at its probe path, those holding
one of its keys there or no key. With no known key there, all `n`. -/
def cands (ix : DetIndex) (n i : Nat) (ks : List (Option (List Key))) : List Nat :=
  match ix.probes[i]? with
  | some p => match ks[p]? with
    | some (some K) => K.flatMap (ix.bucket p) ++ ix.wildAt p
    | _ => List.range n
  | none => List.range n

end DetIndex

/-- The index is the rules': each rule's keys are `ruleKeys`, and each rule is in the bucket of each
of its keys, or in `wild`, at every path. -/
def idxOK (c : Semantics) (T : Tables) (ix : DetIndex) : Bool :=
  ix.keys.length == c.rules.length &&
  (List.range c.rules.length).all fun i => match c.rules[i]?, ix.keys[i]? with
    | some r, some ks => ks == ruleKeys c T ix.paths r &&
        (List.range ix.paths.length).all fun p => match ks[p]? with
          | some (some K) => K.all fun k => (ix.bucket p k).contains i
          | _ => (ix.wildAt p).contains i
    | _, _ => false

/-- Two steps by rules i and j, of one priority, give one successor: they are apart (in one order or
the other), alike (`sameRule`, in one order or the other), or a listed overlap. -/
def pairOK (c : Semantics) (T : Tables) (ovl : List (Nat × Nat)) (i j : Nat) (r r' : Rule) : Bool :=
  r.prio != r'.prio || apart c T r r' || apart c T r' r || sameRule r r' || sameRule r' r ||
    ovl.contains (i, j) || ovl.contains (j, i)

/-- Rule i's row: its match fixes its right-hand side, and with every candidate j after it whose keys
are compatible, the pair is fine. -/
def detRow (c : Semantics) (T : Tables) (ix : DetIndex) (ovl : List (Nat × Nat)) (i : Nat) : Bool :=
  match c.rules[i]?, ix.keys[i]? with
  | some r, some ks => uniqOK c r && (ix.cands c.rules.length i ks).all fun j =>
      decide (j ≤ i) || match c.rules[j]?, ix.keys[j]? with
        | some r', some ks' => !compat ks ks' || pairOK c T ovl i j r r'
        | _, _ => false
  | _, _ => false

/-- The rows lo, …, lo + len - 1: a block, decided on its own (`detRows_add` joins blocks). -/
def detRows (c : Semantics) (T : Tables) (ix : DetIndex) (ovl : List (Nat × Nat)) (lo len : Nat) : Bool :=
  (List.range' lo len).all (detRow c T ix ovl)

/-- The condition: the index is the rules', and every row is fine. -/
def detOKExcept (c : Semantics) (T : Tables) (ix : DetIndex) (ovl : List (Nat × Nat)) : Bool :=
  idxOK c T ix && detRows c T ix ovl 0 c.rules.length

/-- `detOKExcept` with no pair excepted. -/
def detOK (c : Semantics) (T : Tables) (ix : DetIndex) : Bool := detOKExcept c T ix []

/-! ## Building the index (what the generator computes; `idxOK` checks it) -/

def addKey (k : Key) (i : Nat) : List (Key × List Nat) → List (Key × List Nat)
  | [] => [(k, [i])]
  | (k', is) :: bs => if k' == k then (k', is ++ [i]) :: bs else (k', is) :: addKey k i bs

def numbered {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | i, a :: as => (i, a) :: numbered (i + 1) as

def DetIndex.build (c : Semantics) (T : Tables) (paths : List (List Nat)) : DetIndex :=
  let ks := c.rules.map (ruleKeys c T paths)
  let rows := numbered 0 ks
  let buckets := (List.range paths.length).map fun p => rows.foldl (fun bs (i, rk) => match rk[p]? with
      | some (some K) => K.foldl (fun bs k => addKey k i bs) bs
      | _ => bs) []
  let wild := (List.range paths.length).map fun p => rows.filterMap fun (i, rk) => match rk[p]? with
      | some (some _) => none
      | _ => some i
  let ix0 : DetIndex := { paths, keys := ks, buckets, wild, probes := [] }
  -- each rule's probe: the known path with the fewest candidates
  let probes := ks.map fun rk => ((numbered 0 rk).foldl (fun (best : Option (Nat × Nat)) (p, k) => match k with
      | some K =>
        let n := (K.flatMap (ix0.bucket p)).length + (ix0.wildAt p).length
        match best with
        | some (_, m) => if n < m then some (p, n) else best
        | none => some (p, n)
      | none => best) none).elim 0 (·.1)
  { ix0 with probes }

mutual
  /-- The path to the first `kseq` of a pattern (the k cell's content). -/
  def kseqPath : Term → Option (List Nat)
    | .app f ts => if f == kseq then some [] else kseqPathL ts 0
    | .as t _ => kseqPath t
    | _ => none
    termination_by structural t => t
  def kseqPathL : List Term → Nat → Option (List Nat)
    | [], _ => none
    | t :: ts, i => match kseqPath t with
      | some P => some (i :: P)
      | none => kseqPathL ts (i + 1)
    termination_by structural ts => ts
end

/-- Default paths: at the k cell's first item, its injection and its head, and the head of the
second item. -/
def autoPaths (c : Semantics) : List (List Nat) :=
  match c.rules.head? >>= fun r => kseqPath r.lhs with
  | some P => [P ++ [0], P ++ [0, 0], P ++ [1, 0]]
  | none => []

/-- The index at the default paths. -/
def autoIndex (c : Semantics) (T : Tables) : DetIndex := DetIndex.build c T (autoPaths c)

/-! ## Witnesses of overlaps -/

/-- Rule r applies to x, by the executable matcher and evaluation at fuel n. -/
def appliesN (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : Bool :=
  (ruleMatches c n r x).any (·.2 == some true)

/-- The listed pair (i, j) is witnessed at x: both rules apply there, and x has two different
successors. -/
def witnessOK (c : Semantics) (n i j : Nat) (x : GroundTerm) : Bool :=
  match c.rules[i]?, c.rules[j]? with
  | some r, some r' =>
    appliesN c n r x && appliesN c n r' x &&
      (successorsN c n x).any fun y => (successorsN c n x).any fun y' => !same y y'
  | _, _ => false

/-- The pairs of distinct rules of one priority, with compatible keys, not shown apart, and the
rules whose match is not shown to fix the right-hand side (a probe's report). -/
def detReport (c : Semantics) (T : Tables) (ix : DetIndex) : List Nat × List (Nat × Nat) :=
  let n := c.rules.length
  ((List.range n).filter fun i => match c.rules[i]? with
      | some r => !uniqOK c r
      | none => true,
   (List.range n).flatMap fun i => match ix.keys[i]? with
    | some ks => ((ix.cands n i ks).filter fun j => decide (i < j) && match c.rules[i]?, c.rules[j]?, ix.keys[j]? with
      | some r, some r', some ks' => compat ks ks' && !pairOK c T [] i j r r'
      | _, _, _ => true).map (i, ·)
    | none => [])

end KCore.Det
