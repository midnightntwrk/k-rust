import KcoreSpec.KKLitsVPatVal
import KcoreSpec.CollExecStep
import KcoreSpec.KKEncCanon

/-!
# `kore.k`'s matching

`matchF`, `matchTsF`, `matchKF`, `bindAfterF`, `lookF`, `bindVarF`, `leqF` and `aboveF` are
`kore.k`'s functions `match`, `matchTs`, `matchK`, `bindAfter`, `look`, `bindVar`, `leq` and `above`
over the mirrors, and `matchColF`, `chooseF`, `splitF`, `splitOnF` and `restF` its `matchCol`,
`choose`, `split`, `splitOn` and `rest`, one Lean equation per equation of `kore.k`; `cat` and `app`
are `++`, and `isElem` is `isElemT`. A substitution `Bind` is `kore.k`'s list `bind(X, T, B)`, newest
entry first, and `Ms` the list of substitutions a match gives.

`matchTs` has an equation for two empty lists and for two non-empty lists only, so `matchTsF` is
`none` at lists of two lengths, where `kore.k`'s `matchTs` has no value; a function applied to an
argument without a value has none, so every function here gives `Option Ms`, and `none` at a
concatenation one of whose arguments is `none`.
`match` of a collection pattern (`cb`) against a collection (`co`) is `matchCol` at the pattern's
kind and sort and the collection's elements: the collection's own kind and sort are not read.

The statements are about one semantics `c`: `matchF_sound` and `matchF_complete` relate `matchF` at
the encoding of a pattern (`encTerm`) and of a value (`enc`) to `PatVal c`, for a pattern without
`cb` (`noCb`). The pattern is well
sorted in a left side's context at the sort of the value: `kore.k` compares the sources of two
injections and never their targets, and a variable seen twice by `==K` on encodings, which is
equality of values on values sorted in `c` whose literals `kore.k` has (`enc_inj`).
-/

set_option autoImplicit false

namespace KCore.KK

mutual
/-- Two `kore.k` terms are the same term. -/
def eqTF : T → T → Bool
  | .ap f as, .ap g bs => f == g && eqTsF as bs
  | .iv i, .iv j => i == j
  | .bv x, .bv y => x == y
  | .tk s x, .tk t y => s == t && x == y
  | .ij a b t, .ij c e u => a == c && b == e && eqTF t u
  | .vr i, .vr j => i == j
  | .as p i, .as q j => eqTF p q && i == j
  | .hk o as, .hk n bs => o == n && eqTsF as bs
  | .bot, .bot => true
  | .cb k c ps, .cb l e qs => k == l && c == e && eqTsF ps qs
  | .co k c ps, .co l e qs => k == l && c == e && eqTsF ps qs
  | .en t e, .en u f => eqTF t u && eqTF e f
  | .kv a v, .kv b w => eqTF a b && eqTF v w
  | .el x, .el y => eqTF x y
  | _, _ => false
  termination_by structural t => t
def eqTsF : List T → List T → Bool
  | [], [] => true
  | t :: ts, u :: us => eqTF t u && eqTsF ts us
  | _, _ => false
  termination_by structural ts => ts
end

theorem eqTsF_iff_kmf : ∀ {as bs : List T}, (∀ a ∈ as, ∀ u, eqTF a u = true ↔ a = u) →
    (eqTsF as bs = true ↔ as = bs)
  | [], [], _ => by simp [eqTsF]
  | [], _ :: _, _ => by simp [eqTsF]
  | _ :: _, [], _ => by simp [eqTsF]
  | a :: as, b :: bs, h => by
    have ih := eqTsF_iff_kmf (as := as) (bs := bs) fun x hx => h x (by simp [hx])
    simp [eqTsF, h a (by simp) b, ih]

set_option maxHeartbeats 1600000 in
theorem eqTF_iff (t : T) : ∀ u, eqTF t u = true ↔ t = u := by
  induction t using tInd_kkc with
  | hap f as ih => intro u; cases u <;> simp [eqTF, eqTsF_iff_kmf ih]
  | hiv i => intro u; cases u <;> simp [eqTF]
  | hbv b => intro u; cases u <;> simp [eqTF]
  | htk s x =>
    intro u
    cases u <;> simp only [eqTF, Bool.and_eq_true, beq_iff_eq, T.tk.injEq, reduceCtorEq, Bool.false_eq_true]
  | hij a b t ih => intro u; cases u <;> simp [eqTF, ih, and_assoc]
  | hvr i => intro u; cases u <;> simp [eqTF]
  | has p i ih => intro u; cases u <;> simp [eqTF, ih]
  | hhk o as ih => intro u; cases u <;> simp [eqTF, eqTsF_iff_kmf ih]
  | hbot => intro u; cases u <;> simp [eqTF]
  | hcb k c ps ih => intro u; cases u <;> simp [eqTF, eqTsF_iff_kmf ih, and_assoc]
  | hco k c ps ih => intro u; cases u <;> simp [eqTF, eqTsF_iff_kmf ih, and_assoc]
  | hen t e iht ihe => intro u; cases u <;> simp [eqTF, iht, ihe]
  | hkv a v iha ihv => intro u; cases u <;> simp [eqTF, iha, ihv]
  | hel x ih => intro u; cases u <;> simp [eqTF, ih]

/-- `==K` on two `kore.k` terms is decided. -/
instance instDecidableEqT_kmf : DecidableEq T := fun t u => decidable_of_iff _ (eqTF_iff t u)

/-- `kore.k`'s `Bind`: `bind(X, T, B)` is `(X, T) :: B`. -/
abbrev Bind := List (Int × T)

/-- `kore.k`'s `Ms`: `m(B, Ms)` is `B :: Ms`. -/
abbrev Ms := List Bind

/-! ## The subsort test -/

/-- `above(A, B, T, All, F)`: an entry of `T` starts at `A` and reaches `B` by at most as many
entries as `F` has. -/
def aboveF (a b : Int) : List (Int × Int) → List (Int × Int) → List (Int × Int) → Bool
  | [], _, _ => false
  | _ :: _, _, [] => false
  | (x, y) :: rest, all, pq :: f =>
      if x = a then (y == b || aboveF y b all all f) || aboveF a b rest all (pq :: f)
      else aboveF a b rest all (pq :: f)
  termination_by t _ f => (f.length, t.length)

/-- `leq(A, B, S)`: `A` is `B` or below it by the entries of `S`. -/
def leqF (a b : Int) (S : List (Int × Int)) : Bool := if a = b then true else aboveF a b S S S

/-! ## Substitutions -/

/-- `look(X, B)`: the newest entry of `X`. -/
def lookF (x : Int) : Bind → Option T
  | [] => none
  | (y, t) :: B => if x = y then some t else lookF x B

/-- `bindVar(X, T, B, look(X, B))`: a new entry where `X` has none, `B` where its entry is `T`, no
substitution where it is another term. -/
def bindVarF (x : Int) (t : T) (B : Bind) : Option T → Ms
  | none => [(x, t) :: B]
  | some u => if t = u then [B] else []

/-- `bindAfter(X, T, Ms)`: `X` bound to `T` in each substitution. -/
def bindAfterF (x : Int) (t : T) : Ms → Ms
  | [] => []
  | B :: ms => bindVarF x t B (lookF x B) ++ bindAfterF x t ms

/-! ## Matching -/

mutual
/-- The measure's size of a pattern: an entry `kv(P, Q)` is above the list `P ; Q ; .Ts`. -/
def psizeF : T → Nat
  | .ap _ as | .hk _ as | .cb _ _ as | .co _ _ as => 1 + psizeLF as
  | .ij _ _ t | .as t _ | .el t => 1 + psizeF t
  | .kv a v | .en a v => 3 + psizeF a + psizeF v
  | .iv _ | .bv _ | .tk _ _ | .vr _ | .bot => 1
  termination_by structural t => t
def psizeLF : List T → Nat
  | [] => 0
  | t :: ts => 1 + psizeF t + psizeLF ts
  termination_by structural ts => ts
end

mutual
/-- `match(P, T, B, S)`: the substitutions extending `B` under which `P` is `T`, in order. -/
def matchF (S : List (Int × Int)) : T → T → Bind → Option Ms
  | .vr x, t, B => some (bindVarF x t B (lookF x B))
  | .iv i, a, B => match a with
    | .iv j => if i = j then some [B] else some []
    | _ => some []
  | .bv x, a, B => match a with
    | .bv y => if x = y then some [B] else some []
    | _ => some []
  | .tk s x, a, B => match a with
    | .tk t y => if s = t ∧ x = y then some [B] else some []
    | _ => some []
  | .ap f ps, a, B => match a with
    | .ap g ts => if f = g then matchTsF S ps ts B else some []
    | _ => some []
  | .ij a _ p, u, B => match u with
    | .ij c _ t =>
        if a = c then matchF S p t B
        else if leqF c a S then matchF S p (.ij c a t) B
        else some []
    | _ => some []
  | .as p x, t, B => (matchF S p t B).map (bindAfterF x t)
  | .cb k c ps, a, B => match a with
    | .co _ _ es => matchColF S k c ps es B
    | _ => some []
  | .kv p q, a, B => match a with
    | .kv k v => matchTsF S [p, q] [k, v] B
    | _ => some []
  | .el p, a, B => match a with
    | .el x => matchF S p x B
    | _ => some []
  | .hk _ _, _, _ | .bot, _, _ | .co _ _ _, _, _ | .en _ _, _, _ => some []
  termination_by p => (psizeF p, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
/-- `matchTs(Ps, Ts, B, S)`: two lists of one length, pattern by pattern. -/
def matchTsF (S : List (Int × Int)) : List T → List T → Bind → Option Ms
  | [], [], B => some [B]
  | p :: ps, t :: ts, B => match matchF S p t B with
    | some ms => matchKF S ms ps ts
    | none => none
  | _, _, _ => none
  termination_by ps => (psizeLF ps, 1, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
/-- `matchK(Ms, Ps, Ts, S)`: the rest of two lists under each substitution of `Ms`. -/
def matchKF (S : List (Int × Int)) : Ms → List T → List T → Option Ms
  | [], _, _ => some []
  | B :: ms, ps, ts => match matchTsF S ps ts B, matchKF S ms ps ts with
    | some x, some y => some (x ++ y)
    | _, _ => none
  termination_by ms ps => (psizeLF ps, 2, ms.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
/-- `matchCol(K, C, Ps, Es, B, S)`: the parts `Ps` of a collection pattern against the elements
`Es`. An element part of a `Map` or a `Set` takes each element in turn (`mc-choose`), a `List`'s the
first (`mc-head`); a last part that is no element takes the elements left, as a collection of the
pattern's kind and sort (`mc-frame`); a `List`'s part that is no element and has parts after it
takes each prefix in turn (`mc-split`). -/
def matchColF (S : List (Int × Int)) (k : Kind) (c : Int) (ps es : List T) (B : Bind) : Option Ms :=
  match ps with
  | [] => match es with
    | [] => some [B]
    | _ :: _ => some []
  | p :: ps' =>
    if isElemT p then
      if k = .list then match es with
        | e :: es' => match matchF S p e B with
          | some ms => restF S .list c ps' es' ms
          | none => none
        | [] => some []
      else chooseF S k c p ps' [] es B
    else match ps' with
      | [] => matchF S p (.co k c es) B
      | q :: qs => if k = .list then splitF S c p (q :: qs) [] es B else some []
  termination_by (psizeLF ps, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
/-- `choose(K, C, P, Ps, Pre, Post, B, S)`: the element part `P` against each element of `Post` in
turn, the parts `Ps` against the other elements. -/
def chooseF (S : List (Int × Int)) (k : Kind) (c : Int) (p : T) (ps pre post : List T) (B : Bind) :
    Option Ms :=
  match post with
  | [] => some []
  | e :: post' =>
    match (match matchF S p e B with
      | some ms => restF S k c ps (pre ++ post') ms
      | none => none), chooseF S k c p ps (pre ++ [e]) post' B with
    | some x, some y => some (x ++ y)
    | _, _ => none
  termination_by (psizeLF (p :: ps), 2, post.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
/-- `split(C, F, Ps, Pre, Post, B, S)`: the part `F` against the list of `Pre` and the parts `Ps`
against `Post`, then the same at each longer prefix (`splitOn`). -/
def splitF (S : List (Int × Int)) (c : Int) (f : T) (ps pre post : List T) (B : Bind) : Option Ms :=
  match (match matchF S f (.co .list c pre) B with
    | some ms => restF S .list c ps post ms
    | none => none), splitOnF S c f ps pre post B with
  | some x, some y => some (x ++ y)
  | _, _ => none
  termination_by (psizeLF (f :: ps), 2, 2 * post.length + 1)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
/-- `splitOn(C, F, Ps, Pre, Post, B, S)`: `split` with the first element of `Post` moved to the
end of `Pre`; no substitution where `Post` is empty. -/
def splitOnF (S : List (Int × Int)) (c : Int) (f : T) (ps pre post : List T) (B : Bind) : Option Ms :=
  match post with
  | [] => some []
  | e :: post' => splitF S c f ps (pre ++ [e]) post' B
  termination_by (psizeLF (f :: ps), 2, 2 * post.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
/-- `rest(K, C, Ps, Es, Ms, S)`: the parts `Ps` against the elements `Es` under each substitution
of `Ms`. -/
def restF (S : List (Int × Int)) (k : Kind) (c : Int) (ps es : List T) (ms : Ms) : Option Ms :=
  match ms with
  | [] => some []
  | B :: ms' => match matchColF S k c ps es B, restF S k c ps es ms' with
    | some x, some y => some (x ++ y)
    | _, _ => none
  termination_by (psizeLF ps, 4, ms.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | (apply Prod.Lex.left; (try simp only [psizeF]); (try simp only [psizeLF]); omega)
end

/-! ## The equations, as `kore.k` states them -/

section
variable (S : List (Int × Int))

theorem matchF_vr (x : Int) (t : T) (B : Bind) :
    matchF S (.vr x) t B = some (bindVarF x t B (lookF x B)) := by rw [matchF]

theorem matchF_as (p : T) (x : Int) (t : T) (B : Bind) :
    matchF S (.as p x) t B = (matchF S p t B).map (bindAfterF x t) := by rw [matchF]

theorem matchF_ap_ap (f g : Int) (ps ts : List T) (B : Bind) :
    matchF S (.ap f ps) (.ap g ts) B = if f = g then matchTsF S ps ts B else some [] := by
  rw [matchF]

theorem matchF_ij_ij (a b c e : Int) (p t : T) (B : Bind) :
    matchF S (.ij a b p) (.ij c e t) B =
      if a = c then matchF S p t B else if leqF c a S then matchF S p (.ij c a t) B else some [] := by
  rw [matchF]

/-- `m-int`, `m-bool`, `m-tok` and `m-fail`: a literal matches itself only, and binds nothing. -/
theorem matchF_iv (i : Int) (a : T) (B : Bind) :
    matchF S (.iv i) a B = some (if a = .iv i then [B] else []) := by
  cases a with
  | iv j => unfold matchF; by_cases h : i = j <;> simp [h, eq_comm]
  | _ => unfold matchF; simp

theorem matchF_bv (x : Bool) (a : T) (B : Bind) :
    matchF S (.bv x) a B = some (if a = .bv x then [B] else []) := by
  cases a with
  | bv y => unfold matchF; by_cases h : x = y <;> simp [h, eq_comm]
  | _ => unfold matchF; simp

theorem matchF_tk (s : Int) (x : String) (a : T) (B : Bind) :
    matchF S (.tk s x) a B = some (if a = .tk s x then [B] else []) := by
  cases a with
  | tk t y => unfold matchF; by_cases h : s = t ∧ x = y <;> simp [h, eq_comm]
  | _ => unfold matchF; simp

/-- `m-fail` at an operation: no equation of `match` has `hk` as its pattern. -/
theorem matchF_hk (o : Int) (as : List T) (a : T) (B : Bind) : matchF S (.hk o as) a B = some [] := by
  rw [matchF]

/-- `m-app` is the one equation that gives a substitution at an application. -/
theorem matchF_ap_inv {f : Int} {ps : List T} {a : T} {B B' : Bind} {M : Ms}
    (h : matchF S (.ap f ps) a B = some M) (hB : B' ∈ M) :
    ∃ ts, a = .ap f ts ∧ matchTsF S ps ts B = some M := by
  cases a with
  | ap g ts =>
    rw [matchF_ap_ap] at h
    split at h
    · rename_i hfg; subst hfg; exact ⟨ts, rfl, h⟩
    · cases h; cases hB
  | _ => unfold matchF at h; simp at h; subst h; cases hB

/-- `m-inj-same` and `m-inj-sub` are the two equations that give a substitution at an injection. -/
theorem matchF_ij_inv {a b : Int} {p u : T} {B B' : Bind} {M : Ms}
    (h : matchF S (.ij a b p) u B = some M) (hB : B' ∈ M) :
    ∃ c e t, u = .ij c e t ∧ ((a = c ∧ matchF S p t B = some M) ∨
      (a ≠ c ∧ leqF c a S = true ∧ matchF S p (.ij c a t) B = some M)) := by
  cases u with
  | ij c e t =>
    rw [matchF_ij_ij] at h
    refine ⟨c, e, t, rfl, ?_⟩
    split at h
    · rename_i hac; exact .inl ⟨hac, h⟩
    · rename_i hac
      split at h
      · rename_i hle; exact .inr ⟨hac, hle, h⟩
      · cases h; cases hB
  | _ => unfold matchF at h; simp at h; subst h; cases hB

/-- `m-fail` at `bot`, a collection value and a right side with its ensures as patterns. -/
theorem matchF_bot (a : T) (B : Bind) : matchF S .bot a B = some [] := by rw [matchF]

theorem matchF_co (k : Kind) (c : Int) (es : List T) (a : T) (B : Bind) :
    matchF S (.co k c es) a B = some [] := by rw [matchF]

theorem matchF_en (t e a : T) (B : Bind) : matchF S (.en t e) a B = some [] := by rw [matchF]

theorem matchTsF_nil (B : Bind) : matchTsF S [] [] B = some [B] := by rw [matchTsF]

/-- `matchTs` has no equation at lists of two lengths. -/
theorem matchTsF_nil_cons (t : T) (ts : List T) (B : Bind) : matchTsF S [] (t :: ts) B = none := by
  rw [matchTsF] <;> simp

theorem matchTsF_cons_nil (p : T) (ps : List T) (B : Bind) : matchTsF S (p :: ps) [] B = none := by
  rw [matchTsF] <;> simp

theorem matchTsF_cons (p : T) (ps : List T) (t : T) (ts : List T) (B : Bind) :
    matchTsF S (p :: ps) (t :: ts) B =
      match matchF S p t B with
      | some ms => matchKF S ms ps ts
      | none => none := by rw [matchTsF]

theorem matchKF_nil (ps ts : List T) : matchKF S [] ps ts = some [] := by rw [matchKF]

theorem matchKF_cons (B : Bind) (ms : Ms) (ps ts : List T) :
    matchKF S (B :: ms) ps ts =
      match matchTsF S ps ts B, matchKF S ms ps ts with
      | some x, some y => some (x ++ y)
      | _, _ => none := by rw [matchKF]

/-- A substitution `matchK` gives is one `matchTs` gives under a substitution of the list. -/
theorem matchKF_mem {ps ts : List T} {B' : Bind} : ∀ {ms M : Ms}, matchKF S ms ps ts = some M →
    B' ∈ M → ∃ B₁ ∈ ms, ∃ M₁, matchTsF S ps ts B₁ = some M₁ ∧ B' ∈ M₁
  | [], M, h, hB => by rw [matchKF_nil] at h; cases h; cases hB
  | B :: ms, M, h, hB => by
    rw [matchKF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      rcases List.mem_append.mp hB with hB | hB
      · exact ⟨B, by simp, x, hx, hB⟩
      · obtain ⟨B₁, h1, M₁, h2, h3⟩ := matchKF_mem hy hB
        exact ⟨B₁, by simp [h1], M₁, h2, h3⟩
    · cases h

/-- `matchK` at one substitution is `matchTs` under it. -/
theorem matchKF_single {ps ts : List T} {B : Bind} {M : Ms} (h : matchTsF S ps ts B = some M) :
    matchKF S [B] ps ts = some M := by
  rw [matchKF_cons, matchKF_nil, h]; simp

/-! ### The collection equations -/

/-- `m-col`: the subject's own kind and sort are not read. -/
theorem matchF_cb_co (k l : Kind) (c e : Int) (ps es : List T) (B : Bind) :
    matchF S (.cb k c ps) (.co l e es) B = matchColF S k c ps es B := by rw [matchF]

/-- `m-col` is the one equation that gives a substitution at a collection pattern. -/
theorem matchF_cb_inv {k : Kind} {c : Int} {ps : List T} {a : T} {B B' : Bind} {M : Ms}
    (h : matchF S (.cb k c ps) a B = some M) (hB : B' ∈ M) :
    ∃ l e es, a = .co l e es ∧ matchColF S k c ps es B = some M := by
  cases a with
  | co l e es => rw [matchF_cb_co] at h; exact ⟨l, e, es, rfl, h⟩
  | _ => unfold matchF at h; simp at h; subst h; cases hB

/-- `m-kv`. -/
theorem matchF_kv_kv (p q a v : T) (B : Bind) :
    matchF S (.kv p q) (.kv a v) B = matchTsF S [p, q] [a, v] B := by rw [matchF]

/-- `m-el`. -/
theorem matchF_el_el (p x : T) (B : Bind) : matchF S (.el p) (.el x) B = matchF S p x B := by
  rw [matchF]

theorem matchF_kv_inv {p q a : T} {B B' : Bind} {M : Ms}
    (h : matchF S (.kv p q) a B = some M) (hB : B' ∈ M) :
    ∃ k v, a = .kv k v ∧ matchTsF S [p, q] [k, v] B = some M := by
  cases a with
  | kv k v => rw [matchF_kv_kv] at h; exact ⟨k, v, rfl, h⟩
  | _ => unfold matchF at h; simp at h; subst h; cases hB

theorem matchF_el_inv {p a : T} {B B' : Bind} {M : Ms}
    (h : matchF S (.el p) a B = some M) (hB : B' ∈ M) :
    ∃ x, a = .el x ∧ matchF S p x B = some M := by
  cases a with
  | el x => rw [matchF_el_el] at h; exact ⟨x, rfl, h⟩
  | _ => unfold matchF at h; simp at h; subst h; cases hB

/-- `mc-done`, and `mc-fail` at no part and an element. -/
theorem matchColF_nil (k : Kind) (c : Int) (es : List T) (B : Bind) :
    matchColF S k c [] es B = some (if es = [] then [B] else []) := by
  rw [matchColF.eq_def]; cases es <;> simp

/-- `mc-choose`. -/
theorem matchColF_choose {k : Kind} {p : T} (hp : isElemT p = true) (hk : k ≠ .list) (c : Int)
    (ps es : List T) (B : Bind) :
    matchColF S k c (p :: ps) es B = chooseF S k c p ps [] es B := by
  rw [matchColF.eq_def]; simp [hp, hk]

/-- `mc-head`. -/
theorem matchColF_head {p : T} (hp : isElemT p = true) (c : Int) (ps : List T) (e : T)
    (es : List T) (B : Bind) :
    matchColF S .list c (p :: ps) (e :: es) B =
      match matchF S p e B with
      | some ms => restF S .list c ps es ms
      | none => none := by
  rw [matchColF.eq_def]; simp [hp]

/-- `mc-fail` at a list's element part and no element. -/
theorem matchColF_head_nil {p : T} (hp : isElemT p = true) (c : Int) (ps : List T) (B : Bind) :
    matchColF S .list c (p :: ps) [] B = some [] := by
  rw [matchColF.eq_def]; simp [hp]

/-- `mc-frame`. -/
theorem matchColF_frame {f : T} (hf : isElemT f = false) (k : Kind) (c : Int) (es : List T)
    (B : Bind) : matchColF S k c [f] es B = matchF S f (.co k c es) B := by
  rw [matchColF.eq_def]; simp [hf]

/-- `mc-split`. -/
theorem matchColF_split {f : T} (hf : isElemT f = false) (c : Int) (p : T) (ps es : List T)
    (B : Bind) : matchColF S .list c (f :: p :: ps) es B = splitF S c f (p :: ps) [] es B := by
  rw [matchColF.eq_def]; simp [hf]

/-- `mc-fail` at a `Map`'s or a `Set`'s part that is no element and has parts after it. -/
theorem matchColF_frame_more {f : T} (hf : isElemT f = false) {k : Kind} (hk : k ≠ .list) (c : Int)
    (p : T) (ps es : List T) (B : Bind) : matchColF S k c (f :: p :: ps) es B = some [] := by
  rw [matchColF.eq_def]; simp [hf, hk]

theorem chooseF_nil (k : Kind) (c : Int) (p : T) (ps pre : List T) (B : Bind) :
    chooseF S k c p ps pre [] B = some [] := by rw [chooseF]

theorem chooseF_cons (k : Kind) (c : Int) (p : T) (ps pre : List T) (e : T) (post : List T)
    (B : Bind) :
    chooseF S k c p ps pre (e :: post) B =
      match (match matchF S p e B with
        | some ms => restF S k c ps (pre ++ post) ms
        | none => none), chooseF S k c p ps (pre ++ [e]) post B with
      | some x, some y => some (x ++ y)
      | _, _ => none := by rw [chooseF]

theorem splitF_eq (c : Int) (f : T) (ps pre post : List T) (B : Bind) :
    splitF S c f ps pre post B =
      match (match matchF S f (.co .list c pre) B with
        | some ms => restF S .list c ps post ms
        | none => none), splitOnF S c f ps pre post B with
      | some x, some y => some (x ++ y)
      | _, _ => none := by rw [splitF]

theorem splitOnF_nil (c : Int) (f : T) (ps pre : List T) (B : Bind) :
    splitOnF S c f ps pre [] B = some [] := by rw [splitOnF]

theorem splitOnF_cons (c : Int) (f : T) (ps pre : List T) (e : T) (post : List T) (B : Bind) :
    splitOnF S c f ps pre (e :: post) B = splitF S c f ps (pre ++ [e]) post B := by rw [splitOnF]

theorem restF_nil (k : Kind) (c : Int) (ps es : List T) : restF S k c ps es [] = some [] := by
  rw [restF]

theorem restF_cons (k : Kind) (c : Int) (ps es : List T) (B : Bind) (ms : Ms) :
    restF S k c ps es (B :: ms) =
      match matchColF S k c ps es B, restF S k c ps es ms with
      | some x, some y => some (x ++ y)
      | _, _ => none := by rw [restF]

/-- A substitution `rest` gives is one `matchCol` gives under a substitution of the list. -/
theorem restF_mem {k : Kind} {c : Int} {ps es : List T} {B' : Bind} : ∀ {ms M : Ms},
    restF S k c ps es ms = some M → B' ∈ M →
    ∃ B₁ ∈ ms, ∃ M₁, matchColF S k c ps es B₁ = some M₁ ∧ B' ∈ M₁
  | [], M, h, hB => by rw [restF_nil] at h; cases h; cases hB
  | B :: ms, M, h, hB => by
    rw [restF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      rcases List.mem_append.mp hB with hB | hB
      · exact ⟨B, by simp, x, hx, hB⟩
      · obtain ⟨B₁, h1, M₁, h2, h3⟩ := restF_mem hy hB
        exact ⟨B₁, by simp [h1], M₁, h2, h3⟩
    · cases h

/-- A substitution `choose` gives: the element part matched one element of `Post`, and the parts
after it the elements before and after that one. -/
theorem chooseF_mem {k : Kind} {c : Int} {p : T} {ps : List T} {B B' : Bind} :
    ∀ {post pre : List T} {M : Ms}, chooseF S k c p ps pre post B = some M → B' ∈ M →
    ∃ l e r M₁ B₁ M₂, post = l ++ e :: r ∧ matchF S p e B = some M₁ ∧ B₁ ∈ M₁ ∧
      matchColF S k c ps (pre ++ l ++ r) B₁ = some M₂ ∧ B' ∈ M₂
  | [], pre, M, h, hB => by rw [chooseF_nil] at h; cases h; cases hB
  | e :: post, pre, M, h, hB => by
    rw [chooseF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      rcases List.mem_append.mp hB with hB | hB
      · cases hm : matchF S p e B with
        | none => rw [hm] at hx; cases hx
        | some ms =>
          rw [hm] at hx
          obtain ⟨B₁, h1, M₂, h2, h3⟩ := restF_mem S hx hB
          exact ⟨[], e, post, ms, B₁, M₂, rfl, hm, h1, by simpa using h2, h3⟩
      · obtain ⟨l, e', r, M₁, B₁, M₂, rfl, h1, h2, h3, h4⟩ := chooseF_mem hy hB
        exact ⟨e :: l, e', r, M₁, B₁, M₂, rfl, h1, h2, by simpa using h3, h4⟩
    · cases h

/-- A substitution `split` gives: the first part matched the list of `Pre` and a prefix of `Post`,
and the parts after it the elements after that prefix. -/
theorem splitF_mem {c : Int} {f : T} {ps : List T} {B B' : Bind} :
    ∀ {post pre : List T} {M : Ms}, splitF S c f ps pre post B = some M → B' ∈ M →
    ∃ l r M₁ B₁ M₂, post = l ++ r ∧ matchF S f (.co .list c (pre ++ l)) B = some M₁ ∧ B₁ ∈ M₁ ∧
      matchColF S .list c ps r B₁ = some M₂ ∧ B' ∈ M₂ := by
  intro post
  induction post with
  | nil =>
    intro pre M h hB
    rw [splitF_eq, splitOnF_nil] at h
    cases hm : matchF S f (.co .list c pre) B with
    | none => rw [hm] at h; cases h
    | some ms =>
      rw [hm] at h
      cases hr : restF S .list c ps [] ms with
      | none => simp only [hr] at h; cases h
      | some x =>
        simp only [hr, List.append_nil, Option.some.injEq] at h
        subst h
        obtain ⟨B₁, h1, M₂, h2, h3⟩ := restF_mem S hr hB
        exact ⟨[], [], ms, B₁, M₂, rfl, by simpa using hm, h1, h2, h3⟩
  | cons e post ih =>
    intro pre M h hB
    rw [splitF_eq, splitOnF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      rcases List.mem_append.mp hB with hB | hB
      · cases hm : matchF S f (.co .list c pre) B with
        | none => rw [hm] at hx; cases hx
        | some ms =>
          rw [hm] at hx
          obtain ⟨B₁, h1, M₂, h2, h3⟩ := restF_mem S hx hB
          exact ⟨[], e :: post, ms, B₁, M₂, rfl, by simpa using hm, h1, h2, h3⟩
      · obtain ⟨l, r, M₁, B₁, M₂, rfl, h1, h2, h3, h4⟩ := ih hy hB
        exact ⟨e :: l, r, M₁, B₁, M₂, rfl, by simpa using h1, h2, h3, h4⟩
    · cases h

end

/-! ## `leq` on a transitive table -/

theorem aboveF_sound_kmf {b : Int} {All : List (Int × Int)}
    (htr : ∀ x y z, (x, y) ∈ All → (y, z) ∈ All → (x, z) ∈ All) :
    ∀ (F T : List (Int × Int)) (a : Int), (∀ e ∈ T, e ∈ All) → aboveF a b T All F = true →
      (a, b) ∈ All
  | [], [], _, _, h => by rw [aboveF] at h; cases h
  | [], _ :: _, _, _, h => by rw [aboveF] at h; cases h
  | _ :: _, [], _, _, h => by rw [aboveF] at h; cases h
  | pq :: f, (x, y) :: rest, a, hT, h => by
    rw [aboveF] at h
    have hxy : (x, y) ∈ All := hT _ (by simp)
    have hrest : ∀ e ∈ rest, e ∈ All := fun e he => hT e (by simp [he])
    split at h
    · rename_i hxa
      subst hxa
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (h | h) | h
      · subst h; exact hxy
      · exact htr _ _ _ hxy (aboveF_sound_kmf htr f All y (fun _ he => he) h)
      · exact aboveF_sound_kmf htr (pq :: f) rest x hrest h
    · exact aboveF_sound_kmf htr (pq :: f) rest a hrest h
  termination_by F T => (F.length, T.length)

theorem aboveF_complete_kmf {a b : Int} {All : List (Int × Int)} (pq : Int × Int)
    (f : List (Int × Int)) : ∀ (T : List (Int × Int)), (a, b) ∈ T → aboveF a b T All (pq :: f) = true
  | [], h => by cases h
  | (x, y) :: rest, h => by
    rw [aboveF]
    rcases List.mem_cons.mp h with h | h
    · cases h; simp
    · have := aboveF_complete_kmf (All := All) pq f rest h
      split <;> simp [this]

/-- On a transitive table, `leq(A, B, S)` is: `A` is `B` or `(A, B)` is an entry. -/
theorem leqF_eq {S : List (Int × Int)}
    (htr : ∀ x y z, (x, y) ∈ S → (y, z) ∈ S → (x, z) ∈ S) (a b : Int) :
    leqF a b S = (a == b || S.contains (a, b)) := by
  unfold leqF
  split
  · rename_i h; simp [h]
  · rename_i h
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, beq_iff_eq, h, false_or, List.contains_iff_mem]
    constructor
    · exact aboveF_sound_kmf htr S S a (fun _ he => he)
    · intro hm
      cases S with
      | nil => cases hm
      | cons pq f => exact aboveF_complete_kmf pq f _ hm

/-- The subsort table of `c` as `kore.k` holds it (`encDef`'s `subs`). -/
def subsF (c : Semantics) : List (Int × Int) := c.subsorts.map fun (a, b) => ((a : Int), (b : Int))

theorem encDef_subs {d : Semantics} {E : D} (h : encDef d = some E) : E.subs = subsF d := by
  unfold encDef at h
  split at h
  · cases h; rfl
  · cases h

theorem mem_subsF_kmf {c : Semantics} {a b : Srt} : ((a : Int), (b : Int)) ∈ subsF c ↔ (a, b) ∈ c.subsorts := by
  simp only [subsF, List.mem_map, Prod.exists, Prod.mk.injEq, Int.natCast_inj]
  constructor
  · rintro ⟨x, y, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨a, b, h, rfl, rfl⟩

/-- Under transitive subsorts, `leq` on the table of `c` is: the same sort, or a stated subsort. -/
theorem leqF_subsF {c : Semantics}
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) (a b : Srt) :
    leqF (a : Int) (b : Int) (subsF c) = (a == b || c.subsorts.contains (a, b)) := by
  rw [leqF_eq]
  · rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, mem_subsF_kmf, Int.natCast_inj]
  · intro x y z hxy hyz
    simp only [subsF, List.mem_map, Prod.exists, Prod.mk.injEq] at hxy hyz ⊢
    obtain ⟨p, q, h1, rfl, rfl⟩ := hxy
    obtain ⟨q', r, h2, hq, rfl⟩ := hyz
    have : q' = q := Int.natCast_inj.mp hq
    subst this
    exact ⟨p, r, htr _ _ _ h1 h2, rfl, rfl⟩

end KCore.KK
