import KcoreSpec.KKLitsVPatVal
import KcoreSpec.CollExecStep
import KcoreSpec.KKEncCanon

/-!
# `kore.k`'s matching of a pattern without a collection

`matchF`, `matchTsF`, `matchKF`, `bindAfterF`, `lookF`, `bindVarF`, `leqF` and `aboveF` are
`kore.k`'s functions `match`, `matchTs`, `matchK`, `bindAfter`, `look`, `bindVar`, `leq` and `above`
over the mirrors, one Lean equation per equation of `kore.k`; `cat` is `++`. A substitution `Bind`
is `kore.k`'s list `bind(X, T, B)`, newest entry first, and `Ms` the list of substitutions a match
gives.

`matchTs` has an equation for two empty lists and for two non-empty lists only, so `matchTsF` is
`none` at lists of two lengths, where `kore.k`'s `matchTs` has no value; a function applied to an
argument without a value has none, so `matchF`, `matchKF` and `matchTsF` give `Option Ms`.
`match` of a collection pattern (`cb`) against a collection (`co`) is `matchCol`, which is not
mirrored here: `matchF` is `none` there, and every statement below is about a pattern without `cb`
(`noCb`).

The statements are about one semantics `c`: `matchF_sound` and `matchF_complete` relate `matchF` at
the encoding of a pattern (`encTerm`) and of a value (`enc`) to `PatVal c`. The pattern is well
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
  | .cb _ _ _, a, _ => match a with
    | .co _ _ _ => none
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

theorem matchTsF_nil (B : Bind) : matchTsF S [] [] B = some [B] := by rw [matchTsF]

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
