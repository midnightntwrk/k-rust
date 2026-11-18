import KcoreSpec.KKMatchColSpec

/-!
# `match` has a value, and finds every substitution a denotation gives

`match` has no value only where `matchTs` is applied at two lists of different lengths, and
`matchTs` is applied only at the arguments of two applications of one symbol (and at the two
halves of two map entries). `ArT A t`: every application in `t` has an arity `A` allows.
`matchF_isSome_kct`: where the pattern's applications have the arities `Ap` allows, the subject's
those `Av` allows, and the two agree on a symbol both have, `match` has a value at every
substitution, and so do `matchTs`, `matchCol`, `choose`, `split` and `rest` (the elements a
collection pattern's parts are matched against, and the terms `match` builds, an injection or the
collection of the elements left, are made of the subject's applications). No sort is read.

`matchF_total`: at the encoding of a pattern sorted in a left side's context and the encoding of a
value sorted in `c` (any two sorts), `match` has a value, where `c` has no overloading symbol: a
pattern's application `ap f` is a constructor or a function that is no parameter at its
signature's arity, a value's `ap f` a constructor at its signature's arity or an open parameter
symbol, which no pattern writes as `ap`.

`matchF_of_den`: the converse of `matchF_den`. Where under `Bρ` the pattern form is the term
(`DenF`) and the given substitution's entries are `Bρ`'s, every value `match` gives holds a
substitution whose entries are `Bρ`'s, which states the match. With `bindOfSubst σ` as `Bρ`,
`BindAgree B σ` is `BindExt B (bindOfSubst σ)`. `varsIn_kct`: a pattern's encoding holds its
variables. `matchF_complete_of_den` puts the three together at encodings: where under `σ` encoded
the encoding of a sorted pattern is the encoding of a sorted value, `match` has a value that holds a
substitution agreeing with `σ` and binding every variable of the pattern; a `Map` or `Set` pattern
with an element whose key is unbound gives several.
-/

set_option autoImplicit false

namespace KCore.KK

/-! ## Arities -/

/-- Every application in the term has an arity `A` allows. Below an operation, a right side with
its ensures and `bot` nothing is read: no equation of `match` looks into them. -/
inductive ArT (A : Int → Nat → Prop) : T → Prop where
  | ap {f : Int} {ts : List T} (h : A f ts.length) (hs : ∀ t ∈ ts, ArT A t) : ArT A (.ap f ts)
  | iv (i : Int) : ArT A (.iv i)
  | bv (b : Bool) : ArT A (.bv b)
  | tk (s : Int) (x : String) : ArT A (.tk s x)
  | vr (x : Int) : ArT A (.vr x)
  | ij {a b : Int} {t : T} (h : ArT A t) : ArT A (.ij a b t)
  | as {t : T} {x : Int} (h : ArT A t) : ArT A (.as t x)
  | hk (o : Int) (as : List T) : ArT A (.hk o as)
  | bot : ArT A .bot
  | cb {k : Kind} {c : Int} {ps : List T} (hs : ∀ t ∈ ps, ArT A t) : ArT A (.cb k c ps)
  | co {k : Kind} {c : Int} {es : List T} (hs : ∀ t ∈ es, ArT A t) : ArT A (.co k c es)
  | en (t e : T) : ArT A (.en t e)
  | kv {a v : T} (ha : ArT A a) (hv : ArT A v) : ArT A (.kv a v)
  | el {x : T} (h : ArT A x) : ArT A (.el x)

/-! ## The functions over lists have a value where their components have -/

section
variable (S : List (Int × Int))

theorem matchKF_isSome_kct {ps ts : List T} (h : ∀ B, (matchTsF S ps ts B).isSome = true) :
    ∀ ms, (matchKF S ms ps ts).isSome = true
  | [] => by rw [matchKF_nil]; rfl
  | B :: ms => by
    rw [matchKF_cons]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h B)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (matchKF_isSome_kct h ms)
    rw [hx, hy]; rfl

theorem restF_isSome_kct {k : Kind} {c : Int} {ps es : List T}
    (h : ∀ B, (matchColF S k c ps es B).isSome = true) : ∀ ms, (restF S k c ps es ms).isSome = true
  | [] => by rw [restF_nil]; rfl
  | B :: ms => by
    rw [restF_cons]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h B)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (restF_isSome_kct h ms)
    rw [hx, hy]; rfl

theorem chooseF_isSome_kct {k : Kind} {c : Int} {p : T} {ps : List T} {B : Bind} (Q : T → Prop)
    (hm : ∀ e, Q e → (matchF S p e B).isSome = true)
    (hr : ∀ l, (∀ x ∈ l, Q x) → ∀ B', (matchColF S k c ps l B').isSome = true) :
    ∀ (post pre : List T), (∀ x ∈ pre, Q x) → (∀ x ∈ post, Q x) →
      (chooseF S k c p ps pre post B).isSome = true
  | [], pre, _, _ => by rw [chooseF_nil]; rfl
  | e :: post, pre, hpre, hpost => by
    rw [chooseF_cons]
    obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp (hm e (hpost e (by simp)))
    have hl : ∀ x ∈ pre ++ post, Q x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpre x hx
      · exact hpost x (by simp [hx])
    have hl' : ∀ x ∈ pre ++ [e], Q x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpre x hx
      · rw [List.mem_singleton.mp hx]; exact hpost e (by simp)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (restF_isSome_kct S (hr _ hl) ms)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
      (chooseF_isSome_kct Q hm hr post (pre ++ [e]) hl' fun x hx => hpost x (by simp [hx]))
    simp only [hms, hx, hy, Option.isSome_some]

theorem splitF_isSome_kct {c : Int} {f : T} {ps : List T} {B : Bind} (Q : T → Prop)
    (hm : ∀ l, (∀ x ∈ l, Q x) → (matchF S f (.co .list c l) B).isSome = true)
    (hr : ∀ l, (∀ x ∈ l, Q x) → ∀ B', (matchColF S .list c ps l B').isSome = true) :
    ∀ (post pre : List T), (∀ x ∈ pre, Q x) → (∀ x ∈ post, Q x) →
      (splitF S c f ps pre post B).isSome = true
  | [], pre, hpre, _ => by
    rw [splitF_eq, splitOnF_nil]
    obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp (hm pre hpre)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
      (restF_isSome_kct S (hr [] (fun _ h => nomatch h)) ms)
    simp only [hms, hx, Option.isSome_some]
  | e :: post, pre, hpre, hpost => by
    rw [splitF_eq, splitOnF_cons]
    obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp (hm pre hpre)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (restF_isSome_kct S (hr _ hpost) ms)
    have hl' : ∀ x ∈ pre ++ [e], Q x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpre x hx
      · rw [List.mem_singleton.mp hx]; exact hpost e (by simp)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
      (splitF_isSome_kct Q hm hr post (pre ++ [e]) hl' fun x hx => hpost x (by simp [hx]))
    simp only [hms, hx, hy, Option.isSome_some]

end

/-! ## `match` has a value -/

section
variable {Ap Av : Int → Nat → Prop} (hA : ∀ f n m, Ap f n → Av f m → n = m)
  (S : List (Int × Int))
include hA
set_option linter.unusedSectionVars false

mutual
/-- **`match` has a value** where the two terms' applications have arities that agree. -/
theorem matchF_isSome_kct : ∀ (p a : T) (B : Bind), ArT Ap p → ArT Av a →
    (matchF S p a B).isSome = true
  | .vr x, a, B, _, _ => by rw [matchF_vr]; rfl
  | .iv i, a, B, _, _ => by rw [matchF_iv]; rfl
  | .bv b, a, B, _, _ => by rw [matchF_bv]; rfl
  | .tk s x, a, B, _, _ => by rw [matchF_tk]; rfl
  | .hk o as, a, B, _, _ => by rw [matchF_hk]; rfl
  | .bot, a, B, _, _ => by rw [matchF_bot]; rfl
  | .co k c es, a, B, _, _ => by rw [matchF_co]; rfl
  | .en t e, a, B, _, _ => by rw [matchF_en]; rfl
  | .ap f ps, a, B, hp, ha => by
    cases a with
    | ap g ts =>
      rw [matchF_ap_ap]
      split
      · rename_i hfg
        subst hfg
        cases hp with
        | ap hf hps =>
          cases ha with
          | ap hg hts => exact matchTsF_isSome_kct ps ts B (hA _ _ _ hf hg) hps hts
      · rfl
    | _ => unfold matchF; simp
  | .ij a b p, u, B, hp, hu => by
    cases hp with
    | ij hp' =>
      cases u with
      | ij c e t =>
        cases hu with
        | ij ht =>
          rw [matchF_ij_ij]
          split
          · exact matchF_isSome_kct p t B hp' ht
          · split
            · exact matchF_isSome_kct p (.ij c a t) B hp' (.ij ht)
            · rfl
      | _ => unfold matchF; simp
  | .as p x, a, B, hp, ha => by
    cases hp with
    | as hp' =>
      rw [matchF_as]
      obtain ⟨M, hM⟩ := Option.isSome_iff_exists.mp (matchF_isSome_kct p a B hp' ha)
      rw [hM]; rfl
  | .cb k c ps, a, B, hp, ha => by
    cases hp with
    | cb hps =>
      cases a with
      | co l e es =>
        cases ha with
        | co hes => rw [matchF_cb_co]; exact matchColF_isSome_kct k c ps es B hps hes
      | _ => unfold matchF; simp
  | .kv p q, a, B, hp, ha => by
    cases hp with
    | kv hp1 hp2 =>
      cases a with
      | kv x v =>
        cases ha with
        | kv hx hv =>
          rw [matchF_kv_kv]
          refine matchTsF_isSome_kct [p, q] [x, v] B rfl ?_ ?_
          · intro t ht
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · exact hp1
            · exact hp2
          · intro t ht
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · exact hx
            · exact hv
      | _ => unfold matchF; simp
  | .el p, a, B, hp, ha => by
    cases hp with
    | el hp' =>
      cases a with
      | el x =>
        cases ha with
        | el hx => rw [matchF_el_el]; exact matchF_isSome_kct p x B hp' hx
      | _ => unfold matchF; simp
  termination_by p => psizeF p
  decreasing_by
    all_goals simp_wf
    all_goals (simp only [psizeF, psizeLF] <;> omega)
/-- `matchTs` has a value at two lists of one length. -/
theorem matchTsF_isSome_kct : ∀ (ps ts : List T) (B : Bind), ps.length = ts.length →
    (∀ p ∈ ps, ArT Ap p) → (∀ t ∈ ts, ArT Av t) → (matchTsF S ps ts B).isSome = true
  | [], [], B, _, _, _ => by rw [matchTsF_nil]; rfl
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | p :: ps, t :: ts, B, hl, hps, hts => by
    rw [matchTsF_cons]
    obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp
      (matchF_isSome_kct p t B (hps p (by simp)) (hts t (by simp)))
    simp only [hms]
    exact matchKF_isSome_kct S (fun B' => matchTsF_isSome_kct ps ts B' (by simpa using hl)
      (fun x hx => hps x (by simp [hx])) (fun x hx => hts x (by simp [hx]))) ms
  termination_by ps => psizeLF ps
  decreasing_by
    all_goals simp_wf
    all_goals (simp only [psizeLF] <;> omega)
/-- `matchCol` has a value. -/
theorem matchColF_isSome_kct : ∀ (k : Kind) (c : Int) (ps es : List T) (B : Bind),
    (∀ p ∈ ps, ArT Ap p) → (∀ e ∈ es, ArT Av e) → (matchColF S k c ps es B).isSome = true
  | k, c, [], es, B, _, _ => by rw [matchColF_nil]; rfl
  | k, c, p :: ps, es, B, hps, hes => by
    have hp' : ArT Ap p := hps p (by simp)
    have hps' : ∀ x ∈ ps, ArT Ap x := fun x hx => hps x (by simp [hx])
    cases hp : isElemT p with
    | true =>
      by_cases hk : k = .list
      · subst hk
        cases es with
        | nil => rw [matchColF_head_nil S hp]; rfl
        | cons e es =>
          rw [matchColF_head S hp]
          obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp
            (matchF_isSome_kct p e B hp' (hes e (by simp)))
          simp only [hms]
          exact restF_isSome_kct S (fun B' => matchColF_isSome_kct .list c ps es B' hps'
            (fun x hx => hes x (by simp [hx]))) ms
      · rw [matchColF_choose S hp hk]
        exact chooseF_isSome_kct S (ArT Av) (fun e he => matchF_isSome_kct p e B hp' he)
          (fun l hl B' => matchColF_isSome_kct k c ps l B' hps' hl) es [] (fun _ h => nomatch h) hes
    | false =>
      by_cases hnil : ps = []
      · subst hnil
        rw [matchColF_frame S hp]; exact matchF_isSome_kct p (.co k c es) B hp' (.co hes)
      · obtain ⟨q, qs, hqs⟩ : ∃ q qs, ps = q :: qs := by
          cases ps with
          | nil => exact absurd rfl hnil
          | cons q qs => exact ⟨q, qs, rfl⟩
        by_cases hk : k = .list
        · subst hk
          rw [hqs, matchColF_split S hp, ← hqs]
          exact splitF_isSome_kct S (ArT Av)
            (fun l hl => matchF_isSome_kct p (.co .list c l) B hp' (.co hl))
            (fun l hl B' => matchColF_isSome_kct .list c ps l B' hps' hl) es []
            (fun _ h => nomatch h) hes
        · rw [hqs, matchColF_frame_more S hp hk]; rfl
  termination_by _ _ ps => psizeLF ps
  decreasing_by
    all_goals simp_wf
    all_goals (simp only [psizeLF] <;> omega)
end

end

/-! ## The arities of encodings -/

/-- An arity a pattern of `c` writes: `ap f` at a constructor or a function that is no parameter,
with as many arguments as its signature in a left side's context. -/
def patArity (c : Semantics) (f : Int) (n : Nat) : Prop :=
  ∃ g : Sym, f = g ∧ (c.isCtor g = true ∨ c.isParam g = false) ∧
    ∃ k, lookupSig c.patCtxAll.heads g = some k ∧ k.args.length = n

/-- An arity a value sorted in `c` has: `ap f` at as many arguments as a sorted application. -/
def valArity (c : Semantics) (f : Int) (n : Nat) : Prop :=
  ∃ (g : Sym) (vs : List GroundTerm) (s : Srt), f = g ∧ c.sortOf (.ctor g vs) = some s ∧
    vs.length = n

theorem sortsOf_length_kct {c : Semantics} : ∀ {vs : List GroundTerm} {ss : List Srt},
    c.sortsOf vs = some ss → vs.length = ss.length
  | [], ss, h => by
    simp only [Semantics.sortsOf, Option.some.injEq] at h; subst h; rfl
  | v :: vs, ss, h => by
    obtain ⟨s, ss', -, h2, rfl⟩ := sortsOf_cons.mp h
    simp [sortsOf_length_kct h2]

theorem sortsOfTerms_length_kct {x : TermCtx} {vars : List Srt} : ∀ {ts : List Term} {ss : List Srt},
    sortsOfTerms x vars ts = some ss → ts.length = ss.length
  | [], ss, h => by rw [sortsOfTerms_nil.mp h]; rfl
  | t :: ts, ss, h => by
    obtain ⟨s, ss', -, h2, rfl⟩ := sortsOfTerms_cons.mp h
    simp [sortsOfTerms_length_kct h2]

theorem sortsOfTerms_mem_kct {x : TermCtx} {vars : List Srt} : ∀ {ts : List Term} {ss : List Srt},
    sortsOfTerms x vars ts = some ss → ∀ t ∈ ts, ∃ s, sortOfTerm x vars t = some s
  | [], _, _, t, ht => nomatch ht
  | u :: ts, ss, h, t, ht => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨s, h1⟩
    · exact sortsOfTerms_mem_kct h2 t ht

/-- The arities patterns and values of `c` have agree, where `c` has no overloading symbol. -/
theorem arity_agree_kct {c : Semantics} (hov : c.ovls = []) :
    ∀ f n m, patArity c f n → valArity c f m → n = m := by
  rintro f n m ⟨g, rfl, hcp, k, hk, rfl⟩ ⟨g', vs, s, hgg, hv, rfl⟩
  have : g' = g := (Int.natCast_inj.mp hgg).symm
  subst this
  rcases c.sortOf_ctor_iff.mp hv with ⟨k', hk', hs, -⟩ | ⟨-, o, ho, -⟩ | ⟨hn, -, k', hk', -⟩
  · rw [lookupSig_patCtxAll_kmf hk'] at hk
    cases hk
    exact (sortsOf_length_kct hs).symm
  · simp [Semantics.lookupOvl, hov] at ho
  · rcases hcp with hcp | hcp
    · simp [Semantics.isCtor, hn] at hcp
    · rw [isParam_of_lookupOpen_kmf hk'] at hcp; cases hcp

/-- The encoding of a value sorted in `c` has the arities of `c`'s values. -/
theorem arT_enc_kct {c : Semantics} (hov : c.ovls = []) (v : GroundTerm) :
    ∀ s, c.sortOf v = some s → ArT (valArity c) (enc v) := by
  induction v using gtInd_kel with
  | hctor f vs ih =>
    intro s hv
    rw [enc_ctor_kmf]
    have hsub : ∃ ss, c.sortsOf vs = some ss := by
      rcases sortOf_ctor_kel hov hv with ⟨k, -, h⟩ | ⟨k, -, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    obtain ⟨ss, hss⟩ := hsub
    refine .ap ⟨f, vs, s, rfl, hv, by rw [encTs_eq_map]; simp⟩ fun t ht => ?_
    rw [encTs_eq_map] at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    obtain ⟨s', -, hs'⟩ := sortsOf_mem_kel hss w hw
    exact ih w hw s' hs'
  | hinj a b t ih =>
    intro s hv
    rw [enc_inj_form_kmf]
    exact .ij (ih a (sortOf_inj_kel hv).2.2.1)
  | hdv s l =>
    intro _ _
    rcases enc_dv_cases_kkc s l with ⟨i, h⟩ | ⟨b, h⟩ | ⟨t, x, h⟩ | h <;> rw [h]
    · exact .iv i
    · exact .bv b
    · exact .tk t x
    · exact .bot
  | hmap s' es ih =>
    intro s hv
    obtain ⟨k, vs, -, -, -, he⟩ := sortOf_map_kel hv
    rw [enc]
    refine .co fun t ht => ?_
    rw [mem_sortK, encKvs_eq_map] at ht
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp ht
    obtain ⟨h1, h2⟩ := entriesOK_mem_kel he e he'
    exact .kv ((ih e he').1 _ h1) ((ih e he').2 _ h2)
  | hset s' es ih =>
    intro s hv
    obtain ⟨k, ss, -, -, hss, -⟩ := sortOf_set_kel hv
    rw [enc]
    refine .co fun t ht => ?_
    rw [mem_sortK, encEls_eq_map] at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    obtain ⟨s'', -, hs''⟩ := sortsOf_mem_kel hss w hw
    exact .el (ih w hw s'' hs'')
  | hlist s' es ih =>
    intro s hv
    obtain ⟨k, ss, -, hss, -⟩ := sortOf_list_kel hv
    rw [enc]
    refine .co fun t ht => ?_
    rw [encEls_eq_map] at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    obtain ⟨s'', -, hs''⟩ := sortsOf_mem_kel hss w hw
    exact .el (ih w hw s'' hs'')

section
variable {c : Semantics}

theorem encTermsWith_mem_kct : ∀ {ts : List Term} {qs : List T},
    encTermsWith c encLit ts = some qs → qs.length = ts.length ∧
      ∀ q ∈ qs, ∃ t ∈ ts, encTerm c t = some q
  | [], qs, h => by cases encTerms_nil_kmf c h; exact ⟨rfl, fun _ h => nomatch h⟩
  | t :: ts, qs, h => by
    obtain ⟨q, qs', h1, h2, rfl⟩ := encTerms_cons_kmf c h
    obtain ⟨g1, g2⟩ := encTermsWith_mem_kct h2
    refine ⟨by simp [g1], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨t, by simp, h1⟩
    · obtain ⟨u, hu, h⟩ := g2 x hx
      exact ⟨u, by simp [hu], h⟩

theorem mem_orderParts_kct {k : Kind} {ps : List T} {q : T} (h : q ∈ orderParts k ps) : q ∈ ps := by
  unfold orderParts at h
  split at h
  · exact h
  · rcases List.mem_append.mp h with h | h
    · exact (List.mem_filter.mp h).1
    · exact (List.mem_filter.mp h).1

/-- `readApp`'s form, from arguments of a signature's arity and parts with the arities of `c`'s
patterns. -/
theorem readApp_arT_kct {f : Sym} {args parts : Option (List T)} {q : T}
    (hsig : ∃ k, lookupSig c.patCtxAll.heads f = some k ∧
      ∀ qs, args = some qs → k.args.length = qs.length)
    (hargs : ∀ qs, args = some qs → ∀ q ∈ qs, ArT (patArity c) q)
    (hparts : ∀ ps, parts = some ps → ∀ q ∈ ps, ArT (patArity c) q)
    (h : readApp c f args parts = some q) : ArT (patArity c) q := by
  obtain ⟨k, hk, hlen⟩ := hsig
  unfold readApp at h
  split at h
  · rename_i hc
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .ap ⟨f, rfl, .inl hc, k, hk, hlen qs hqs⟩ (hargs qs hqs)
  · split at h
    · obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .cb fun x hx => hparts ps hps x (mem_orderParts_kct hx)
    · split at h
      · split at h
        · obtain ⟨qs, -, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .hk _ _
        · obtain ⟨qs, -, h'⟩ := Option.bind_eq_some_iff.mp h
          unfold derivedHook at h'
          split at h'
          · cases h'; exact .hk _ _
          · cases h'
      · split at h
        · cases h
        · rename_i hp
          split at h
          · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
            exact .ap ⟨f, rfl, .inr (by simpa using hp), k, hk, hlen qs hqs⟩ (hargs qs hqs)
          · cases h

variable {vars : List Srt}

/-- What the induction gives of a sorted term: its form and its parts as a concatenation's argument
have the arities of `c`'s patterns. -/
def PatAr_kct (c : Semantics) (vars : List Srt) (t : Term) : Prop :=
  (∃ s, sortOfTerm c.patCtxAll vars t = some s) →
    (∀ q, encTerm c t = some q → ArT (patArity c) q) ∧
      ∀ k s qs, encPartWith c encLit k s t = some qs → ∀ q ∈ qs, ArT (patArity c) q

theorem encTermsWith_arT_kct {ts : List Term} (ih : ∀ t ∈ ts, PatAr_kct c vars t)
    (hs : ∀ t ∈ ts, ∃ s, sortOfTerm c.patCtxAll vars t = some s) {qs : List T}
    (h : encTermsWith c encLit ts = some qs) : ∀ q ∈ qs, ArT (patArity c) q := by
  intro q hq
  obtain ⟨t, ht, h'⟩ := (encTermsWith_mem_kct h).2 q hq
  exact (ih t ht (hs t ht)).1 q h'

theorem encCollWith_arT_kct {ts : List Term} (ih : ∀ t ∈ ts, PatAr_kct c vars t)
    (hs : ∀ t ∈ ts, ∃ s, sortOfTerm c.patCtxAll vars t = some s) (k : Kind) (s : Srt) (r : CRole)
    {ps : List T} (h : encCollWith c encLit k s r ts = some ps) : ∀ q ∈ ps, ArT (patArity c) q := by
  rcases ts with _ | ⟨x, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
  · simp only [encCollWith] at h
    split at h
    · cases h; intro q hq; cases hq
    · cases h
  · simp only [encCollWith] at h
    split at h
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact .el ((ih x (by simp) (hs x (by simp))).1 p hp)
    · cases h
  · have ha := ih x (by simp) (hs x (by simp))
    have hv := ih v (by simp) (hs v (by simp))
    simp only [encCollWith] at h
    split at h
    · split at h
      · rename_i p q' hp hq
        cases h
        intro y hy
        rw [List.mem_singleton.mp hy]
        exact .kv (ha.1 p hp) (hv.1 q' hq)
      · cases h
    · split at h
      · split at h
        · rename_i p q' hp hq
          cases h
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact ha.2 k s p hp y hy
          · exact hv.2 k s q' hq y hy
        · cases h
      · cases h
  · simp only [encCollWith] at h; cases h

/-- The encoding of a term sorted in a left side's context has the arities of `c`'s patterns. -/
theorem patAr_kct (t : Term) : PatAr_kct c vars t := by
  induction t using termInd_kel with
  | hvar i =>
    intro _
    refine ⟨fun q hq => ?_, fun k s qs hq => ?_⟩
    · rw [encTerm_var_kmf] at hq; cases hq; exact .vr _
    · simp only [encPartWith, Option.some.injEq] at hq
      subst hq; intro q hq; rw [List.mem_singleton.mp hq]; exact .vr _
  | hdv s l =>
    intro _
    have hlit : ∀ q, encLit s l = some q → ArT (patArity c) q := by
      intro q hq
      rcases encLit_some hq with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩
      · exact .iv i
      · exact .bv b
      · exact .tk _ x
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_dv_kmf] at hq; exact hlit q hq
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro q hq; rw [List.mem_singleton.mp hq]; exact hlit p hp
  | hinj a b t ih =>
    rintro ⟨s, hs⟩
    obtain ⟨-, ht, -⟩ := sortOfTerm_inj.mp hs
    have ih' := (ih ⟨a, ht⟩).1
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_inj_kmf] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact .ij (ih' p hp)
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro q hq; rw [List.mem_singleton.mp hq]; exact .ij (ih' p hp)
  | has t i ih =>
    rintro ⟨s, hs⟩
    obtain ⟨-, ht⟩ := Exec.sortOfTerm_as hs
    have ih' := (ih ⟨s, ht⟩).1
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_as_kmf] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact .as (ih' p hp)
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro q hq; rw [List.mem_singleton.mp hq]; exact .as (ih' p hp)
  | happ f ts ih =>
    rintro ⟨s, hs⟩
    obtain ⟨k, hk, hts, -⟩ := sortOfTerm_app.mp hs
    have hsub := sortsOfTerms_mem_kct hts
    have hsig : ∃ k, lookupSig c.patCtxAll.heads f = some k ∧
        ∀ qs, encTermsWith c encLit ts = some qs → k.args.length = qs.length :=
      ⟨k, hk, fun qs hqs => by
        rw [(encTermsWith_mem_kct hqs).1, sortsOfTerms_length_kct hts]⟩
    have hargs := fun qs (h : encTermsWith c encLit ts = some qs) => encTermsWith_arT_kct ih hsub h
    have hcoll : ∀ k' s' r ps, encCollWith c encLit k' s' r ts = some ps →
        ∀ q ∈ ps, ArT (patArity c) q := fun k' s' r ps h => encCollWith_arT_kct ih hsub k' s' r h
    have hparts : ∀ ps, ((collSymOf c f).bind fun (k', s', r) => encCollWith c encLit k' s' r ts) =
        some ps → ∀ q ∈ ps, ArT (patArity c) q := by
      intro ps h
      obtain ⟨⟨k', s', r⟩, -, h'⟩ := Option.bind_eq_some_iff.mp h
      exact hcoll k' s' r ps h'
    refine ⟨fun q hq => ?_, fun k₀ s₀ qs hq => ?_⟩
    · rw [encTerm_app_kmf] at hq
      exact readApp_arT_kct hsig hargs hparts hq
    · simp only [encPartWith] at hq
      split at hq
      · rename_i k' s' r _ _
        split at hq
        · exact hcoll _ _ _ _ hq
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
          intro q hq'; rw [List.mem_singleton.mp hq']
          exact readApp_arT_kct hsig hargs (fun ps h => hcoll _ _ _ ps h) hp
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
        intro q hq'; rw [List.mem_singleton.mp hq']
        exact readApp_arT_kct hsig hargs hparts hp

end

/-! ## At encodings -/

/-- **`match` has a value at encodings.** At the encoding of a pattern sorted in a left side's
context and of a value sorted in `c`, at any two sorts, `match` has a value at every subsort table
and substitution, where `c` has no overloading symbol. -/
theorem matchF_total {c : Semantics} (hov : c.ovls = []) {vars : List Srt} {p : Term} {q : T}
    {s s' : Srt} {v : GroundTerm} (hq : encTerm c p = some q)
    (hp : sortOfTerm c.patCtxNF vars p = some s) (hv : c.sortOf v = some s')
    (S : List (Int × Int)) (B : Bind) : (matchF S q (enc v) B).isSome = true :=
  matchF_isSome_kct (arity_agree_kct hov) S q (enc v) B
    ((patAr_kct p ⟨s, sortOfTerm_all_of_nf hp⟩).1 q hq) (arT_enc_kct hov v s' hv)

/-- The same of `matchTs`: patterns sorted at the sorts of the values. -/
theorem matchTsF_total {c : Semantics} (hov : c.ovls = []) {vars : List Srt} {ps : List Term}
    {qs : List T} {ss : List Srt} {vs : List GroundTerm} (hq : encTermsWith c encLit ps = some qs)
    (hp : sortsOfTerms c.patCtxNF vars ps = some ss) (hv : c.sortsOf vs = some ss)
    (S : List (Int × Int)) (B : Bind) : (matchTsF S qs (encTs vs) B).isSome = true := by
  have hp' := sortsOfTerms_all_of_nf hp
  refine matchTsF_isSome_kct (arity_agree_kct hov) S qs (encTs vs) B ?_
    (encTermsWith_arT_kct (fun t _ => patAr_kct t) (sortsOfTerms_mem_kct hp') hq) ?_
  · rw [(encTermsWith_mem_kct hq).1, encTs_eq_map, List.length_map, sortsOfTerms_length_kct hp,
      sortsOf_length_kct hv]
  · intro t ht
    rw [encTs_eq_map] at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    obtain ⟨s', -, hs'⟩ := sortsOf_mem_kel hv w hw
    exact arT_enc_kct hov w s' hs'

/-! ## `match` finds what a denotation gives -/

section
variable (S : List (Int × Int))

theorem matchKF_sub_kct {ps ts : List T} : ∀ {ms M : Ms}, matchKF S ms ps ts = some M →
    ∀ B₁ ∈ ms, ∃ M₁, matchTsF S ps ts B₁ = some M₁ ∧ ∀ B' ∈ M₁, B' ∈ M
  | [], _, _, _, h => nomatch h
  | B :: ms, M, h, B₁, hB => by
    rw [matchKF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      rcases List.mem_cons.mp hB with rfl | hB
      · exact ⟨x, hx, fun _ h => List.mem_append_left _ h⟩
      · obtain ⟨M₁, h1, h2⟩ := matchKF_sub_kct hy B₁ hB
        exact ⟨M₁, h1, fun B' h => List.mem_append_right _ (h2 B' h)⟩
    · cases h

theorem restF_sub_kct {k : Kind} {c : Int} {ps es : List T} : ∀ {ms M : Ms},
    restF S k c ps es ms = some M →
    ∀ B₁ ∈ ms, ∃ M₁, matchColF S k c ps es B₁ = some M₁ ∧ ∀ B' ∈ M₁, B' ∈ M
  | [], _, _, _, h => nomatch h
  | B :: ms, M, h, B₁, hB => by
    rw [restF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      rcases List.mem_cons.mp hB with rfl | hB
      · exact ⟨x, hx, fun _ h => List.mem_append_left _ h⟩
      · obtain ⟨M₁, h1, h2⟩ := restF_sub_kct hy B₁ hB
        exact ⟨M₁, h1, fun B' h => List.mem_append_right _ (h2 B' h)⟩
    · cases h

theorem chooseF_sub_kct {k : Kind} {c : Int} {p : T} {ps : List T} {B : Bind} {e : T}
    {r : List T} : ∀ (l pre : List T) {M : Ms}, chooseF S k c p ps pre (l ++ e :: r) B = some M →
    ∃ M₁, matchF S p e B = some M₁ ∧ ∀ B₁ ∈ M₁, ∃ M₂, matchColF S k c ps (pre ++ l ++ r) B₁ = some M₂ ∧
      ∀ B' ∈ M₂, B' ∈ M
  | [], pre, M, h => by
    rw [List.nil_append, chooseF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      cases hm : matchF S p e B with
      | none => rw [hm] at hx; cases hx
      | some ms =>
        rw [hm] at hx
        refine ⟨ms, rfl, fun B₁ hB₁ => ?_⟩
        obtain ⟨M₂, h1, h2⟩ := restF_sub_kct S hx B₁ hB₁
        exact ⟨M₂, by simpa using h1, fun B' h => List.mem_append_left _ (h2 B' h)⟩
    · cases h
  | e' :: l, pre, M, h => by
    rw [List.cons_append, chooseF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      obtain ⟨M₁, h1, h2⟩ := chooseF_sub_kct l (pre ++ [e']) hy
      refine ⟨M₁, h1, fun B₁ hB₁ => ?_⟩
      obtain ⟨M₂, g1, g2⟩ := h2 B₁ hB₁
      exact ⟨M₂, by simpa using g1, fun B' h => List.mem_append_right _ (g2 B' h)⟩
    · cases h

theorem splitF_sub_kct {c : Int} {f : T} {ps : List T} {B : Bind} {r : List T} :
    ∀ (l pre : List T) {M : Ms}, splitF S c f ps pre (l ++ r) B = some M →
    ∃ M₁, matchF S f (.co .list c (pre ++ l)) B = some M₁ ∧
      ∀ B₁ ∈ M₁, ∃ M₂, matchColF S .list c ps r B₁ = some M₂ ∧ ∀ B' ∈ M₂, B' ∈ M
  | [], pre, M, h => by
    rw [List.nil_append, splitF_eq] at h
    split at h
    · rename_i x y hx hy
      cases h
      cases hm : matchF S f (.co .list c pre) B with
      | none => rw [hm] at hx; cases hx
      | some ms =>
        rw [hm] at hx
        refine ⟨ms, by simpa using hm, fun B₁ hB₁ => ?_⟩
        obtain ⟨M₂, h1, h2⟩ := restF_sub_kct S hx B₁ hB₁
        exact ⟨M₂, h1, fun B' h => List.mem_append_left _ (h2 B' h)⟩
    · cases h
  | e :: l, pre, M, h => by
    rw [List.cons_append, splitF_eq, splitOnF_cons] at h
    split at h
    · rename_i x y hx hy
      cases h
      obtain ⟨M₁, h1, h2⟩ := splitF_sub_kct l (pre ++ [e]) hy
      refine ⟨M₁, by simpa using h1, fun B₁ hB₁ => ?_⟩
      obtain ⟨M₂, g1, g2⟩ := h2 B₁ hB₁
      exact ⟨M₂, g1, fun B' h => List.mem_append_right _ (g2 B' h)⟩
    · cases h

theorem mem_bindAfterF_kct {x : Int} {t : T} {B₁ B' : Bind} : ∀ {ms : Ms}, B₁ ∈ ms →
    B' ∈ bindVarF x t B₁ (lookF x B₁) → B' ∈ bindAfterF x t ms
  | [], h, _ => nomatch h
  | B :: ms, h, hB => by
    simp only [bindAfterF, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl hB
    · exact .inr (mem_bindAfterF_kct h hB)

/-- Where `B`'s entries are `Bρ`'s and `Bρ` gives `x` the term `t`, `bindVar` gives a substitution
whose entries are `Bρ`'s. -/
theorem bindVarF_sub_kct {x : Int} {t : T} {B Bρ : Bind} (hx : lookF x Bρ = some t)
    (hB : BindExt B Bρ) : ∃ B' ∈ bindVarF x t B (lookF x B), BindExt B' Bρ := by
  cases hl : lookF x B with
  | none =>
    refine ⟨(x, t) :: B, by simp [bindVarF], fun y u hy => ?_⟩
    rw [lookF_cons_kmf] at hy
    split at hy
    · rename_i hyx; subst hyx; cases hy; exact hx
    · exact hB y u hy
  | some u =>
    have : u = t := Option.some.inj ((hB x u hl).symm.trans hx)
    subst this
    exact ⟨B, by simp [bindVarF], hB⟩

/-- `matchTs` at two pairs finds what the two `match`es find. -/
theorem matchTsF_pair_kct {p q a v : T} {Bρ : Bind}
    (h1 : ∀ {B : Bind} {M : Ms}, BindExt B Bρ → matchF S p a B = some M → ∃ B' ∈ M, BindExt B' Bρ)
    (h2 : ∀ {B : Bind} {M : Ms}, BindExt B Bρ → matchF S q v B = some M → ∃ B' ∈ M, BindExt B' Bρ)
    {B : Bind} {M : Ms} (hB : BindExt B Bρ) (h : matchTsF S [p, q] [a, v] B = some M) :
    ∃ B' ∈ M, BindExt B' Bρ := by
  rw [matchTsF_cons] at h
  cases hm : matchF S p a B with
  | none => rw [hm] at h; cases h
  | some ms =>
    rw [hm] at h
    obtain ⟨B₁, hB₁, hx₁⟩ := h1 hB hm
    obtain ⟨M₁, g1, g2⟩ := matchKF_sub_kct S h B₁ hB₁
    rw [matchTsF_cons] at g1
    cases hm' : matchF S q v B₁ with
    | none => rw [hm'] at g1; cases g1
    | some ms' =>
      rw [hm'] at g1
      obtain ⟨B₂, hB₂, hx₂⟩ := h2 hx₁ hm'
      obtain ⟨M₂, k1, k2⟩ := matchKF_sub_kct S g1 B₂ hB₂
      rw [matchTsF_nil] at k1
      cases k1
      exact ⟨B₂, g2 B₂ (k2 B₂ (by simp)), hx₂⟩

mutual
theorem matchF_of_den_kct {Bρ : Bind} : ∀ {p a : T}, DenF S Bρ p a → ∀ {B : Bind} {M : Ms},
    BindExt B Bρ → matchF S p a B = some M → ∃ B' ∈ M, BindExt B' Bρ
  | _, _, .vr hx, B, M, hB, h => by
    rw [matchF_vr] at h; cases h
    exact bindVarF_sub_kct hx hB
  | _, _, .iv i, B, M, hB, h => by
    rw [matchF_iv] at h; cases h; exact ⟨B, by simp, hB⟩
  | _, _, .bv b, B, M, hB, h => by
    rw [matchF_bv] at h; cases h; exact ⟨B, by simp, hB⟩
  | _, _, .tk s x, B, M, hB, h => by
    rw [matchF_tk] at h; cases h; exact ⟨B, by simp, hB⟩
  | _, _, .ap hs, B, M, hB, h => by
    rw [matchF_ap_ap] at h
    simp only [↓reduceIte] at h
    exact matchTsF_of_den_kct hs hB h
  | _, _, .ijSame hd, B, M, hB, h => by
    rw [matchF_ij_ij] at h
    simp only [↓reduceIte] at h
    exact matchF_of_den_kct hd hB h
  | _, _, .ijSub hne hle hd, B, M, hB, h => by
    rw [matchF_ij_ij] at h
    simp only [hne, hle, ↓reduceIte] at h
    exact matchF_of_den_kct hd hB h
  | _, _, .as (x := x) (t := t) hd hx, B, M, hB, h => by
    rw [matchF_as] at h
    obtain ⟨M₁, hm₁, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨B₁, hB₁, hx₁⟩ := matchF_of_den_kct hd hB hm₁
    obtain ⟨B', h1, h2⟩ := bindVarF_sub_kct hx hx₁
    exact ⟨B', mem_bindAfterF_kct hB₁ h1, h2⟩
  | _, _, .kv hp hq, B, M, hB, h => by
    rw [matchF_kv_kv] at h
    exact matchTsF_pair_kct S (fun hB h => matchF_of_den_kct hp hB h)
      (fun hB h => matchF_of_den_kct hq hB h) hB h
  | _, _, .el hd, B, M, hB, h => by
    rw [matchF_el_el] at h
    exact matchF_of_den_kct hd hB h
  | _, _, .cb hd, B, M, hB, h => by
    rw [matchF_cb_co] at h
    exact matchColF_of_den_kct hd hB h
  termination_by structural _ _ hd => hd
theorem matchTsF_of_den_kct {Bρ : Bind} : ∀ {ps ts : List T}, DensF S Bρ ps ts →
    ∀ {B : Bind} {M : Ms}, BindExt B Bρ → matchTsF S ps ts B = some M → ∃ B' ∈ M, BindExt B' Bρ
  | _, _, .nil, B, M, hB, h => by
    rw [matchTsF_nil] at h; cases h; exact ⟨B, by simp, hB⟩
  | _, _, .cons (p := p) (t := t) hd hs, B, M, hB, h => by
    rw [matchTsF_cons] at h
    cases hm : matchF S p t B with
    | none => rw [hm] at h; cases h
    | some ms =>
      rw [hm] at h
      obtain ⟨B₁, hB₁, hx₁⟩ := matchF_of_den_kct hd hB hm
      obtain ⟨M₁, h1, h2⟩ := matchKF_sub_kct S h B₁ hB₁
      obtain ⟨B', g1, g2⟩ := matchTsF_of_den_kct hs hx₁ h1
      exact ⟨B', h2 B' g1, g2⟩
  termination_by structural _ _ hd => hd
theorem matchColF_of_den_kct {Bρ : Bind} : ∀ {k : Kind} {c : Int} {ps es : List T},
    DenColF S Bρ k c ps es → ∀ {B : Bind} {M : Ms}, BindExt B Bρ →
    matchColF S k c ps es B = some M → ∃ B' ∈ M, BindExt B' Bρ
  | _, _, _, _, .done, B, M, hB, h => by
    rw [matchColF_nil] at h; cases h; exact ⟨B, by simp, hB⟩
  | _, _, _, _, .choose (p := p) (e := e) (l := l) (r := r) hp hk hd hs, B, M, hB, h => by
    rw [matchColF_choose S hp hk] at h
    obtain ⟨M₁, h1, h2⟩ := chooseF_sub_kct S l [] h
    obtain ⟨B₁, hB₁, hx₁⟩ := matchF_of_den_kct hd hB h1
    obtain ⟨M₂, g1, g2⟩ := h2 B₁ hB₁
    rw [List.nil_append] at g1
    obtain ⟨B', k1, k2⟩ := matchColF_of_den_kct hs hx₁ g1
    exact ⟨B', g2 B' k1, k2⟩
  | _, _, _, _, .head (p := p) (e := e) hp hd hs, B, M, hB, h => by
    rw [matchColF_head S hp] at h
    cases hm : matchF S p e B with
    | none => rw [hm] at h; cases h
    | some ms =>
      rw [hm] at h
      obtain ⟨B₁, hB₁, hx₁⟩ := matchF_of_den_kct hd hB hm
      obtain ⟨M₂, g1, g2⟩ := restF_sub_kct S h B₁ hB₁
      obtain ⟨B', k1, k2⟩ := matchColF_of_den_kct hs hx₁ g1
      exact ⟨B', g2 B' k1, k2⟩
  | _, _, _, _, .frame hf hd, B, M, hB, h => by
    rw [matchColF_frame S hf] at h
    exact matchF_of_den_kct hd hB h
  | _, _, _, _, .split (l := l) hf hd hs, B, M, hB, h => by
    rw [matchColF_split S hf] at h
    obtain ⟨M₁, h1, h2⟩ := splitF_sub_kct S l [] h
    rw [List.nil_append] at h1
    obtain ⟨B₁, hB₁, hx₁⟩ := matchF_of_den_kct hd hB h1
    obtain ⟨M₂, g1, g2⟩ := h2 B₁ hB₁
    obtain ⟨B', k1, k2⟩ := matchColF_of_den_kct hs hx₁ g1
    exact ⟨B', g2 B' k1, k2⟩
  termination_by structural _ _ _ _ hd => hd
end

/-- **`match` finds what a denotation gives.** Where under `Bρ` the pattern form is the term and
`B`'s entries are `Bρ`'s, every value `match` gives from `B` holds a substitution that extends
`B`, whose entries are `Bρ`'s, which states the match and binds every variable of the pattern. -/
theorem matchF_of_den {p a : T} {Bρ B : Bind} {M : Ms} (hd : DenF S Bρ p a) (hB : BindExt B Bρ)
    (h : matchF S p a B = some M) :
    ∃ B' ∈ M, BindExt B B' ∧ BindExt B' Bρ ∧ DenF S B' p a ∧
      ∀ x ∈ tvarsF p, (lookF x B').isSome = true := by
  obtain ⟨B', h1, h2⟩ := matchF_of_den_kct S hd hB h
  obtain ⟨g1, g2, -⟩ := matchF_den S p a h h1
  exact ⟨B', h1, g1, h2, g2, DenF.bound g2⟩

end

/-! ## A substitution of values as a substitution of `kore.k` -/

/-- `σ` with each value encoded. -/
def bindOfSubst (σ : Subst) : Bind := σ.map fun e => ((e.1 : Int), enc e.2)

theorem lookF_bindOfSubst {x : Int} {t : T} : ∀ {σ : Subst}, lookF x (bindOfSubst σ) = some t →
    ∃ (i : Nat) (w : GroundTerm), x = (i : Int) ∧ σ.lookup i = some w ∧ t = enc w
  | [], h => by simp [bindOfSubst, lookF] at h
  | (j, w) :: σ, h => by
    simp only [bindOfSubst, List.map_cons] at h
    rw [lookF_cons_kmf] at h
    split at h
    · rename_i hxj
      cases h
      exact ⟨j, w, hxj, by simp [List.lookup], rfl⟩
    · rename_i hxj
      obtain ⟨i, w', rfl, h1, h2⟩ := lookF_bindOfSubst (σ := σ) h
      have hij : (i == j) = false := by
        rw [beq_eq_false_iff_ne]; intro hij; exact hxj (by rw [hij])
      exact ⟨i, w', rfl, by simp [List.lookup, hij, h1], h2⟩

theorem lookF_bindOfSubst_of {i : Nat} {w : GroundTerm} : ∀ {σ : Subst}, σ.lookup i = some w →
    lookF (i : Int) (bindOfSubst σ) = some (enc w)
  | [], h => by simp [List.lookup] at h
  | (j, u) :: σ, h => by
    simp only [bindOfSubst, List.map_cons]
    rw [lookF_cons_kmf]
    by_cases hij : i = j
    · subst hij
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h; simp
    · have hij' : (i == j) = false := beq_eq_false_iff_ne.mpr hij
      have hne : ¬ ((i : Int) = (j : Int)) := fun h => hij (Int.natCast_inj.mp h)
      simp only [List.lookup, hij'] at h
      simp only [hne, ↓reduceIte]
      exact lookF_bindOfSubst_of h

/-- `B` agrees with `σ` exactly where its entries are those of `σ` encoded. -/
theorem bindAgree_iff_ext {B : Bind} {σ : Subst} : BindAgree B σ ↔ BindExt B (bindOfSubst σ) := by
  constructor
  · intro h x t hx
    obtain ⟨i, w, rfl, h1, rfl⟩ := h x t hx
    exact lookF_bindOfSubst_of h1
  · intro h x t hx
    exact lookF_bindOfSubst (h x t hx)

/-! ## The variables of a pattern are those of its encoding -/

theorem mem_tvarsLF_kct {x : Int} : ∀ {qs : List T}, x ∈ tvarsLF qs ↔ ∃ q ∈ qs, x ∈ tvarsF q
  | [] => by simp [tvarsLF]
  | q :: qs => by
    rw [tvarsLF, List.mem_append, mem_tvarsLF_kct]
    simp

section
variable {c : Semantics}

/-- `readApp`'s form holds the variables its arguments' forms and parts hold. -/
theorem readApp_vars_kct {f : Sym} {args parts : Option (List T)} {q : T} {V : List Int}
    (hargs : ∀ qs, args = some qs → ∀ i ∈ V, i ∈ tvarsLF qs)
    (hparts : ∀ ps, parts = some ps → ∀ i ∈ V, i ∈ tvarsLF ps)
    (h : readApp c f args parts = some q) : ∀ i ∈ V, i ∈ tvarsF q := by
  unfold readApp at h
  split at h
  · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    intro i hi; rw [tvarsF]; exact hargs qs hqs i hi
  · split at h
    · obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.mp h
      intro i hi
      rw [tvarsF, mem_tvarsLF_kct]
      obtain ⟨x, hx, hix⟩ := mem_tvarsLF_kct.mp (hparts ps hps i hi)
      refine ⟨x, ?_, hix⟩
      unfold orderParts
      split
      · exact hx
      · cases hx' : isElemT x
        · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hx, by simp [hx']⟩)
        · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hx, hx'⟩)
    · split at h
      · split at h
        · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
          intro i hi; rw [tvarsF]; exact hargs qs hqs i hi
        · obtain ⟨qs, hqs, h'⟩ := Option.bind_eq_some_iff.mp h
          unfold derivedHook at h'
          split at h'
          · cases h'
            intro i hi
            simp only [tvarsF, tvarsLF, List.append_nil]
            exact hargs qs hqs i hi
          · cases h'
      · split at h
        · cases h
        · split at h
          · obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
            intro i hi; rw [tvarsF]; exact hargs qs hqs i hi
          · cases h

/-- What the induction gives of a term: its form and its parts as a concatenation's argument hold
its variables. -/
def VarsIn_kct (c : Semantics) (t : Term) : Prop :=
  (∀ q, encTerm c t = some q → ∀ i ∈ varOccs t, (i : Int) ∈ tvarsF q) ∧
    ∀ k s qs, encPartWith c encLit k s t = some qs → ∀ i ∈ varOccs t, (i : Int) ∈ tvarsLF qs

theorem encTermsWith_vars_kct : ∀ {ts : List Term}, (∀ t ∈ ts, VarsIn_kct c t) → ∀ {qs : List T},
    encTermsWith c encLit ts = some qs → ∀ i ∈ varOccsList ts, (i : Int) ∈ tvarsLF qs
  | [], _, qs, _, i, hi => by simp [varOccsList] at hi
  | t :: ts, ih, qs, h, i, hi => by
    obtain ⟨q, qs', h1, h2, rfl⟩ := encTerms_cons_kmf c h
    rw [tvarsLF, List.mem_append]
    rw [varOccsList, List.mem_append] at hi
    rcases hi with hi | hi
    · exact .inl ((ih t (by simp)).1 q h1 i hi)
    · exact .inr (encTermsWith_vars_kct (fun x hx => ih x (by simp [hx])) h2 i hi)

theorem encCollWith_vars_kct {ts : List Term} (ih : ∀ t ∈ ts, VarsIn_kct c t) (k : Kind) (s : Srt)
    (r : CRole) {ps : List T} (h : encCollWith c encLit k s r ts = some ps) :
    ∀ i ∈ varOccsList ts, (i : Int) ∈ tvarsLF ps := by
  rcases ts with _ | ⟨x, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
  · intro i hi; simp [varOccsList] at hi
  · simp only [encCollWith] at h
    split at h
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      intro i hi
      simp only [varOccsList, List.append_nil] at hi
      simp only [tvarsLF, tvarsF, List.append_nil]
      exact (ih x (by simp)).1 p hp i hi
    · cases h
  · have ha := ih x (by simp)
    have hv := ih v (by simp)
    simp only [encCollWith] at h
    split at h
    · split at h
      · rename_i p q' hp hq
        cases h
        intro i hi
        simp only [varOccsList, List.append_nil, List.mem_append] at hi
        simp only [tvarsLF, tvarsF, List.append_nil, List.mem_append]
        rcases hi with hi | hi
        · exact .inl (ha.1 p hp i hi)
        · exact .inr (hv.1 q' hq i hi)
      · cases h
    · split at h
      · split at h
        · rename_i p q' hp hq
          cases h
          intro i hi
          simp only [varOccsList, List.append_nil, List.mem_append] at hi
          rw [mem_tvarsLF_kct]
          rcases hi with hi | hi
          · obtain ⟨y, hy, hiy⟩ := mem_tvarsLF_kct.mp (ha.2 k s p hp i hi)
            exact ⟨y, List.mem_append_left _ hy, hiy⟩
          · obtain ⟨y, hy, hiy⟩ := mem_tvarsLF_kct.mp (hv.2 k s q' hq i hi)
            exact ⟨y, List.mem_append_right _ hy, hiy⟩
        · cases h
      · cases h
  · simp only [encCollWith] at h; cases h

/-- The encoding of a term holds its variables. -/
theorem varsIn_kct (t : Term) : VarsIn_kct c t := by
  induction t using termInd_kel with
  | hvar i =>
    refine ⟨fun q hq => ?_, fun k s qs hq => ?_⟩
    · rw [encTerm_var_kmf] at hq; cases hq; intro j hj
      simp only [varOccs, List.mem_singleton] at hj; subst hj; simp [tvarsF]
    · simp only [encPartWith, Option.some.injEq] at hq
      subst hq; intro j hj
      simp only [varOccs, List.mem_singleton] at hj; subst hj; simp [tvarsF, tvarsLF]
  | hdv s l => exact ⟨fun _ _ j hj => by simp [varOccs] at hj, fun _ _ _ _ j hj => by simp [varOccs] at hj⟩
  | hinj a b t ih =>
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_inj_kmf] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro j hj; rw [tvarsF]; exact ih.1 p hp j (by simpa [varOccs] using hj)
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro j hj
      simp only [tvarsLF, tvarsF, List.append_nil]
      exact ih.1 p hp j (by simpa [varOccs] using hj)
  | has t i ih =>
    refine ⟨fun q hq => ?_, fun k s' qs hq => ?_⟩
    · rw [encTerm_as_kmf] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro j hj
      simp only [varOccs, List.mem_append, List.mem_singleton] at hj
      simp only [tvarsF, List.mem_append, List.mem_singleton]
      rcases hj with hj | rfl
      · exact .inl (ih.1 p hp j hj)
      · exact .inr rfl
    · simp only [encPartWith] at hq
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
      intro j hj
      simp only [varOccs, List.mem_append, List.mem_singleton] at hj
      simp only [tvarsLF, tvarsF, List.append_nil, List.mem_append, List.mem_singleton]
      rcases hj with hj | rfl
      · exact .inl (ih.1 p hp j hj)
      · exact .inr rfl
  | happ f ts ih =>
    have hargs : ∀ qs, encTermsWith c encLit ts = some qs →
        ∀ i ∈ (varOccsList ts).map (fun j : Nat => (j : Int)), i ∈ tvarsLF qs := by
      intro qs h i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact encTermsWith_vars_kct ih h j hj
    have hcoll : ∀ k' s' r ps, encCollWith c encLit k' s' r ts = some ps →
        ∀ i ∈ (varOccsList ts).map (fun j : Nat => (j : Int)), i ∈ tvarsLF ps := by
      intro k' s' r ps h i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact encCollWith_vars_kct ih k' s' r h j hj
    have hparts : ∀ ps, ((collSymOf c f).bind fun (k', s', r) => encCollWith c encLit k' s' r ts) =
        some ps → ∀ i ∈ (varOccsList ts).map (fun j : Nat => (j : Int)), i ∈ tvarsLF ps := by
      intro ps h
      obtain ⟨⟨k', s', r⟩, -, h'⟩ := Option.bind_eq_some_iff.mp h
      exact hcoll k' s' r ps h'
    refine ⟨fun q hq j hj => ?_, fun k₀ s₀ qs hq j hj => ?_⟩
    · rw [encTerm_app_kmf] at hq
      exact readApp_vars_kct hargs hparts hq _ (List.mem_map_of_mem (by simpa [varOccs] using hj))
    · have hj' : (j : Int) ∈ (varOccsList ts).map (fun j : Nat => (j : Int)) :=
        List.mem_map_of_mem (by simpa [varOccs] using hj)
      simp only [encPartWith] at hq
      split at hq
      · split at hq
        · exact hcoll _ _ _ _ hq _ hj'
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
          simp only [tvarsLF, List.append_nil]
          exact readApp_vars_kct hargs (fun ps h => hcoll _ _ _ ps h) hp _ hj'
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
        simp only [tvarsLF, List.append_nil]
        exact readApp_vars_kct hargs hparts hp _ hj'

end

/-- **Completeness from a denotation, at encodings.** Where under `σ` encoded the encoding of a
sorted pattern is the encoding of a sorted value, and `B` agrees with `σ`: `match` has a value,
and it holds a substitution that extends `B`, agrees with `σ` and binds every variable of the
pattern. -/
theorem matchF_complete_of_den {c : Semantics} (hov : c.ovls = []) {vars : List Srt} {p : Term}
    {q : T} {s s' : Srt} {v : GroundTerm} {σ : Subst} {B : Bind} (hq : encTerm c p = some q)
    (hp : sortOfTerm c.patCtxNF vars p = some s) (hv : c.sortOf v = some s')
    (hd : DenF (subsF c) (bindOfSubst σ) q (enc v)) (hB : BindAgree B σ) :
    ∃ M, matchF (subsF c) q (enc v) B = some M ∧ ∃ B' ∈ M, BindAgree B' σ ∧ BindExt B B' ∧
      ∀ i ∈ varOccs p, (lookF (i : Int) B').isSome = true := by
  obtain ⟨M, hM⟩ := Option.isSome_iff_exists.mp (matchF_total hov hq hp hv (subsF c) B)
  obtain ⟨B', h1, h2, h3, -, h5⟩ := matchF_of_den _ hd (bindAgree_iff_ext.mp hB) hM
  exact ⟨M, hM, B', h1, bindAgree_iff_ext.mpr h3, h2, fun i hi => h5 _ ((varsIn_kct p).1 q hq i hi)⟩

end KCore.KK
