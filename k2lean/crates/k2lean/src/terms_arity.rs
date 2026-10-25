//! `Terms.lean` in the arity-indexed encoding (`gen --arity-terms`, `k2lean/docs/design.md`, §2.1).
//!
//! The term universe is one inductive family `Term : Tag → Type`, indexed by sorts, with one
//! constructor per *arity* (`c0`, `c1`, …), one per builtin carrier used as an argument
//! (`b_SortInt v`), and one per collection sort, whose entries are a nested `List`:
//!
//! ```lean
//! inductive Term : Tag → Type where
//!   | «b_SortInt» (v : SortInt) : Term .«SortInt»
//!   | c2 {s : Tag} (c : C2 s) (a0 : Term (A2_0 s c)) (a1 : Term (A2_1 s c)) : Term s
//!   | «coll_SortMap» (l : List (Term .«SortKItem» × Term .«SortKItem»)) : Term .«SortMap»
//! ```
//!
//! `Ck s` is the enumeration of sort `s`'s constructors of arity k (`Empty` if it has none) and
//! `Ak_i s c` the sort of argument i, so a value of sort `s` is exactly one constructor of `s`
//! applied to arguments of its argument sorts: the same values as the per-sort mutual block,
//! with the same canonical forms (Lean `=` is K's equality). Each K constructor is a reducible
//! `@[match_pattern]` definition with the generator's name, so the rest of the generated code
//! builds and matches terms as before.
//!
//! Why: Lean's auxiliary constructions for a mutual block grow with types × constructors (KEVM's
//! 392 types did not elaborate in 90 min); a family with one constructor per K constructor
//! elaborates but every match at a fixed sort then refutes every other constructor (2.4 s per
//! two-arm match on KEVM) and is not executable (constructor tags above 243). Here the family
//! has ~20 constructors, a match at a fixed sort splits one enumeration of that sort's own
//! constructors, and every inductive stays under the runtime's tag limit (enumerations are
//! scalars). Serialization, its decoder and their round trip are one case per arity.

use crate::model::{Coll, Kind, Model};
use crate::names;
use crate::terms::{LCtor, Print, block_types, fsuffix, inj_pairs};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

fn q(s: &str) -> String {
    format!("«{}»", s.trim_start_matches('«').trim_end_matches('»'))
}

fn tag(t: &str) -> String {
    format!(".{}", q(t))
}

struct Coll1 {
    sort: String,
    kind: Coll,
    /// Lean element types (`Term .«S»` for block sorts, the carrier otherwise) and their sorts.
    elems: Vec<(String, String)>,
}

pub fn emit(m: &Model, ns: &str) -> String {
    let mut o = crate::terms::prefix(
        m,
        ns,
        "Term universe: one inductive family `Term : Tag → Type` indexed by the sorts, with one\n\
constructor per arity of the sorts' own constructors (`Ck s` enumerates sort `s`'s constructors\n\
of arity k), one per builtin carrier, one per collection sort (a nested list), and the leaf\n\
injection `inj`; each K constructor is a reducible `@[match_pattern]` definition.",
    );
    let types = block_types(m);
    let names: BTreeSet<String> = types.iter().map(|(t, _)| t.clone()).collect();
    let lty = |s: &str| {
        if names.contains(s) {
            format!("(Term {})", tag(s))
        } else {
            s.to_string()
        }
    };
    // plain types (own constructors) and collections (nested lists)
    let mut plain: Vec<(&String, &Vec<LCtor>)> = Vec::new();
    let mut colls: Vec<Coll1> = Vec::new();
    // sorts with subsorts: a value is a leaf's own value, injected (`Term.inj`)
    let mut sums: Vec<(&String, &Vec<LCtor>)> = Vec::new();
    for (ty, cs) in &types {
        match &m.sorts.get(ty).map(|s| s.kind.clone()) {
            Some(Kind::Coll(k)) => {
                let info = m.sort(ty);
                colls.push(Coll1 {
                    sort: ty.clone(),
                    kind: k.clone(),
                    elems: info.elems.iter().map(|e| (lty(e), e.clone())).collect(),
                });
            }
            Some(Kind::Plain) if !m.sort(ty).is_simple() => sums.push((ty, cs)),
            _ => plain.push((ty, cs)),
        }
    }
    let mut builtins: BTreeSet<String> = BTreeSet::new();
    for (_, cs) in &plain {
        for c in cs.iter() {
            for a in &c.args {
                if !names.contains(a) {
                    builtins.insert(a.clone());
                }
            }
        }
    }
    for c in &colls {
        for (_, e) in &c.elems {
            if !names.contains(e) {
                builtins.insert(e.clone());
            }
        }
    }
    for (_, cs) in &sums {
        for c in cs.iter() {
            if !names.contains(&c.args[0]) {
                builtins.insert(c.args[0].clone());
            }
        }
    }
    let builtins: Vec<String> = builtins.into_iter().collect();
    let ntags = types.len() + builtins.len();
    writeln!(o, "set_option linter.unusedVariables false\n").unwrap();
    writeln!(o, "/-! The sorts, as the index of the term family. -/\n").unwrap();
    writeln!(o, "inductive Tag where").unwrap();
    for (t, _) in &types {
        writeln!(o, "  | {}", q(t)).unwrap();
    }
    for b in &builtins {
        writeln!(o, "  | {}", q(b)).unwrap();
    }
    writeln!(o, "  deriving DecidableEq\n").unwrap();
    // per (sort, arity) enumerations
    let mut by: BTreeMap<usize, Vec<(&String, Vec<&LCtor>)>> = BTreeMap::new();
    for (ty, cs) in &plain {
        let mut ar: BTreeMap<usize, Vec<&LCtor>> = BTreeMap::new();
        for c in cs.iter() {
            ar.entry(c.args.len()).or_default().push(c);
        }
        for (k, v) in ar {
            by.entry(k).or_default().push((ty, v));
        }
    }
    for (k, ts) in &by {
        for (ty, cs) in ts {
            writeln!(o, "inductive {ty}.C{k} where").unwrap();
            for c in cs {
                writeln!(o, "  | {}", c.name).unwrap();
            }
            writeln!(o, "  deriving DecidableEq\n").unwrap();
        }
    }
    for (k, ts) in &by {
        writeln!(o, "@[reducible] def C{k} : Tag → Type").unwrap();
        for (ty, _) in ts {
            writeln!(o, "  | {} => {ty}.C{k}", tag(ty)).unwrap();
        }
        if ts.len() < ntags {
            writeln!(o, "  | _ => Empty").unwrap();
        }
        for i in 0..*k {
            for (ty, cs) in ts {
                writeln!(o, "@[reducible] def {ty}.A{k}_{i} : {ty}.C{k} → Tag").unwrap();
                for c in cs {
                    writeln!(o, "  | .{} => {}", c.name, tag(&c.args[i])).unwrap();
                }
            }
            writeln!(o, "@[reducible] def A{k}_{i} : (s : Tag) → C{k} s → Tag").unwrap();
            for (ty, _) in ts {
                writeln!(o, "  | {} => {ty}.A{k}_{i}", tag(ty)).unwrap();
            }
            if ts.len() < ntags {
                writeln!(
                    o,
                    "  | _ => fun _ => {}",
                    tag(&builtins
                        .first()
                        .cloned()
                        .unwrap_or_else(|| types[0].0.clone()))
                )
                .unwrap();
            }
        }
        writeln!(o).unwrap();
    }
    let coll_ty = |c: &Coll1| -> String {
        match c.kind {
            Coll::Map => format!("List ({} × {})", c.elems[0].0, c.elems[1].0),
            Coll::Set => format!("List ({} × Unit)", c.elems[0].0),
            Coll::List => format!("List {}", c.elems[0].0),
        }
    };
    // the leaves of each sort with subsorts, by the tag of the leaf's own values
    writeln!(
        o,
        "/-! Leaves: `leafOK s l` holds when `l` is the own type of a leaf sort of `s`. -/\n"
    )
    .unwrap();
    // a leaf set is a table on tags (a bit mask would make inclusion one comparison, but `simp`
    // does not evaluate `Nat.testBit` on literals, which the generated proofs need)
    for (ty, cs) in &sums {
        writeln!(o, "@[reducible] def {ty}.leaf : Tag → Bool").unwrap();
        for c in cs.iter() {
            writeln!(o, "  | {} => true", tag(&c.args[0])).unwrap();
        }
        writeln!(o, "  | _ => false").unwrap();
    }
    writeln!(o, "@[reducible] def leafOK : Tag → Tag → Bool").unwrap();
    for (ty, _) in &sums {
        writeln!(o, "  | {} => {ty}.leaf", tag(ty)).unwrap();
    }
    writeln!(o, "  | _ => fun _ => false\n").unwrap();
    // `hasLeaves s`: `s` has leaf sorts (from the same data as `leafOK`). `Term.inj` takes it as its
    // first explicit field, so a `match` at a sort without leaves refutes `inj` on that field
    // (`false = true`) instead of splitting the leaf tag `l` over every tag
    writeln!(o, "@[reducible] def hasLeaves : Tag → Bool").unwrap();
    for (ty, _) in &sums {
        writeln!(o, "  | {} => true", tag(ty)).unwrap();
    }
    writeln!(o, "  | _ => false\n").unwrap();
    writeln!(o, "inductive Term : Tag → Type where").unwrap();
    for b in &builtins {
        writeln!(
            o,
            "  | {} (v : {b}) : Term {}",
            q(&format!("b_{b}")),
            tag(b)
        )
        .unwrap();
    }
    for k in by.keys() {
        let a: String = (0..*k)
            .map(|i| format!(" (a{i} : Term (A{k}_{i} s c))"))
            .collect();
        writeln!(o, "  | c{k} {{s : Tag}} (c : C{k} s){a} : Term s").unwrap();
    }
    for c in &colls {
        writeln!(
            o,
            "  | {} (l : {}) : Term {}",
            q(&format!("coll_{}", fsuffix(&c.sort))),
            coll_ty(c),
            tag(&c.sort)
        )
        .unwrap();
    }
    writeln!(o, "  | inj {{s : Tag}} (hs : hasLeaves s = true) (l : Tag) (h : leafOK s l = true) (a : Term l) : Term s").unwrap();
    writeln!(o).unwrap();
    for (t, _) in &types {
        writeln!(o, "abbrev {t} := Term {}", tag(t)).unwrap();
    }
    writeln!(o).unwrap();
    // K constructors: reducible match patterns with the generator's names
    for (ty, cs) in &plain {
        for c in cs.iter() {
            let k = c.args.len();
            let ps: String = c
                .args
                .iter()
                .enumerate()
                .map(|(i, a)| format!(" (a{i} : {a})"))
                .collect();
            let vs: String = c
                .args
                .iter()
                .enumerate()
                .map(|(i, a)| {
                    if names.contains(a) {
                        format!(" a{i}")
                    } else {
                        format!(" (Term.{} a{i})", q(&format!("b_{a}")))
                    }
                })
                .collect();
            writeln!(
                o,
                "@[match_pattern, reducible] def {ty}.{}{ps} : {ty} := Term.c{k} (s := {}) {ty}.C{k}.{}{vs}",
                c.name,
                tag(ty),
                c.name
            )
            .unwrap();
        }
    }
    for (ty, cs) in &sums {
        for c in cs.iter() {
            let a = &c.args[0];
            let v = if names.contains(a) {
                "a0".to_string()
            } else {
                format!("(Term.{} a0)", q(&format!("b_{a}")))
            };
            writeln!(o, "@[match_pattern, reducible] def {ty}.{} (a0 : {a}) : {ty} := Term.inj (s := {}) rfl {} rfl {v}", c.name, tag(ty), tag(a)).unwrap();
        }
    }
    // the payload of a builtin carrier
    for b in &builtins {
        writeln!(
            o,
            "def Term.{} : Term {} → {b}\n  | .{} v => v",
            q(&format!("v_{b}")),
            tag(b),
            q(&format!("b_{b}"))
        )
        .unwrap();
        writeln!(o, "theorem Term.{} (a : Term {}) : Term.{} (Term.{} a) = a := by\n  match a with\n  | .{} _ => rfl", q(&format!("bv_{b}")), tag(b), q(&format!("b_{b}")), q(&format!("v_{b}")), q(&format!("b_{b}"))).unwrap();
    }
    writeln!(o).unwrap();
    // constructor indices and their inverse
    for (k, ts) in &by {
        writeln!(o, "@[reducible] def idx{k} : (s : Tag) → C{k} s → Nat").unwrap();
        for (ty, _) in ts {
            writeln!(o, "  | {} => {ty}.C{k}.ctorIdx", tag(ty)).unwrap();
        }
        if ts.len() < ntags {
            writeln!(o, "  | _ => fun _ => 0").unwrap();
        }
        writeln!(o, "def ofIdx{k} : (s : Tag) → Nat → Option (C{k} s)").unwrap();
        for (ty, cs) in ts {
            writeln!(
                o,
                "  | {} => fun n => if n < {} then some ({ty}.C{k}.ofNat n) else none",
                tag(ty),
                cs.len()
            )
            .unwrap();
        }
        if ts.len() < ntags {
            writeln!(o, "  | _ => fun _ => none").unwrap();
        }
        writeln!(o, "theorem ofIdx{k}_idx{k} (s : Tag) (c : C{k} s) : ofIdx{k} s (idx{k} s c) = some c := by\n  cases s <;> cases c <;> rfl\n").unwrap();
    }
    // serialization, by structural recursion (one case per arity), and its decoder
    let ser_of = |e: &(String, String), v: &str| {
        if names.contains(&e.1) {
            format!("ser {v}")
        } else {
            format!("ser_{} {v}", e.1)
        }
    };
    writeln!(
        o,
        "/-! Serialization: injective (`dec_ser`), it induces the order on terms. -/\n"
    )
    .unwrap();
    writeln!(o, "mutual").unwrap();
    writeln!(o, "def ser : {{s : Tag}} → Term s → List Tok").unwrap();
    for b in &builtins {
        writeln!(o, "  | _, .{} v => ser_{b} v", q(&format!("b_{b}"))).unwrap();
    }
    for k in by.keys() {
        let vs: Vec<String> = (0..*k).map(|i| format!("a{i}")).collect();
        let body = if *k == 0 {
            "[]".to_string()
        } else {
            nest(&vs.iter().map(|v| format!("ser {v}")).collect::<Vec<_>>())
        };
        writeln!(
            o,
            "  | _, @Term.c{k} s c {} => .c {k} :: .c (idx{k} s c) :: {body}",
            vs.join(" ")
        )
        .unwrap();
    }
    for (j, c) in colls.iter().enumerate() {
        writeln!(
            o,
            "  | _, .{} l => .c {} :: serL_{} l",
            q(&format!("coll_{}", fsuffix(&c.sort))),
            1000 + j,
            fsuffix(&c.sort)
        )
        .unwrap();
    }
    writeln!(
        o,
        "  | _, Term.inj _ l _ a => .c 999 :: .c l.ctorIdx :: ser a"
    )
    .unwrap();
    for c in &colls {
        let f = fsuffix(&c.sort);
        writeln!(o, "def serL_{f} : {} → List Tok", coll_ty(c)).unwrap();
        writeln!(o, "  | [] => [.c 0]").unwrap();
        match c.kind {
            Coll::Map => writeln!(
                o,
                "  | (k, v) :: t => .c 1 :: {}",
                nest(&[
                    ser_of(&c.elems[0], "k"),
                    ser_of(&c.elems[1], "v"),
                    format!("serL_{f} t")
                ])
            ),
            Coll::Set => writeln!(
                o,
                "  | (k, ()) :: t => .c 1 :: {}",
                nest(&[ser_of(&c.elems[0], "k"), format!("serL_{f} t")])
            ),
            Coll::List => writeln!(
                o,
                "  | k :: t => .c 1 :: {}",
                nest(&[ser_of(&c.elems[0], "k"), format!("serL_{f} t")])
            ),
        }
        .unwrap();
    }
    writeln!(o, "end\n").unwrap();
    let dec_of = |e: &(String, String)| {
        if names.contains(&e.1) {
            format!("dec n {}", tag(&e.1))
        } else {
            format!("dec_{} n", e.1)
        }
    };
    writeln!(o, "/-- An injected value of sort `s` from a decoded leaf value of tag `l`. -/\ndef decInj (s l : Tag) (r : Option (Term l × List Tok)) : Option (Term s × List Tok) :=\n  if hs : hasLeaves s = true then\n    if h : leafOK s l = true then r.map (fun p => (Term.inj hs l h p.1, p.2)) else none\n  else none\n").unwrap();
    writeln!(o, "mutual").unwrap();
    writeln!(
        o,
        "def dec : Nat → (s : Tag) → List Tok → Option (Term s × List Tok)"
    )
    .unwrap();
    writeln!(o, "  | 0, _, _ => none").unwrap();
    for k in by.keys() {
        let mut body = format!("do let c ← ofIdx{k} s i;");
        for i in 0..*k {
            write!(body, " let (a{i}, t) ← dec n (A{k}_{i} s c) t;").unwrap();
        }
        let vs: String = (0..*k).map(|i| format!(" a{i}")).collect();
        write!(body, " pure (Term.c{k} c{vs}, t)").unwrap();
        writeln!(o, "  | n + 1, s, .c {k} :: .c i :: t => {body}").unwrap();
    }
    for (j, c) in colls.iter().enumerate() {
        let f = fsuffix(&c.sort);
        writeln!(
            o,
            "  | n + 1, {}, .c {} :: t => do let (l, t) ← decL_{f} n t; pure (.{} l, t)",
            tag(&c.sort),
            1000 + j,
            q(&format!("coll_{f}"))
        )
        .unwrap();
    }
    writeln!(
        o,
        "  | n + 1, s, .c 999 :: .c i :: t => decInj s (Tag.ofNat i) (dec n (Tag.ofNat i) t)"
    )
    .unwrap();
    for b in &builtins {
        writeln!(
            o,
            "  | n + 1, {}, t => do let (v, t) ← dec_{b} (n + 1) t; pure (.{} v, t)",
            tag(b),
            q(&format!("b_{b}"))
        )
        .unwrap();
    }
    writeln!(o, "  | _, _, _ => none").unwrap();
    for c in &colls {
        let f = fsuffix(&c.sort);
        writeln!(
            o,
            "def decL_{f} : Nat → List Tok → Option ({} × List Tok)",
            coll_ty(c)
        )
        .unwrap();
        writeln!(o, "  | 0, _ => none").unwrap();
        writeln!(o, "  | _ + 1, .c 0 :: t => pure ([], t)").unwrap();
        match c.kind {
            Coll::Map => writeln!(
                o,
                "  | n + 1, .c 1 :: t => do let (k, t) ← {} t; let (v, t) ← {} t; let (r, t) ← decL_{f} n t; pure ((k, v) :: r, t)",
                dec_of(&c.elems[0]),
                dec_of(&c.elems[1])
            ),
            Coll::Set => writeln!(o, "  | n + 1, .c 1 :: t => do let (k, t) ← {} t; let (r, t) ← decL_{f} n t; pure ((k, ()) :: r, t)", dec_of(&c.elems[0])),
            Coll::List => writeln!(o, "  | n + 1, .c 1 :: t => do let (k, t) ← {} t; let (r, t) ← decL_{f} n t; pure (k :: r, t)", dec_of(&c.elems[0])),
        }
        .unwrap();
        writeln!(o, "  | _, _ => none").unwrap();
    }
    writeln!(o, "end\n").unwrap();
    // the round trip, by structural recursion on the term
    let simp_dec = "simp only [ser, dec, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind, Option.bind_some, Option.pure_def, bind, pure]";
    writeln!(o, "mutual").unwrap();
    writeln!(
        o,
        "theorem dec_ser : ∀ {{s : Tag}} (a : Term s) (r : List Tok) (n : Nat), (ser a).length ≤ n → dec n s (ser a ++ r) = some (a, r)"
    )
    .unwrap();
    for b in &builtins {
        writeln!(
            o,
            "  | _, .{} v, r, 0, h => absurd h (by simp [ser, ser_{b}, KPrelude.BytesHook.ser])",
            q(&format!("b_{b}"))
        )
        .unwrap();
        // `dec` reaches the builtin case by evaluation: the serialization does not start with `.c`
        writeln!(
            o,
            "  | _, .{bq} v, r, n + 1, h => by\n    have e := dec_ser_{b} v r (n + 1) h\n    show (dec_{b} (n + 1) (ser_{b} v ++ r) >>= fun (p : {b} × List Tok) => pure (Term.{bq} p.1, p.2)) = _\n    rw [e]; rfl",
            bq = q(&format!("b_{b}"))
        )
        .unwrap();
    }
    for k in by.keys() {
        let vs: Vec<String> = (0..*k).map(|i| format!("a{i}")).collect();
        writeln!(
            o,
            "  | _, @Term.c{k} s c {}, r, 0, h => absurd h (by simp [ser])",
            vs.join(" ")
        )
        .unwrap();
        writeln!(
            o,
            "  | _, @Term.c{k} s c {}, r, n + 1, h => by",
            vs.join(" ")
        )
        .unwrap();
        if *k > 0 {
            // the arguments' serializations follow the two tag tokens; each is bounded through the
            // appends (no `omega` over all the lengths at once)
            let all: Vec<String> = vs.iter().map(|v| format!("ser {v}")).collect();
            writeln!(o, "    have hl : ({}).length ≤ n := by\n      have e : (ser (Term.c{k} c {})).length = ({}).length + 2 := rfl\n      omega", nest(&all), vs.join(" "), nest(&all)).unwrap();
            // the rests: a_i is followed by the serializations of a_{i+1}.. and r
            for i in 0..*k {
                let rest: Vec<String> = vs[i + 1..]
                    .iter()
                    .map(|v| format!("ser {v}"))
                    .chain(std::iter::once("r".to_string()))
                    .collect();
                let mut bound = "hl".to_string();
                for _ in 0..i {
                    bound = format!("(KPrelude.len_right {bound})");
                }
                if i + 1 < *k {
                    bound = format!("(KPrelude.len_left {bound})");
                }
                writeln!(
                    o,
                    "    have h{i} := dec_ser a{i} ({}) n {bound}",
                    nest(&rest)
                )
                .unwrap();
            }
            let hs: String = (0..*k).map(|i| format!(", h{i}")).collect();
            writeln!(
                o,
                "    {}",
                simp_dec.replace("]", &format!(", ofIdx{k}_idx{k}{hs}]"))
            )
            .unwrap();
        } else {
            writeln!(
                o,
                "    {}",
                simp_dec.replace("]", &format!(", ofIdx{k}_idx{k}]"))
            )
            .unwrap();
        }
    }
    writeln!(
        o,
        "  | _, Term.inj hs l hl a, r, 0, h => absurd h (by simp [ser])"
    )
    .unwrap();
    writeln!(
        o,
        "  | _, Term.inj hs l hl a, r, n + 1, h => by\n    have e := dec_ser a r n (by simp only [ser, List.length_cons] at h; omega)\n    simp only [ser, dec, List.cons_append]\n    rw [Tag.ofNat_ctorIdx, e]\n    simp only [decInj, hs, hl, dite_true, Option.map_some]"
    )
    .unwrap();
    for c in &colls {
        let f = fsuffix(&c.sort);
        writeln!(
            o,
            "  | _, .{} l, r, 0, h => absurd h (by simp [ser])",
            q(&format!("coll_{f}"))
        )
        .unwrap();
        writeln!(
            o,
            "  | _, .{} l, r, n + 1, h => by\n    have e := dec_serL_{f} l r n (by simp only [ser, List.length_cons] at h; omega)\n    {}",
            q(&format!("coll_{f}")),
            simp_dec.replace("]", ", e]")
        )
        .unwrap();
    }
    for c in &colls {
        let f = fsuffix(&c.sort);
        writeln!(
            o,
            "theorem dec_serL_{f} : ∀ (l : {}) (r : List Tok) (n : Nat), (serL_{f} l).length ≤ n → decL_{f} n (serL_{f} l ++ r) = some (l, r)",
            coll_ty(c)
        )
        .unwrap();
        writeln!(
            o,
            "  | l, r, 0, h => absurd h (by cases l <;> simp [serL_{f}])"
        )
        .unwrap();
        writeln!(o, "  | [], r, n + 1, h => by simp [serL_{f}, decL_{f}]").unwrap();
        let rt = |e: &(String, String), v: &str, rest: &str| {
            if names.contains(&e.1) {
                format!("dec_ser {v} ({rest}) n (by omega)")
            } else {
                format!("dec_ser_{} {v} ({rest}) n (by omega)", e.1)
            }
        };
        let len = |e: &(String, String), v: &str| {
            if names.contains(&e.1) {
                format!("(ser {v}).length")
            } else {
                format!("(ser_{} {v}).length", e.1)
            }
        };
        type Item<'e> = (&'e (String, String), &'static str);
        let (pat, items): (&str, Vec<Item>) = match c.kind {
            Coll::Map => ("(k, v) :: t", vec![(&c.elems[0], "k"), (&c.elems[1], "v")]),
            Coll::Set => ("(k, ()) :: t", vec![(&c.elems[0], "k")]),
            Coll::List => ("k :: t", vec![(&c.elems[0], "k")]),
        };
        writeln!(o, "  | {pat}, r, n + 1, h => by").unwrap();
        let mut lens: Vec<String> = items.iter().map(|(e, v)| len(e, v)).collect();
        lens.push(format!("(serL_{f} t).length"));
        writeln!(o, "    have hl : {} ≤ n := by simp only [serL_{f}, List.length_cons, List.length_append] at h; omega", lens.join(" + ")).unwrap();
        let mut names_h = Vec::new();
        for (i, (e, v)) in items.iter().enumerate() {
            let rest: Vec<String> = items[i + 1..]
                .iter()
                .map(|(e2, v2)| {
                    if names.contains(&e2.1) {
                        format!("ser {v2}")
                    } else {
                        format!("ser_{} {v2}", e2.1)
                    }
                })
                .chain(std::iter::once(format!("serL_{f} t")))
                .chain(std::iter::once("r".to_string()))
                .collect();
            writeln!(o, "    have h{i} := {}", rt(e, v, &nest(&rest))).unwrap();
            names_h.push(format!("h{i}"));
        }
        writeln!(o, "    have ht := dec_serL_{f} t r n (by omega)").unwrap();
        writeln!(
            o,
            "    simp only [serL_{f}, decL_{f}, List.cons_append, List.append_assoc, Option.bind_eq_bind, Option.bind_some, Option.pure_def, bind, pure, {}, ht]",
            names_h.join(", ")
        )
        .unwrap();
    }
    writeln!(o, "end\n").unwrap();
    writeln!(
        o,
        "theorem ser_inj {{s : Tag}} (a b : Term s) (h : ser a = ser b) : a = b := by\n  have ha := dec_ser a [] (ser a).length (Nat.le_refl _)\n  have hb := dec_ser b [] (ser a).length (by simp [h])\n  rw [h] at ha\n  simp_all\n"
    )
    .unwrap();
    writeln!(
        o,
        "theorem compare_append_ser_Term {{s : Tag}} (a b : Term s) (r r' : List Tok) :\n    compare (ser a ++ r) (ser b ++ r') = (compare (ser a) (ser b)).then (compare r r') :=\n  compare_append_ser (@ser s) (fun n t => dec n s t) (fun a r n h => dec_ser a r n h) a b r r'\n"
    )
    .unwrap();
    let tokens: Vec<&String> = builtins
        .iter()
        .filter(|b| matches!(m.sorts.get(*b).map(|s| &s.kind), Some(Kind::Token)))
        .collect();
    emit_beq(&mut o, &names, &builtins, &tokens, &by, &colls);
    // per-type names used by the rest of the generated code
    for (t, _) in &types {
        let f = fsuffix(t);
        writeln!(o, "@[reducible] def ser_{f} (x : {t}) : List Tok := ser x").unwrap();
        writeln!(
            o,
            "def dec_{f} (n : Nat) (t : List Tok) : Option ({t} × List Tok) := dec n {} t",
            tag(t)
        )
        .unwrap();
        writeln!(
            o,
            "theorem ser_{f}_inj (a b : {t}) (h : ser_{f} a = ser_{f} b) : a = b := ser_inj a b h"
        )
        .unwrap();
        writeln!(
            o,
            "def cmp_{f} (a b : {t}) : Ordering := compare (ser_{f} a) (ser_{f} b)"
        )
        .unwrap();
        writeln!(
            o,
            "theorem cmp_{f}_eq (a b : {t}) : cmp_{f} a b = compare (ser_{f} a) (ser_{f} b) := rfl"
        )
        .unwrap();
        writeln!(
            o,
            "theorem compare_append_ser_{f} (a b : {t}) (r r' : List Tok) :\n    compare (ser_{f} a ++ r) (ser_{f} b ++ r') = (compare (ser_{f} a) (ser_{f} b)).then (compare r r') :=\n  compare_append_ser_Term a b r r'"
        )
        .unwrap();
    }
    writeln!(o).unwrap();
    // the order on map keys and set elements
    let mut key_sorts: Vec<String> = Vec::new();
    for c in &colls {
        if !key_sorts.contains(&c.elems[0].1) {
            key_sorts.push(c.elems[0].1.clone());
        }
    }
    if m.sorts.contains_key("SortKItem") && !key_sorts.iter().any(|k| k == "SortKItem") {
        key_sorts.insert(0, "SortKItem".into());
    }
    for k in &key_sorts {
        if !names.contains(k) {
            continue;
        }
        let f = fsuffix(k);
        writeln!(o, "instance : Ord {k} := ⟨cmp_{f}⟩").unwrap();
        writeln!(
            o,
            "instance : Std.TransOrd {k} := transOrd_of_cmp cmp_{f} ser_{f} cmp_{f}_eq"
        )
        .unwrap();
        writeln!(o, "instance : Std.LawfulEqOrd {k} :=\n  lawfulEqOrd_of_cmp cmp_{f} ser_{f} cmp_{f}_eq ser_{f}_inj\n").unwrap();
    }
    // collections: the nested list is the carrier
    for c in &colls {
        let s = &c.sort;
        let f = fsuffix(s);
        let elem = match c.kind {
            Coll::Map => format!("{} × {}", c.elems[0].1, c.elems[1].1),
            Coll::Set => format!("{} × Unit", c.elems[0].1),
            Coll::List => c.elems[0].1.clone(),
        };
        writeln!(
            o,
            "def {s}.toList : {s} → List ({elem})\n  | .{} l => l",
            q(&format!("coll_{f}"))
        )
        .unwrap();
        writeln!(
            o,
            "@[reducible] def {s}.ofList (l : List ({elem})) : {s} := .{} l",
            q(&format!("coll_{f}"))
        )
        .unwrap();
        writeln!(
            o,
            "theorem {s}.toList_ofList (l : List ({elem})) : {s}.toList ({s}.ofList l) = l := rfl"
        )
        .unwrap();
        writeln!(
            o,
            "theorem {s}.ofList_toList : ∀ m, {s}.ofList ({s}.toList m) = m\n  | .{} _ => rfl",
            q(&format!("coll_{f}"))
        )
        .unwrap();
        writeln!(o, "instance : ListIso {s} ({elem}) := ⟨{s}.toList, {s}.ofList, {s}.toList_ofList, {s}.ofList_toList⟩").unwrap();
        match c.kind {
            Coll::Map => writeln!(
                o,
                "instance : MapRepr {s} {} {} := {{}}\n",
                c.elems[0].1, c.elems[1].1
            )
            .unwrap(),
            Coll::Set => {
                writeln!(o, "instance : MapRepr {s} {} Unit := {{}}\n", c.elems[0].1).unwrap()
            }
            Coll::List => writeln!(o).unwrap(),
        }
    }
    // injections and projections: one test on the leaf tag, no case split over the leaves
    writeln!(
        o,
        "/-! Injections `inj{{A,B}}` re-tag the leaf; projections are their partial inverses. -/\n"
    )
    .unwrap();
    for (a, b) in inj_pairs(m) {
        let ia = m.sort(&a);
        let fa = names::short_sort(&a);
        let fb = names::short_sort(&b);
        if ia.is_simple() {
            let own = m.own_ty(&a);
            let val = if names.contains(&own) {
                format!("(h ▸ x : Term {})", tag(&own))
            } else {
                format!(
                    "(Term.{} (h ▸ x : Term {}))",
                    q(&format!("v_{own}")),
                    tag(&own)
                )
            };
            writeln!(
                o,
                "@[reducible] def inj_{fa}_{fb} (x : {a}) : {b} := {b}.inj_{fa} x"
            )
            .unwrap();
            writeln!(o, "def proj_{fb}_{fa} (y : {b}) : Option {a} :=\n  match y with\n  | Term.inj _ l _ x => if h : l = {} then some {val} else none\n  | _ => none", tag(&own)).unwrap();
            writeln!(o, "@[simp] theorem proj_inj_{fb}_{fa} (x : {a}) : proj_{fb}_{fa} (inj_{fa}_{fb} x) = some x := rfl").unwrap();
            let fin = if names.contains(&own) {
                "rfl".to_string()
            } else {
                format!(
                    "exact congrArg (Term.inj _ _ _) (Term.{} z)",
                    q(&format!("bv_{own}"))
                )
            };
            writeln!(
                o,
                "theorem inj_proj_{fb}_{fa} {{y : {b}}} {{x : {a}}} (h : proj_{fb}_{fa} y = some x) : inj_{fa}_{fb} x = y :=\n  match y, h with\n  | Term.inj _ l hl z, h => by\n    dsimp only [proj_{fb}_{fa}] at h\n    split at h <;> simp at h <;> subst_vars <;> {fin}"
            )
            .unwrap();
        } else {
            writeln!(o, "theorem sub_{fa}_{fb} : ∀ l, leafOK {} l = true → leafOK {} l = true := by\n  intro l; cases l <;> decide", tag(&a), tag(&b)).unwrap();
            writeln!(o, "def inj_{fa}_{fb} (x : {a}) : {b} :=\n  match x with\n  | Term.inj _ l h y => Term.inj rfl l (sub_{fa}_{fb} l h) y").unwrap();
            writeln!(o, "def proj_{fb}_{fa} (y : {b}) : Option {a} :=\n  match y with\n  | Term.inj _ l _ x => if h : leafOK {} l = true then some (Term.inj rfl l h x) else none\n  | _ => none", tag(&a)).unwrap();
            writeln!(
                o,
                "@[simp] theorem proj_inj_{fb}_{fa} (x : {a}) : proj_{fb}_{fa} (inj_{fa}_{fb} x) = some x :=\n  match x with\n  | Term.inj _ l hl y => by simp [inj_{fa}_{fb}, proj_{fb}_{fa}, hl]"
            )
            .unwrap();
            writeln!(
                o,
                "theorem inj_proj_{fb}_{fa} {{y : {b}}} {{x : {a}}} (h : proj_{fb}_{fa} y = some x) : inj_{fa}_{fb} x = y :=\n  match y, h with\n  | Term.inj _ l hl z, h => by\n    dsimp only [proj_{fb}_{fa}] at h\n    split at h <;> simp at h <;> subst_vars <;> rfl"
            )
            .unwrap();
        }
        writeln!(
            o,
            "theorem proj_eq_some_{fb}_{fa} {{y : {b}}} {{x : {a}}} : proj_{fb}_{fa} y = some x ↔ y = inj_{fa}_{fb} x :=\n  ⟨fun h => (inj_proj_{fb}_{fa} h).symm, fun h => by subst h; exact proj_inj_{fb}_{fa} x⟩\n"
        )
        .unwrap();
    }
    // printing: labels per constructor, one case per arity
    writeln!(
        o,
        "/-! Printing (for test reports), in a KORE-like notation with K labels. -/\n"
    )
    .unwrap();
    for (k, ts) in &by {
        for (ty, cs) in ts {
            writeln!(o, "def {ty}.L{k} : {ty}.C{k} → String").unwrap();
            for c in cs {
                let l = match &c.print {
                    Print::Transparent => String::new(),
                    Print::KSeq => "~>".into(),
                    Print::DotK => ".K".into(),
                    Print::Label(l) => l.clone(),
                    _ => String::new(),
                };
                writeln!(o, "  | .{} => {}", c.name, names::string_lit(&l)).unwrap();
            }
        }
        writeln!(o, "def lbl{k} : (s : Tag) → C{k} s → String").unwrap();
        for (ty, _) in ts {
            writeln!(o, "  | {} => {ty}.L{k}", tag(ty)).unwrap();
        }
        if ts.len() < ntags {
            writeln!(o, "  | _ => fun _ => \"\"").unwrap();
        }
    }
    let show_of = |e: &(String, String), v: &str| {
        if names.contains(&e.1) {
            format!("toK {v}")
        } else {
            format!("toK_{} {v}", e.1)
        }
    };
    writeln!(o, "mutual").unwrap();
    writeln!(o, "def toK : {{s : Tag}} → Term s → String").unwrap();
    for b in &builtins {
        writeln!(o, "  | _, .{} v => toK_{b} v", q(&format!("b_{b}"))).unwrap();
    }
    for k in by.keys() {
        let vs: Vec<String> = (0..*k).map(|i| format!("a{i}")).collect();
        let shown: Vec<String> = vs.iter().map(|v| format!("toK {v}")).collect();
        let body = match k {
            0 => "lbl0 s c".to_string(),
            1 => format!(
                "let l := lbl1 s c; if l = \"\" then {} else l ++ \"(\" ++ {} ++ \")\"",
                shown[0], shown[0]
            ),
            2 => format!(
                "let l := lbl2 s c; if l = \"~>\" then {} ++ \" ~> \" ++ {} else l ++ \"(\" ++ {} ++ \")\"",
                shown[0],
                shown[1],
                shown.join(" ++ \", \" ++ ")
            ),
            _ => format!(
                "lbl{k} s c ++ \"(\" ++ {} ++ \")\"",
                shown.join(" ++ \", \" ++ ")
            ),
        };
        writeln!(o, "  | _, @Term.c{k} s c {} => {body}", vs.join(" ")).unwrap();
    }
    for c in &colls {
        writeln!(
            o,
            "  | _, .{} l => toKL_{} l",
            q(&format!("coll_{}", fsuffix(&c.sort))),
            fsuffix(&c.sort)
        )
        .unwrap();
    }
    writeln!(o, "  | _, Term.inj _ _ _ a => toK a").unwrap();
    for c in &colls {
        let f = fsuffix(&c.sort);
        writeln!(o, "def toKL_{f} : {} → String", coll_ty(c)).unwrap();
        let (unit, item) = match c.kind {
            Coll::Map => (
                ".Map",
                format!(
                    "{} ++ \" |-> \" ++ {}",
                    show_of(&c.elems[0], "k"),
                    show_of(&c.elems[1], "v")
                ),
            ),
            Coll::Set => (
                ".Set",
                format!("\"SetItem(\" ++ {} ++ \")\"", show_of(&c.elems[0], "k")),
            ),
            Coll::List => (
                ".List",
                format!("\"ListItem(\" ++ {} ++ \")\"", show_of(&c.elems[0], "k")),
            ),
        };
        let pat = match c.kind {
            Coll::Map => "(k, v) :: t",
            Coll::Set => "(k, ()) :: t",
            Coll::List => "k :: t",
        };
        writeln!(
            o,
            "  | [] => \"{unit}\"\n  | {pat} => {item} ++ \" \" ++ toKL_{f} t"
        )
        .unwrap();
    }
    writeln!(o, "end\n").unwrap();
    for (t, _) in &types {
        writeln!(
            o,
            "@[reducible] def toK_{} (x : {t}) : String := toK x",
            fsuffix(t)
        )
        .unwrap();
    }
    writeln!(o, "\nend {ns}").unwrap();
    o
}

/// `a ++ (b ++ (c ++ …))`
/// `Term.beq`, a Boolean equality on terms by structural recursion, its two laws, and the
/// `DecidableEq (Term s)` instance it gives.
///
/// The instance is what `==K` and `decide (a = b)` evaluate, the kernel included (the witnesses
/// of overlaps are checked by it). Every step of `Term.beq` is a constructor split, a comparison
/// of two enumeration indices or tags (literals), or `LeafEq.beq` on a builtin value, so the
/// kernel never meets a definition by well-founded recursion on the way to `isTrue`/`isFalse`;
/// a `String` or `Bytes` leaf compares as the list of its bytes, without decoding. The
/// conjunctions nest to the right, so a recursive call on the last argument (a list's tail) is
/// the last thing evaluated.
///
/// `Term.beq` is heterogeneous in the index (`Term s → Term t → Bool`, `s` and `t` compared
/// first): its soundness `Term.eq_of_beq` then needs no cast and gives `s = t ∧ HEq a b`.
fn emit_beq(
    o: &mut String,
    names: &BTreeSet<String>,
    builtins: &[String],
    tokens: &[&String],
    by: &BTreeMap<usize, Vec<(&String, Vec<&LCtor>)>>,
    colls: &[Coll1],
) {
    let rconj = |parts: &[String]| -> String {
        let mut acc = parts.last().cloned().unwrap_or_else(|| "true".into());
        for p in parts.iter().rev().skip(1) {
            acc = format!("{p} && ({acc})");
        }
        acc
    };
    let elem_beq = |e: &(String, String), x: &str, y: &str| {
        if names.contains(&e.1) {
            format!("Term.beq {x} {y}")
        } else {
            format!("LeafEq.beq {x} {y}")
        }
    };
    let elem_eq = |e: &(String, String), h: &str, x: &str, y: &str| {
        if names.contains(&e.1) {
            format!("eq_of_heq (Term.eq_of_beq {x} {y} {h}).2")
        } else {
            format!("LeafEq.eq_of_beq {h}")
        }
    };
    let elem_self = |e: &(String, String), x: &str| {
        if names.contains(&e.1) {
            format!("Term.beq_self {x}")
        } else {
            format!("LeafEq.beq_self {x}")
        }
    };
    let coll_ty = |c: &Coll1| -> String {
        match c.kind {
            Coll::Map => format!("List ({} × {})", c.elems[0].0, c.elems[1].0),
            Coll::Set => format!("List ({} × Unit)", c.elems[0].0),
            Coll::List => format!("List {}", c.elems[0].0),
        }
    };
    // (pattern of an entry, of the other entry, the comparisons of their elements)
    let entry = |c: &Coll1| -> (&str, &str, Vec<(usize, &str, &str)>) {
        match c.kind {
            Coll::Map => ("(k, v)", "(k', v')", vec![(0, "k", "k'"), (1, "v", "v'")]),
            Coll::Set => ("(k, ())", "(k', ())", vec![(0, "k", "k'")]),
            Coll::List => ("k", "k'", vec![(0, "k", "k'")]),
        }
    };
    writeln!(
        o,
        "/-! Equality by structural recursion (`Term.beq`): the kernel decides `a = b` on closed terms\n\
without unfolding a definition by well-founded recursion; builtin values compare by `LeafEq`. -/\n"
    )
    .unwrap();
    for t in tokens {
        writeln!(
            o,
            "instance : LeafEq {t} := LeafEq.ofVal {t}.val (fun a b h => by cases a; cases b; cases h; rfl)"
        )
        .unwrap();
    }
    if !tokens.is_empty() {
        writeln!(o).unwrap();
    }
    for k in by.keys() {
        writeln!(o, "theorem idx{k}_inj {{s : Tag}} {{c d : C{k} s}} (h : idx{k} s c = idx{k} s d) : c = d := by\n  have e := ofIdx{k}_idx{k} s c\n  rw [h, ofIdx{k}_idx{k}] at e\n  exact (Option.some.inj e).symm").unwrap();
    }
    writeln!(o).unwrap();
    // the definition
    writeln!(o, "mutual").unwrap();
    writeln!(o, "def Term.beq : {{s t : Tag}} → Term s → Term t → Bool").unwrap();
    for b in builtins {
        let c = q(&format!("b_{b}"));
        writeln!(
            o,
            "  | _, _, .{c} v, b => match b with | .{c} w => LeafEq.beq v w | _ => false"
        )
        .unwrap();
    }
    for k in by.keys() {
        let vs: String = (0..*k).map(|i| format!(" a{i}")).collect();
        let ws: String = (0..*k).map(|i| format!(" b{i}")).collect();
        let mut parts = vec![
            "decide (s = t)".to_string(),
            format!("idx{k} s c == idx{k} t d"),
        ];
        parts.extend((0..*k).map(|i| format!("Term.beq a{i} b{i}")));
        writeln!(
            o,
            "  | _, _, @Term.c{k} s c{vs}, b => match b with\n    | @Term.c{k} t d{ws} => {}\n    | _ => false",
            rconj(&parts)
        )
        .unwrap();
    }
    for c in colls {
        let n = q(&format!("coll_{}", fsuffix(&c.sort)));
        writeln!(
            o,
            "  | _, _, .{n} l, b => match b with | .{n} l' => beqL_{} l l' | _ => false",
            fsuffix(&c.sort)
        )
        .unwrap();
    }
    writeln!(o, "  | _, _, @Term.inj s _ l _ a, b => match b with\n    | @Term.inj t _ l' _ b' => decide (s = t) && (decide (l = l') && (Term.beq a b'))\n    | _ => false\ntermination_by structural _ _ a _ => a").unwrap();
    for c in colls {
        let f = fsuffix(&c.sort);
        let (p, p2, es) = entry(c);
        let mut parts: Vec<String> = es
            .iter()
            .map(|(i, x, y)| elem_beq(&c.elems[*i], x, y))
            .collect();
        parts.push(format!("beqL_{f} t t'"));
        writeln!(
            o,
            "def beqL_{f} : {ty} → {ty} → Bool\n  | [], [] => true\n  | {p} :: t, {p2} :: t' => {}\n  | _, _ => false\ntermination_by structural l _ => l",
            rconj(&parts),
            ty = coll_ty(c)
        )
        .unwrap();
    }
    writeln!(o, "end\n").unwrap();
    // soundness
    let other = "cases b <;> first | exact absurd h Bool.false_ne_true | skip";
    writeln!(o, "mutual").unwrap();
    writeln!(o, "theorem Term.eq_of_beq : ∀ {{s t : Tag}} (a : Term s) (b : Term t), Term.beq a b = true → s = t ∧ HEq a b").unwrap();
    for b in builtins {
        let c = q(&format!("b_{b}"));
        writeln!(
            o,
            "  | _, _, .{c} v, b, h => by\n    {other}\n    rename_i w\n    obtain rfl : v = w := LeafEq.eq_of_beq h\n    exact ⟨rfl, HEq.rfl⟩"
        )
        .unwrap();
    }
    for k in by.keys() {
        let vs: String = (0..*k).map(|i| format!(" a{i}")).collect();
        let ws: String = (0..*k).map(|i| format!(" b{i}")).collect();
        let mut parts = vec![
            "decide (s = t)".to_string(),
            format!("idx{k} s c == idx{k} t d"),
        ];
        parts.extend((0..*k).map(|i| format!("Term.beq a{i} b{i}")));
        let hs: String = (0..*k).map(|i| format!(", h{i}")).collect();
        let recs: String = (0..*k)
            .map(|i| format!("    obtain rfl := eq_of_heq (Term.eq_of_beq a{i} b{i} h{i}).2\n"))
            .collect();
        writeln!(
            o,
            "  | _, _, @Term.c{k} s c{vs}, b, h => by\n    {other}\n    rename_i t d{ws}\n    have h' : ({}) = true := h\n    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'\n    obtain ⟨rfl, hi{hs}⟩ := h'\n    obtain rfl := idx{k}_inj hi\n{recs}    exact ⟨rfl, HEq.rfl⟩",
            rconj(&parts)
        )
        .unwrap();
    }
    for c in colls {
        let n = q(&format!("coll_{}", fsuffix(&c.sort)));
        writeln!(
            o,
            "  | _, _, .{n} l, b, h => by\n    {other}\n    rename_i l'\n    obtain rfl := beqL_{}_sound l l' h\n    exact ⟨rfl, HEq.rfl⟩",
            fsuffix(&c.sort)
        )
        .unwrap();
    }
    writeln!(o, "  | _, _, @Term.inj s hs l hl a, b, h => by\n    {other}\n    rename_i t l' b' _ _\n    have h' : (decide (s = t) && (decide (l = l') && (Term.beq a b'))) = true := h\n    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'\n    obtain ⟨rfl, rfl, h0⟩ := h'\n    obtain rfl := eq_of_heq (Term.eq_of_beq a b' h0).2\n    exact ⟨rfl, HEq.rfl⟩\ntermination_by structural _ _ a _ _ => a").unwrap();
    for c in colls {
        let f = fsuffix(&c.sort);
        let (p, p2, es) = entry(c);
        let mut parts: Vec<String> = es
            .iter()
            .map(|(i, x, y)| elem_beq(&c.elems[*i], x, y))
            .collect();
        parts.push(format!("beqL_{f} t t'"));
        let hs: Vec<String> = es.iter().map(|(_, x, _)| format!("h{x}")).collect();
        let recs: String = es
            .iter()
            .map(|(i, x, y)| {
                format!(
                    "    obtain rfl := {}\n",
                    elem_eq(&c.elems[*i], &format!("h{x}"), x, y)
                )
            })
            .collect();
        writeln!(
            o,
            "theorem beqL_{f}_sound : ∀ l l' : {ty}, beqL_{f} l l' = true → l = l'\n  | [], [], _ => rfl\n  | [], _ :: _, h => absurd h Bool.false_ne_true\n  | _ :: _, [], h => absurd h Bool.false_ne_true\n  | {p} :: t, {p2} :: t', h => by\n    have h' : ({}) = true := h\n    simp only [Bool.and_eq_true] at h'\n    obtain ⟨{}, ht⟩ := h'\n{recs}    obtain rfl := beqL_{f}_sound t t' ht\n    rfl\ntermination_by structural l _ _ => l",
            rconj(&parts),
            hs.join(", "),
            ty = coll_ty(c)
        )
        .unwrap();
    }
    writeln!(o, "end\n").unwrap();
    // reflexivity
    writeln!(o, "mutual").unwrap();
    writeln!(
        o,
        "theorem Term.beq_self : ∀ {{s : Tag}} (a : Term s), Term.beq a a = true"
    )
    .unwrap();
    for b in builtins {
        writeln!(o, "  | _, .{} v => LeafEq.beq_self v", q(&format!("b_{b}"))).unwrap();
    }
    for k in by.keys() {
        let vs: String = (0..*k).map(|i| format!(" a{i}")).collect();
        let mut parts = vec![
            "decide (s = s)".to_string(),
            format!("idx{k} s c == idx{k} s c"),
        ];
        parts.extend((0..*k).map(|i| format!("Term.beq a{i} a{i}")));
        let rws: Vec<String> = (0..*k).map(|i| format!("Term.beq_self a{i}")).collect();
        let rw = if rws.is_empty() {
            String::new()
        } else {
            format!("rw [{}]; ", rws.join(", "))
        };
        writeln!(
            o,
            "  | _, @Term.c{k} s c{vs} => by\n    show ({}) = true\n    {rw}simp",
            rconj(&parts)
        )
        .unwrap();
    }
    for c in colls {
        writeln!(
            o,
            "  | _, .{} l => beqL_{}_self l",
            q(&format!("coll_{}", fsuffix(&c.sort))),
            fsuffix(&c.sort)
        )
        .unwrap();
    }
    writeln!(o, "  | _, @Term.inj s _ l _ a => by\n    show (decide (s = s) && (decide (l = l) && (Term.beq a a))) = true\n    rw [Term.beq_self a]; simp\ntermination_by structural _ a => a").unwrap();
    for c in colls {
        let f = fsuffix(&c.sort);
        let (p, _, es) = entry(c);
        let mut parts: Vec<String> = es
            .iter()
            .map(|(i, x, _)| elem_beq(&c.elems[*i], x, x))
            .collect();
        parts.push(format!("beqL_{f} t t"));
        let mut rws: Vec<String> = es
            .iter()
            .map(|(i, x, _)| elem_self(&c.elems[*i], x))
            .collect();
        rws.push(format!("beqL_{f}_self t"));
        writeln!(
            o,
            "theorem beqL_{f}_self : ∀ l : {}, beqL_{f} l l = true\n  | [] => rfl\n  | {p} :: t => by\n    show ({}) = true\n    rw [{}]; rfl\ntermination_by structural l => l",
            coll_ty(c),
            rconj(&parts),
            rws.join(", ")
        )
        .unwrap();
    }
    writeln!(o, "end\n").unwrap();
    writeln!(
        o,
        "instance (s : Tag) : DecidableEq (Term s) := fun a b =>\n  if h : Term.beq a b = true then isTrue (eq_of_heq (Term.eq_of_beq a b h).2)\n  else isFalse (fun e => h (e ▸ Term.beq_self a))\n"
    )
    .unwrap();
}

fn nest(parts: &[String]) -> String {
    let mut body = parts.last().unwrap().clone();
    for p in parts.iter().rev().skip(1) {
        body = format!("({p} ++ {body})");
    }
    body
}

/// The shape of terms (`KPrelude.Shape`, a termination measure of `KPrelude.Termination`) in this
/// universe: emitted in `Functions.lean` when a termination proof needs it (`termination.rs`).
/// Every constructor and builtin value counts one, and every element of a collection one more
/// than its own shape.
pub fn shape_support(m: &Model) -> String {
    let types = block_types(m);
    let names: BTreeSet<String> = types.iter().map(|(t, _)| t.clone()).collect();
    let lty = |s: &str| {
        if names.contains(s) {
            format!("(Term {})", tag(s))
        } else {
            s.to_string()
        }
    };
    let mut plain: Vec<&Vec<LCtor>> = Vec::new();
    let mut colls: Vec<Coll1> = Vec::new();
    let mut sums: Vec<&Vec<LCtor>> = Vec::new();
    for (ty, cs) in &types {
        match &m.sorts.get(ty).map(|s| s.kind.clone()) {
            Some(Kind::Coll(k)) => colls.push(Coll1 {
                sort: ty.clone(),
                kind: k.clone(),
                elems: m
                    .sort(ty)
                    .elems
                    .iter()
                    .map(|e| (lty(e), e.clone()))
                    .collect(),
            }),
            Some(Kind::Plain) if !m.sort(ty).is_simple() => sums.push(cs),
            _ => plain.push(cs),
        }
    }
    let mut builtins: BTreeSet<String> = BTreeSet::new();
    for cs in &plain {
        for c in cs.iter() {
            for a in &c.args {
                if !names.contains(a) {
                    builtins.insert(a.clone());
                }
            }
        }
    }
    for c in &colls {
        for (_, e) in &c.elems {
            if !names.contains(e) {
                builtins.insert(e.clone());
            }
        }
    }
    for cs in &sums {
        for c in cs.iter() {
            if !names.contains(&c.args[0]) {
                builtins.insert(c.args[0].clone());
            }
        }
    }
    let arities: BTreeSet<usize> = plain
        .iter()
        .flat_map(|cs| cs.iter().map(|c| c.args.len()))
        .collect();
    let mut o = String::from(
        "/-! Shapes (termination measures): every constructor and builtin value counts one. -/\nmutual\ndef Term.shape : {s : Tag} → Term s → Nat\n",
    );
    for b in &builtins {
        writeln!(o, "  | _, .{} _ => 1", q(&format!("b_{b}"))).unwrap();
    }
    for k in &arities {
        let vs: Vec<String> = (0..*k).map(|i| format!(" a{i}")).collect();
        let sum: String = (0..*k).map(|i| format!(" + Term.shape a{i}")).collect();
        writeln!(o, "  | _, .c{k} _{} => 1{sum}", vs.concat()).unwrap();
    }
    let elem_shape = |e: &(String, String), v: &str| -> String {
        if names.contains(&e.1) {
            format!("Term.shape {v}")
        } else {
            "1".to_string()
        }
    };
    for c in &colls {
        let f = fsuffix(&c.sort);
        writeln!(
            o,
            "  | _, .{} l => Term.shapeL_{f} l",
            q(&format!("coll_{f}"))
        )
        .unwrap();
    }
    writeln!(o, "  | _, .inj _ _ _ a => 1 + Term.shape a").unwrap();
    for c in &colls {
        let f = fsuffix(&c.sort);
        let ty = match c.kind {
            Coll::Map => format!("List ({} × {})", c.elems[0].0, c.elems[1].0),
            Coll::Set => format!("List ({} × Unit)", c.elems[0].0),
            Coll::List => format!("List {}", c.elems[0].0),
        };
        writeln!(o, "def Term.shapeL_{f} : {ty} → Nat\n  | [] => 0").unwrap();
        match c.kind {
            Coll::Map => writeln!(
                o,
                "  | (k, v) :: t => {} + {} + 1 + Term.shapeL_{f} t",
                elem_shape(&c.elems[0], "k"),
                elem_shape(&c.elems[1], "v")
            ),
            Coll::Set => writeln!(
                o,
                "  | (k, ()) :: t => {} + 1 + Term.shapeL_{f} t",
                elem_shape(&c.elems[0], "k")
            ),
            Coll::List => writeln!(
                o,
                "  | k :: t => {} + 1 + Term.shapeL_{f} t",
                elem_shape(&c.elems[0], "k")
            ),
        }
        .unwrap();
    }
    writeln!(o, "end\n").unwrap();
    writeln!(
        o,
        "instance {{s : Tag}} : KPrelude.Shape (Term s) := ⟨Term.shape⟩"
    )
    .unwrap();
    writeln!(o, "theorem Term.shape_eq {{s : Tag}} (t : Term s) : KPrelude.Shape.shape t = Term.shape t := rfl").unwrap();
    let elem_builtins: BTreeSet<&String> = colls
        .iter()
        .flat_map(|c| c.elems.iter().map(|(_, e)| e))
        .filter(|e| !names.contains(*e))
        .collect();
    for b in elem_builtins {
        // a builtin element of a collection counts one
        writeln!(o, "instance : KPrelude.Shape {b} := ⟨fun _ => 1⟩").unwrap();
    }
    for c in &colls {
        let f = fsuffix(&c.sort);
        let (elem, pat, extra) = match c.kind {
            Coll::Map => (
                format!("{} × {}", c.elems[0].0, c.elems[1].0),
                "obtain ⟨k, v⟩ := x; ",
                "KPrelude.shape_prod, ",
            ),
            Coll::Set => (
                format!("{} × Unit", c.elems[0].0),
                "obtain ⟨k, ⟨⟩⟩ := x; ",
                "KPrelude.shape_prod, KPrelude.shape_unit, ",
            ),
            Coll::List => (c.elems[0].0.clone(), "", ""),
        };
        writeln!(
            o,
            "instance : KPrelude.ListShape {} ({elem}) := ⟨fun l => by\n  show Term.shapeL_{f} l = _\n  induction l with\n  | nil => rfl\n  | cons x t ih => {pat}simp only [Term.shapeL_{f}, List.map_cons, List.sum_cons, ih, {extra}Term.shape_eq] <;> first | rfl | omega⟩",
            c.sort
        )
        .unwrap();
    }
    o.push('\n');
    o
}
