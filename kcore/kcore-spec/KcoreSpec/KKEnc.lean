import KcoreSpec.KKStatements
import KcoreSpec.StringDomain

/-!
# A value of an object definition as a `kore.k` term

`enc` writes a value (`GroundTerm`) as a value of `kore.k`'s sort `Term` (the mirror `KK.T`).
Symbols and sorts keep KCore's numbers. A constructor application is `ap`, an injection `ij`, a
domain value of `Int` `iv`, of `Bool` `bv`, a token or a `String` `tk` with its sort; any other
literal (a Float, or a literal at another sort) has no place in `kore.k` and is written `bot`.
A collection is `co` with its elements `kv` (a map entry) or `el` (a set or list element). `kore.k`
holds a map's entries ordered by key and a set's elements by value, in its own order `cmp`, which
is not `GroundTerm.cmp`'s (it orders the term forms and the literals differently), so `enc`
re-sorts a map's and a set's elements by `ckeyF`; a list keeps its order.

`cmpF`, `cmpTsF`, `cmpIF`, `lexF`, `b2iF`, `tagF` and `ckeyF` are `kore.k`'s functions `cmp`, `cmpTs`,
`cmpI`, `lex`, `b2i`, `tag` and `ckey`, one Lean equation per equation of `kore.k`. `ckey` has
equations for two map entries and for two elements only; `ckeyF` is `none` at every other pair,
where `kore.k`'s `ckey` has no value.
-/

set_option autoImplicit false

namespace KCore.KK

deriving instance Repr for Kind
deriving instance Repr for T

/-! ## kore.k's order on terms -/

/-- `cmpI(X, Y)`: -1, 0 or 1 as `X` is below, equal to or above `Y`. -/
def cmpIF (x y : Int) : Int := if x < y then -1 else if x = y then 0 else 1

/-- `lex(X, Y)`: `Y` where `X` is 0, `X` otherwise. -/
def lexF (x y : Int) : Int := if x = 0 then y else x

/-- `b2i(B)`: 1 for true, 0 for false. -/
def b2iF : Bool → Int
  | true => 1
  | false => 0

/-- `tag(T)`: the rank of a term's form in `cmp`'s order between forms. -/
def tagF : T → Int
  | .iv _ => 0
  | .bv _ => 1
  | .ap _ _ => 2
  | .ij _ _ _ => 3
  | .co _ _ _ => 4
  | .tk _ _ => 5
  | _ => 6

mutual
/-- `cmp(T, U)`: two terms of one form by their parts, else by `tag`. Two collections compare by
their sort numbers and elements whatever their kinds; two tokens by their sorts, then by
`<String` on their texts; two terms of the forms `tag` ranks 6 compare as 0. -/
def cmpF : T → T → Int
  | .iv x, .iv y => cmpIF x y
  | .bv x, .bv y => cmpIF (b2iF x) (b2iF y)
  | .tk s x, .tk t y =>
      lexF (cmpIF s t) (cmpIF (b2iF (KStr.lexLt y.toList x.toList)) (b2iF (KStr.lexLt x.toList y.toList)))
  | .ap f as, .ap g bs => lexF (cmpIF f g) (cmpTsF as bs)
  | .ij a b t, .ij c e u => lexF (cmpIF a c) (lexF (cmpIF b e) (cmpF t u))
  | .co _ c es, .co _ d fs => lexF (cmpIF c d) (cmpTsF es fs)
  | .kv a v, .kv b w => lexF (cmpF a b) (cmpF v w)
  | .el x, .el y => cmpF x y
  | t, u => cmpIF (tagF t) (tagF u)
  termination_by structural t => t
/-- `cmpTs(Ts, Us)`: two lists lexicographically, a proper prefix below. -/
def cmpTsF : List T → List T → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | t :: ts, u :: us => lexF (cmpF t u) (cmpTsF ts us)
  termination_by structural ts => ts
end

/-- `ckey(E, F)`: two map entries by their keys, two elements by their values; no value at any
other pair. -/
def ckeyF : T → T → Option Int
  | .kv a _, .kv b _ => some (cmpF a b)
  | .el x, .el y => some (cmpF x y)
  | _, _ => none

/-- Insert an element into a list ordered by `ckeyF`: before the first element it is below, so
after every element whose key it equals and after a pair `ckeyF` gives no value. -/
def insK (e : T) : List T → List T
  | [] => [e]
  | f :: fs => if (ckeyF e f).any (· < 0) then e :: f :: fs else f :: insK e fs

/-- The elements ordered by `ckeyF`, inserted one by one from the first, as `kore.k` builds a
collection from its parts. -/
def sortK (es : List T) : List T := es.foldl (fun acc e => insK e acc) []

/-! ## The encoding of values -/

mutual
/-- A value as a `kore.k` term. -/
def enc : GroundTerm → T
  | .ctor f vs => .ap f (encTs vs)
  | .inj a b v => .ij a b (enc v)
  | .dv Srt.int (.int i) => .iv i
  | .dv Srt.bool (.bool b) => .bv b
  | .dv s (.tok x) => .tk s x
  | .dv _ _ => .bot
  | .map s es => .co .map s (sortK (encKvs es))
  | .set s es => .co .set s (sortK (encEls es))
  | .list s es => .co .list s (encEls es)
  termination_by structural v => v
/-- Values as `kore.k` terms, in order. -/
def encTs : List GroundTerm → List T
  | [] => []
  | v :: vs => enc v :: encTs vs
  termination_by structural vs => vs
/-- Map entries as `kv` terms, in order. -/
def encKvs : List (GroundTerm × GroundTerm) → List T
  | [] => []
  | e :: es => encKv e :: encKvs es
  termination_by structural es => es
/-- A map entry as a `kv` term. -/
def encKv : GroundTerm × GroundTerm → T
  | (k, v) => .kv (enc k) (enc v)
  termination_by structural e => e
/-- Set or list elements as `el` terms, in order. -/
def encEls : List GroundTerm → List T
  | [] => []
  | v :: vs => .el (enc v) :: encEls vs
  termination_by structural vs => vs
end

/-- A result as a `kore.k` term: an undefined result is `bot`. -/
def encR : Option GroundTerm → T
  | some v => enc v
  | none => .bot

/-! ## Checks the kernel decides -/

/-- `GroundTerm.cmp` puts the Bool sort (2) before the Int sort (3); `kore.k`'s `cmp` puts `iv`
before `bv`, so a map with one key of each is re-sorted. -/
example : enc (.map Srt.map [(.dv Srt.bool (.bool true), .dv Srt.int (.int 1)),
    (.dv Srt.int (.int 7), .dv Srt.int (.int 2))]) =
    .co .map 6 [.kv (.iv 7) (.iv 2), .kv (.bv true) (.iv 1)] := rfl

/-- A list keeps its order. -/
example : enc (.list Srt.list [.dv Srt.bool (.bool true), .dv Srt.int (.int 7)]) =
    .co .list 5 [.el (.bv true), .el (.iv 7)] := rfl

/-- A Float has no place in `kore.k`. -/
example : enc (.dv Srt.float (.float 53 11 0)) = .bot := rfl

/-- Two tokens of one sort by `<String`. -/
example : cmpF (.tk 9 "$n") (.tk 9 "$s") = -1 := by decide

end KCore.KK
