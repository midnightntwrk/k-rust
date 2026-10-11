//! Definitions whose runs are checked both through `krust krun` (`cli.rs`: printed KORE, exit
//! status, diagnostics) and in-process (`execution_semantics.rs`: the backend's result on the
//! KORE krust compiles from them).
//!
//! Test binaries include this file with
//! `#[path = "support/execution_sources.rs"] mod execution_sources;`.

/// The BN128 section of `plugin/krypto.md` at blockchain-k-plugin `651a2db5`, the plugin the pinned
/// KEVM uses, verbatim in a module of the same name: its point productions carry no `symbol`
/// attribute, so their Kore labels are generated from the production.
pub const PINNED_PLUGIN_BN128: &str = r#"
module KRYPTO
    imports BOOL-SYNTAX
    imports INT-SYNTAX
    imports LIST

    syntax G1Point ::= "(" Int "," Int ")" [prefer]
    syntax G2Point ::= "(" Int "x" Int "," Int "x" Int ")"
    syntax G1Point ::= BN128Add(G1Point, G1Point) [function, hook(KRYPTO.bn128add)]
                     | BN128Mul(G1Point, Int)     [function, hook(KRYPTO.bn128mul)]

    syntax Bool ::= BN128AtePairing(List, List) [function, hook(KRYPTO.bn128ate)]

    syntax Bool ::= isValidPoint(G1Point) [function, hook(KRYPTO.bn128valid)]
                  | isValidPoint(G2Point) [function, symbol(isValidG2Point), hook(KRYPTO.bn128g2valid)]
endmodule

module MAIN
  imports INT
  imports BOOL
  imports LIST
  imports KRYPTO

  syntax G1Point ::= alt(Int, Int, Int)
  syntax Check ::= "valid" | "off-curve" | "other-constructor" | "g2-valid" | "add" | "mul"
                 | "pairing"
  syntax KItem ::= result(K)

  rule <k> valid => result(isValidPoint((1, 2))) </k>
  rule <k> off-curve => result(isValidPoint((1, 3))) </k>
  rule <k> other-constructor => result(isValidPoint(alt(1, 2, 0))) </k>
  rule <k> g2-valid => result(isValidPoint((
      10857046999023057135944570762232829481370756359578518086990519993285655852781
        x 11559732032986387107991004021392285783925812861821192530917403151452391805634,
      8495653923123431417604973247489272438418190587263600148770280649306958101930
        x 4082367875863433681332203403145435568316851327593401208105741076214120093531)))
  </k>
  rule <k> add => result(BN128Add((1, 2), (1, 2))) </k>
  rule <k> mul => result(BN128Mul((1, 2), 2)) </k>
  rule <k> pairing => result(BN128AtePairing(
    ListItem((1, 2))
      ListItem((1, 21888242871839275222246405745257275088696311157297823662689037894645226208581)),
    ListItem((
      10857046999023057135944570762232829481370756359578518086990519993285655852781
        x 11559732032986387107991004021392285783925812861821192530917403151452391805634,
      8495653923123431417604973247489272438418190587263600148770280649306958101930
        x 4082367875863433681332203403145435568316851327593401208105741076214120093531))
      ListItem((
        10857046999023057135944570762232829481370756359578518086990519993285655852781
          x 11559732032986387107991004021392285783925812861821192530917403151452391805634,
        8495653923123431417604973247489272438418190587263600148770280649306958101930
          x 4082367875863433681332203403145435568316851327593401208105741076214120093531))))
  </k>

  configuration <k> $PGM:Check </k>
endmodule
"#;

/// Applications of `total` hooks this backend has no evaluator for (`expFloat`) and of a partial
/// one (`logFloat`), discarded (`unused`, `branch`, `partial`), decided over (`decide`) or kept in
/// the final configuration (`used`). `i` and `fl` hide the constants from the constant folder.
pub const NO_EVALUATOR: &str = r#"
module NOEVAL
  imports INT
  imports BOOL
  imports FLOAT
  imports K-EQUAL
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= "unused" | "branch" | "used" | "decide" | "partial"
  syntax KItem ::= r(K) | f(Float) | "pos" | "nonpos"
  syntax Int ::= i(Int) [function, total]
  rule i(X) => X
  syntax Float ::= fl(Float) [function, total]
  rule fl(X) => X
  rule <k> unused => r(false andBool (Float2Int(expFloat(fl(1.0))) ==Int 2)) </k>
  rule <k> branch => r(#if i(1) ==Int i(1) #then 7 #else Float2Int(expFloat(fl(1.0))) #fi) </k>
  rule <k> used => r(expFloat(fl(1.0))) </k>
  rule <k> decide => f(expFloat(fl(1.0))) </k>
  rule <k> partial => r(false andBool (Float2Int(logFloat(fl(2.0))) ==Int 0)) </k>
  rule <k> f(X) => r(pos) </k> requires X >Float 0.0
  rule <k> f(X) => r(nonpos) </k> requires X <=Float 0.0
endmodule
"#;

/// `<<Int` (no interpreted solver encoding) and `^Int` (an interpreted one) results above the
/// backend's result size bound, from `go` and `power`; `i` hides the shift amount and the exponent
/// from the constant folder.
pub const SEARCH_BOUND: &str = r#"
module SEARCH-BOUND
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= "go" | "power"
  syntax KItem ::= f(Int) | "done"
  syntax Int ::= i(Int) [function, total]
  rule i(X) => X
  rule <k> go => f(1 <<Int i(16777217)) </k>
  rule <k> power => f(2 ^Int i(16777217)) </k>
  rule <k> f(_) => done </k>
endmodule
"#;
