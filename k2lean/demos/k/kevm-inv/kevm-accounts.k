// A kind 1 invariant of KEVM (k2lean/docs/invariants.md), the scale test of `k2l_preserve` on a
// definition about ten times SIMPLE's size: every entry of the `<accounts>` cell map is stored
// under its own `<acctID>`, in the current world state and in every world state saved on
// `<interimStates>` (`#pushWorldState` saves the whole `<accounts>` cell, `#popWorldState` puts it
// back, so the current map alone is not inductive).
// The walk's pattern names the key and the `<acctID>` with one variable: the frontend writes a
// cell map item's key from the item's key cell, so the pattern matches exactly the entries whose
// key is their `<acctID>`. The functions are partial: on a map with any other entry no equation
// gives a value, so the invariant (`= some true`) fails there, as it would with an `owise`
// equation giving `false`.
requires "evm.md"

module KEVM-ACCOUNTS
  imports EVM

  syntax Bool ::= acctsOk(EthereumCell) [function]
                | mapOk(AccountsCell) [function]
                | statesOk(List) [function]
                | stateOk(KItem) [function]
  rule acctsOk(<ethereum> <evm> <interimStates> S </interimStates> ... </evm> <network> AS:AccountsCell ... </network> </ethereum>)
    => mapOk(AS) andBool statesOk(S)
  rule mapOk(<accounts> .Bag </accounts>) => true
  rule mapOk(<accounts> <account> <acctID> A </acctID> ... </account> REST </accounts>)
    => mapOk(<accounts> REST </accounts>)
  rule statesOk(.List) => true
  rule statesOk(ListItem(X) L) => stateOk(X) andBool statesOk(L)
  rule stateOk({ AS:AccountsCell | _ }) => mapOk(AS)
endmodule
