module TX-DATA
  imports DOMAINS
  imports BYTES
  configuration <k> $PGM:K </k>
                <chainID> 0 </chainID>
                <messages>
                  <message multiplicity="*" type="Map">
                    <msgID> 0 </msgID>
                    <txNonce> 0 </txNonce>
                    <sigV> 0 </sigV>
                    <data> .Bytes </data>
                  </message>
                </messages>
  syntax TxData ::= txData(Int, Bytes, Int) [symbol(txData)]
  syntax TxData ::= "#getTxData" "(" Int ")" [function, symbol(getTxData)]
  rule [tx-data]: [[ #getTxData(TXID) => txData(TN, DATA, B) ]]
       <chainID> B </chainID>
       <message>
         <msgID> TXID </msgID>
         <txNonce> TN </txNonce>
         <sigV> TW </sigV>
         <data> DATA </data>
         ...
       </message>
    requires TW ==Int 2 *Int B +Int 35
endmodule
