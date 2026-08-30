// Minimized from EVM-OPTIMIZATIONS.optimized.add at pinned KEVM revision
// 5dd05ea7936c13f4029389bafd25785ed9ff0a55.
module EVM-OPTIMIZED-ADD
  imports INT

  syntax Input ::= "optimized-add"
                 | "#next" "[" OpCode "]"
  syntax OpCode ::= "ADD"
  syntax Schedule ::= "CANCUN"
  syntax WordStack ::= ".WordStack"
                     | Int ":" WordStack

  syntax Int ::= "chop" "(" Int ")" [function, total]
               | "#sizeWordStack" "(" WordStack ")" [function, total]
               | "Gverylow" "<" Schedule ">" [function, total]
               | Int "-Gas" Int [function, total]

  rule chop(I) => I modInt 115792089237316195423570985008687907853269984665640564039457584007913129639936
  rule #sizeWordStack(.WordStack) => 0
  rule #sizeWordStack(_ : WS) => 1 +Int #sizeWordStack(WS)
  rule Gverylow < CANCUN > => 3
  rule I -Gas J => I -Int J

  configuration
    <kevm>
      <k> $PGM:Input </k>
      <schedule> CANCUN </schedule>
      <useGas> false </useGas>
      <ethereum>
        <evm>
          <callState>
            <wordStack> 5 : 6 : .WordStack </wordStack>
            <pc> 0 </pc>
            <gas> 99 </gas>
          </callState>
        </evm>
      </ethereum>
    </kevm>

  rule <k> optimized-add => #next [ ADD ] ... </k>

  rule [optimized.add]:
    <kevm>
      <k>
        ( #next [ ADD ] => .K ) ...
      </k>
      <schedule>
        SCHED
      </schedule>
      <useGas>
        USEGAS
      </useGas>
      <ethereum>
        <evm>
          <callState>
            <wordStack>
              ( W0 : W1 : WS => chop((W0 +Int W1)) : WS )
            </wordStack>
            <pc>
              ( PCOUNT => PCOUNT +Int 1 )
            </pc>
            <gas>
              ( GAVAIL => #if USEGAS #then GAVAIL -Gas Gverylow < SCHED > #else GAVAIL #fi )
            </gas>
          </callState>
        </evm>
      </ethereum>
    </kevm>
    requires ( #if USEGAS #then Gverylow < SCHED > <=Int GAVAIL #else true #fi )
     andBool ( #sizeWordStack(WS) <=Int 1023 )
    [priority(40)]
endmodule
