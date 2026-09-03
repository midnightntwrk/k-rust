// reference: k/result/bin/kompile -w2e -w all --backend haskell configVarInitial.k
module CONFIGVARINITIAL-SYNTAX
endmodule

module CONFIGVARINITIAL
imports CONFIGVARINITIAL-SYNTAX

configuration <k> $PGM </k>
              <goods>
	        <good multiplicity="*" type="Set" initial=""> $FOO </good>
	      </goods>
	      <bads>
	        <bad multiplicity="*" type="Set"> $FOO </bad>
	      </bads>

endmodule
