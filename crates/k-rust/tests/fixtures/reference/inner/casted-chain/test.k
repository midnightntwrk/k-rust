module CASTED-CHAIN
  syntax Int ::= r"[0-9]+" [token]
  syntax Val ::= Int
               | Val "+" Val [symbol(plus), left]
  rule X1:Val + X2:Val + X3:Val + X4:Val + X5:Val + X6:Val + X7:Val + X8:Val + X9:Val + X10:Val + X11:Val + X12:Val + X13:Val + X14:Val + X15:Val + X16:Val + X17:Val + X18:Val + X19:Val + X20:Val + X21:Val + X22:Val + X23:Val + X24:Val + X25:Val + X26:Val + X27:Val + X28:Val + X29:Val + X30:Val + X31:Val + X32:Val + X33:Val + X34:Val + X35:Val + X36:Val + X37:Val + X38:Val + X39:Val + X40:Val + X41:Val + X42:Val + X43:Val + X44:Val + X45:Val + X46:Val + X47:Val + X48:Val + X49:Val + X50:Val + X51:Val + X52:Val + X53:Val + X54:Val + X55:Val + X56:Val + X57:Val + X58:Val + X59:Val + X60:Val + X61:Val + X62:Val + X63:Val + X64:Val + X65:Val + X66:Val + X67:Val + X68:Val + X69:Val + X70:Val + X71:Val + X72:Val + X73:Val + X74:Val + X75:Val + X76:Val + X77:Val + X78:Val + X79:Val + X80:Val => 0
endmodule
