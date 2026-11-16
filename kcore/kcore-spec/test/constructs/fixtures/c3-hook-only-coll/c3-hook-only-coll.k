module C3-HOOK-ONLY-COLL
  imports INT
  imports BOOL
  syntax MyList [hook(LIST.List)]
  syntax MyList ::= MyList MyList     [left, function, total, hook(LIST.concat), symbol(_MyList_), assoc, unit(.MyList), element(MyListItem)]
  syntax MyList ::= ".MyList"         [function, total, hook(LIST.unit), symbol(.MyList)]
  syntax MyList ::= MyListItem(KItem) [function, total, hook(LIST.element), symbol(MyListItem)]
endmodule
