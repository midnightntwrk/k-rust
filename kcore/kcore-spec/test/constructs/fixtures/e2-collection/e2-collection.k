module E2-COLLECTION
  imports BOOL
  imports K-EQUAL
  syntax MySet [hook(SET.Set)]
  syntax MySet ::= MySet MySet                       [left, function, hook(SET.concat), symbol(_MySet_), assoc, comm, unit(.MySet), idem, element(MySetItem)]
  syntax MySet ::= ".MySet"                          [function, total, hook(SET.unit), symbol(.MySet)]
  syntax MySet ::= MySetItem(KItem)                  [function, total, hook(SET.element), symbol(MySetItem), injective]
  syntax MyList [hook(LIST.List)]
  syntax MyList ::= MyList MyList                    [left, function, total, hook(LIST.concat), symbol(_MyList_), assoc, unit(.MyList), element(MyListItem), update(MyList:set)]
  syntax MyList ::= ".MyList"                        [function, total, hook(LIST.unit), symbol(.MyList)]
  syntax MyList ::= MyListItem(KItem)                [function, total, hook(LIST.element), symbol(MyListItem)]
  syntax MyList ::= MyList "[" Int "<-" KItem "]"    [function, hook(LIST.update), symbol(MyList:set)]
  syntax Int
endmodule
