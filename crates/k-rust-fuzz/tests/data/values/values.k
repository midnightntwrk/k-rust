// Hole values of every kind the values module generates and prints (FZ-03 review, FZ-G6,
// FZ-09). The program grammar holds one data sort (`Stmt`), so a constructor that takes a
// program sort can be refused; every other sort is declared in the semantic module, outside the
// closure of the program sort. Each configuration variable binds a value of one hole sort, so
// the tests can assemble a configuration and read the value back at its cell.

module VALUES-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX

  syntax Pgm  ::= "run"                      [symbol(run)]
                | Stmt
  syntax Stmt ::= Id "=" Int ";"             [symbol(assign)]
                | "skip"                     [symbol(skip)]
endmodule

module VALUES
  imports VALUES-SYNTAX
  imports INT
  imports BOOL
  imports STRING
  imports BYTES
  imports LIST
  imports SET
  imports MAP
  imports MINT
  imports ID

  // A declared instance of MInt, so that its literals parse.
  syntax MInt{8}

  // A sort hooked INT.Int under its own name, with its own literals.
  syntax MyInt [hook(INT.Int)]
  syntax MyInt ::= r"[\\+\\-]?[0-9]+"         [token, prec(2)]

  // Records, recursion, subsorts, builtin subsorts and mixfix syntax.
  syntax Account ::= account(Int, Map)       [symbol(account)]
  syntax Tree    ::= leaf(Int)               [symbol(leaf)]
                   | node(Tree, Tree)        [symbol(node)]
  syntax Shape   ::= Circle | Square
  syntax Circle  ::= circle(Int)             [symbol(circle)]
  syntax Square  ::= square(Int, Bool)       [symbol(square)]
                   | "unit"                  [symbol(unitSquare)]
  syntax Val     ::= Int | Bool | String
  syntax Pair    ::= Int "&" Val             [symbol(pair)]
  syntax Rec     ::= rec(Val, Shape, Tree)   [symbol(rec)]
  syntax Wrapper ::= wrap(MyInt)             [symbol(wrap)]
                   | wb(String, Bytes)       [symbol(wb)]
                   | wl(List)                [symbol(wl)]
  // An MInt argument: the frontend infers parametric sorts only with Z3.
  syntax Word    ::= w8(MInt{8})             [symbol(w8)]

  // A builtin hooked under a second name, whose values are those of Int: a subsort holding
  // both keeps Int, whose literals read back at their own sort.
  syntax AInt [hook(INT.Int)]
  syntax Num     ::= Int | AInt
  // A nested infix term without a bracket production has no text that reads back as it.
  syntax Path    ::= Path "/" Path           [symbol(slash)]
                   | seg(Int)                [symbol(seg)]

  // Constructors the generators must not choose.
  syntax Holder  ::= hold(Stmt)              [symbol(hold)]
                   | named(Id, Int)          [symbol(named)]
                   | anon(Int)               [symbol(anon)]
                   | mk(Int)                 [symbol(mk), function, total]
                   | Loop
  syntax Loop    ::= loop(Loop)              [symbol(loop)]
  rule mk(I) => anon(I)

  configuration <k> $PGM:Pgm </k>
                <shape> $SHAPE:Shape </shape>
                <rec> $REC:Rec </rec>
                <pair> $PAIR:Pair </pair>
                <wrapper> $WRAPPER:Wrapper </wrapper>
                <account> $ACCOUNT:Account </account>
                <list> $LIST:List </list>
                <set> $SET:Set </set>
                <map> $MAP:Map </map>

  rule <k> run => .K ... </k>
endmodule
