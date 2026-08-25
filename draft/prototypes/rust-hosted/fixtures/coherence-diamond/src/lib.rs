trait KItem {}
trait Expr {}
trait KResult {}
trait Value: Expr + KResult {}

// The tempting encoding of transitive K subsorting as blanket Rust impls is
// incoherent at the diamond's join.
impl<T: Expr> KItem for T {}
impl<T: KResult> KItem for T {}

struct V;
impl Expr for V {}
impl KResult for V {}
impl Value for V {}

