//! A Rust encoding of transitive sort membership is incoherent at a diamond.

trait KItem {}
trait Expr: KItem {}
trait KResult: KItem {}
trait Value: Expr + KResult {}
trait Is<S: ?Sized> {}

impl<T: ?Sized + Is<dyn Expr>> Is<dyn KItem> for T {}
impl<T: ?Sized + Is<dyn KResult>> Is<dyn KItem> for T {}

fn main() {}

