use span_probe_macros::probe;

pub trait Expr {}
pub struct Term<T: ?Sized>(core::marker::PhantomData<T>);

#[probe(path = "not a Rust path")]
pub fn malformed(_: Term<dyn Expr>) -> Term<dyn Expr> {
    loop {}
}

