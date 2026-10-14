#[cfg(test)]
mod tests {}

#[cfg_attr(feature = "x", derive(Debug))]
pub struct S;

pub fn f() {
    #[cfg(unix)]
    let _ = 1;
}
