#[rustfmt::skip]
pub fn table() -> [u8; 4] {
    #[rustfmt::skip]
    let values = [1,   2,
                  3,   4];
    values
}

#[rustfmt::skip]
mod layout {
    pub struct Cell;
}
