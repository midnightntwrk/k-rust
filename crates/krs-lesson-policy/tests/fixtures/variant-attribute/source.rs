#[derive(Default)]
#[default]
pub struct NotAVariant;

#[derive(Default)]
pub enum Choice {
    #[default(First)]
    First,
}

pub struct Fields {
    #[default]
    pub value: u8,
}

pub fn body() {
    #[default]
    let _x = 1;
}
