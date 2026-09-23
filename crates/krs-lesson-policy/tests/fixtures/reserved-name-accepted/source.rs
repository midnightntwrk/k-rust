pub static KRS_REGISTRATIONS: u8 = 0;

fn krs_register_descriptors() {}

pub struct _krs_single;

pub struct Fields {
    pub __krs_field: u8,
}

pub enum Choice {
    __KrsVariant,
}

pub fn locals() -> u8 {
    let __krs_local = 1;
    __krs_local
}

use std::vec::Vec as KrsVec;
