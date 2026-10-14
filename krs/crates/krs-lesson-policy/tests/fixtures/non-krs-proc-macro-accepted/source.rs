#![allow(dead_code)]
//! Inner docs.

#[derive(Clone, Copy, Debug, Default, core::cmp::PartialEq, ::std::cmp::Eq, Hash)]
#[repr(u8)]
#[non_exhaustive]
pub enum Flag {
    Off,
}

#[inline]
#[must_use]
pub fn build() -> Vec<u32> {
    let values = std::vec![1, 2];
    assert_eq!(values.len(), 2);
    debug_assert!(matches!(values[0], 1));
    let _ = core::format_args!("{}", 1);
    values
}
