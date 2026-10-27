use k::Term;
use k::builtin::{Bool, Int, KSequence, int};

k::sorts! { Cmd: k::KItem; }

#[k::constructors(sort = Cmd, result = k::KResult)]
pub enum Op {
    Extract { b: Bool },
    Inline { b: Bool },
}

#[k::function(total, sort = Int, syntax = "bitValue({b})")]
pub struct BitValue {
    pub b: Term<Bool>,
}

#[k::equation]
fn bit_true(k::term![BitValue(true)]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation]
fn bit_false(k::term![BitValue(false)]: Term<Int>) -> Term<Int> {
    0
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Cmd) -> Self {
        Self {
            k: k::k![pgm],
            n: 0,
        }
    }
}

k::rules! {
    for Machine;

    extract: { k: [Op::Extract { b }, ..], n: _ } => { k: [..], n: BitValue(b) };
    inline_true: { k: [Op::Inline { b: true }, ..], n: _ } => { k: [..], n: 1 };
    inline_false: { k: [Op::Inline { b: false }, ..], n: _ } => { k: [..], n: 0 };
}

#[k::spec_module(name = "NATIVE-FINITE-SPEC", imports = [crate])]
pub mod spec {
    use super::*;

    k::claims! {
        for Machine;

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(int::ge(y, 0) && int::le(y, 1))]
        extracted_cases: { k: [Op::Extract { b: true | false }], n: _ } => { k: [], n: y };

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(int::ge(y, 0) && int::le(y, 1))]
        inlined_cases: { k: [Op::Inline { b: true | false }], n: _ } => { k: [], n: y };

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(int::ge(y, 0) && int::le(y, 1))]
        unselected_helper: { k: [Op::Extract { b }], n: _ } => { k: [], n: y } where b: Bool;

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(int::ge(y, 0) && int::le(y, 1))]
        unselected_inline: { k: [Op::Inline { b }], n: _ } => { k: [], n: y } where b: Bool;

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(int::ge(y, 0) && int::le(y, 1))]
        helper_composition: {
            k: [Op::Extract { b: true | false }, Op::Extract { b: true | false }], n: _,
        } => { k: [], n: y };

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(int::eq(y, 1))]
        partly_false_cases: { k: [Op::Extract { b: true | false }], n: _ } => { k: [], n: y };

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(int::gt(y, 1))]
        invalid_cases: { k: [Op::Extract { b: true | false }], n: _ } => { k: [], n: y };
    }
}
