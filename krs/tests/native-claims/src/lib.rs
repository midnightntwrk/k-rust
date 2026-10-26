use k::builtin::{Int, KSequence, Map, int, map};

k::sorts! { Cmd: k::KItem; }

#[k::constructors(sort = Cmd, result = k::KResult)]
pub enum Op {
    Tick,
    AndSelf { x: Int },
    XorSelf { x: Int },
    Write { key: Int, value: Int },
    Read { key: Int },
    Count { n: Int },
    Spin,
    SpinAgain,
    Done { n: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Cmd) -> Self {
        Self {
            k: k::k![pgm],
            n: 0,
            mem: map::empty(),
        }
    }
}

k::rules! {
    for Machine;

    execute_and_self: { k: [Op::AndSelf { x }, ..], n: _ } => { k: [..], n: int::bit_and(x, x) };
    execute_xor_self: { k: [Op::XorSelf { x }, ..], n: _ } => { k: [..], n: int::bit_xor(x, x) };
    write: { k: [Op::Write { key, value }, ..], mem: m } => { k: [..], mem: map::update(m, key, value) };
    read: { k: [Op::Read { key }, ..], mem: m, n: _ } => { k: [..], n: map::get(m, key) };

    tick: { k: [Op::Tick], n: 0 } => { n: 1 };
    count_zero: { k: [Op::Count { n: 0 }, ..] } => { k: [Op::Done { n: 0 }, ..] };
    #[k::requires(n > 0)]
    count_positive: { k: [Op::Count { n }, ..] } => { k: [Op::Count { n: n - 1 }, ..] };
    spin: { k: [Op::Spin, ..] } => { k: [Op::SpinAgain, ..] };
    spin_back: { k: [Op::SpinAgain, ..] } => { k: [Op::Spin, ..] };
}

#[k::spec_module(name = "NATIVE-CONTINUATION-SPEC", imports = [crate])]
pub mod continuation {
    use super::*;

    k::claims! {
        for Machine;

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(y == 1)]
        later_target: { k: [Op::Tick], n: 0 } => { n: y };

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::requires(0 <= n && n <= 1)]
        #[k::ensures(y == 1)]
        partially_covered: { k: [Op::Tick], n } => { n: y };

        #[k::claim(all_paths)]
        #[k::exists(y: Int)]
        #[k::ensures(y == 2)]
        terminal_false: { k: [Op::Tick], n: 0 } => { n: y };

        #[k::claim(all_paths)]
        #[k::requires(n >= 0)]
        countdown: { k: [Op::Count { n }] } => { k: [Op::Done { n: 0 }] };

        #[k::claim(all_paths)]
        cycle: { k: [Op::Spin] } => { k: [Op::Done { n: 0 }] };
    }
}

#[k::spec_module(name = "NATIVE-PRIMITIVE-SPEC", imports = [crate])]
pub mod primitives {
    use super::*;

    k::claims! {
        for Machine;

        #[k::claim(all_paths)]
        and_self: { k: [Op::AndSelf { x }], n: _ } => { k: [], n: x };

        #[k::claim(all_paths)]
        xor_self: { k: [Op::XorSelf { x }], n: _ } => { k: [], n: 0 };

        #[k::claim(all_paths)]
        store_load: {
            k: [Op::Write { key, value }, Op::Read { key }], mem: m, n: _,
        } => {
            k: [], n: value, mem: map::update(m, key, value),
        };

        #[k::claim(all_paths)]
        #[k::requires(key != other && map::get(m, other) == old)]
        distinct_store_load: {
            k: [Op::Write { key, value }, Op::Read { key: other }], mem: m, n: old,
        } => {
            k: [], n: old, mem: map::update(m, key, value),
        };

        #[k::claim(all_paths)]
        overwrite: {
            k: [Op::Write { key, value: first }, Op::Write { key, value: last }, Op::Read { key }], mem: m, n: _,
        } => {
            k: [], n: last, mem: map::update(m, key, last),
        };

        #[k::claim(all_paths)]
        concrete_store_load: {
            k: [Op::Write { key: 1, value: 12 }, Op::Read { key: 1 }],
            mem: map::update(map::empty(), 0, 10), n: 0,
        } => {
            k: [], n: 12, mem: map::update(map::update(map::empty(), 0, 10), 1, 12),
        };

        #[k::claim(all_paths)]
        concrete_wrong_value: {
            k: [Op::Write { key: 1, value: 12 }, Op::Read { key: 1 }],
            mem: map::update(map::empty(), 0, 10), n: 0,
        } => {
            k: [], n: 13, mem: map::update(map::update(map::empty(), 0, 10), 1, 12),
        };

        #[k::claim(all_paths)]
        wrong_value: {
            k: [Op::Write { key, value }, Op::Read { key }], mem: m, n: _,
        } => {
            k: [], n: value + 1, mem: map::update(m, key, value),
        };
    }
}
