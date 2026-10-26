use k::builtin::{Int, KSequence};

k::sorts! { Cmd: k::KItem; }

#[k::constructors(sort = Cmd, result = k::KResult)]
pub enum Op {
    Tick,
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
