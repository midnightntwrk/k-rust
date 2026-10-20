use renamed_krs::KResult;
use renamed_krs::builtin::{Int, Map};

renamed_krs::sorts! {
    Reg8;
    Cpu;
}

#[renamed_krs::constructors(sort = Cpu, result = KResult)]
#[renamed_krs::precedence((Registers))]
enum CpuSyntax {
    #[renamed_krs::syntax("registers({file})")]
    Registers {
        file: Map<Reg8, Int>, //~ ERROR K's `Map` sort is not parametric, so a field or term sort is the sort `Map` and cannot constrain its keys or values
    },
}

#[renamed_krs::function(total, sort = Cpu, syntax = "load({regs})")]
pub struct Load {
    pub regs: renamed_krs::Term<Map<Reg8, Int>>, //~ ERROR write `Map` without generic arguments
}

#[renamed_krs::function(total, sort = Cpu, syntax = "trace({log})")]
pub struct Trace {
    pub log: renamed_krs::Term<renamed_krs::builtin::List<Int>>, //~ ERROR a field or term sort is the sort `List` and cannot constrain its elements
}

fn main() {}
