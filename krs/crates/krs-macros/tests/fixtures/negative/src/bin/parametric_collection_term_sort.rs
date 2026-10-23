use renamed_krs::KResult;
use renamed_krs::builtin::{Int, Map};

renamed_krs::sorts! {
    Reg8;
    Cpu;
}

// A constructor field and a function signature declare element types.
#[renamed_krs::constructors(sort = Cpu, result = KResult)]
#[renamed_krs::precedence((Registers, Flags))]
enum CpuSyntax {
    #[renamed_krs::syntax("registers({file})")]
    Registers { file: Map<Reg8, Int> },
    #[renamed_krs::syntax("flags({file})")]
    Flags {
        file: Map<Reg8, &Int>, //~ ERROR an element type of a collection is a sort
    },
}

#[renamed_krs::function(total, sort = Map<Reg8, Int>, syntax = "load({regs})")]
pub struct Load {
    pub regs: renamed_krs::Term<Map<Reg8, Int>>,
}

// An equation's subject and result sorts name only the sort.
#[renamed_krs::equation]
fn load(
    renamed_krs::term![Load(regs)]: renamed_krs::Term<Map<Reg8, Int>>, //~ ERROR a binder's or term's sort names only the sort `Map`
) -> renamed_krs::Term<Map> {
    regs
}

fn main() {}
