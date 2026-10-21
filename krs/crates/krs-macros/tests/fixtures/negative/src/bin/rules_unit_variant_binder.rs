use renamed_krs as k;

renamed_krs::sorts! {
    Cmd: renamed_krs::KItem;
}

#[k::constructors(sort = Cmd, result = renamed_krs::KResult)]
#[k::precedence((Load, Halt))]
pub enum CmdSyntax {
    #[k::syntax("load({c})")]
    Load { c: Cmd },
    #[k::syntax("halt")]
    Halt,
}

// A bare `Halt` is a binder in a pattern; rustc rejects it where the block's
// import makes it a unit variant, which `Halt()` or `CmdSyntax::Halt` spells.
k::rules! {
    for Cmd;
    use CmdSyntax::*;
    load_halt: Load(Halt) => Halt(); //~ ERROR mismatched types
}

fn main() {}
