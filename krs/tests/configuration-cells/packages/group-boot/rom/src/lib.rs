//! Start values for a definition that holds the group `Core`, in a package
//! that depends on the group's.
//!
//! Every function here is `internal`: a program cannot contain it. `Cost` is
//! over `Instr`, a sort the group's package declares. A definition's
//! initializer may call them, although the group's rules, which need the
//! configuration, are in a package this one depends on: the configuration
//! names only a function's declaration, and its equations stay here.

use group_core::{Instr, Op};
use k::Term;
use k::builtin::{Int, Map};

/// The word the image holds at each address it maps. Only `RomImage`'s
/// equation names it.
#[k::function(total, internal)]
pub fn RomWord() -> Term<Int> {
    9
}

/// The memory a definition starts with.
#[k::function(total, internal)]
pub fn RomImage() -> Term<Map<Int, Int>> {
    k::map![3 -> RomWord(), 4 -> RomWord() + 1]
}

/// What an instruction costs.
#[k::function(total, internal)]
pub fn Cost(instr: Term<Instr>) -> Term<Int>;

k::equations! {
    for Cost;
    cost_inc:   (Op::Inc())        => 1;
    cost_load:  (Op::Load { .. })  => 2;
    cost_store: (Op::Store { .. }) => 3;
}
