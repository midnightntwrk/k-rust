//! Claims over the same natural-number specification the introduction executes.

use story_plus::{Machine, NatSyntax, Plus};

// [!region claim]
k::claims! {
    for Machine;
    use NatSyntax::*;

    #[k::claim(all_paths)]
    add_one: {
        k: [Plus(Succ(Zero()), n)],
    } => {
        k: [Succ(n)],
    };
}
// [!endregion claim]
