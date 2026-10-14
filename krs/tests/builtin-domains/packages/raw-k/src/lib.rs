//! A raw K rule (KF-037).
//!
//! `double(e)` is program syntax whose only rule is K text that KRS keeps
//! verbatim in the package's semantics module; K parses it with the
//! package's grammar. The package opts in with `allow-raw-k`.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

/// Doubling, defined only by the raw rule below.
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Double))]
#[rustfmt::skip]
pub enum Doubling {
    #[k::syntax("double({value})")] #[k::strict]
    Double { value: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::raw_k!(r#"rule <k> double(I:Int) => I +Int I ... </k> [label(raw-double)]"#);
