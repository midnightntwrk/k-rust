//! Token productions follow their carrier's Rust visibility (KF-045): `Name`
//! is not `pub`, so its only token is K `private` and lexes only in this
//! package's rules. `StmtSyntax::Call` is program syntax, yet no program can
//! spell its `Name` field.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
    impl KItem for Name;
}

#[k::token(regex = r"[a-z]+")]
struct Name(String);

#[allow(private_interfaces)]
#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Call))]
pub enum StmtSyntax {
    #[k::syntax("call {target}")]
    Call { target: Name },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}
