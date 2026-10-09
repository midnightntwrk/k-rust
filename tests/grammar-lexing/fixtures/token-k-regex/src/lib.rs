//! `Name`'s regex is the text of K's own `#LowerId` token, which K declares
//! at `prec(2)`. K keys a regex token by its text, so at the default `prec`
//! Java K reports inconsistent token precedence and k-rust fails to load.

use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Stmt: KItem;
    impl KItem for Name;
}

#[k::token(regex = r"[a-z][a-zA-Z0-9]*")]
pub struct Name(pub String);

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
