#[language_host::token(regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2)]
pub struct Identifier(pub String);

impl KItem for Identifier {}
impl Expr for Identifier {}
impl KResult for Identifier {}
