#[k::cell]
pub struct Account {
    #[k::cell(name = "acctID")]
    pub account_id: Int,
    #[k::cell(name = "balance")]
    pub balance: Int,
    #[k::cell(name = "code")]
    pub code: Bytes,
    #[k::cell(name = "nonce")]
    pub nonce: Int,
    #[k::cell(name = "storage")]
    pub storage: Map<Int, Int>,
    #[k::cell(name = "origStorage")]
    pub original_storage: Map<Int, Int>,
}

#[k::cell]
pub struct Accounts {
    #[k::cell(name = "account", multiplicity = "*", cell_type = "Map", nested)]
    pub account: Account,
}
