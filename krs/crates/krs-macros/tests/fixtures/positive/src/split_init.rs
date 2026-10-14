use crate::split_config::Split;

impl Split {
    #[language_host::init]
    pub fn init() -> Self {
        Self {
            k: language_host::configuration::KCell::new(language_host::k![crate::Halt]),
        }
    }
}
