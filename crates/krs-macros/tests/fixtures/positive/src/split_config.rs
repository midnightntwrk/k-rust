#[allow(dead_code)]
#[language_host::configuration(root = "split")]
pub struct Split {
    pub k: language_host::configuration::KCell<language_host::builtin::KSequence>,
}
