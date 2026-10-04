#[expect(
    dead_code,
    reason = "The fixture registers the split configuration without reading its cell directly."
)]
#[language_host::configuration(root = "split")]
pub struct Split {
    pub k: language_host::configuration::KCell<language_host::builtin::KSequence>,
}
