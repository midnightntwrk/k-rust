//! Pure compilation passes and KORE emission.

mod module_to_kore;
mod sort_injections;
mod term_to_kore;

pub use module_to_kore::{
    DeclarationError, DeclarationModules, ModuleToKoreError, declaration_modules,
    declaration_modules_from_resolved, encode_kore_identifier, encode_kore_label, encode_kore_sort,
    module_to_kore, module_to_kore_from_resolved,
};
pub use sort_injections::{
    SortInjectionError, SortInjector, add_sort_injections, add_sort_injections_from_resolved,
};
pub use term_to_kore::{
    TermConversionError, TermConverter, term_to_kore, term_to_kore_from_resolved,
};
