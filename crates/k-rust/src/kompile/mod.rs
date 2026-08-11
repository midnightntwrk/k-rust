//! Pure compilation passes and KORE emission.

mod module_to_kore;

pub use module_to_kore::{
    DeclarationError, DeclarationModules, declaration_modules, declaration_modules_from_resolved,
    encode_kore_identifier, encode_kore_label, encode_kore_sort,
};
