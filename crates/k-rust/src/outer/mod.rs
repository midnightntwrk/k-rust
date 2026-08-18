//! The unlowered AST and parser for user-authored `.k` files.

mod ast;
mod checks;
mod loader;
mod lower;
mod markdown;
mod parser;
mod virtual_path;

pub use ast::*;
pub use checks::{check_brackets, check_list_declarations};
pub use loader::{
    LoadError, LoadOptions, LoadedDefinition, ResolvedSource, SourceResolver, load,
    load_with_options,
};
pub use lower::lower;
pub use markdown::{MarkdownError, extract_fenced_k_code};
pub use parser::{ParseError, parse};
pub use virtual_path::normalize_virtual_path;
