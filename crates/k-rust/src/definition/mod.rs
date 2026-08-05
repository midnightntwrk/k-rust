//! K definition syntax and KAST JSON interchange.

pub mod ast;
pub mod json;
pub mod resolve;

pub use ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, Location, ProductionItem,
    Sentence,
};
pub use resolve::{Error as ResolveError, ImportRef, ModuleId, ResolvedDefinition, ResolvedModule};
