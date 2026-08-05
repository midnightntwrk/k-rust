//! K definition syntax and KAST JSON interchange.

pub mod ast;
pub mod json;

pub use ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, Location, ProductionItem,
    Sentence,
};
