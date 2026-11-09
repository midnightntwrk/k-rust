//! What a value denotes where it is used.
//!
//! A local names its value, and a block's value is its result, so a value
//! written through blocks and locals is, where it is used, the term its
//! innermost result names. Each pass that judges a value at its uses judges
//! that term: sort inference ([`super::infer`]) for the sort the position
//! reads it at, the element-type pass ([`super::collection_types`]) for its
//! element types. So a value gets, through any number of blocks and locals,
//! the verdict the term it denotes gets written at the use.

use krs_ir::DescriptorTerm;

/// The term a value denotes where it is used, and the `let` statements in
/// whose scope that term is read.
pub(super) struct Denotation<'t> {
    /// The statements of the blocks the term lies in, outermost first, each
    /// a [`DescriptorTerm::Let`]: the term may read the names they bind.
    pub(super) statements: Vec<&'t DescriptorTerm>,
    /// The term itself: never a block, nor a name one of [`Self::statements`]
    /// binds to its whole value with no ascription.
    pub(super) term: &'t DescriptorTerm,
}

impl Denotation<'_> {
    /// Whether one of the statements binds `name`. The term's `name` is then
    /// that statement's: a part of its value, or its value read at the sort
    /// its ascription names, which the name has as its own.
    pub(super) fn binds(&self, name: &str) -> bool {
        self.statements.iter().any(|statement| match statement {
            DescriptorTerm::Let { pattern, .. } => super::infer::pattern_binds(pattern, name),
            _ => false,
        })
    }
}

/// What `value` denotes where it is used.
///
/// - A block `{ let p = v; r }` denotes what its result `r` denotes, read in
///   the scope of its statement.
/// - A name a statement binds whole with no ascription, `let x = v;`, denotes
///   what `v` denotes, read in the scope `v` is written in: the binding adds
///   nothing to the value.
/// - Every other term denotes itself: a name a statement binds to a part of
///   its value (`let [x, ..] = v;`) or with an ascription (`let x: S = v;`,
///   the value read at `S`), a name bound outside the value, and any term
///   that is not a block.
///
/// A branching body and parentheses are no terms of their own: the function
/// shorthand defines one equation per branch, each branch's result read at
/// the function's result, and parentheses group the term they enclose.
pub(super) fn denotation(value: &DescriptorTerm) -> Denotation<'_> {
    let mut statements = Vec::new();
    let mut term = value;
    loop {
        match term {
            DescriptorTerm::Let { body, .. } => {
                statements.push(term);
                term = body;
            }
            DescriptorTerm::Variable { name, .. } => {
                let Some(index) = statements.iter().rposition(|statement| {
                    matches!(statement, DescriptorTerm::Let { pattern, .. }
                        if super::infer::pattern_binds(pattern, name))
                }) else {
                    break;
                };
                let DescriptorTerm::Let {
                    pattern,
                    sort: None,
                    value,
                    ..
                } = statements[index]
                else {
                    break;
                };
                if !matches!(pattern.as_ref(), DescriptorTerm::Variable { .. }) {
                    break;
                }
                statements.truncate(index);
                term = value;
            }
            _ => break,
        }
    }
    Denotation { statements, term }
}
