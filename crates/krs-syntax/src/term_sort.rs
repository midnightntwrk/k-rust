use quote::ToTokens;
use syn::spanned::Spanned;
use syn::{GenericArgument, Path, PathArguments, TraitBoundModifier, Type, TypeParamBound};

use crate::path::is_plain_path;
use crate::{SyntaxError, SyntaxErrorKind};

/// A validated `Term<SortPath>` or `Term<dyn SortPath>` type reference.
#[derive(Clone, Debug)]
pub struct TermSort {
    ty: Type,
    sort: Path,
    dynamic: bool,
}

impl TermSort {
    /// Returns the complete authored `Term<...>` type.
    #[must_use]
    pub const fn ty(&self) -> &Type {
        &self.ty
    }

    /// Returns the Rust-resolved sort path inside `Term`.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }

    /// Returns whether the sort was written as a `dyn` trait object.
    #[must_use]
    pub const fn is_dynamic(&self) -> bool {
        self.dynamic
    }

    /// Returns the token-stream text of the sort path, such as `model :: Expr`,
    /// which descriptors carry as the sort's `authored_path`.
    #[must_use]
    pub fn sort_token_text(&self) -> String {
        self.sort.to_token_stream().to_string()
    }
}

pub(crate) fn parse_term_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    let Type::Path(term_path) = &ty else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    };
    if term_path.qself.is_some() || term_path.path.segments.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    }
    let last_index = term_path.path.segments.len() - 1;
    for (index, segment) in term_path.path.segments.iter().enumerate() {
        if index != last_index && !matches!(segment.arguments, PathArguments::None) {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidTermType,
                segment.span(),
            ));
        }
    }
    let last = &term_path.path.segments[last_index];
    if last.ident != "Term" {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            last.span(),
        ));
    }
    let PathArguments::AngleBracketed(arguments) = &last.arguments else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            last.span(),
        ));
    };
    if arguments.args.len() != 1 {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            arguments.span(),
        ));
    }
    let Some(GenericArgument::Type(sort_type)) = arguments.args.first() else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            arguments.span(),
        ));
    };

    let (sort, dynamic) = match sort_type {
        Type::Path(sort) if sort.qself.is_none() && is_plain_path(&sort.path) => {
            (sort.path.clone(), false)
        }
        Type::TraitObject(object) if object.dyn_token.is_some() && object.bounds.len() == 1 => {
            let Some(TypeParamBound::Trait(bound)) = object.bounds.first() else {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidTermType,
                    object.span(),
                ));
            };
            if !matches!(bound.modifier, TraitBoundModifier::None)
                || bound.lifetimes.is_some()
                || bound.paren_token.is_some()
                || !is_plain_path(&bound.path)
            {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidTermType,
                    bound.span(),
                ));
            }
            (bound.path.clone(), true)
        }
        _ => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidTermType,
                sort_type.span(),
            ));
        }
    };
    Ok(TermSort { ty, sort, dynamic })
}

pub(crate) fn parse_readable_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    let Type::Path(path) = &ty else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    };
    if path.qself.is_some() || !is_plain_path(&path.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    }
    Ok(TermSort {
        sort: path.path.clone(),
        ty,
        dynamic: false,
    })
}

/// Parses one turbofish argument of a parametric application head
/// (`Choose::<k::builtin::Int>` or `Choose::<dyn ExpSort>`, KF-027): the sort
/// marker that goes inside `k::Term<..>`, a plain path or a single-trait
/// `dyn` object.
pub(crate) fn parse_instance_sort(ty: &Type) -> Option<TermSort> {
    match ty {
        Type::Path(sort) if sort.qself.is_none() && is_plain_path(&sort.path) => Some(TermSort {
            ty: ty.clone(),
            sort: sort.path.clone(),
            dynamic: false,
        }),
        Type::TraitObject(object) if object.dyn_token.is_some() && object.bounds.len() == 1 => {
            let Some(TypeParamBound::Trait(bound)) = object.bounds.first() else {
                return None;
            };
            (matches!(bound.modifier, TraitBoundModifier::None)
                && bound.lifetimes.is_none()
                && bound.paren_token.is_none()
                && is_plain_path(&bound.path))
            .then(|| TermSort {
                ty: ty.clone(),
                sort: bound.path.clone(),
                dynamic: true,
            })
        }
        Type::Group(group) => parse_instance_sort(&group.elem),
        _ => None,
    }
}
