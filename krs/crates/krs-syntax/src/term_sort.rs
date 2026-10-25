use quote::ToTokens;
use syn::spanned::Spanned;
use syn::{GenericArgument, Path, PathArguments, TraitBoundModifier, Type, TypeParamBound};

use crate::configuration::{SortArgument, collection_arguments};
use crate::path::{
    is_plain_path, parametric_collection, parametric_collection_error, without_last_arguments,
};
use crate::{SyntaxError, SyntaxErrorKind};

/// A validated `Term<SortPath>` or `Term<dyn SortPath>` type reference, or
/// the `ml::Predicate` subject and result type of a predicate simplification
/// (KF-039).
#[derive(Clone, Debug)]
pub struct TermSort {
    ty: Type,
    sort: Path,
    dynamic: bool,
    predicate: bool,
    /// Whether this is the result sort of the function named by [`Self::sort`],
    /// which a `k::equations!` header names instead of a sort.
    function_result: bool,
    /// The element types of a typed collection sort (`Int` of
    /// `k::Term<Set<Int>>`), which only a constructor field or a function
    /// signature may declare; empty for every other sort.
    arguments: Vec<SortArgument>,
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

    /// Returns whether the type is `ml::Predicate` (KF-039): [`Self::sort`]
    /// is then the authored path of `Predicate` itself, not a sort.
    #[must_use]
    pub const fn is_predicate(&self) -> bool {
        self.predicate
    }

    /// Whether [`Self::sort`] names a function whose result sort this is: the
    /// sort of every equation in a `k::equations!` table, which rustc
    /// resolves through the function's `__KrsFunction::Result`.
    #[must_use]
    pub const fn is_function_result(&self) -> bool {
        self.function_result
    }

    /// Returns the element types of a typed collection sort, such as `Int`
    /// and `Set<Int>` of `k::Term<Map<Int, Set<Int>>>`; empty for every
    /// other sort.
    #[must_use]
    pub fn arguments(&self) -> &[SortArgument] {
        &self.arguments
    }

    /// The element types, for a pass that keys them.
    pub(crate) fn arguments_mut(&mut self) -> &mut [SortArgument] {
        &mut self.arguments
    }

    /// Returns the token-stream text of the sort path, such as `model :: Expr`,
    /// which descriptors carry as the sort's `authored_path`.
    #[must_use]
    pub fn sort_token_text(&self) -> String {
        self.sort.to_token_stream().to_string()
    }
}

pub(crate) fn parse_term_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    parse_term_sort_with(ty, false)
}

/// Parses the `Term<..>` type of a constructor field or a function
/// parameter or result, whose sort may be a typed collection
/// (`k::Term<Map<Int, Set<Int>>>`): the sort is the collection, and its
/// element types are [`TermSort::arguments`].
pub(crate) fn parse_typed_term_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    parse_term_sort_with(ty, true)
}

fn parse_term_sort_with(ty: Type, typed: bool) -> Result<TermSort, SyntaxError> {
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

    if let Type::Path(sort) = sort_type
        && sort.qself.is_none()
    {
        if typed && parametric_collection(&sort.path).is_some() {
            return typed_collection(ty.clone(), sort_type);
        }
        if let Some(error) = parametric_collection_error(&sort.path, false) {
            return Err(error);
        }
    }
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
    Ok(TermSort {
        ty,
        sort,
        dynamic,
        predicate: false,
        function_result: false,
        arguments: Vec::new(),
    })
}

/// A typed collection sort `Map<K, V>`, `List<T>`, or `Set<T>` written as
/// `sort_type`, whose authored type is `ty`.
fn typed_collection(ty: Type, sort_type: &Type) -> Result<TermSort, SyntaxError> {
    let Type::Path(path) = sort_type else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            sort_type.span(),
        ));
    };
    Ok(TermSort {
        ty,
        sort: without_last_arguments(&path.path),
        dynamic: false,
        predicate: false,
        function_result: false,
        arguments: collection_arguments(sort_type, invalid_collection_argument)?,
    })
}

/// The sort type inside `Term<..>`: `Set<Int>` of `k::Term<Set<Int>>`.
pub(crate) fn term_sort_type(ty: &Type) -> Option<&Type> {
    let Type::Path(term) = ty else {
        return None;
    };
    match &term.path.segments.last()?.arguments {
        PathArguments::AngleBracketed(arguments) if arguments.args.len() == 1 => {
            match arguments.args.first()? {
                GenericArgument::Type(sort) => Some(sort),
                _ => None,
            }
        }
        _ => None,
    }
}

/// `ty` with the element types of a typed collection sort removed:
/// `k::Term<Set>` for `k::Term<Set<Int>>`; every other type unchanged.
pub(crate) fn without_collection_arguments(ty: &Type) -> Type {
    let mut ty = ty.clone();
    if let Type::Path(term) = &mut ty
        && let Some(last) = term.path.segments.last_mut()
        && let PathArguments::AngleBracketed(arguments) = &mut last.arguments
        && let Some(GenericArgument::Type(Type::Path(sort))) = arguments.args.first_mut()
        && sort.qself.is_none()
        && parametric_collection(&sort.path).is_some()
    {
        sort.path = without_last_arguments(&sort.path);
    }
    ty
}

fn invalid_collection_argument(span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidCollectionArgument, span)
}

/// Parses the subject or result type of a term-shaped rule fn: a `Term<..>`
/// type, or `ml::Predicate` for a predicate simplification (KF-039), a plain
/// path ending in `Predicate` whose rustc identity the expansion checks.
pub(crate) fn parse_rule_term_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    if let Type::Path(path) = &ty
        && path.qself.is_none()
        && is_plain_path(&path.path)
        && path
            .path
            .segments
            .last()
            .is_some_and(|last| last.ident == "Predicate")
    {
        return Ok(TermSort {
            sort: path.path.clone(),
            ty,
            dynamic: false,
            predicate: true,
            function_result: false,
            arguments: Vec::new(),
        });
    }
    parse_term_sort(ty)
}

/// Parses a `Term<..>` sort, or else a readable sort path. A parametric
/// collection sort inside `Term<..>` reports that rather than the readable
/// parse's failure on the `Term` path itself.
pub(crate) fn parse_term_or_readable_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    parse_term_sort(ty.clone()).or_else(|error| match error.kind() {
        SyntaxErrorKind::ParametricCollectionSort { .. } => Err(error),
        _ => parse_readable_sort(ty),
    })
}

pub(crate) fn parse_readable_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    parse_readable_sort_with(ty, false)
}

/// Parses the readable sort of a constructor field, which may be a typed
/// collection (`Set<Int>`), as [`parse_typed_term_sort`] does inside
/// `Term<..>`.
pub(crate) fn parse_typed_readable_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    parse_readable_sort_with(ty, true)
}

fn parse_readable_sort_with(ty: Type, typed: bool) -> Result<TermSort, SyntaxError> {
    let Type::Path(path) = &ty else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    };
    if path.qself.is_none() {
        if typed && parametric_collection(&path.path).is_some() {
            return typed_collection(ty.clone(), &ty);
        }
        if let Some(error) = parametric_collection_error(&path.path, false) {
            return Err(error);
        }
    }
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
        predicate: false,
        function_result: false,
        arguments: Vec::new(),
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
            predicate: false,
            function_result: false,
            arguments: Vec::new(),
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
                predicate: false,
                function_result: false,
                arguments: Vec::new(),
            })
        }
        Type::Group(group) => parse_instance_sort(&group.elem),
        _ => None,
    }
}

/// The sort of a `k::equations!` row: the result sort of the function the
/// table's header path names.
pub(crate) fn parse_function_result_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    match &ty {
        Type::Path(path) if path.qself.is_none() && is_plain_path(&path.path) => Ok(TermSort {
            sort: path.path.clone(),
            ty,
            dynamic: false,
            predicate: false,
            function_result: true,
            arguments: Vec::new(),
        }),
        _ => Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        )),
    }
}
