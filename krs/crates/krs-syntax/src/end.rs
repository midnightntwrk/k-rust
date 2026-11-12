//! `#[k::end(finished)]` and `#[k::end(refused)]`: a declared end of the definition.
//!
//! An end is a set of states: those where the definition says the run is over, and in which
//! class. It is declared in one of two spellings.
//!
//! ```ignore
//! #[k::end(refused)]
//! #[k::requires(!memory.contains_key(addr))]
//! fn unmapped_read(
//!     addr: k::Term<Int>,
//!     memory: k::Term<Map<Int, Int>>,
//!     k::cells! { k: KCell(Bus::Read { addr }, _rest @ ..), memory: Cell(memory), .. }: Machine,
//! ) -> k::Term<Int> {
//!     addr
//! }
//! ```
//!
//! is the reference form: the states its `k::cells!` pattern matches under its conditions, with
//! the body as the reason of a `refused` end (a `finished` end has no result and an empty
//! body). `#[k::end(..)]` on a constructor is the shorthand for the states whose main
//! computation cell starts with that constructor, the constructor's term being the reason.
//!
//! Each spelling is lowered here to the items both the macro and the collector then read as
//! they read authored ones, so the two agree on every key by construction:
//!
//! - the function `End<Name>`, total, of sort `Bool`, with one equation per clause whose result
//!   is `true` and an `owise` equation whose result is `false`: it is true exactly on the end's
//!   clauses;
//! - for a `refused` end, the function `End<Name>Reason`, partial, of the reason's sort, with
//!   the same left sides as the clauses.
//!
//! Both functions are marked with the end they belong to ([`EndMarker`]). The compiler emits
//! each as a function of one argument, the whole configuration; in the reference form its
//! equations read the configuration through their function context, and in the constructor
//! form they carry the constructor's pattern as the function's one field, which the compiler
//! places at the head of the definition's main computation cell.
//!
//! Every token this module writes takes the span of an authored token, so a key of a lowered
//! item names the same source range under rustc and in the collector's reparse. The tokens of
//! one keyed node stand at one authored token, or run from an earlier one to a later one, since
//! a key names a node by the range from its first token to its last. The two functions are
//! named at two different tokens, and neither at the name of a constructor the end is declared
//! on: a production is told from the others of its file by where its name stands.

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::{Attribute, FnArg, Ident, ItemFn, ItemStruct, Path, ReturnType};

use crate::attribute::EndMarker;
use crate::surface::{AttributeMacro, helper_entry};
use crate::term_sort::parse_typed_term_sort;
use crate::{FunctionAttribute, KrsSyntax, SyntaxError, SyntaxErrorKind};

/// The payload of `#[k::end(..)]`: one class word.
#[derive(Clone, Debug)]
pub struct EndAttribute {
    word: Ident,
    class: krs_ir::EndClass,
    /// The `end` of the attribute's path, where the attribute is a constructor's helper, which
    /// the constructor's macro reads with its path.
    helper: Option<Ident>,
}

impl EndAttribute {
    /// The authored class word.
    #[must_use]
    pub const fn word(&self) -> &Ident {
        &self.word
    }

    /// The class the word names.
    #[must_use]
    pub const fn class(&self) -> krs_ir::EndClass {
        self.class
    }
}

impl KrsSyntax for EndAttribute {
    /// Parses the class word.
    ///
    /// # Errors
    ///
    /// Rejects anything but exactly one of `finished` and `refused`.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let span = tokens.span();
        let word: Ident = syn::parse2(crate::parse::strip_trailing_comma(tokens))
            .map_err(|_| invalid(CLASS_WORDS, span))?;
        let class = krs_ir::EndClass::from_word(&word.unraw().to_string())
            .ok_or_else(|| invalid(CLASS_WORDS, word.span()))?;
        Ok(Self {
            word,
            class,
            helper: None,
        })
    }
}

impl EndAttribute {
    /// Parses a constructor's `#[k::end(..)]` helper `attribute`.
    ///
    /// # Errors
    ///
    /// The errors of [`KrsSyntax::parse_tokens`], and an attribute without a parenthesized
    /// class word.
    pub fn parse_helper(attribute: &Attribute) -> Result<Self, SyntaxError> {
        let syn::Meta::List(list) = &attribute.meta else {
            return Err(invalid(CLASS_WORDS, attribute.span()));
        };
        let mut end = Self::parse_tokens(list.tokens.clone())?;
        end.helper = attribute
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.clone());
        Ok(end)
    }
}

const CLASS_WORDS: &str = "`#[k::end(..)]` takes one class word, `finished` or `refused`: the classes are a closed set, so that every tool reads an end's class alike";

/// One function a declared end is lowered to.
#[derive(Clone, Debug)]
pub struct EndFunction {
    attribute: FunctionAttribute,
    structure: ItemStruct,
}

impl EndFunction {
    /// The function's attribute, marked with the end it belongs to.
    #[must_use]
    pub const fn attribute(&self) -> &FunctionAttribute {
        &self.attribute
    }

    /// The function's struct.
    #[must_use]
    pub const fn structure(&self) -> &ItemStruct {
        &self.structure
    }
}

/// One equation a declared end is lowered to.
#[derive(Clone, Debug)]
pub struct EndEquation {
    keys: TokenStream,
    item: ItemFn,
}

impl EndEquation {
    /// The equation's `#[k::equation(..)]` keys: `owise` for the equation that makes the
    /// function `false` outside the end's clauses, none otherwise.
    #[must_use]
    pub fn keys(&self) -> TokenStream {
        self.keys.clone()
    }

    /// The equation fn.
    #[must_use]
    pub const fn item(&self) -> &ItemFn {
        &self.item
    }
}

/// How a constructor's application is written as a pattern.
#[derive(Clone, Debug)]
pub enum EndConstructorShape {
    /// `Path`, a unit constructor.
    Unit,
    /// `Path()`, a constructor declared with empty parentheses.
    Call,
    /// `Path { field, .. }`, a record of the named fields.
    Record(Vec<Ident>),
}

/// The functions and equations one declared end stands for.
#[derive(Clone, Debug)]
pub struct EndDeclaration {
    item: Ident,
    functions: Vec<EndFunction>,
    equations: Vec<EndEquation>,
}

impl EndDeclaration {
    /// The end's item name: the fn's name, or [`end_item_name`] of the constructor.
    #[must_use]
    pub const fn item(&self) -> &Ident {
        &self.item
    }

    /// The end's functions: the one that holds on its clauses, then a `refused` end's reason.
    #[must_use]
    pub fn functions(&self) -> &[EndFunction] {
        &self.functions
    }

    /// The end's equations, in the order they are declared.
    #[must_use]
    pub fn equations(&self) -> &[EndEquation] {
        &self.equations
    }

    /// Lowers the reference form: `#[k::end(attribute)]` on the fn `item`, whose remaining
    /// attributes are `item.attrs`. `facade` is the path generated code names the `krs`
    /// facade by.
    ///
    /// # Errors
    ///
    /// Rejects every shape outside the reference form (`krs::syntax::invalid-end`): a class
    /// word other than `finished` or `refused`, a fn whose last parameter is no `k::cells!`
    /// pattern, a `finished` end with a result or a body, a `refused` end without them, and a
    /// generic, `async`, `const`, `unsafe` or `extern` fn.
    pub fn lower_fn(
        attribute: TokenStream,
        item: ItemFn,
        facade: &Path,
    ) -> Result<Self, SyntaxError> {
        let end = EndAttribute::parse_tokens(attribute)?;
        let ItemFn {
            attrs,
            vis,
            sig,
            block,
        } = item;
        validate_signature(&sig)?;
        let context = context_parameter(&sig)?;
        let binders = sig
            .inputs
            .iter()
            .take(sig.inputs.len() - 1)
            .collect::<Vec<_>>();
        let name = sig.ident.clone();
        let word = end.word.span();
        let reason = declared_reason(&end, &sig, &block)?;
        let EndAttributes {
            documentation,
            cfg,
            sentence,
        } = end_attributes(attrs)?;
        // The function that holds stands at the fn's name, the reason's at the class word.
        let names = EndNames::new(&name, name.span(), word);
        let bool_type = bool_type(facade, word);
        let holds = names.holds();
        let marker = |role| EndMarker {
            word: end.word.clone(),
            class: end.class,
            role,
            form: krs_ir::EndForm::Clause,
            item: name.unraw().to_string(),
        };
        let mut functions = vec![end_function(
            function_keys(&vis, word, true),
            &bool_path(facade, word),
            &[],
            syn::parse2(quote_spanned! {holds.span()=>
                #(#documentation)*
                #(#cfg)*
                #[doc(hidden)]
                #[allow(dead_code)]
                #vis struct #holds {}
            })?,
            marker(krs_ir::EndRole::Holds),
        )?];
        let term = at(quote!(#facade::term), name.span());
        let subject = quote_spanned!(name.span()=> #term![#holds()]);
        let mut equations = holds_equations(
            &cfg,
            &sentence,
            (&name, &names.otherwise()),
            (
                &quote!(#(#binders,)* #subject: #bool_type, #context),
                &subject,
            ),
            &bool_type,
            word,
        )?;
        if let Some((result, body)) = reason {
            let sort = parse_typed_term_sort(result.clone())?;
            if sort.is_dynamic() || sort.is_predicate() {
                return Err(invalid(
                    "a `refused` end returns its reason as `k::Term<Sort>` with a sort alias or builtin sort, such as `k::Term<Int>`",
                    result.span(),
                ));
            }
            let reason = names.reason();
            let reason_equation = names.reason_equation();
            // An equation's subject and result are applications of the function, whose element
            // types its declaration states: the equation names only the sort.
            let equation_type = crate::term_sort::without_collection_arguments(&result);
            functions.push(end_function(
                function_keys(&vis, word, false),
                sort.sort(),
                sort.arguments(),
                syn::parse2(quote_spanned! {reason.span()=>
                    #(#cfg)*
                    #[doc(hidden)]
                    #[allow(dead_code)]
                    #vis struct #reason {}
                })?,
                marker(krs_ir::EndRole::Reason),
            )?);
            let reason_term = at(quote!(#facade::term), reason.span());
            let reason_subject = quote_spanned!(reason.span()=> #reason_term![#reason()]);
            equations.push(EndEquation {
                keys: TokenStream::new(),
                item: crate::term::parse_fn_item(quote! {
                    #(#cfg)*
                    #(#sentence)*
                    fn #reason_equation(#(#binders,)* #reason_subject: #equation_type, #context) -> #equation_type #body
                })?,
            });
        }
        Ok(Self {
            item: name,
            functions,
            equations,
        })
    }

    /// Lowers the constructor shorthand: `end` on the constructor named `name`, of visibility
    /// `vis`, whose application is written `application` in the shape `shape` and constructs
    /// the sort `sort`. `cfg` are the constructor's `#[cfg]` attributes and `facade` the path
    /// generated code names the `krs` facade by.
    ///
    /// # Errors
    ///
    /// The errors of parsing the lowered items.
    pub fn lower_constructor(
        end: &EndAttribute,
        (vis, name): (&syn::Visibility, &Ident),
        application: &TokenStream,
        shape: &EndConstructorShape,
        sort: &Path,
        cfg: &[Attribute],
        facade: &Path,
    ) -> Result<Self, SyntaxError> {
        let word = end.word.span();
        let at = name.span();
        let item = Ident::new(&end_item_name(&name.unraw().to_string()), at);
        // The constructor's own production stands at its name, so the function that holds
        // stands at the class word and the reason's at the helper's `end`.
        let names = EndNames::new(&item, word, end.helper.as_ref().map_or(word, Ident::span));
        let bool_type = bool_type(facade, word);
        let spanned_facade = self::at(facade, at);
        let sort_type = quote_spanned!(at=> #spanned_facade::Term<#sort>);
        let holds = names.holds();
        let marker = |role| EndMarker {
            word: end.word.clone(),
            class: end.class,
            role,
            form: krs_ir::EndForm::Constructor,
            item: item.unraw().to_string(),
        };
        let pattern = match shape {
            EndConstructorShape::Unit => application.clone(),
            EndConstructorShape::Call => quote_spanned!(at=> #application()),
            EndConstructorShape::Record(fields) => {
                quote_spanned!(at=> #application { #(#fields),* })
            }
        };
        // Whether the end holds does not depend on the constructor's arguments, which only the
        // reason reads: the equation that says so binds each under a name it does not read
        // (`_addr`), typed by the field as the reason's binder is.
        let any_arguments = match shape {
            EndConstructorShape::Unit | EndConstructorShape::Call => pattern.clone(),
            EndConstructorShape::Record(fields) => {
                let fields = fields.iter().map(|field| {
                    let unread = Ident::new(&format!("_{}", field.unraw()), field.span());
                    quote_spanned!(field.span()=> #field: #unread)
                });
                quote_spanned!(at=> #application { #(#fields),* })
            }
        };
        let mut functions = vec![end_function(
            function_keys(vis, word, true),
            &bool_path(facade, word),
            &[],
            syn::parse2(quote_spanned! {holds.span()=>
                #(#cfg)*
                #[doc(hidden)]
                #[allow(dead_code)]
                #vis struct #holds {
                    #vis head: #sort_type,
                }
            })?,
            marker(krs_ir::EndRole::Holds),
        )?];
        let term = quote_spanned!(at=> #spanned_facade::term);
        // Each pattern's tokens stand at one authored token, or run from an earlier one to a
        // later one: a key names a node by the range from its first token to its last.
        let holds_here = Ident::new(&holds.to_string(), at);
        let subject = quote_spanned!(at=> #term![#holds_here(#any_arguments)]);
        let term_at_word = self::at(quote!(#facade::term), word);
        let mut equations = holds_equations(
            cfg,
            &[],
            (&item, &names.otherwise()),
            (
                &quote!(#subject: #bool_type),
                &quote_spanned!(word=> #term_at_word![#holds(_)]),
            ),
            &bool_type,
            word,
        )?;
        if end.class == krs_ir::EndClass::Refused {
            let reason = names.reason();
            let reason_equation = names.reason_equation();
            let reason_here = Ident::new(&reason.to_string(), at);
            let reason_subject = quote_spanned!(at=> #term![#reason_here(#pattern)]);
            functions.push(end_function(
                function_keys(vis, word, false),
                sort,
                &[],
                syn::parse2(quote_spanned! {reason.span()=>
                    #(#cfg)*
                    #[doc(hidden)]
                    #[allow(dead_code)]
                    #vis struct #reason {
                        #vis head: #sort_type,
                    }
                })?,
                marker(krs_ir::EndRole::Reason),
            )?);
            equations.push(EndEquation {
                keys: TokenStream::new(),
                item: crate::term::parse_fn_item(quote! {
                    #(#cfg)*
                    fn #reason_equation(#reason_subject: #sort_type) -> #sort_type {
                        #pattern
                    }
                })?,
            });
        }
        Ok(Self {
            item,
            functions,
            equations,
        })
    }
}

impl EndDeclaration {
    /// Lowers the shorthand on a `#[k::constructor]` struct `item`, whose attribute names the
    /// sort `sort`.
    ///
    /// # Errors
    ///
    /// Rejects a parametric constructor, and the errors of [`Self::lower_constructor`].
    pub fn lower_struct(
        end: &EndAttribute,
        item: &ItemStruct,
        sort: &Path,
        facade: &Path,
    ) -> Result<Self, SyntaxError> {
        if !item.generics.params.is_empty() {
            return Err(end_placement_error(
                "a parametric constructor, whose sort depends on its arguments: declare the end on a `fn`, for the instance it is about",
                end.word.span(),
            ));
        }
        let shape = match &item.fields {
            syn::Fields::Unit => EndConstructorShape::Unit,
            syn::Fields::Unnamed(_) => EndConstructorShape::Call,
            syn::Fields::Named(fields) => EndConstructorShape::Record(
                fields
                    .named
                    .iter()
                    .filter_map(|field| field.ident.clone())
                    .collect(),
            ),
        };
        let name = &item.ident;
        let cfg = item
            .attrs
            .iter()
            .filter(|attribute| attribute.path().is_ident("cfg"))
            .cloned()
            .collect::<Vec<_>>();
        Self::lower_constructor(
            end,
            (&item.vis, name),
            &quote!(#name),
            &shape,
            sort,
            &cfg,
            facade,
        )
    }
}

/// The `k::cells!` parameter an end's `fn` ends with: the pattern the end's states match.
fn context_parameter(sig: &syn::Signature) -> Result<&FnArg, SyntaxError> {
    sig.inputs
        .last()
        .filter(|argument| crate::is_cells_parameter(argument))
        .ok_or_else(|| {
            invalid(
                "an end is a set of states of the configuration, so the `fn` it is declared on ends with a `k::cells! { .. }` parameter typed by the configuration or by a cell group it holds, which the end's states match; to declare the states whose main computation cell starts with one constructor, write `#[k::end(..)]` on that constructor",
                sig.inputs
                    .last()
                    .map_or_else(|| sig.paren_token.span.join(), Spanned::span),
            )
        })
}

/// The result type and the body of a `refused` end's `fn`, its reason; `None` for a `finished`
/// end, which has neither.
fn declared_reason(
    end: &EndAttribute,
    sig: &syn::Signature,
    block: &syn::Block,
) -> Result<Option<(syn::Type, syn::Block)>, SyntaxError> {
    match (end.class, &sig.output) {
        (krs_ir::EndClass::Finished, ReturnType::Default) => {
            if !block.stmts.is_empty() {
                return Err(invalid(FINISHED_HAS_NO_REASON, block.span()));
            }
            Ok(None)
        }
        (krs_ir::EndClass::Finished, ReturnType::Type(_, result)) => {
            Err(invalid(FINISHED_HAS_NO_REASON, result.span()))
        }
        (krs_ir::EndClass::Refused, ReturnType::Default) => Err(invalid(
            "a `refused` end states its reason: the `fn` returns it, `-> k::Term<Sort>`, and its body is the reason's term over the names the pattern binds",
            sig.ident.span(),
        )),
        (krs_ir::EndClass::Refused, ReturnType::Type(_, result)) => {
            if block.stmts.is_empty() {
                return Err(invalid(
                    "a `refused` end states its reason: the body is the reason's term over the names the pattern binds",
                    block.span(),
                ));
            }
            Ok(Some((result.as_ref().clone(), block.clone())))
        }
    }
}

const FINISHED_HAS_NO_REASON: &str = "a `finished` end has no reason, so its `fn` has no result and an empty body; a `refused` end returns its reason";

/// The two equations of the function that says whether an end holds: `clause`, whose result
/// is `true`, over `parameters` (the fn's parameters, among them `subject`, the function's
/// application), with the attributes `sentence`; and `otherwise`, the `owise` equation whose
/// result is `false`, over `anything`, the function applied to any argument. `word` is the
/// end's class word, at which the results stand.
fn holds_equations(
    cfg: &[Attribute],
    sentence: &[Attribute],
    (clause, otherwise): (&Ident, &Ident),
    (parameters, anything): (&TokenStream, &TokenStream),
    bool_type: &TokenStream,
    word: Span,
) -> Result<Vec<EndEquation>, SyntaxError> {
    let truth = quote_spanned!(word=> true);
    let falsity = quote_spanned!(word=> false);
    Ok(vec![
        EndEquation {
            keys: TokenStream::new(),
            item: crate::term::parse_fn_item(quote! {
                #(#cfg)*
                #(#sentence)*
                fn #clause(#parameters) -> #bool_type {
                    #truth
                }
            })?,
        },
        EndEquation {
            keys: quote_spanned!(word=> owise),
            item: crate::term::parse_fn_item(quote! {
                #(#cfg)*
                fn #otherwise(#anything: #bool_type) -> #bool_type {
                    #falsity
                }
            })?,
        },
    ])
}

/// The item name of the end a constructor's shorthand declares: the constructor's upper camel
/// case name in snake case ([`crate::equation_name`]), the name the reference form's `fn` of
/// the same end takes.
#[must_use]
pub fn end_item_name(constructor: &str) -> String {
    crate::equation_name(constructor)
}

/// The names of the items an end named `item` is lowered to.
///
/// The two functions are named at two different authored tokens: a function's declaration is
/// told from every other production of the file by where its name stands, and an end declares
/// up to two.
struct EndNames {
    item: Ident,
    camel: String,
    holds_at: Span,
    reason_at: Span,
}

impl EndNames {
    fn new(item: &Ident, holds_at: Span, reason_at: Span) -> Self {
        let camel = item
            .unraw()
            .to_string()
            .split('_')
            .filter(|word| !word.is_empty())
            .map(|word| {
                let mut characters = word.chars();
                characters
                    .next()
                    .map(|first| first.to_uppercase().chain(characters).collect::<String>())
                    .unwrap_or_default()
            })
            .collect::<String>();
        Self {
            item: item.clone(),
            camel,
            holds_at,
            reason_at,
        }
    }

    fn ident(&self, name: &str) -> Ident {
        Ident::new(name, self.item.span())
    }

    /// `End<Name>`: the function that is true exactly on the end's clauses.
    fn holds(&self) -> Ident {
        Ident::new(&format!("End{}", self.camel), self.holds_at)
    }

    /// `End<Name>Reason`: the function that gives a refused end's reason.
    fn reason(&self) -> Ident {
        Ident::new(&format!("End{}Reason", self.camel), self.reason_at)
    }

    /// `<name>_otherwise`: the equation that makes the end `false` outside its clauses.
    fn otherwise(&self) -> Ident {
        self.ident(&format!("{}_otherwise", self.item.unraw()))
    }

    /// `<name>_reason`: the equation that states the reason.
    fn reason_equation(&self) -> Ident {
        self.ident(&format!("{}_reason", self.item.unraw()))
    }
}

/// The `#[k::function]` keys of an end's function: its totality, and `internal` where the
/// declaring item is `pub`, since the function is no program syntax; an item that is not `pub`
/// declares a production no program can name already.
fn function_keys(vis: &syn::Visibility, span: Span, total: bool) -> TokenStream {
    let totality = if total {
        quote_spanned!(span=> total)
    } else {
        quote_spanned!(span=> partial)
    };
    if matches!(vis, syn::Visibility::Public(_)) {
        quote_spanned!(span=> #totality, internal)
    } else {
        totality
    }
}

/// `tokens` with every token, and every delimiter, at `span`: the facade path is written by
/// the host (rustc's expansion or the collector's reparse), at a span of the host's, and a key
/// names a node by its tokens' positions.
pub(crate) fn at(tokens: impl quote::ToTokens, span: Span) -> TokenStream {
    tokens
        .into_token_stream()
        .into_iter()
        .map(|mut token| {
            if let proc_macro2::TokenTree::Group(group) = &token {
                let mut inner =
                    proc_macro2::Group::new(group.delimiter(), at(group.stream(), span));
                inner.set_span(span);
                token = proc_macro2::TokenTree::Group(inner);
            } else {
                token.set_span(span);
            }
            token
        })
        .collect()
}

fn bool_path(facade: &Path, span: Span) -> Path {
    let facade = at(facade, span);
    syn::parse_quote_spanned!(span=> #facade::builtin::Bool)
}

fn bool_type(facade: &Path, span: Span) -> TokenStream {
    let facade = at(facade, span);
    quote_spanned!(span=> #facade::Term<#facade::builtin::Bool>)
}

/// One function of an end: `keys` are its `#[k::function]` keys, `sort` its result sort.
fn end_function(
    keys: TokenStream,
    sort: &Path,
    sort_arguments: &[crate::SortArgument],
    structure: ItemStruct,
    marker: EndMarker,
) -> Result<EndFunction, SyntaxError> {
    let mut attribute = FunctionAttribute::parse_shorthand_tokens(keys, sort, sort_arguments)?;
    let declaration = crate::ConstructorDeclaration::from_item(structure.clone())?;
    attribute.complete_default_syntax(&declaration)?;
    attribute.production().validate_declaration(&declaration)?;
    Ok(EndFunction {
        attribute: attribute.with_end(marker)?,
        structure,
    })
}

/// An end fn's attributes, sorted by the items they go to.
struct EndAttributes {
    /// Documentation, which the function that holds on the end's clauses carries.
    documentation: Vec<Attribute>,
    /// `#[cfg]`, which every item carries.
    cfg: Vec<Attribute>,
    /// `#[k::requires]` and every remaining attribute, which each clause equation carries.
    sentence: Vec<Attribute>,
}

fn end_attributes(attrs: Vec<Attribute>) -> Result<EndAttributes, SyntaxError> {
    let mut sorted = EndAttributes {
        documentation: Vec::new(),
        cfg: Vec::new(),
        sentence: Vec::new(),
    };
    for attribute in attrs {
        match helper_entry(attribute.path()) {
            Some(AttributeMacro::Requires) => sorted.sentence.push(attribute),
            Some(entry) => {
                return Err(invalid(
                    &format!(
                        "`#[k::{}]` does not apply to a declared end, which states a set of states and, for `refused`, a reason: its conditions are `#[k::requires(..)]`",
                        entry.name()
                    ),
                    attribute.span(),
                ));
            }
            None if attribute.path().is_ident("cfg") => sorted.cfg.push(attribute),
            None if attribute.path().is_ident("doc") => sorted.documentation.push(attribute),
            None => sorted.sentence.push(attribute),
        }
    }
    Ok(sorted)
}

fn validate_signature(sig: &syn::Signature) -> Result<(), SyntaxError> {
    let refused = [
        sig.constness.map(|token| token.span()),
        sig.asyncness.map(|token| token.span()),
        sig.unsafety.map(|token| token.span()),
        sig.abi.as_ref().map(Spanned::span),
        (!sig.generics.params.is_empty()).then(|| sig.generics.span()),
        sig.generics.where_clause.as_ref().map(Spanned::span),
        sig.variadic.as_ref().map(Spanned::span),
    ]
    .into_iter()
    .flatten()
    .next();
    if let Some(span) = refused {
        return Err(invalid(
            "the `fn` of a declared end is a plain `fn`: its parameters are the names its pattern binds, then the `k::cells!` pattern",
            span,
        ));
    }
    if let Some(receiver) = sig.inputs.iter().find_map(|argument| match argument {
        FnArg::Receiver(receiver) => Some(receiver),
        FnArg::Typed(_) => None,
    }) {
        return Err(invalid(
            "the `fn` of a declared end is a free `fn`, without `self`",
            receiver.span(),
        ));
    }
    Ok(())
}

/// Why `#[k::end(..)]` does not apply where it was written.
#[must_use]
pub fn end_placement_reason(found: &str) -> String {
    format!(
        "`#[k::end(..)]` declares an end on a `fn` whose last parameter is a `k::cells!` pattern, or on a constructor (a `#[k::constructor]` struct or a variant of a `#[k::constructors]` enum), not on {found}"
    )
}

fn invalid(reason: &str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidEnd {
            reason: reason.to_owned(),
        },
        span,
    )
}

/// The refusal of `#[k::end(..)]` on `found`, at `span`.
#[must_use]
pub fn end_placement_error(found: &str, span: Span) -> SyntaxError {
    invalid(&end_placement_reason(found), span)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn facade() -> Path {
        syn::parse_quote!(::k)
    }

    fn lower(attribute: &str, item: &str) -> Result<EndDeclaration, SyntaxError> {
        EndDeclaration::lower_fn(
            attribute.parse().expect("attribute tokens"),
            crate::term::parse_fn_item(item.parse().expect("item tokens")).expect("a fn"),
            &facade(),
        )
    }

    fn names(declaration: &EndDeclaration) -> (Vec<String>, Vec<String>) {
        (
            declaration
                .functions()
                .iter()
                .map(|function| function.structure().ident.to_string())
                .collect(),
            declaration
                .equations()
                .iter()
                .map(|equation| equation.item().sig.ident.to_string())
                .collect(),
        )
    }

    #[test]
    fn a_finished_end_is_one_total_function_with_its_clause_and_its_otherwise() {
        let declaration = lower(
            "finished",
            "fn locked(k::cells! { k: KCell(Step::Locked, _rest @ ..), .. }: Cpu) {}",
        )
        .unwrap();
        assert_eq!(
            names(&declaration),
            (
                vec!["EndLocked".to_owned()],
                vec!["locked".to_owned(), "locked_otherwise".to_owned()]
            )
        );
        let function = &declaration.functions()[0];
        assert!(function.attribute().is_total());
        let end = function.attribute().end().unwrap();
        assert_eq!(end.class, krs_ir::EndClass::Finished);
        assert_eq!(end.role, krs_ir::EndRole::Holds);
        assert_eq!(end.form, krs_ir::EndForm::Clause);
        assert_eq!(end.item, "locked");
        assert_eq!(declaration.equations()[1].keys().to_string(), "owise");
    }

    #[test]
    fn a_refused_end_has_a_partial_reason_function_with_the_clause_left_side() {
        let declaration = lower(
            "refused",
            "#[k::requires(int::lt(addr, 0))] fn unmapped_read(addr: k::Term<Int>, k::cells! { k: KCell(Read { addr }, _rest @ ..), .. }: Machine) -> k::Term<Int> { addr }",
        )
        .unwrap();
        assert_eq!(
            names(&declaration),
            (
                vec![
                    "EndUnmappedRead".to_owned(),
                    "EndUnmappedReadReason".to_owned()
                ],
                vec![
                    "unmapped_read".to_owned(),
                    "unmapped_read_otherwise".to_owned(),
                    "unmapped_read_reason".to_owned()
                ]
            )
        );
        let reason = &declaration.functions()[1];
        assert!(!reason.attribute().is_total());
        assert_eq!(
            reason.attribute().end().unwrap().role,
            krs_ir::EndRole::Reason
        );
        // The condition guards the clause and the reason, and not the otherwise equation.
        let guarded = declaration
            .equations()
            .iter()
            .map(|equation| equation.item().attrs.len())
            .collect::<Vec<_>>();
        assert_eq!(guarded, [1, 0, 1]);
    }

    #[test]
    fn shapes_outside_the_reference_form_are_refused() {
        for (attribute, item) in [
            ("stuck", "fn a(k::cells! { .. }: M) {}"),
            ("finished, refused", "fn a(k::cells! { .. }: M) {}"),
            ("finished", "fn a(x: k::Term<Int>) {}"),
            (
                "finished",
                "fn a(k::cells! { .. }: M) -> k::Term<Int> { 1 }",
            ),
            ("refused", "fn a(k::cells! { .. }: M) {}"),
            ("finished", "fn a<T>(k::cells! { .. }: M) {}"),
            (
                "finished",
                "#[k::ensures(true)] fn a(k::cells! { .. }: M) {}",
            ),
        ] {
            let error = lower(attribute, item).unwrap_err();
            assert!(
                matches!(error.kind(), SyntaxErrorKind::InvalidEnd { .. }),
                "{attribute} {item}: {error}"
            );
        }
    }

    #[test]
    fn a_constructor_shorthand_takes_the_item_name_its_reference_fn_has() {
        let end = EndAttribute::parse_tokens("refused".parse().unwrap()).unwrap();
        let declaration = EndDeclaration::lower_constructor(
            &end,
            (&syn::Visibility::Inherited, &syn::parse_quote!(BadRead)),
            &quote!(BusOp::BadRead),
            &EndConstructorShape::Record(vec![syn::parse_quote!(addr)]),
            &syn::parse_quote!(Bus),
            &[],
            &facade(),
        )
        .unwrap();
        assert_eq!(declaration.item().to_string(), "bad_read");
        assert_eq!(
            names(&declaration),
            (
                vec!["EndBadRead".to_owned(), "EndBadReadReason".to_owned()],
                vec![
                    "bad_read".to_owned(),
                    "bad_read_otherwise".to_owned(),
                    "bad_read_reason".to_owned()
                ]
            )
        );
        assert_eq!(
            declaration.functions()[0].attribute().end().unwrap().form,
            krs_ir::EndForm::Constructor
        );
    }
}
