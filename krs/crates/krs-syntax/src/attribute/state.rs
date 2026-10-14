use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::{Expr, Ident, LitStr, Token};

use crate::parse::{KrsSyntax, ParseError, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

use super::value::{parse_empty_attribute, parse_empty_tokens, parse_string_value};

/// Generated-top or explicit named-root configuration metadata.
#[derive(Clone, Debug)]
pub struct ConfigurationAttribute {
    root: Option<LitStr>,
}

impl ConfigurationAttribute {
    /// Returns the authored K root-cell name literal when a named root is selected.
    #[must_use]
    pub const fn root(&self) -> Option<&LitStr> {
        self.root.as_ref()
    }

    /// Returns the optional authored root without assuming named-root policy.
    #[must_use]
    pub const fn optional_root(&self) -> Option<&LitStr> {
        self.root.as_ref()
    }

    /// Whether the frontend should use K's generated top cell.
    #[must_use]
    pub const fn is_generated_top(&self) -> bool {
        self.root.is_none()
    }

    /// Returns the canonical root-name anchor.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the parsed literal emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.root
            .as_ref()
            .map(|root| {
                TokenRange::for_tokens(root).map(|range| {
                    vec![ProvenanceAnchor::new(
                        ProvenanceRole::ConfigurationRoot,
                        0,
                        range,
                    )]
                })
            })
            .transpose()
            .map(Option::unwrap_or_default)
    }
}

/// Classified payload of `#[k::cell(...)]`.
#[derive(Clone, Debug, Default)]
pub struct CellAttributePayload {
    name: Option<LitStr>,
    color: Option<LitStr>,
    multiplicity: Option<LitStr>,
    cell_type: Option<LitStr>,
    nested: bool,
    stream: Option<LitStr>,
    exit: Option<Ident>,
    initial: Option<Ident>,
}

impl CellAttributePayload {
    /// Optional exact emitted cell name.
    #[must_use]
    pub const fn name(&self) -> Option<&LitStr> {
        self.name.as_ref()
    }

    /// Optional target-neutral cell color.
    #[must_use]
    pub const fn color(&self) -> Option<&LitStr> {
        self.color.as_ref()
    }

    /// Optional K cell multiplicity.
    #[must_use]
    pub const fn multiplicity(&self) -> Option<&LitStr> {
        self.multiplicity.as_ref()
    }

    /// Optional collection type for a repeated cell.
    #[must_use]
    pub const fn cell_type(&self) -> Option<&LitStr> {
        self.cell_type.as_ref()
    }

    /// Whether this helper explicitly classifies a plain path as a nested declaration.
    #[must_use]
    pub const fn is_nested(&self) -> bool {
        self.nested
    }

    /// Optional K console stream, `"stdin"` or `"stdout"`.
    #[must_use]
    pub const fn stream(&self) -> Option<&LitStr> {
        self.stream.as_ref()
    }

    /// The bare `exit` flag, when the cell's final Int value is the process exit status.
    #[must_use]
    pub const fn exit(&self) -> Option<&Ident> {
        self.exit.as_ref()
    }

    /// The bare `initial` flag: an optional or collection cell that starts
    /// present, built from its template (KF-023).
    #[must_use]
    pub const fn initial(&self) -> Option<&Ident> {
        self.initial.as_ref()
    }

    /// Returns exact value anchors in stable name, color, multiplicity, type, stream, exit,
    /// initial order.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if an authored literal has no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(6);
        if let Some(name) = &self.name {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellName,
                0,
                TokenRange::for_tokens(name)?,
            ));
        }
        if let Some(color) = &self.color {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellColor,
                0,
                TokenRange::for_tokens(color)?,
            ));
        }
        if let Some(multiplicity) = &self.multiplicity {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellMultiplicity,
                0,
                TokenRange::for_tokens(multiplicity)?,
            ));
        }
        if let Some(cell_type) = &self.cell_type {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellType,
                0,
                TokenRange::for_tokens(cell_type)?,
            ));
        }
        if let Some(stream) = &self.stream {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellStream,
                0,
                TokenRange::for_tokens(stream)?,
            ));
        }
        if let Some(exit) = &self.exit {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellExit,
                0,
                TokenRange::for_tokens(exit)?,
            ));
        }
        if let Some(initial) = &self.initial {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellInitial,
                0,
                TokenRange::for_tokens(initial)?,
            ));
        }
        Ok(anchors)
    }
}

impl Parse for ConfigurationAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_configuration_stream(input).map_err(syn::Error::from)
    }
}

/// Validated empty payload of `#[k::init]`.
#[derive(Clone, Copy, Debug, Default)]
pub struct InitAttribute;

impl Parse for InitAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_empty_attribute(input, "init")?;
        Ok(Self)
    }
}

impl KrsSyntax for ConfigurationAttribute {
    /// Parses the generated-top or named-root configuration attribute payload.
    ///
    /// # Errors
    ///
    /// Rejects unknown, repeated, empty, or non-string `root` arguments at their own tokens.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_configuration_stream)
    }
}

impl KrsSyntax for CellAttributePayload {
    /// Parses a fixed-cell helper payload.
    ///
    /// # Errors
    ///
    /// Rejects unknown/repeated keys and empty or non-string values locally.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_cell_stream)
    }
}

impl KrsSyntax for InitAttribute {
    /// Parses the empty initializer attribute payload.
    ///
    /// # Errors
    ///
    /// Rejects any payload at its first token.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        parse_empty_tokens(tokens, "init").map(|()| InitAttribute)
    }
}

fn parse_configuration_stream(
    input: ParseStream<'_>,
) -> Result<ConfigurationAttribute, ParseError> {
    let mut root = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "root" if root.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "root" },
                    key.span(),
                )
                .into());
            }
            "root" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        let literal = parse_string_value("root", value)?;
        if literal.value().is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidArgumentValue {
                    name: "root",
                    expected: "a nonempty Rust string literal",
                },
                literal.span(),
            )
            .into());
        }
        root = Some(literal);
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }
    Ok(ConfigurationAttribute { root })
}

#[expect(
    clippy::too_many_lines,
    reason = "Keeps the closed cell-attribute grammar in one ordered parser."
)]
fn parse_cell_stream(input: ParseStream<'_>) -> Result<CellAttributePayload, ParseError> {
    let mut name = None;
    let mut color = None;
    let mut multiplicity = None;
    let mut cell_type = None;
    let mut nested = false;
    let mut stream = None;
    let mut exit = None;
    let mut initial = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        if key_name == "exit" || key_name == "initial" {
            let (slot, name, reason): (&mut Option<Ident>, &'static str, &'static str) =
                if key_name == "exit" {
                    (&mut exit, "exit", "exit takes no value")
                } else {
                    (&mut initial, "initial", "initial takes no value")
                };
            if slot.is_some() {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name },
                    key.span(),
                )
                .into());
            }
            if input.peek(Token![=]) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidCellAttribute { reason },
                    input.parse::<Token![=]>()?.span,
                )
                .into());
            }
            *slot = Some(key);
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
        if key_name == "nested" {
            if nested {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "nested" },
                    key.span(),
                )
                .into());
            }
            nested = true;
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
        let (slot, argument_name) = match key_name.as_str() {
            "name" => (&mut name, "name"),
            "color" => (&mut color, "color"),
            "multiplicity" => (&mut multiplicity, "multiplicity"),
            "cell_type" => (&mut cell_type, "cell_type"),
            "stream" => (&mut stream, "stream"),
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        };
        if slot.is_some() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::DuplicateArgument {
                    name: argument_name,
                },
                key.span(),
            )
            .into());
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        let literal = parse_string_value(argument_name, value)?;
        if literal.value().trim().is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidCellAttribute {
                    reason: "cell metadata values must be nonempty strings",
                },
                literal.span(),
            )
            .into());
        }
        *slot = Some(literal);
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }
    validate_multiplicity(
        multiplicity.as_ref(),
        cell_type.as_ref(),
        nested,
        initial.as_ref(),
    )?;
    if let Some(value) = &stream
        && !matches!(value.value().as_str(), "stdin" | "stdout")
    {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "K supports stream=\"stdin\" and \"stdout\"",
            },
            value.span(),
        )
        .into());
    }
    Ok(CellAttributePayload {
        name,
        color,
        multiplicity,
        cell_type,
        nested,
        stream,
        exit,
        initial,
    })
}

/// The multiplicity keys (KF-023): `multiplicity` is `"?"` or `"*"`; a `*`
/// collection names its `cell_type` (Set, Map, or List; K's cell bags are
/// unsupported by its LLVM and Haskell backends; upstream k/cell-bags-unsupported,
/// reviewed, not a request) and is `nested`;
/// `cell_type` belongs to a `*` cell and `initial` to a `?` or `*` cell.
fn validate_multiplicity(
    multiplicity: Option<&LitStr>,
    cell_type: Option<&LitStr>,
    nested: bool,
    initial: Option<&Ident>,
) -> Result<(), ParseError> {
    let invalid = |reason: &'static str, span: proc_macro2::Span| -> ParseError {
        SyntaxError::new(SyntaxErrorKind::InvalidCellAttribute { reason }, span).into()
    };
    let star = match multiplicity {
        None => false,
        Some(value) => match value.value().as_str() {
            "*" => true,
            "?" => false,
            _ => {
                return Err(invalid(
                    "cell `multiplicity` is \"?\" (an optional cell) or \"*\" (a cell collection)",
                    value.span(),
                ));
            }
        },
    };
    if let Some(value) = cell_type {
        // upstream k/cell-bags-unsupported (reviewed, not a request).
        if value.value() == "Bag" {
            return Err(invalid(
                "cell bags are unsupported by K's LLVM and Haskell backends; use cell_type = \"Set\", \"Map\", or \"List\"",
                value.span(),
            ));
        }
        if !matches!(value.value().as_str(), "List" | "Map" | "Set") {
            return Err(invalid(
                "a collection's `cell_type` is \"Set\", \"Map\", or \"List\"",
                value.span(),
            ));
        }
        if !star {
            return Err(invalid(
                "`cell_type` requires `multiplicity = \"*\"`",
                value.span(),
            ));
        }
    }
    if let Some(value) = multiplicity
        && star
    {
        if cell_type.is_none() {
            return Err(invalid(
                "a `multiplicity = \"*\"` collection needs `cell_type = \"Set\"`, `\"Map\"`, or `\"List\"`",
                value.span(),
            ));
        }
        if !nested {
            return Err(invalid(
                "a `multiplicity = \"*\"` collection holds whole cells: add `nested` and declare its instance as a `#[k::cell]` struct",
                value.span(),
            ));
        }
    }
    if let Some(flag) = initial
        && multiplicity.is_none()
    {
        return Err(invalid(
            "`initial` belongs to an optional (`multiplicity = \"?\"`) or collection (`multiplicity = \"*\"`) cell",
            flag.span(),
        ));
    }
    Ok(())
}
