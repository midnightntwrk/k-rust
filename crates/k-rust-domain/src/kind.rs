//! The kind of a sort's domain values, read from the sort's declaration, and the width of a
//! machine-integer sort, read from its KORE name.

/// The KORE name of the sort of K's integers, `Int`.
pub const INT_SORT: &str = "SortInt";
/// The KORE name of the sort of K's Booleans, `Bool`.
pub const BOOL_SORT: &str = "SortBool";
/// The KORE name of the sort of K's strings, `String`.
pub const STRING_SORT: &str = "SortString";
/// The KORE name of the sort of K's byte sequences, `Bytes`.
pub const BYTES_SORT: &str = "SortBytes";
/// The KORE name of the sort of K's floating-point numbers, `Float`.
pub const FLOAT_SORT: &str = "SortFloat";
/// The KORE name of the sort constructor of K's machine integers, `MInt{W}`.
pub const MINT_SORT: &str = "SortMInt";

/// A KORE sort as a domain value reads it: the application of a named sort constructor to
/// argument sorts, or a sort variable.
pub trait DomainSort: Sized {
    /// The constructor's KORE name and the arguments when the sort is an application; `None`
    /// for a sort variable.
    fn as_application(&self) -> Option<(&str, &[Self])>;

    /// True when a sort variable occurs anywhere in the sort.
    fn has_variable(&self) -> bool {
        self.as_application()
            .is_none_or(|(_, arguments)| arguments.iter().any(DomainSort::has_variable))
    }
}

/// True for the nullary application of the KORE name `name`.
pub(crate) fn is_nullary<S: DomainSort>(sort: &S, name: &str) -> bool {
    matches!(sort.as_application(), Some((found, [])) if found == name)
}

/// The width of a machine-integer sort `SortMInt{A}`, the KORE head of K's one parametric builtin
/// sort `MInt{W}`: the natural number its argument names. The frontend declares a width `W` as
/// the sort `Sort<digits>{}` (`nat{}("<digits>")`), so the width is read from that name.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MIntWidth {
    /// The argument `Sort<digits>{}` names this many bits (leading zeros allowed: `Sort08` is 8).
    Bits(u64),
    /// The argument names a numeral beyond `u64`.
    Unrepresentable,
    /// A closed argument that names no numeral (a declared `MInt{Foo}`): no text is a literal
    /// of the sort.
    NoWidth,
}

/// How the domain values of a sort denote its elements, which fixes their canonical text:
/// equal elements of one sort have one text, so every comparison that reads domain values by
/// text (matching, unification, `KEQUAL`, apartness, hashing) compares elements.
///
/// With a definition at hand the kind comes from the sort's hook
/// (the backend's `BackendDefinition::domain_kind`), never from its name.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DomainKind {
    /// The integers (`INT.Int`) in decimal: the canonical text has no `+` and no leading zero.
    Int,
    /// The `2^W` bit patterns of a machine integer (`MINT.MInt`) of this width: a literal
    /// denotes its signed decimal reduced modulo `2^W`, and the canonical text is that unsigned
    /// residue, `p`, and the digits of the sort's width argument.
    MInt(MIntWidth),
    /// The Booleans (`BOOL.Bool`): the texts `true` and `false`, each its own canonical text.
    Bool,
    /// The strings (`STRING.String`): sequences of code points, stored as their UTF-8, so that
    /// each string has one payload (`"\x41"`, `"\u0041"` and `"A"` are one value).
    String,
    /// The byte sequences (`BYTES.Bytes`): stored one byte per code point at `SortBytes` and as
    /// the UTF-8 of code points at any other sort (`LiteralEncoding::of_domain_value`, read by
    /// the sort's KORE name on every route). A code point above U+00FF names no byte.
    Bytes,
    /// The floating-point numbers of every format (`FLOAT.Float`): a literal denotes its decimal
    /// rounded to nearest, ties to even by k-rust's reading of FLOAT rounding
    /// (`docs/compatibility.md`, "Backend scope"), in the format its suffix names, and the
    /// canonical text is the one text of that value ([`crate::canonical_float_text`]):
    /// the hooks' text for binary32 and binary64, the exact decimal for every other format.
    Float,
    /// Every other sort with domain values (an unhooked token sort, `Id`, an unhooked
    /// `SortFloat`, ...): a text is its own value.
    Token,
}

impl DomainKind {
    /// The kind of the domain values of `sort` in a definition that declares the sort's head
    /// with the `hasDomainValues` attribute exactly when `has_domain_values` holds, and with the
    /// hook `hook`. This is the rule the backend's `BackendDefinition::domain_kind`
    /// states, and every reader of a definition's declarations applies it to the facts it has
    /// (the backend's `DeclarationFacts`).
    ///
    /// A sort without domain values has no kind, and neither has a sort hooked `MINT.MInt` that
    /// names no width or whose width argument is still a sort variable.
    pub fn of_declared_sort<S: DomainSort>(
        sort: &S,
        has_domain_values: bool,
        hook: Option<&str>,
    ) -> Option<Self> {
        if !has_domain_values {
            return None;
        }
        if is_nullary(sort, INT_SORT) {
            return Some(Self::Int);
        }
        if is_nullary(sort, BOOL_SORT) {
            return Some(Self::Bool);
        }
        Some(match hook {
            Some("INT.Int") => Self::Int,
            Some("BOOL.Bool") => Self::Bool,
            Some("STRING.String") => Self::String,
            Some("BYTES.Bytes") => Self::Bytes,
            Some("FLOAT.Float") => Self::Float,
            Some("MINT.MInt") => match mint_width(sort)? {
                MIntWidth::NoWidth => return None,
                width => Self::MInt(width),
            },
            _ => Self::Token,
        })
    }

    /// Whether two texts can name one element of a sort of this kind, so that its canonical text
    /// is not always the text as written (`canonical_text`): `07` and `7` are one integer,
    /// `01p8` and `1p8` one machine integer, `1.0` and `1.00` one Float. A Boolean's, a
    /// `String`'s and a `Bytes` value's text is its one text, as a token's is.
    pub fn identifies_texts(self) -> bool {
        match self {
            Self::Int | Self::MInt(_) | Self::Float => true,
            Self::Bool | Self::String | Self::Bytes | Self::Token => false,
        }
    }

    /// The kind the builtin hooks' argument readers take a domain value of `sort` to have,
    /// judging by the sort's name alone: `SortInt`, `SortBool`, `SortString`, `SortBytes` and
    /// `SortFloat` their builtins' kinds, and `SortMInt{Sort<digits>{}}` the machine integers of
    /// that width. `None` for every other sort, a `SortMInt` whose argument names no numeral or
    /// is still a sort variable included: no reader reads a literal of one.
    ///
    /// It is the kind the definition gives the sort only where the definition declares the
    /// sort with its builtin's hook ([`Self::of_declared_sort`]; `SortInt` and `SortBool` take
    /// their kinds from their names). Where this kind identifies texts
    /// ([`Self::identifies_texts`]) and the definition gives the sort another, the evaluation
    /// entry refuses the application before any reader sees the argument
    /// (the backend's `misread_by_name`).
    pub fn named<S: DomainSort>(sort: &S) -> Option<Self> {
        let (name, arguments) = sort.as_application()?;
        if !arguments.is_empty() {
            return match mint_width(sort)? {
                MIntWidth::NoWidth => None,
                width => Some(Self::MInt(width)),
            };
        }
        [
            (INT_SORT, Self::Int),
            (BOOL_SORT, Self::Bool),
            (STRING_SORT, Self::String),
            (BYTES_SORT, Self::Bytes),
            (FLOAT_SORT, Self::Float),
        ]
        .into_iter()
        .find_map(|(builtin, kind)| (name == builtin).then_some(kind))
    }
}

/// The width of `sort` when it is a machine-integer sort `SortMInt{A}`: `Bits(n)` when `A` is
/// `Sort<digits>{}` naming `n`, `Unrepresentable` when those digits exceed `u64`, and `NoWidth`
/// for any other closed `A` (a declared `MInt{Foo}`). `None` when `A` holds a sort variable,
/// whose width is not fixed yet, and for every other sort.
pub fn mint_width<S: DomainSort>(sort: &S) -> Option<MIntWidth> {
    let (name, arguments) = sort.as_application()?;
    let [argument] = arguments else {
        return None;
    };
    if name != MINT_SORT || argument.has_variable() {
        return None;
    }
    Some(
        numeral_sort_digits(argument).map_or(MIntWidth::NoWidth, |digits| {
            digits
                .parse::<u64>()
                .map_or(MIntWidth::Unrepresentable, MIntWidth::Bits)
        }),
    )
}

/// The digits of the width argument of a machine-integer sort `SortMInt{Sort<digits>{}}`, as
/// written in the sort's name.
pub fn mint_width_digits<S: DomainSort>(sort: &S) -> Option<&str> {
    match sort.as_application()? {
        (name, [argument]) if name == MINT_SORT => numeral_sort_digits(argument),
        _ => None,
    }
}

/// The digits `d` of a nullary sort `Sort<d>{}`, the KORE declaration of a numeral.
fn numeral_sort_digits<S: DomainSort>(sort: &S) -> Option<&str> {
    let (name, arguments) = sort.as_application()?;
    let digits = name.strip_prefix("Sort")?;
    (arguments.is_empty() && !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()))
        .then_some(digits)
}
