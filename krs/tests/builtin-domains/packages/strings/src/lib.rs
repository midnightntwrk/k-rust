//! String literals and STRING operations (KF-008).
//!
//! A Rust string literal is a K `String` token in equations, readable patterns,
//! results, and programs. K strings hold code points in U+0000..=U+00FF, so
//! `"\u{c1}"` in Rust is `"\xc1"` in K. Import the module, not the marker:
//! `string::String` leaves the standard `String` unshadowed.

use k::builtin::{Bool, Bytes, Int, KSequence, bool, bytes, string};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Bytes, Int, string::String;
}

/// A greeting whose argument is matched as a string literal.
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Greet))]
#[rustfmt::skip]
pub enum Greeting {
    #[k::syntax("greet({name})")] #[k::strict]
    Greet { name: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Exp;
    use Greeting::*;

    greet_world: Greet("world")  => "hello, world";
    greet_latin: Greet("\u{c1}") => "\u{c1}!";
}

/// The `msg` example of K's tutorial (`1_basic/10`): two concatenations.
#[k::function(total, sort = string::String, syntax = "msg({s})")]
pub struct Msg {
    pub s: Term<string::String>,
}

#[k::equation]
fn msg(k::term![Msg(s)]: Term<string::String>) -> Term<string::String> {
    string::concat(
        string::concat("The string you provided: ", s),
        "\nHave a nice day!",
    )
}

/// `string::length`, the number of code points.
#[k::function(total, sort = Int, syntax = "length({s})")]
pub struct Length {
    pub s: Term<string::String>,
}

#[k::equation]
fn length(k::term![Length(s)]: Term<Int>) -> Term<Int> {
    string::length(s)
}

/// `string::substr` over a half-open range.
#[k::function(total, sort = string::String, syntax = "substr({s}, {start}, {end})")]
pub struct Substr {
    pub s: Term<string::String>,
    pub start: Term<Int>,
    pub end: Term<Int>,
}

#[k::equation]
fn substr(k::term![Substr(s, start, end)]: Term<string::String>) -> Term<string::String> {
    string::substr(s, start, end)
}

/// `string::find`, `-1` when the needle is absent.
#[k::function(partial, sort = Int, syntax = "find({haystack}, {needle}, {from})")]
pub struct Find {
    pub haystack: Term<string::String>,
    pub needle: Term<string::String>,
    pub from: Term<Int>,
}

#[k::equation]
fn find(k::term![Find(haystack, needle, from)]: Term<Int>) -> Term<Int> {
    string::find(haystack, needle, from)
}

/// `string::chr`.
#[k::function(partial, sort = string::String, syntax = "chr({code})")]
pub struct Chr {
    pub code: Term<Int>,
}

#[k::equation]
fn chr(k::term![Chr(code)]: Term<string::String>) -> Term<string::String> {
    string::chr(code)
}

/// `string::ord`.
#[k::function(partial, sort = Int, syntax = "ord({s})")]
pub struct Ordinal {
    pub s: Term<string::String>,
}

#[k::equation]
fn ord(k::term![Ordinal(s)]: Term<Int>) -> Term<Int> {
    string::ord(s)
}

/// `string::from_int`.
#[k::function(total, sort = string::String, syntax = "fromInt({i})")]
pub struct FromInt {
    pub i: Term<Int>,
}

#[k::equation]
fn from_int(k::term![FromInt(i)]: Term<string::String>) -> Term<string::String> {
    string::from_int(i)
}

/// `string::to_int`.
#[k::function(partial, sort = Int, syntax = "toInt({s})")]
pub struct ToInt {
    pub s: Term<string::String>,
}

#[k::equation]
fn to_int(k::term![ToInt(s)]: Term<Int>) -> Term<Int> {
    string::to_int(s)
}

/// `string::from_bool`.
#[k::function(total, sort = string::String, syntax = "fromBool({b})")]
pub struct FromBool {
    pub b: Term<Bool>,
}

#[k::equation]
fn from_bool(k::term![FromBool(b)]: Term<string::String>) -> Term<string::String> {
    string::from_bool(b)
}

/// `string::to_bool`.
#[k::function(partial, sort = Bool, syntax = "toBool({s})")]
pub struct ToBool {
    pub s: Term<string::String>,
}

#[k::equation]
fn to_bool(k::term![ToBool(s)]: Term<Bool>) -> Term<Bool> {
    string::to_bool(s)
}

/// `string::eq` and `string::ne`.
#[k::function(total, sort = Bool, syntax = "same({a}, {b})")]
pub struct Same {
    pub a: Term<string::String>,
    pub b: Term<string::String>,
}

#[k::equation]
fn same(k::term![Same(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::and(string::eq(a, b), string::ne(a, "never"))
}

/// `string::lt`, `le`, `gt`, and `ge`: whether `a` sorts strictly before `b`.
#[k::function(total, sort = Bool, syntax = "before({a}, {b})")]
pub struct Before {
    pub a: Term<string::String>,
    pub b: Term<string::String>,
}

#[k::equation]
fn before(k::term![Before(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::and(
        bool::and(string::lt(a, b), string::le(a, b)),
        bool::and(string::gt(b, a), string::ge(b, a)),
    )
}

/// `bytes::from_string` and `bytes::to_string`: the byte count, then the round trip.
#[k::function(total, sort = Int, syntax = "byteCount({s})")]
pub struct ByteCount {
    pub s: Term<string::String>,
}

#[k::equation]
fn byte_count(k::term![ByteCount(s)]: Term<Int>) -> Term<Int> {
    bytes::length(bytes::from_string(s))
}

/// `bytes::to_string` of `bytes::from_string`.
#[k::function(total, sort = string::String, syntax = "roundTrip({s})")]
pub struct RoundTrip {
    pub s: Term<string::String>,
}

#[k::equation]
fn round_trip(k::term![RoundTrip(s)]: Term<string::String>) -> Term<string::String> {
    bytes::to_string(bytes::from_string(s))
}
