//! Golden layouts of KRS macro bodies too long for the line width.
//!
//! Each case formats a body whose one-line form exceeds the width and checks
//! the wrapped layout; `format_source` also checks that the tokens and line
//! comments are unchanged and that a second pass changes nothing.

use krs_fmt::{FormatOptions, format_source};

fn format(source: &str, max_width: usize) -> String {
    let options = FormatOptions {
        max_width: Some(max_width),
        rustfmt: false,
        check_rustfmt_fixpoint: false,
        ..FormatOptions::default()
    };
    let output = format_source(source, &options).expect("format source");
    for line in output.lines() {
        assert!(
            line.len() <= max_width,
            "line of {} columns:\n{line}\n{output}",
            line.len()
        );
    }
    output
}

/// A long or-pattern puts one alternative per line with a leading `|`,
/// aligned with the first; in parentheses it hugs them.
#[test]
fn long_or_patterns_put_one_alternative_per_line() {
    let source = "k::rules! { for Machine;
push: { k: [op @ (Op::PushZero | Op::Address | Op::Origin | Op::Caller | Op::CallValue | Op::CallDataSize), ..], gas: g } => { k: [Charge(op, g, 2), ..] };
}
k::equations! { for Size;
size_bool: (_, Bool()) => 1;
size_aggregate: (_, EnumType(_, _, layout) | StructType(_, layout) | UnionType(_, layout) | TupleType(layout)) => Size(layout);
}
k::rules! { for Step; use Op::*;
quiet: Push(n) | PushZero(n) | PushOne(n) | PushTwo(n) | PushThree(n) | PushFour(n) | PushFive(n) => n;
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            push: {
                k: [
                    op @ (Op::PushZero
                    | Op::Address
                    | Op::Origin
                    | Op::Caller
                    | Op::CallValue
                    | Op::CallDataSize),
                    ..
                ],
                gas: g
            } => {
                k: [Charge(op, g, 2), ..]
            };
        }
        k::equations! {
            for Size;
            size_bool: (_, Bool()) => 1;
            size_aggregate:
                (
                    _,
                    EnumType(_, _, layout)
                    | StructType(_, layout)
                    | UnionType(_, layout)
                    | TupleType(layout)
                ) => Size(layout);
        }
        k::rules! {
            for Step;
            use Op::*;
            quiet:
                Push(n)
                | PushZero(n)
                | PushOne(n)
                | PushTwo(n)
                | PushThree(n)
                | PushFour(n)
                | PushFive(n) => n;
        }
    "]]
    .assert_eq(&format(source, 80));
}

/// A long constructor term breaks its outermost group first, one argument
/// per line, and an inner group only when it still does not fit.
#[test]
fn long_constructor_terms_break_from_the_outside_in() {
    let source = "k::equations! { for Statement;
assign: (place, value) => Assign(Place(0, Projections::Empty()), Use(Operand::Copy(Place(3, Projections::Cons(Projection::Field(value), Projections::Empty())))));
}
";
    expect_test::expect![[r"
        k::equations! {
            for Statement;
            assign:
                (place, value) => Assign(
                    Place(0, Projections::Empty()),
                    Use(
                        Operand::Copy(
                            Place(3, Projections::Cons(Projection::Field(value), Projections::Empty()))
                        )
                    )
                );
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// A long record entry breaks inside its value, nested records included,
/// and a record update's `..base` and cell shorthand keep their spelling.
#[test]
fn long_record_entries_break_inside_their_values() {
    let source = "k::rules! { for Machine;
copy: { k: [t @ CopyBytes { memory: PrepareMemory { memory, used, start: argument_start, width: argument_width }, destination, .. }, ..], pc, gas } => { k: [CopyBytes { memory: MemoryUsage { used, start: argument_start, width: argument_width }, ..t }, ..], pc, gas: int::sub(gas, 3) };
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            copy: {
                k: [
                    t @ CopyBytes {
                        memory: PrepareMemory {
                            memory,
                            used,
                            start: argument_start,
                            width: argument_width
                        },
                        destination,
                        ..
                    },
                    ..
                ],
                pc,
                gas
            } => {
                k: [
                    CopyBytes {
                        memory: MemoryUsage {
                            used,
                            start: argument_start,
                            width: argument_width
                        },
                        ..t
                    },
                    ..
                ],
                pc,
                gas: int::sub(gas, 3)
            };
        }
    "]]
    .assert_eq(&format(source, 90));
}

/// A long `where` list puts one binder per line, under `where`.
#[test]
fn long_where_lists_put_one_binder_per_line() {
    let source = "k::rules! { for Machine;
step: { k: [Resolve(height, place, mutability, metadata, destination), ..] } => { k: [..] } where height: Int, place: Place, mutability: Mutability, metadata: Metadata, destination: Place;
short: { k: [Done(v), ..] } => { k: [..] } where v: Int;
}
k::rules! { for Expr;
long_row: Resolve(height, place, mutability, metadata) => place where height: Int, place: Place, mutability: Mutability;
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            step: {
                k: [Resolve(height, place, mutability, metadata, destination), ..]
            } => {
                k: [..]
            }
            where
                height: Int,
                place: Place,
                mutability: Mutability,
                metadata: Metadata,
                destination: Place;
            short: {
                k: [Done(v), ..]
            } => {
                k: [..]
            }
            where v: Int;
        }
        k::rules! {
            for Expr;
            long_row:
                Resolve(height, place, mutability, metadata) => place
                where height: Int, place: Place, mutability: Mutability;
        }
    "]]
    .assert_eq(&format(source, 80));
}

/// A table keeps its alignment for the rows that fit; a row that does not
/// is laid out on its own and widens no column, and a row that fits only
/// unaligned stays on one line outside the alignment.
#[test]
fn tables_align_only_the_rows_that_fit() {
    let source = "k::equations! { for Width;
w_bool: Bool() => 1;
w_char: Char() => 4;
w_signed: Signed(kind) => int::div(IntWidth(kind), 8);
w_static_array: ArrayType(element, Some(Constant(Value(Allocation(bytes, _, _, _)), _))) => int::mul(Width(element), ReadInt(bytes, 0, 1, 0));
w_wide_pattern_only: Pointer(PointerKind::Thin, Mutability::Mutable) => 8;
w_x: X => Pair(Pair(Pair(aaaaaaaa, bbbbbbbb), Pair(cccccccc, dddddddd)), eeeeeeee);
#[k::equation(owise)]
w_other: _ => 0;
}
";
    expect_test::expect![[r"
        k::equations! {
            for Width;
            w_bool  : Bool()       => 1;
            w_char  : Char()       => 4;
            w_signed: Signed(kind) => int::div(IntWidth(kind), 8);
            w_static_array:
                ArrayType(element, Some(Constant(Value(Allocation(bytes, _, _, _)), _)))
                => int::mul(Width(element), ReadInt(bytes, 0, 1, 0));
            w_wide_pattern_only: Pointer(PointerKind::Thin, Mutability::Mutable) => 8;
            w_x: X => Pair(Pair(Pair(aaaaaaaa, bbbbbbbb), Pair(cccccccc, dddddddd)), eeeeeeee);
            #[k::equation(owise)]
            w_other : _            => 0;
        }
    "]]
    .assert_eq(&format(source, 90));
}

/// Comments inside a wrapped term keep their place: one on its own line
/// before an item, one ending an item's line, one before a group's close.
/// They break their groups, and a second pass changes nothing.
#[test]
fn comments_inside_wrapped_terms_keep_their_place() {
    let source = "k::rules! { for Machine;
call: {
    // the callee's frame
    k: [Call(
        // the target
        target, arguments, // still the caller's
        gas
        // nothing after the gas
    ), ..],
    gas: g, // charged later
} => { k: [Enter(target, arguments, gas), ..], gas: g };
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            call: {
                // the callee's frame
                k: [
                    Call(
                        // the target
                        target,
                        arguments, // still the caller's
                        gas
                        // nothing after the gas
                    ),
                    ..
                ],
                gas: g, // charged later
            } => {
                k: [Enter(target, arguments, gas), ..],
                gas: g
            };
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// A one-line attribute too long for the width breaks inside its
/// arguments; one written over several lines keeps its layout.
#[test]
fn long_attributes_break_inside_their_arguments() {
    let source = "k::rules! { for Expr;
#[k::requires(SameTypeInfo { first: map::get(types, element), second: PrimitiveType { primitive: Unsigned(U8()) } })]
cast: Cast(element, types) => element;
#[k::requires(a.gt::<Int>(2)
    || a.eq::<Int>(0))]
keep: Keep(a) => a;
}
";
    expect_test::expect![[r"
        k::rules! {
            for Expr;
            #[k::requires(
                SameTypeInfo {
                    first: map::get(types, element),
                    second: PrimitiveType { primitive: Unsigned(U8()) }
                }
            )]
            cast: Cast(element, types) => element;
            #[k::requires(a.gt::<Int>(2)
                || a.eq::<Int>(0))]
            keep: Keep(a)              => a;
        }
    "]]
    .assert_eq(&format(source, 80));
}

/// Long conditions break before `||`, else `&&`, one level deeper, and an
/// operator expression keeps its spelling.
#[test]
fn long_connectives_break_before_their_operator() {
    let source = "k::equations! { for Check;
check: (first, second, third) => first.gt::<Int>(0) && second.lt::<Int>(third) || first + second * 2 == third - 1 && !third;
}
";
    expect_test::expect![[r"
        k::equations! {
            for Check;
            check:
                (first, second, third)
                => first.gt::<Int>(0) && second.lt::<Int>(third)
                    || first + second * 2 == third - 1 && !third;
        }
    "]]
    .assert_eq(&format(source, 70));
}

/// A claim block lays out like a block of cell records.
#[test]
fn claims_wrap_like_cell_records() {
    let source = "k::claims! { for Machine; use Instr::*;
#[k::claim(all_paths)]
simple_addition: { instrs: [Const(IntegerType::I64, 3), Const(IntegerType::I64, 4), Binary(IntegerType::I64, Add), ..], stack: Empty() } => { instrs: [..], stack: Cons(Value(IntegerType::I64, 7), Empty()) };
}
";
    expect_test::expect![[r"
        k::claims! {
            for Machine;
            use Instr::*;
            #[k::claim(all_paths)]
            simple_addition: {
                instrs: [
                    Const(IntegerType::I64, 3),
                    Const(IntegerType::I64, 4),
                    Binary(IntegerType::I64, Add),
                    ..
                ],
                stack: Empty()
            } => {
                instrs: [..],
                stack: Cons(Value(IntegerType::I64, 7), Empty())
            };
        }
    "]]
    .assert_eq(&format(source, 80));
}
