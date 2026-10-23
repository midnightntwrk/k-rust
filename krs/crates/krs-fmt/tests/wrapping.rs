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
                    ..,
                ],
                gas: g,
            } => {
                k: [Charge(op, g, 2), ..],
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
                    | TupleType(layout),
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
                    Use(Operand::Copy(Place(
                        3,
                        Projections::Cons(Projection::Field(value), Projections::Empty()),
                    ))),
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
                            width: argument_width,
                        },
                        destination,
                        ..
                    },
                    ..,
                ],
                pc,
                gas,
            } => {
                k: [
                    CopyBytes {
                        memory: MemoryUsage {
                            used,
                            start: argument_start,
                            width: argument_width,
                        },
                        ..t
                    },
                    ..,
                ],
                pc,
                gas: int::sub(gas, 3),
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
                k: [Resolve(height, place, mutability, metadata, destination), ..],
            } => {
                k: [..],
            }
            where
                height: Int,
                place: Place,
                mutability: Mutability,
                metadata: Metadata,
                destination: Place;
            short: {
                k: [Done(v), ..],
            } => {
                k: [..],
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
                        gas,
                        // nothing after the gas
                    ),
                    ..,
                ],
                gas: g, // charged later
            } => {
                k: [Enter(target, arguments, gas), ..],
                gas: g,
            };
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// A comment beside an operator keeps its side of it: one before `|` ends
/// the previous alternative's line, one after it ends the operator's.
#[test]
fn comments_beside_operators_keep_their_side() {
    let source = "k::equations! { for Size;
size: (_, Enum(a) // before the bar
| Struct(a) | // after the bar
Union(a)) => a;
}
";
    expect_test::expect![[r"
        k::equations! {
            for Size;
            size:
                (
                    _,
                    Enum(a) // before the bar
                    | Struct(a)
                    | // after the bar
                    Union(a),
                ) => a;
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
            #[k::requires(SameTypeInfo {
                first: map::get(types, element),
                second: PrimitiveType { primitive: Unsigned(U8()) },
            })]
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
                    ..,
                ],
                stack: Empty(),
            } => {
                instrs: [..],
                stack: Cons(Value(IntegerType::I64, 7), Empty()),
            };
        }
    "]]
    .assert_eq(&format(source, 80));
}

/// A broken comma list ends with a comma and a list on one line has none,
/// whatever the source wrote: calls, records, brackets, macro arguments, and
/// table rows. A one-element row `(0,)` and a `where` list before its `;`
/// keep their own spelling.
#[test]
fn trailing_commas_follow_the_layout() {
    let source = "k::rules! { for Machine;
step: { k: [Resolve(first_argument, second_argument, third_argument, fourth_argument), ..], gas: g, } => { k: [Pair(g, g,), ..,], gas: g, } where g: Int,;
}
k::equations! { for Size;
one: (0,) => 1;
pair: (0, b,) => Wrap(b,);
long: (first_argument, second_argument) => Combine(first_argument, second_argument, first_argument);
}
k::claims! { for Machine;
#[k::claim(all_paths)]
loads: { program: k::bytes!(b\"\\x60\\x02\\x60\\x07\\x05\\x60\\x02\\x60\\x07\\x07\\x60\\x05\\x60\\x06\\x60\"), pc: 0 } => { program: k::bytes!(b\"\\x60\\x02\",), pc: 2 };
}
";
    expect_test::expect![[r#"
        k::rules! {
            for Machine;
            step: {
                k: [
                    Resolve(
                        first_argument,
                        second_argument,
                        third_argument,
                        fourth_argument,
                    ),
                    ..,
                ],
                gas: g,
            } => {
                k: [Pair(g, g), ..],
                gas: g,
            }
            where g: Int;
        }
        k::equations! {
            for Size;
            one : (0,)   => 1;
            pair: (0, b) => Wrap(b);
            long:
                (first_argument, second_argument)
                => Combine(first_argument, second_argument, first_argument);
        }
        k::claims! {
            for Machine;
            #[k::claim(all_paths)]
            loads: {
                program: k::bytes!(
                    b"\x60\x02\x60\x07\x05\x60\x02\x60\x07\x07\x60\x05\x60\x06\x60",
                ),
                pc: 0,
            } => {
                program: k::bytes!(b"\x60\x02"),
                pc: 2,
            };
        }
    "#]]
    .assert_eq(&format(source, 80));
}

/// A rest ends a record without a comma, as in Rust; in brackets it is an
/// element like any other and takes one.
#[test]
fn a_rest_takes_a_comma_in_brackets_and_none_in_braces() {
    let source = "k::rules! { for Machine;
copy: { k: [CopyBytes { memory_region: m, destination_offset: d, source_offset: s, .. }, rest @ ..], acc: saved } => { k: [Done(m, d, s), ..rest], acc: Frame { pc: first_program_counter, depth: call_depth, ..saved } };
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            copy: {
                k: [
                    CopyBytes {
                        memory_region: m,
                        destination_offset: d,
                        source_offset: s,
                        ..
                    },
                    rest @ ..,
                ],
                acc: saved,
            } => {
                k: [Done(m, d, s), ..rest],
                acc: Frame {
                    pc: first_program_counter,
                    depth: call_depth,
                    ..saved
                },
            };
        }
    "]]
    .assert_eq(&format(source, 72));
}

/// A call whose one argument is a delimited term hugs it, nested calls too;
/// an argument with an alias, an operator, or a comment does not hug.
#[test]
fn a_call_hugs_its_one_delimited_argument() {
    let source = "k::rules! { for Machine;
log: { k: [Log(address, memory, start, width), ..], logs } => { k: [..], logs: list::concat(logs, list::item(LogRecord::Entry { address, topics: StackTakeList { stack, remaining }, data: ReturnBytes(memory, start, width) })) };
nested: { k: [Add(lhs, rhs, width, signed), ..] } => { k: [Boolean(TruncateInteger { value: lhs + rhs, width, signed } != lhs + rhs), ..] };
}
k::equations! { for Restore;
alias: Restore(saved @ CallState { program_counter: caller_frame_value, call_depth: depth, .. }) => saved;
operator: Restore(state) => Wrap(Frame { program_counter: caller_frame_value, depth } != Frame::empty());
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            log: {
                k: [Log(address, memory, start, width), ..],
                logs,
            } => {
                k: [..],
                logs: list::concat(
                    logs,
                    list::item(LogRecord::Entry {
                        address,
                        topics: StackTakeList { stack, remaining },
                        data: ReturnBytes(memory, start, width),
                    }),
                ),
            };
            nested: {
                k: [Add(lhs, rhs, width, signed), ..],
            } => {
                k: [
                    Boolean(
                        TruncateInteger { value: lhs + rhs, width, signed }
                            != lhs + rhs,
                    ),
                    ..,
                ],
            };
        }
        k::equations! {
            for Restore;
            alias:
                Restore(
                    saved @ CallState {
                        program_counter: caller_frame_value,
                        call_depth: depth,
                        ..
                    },
                ) => saved;
            operator:
                Restore(state) => Wrap(
                    Frame { program_counter: caller_frame_value, depth }
                        != Frame::empty(),
                );
        }
    "]]
    .assert_eq(&format(source, 80));
}

/// KMIR's `Boolean(..)` argument fills its line to exactly 100 columns: the
/// call hugs it, so its trailing comma does not reflow the record.
#[test]
fn a_hugged_argument_at_the_width_keeps_its_record_whole() {
    let source = "k::rules! { for Machine;
add_checked: { k: [BinaryOperation(lhs, rhs, width, signed), ..] } => { k: [SetLocalValue { place, value: Aggregate { variant: 0, fields: list::concat(list::item(Integer { value: TruncateInteger { value: lhs + rhs, width, signed }, width, signed }), list::concat(list::item(Boolean(TruncateInteger { value: lhs + rhs, width, signed } != lhs + rhs)), list::empty())) } }, ..] };
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            add_checked: {
                k: [BinaryOperation(lhs, rhs, width, signed), ..],
            } => {
                k: [
                    SetLocalValue {
                        place,
                        value: Aggregate {
                            variant: 0,
                            fields: list::concat(
                                list::item(Integer {
                                    value: TruncateInteger { value: lhs + rhs, width, signed },
                                    width,
                                    signed,
                                }),
                                list::concat(
                                    list::item(Boolean(
                                        TruncateInteger { value: lhs + rhs, width, signed } != lhs + rhs,
                                    )),
                                    list::empty(),
                                ),
                            ),
                        },
                    },
                    ..,
                ],
            };
        }
    "]].assert_eq(&format(source, 100));
}

/// A comparison too long for its line breaks before its operator, one
/// level deeper, after `||` and `&&`; a turbofish's brackets are no
/// comparison.
#[test]
fn a_long_comparison_breaks_before_its_operator() {
    let source = "k::equations! { for Check;
wide: (lhs, rhs) => Boolean(TruncateInteger { value: lhs + rhs, width, signed } != lhs.add::<Int>(rhs));
}
";
    expect_test::expect![[r"
        k::equations! {
            for Check;
            wide:
                (lhs, rhs) => Boolean(
                    TruncateInteger { value: lhs + rhs, width, signed }
                        != lhs.add::<Int>(rhs),
                );
        }
    "]]
    .assert_eq(&format(source, 76));
}

/// An operator after a left operand that breaks anyway joins the line of its
/// closing delimiters, and its own operand continues from there at the
/// chain's indentation: `} != rhs`, also when that operand breaks in turn.
#[test]
fn an_operator_joins_the_closing_line_of_a_broken_left_operand() {
    let source = "k::equations! { for Check;
wide: (lhs, rhs) => Boolean(TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } != lhs.add::<Int>(rhs));
both: (lhs, rhs) => Boolean(TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } == TruncateInteger { value: rhs, width: some_long_width_name, signed: signedness_flag_value });
call: (lhs, rhs) => Boolean(TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } != some_function_with_long_name(lhs, rhs, some_long_width_name, signedness_flag_value));
}
";
    expect_test::expect![[r"
        k::equations! {
            for Check;
            wide:
                (lhs, rhs) => Boolean(
                    TruncateInteger {
                        value: lhs + rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    } != lhs.add::<Int>(rhs),
                );
            both:
                (lhs, rhs) => Boolean(
                    TruncateInteger {
                        value: lhs + rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    } == TruncateInteger {
                        value: rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    },
                );
            call:
                (lhs, rhs) => Boolean(
                    TruncateInteger {
                        value: lhs + rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    } != some_function_with_long_name(
                        lhs,
                        rhs,
                        some_long_width_name,
                        signedness_flag_value,
                    ),
                );
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// A row whose result is a chain with a first operand that fits on no line
/// keeps `=>` on the pattern line, as it does for that operand alone; a
/// first operand that fits whole on the arm's own line moves the arm there
/// and stays whole.
#[test]
fn an_arm_measures_a_chain_by_its_first_operands_first_line() {
    let source = "k::equations! { for Check;
cmp: (lhs, rhs) => TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } != rhs;
plain: (lhs, rhs) => TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value };
whole: (left_operand_name, right_operand_name) => TruncateInteger { value: lhs + rhs, width: some_width, signed: flag } != rhs.add::<Int>(right_operand_name);
}
";
    expect_test::expect![[r"
        k::equations! {
            for Check;
            cmp:
                (lhs, rhs) => TruncateInteger {
                    value: lhs + rhs,
                    width: some_long_width_name,
                    signed: signedness_flag_value,
                } != rhs;
            plain:
                (lhs, rhs) => TruncateInteger {
                    value: lhs + rhs,
                    width: some_long_width_name,
                    signed: signedness_flag_value,
                };
            whole:
                (left_operand_name, right_operand_name)
                => TruncateInteger { value: lhs + rhs, width: some_width, signed: flag }
                    != rhs.add::<Int>(right_operand_name);
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// The join applies to every expression rank: after a broken operand, `&&`
/// and `||` join as a comparison does, and a looser operator after a joined
/// comparison starts its line; a middle operand's closing line sits deeper
/// than the chain's continuation, so the operator after it starts its line.
#[test]
fn logical_operators_join_a_broken_left_operand_too() {
    let source = "k::equations! { for Check;
mixed: (lhs, rhs) => TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } != rhs && other_condition;
chain: (lhs, rhs) => Boolean(Holds(TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value }) && second_operand_name && third_operand_name);
middle: (lhs, rhs) => Boolean(first_operand_name_that_is_long && TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } && third);
}
";
    expect_test::expect![[r"
        k::equations! {
            for Check;
            mixed:
                (lhs, rhs) => TruncateInteger {
                    value: lhs + rhs,
                    width: some_long_width_name,
                    signed: signedness_flag_value,
                } != rhs
                    && other_condition;
            chain:
                (lhs, rhs) => Boolean(
                    Holds(TruncateInteger {
                        value: lhs + rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    }) && second_operand_name
                        && third_operand_name,
                );
            middle:
                (lhs, rhs) => Boolean(
                    first_operand_name_that_is_long
                        && TruncateInteger {
                            value: lhs + rhs,
                            width: some_long_width_name,
                            signed: signedness_flag_value,
                        }
                        && third,
                );
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// A left operand no wider than one level keeps the operator and the first
/// line of a breaking right operand on its line.
#[test]
fn an_operator_joins_a_short_left_operand() {
    let source = "k::equations! { for Check;
tiny: (lhs, rhs) => Boolean(x != TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value });
}
";
    expect_test::expect![[r"
        k::equations! {
            for Check;
            tiny:
                (lhs, rhs) => Boolean(
                    x != TruncateInteger {
                        value: lhs + rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    },
                );
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// A line comment before or after an operator keeps the operator at the
/// start of its line; an or-pattern's alternatives never join.
#[test]
fn comments_and_or_patterns_keep_the_operator_leading() {
    let source = "k::equations! { for Check;
before: (lhs, rhs) => Boolean(TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } // the truncated sum
!= lhs.add::<Int>(rhs));
after: (lhs, rhs) => Boolean(TruncateInteger { value: lhs + rhs, width: some_long_width_name, signed: signedness_flag_value } != // the plain sum
lhs.add::<Int>(rhs));
}
k::rules! { for Step;
alternatives: Frame { value: SOME_LONG_VALUE_NAME, width: SOME_LONG_WIDTH_NAME, signed: SIGNEDNESS_FLAG_VALUE } | Other => Done;
}
";
    expect_test::expect![[r"
        k::equations! {
            for Check;
            before:
                (lhs, rhs) => Boolean(
                    TruncateInteger {
                        value: lhs + rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    } // the truncated sum
                        != lhs.add::<Int>(rhs),
                );
            after:
                (lhs, rhs) => Boolean(
                    TruncateInteger {
                        value: lhs + rhs,
                        width: some_long_width_name,
                        signed: signedness_flag_value,
                    }
                        != // the plain sum
                        lhs.add::<Int>(rhs),
                );
        }
        k::rules! {
            for Step;
            alternatives:
                Frame {
                    value: SOME_LONG_VALUE_NAME,
                    width: SOME_LONG_WIDTH_NAME,
                    signed: SIGNEDNESS_FLAG_VALUE,
                }
                | Other => Done;
        }
    "]]
    .assert_eq(&format(source, 100));
}

/// A builtin `List` bracket with its rest in front or in the middle wraps
/// like any other: one element per line, the rest in place, a trailing
/// comma after the last.
#[test]
fn long_lists_with_a_rest_anywhere_put_one_entry_per_line() {
    let source = "k::rules! { for Machine;
rotate: { k: [Rotate(), ..], queue: [first_element, second_element, middle @ .., last_element] } => { k: [..], queue: [last_element, ..middle, second_element, first_element] };
log: { k: [Log(entry), ..], logs } => { k: [..], logs: [..logs, LogRecord::Entry { account: entry, topics: entry }] };
}
";
    expect_test::expect![[r"
        k::rules! {
            for Machine;
            rotate: {
                k: [Rotate(), ..],
                queue: [
                    first_element,
                    second_element,
                    middle @ ..,
                    last_element,
                ],
            } => {
                k: [..],
                queue: [
                    last_element,
                    ..middle,
                    second_element,
                    first_element,
                ],
            };
            log: {
                k: [Log(entry), ..],
                logs,
            } => {
                k: [..],
                logs: [
                    ..logs,
                    LogRecord::Entry {
                        account: entry,
                        topics: entry,
                    },
                ],
            };
        }
    "]]
    .assert_eq(&format(source, 60));
}
