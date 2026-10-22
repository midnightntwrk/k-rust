//! Readable claims, `k::claims!` (F7), end to end: each clause is the
//! `#[k::claim]` fn its records stand for. `KWasm`'s integer slice and a
//! KEVM-shaped machine prove their claims, emit the reference claims' K,
//! and expand to the reference fns; and the clause shapes a claim rejects.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// `KWasm`'s integer arithmetic slice, as the port writes it up to its claim.
const KWASM: &str = r##"//! Readable qualification slice for `KWasm` integer arithmetic.
//!
//! The source mapping is pinned in `../../tests/kwasm/source-map.md`.
//! This definition preserves `KWasm`'s constant normalization, value transfer,
//! operand loading, functional arithmetic, and division traps.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    IValType;
    IBinOp;
    Instr: k::KItem;
    Instrs: k::KItem;
    Val: KResult;
    ValStack;
}

#[k::constructors(sort = IValType, result = KResult)]
pub enum IntegerType {
    #[k::syntax("i32")]
    I32,
    #[k::syntax("i64")]
    I64,
}

#[k::constructors(sort = IBinOp, result = KResult)]
pub enum IntegerBinOp {
    #[k::syntax("add")]
    Add,
    #[k::syntax("sub")]
    Sub,
    #[k::syntax("mul")]
    Mul,
    #[k::syntax("div_u")]
    DivU,
}

#[k::constructors(sort = Val, result = KResult)]
pub enum Value {
    #[k::syntax("< {ty} > {value}")]
    Integer { ty: IValType, value: Int },
    #[k::syntax("undefined")]
    Undefined(),
}

#[k::constructors(sort = ValStack, result = KResult)]
#[k::precedence((Empty, Cons))]
pub enum Stack {
    #[k::syntax(".ValStack")]
    Empty(),
    #[k::syntax("{head} : {tail}")]
    Cons { head: Val, tail: ValStack },
}

#[k::constructors(sort = Instr, result = KResult)]
pub enum Instruction {
    #[k::syntax("{ty}.const {value}")]
    Const { ty: IValType, value: Int },
    #[k::syntax("{ty}.{op}")]
    Binary { ty: IValType, op: IBinOp },
    #[k::syntax("trap")]
    Trap(),
}

/// A concrete right-recursive program list, corresponding to `KWasm`'s `Instrs`.
#[k::constructors(sort = Instrs, result = KResult)]
#[k::precedence((InstrEmpty, InstrCons))]
pub enum InstrList {
    #[k::syntax(".Instrs")]
    InstrEmpty(),
    #[k::syntax("{head} ; {tail}")]
    InstrCons { head: Instr, tail: Instrs },
}

#[k::function(total, syntax = "#kwasmChop({ty}, {value})")]
pub fn Chop(ty: k::Term<IValType>, value: k::Term<Int>) -> k::Term<Val>;

#[k::function(total, syntax = "#kwasmIntBinOp({ty}, {op}, {lhs}, {rhs})")]
pub fn IntBinOp(
    ty: k::Term<IValType>,
    op: k::Term<IBinOp>,
    lhs: k::Term<Int>,
    rhs: k::Term<Int>,
) -> k::Term<Val>;

k::equations! {
    for Chop;
    chop_i32: (IntegerType::I32, value) => Value::Integer(IntegerType::I32, int::rem_euclid(value, 4_294_967_296));
    chop_i64: (IntegerType::I64, value) => Value::Integer(IntegerType::I64, int::rem_euclid(value, 18_446_744_073_709_551_616));
}

k::equations! {
    for IntBinOp;
    add       : (ty, IntegerBinOp::Add, lhs, rhs)               => Chop(ty, int::add(lhs, rhs));
    sub_i32   : (IntegerType::I32, IntegerBinOp::Sub, lhs, rhs) => Chop(IntegerType::I32, int::sub(int::add(lhs, 4_294_967_296), rhs));
    sub_i64   : (IntegerType::I64, IntegerBinOp::Sub, lhs, rhs) => Chop(IntegerType::I64, int::sub(int::add(lhs, 18_446_744_073_709_551_616), rhs));
    mul       : (ty, IntegerBinOp::Mul, lhs, rhs)               => Chop(ty, int::mul(lhs, rhs));
    #[k::requires(int::ne(rhs, 0))]
    div_u     : (ty, IntegerBinOp::DivU, lhs, rhs)              => Value::Integer(ty, int::div(lhs, rhs));
    #[k::requires(int::eq(rhs, 0))]
    div_u_zero: (_, IntegerBinOp::DivU, _, rhs)                 => Value::Undefined();
}

/// The two operational cells selected from `KWasm`'s `<wasm>` configuration.
#[k::configuration]
pub struct Machine {
    #[k::cell(name = "instrs")]
    pub instrs: KSequence,
    #[k::cell(name = "valstack")]
    pub valstack: ValStack,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: KSequence,
        #[k::config_var(name = "STACK")] stack: ValStack,
    ) -> Self {
        Self {
            instrs: k::k![program],
            valstack: stack,
        }
    }
}

k::rules! {
    for Machine;
    use InstrList::*;

    sequence_cons: {
        instrs: [InstrCons(head, tail), ..],
    } => {
        instrs: [head, tail, ..],
    }
    where head: Instr, tail: Instrs;

    sequence_empty: {
        instrs: [InstrEmpty(), ..],
    } => {
        instrs: [..],
    };
}

#[rustfmt::skip]
k::rules! {
    for Machine;
    use Instruction::*;

    constant_i32: {
        instrs: [Const(IntegerType::I32, value), ..],
    } => {
        instrs: [crate::Chop(IntegerType::I32, int::add(value, 4_294_967_296)), ..],
    }
    where value: Int;

    constant_i64: {
        instrs: [Const(IntegerType::I64, value), ..],
    } => {
        instrs: [crate::Chop(IntegerType::I64, int::add(value, 18_446_744_073_709_551_616),), ..],
    }
    where value: Int;

    undefined_traps: {
        instrs: [Value::Undefined(), ..],
    } => {
        instrs: [Trap(), ..],
    };

    load_binary: {
        instrs: [Binary(ty, op), ..],
        valstack: Stack::Cons(Value::Integer(ty, rhs), Stack::Cons(Value::Integer(ty, lhs), rest),),
    } => {
        instrs: [crate::IntBinOp(ty, op, lhs, rhs), ..],
        valstack: rest,
    }
    where ty: IValType, op: IBinOp, lhs: Int, rhs: Int, rest: ValStack;

    push_value: {
        instrs: [Value::Integer(ty, value), ..],
        valstack: stack,
    } => {
        instrs: [..],
        valstack: Stack::Cons(Value::Integer(ty, value), stack),
    }
    where ty: IValType, value: Int, stack: ValStack;
}

"##;

/// The port's reference claim.
const KWASM_REFERENCE: &str = r#"/// Executable all-path claim corresponding to `KWasm`'s simple-addition claim shape.
#[k::claim(all_paths, label = "simple-addition")]
fn simple_addition(
    k::cells! {
        instrs: k::configuration::KCell(
            Instruction::Const(IntegerType::I32, 3),
            Instruction::Const(IntegerType::I32, 4),
            Instruction::Binary(IntegerType::I32, IntegerBinOp::Add)
        ),
        valstack: k::configuration::Cell(Stack::Empty()),
    }: Machine,
) -> Machine {
    k::cells! {
        instrs: k::configuration::KCell(.K),
        valstack: k::configuration::Cell(Stack::Cons(
            Value::Integer(IntegerType::I32, 7),
            Stack::Empty(),
        )),
    }
}
"#;

const KWASM_READABLE: &str = r"
k::claims! {
    for Machine;
    use Instruction::*;

    /// Executable all-path claim corresponding to `KWasm`'s simple-addition claim shape.
    #[k::claim(all_paths)]
    simple_addition: {
        instrs: [Const(IntegerType::I32, 3), Const(IntegerType::I32, 4), Binary(IntegerType::I32, IntegerBinOp::Add)],
        valstack: Stack::Empty(),
    } => {
        instrs: [],
        valstack: Stack::Cons(Value::Integer(IntegerType::I32, 7), Stack::Empty()),
    };
}
";

/// A KEVM-shaped machine: the computation, a status code, and a nested
/// call state whose cells the rules name directly.
const KEVM: &str = r#"use k::builtin::{Int, KSequence, int};
use k::KResult;

k::sorts! {
    Op: k::KItem;
    WordStack;
    StatusCode;
}

#[k::constructors(sort = Op, result = KResult)]
#[k::precedence((Push, Add, Stop))]
pub enum Operation {
    #[k::syntax("PUSH({value})")]
    Push { value: Int },
    #[k::syntax("ADD")]
    Add(),
    #[k::syntax("STOP")]
    Stop(),
}

#[k::constructors(sort = WordStack, result = KResult)]
#[k::precedence((StackEmpty, StackCons))]
pub enum Stack {
    #[k::syntax(".WordStack")]
    StackEmpty(),
    #[k::syntax("{head} : {tail}")]
    StackCons { head: Int, tail: WordStack },
}

#[k::constructors(sort = StatusCode, result = KResult)]
#[k::precedence((Running, Success))]
pub enum Status {
    #[k::syntax("RUNNING")]
    Running(),
    #[k::syntax("SUCCESS")]
    Success(),
}

#[k::cell]
pub struct CallState {
    #[k::cell(name = "wordStack")]
    pub word_stack: WordStack,
    #[k::cell(name = "pc")]
    pub pc: Int,
    #[k::cell(name = "gas")]
    pub gas: Int,
    #[k::cell(name = "callDepth")]
    pub call_depth: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "statusCode")]
    pub status_code: StatusCode,
    #[k::cell(name = "callState", nested)]
    pub call_state: CallState,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: KSequence) -> Self {
        Self {
            k: k::k![program],
            status_code: Status::Running(),
            call_state: CallState {
                word_stack: Stack::StackEmpty(),
                pc: 0,
                gas: 0,
                call_depth: 0,
            },
        }
    }
}

k::rules! {
    for Machine;
    use Operation::*;

    push: {
        k: [Push { value }, ..],
        word_stack: stack,
        pc,
        gas,
    } => {
        k: [..],
        word_stack: Stack::StackCons(value, stack),
        pc: int::add(pc, 1),
        gas: int::sub(gas, 3),
    };

    add: {
        k: [Add(), ..],
        word_stack: Stack::StackCons(lhs, Stack::StackCons(rhs, rest)),
        pc,
        gas,
    } => {
        k: [..],
        word_stack: Stack::StackCons(int::add(lhs, rhs), rest),
        pc: int::add(pc, 1),
        gas: int::sub(gas, 3),
    };

    stop: {
        k: [Stop()],
        status_code: _,
    } => {
        k: [],
        status_code: Status::Success(),
    };
}
"#;

/// KEVM's `push-add-pc-stop` shape, over the whole frame, symbolic with an
/// existential result, and one-path.
const KEVM_READABLE: &str = r"k::claims! {
    for Machine;
    use Operation::*;

    /// Two pushes and an add leave their sum, as KEVM's `push-add-pc-stop`.
    #[k::claim(all_paths)]
    push_add_stop: {
        k: [Push { value: 2 }, Push { value: 3 }, Add(), Stop()],
        status_code: Status::Running(),
        word_stack: Stack::StackEmpty(),
        pc: 0,
        gas: 11,
    } => {
        k: [],
        status_code: Status::Success(),
        word_stack: Stack::StackCons(5, Stack::StackEmpty()),
        pc: 3,
        gas: 2,
    };

    /// The same run over the whole frame, which keeps its call depth.
    #[k::claim(all_paths)]
    push_add_frame: {
        k: [Push { value: 2 }, Push { value: 3 }, Add(), Stop()],
        status_code: Status::Running(),
        call_state: frame @ CallState { word_stack: Stack::StackEmpty(), pc: 0, gas: 11, .. },
    } => {
        k: [],
        status_code: Status::Success(),
        call_state: CallState { word_stack: Stack::StackCons(5, Stack::StackEmpty()), pc: 3, gas: 2, ..frame },
    };

    /// Any gas above the cost suffices; what is left is existential.
    #[k::claim(all_paths)]
    #[k::requires(int::ge(g, 9))]
    #[k::exists(left: Int)]
    #[k::ensures(int::eq(left, int::sub(g, 9)))]
    push_add_symbolic: {
        k: [Push { value: 2 }, Push { value: 3 }, Add(), Stop()],
        status_code: Status::Running(),
        word_stack: Stack::StackEmpty(),
        pc,
        gas: g,
    } => {
        k: [],
        status_code: Status::Success(),
        word_stack: Stack::StackCons(5, Stack::StackEmpty()),
        pc: int::add(pc, 3),
        gas: left,
    };

    #[k::claim(one_path)]
    push_one_path: {
        k: [Push { value: 7 }, Stop()],
        status_code: _,
        word_stack: Stack::StackEmpty(),
        pc: 0,
        gas: 3,
    } => {
        k: [],
        status_code: Status::Success(),
        word_stack: Stack::StackCons(7, Stack::StackEmpty()),
        pc: 1,
        gas: 0,
    };
}
";

/// The reference fn of `push_add_stop`, as KEVM writes its claims.
const KEVM_REFERENCE: &str = r#"/// Two pushes and an add leave their sum, as KEVM's `push-add-pc-stop`.
#[k::claim(all_paths, label = "push-add-stop")]
fn push_add_stop(
    k::cells! {
        k: k::configuration::KCell(Operation::Push(2), Operation::Push(3), Operation::Add(), Operation::Stop()),
        status_code: k::configuration::Cell(Status::Running()),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(11),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        status_code: k::configuration::Cell(Status::Success()),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(5, Stack::StackEmpty())),
        CallState::pc: k::configuration::Cell(3),
        CallState::gas: k::configuration::Cell(2),
        ..state
    }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `library`; packages of
/// one `namespace` emit one K module name.
fn package(root: &Path, name: &str, namespace: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .args(extra)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The `spec.k` that `krs emit-k` writes for the package.
fn emitted_spec(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("spec.k")).unwrap()
}

/// The claim results `krs prove` reports, one line per claim.
fn proved(target: &Path, manifest: &Path, extra: &[&str]) -> Vec<String> {
    let (success, stdout, stderr) = krs(target, manifest, "prove", extra);
    assert!(success, "{stdout}\n{stderr}");
    stdout
        .lines()
        .filter(|line| line.contains(": proven") || line.contains(": trusted"))
        .map(ToOwned::to_owned)
        .collect()
}

/// The `#[k::claim]` fn `krs expand` writes for `label`.
fn expanded_claim(expanded: &str, label: &str) -> String {
    let start = expanded
        .find(&format!("label = \"{label}\""))
        .unwrap_or_else(|| panic!("`{label}` is written:\n{expanded}"));
    let start = expanded[..start].rfind("#[k::claim").unwrap();
    let end = start + expanded[start..].find("\n}\n").unwrap() + 2;
    expanded[start..end].to_owned()
}

/// `KWasm`'s `simple_addition` as a readable claim: proven, the port's
/// reference claim's K, and `krs expand` writes the reference fn, which
/// frames the cells the records leave out with `state @ ..`.
#[test]
fn a_readable_kwasm_claim_is_the_reference_claim() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = package(
        temporary.path(),
        "kwasm-readable",
        "ORG-KRS-KWASM-CLAIMS",
        &format!("{KWASM}{KWASM_READABLE}"),
    );
    let reference = package(
        temporary.path(),
        "kwasm-reference",
        "ORG-KRS-KWASM-CLAIMS",
        &format!("{KWASM}{KWASM_REFERENCE}"),
    );
    assert_eq!(
        proved(target.path(), &readable, &[]),
        ["ORG-KRS-KWASM-CLAIMS-SPEC.simple-addition: proven"]
    );
    let spec = emitted_spec(target.path(), &readable);
    assert_eq!(spec, emitted_spec(target.path(), &reference));
    expect_test::expect![[r#"
        requires "definition.k"

        module ORG-KRS-KWASM-CLAIMS-SPEC
          imports ORG-KRS-KWASM-CLAIMS

          claim [simple-addition]:
            <instrs> i32 . const 3 ~> i32 . const 4 ~> i32 . add => .K </instrs>
            <valstack> . ValStack => < i32 > 7 : . ValStack </valstack>
        endmodule
    "#]]
    .assert_eq(&spec);
    let (success, expanded, stderr) = krs(target.path(), &readable, "expand", &[]);
    assert!(success, "{stderr}");
    expect_test::expect![[r#"
        #[k::claim(all_paths, label = "simple-addition")]
        pub fn simple_addition(
            k::cells! {
                instrs : k::configuration::KCell(crate ::Instruction::Const(crate
                ::IntegerType::I32, 3), crate ::Instruction::Const(crate ::IntegerType::I32, 4),
                crate ::Instruction::Binary(crate ::IntegerType::I32, crate
                ::IntegerBinOp::Add)), valstack : k::configuration::Cell(crate ::Stack::Empty()),
                state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                instrs : k::configuration::KCell(), valstack : k::configuration::Cell(crate
                ::Stack::Cons(crate ::Value::Integer(crate ::IntegerType::I32, 7), crate
                ::Stack::Empty())), ..state
            }
        }"#]]
    .assert_eq(&expanded_claim(&expanded, "simple-addition"));
}

/// A KEVM-shaped claim naming nested cells directly emits the reference
/// claim's K; the same run over the whole frame updates it (F5), a
/// symbolic claim states its result with `#[k::exists]` and `#[k::ensures]`,
/// and a one-path claim proves too. The expanded package proves the same
/// claims.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "The recorded spec and expansion are spelled out inline."
)]
fn readable_kevm_claims_prove_and_expand() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = package(
        temporary.path(),
        "kevm-readable",
        "ORG-KRS-KEVM-CLAIMS",
        &format!("{KEVM}{KEVM_READABLE}"),
    );
    expect_test::expect![[r#"
        [
            "ORG-KRS-KEVM-CLAIMS-SPEC.push-add-frame: proven",
            "ORG-KRS-KEVM-CLAIMS-SPEC.push-add-stop: proven",
            "ORG-KRS-KEVM-CLAIMS-SPEC.push-add-symbolic: proven",
            "ORG-KRS-KEVM-CLAIMS-SPEC.push-one-path: proven",
        ]
    "#]]
    .assert_debug_eq(&proved(target.path(), &readable, &[]));
    let spec = emitted_spec(target.path(), &readable);
    // The claim's sentence, up to the next claim or the module's end.
    let one = |spec: &str| {
        let start = spec.find("claim [push-add-stop]").unwrap();
        let rest = &spec[start..];
        let end = ["\n  claim", "\nendmodule"]
            .iter()
            .filter_map(|marker| rest.find(marker))
            .min()
            .unwrap();
        rest[..end].to_owned()
    };
    let reference = package(
        temporary.path(),
        "kevm-reference",
        "ORG-KRS-KEVM-CLAIMS",
        &format!("{KEVM}{KEVM_REFERENCE}"),
    );
    assert_eq!(one(&spec), one(&emitted_spec(target.path(), &reference)));
    expect_test::expect![[r#"
        requires "definition.k"

        module ORG-KRS-KEVM-CLAIMS-SPEC
          imports ORG-KRS-KEVM-CLAIMS

          claim [push-add-frame]:
            <k> PUSH ( 2 ) ~> PUSH ( 3 ) ~> ADD ~> STOP => .K </k>
            <statusCode> RUNNING => SUCCESS </statusCode>
            (<callState> <wordStack> . WordStack </wordStack> <pc> 0 </pc> <gas> 11 </gas> <callDepth> Krs_UpdateFrameCallDepth:Int </callDepth> </callState> => <callState> <wordStack> 5 : . WordStack </wordStack> <pc> 3 </pc> <gas> 2 </gas> <callDepth> Krs_UpdateFrameCallDepth:Int </callDepth> </callState>)
          claim [push-add-stop]:
            <k> PUSH ( 2 ) ~> PUSH ( 3 ) ~> ADD ~> STOP => .K </k>
            <statusCode> RUNNING => SUCCESS </statusCode>
            <wordStack> . WordStack => 5 : . WordStack </wordStack>
            <pc> 0 => 3 </pc>
            <gas> 11 => 2 </gas>
          claim [push-add-symbolic]:
            <k> PUSH ( 2 ) ~> PUSH ( 3 ) ~> ADD ~> STOP => .K </k>
            <statusCode> RUNNING => SUCCESS </statusCode>
            <wordStack> . WordStack => 5 : . WordStack </wordStack>
            <pc> Pc:Int => Pc:Int +Int 3 </pc>
            <gas> G:Int => ?Left:Int </gas>
            requires G:Int >=Int 9
            ensures ?Left:Int ==Int (G:Int -Int 9)
          claim [push-one-path]:
            <k> PUSH ( 7 ) ~> STOP => .K </k>
            <statusCode> _ => SUCCESS </statusCode>
            <wordStack> . WordStack => 7 : . WordStack </wordStack>
            <pc> 0 => 1 </pc>
            <gas> 3 => 0 </gas>
            [one-path]
        endmodule
    "#]].assert_eq(&spec);
    let (success, expanded, stderr) = krs(target.path(), &readable, "expand", &[]);
    assert!(success, "{stderr}");
    expect_test::expect![[r#"
        #[k::claim(all_paths, label = "push-add-frame")]
        pub fn push_add_frame(
            frame_call_depth: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(crate ::Operation::Push(2), crate
                ::Operation::Push(3), crate ::Operation::Add(), crate ::Operation::Stop()),
                status_code : k::configuration::Cell(crate ::Status::Running()), call_state :
                k::fragment![crate ::CallState { word_stack : crate ::Stack::StackEmpty(), pc :
                0, gas : 11, call_depth : frame_call_depth }], state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(), status_code : k::configuration::Cell(crate
                ::Status::Success()), call_state : k::fragment![crate ::CallState { word_stack :
                crate ::Stack::StackCons(5, crate ::Stack::StackEmpty()), pc : 3, gas : 2,
                call_depth : frame_call_depth }], ..state
            }
        }
        #[k::claim(all_paths, label = "push-add-symbolic")]
        #[k::exists(left:Int)]
        #[k::ensures(int::eq(left, int::sub(g, 9)))]
        #[k::requires(k::builtin::int::ge(g, 9))]
        pub fn push_add_symbolic(
            pc: k::Term<k::builtin::Int>,
            g: k::Term<k::builtin::Int>,
            k::cells! {
                k : k::configuration::KCell(crate ::Operation::Push(2), crate
                ::Operation::Push(3), crate ::Operation::Add(), crate ::Operation::Stop()),
                status_code : k::configuration::Cell(crate ::Status::Running()), crate
                ::CallState::word_stack : k::configuration::Cell(crate ::Stack::StackEmpty()),
                crate ::CallState::pc : k::configuration::Cell(pc), crate ::CallState::gas :
                k::configuration::Cell(g), state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            k::cells! {
                k : k::configuration::KCell(), status_code : k::configuration::Cell(crate
                ::Status::Success()), crate ::CallState::word_stack :
                k::configuration::Cell(crate ::Stack::StackCons(5, crate ::Stack::StackEmpty())),
                crate ::CallState::pc : k::configuration::Cell(k::builtin::int::add(pc, 3)),
                crate ::CallState::gas : k::configuration::Cell(left), ..state
            }
        }"#]]
    .assert_eq(&format!(
        "{}\n{}",
        expanded_claim(&expanded, "push-add-frame"),
        expanded_claim(&expanded, "push-add-symbolic")
    ));
    let expanded_package = package(
        temporary.path(),
        "kevm-expanded",
        "ORG-KRS-KEVM-CLAIMS",
        &expanded,
    );
    assert_eq!(
        proved(target.path(), &expanded_package, &[]),
        proved(target.path(), &readable, &[])
    );
}

/// A spec module holds readable claims, with the `trusted` and
/// `circularity` flags.
#[test]
fn a_spec_module_holds_readable_claims() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "kevm-spec-module",
        "ORG-KRS-KEVM-SPEC-MODULE",
        &format!(
            "{KEVM}
#[k::spec_module(name = \"KEVM-READABLE-SPEC\", imports = [crate])]
mod readable_spec {{
    use super::*;

    k::claims! {{
        for Machine;
        use Operation::*;

        #[k::claim(all_paths, trusted)]
        trusted_stop: {{ k: [Stop()], status_code: _ }} => {{ k: [], status_code: Status::Success() }};

        #[k::claim(all_paths, circularity)]
        circular_stop: {{ k: [Stop()], status_code }} => {{ k: [], status_code: Status::Success() }}
        where status_code: StatusCode;
    }}
}}
"
        ),
    );
    assert_eq!(
        proved(
            target.path(),
            &manifest,
            &["--spec-module", "KEVM-READABLE-SPEC"]
        ),
        [
            "KEVM-READABLE-SPEC.circular-stop: proven",
            "KEVM-READABLE-SPEC.trusted-stop: trusted"
        ]
    );
    expect_test::expect![[r#"
        requires "definition.k"

        module KEVM-READABLE-SPEC
          imports ORG-KRS-KEVM-SPEC-MODULE

          claim [circular-stop]:
            <k> STOP => .K </k>
            <statusCode> StatusCode:StatusCode => SUCCESS </statusCode>
            [circularity]
          claim [trusted-stop]:
            <k> STOP => .K </k>
            <statusCode> _ => SUCCESS </statusCode>
            [trusted]
        endmodule
    "#]]
    .assert_eq(&emitted_spec(target.path(), &manifest));
}

/// The `error[..]` headlines of `krs check`.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    stderr
        .lines()
        .filter(|line| line.starts_with("error["))
        .map(ToOwned::to_owned)
        .collect()
}

/// A claim clause states its modality, takes no rule-only attribute and no
/// `label`, and is a pair of records; a block names its configuration.
#[test]
fn a_claim_clause_rejects_rule_only_forms() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let errors = [
        ("modality", "x: { k: [Stop()] } => { k: [] };"),
        (
            "rule",
            "#[k::rule(label = \"x\")]\n    #[k::claim(all_paths)]\n    x: { k: [Stop()] } => { k: [] };",
        ),
        (
            "fresh",
            "#[k::claim(all_paths)]\n    #[k::fresh(n: Int)]\n    x: { k: [Stop()] } => { k: [] };",
        ),
        (
            "label",
            "#[k::claim(all_paths, label = \"x\")]\n    x: { k: [Stop()] } => { k: [] };",
        ),
        ("term", "#[k::claim(all_paths)]\n    x: Stop() => Stop();"),
        (
            "circular-one-path",
            "#[k::claim(one_path, circularity)]\n    x: { k: [Stop()] } => { k: [] };",
        ),
    ]
    .map(|(name, clause)| {
        let manifest = package(
            temporary.path(),
            &format!("invalid-{name}"),
            "ORG-KRS-KEVM-INVALID",
            &format!("{KEVM}k::claims! {{\n    for Machine;\n    use Operation::*;\n    {clause}\n}}\n"),
        );
        check_errors(target.path(), &manifest)
    });
    let missing_for = package(
        temporary.path(),
        "invalid-for",
        "ORG-KRS-KEVM-INVALID",
        &format!(
            "{KEVM}k::claims! {{\n    #[k::claim(all_paths)]\n    x: {{ k: [Operation::Stop()] }} => {{ k: [] }};\n}}\n"
        ),
    );
    let missing_for = check_errors(target.path(), &missing_for);
    expect_test::expect![[r#"
        (
            [
                [
                    "error[krs::syntax::unsupported-rule-signature]: unsupported rule signature: a claim clause states its modality: write `#[k::claim(all_paths)]` or `#[k::claim(one_path)]` before it",
                ],
                [
                    "error[krs::syntax::unsupported-rule-signature]: unsupported rule signature: `#[k::rule(..)]` is a rule's metadata; a claim clause takes `#[k::claim(..)]`",
                ],
                [
                    "error[krs::syntax::unsupported-rule-signature]: unsupported rule signature: `#[k::fresh]` draws values in a rule step; a claim has no fresh binders",
                ],
                [
                    "error[krs::syntax::rust-syntax]: a `k::claims!` clause is labelled by its name: rename the clause instead of writing `label`",
                ],
                [
                    "error[krs::syntax::rust-syntax]: a `k::claims!` clause is a pair of cell records `{ .. } => { .. }` over the block's configuration",
                ],
                [
                    "error[krs::syntax::rust-syntax]: circularity is valid only on an all-path claim",
                ],
            ],
            [
                "error[krs::syntax::rust-syntax]: expected `for`",
            ],
        )
    "#]].assert_debug_eq(&(errors, missing_for));
}

/// A machine whose program is a Bytes cell, as KEVM's is.
const BYTES_MACHINE: &str = r#"use k::builtin::{Bytes, Int, KSequence, bytes};
use k::KResult;

k::sorts! {
    Exp: k::KItem;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum Op {
    #[k::syntax("load")]
    Load(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub program: Bytes,
    #[k::cell]
    pub pc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm], program: bytes::empty(), pc: 0 }
    }
}

k::rules! {
    for Machine;
    use Op::*;

    load: { k: [Load(), ..], program: p, pc: n } => { k: [..], pc: bytes::length(p) };
}
"#;

/// A readable claim whose program cell holds a `k::bytes!(..)` literal.
const BYTES_READABLE: &str = r#"k::claims! {
    for Machine;
    use Op::*;

    #[k::claim(all_paths)]
    loads: { k: [Load()], program: k::bytes!(b"\x60\x00"), pc: k::anonymous!(Int, "_Pc") } => {
        k: [],
        program: k::bytes!(b"\x60\x00"),
        pc: 2,
    };
}
"#;

/// The same claim as a reference fn.
const BYTES_REFERENCE: &str = r#"#[k::claim(all_paths, label = "loads")]
fn loads(
    k::cells! {
        k: k::configuration::KCell(Op::Load()),
        program: k::configuration::Cell(k::bytes!(b"\x60\x00")),
        pc: k::configuration::Cell(k::anonymous!(Int, "_Pc")),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        pc: k::configuration::Cell(2),
        ..state
    }
}
"#;

/// A readable claim's record holds the claim-only literals `k::bytes!(..)`
/// and `k::anonymous!(..)` as whole cell values, as KEVM's claims' program
/// cells need: the claim is the reference claim and proves.
#[test]
fn a_readable_claim_holds_a_bytes_literal() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable = package(
        temporary.path(),
        "bytes-readable",
        "ORG-KRS-BYTES",
        &format!("{BYTES_MACHINE}{BYTES_READABLE}"),
    );
    let reference = package(
        temporary.path(),
        "bytes-reference",
        "ORG-KRS-BYTES",
        &format!("{BYTES_MACHINE}{BYTES_REFERENCE}"),
    );
    let spec = emitted_spec(target.path(), &readable);
    assert_eq!(spec, emitted_spec(target.path(), &reference));
    assert!(
        spec.contains(r#"<program> b"\x60\x00" </program>"#),
        "{spec}"
    );
    expect_test::expect![[r#"
        [
            "ORG-KRS-BYTES-SPEC.loads: proven",
        ]
    "#]]
    .assert_debug_eq(&proved(target.path(), &readable, &[]));
}
