//! Goldens recorded from Java K 7.1.337.
//!
//! Each definition under `tests/data` is compiled here through k-rust's own frontend (the pinned
//! k-rust checkout, with its embedded prelude) and executed by its backend. The printed result must
//! equal, byte for byte, what K 7.1.337 printed for the same definition compiled with
//! `kompile --backend llvm`: `krun --output pretty` (`<name>.run.out`, `<name>.depth1.out`),
//! `krun --color on` (`<name>.color.out`), and `kast --module <MAIN> --output program`
//! (`<name>.program.out`). The expected files are those Java outputs, unedited.

use std::collections::BTreeMap;

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ExecutionStrategy},
    builtin,
    inner::ProgramParser,
    kast::Sort as KastSort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar, SortInjector,
        compile_loaded_definition, program_start_position,
        term_to_kore_from_resolved_with_token_module,
    },
    kore::{ast::Pattern, json as kore_json},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};

use super::*;

/// One compiled test definition.
struct Fixture {
    unparser: Unparser,
    backend: Backend,
    initial: Pattern,
    /// The program as `kast` parses it, macros unexpanded, lowered to KORE.
    program: Pattern,
}

fn data(name: &str) -> String {
    let path = format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{path}: {error}"))
}

impl Fixture {
    fn compile(name: &str) -> Self {
        let main = name.to_ascii_uppercase();
        let source = data(&format!("{name}.k"));
        let mut resolver = |_: &str, required: &str| {
            builtin::embedded(required).ok_or_else(|| format!("no embedded source `{required}`"))
        };
        let options = LoadOptions {
            implicit_sources: vec![builtin::embedded("prelude.md").expect("prelude")],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        };
        let (loaded, syntax) = load_for_compilation(
            ResolvedSource::new(format!("{name}.k"), source),
            main.clone(),
            Some(&format!("{main}-SYNTAX")),
            &mut resolver,
            &options,
        )
        .unwrap_or_else(|error| panic!("{name}.k does not load: {error:?}"));
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend: CompilationBackend::Rust,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{name}.k does not compile: {error}"));
        let unparser =
            Unparser::from_kore(&artifacts.syntax_definition_kore, &artifacts.macros_kore)
                .expect("the compiled artifacts are KORE")
                .with_program_grammar(loaded.definition());
        let grammar = ProgramGrammar::new(loaded.definition()).expect("program grammar");
        let variables: BTreeMap<String, KastSort> = artifacts.configuration_variables.clone();
        let mut assembler = ConfigurationAssembler::new(&grammar, main.clone(), syntax, &variables);
        let start = program_start_position(&variables["PGM"]);
        assembler
            .program(&start, &data(&format!("{name}.pgm")))
            .expect("the program parses");
        let initial = assembler.finish().expect("the configuration assembles");
        let grammar_definition = grammar.resolved();
        let parser = ProgramParser::from_resolved(grammar_definition, &format!("{main}-SYNTAX"))
            .expect("program parser");
        let presented = parser
            .parse_for_presentation(&start, &data(&format!("{name}.pgm")))
            .expect("the program parses");
        let injector = SortInjector::new(grammar_definition, &main).expect("sort injector");
        let sort = injector
            .term_sort(presented.term(), Some(&start))
            .expect("the program has a sort");
        let injected = injector
            .inject(presented.term(), &sort)
            .expect("the program injects");
        let program = term_to_kore_from_resolved_with_token_module(
            grammar_definition,
            &main,
            &format!("{main}-SYNTAX"),
            &injected,
        )
        .expect("the program lowers to KORE");
        let backend = Backend::new(&artifacts.definition_kore, main, BackendOptions::default())
            .expect("the backend loads");
        Self {
            unparser,
            backend,
            initial,
            program,
        }
    }

    fn run(&mut self, depth: Option<u64>) -> Pattern {
        let mut request = ExecuteRequest::new(self.initial.clone());
        request.strategy = ExecutionStrategy::Any;
        request.max_depth = depth;
        let result = self.backend.execute(request).expect("the run succeeds");
        let [leaf] = <[_; 1]>::try_from(result.leaves).expect("one leaf");
        let text = serde_json::to_string(&leaf.state).expect("JSON");
        kore_json::from_str(&text).expect("KORE")
    }

    fn print(&self, pattern: &Pattern, options: Options) -> String {
        let printed = self.unparser.print_kore(pattern, &options);
        assert_eq!(printed.warnings, Vec::new(), "no warnings");
        format!("{}\n", printed.text)
    }
}

fn golden(name: &str, kind: &str) -> String {
    data(&format!("expected/{name}.{kind}.out"))
}

/// Compile and run on a thread with the stack the CLI and gate session give k-rust (64 MiB).
fn on_large_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

fn check_definition(name: &str) {
    let mut fixture = Fixture::compile(name);
    assert_eq!(
        fixture.print(&fixture.program, Options::new(Mode::Program)),
        golden(name, "program"),
        "{name}: kast --output program"
    );
    let final_state = fixture.run(None);
    assert_eq!(
        fixture.print(&final_state, Options::new(Mode::Pretty)),
        golden(name, "run"),
        "{name}: krun --output pretty"
    );
    assert_eq!(
        fixture.print(&final_state, Options::new(Mode::Pretty).with_color(true)),
        golden(name, "color"),
        "{name}: krun --color on"
    );
    let first_step = fixture.run(Some(1));
    assert_eq!(
        fixture.print(&first_step, Options::new(Mode::Pretty)),
        golden(name, "depth1"),
        "{name}: krun --depth 1"
    );
}

#[test]
fn probe_matches_java() {
    on_large_stack(|| {
        check_definition("probe");
        let mut fixture = Fixture::compile("probe");
        let state = fixture.run(Some(2));
        assert_eq!(
            fixture.print(&state, Options::new(Mode::Pretty)),
            golden("probe", "depth2"),
            "probe: krun --depth 2"
        );
    });
}

#[test]
fn formats_match_java() {
    on_large_stack(|| check_definition("formats"));
}

#[test]
fn brackets_match_java() {
    on_large_stack(|| check_definition("brackets"));
}

#[test]
fn aliases_match_java() {
    on_large_stack(|| check_definition("aliases"));
}

#[test]
fn sorted_collections_match_java() {
    on_large_stack(|| check_definition("sorted"));
}

#[test]
fn program_mode_prints_a_bracketless_sort_bare() {
    on_large_stack(|| {
        let mut fixture = Fixture::compile("brackets");
        let state = fixture.run(None);
        let text = fixture.print(&state, Options::new(Mode::Pretty));
        assert!(text.contains("tm ( 1 | 2 ) & 3 ;"), "{text}");
        // `kast --output program` adds no parentheses where the sort has no bracket production.
        let printed = fixture
            .unparser
            .print_kore(&state, &Options::new(Mode::Program));
        assert!(printed.text.contains("tm 1 | 2 & 3 ;"), "{}", printed.text);
    });
}

/// A hand-written syntax definition for the reversal and diagnostic rules no K tutorial definition exercises.
const SYNTHETIC: &str = r#"[]
module SYNTHETIC
  sort SortExp{} []
  symbol Lbla{}() : SortExp{} [format{}("a"), terminals{}("1")]
  symbol Lblf{}(SortExp{}) : SortExp{} [format{}("f ( %1 )"), terminals{}("1101")]
  symbol Lblg{}(SortExp{}) : SortExp{} [format{}("g ( %1 )"), terminals{}("1101")]
  symbol Lblh{}(SortExp{}) : SortExp{} []
  symbol Lblc{}() : SortExp{} [colors{}("red"), format{}("%cc%r%c!%r"), terminals{}("1")]
  symbol Lblbad{}(SortExp{}) : SortExp{} [format{}("bad %2"), terminals{}("10")]
endmodule []
"#;

fn synthetic(rule: &str, attribute: &str) -> Unparser {
    let macros = format!("axiom{{R}} \\equals{{SortExp{{}}, R}}({rule}) [{attribute}]");
    Unparser::from_kore(SYNTHETIC, &macros).expect("synthetic KORE")
}

fn pattern(text: &str) -> Pattern {
    k_rust::kore::parser::parse_pattern(text).expect("pattern")
}

const F_OF_X: &str = "Lblf{}(VarX:SortExp{})";
const F_OF_G_OF_X: &str = "Lblf{}(Lblg{}(VarX:SortExp{}))";
const F_G_G_A: &str = "Lblf{}(Lblg{}(Lblg{}(Lbla{}())))";

#[test]
fn a_non_recursive_alias_reverses_once_per_chain() {
    let unparser = synthetic(&format!("{F_OF_X}, {F_OF_G_OF_X}"), "alias'Kywd'{}()");
    let printed = unparser.print_kore(&pattern(F_G_G_A), &Options::default());
    assert_eq!(printed.text, "f ( g ( a ) )");
    assert_eq!(printed.warnings, Vec::new());
}

#[test]
fn a_recursive_alias_reverses_repeatedly() {
    let unparser = synthetic(&format!("{F_OF_X}, {F_OF_G_OF_X}"), "alias-rec{}()");
    let printed = unparser.print_kore(&pattern(F_G_G_A), &Options::default());
    assert_eq!(printed.text, "f ( a )");
}

#[test]
fn macros_are_never_reversed() {
    for attribute in ["macro{}()", "macro-rec{}()"] {
        let unparser = synthetic(&format!("{F_OF_X}, {F_OF_G_OF_X}"), attribute);
        let printed = unparser.print_kore(&pattern(F_G_G_A), &Options::default());
        assert_eq!(printed.text, "f ( g ( g ( a ) ) )", "{attribute}");
    }
}

#[test]
fn reversal_can_be_disabled() {
    let unparser = synthetic(&format!("{F_OF_X}, {F_OF_G_OF_X}"), "alias-rec{}()");
    let options = Options {
        reverse_aliases: false,
        ..Options::default()
    };
    let printed = unparser.print_kore(&pattern(F_G_G_A), &options);
    assert_eq!(printed.text, "f ( g ( g ( a ) ) )");
}

#[test]
fn an_unbounded_recursive_reversal_is_reported_not_looped() {
    on_large_stack(|| {
        let unparser = synthetic(&format!("{F_OF_X}, {F_OF_X}"), "alias-rec{}()");
        let printed = unparser.print_kore(&pattern("Lblf{}(Lbla{}())"), &Options::default());
        assert_eq!(printed.text, "f ( a )");
        assert_eq!(
            printed.warnings,
            vec![Warning::ReversalBound("Lblf".to_owned())]
        );
        assert_eq!(
            printed.warnings[0].to_string(),
            format!(
                "reversing the aliases of `f` did not finish within {REVERSAL_BOUND} applications; printed unreversed"
            )
        );
    });
}

#[test]
fn a_symbol_without_a_format_prints_as_kast_with_a_warning() {
    let unparser = synthetic(&format!("{F_OF_X}, {F_OF_G_OF_X}"), "alias'Kywd'{}()");
    let printed = unparser.print_kore(&pattern("Lblf{}(Lblh{}(Lbla{}()))"), &Options::default());
    assert_eq!(printed.text, "f ( h(a(.KList)) )");
    assert_eq!(
        printed.warnings,
        vec![Warning::Unprintable(vec!["Lblh".to_owned()])]
    );
    assert_eq!(
        printed.warnings[0].to_string(),
        "no production can print `h`; printed as KAST"
    );
}

#[test]
fn colours_follow_the_colors_list_and_report_a_short_list() {
    let unparser = synthetic(&format!("{F_OF_X}, {F_OF_G_OF_X}"), "alias'Kywd'{}()");
    let plain = unparser.print_kore(&pattern("Lblc{}()"), &Options::default());
    assert_eq!(plain.text, "c!");
    let colored = unparser.print_kore(&pattern("Lblc{}()"), &Options::default().with_color(true));
    assert_eq!(colored.text, "\x1b[38;5;196mc\x1b[0m!\x1b[0m");
    assert_eq!(
        colored.warnings,
        vec![Warning::ShortColors(vec!["Lblc".to_owned()])]
    );
}

#[test]
fn a_format_index_beyond_the_arguments_is_reported() {
    let unparser = synthetic(&format!("{F_OF_X}, {F_OF_G_OF_X}"), "alias'Kywd'{}()");
    let printed = unparser.print_kore(&pattern("Lblbad{}(Lbla{}())"), &Options::default());
    assert_eq!(printed.text, "bad ");
    assert_eq!(
        printed.warnings,
        vec![Warning::InvalidFormat(vec!["Lblbad".to_owned()])]
    );
}

#[test]
fn alphanumeric_order_compares_digit_runs_by_value() {
    use crate::abstract_term::alphanumeric;
    use std::cmp::Ordering::{Equal, Greater, Less};
    assert_eq!(alphanumeric("x2", "x10"), Less);
    assert_eq!(alphanumeric("x10", "x9"), Greater);
    assert_eq!(alphanumeric("b", "a1"), Greater);
    assert_eq!(alphanumeric("a", "a1"), Less);
    assert_eq!(alphanumeric("SetItem ( 100 )", "SetItem ( 9 )"), Greater);
    assert_eq!(alphanumeric("x", "x"), Equal);
}

#[test]
fn kore_names_decode_as_kprint_decodes_them() {
    assert_eq!(decode_kore("'Unds'Map'Unds'"), "_Map_");
    assert_eq!(decode_kore("'-LT-'k'-GT-'"), "<k>");
    assert_eq!(label_name("Lbl'Unds'Map'Unds'"), "_Map_");
    // kprint decodes `SCln` as `l`.
    assert_eq!(decode_kore("'SCln'"), "l");
    assert_eq!(
        enquote(b"a\"\\\n\t\x01\xc3"),
        "\"a\\\"\\\\\\n\\t\\x01\\xc3\""
    );
}

#[test]
fn result_floats_take_the_llvm_runtime_form_in_every_output() {
    let unparser = Unparser::from_kore(
        r#"[]
module FLOATS
  hooked-sort SortFloat{} [hook{}("FLOAT.Float")]
  sort SortText{} []
  sort SortExp{} []
  symbol Lblpair{}(SortFloat{}, SortText{}) : SortExp{} [format{}("pair ( %1 , %3 )"), terminals{}("110101")]
endmodule []
"#,
        "",
    )
    .expect("synthetic KORE");
    let native = pattern(
        r#"Lblpair{}(\dv{SortFloat{}}("-1.5000000000000000e+00p53x11"), \dv{SortText{}}("1.5p53x11"))"#,
    );
    let rewritten = unparser.llvm_floats(&native).expect("a Float to rewrite");
    // Only the domain value of the hooked Float sort changes.
    assert_eq!(
        rewritten.to_string(),
        r#"Lblpair{}(\dv{SortFloat{}}("-0.15000000000000000e1"), \dv{SortText{}}("1.5p53x11"))"#
    );
    // A result already in the LLVM form, or without a Float, is left as it is.
    assert!(unparser.llvm_floats(&rewritten).is_none());
    let printed = unparser.print_kore(&native, &Options::new(Mode::Pretty));
    assert!(
        printed.text.starts_with("pair ( -0.15000000000000000e1 ,"),
        "{}",
        printed.text
    );
}
