use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fs,
    path::Path,
};

use k_rust::{
    builtin,
    definition::{
        Associativity, Attributes, Definition, FlatImport, LabelHead, ProductionItem,
        ResolvedDefinition, Sentence, apply_sort_synonyms, expand_configurations,
    },
    inner::{ProgramParser, resolve_configuration_bubbles, resolve_rule_bubbles},
    kast::{Label, Sort, Term},
    outer::{
        Attribute, BubbleKind, SourceFile, SyntaxBody, extract_fenced_k_code, lower, parse,
    },
};
use serde_json::{Value, json};

const MAIN_MODULE: &str = "KRS-M3B-CALC";
const SYNTAX_MODULE: &str = "KRS-M3B-CALC-SYNTAX";
const ASSIGNMENT_LABEL: &str = "_=_;_KRS-M3B-CALC-SYNTAX_Stmt_Id_Expr";
const SEQUENCE_LABEL: &str = "___KRS-M3B-CALC-SYNTAX_Stmt_Stmt_Stmt";

fn main() {
    if let Err(error) = verify() {
        eprintln!("M3B native structural probe failed: {error}");
        std::process::exit(1);
    }
}

#[derive(Debug, Eq, PartialEq)]
enum CapabilityGap {
    StructuredDefinitionPreparation,
    NamedCellFrameIdentity,
    TypedBuiltinTermConstructors,
}

impl std::fmt::Display for CapabilityGap {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StructuredDefinitionPreparation => formatter.write_str(
                "k-rust 0.3.0 has no public invariant-preserving prepare_definition(Definition) API",
            ),
            Self::NamedCellFrameIdentity => formatter.write_str(
                "parsed cell ellipses are #dots/#noDots terms and carry no named frame identity",
            ),
            Self::TypedBuiltinTermConstructors => formatter.write_str(
                "KAST exposes generic Term::apply(String, ...), not typed Map/cell constructor APIs",
            ),
        }
    }
}

impl Error for CapabilityGap {}

struct Stages {
    outer_calc: SourceFile,
    parsed_configuration: Sentence,
    parsed_definition: Definition,
    resolved: ResolvedDefinition,
}

fn verify() -> Result<(), Box<dyn Error>> {
    let stages = prepare_public_stages()?;
    verify_outer_shapes(&stages.outer_calc)?;
    verify_syntax(&stages.parsed_definition)?;
    verify_configuration(&stages.parsed_configuration, &stages.parsed_definition)?;
    verify_rules(&stages.parsed_definition)?;
    verify_pin_catalog_and_map_unit(&stages.resolved)?;

    let gaps = [
        CapabilityGap::StructuredDefinitionPreparation,
        CapabilityGap::NamedCellFrameIdentity,
        CapabilityGap::TypedBuiltinTermConstructors,
    ];
    assert_eq!(gaps[0], CapabilityGap::StructuredDefinitionPreparation);

    println!("M3B native structural probe passed");
    println!("source: tests/m3b/fixtures/calc.k");
    println!("configuration: #cells(#configCell(k, $PGM:Stmt), #configCell(env, $ENV:Map))");
    println!("colors: k=green env=yellow");
    println!("rules: KRS-M3B-CALC.step,var,assign (structured Term trees)");
    println!("KSequence: Sequence([S1, S2]) and Sequence([])");
    println!("Map catalog: .Map=MAP.unit _|->_=MAP.element Map:update=MAP.update");
    println!("grammar: strict(2), right sequence, stmt > seq-stmt");
    for gap in gaps {
        println!("expected capability gap: {gap}");
    }
    Ok(())
}

fn prepare_public_stages() -> Result<Stages, Box<dyn Error>> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let calc_path = manifest.join("../../tests/m3b/fixtures/calc.k");
    let expr_path = manifest.join("../../tests/m3b/fixtures/expr.k");
    let calc_text = fs::read_to_string(&calc_path)?;
    let expr_text = fs::read_to_string(&expr_path)?;
    let outer_calc = parse(calc_path.display().to_string(), &calc_text)?;
    let outer_expr = parse(expr_path.display().to_string(), &expr_text)?;
    let outer_kast = parse_embedded_markdown("kast.md")?;
    let outer_domains = parse_embedded_markdown("domains.md")?;

    // `outer::lower_files` is intentionally private. A synthetic public
    // SourceFile preserves the one-global-tag-index invariant while using only
    // the public `outer::lower` entry point.
    let mut combined = SourceFile {
        source: "m3b-public-stage://combined".into(),
        requires: Vec::new(),
        modules: [outer_kast, outer_domains, outer_expr, outer_calc.clone()]
            .into_iter()
            .flat_map(|file| file.modules)
            .collect(),
    };
    combined.modules.retain(|module| !excluded_for_llvm(&module.attributes));
    let mut definition = lower(&combined, MAIN_MODULE)
        .map_err(|diagnostics| format!("outer lowering diagnostics: {diagnostics:#?}"))?;
    definition = apply_sort_synonyms(&definition)?;

    // This is the loader's documented implicit MAP import for a module with a
    // local configuration. The flat model exposes the required public fields.
    let main = module_mut(&mut definition, MAIN_MODULE)?;
    if !main.imports.iter().any(|import| import.name == "MAP") {
        main.imports.push(FlatImport {
            name: "MAP".into(),
            public: true,
        });
    }

    remove_dangling_excluded_imports(&mut definition);
    retain_main_import_closure(&mut definition)?;

    let with_configuration = resolve_configuration_bubbles(&definition)?;
    let parsed_configuration = module(&with_configuration, MAIN_MODULE)?
        .local_sentences
        .iter()
        .find(|sentence| matches!(sentence, Sentence::Configuration { .. }))
        .cloned()
        .ok_or("structured configuration sentence was not produced")?;
    let expanded = expand_configurations(&with_configuration)?;
    let parsed_definition = resolve_rule_bubbles(&expanded)?;
    let resolved = ResolvedDefinition::resolve(&parsed_definition)?;
    Ok(Stages {
        outer_calc,
        parsed_configuration,
        parsed_definition,
        resolved,
    })
}

fn parse_embedded_markdown(name: &str) -> Result<SourceFile, Box<dyn Error>> {
    let source = builtin::embedded(name).ok_or_else(|| format!("missing embedded {name}"))?;
    let code = extract_fenced_k_code(&source.text, "k")?;
    Ok(parse(source.source, &code)?)
}

fn excluded_for_llvm(attributes: &[Attribute]) -> bool {
    attributes
        .iter()
        .any(|attribute| matches!(attribute.key.as_str(), "symbolic" | "haskell"))
}

fn remove_dangling_excluded_imports(definition: &mut Definition) {
    let names = definition
        .modules
        .iter()
        .map(|module| module.name.clone())
        .collect::<BTreeSet<_>>();
    for module in &mut definition.modules {
        module.imports.retain(|import| names.contains(&import.name));
    }
}

fn retain_main_import_closure(definition: &mut Definition) -> Result<(), Box<dyn Error>> {
    let resolved = ResolvedDefinition::resolve(definition)?;
    let main = resolved.main_module_id();
    let mut names = resolved
        .transitive_imports(main)
        .into_iter()
        .map(|id| resolved.module(id).name.clone())
        .collect::<BTreeSet<_>>();
    names.insert(MAIN_MODULE.into());
    definition.modules.retain(|module| names.contains(&module.name));
    Ok(())
}

fn verify_outer_shapes(calc: &SourceFile) -> Result<(), Box<dyn Error>> {
    assert_eq!(calc.requires.len(), 1);
    assert_eq!(calc.requires[0].path, "expr.k");
    let syntax = calc
        .modules
        .iter()
        .find(|module| module.name == SYNTAX_MODULE)
        .ok_or("missing outer syntax module")?;
    let semantic = calc
        .modules
        .iter()
        .find(|module| module.name == MAIN_MODULE)
        .ok_or("missing outer semantic module")?;

    let right_blocks = syntax
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            k_rust::outer::Sentence::Syntax(declaration) => match &declaration.body {
                SyntaxBody::Productions(blocks) => Some(blocks),
                _ => None,
            },
            _ => None,
        })
        .flatten()
        .filter(|block| block.associativity == k_rust::outer::Associativity::Right)
        .count();
    assert_eq!(right_blocks, 1);

    let bubbles = semantic
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            k_rust::outer::Sentence::Bubble(bubble) => Some(bubble),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(bubbles.len(), 4);
    assert_eq!(bubbles[0].kind, BubbleKind::Configuration);
    assert_eq!(bubbles[0].label, None);
    assert!(bubbles[0].content.contains("color=\"green\""));
    assert!(bubbles[0].content.contains("color=\"yellow\""));
    assert_eq!(
        bubbles[1..]
            .iter()
            .map(|bubble| (bubble.kind, bubble.label.as_deref()))
            .collect::<Vec<_>>(),
        vec![
            (BubbleKind::Rule, Some("step")),
            (BubbleKind::Rule, Some("var")),
            (BubbleKind::Rule, Some("assign")),
        ]
    );
    assert!(bubbles[1..].iter().all(|bubble| bubble.content.contains("...")));
    Ok(())
}

fn verify_syntax(definition: &Definition) -> Result<(), Box<dyn Error>> {
    let syntax = module(definition, SYNTAX_MODULE)?;
    let expr_from_id = Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: sort("Expr"),
        items: vec![nonterminal("Id")],
        attributes: Attributes::default(),
    };
    let assignment = Sentence::Production {
        label: Some(Label::new(ASSIGNMENT_LABEL)),
        parameters: Vec::new(),
        sort: sort("Stmt"),
        items: vec![
            nonterminal("Id"),
            ProductionItem::Terminal("=".into()),
            nonterminal("Expr"),
            ProductionItem::Terminal(";".into()),
        ],
        attributes: attrs([
            ("format", json!("%1 %2 %3%4")),
            ("group", json!("stmt")),
            ("strict", json!("2")),
        ]),
    };
    let sequence = Sentence::Production {
        label: Some(Label::new(SEQUENCE_LABEL)),
        parameters: Vec::new(),
        sort: sort("Stmt"),
        items: vec![nonterminal("Stmt"), nonterminal("Stmt")],
        attributes: attrs([
            ("format", json!("%1%n%2")),
            ("group", json!("seq-stmt")),
        ]),
    };
    let right = Sentence::SyntaxAssociativity {
        associativity: Associativity::Right,
        tags: vec![SEQUENCE_LABEL.into()],
        attributes: Attributes::default(),
    };
    let priority = Sentence::SyntaxPriority {
        priorities: vec![vec![ASSIGNMENT_LABEL.into()], vec![SEQUENCE_LABEL.into()]],
        attributes: Attributes::default(),
    };
    for expected in [expr_from_id, assignment, sequence, right, priority] {
        let actual = syntax
            .local_sentences
            .iter()
            .find(|candidate| normalized((*candidate).clone()) == expected)
            .ok_or_else(|| format!("missing normalized syntax node {expected:#?}"))?;
        assert_eq!(normalized(actual.clone()), expected);
    }
    Ok(())
}

fn verify_configuration(
    parsed: &Sentence,
    expanded: &Definition,
) -> Result<(), Box<dyn Error>> {
    let expected = Sentence::Configuration {
        body: app(
            "#cells",
            vec![
                config_cell("k", "green", "Stmt", "$PGM"),
                config_cell("env", "yellow", "Map", "$ENV"),
            ],
        ),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    assert_eq!(normalized(parsed.clone()), expected);

    let mut config_vars = Vec::new();
    visit_term(sentence_body(parsed).ok_or("configuration had no body")?, &mut |term| {
        if let Term::Token { token, sort } = term.unannotated()
            && sort.name == "KConfigVar"
        {
            config_vars.push(token.clone());
        }
    });
    assert_eq!(config_vars, ["$PGM", "$ENV"]);

    let main = module(expanded, MAIN_MODULE)?;
    for (label, cell_name, color, main_cell) in [
        ("<k>", "k", "green", true),
        ("<env>", "env", "yellow", false),
    ] {
        let attributes = main
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Production {
                    label: Some(candidate),
                    attributes,
                    ..
                } if candidate.name == label => Some(attributes),
                _ => None,
            })
            .ok_or_else(|| format!("missing generated cell production {label}"))?;
        assert_eq!(attributes.get_str("cellName"), Some(cell_name));
        assert_eq!(attributes.get_str("color"), Some(color));
        assert_eq!(attributes.get("maincell").is_some(), main_cell);
    }
    Ok(())
}

fn verify_rules(definition: &Definition) -> Result<(), Box<dyn Error>> {
    let module = module(definition, MAIN_MODULE)?;
    let expected = [expected_step(), expected_var(), expected_assign()];
    let actual = module
        .local_sentences
        .iter()
        .filter(|sentence| {
            matches!(sentence, Sentence::Rule { attributes, .. }
                if attributes.get_str("label").is_some_and(|label| label.starts_with("KRS-M3B-CALC.")))
        })
        .cloned()
        .map(normalized)
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);

    let step_body = sentence_body(&actual[0]).ok_or("step had no body")?;
    assert!(contains_sequence(step_body, 2));
    let assign_body = sentence_body(&actual[2]).ok_or("assign had no body")?;
    assert!(contains_sequence(assign_body, 0));
    assert!(contains_label(&actual[1], "_|->_"));
    assert!(contains_label(&actual[2], "Map:update"));
    assert_eq!(count_label(&actual[0], "#dots"), 1);
    assert_eq!(count_label(&actual[1], "#dots"), 2);
    assert_eq!(count_label(&actual[2], "#dots"), 1);
    Ok(())
}

fn verify_pin_catalog_and_map_unit(resolved: &ResolvedDefinition) -> Result<(), Box<dyn Error>> {
    let module_id = resolved
        .module_id(MAIN_MODULE)
        .ok_or("resolved main module disappeared")?;
    let catalog = resolved.production_catalog(module_id);
    for (label, hook) in [
        (".Map", "MAP.unit"),
        ("_|->_", "MAP.element"),
        ("Map:update", "MAP.update"),
    ] {
        let head = LabelHead::new(label);
        assert!(!catalog.productions_for(&head).is_empty(), "missing {label}");
        assert_eq!(
            catalog.attributes_for(&head).and_then(|attrs| attrs.get_str("hook")),
            Some(hook)
        );
    }
    for label in [
        ASSIGNMENT_LABEL,
        SEQUENCE_LABEL,
        "#cells",
        "#dots",
        "#noDots",
        "<k>",
        "<env>",
    ] {
        assert!(
            !catalog
                .productions_for(&LabelHead::new(label))
                .is_empty(),
            "pin catalog did not define {label}"
        );
    }

    let parser = ProgramParser::from_resolved(resolved, MAIN_MODULE)?;
    let parsed_unit = parser.parse(&sort("Map"), ".Map")?;
    assert_eq!(parsed_unit, app(".Map", Vec::new()));
    Ok(())
}

fn expected_step() -> Sentence {
    let first = cast("Stmt", variable("S1"));
    let second = cast("Stmt", variable("S2"));
    rule(
        "KRS-M3B-CALC.step",
        cell(
            "k",
            rewrite(
                app(SEQUENCE_LABEL, vec![first.clone(), second.clone()]),
                Term::sequence([first, second]),
            ),
            false,
            true,
        ),
    )
}

fn expected_var() -> Sentence {
    let name = cast("Id", variable("X"));
    let value = cast("K", variable("V"));
    rule(
        "KRS-M3B-CALC.var",
        app(
            "#cells",
            vec![
                cell("k", rewrite(name.clone(), value.clone()), false, true),
                cell("env", app("_|->_", vec![name, value]), false, true),
            ],
        ),
    )
}

fn expected_assign() -> Sentence {
    let name = cast("Id", variable("X"));
    let value = cast("Value", variable("V"));
    let environment = cast("Map", variable("E"));
    rule(
        "KRS-M3B-CALC.assign",
        app(
            "#cells",
            vec![
                cell(
                    "k",
                    rewrite(
                        app(ASSIGNMENT_LABEL, vec![name.clone(), value.clone()]),
                        Term::sequence([]),
                    ),
                    false,
                    true,
                ),
                cell(
                    "env",
                    rewrite(
                        environment.clone(),
                        app("Map:update", vec![environment, name, value]),
                    ),
                    false,
                    false,
                ),
            ],
        ),
    )
}

fn rule(label: &str, body: Term) -> Sentence {
    Sentence::Rule {
        body,
        requires: truth(),
        ensures: truth(),
        attributes: attrs([("label", json!(label))]),
    }
}

fn config_cell(name: &str, color: &str, value_sort: &str, variable_name: &str) -> Term {
    app(
        "#configCell",
        vec![
            token(name, "#CellName"),
            app(
                "#cellPropertyList",
                vec![
                    app(
                        "#cellProperty",
                        vec![
                            token("color", "#CellName"),
                            token(&format!("\"{color}\""), "KString"),
                        ],
                    ),
                    app("#cellPropertyListTerminator", Vec::new()),
                ],
            ),
            cast(value_sort, token(variable_name, "KConfigVar")),
            token(name, "#CellName"),
        ],
    )
}

fn cell(name: &str, contents: Term, open_left: bool, open_right: bool) -> Term {
    app(
        format!("<{name}>"),
        vec![
            app(if open_left { "#dots" } else { "#noDots" }, Vec::new()),
            contents,
            app(if open_right { "#dots" } else { "#noDots" }, Vec::new()),
        ],
    )
}

fn cast(target: &str, term: Term) -> Term {
    app(format!("#SemanticCastTo{target}"), vec![term])
}

fn app(label: impl Into<String>, arguments: Vec<Term>) -> Term {
    Term::Apply {
        label: Label::new(label),
        arguments,
    }
}

fn rewrite(left: Term, right: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn variable(name: &str) -> Term {
    Term::variable(name)
}

fn token(value: &str, sort_name: &str) -> Term {
    Term::Token {
        token: value.into(),
        sort: sort(sort_name),
    }
}

fn truth() -> Term {
    token("true", "Bool")
}

fn sort(name: &str) -> Sort {
    Sort::new(name)
}

fn nonterminal(name: &str) -> ProductionItem {
    ProductionItem::NonTerminal {
        sort: sort(name),
        name: None,
    }
}

fn attrs<const N: usize>(entries: [(&str, Value); N]) -> Attributes {
    Attributes::new(
        entries
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn normalized(mut sentence: Sentence) -> Sentence {
    let attributes = match &mut sentence {
        Sentence::SyntaxSort { attributes, .. }
        | Sentence::SortSynonym { attributes, .. }
        | Sentence::SyntaxLexical { attributes, .. }
        | Sentence::Production { attributes, .. }
        | Sentence::SyntaxAssociativity { attributes, .. }
        | Sentence::SyntaxPriority { attributes, .. }
        | Sentence::ContextAlias { attributes, .. }
        | Sentence::Context { attributes, .. }
        | Sentence::Rule { attributes, .. }
        | Sentence::Claim { attributes, .. }
        | Sentence::Configuration { attributes, .. }
        | Sentence::Bubble { attributes, .. } => attributes,
    };
    let semantic = attributes
        .entries()
        .iter()
        .filter(|(key, _)| {
            !matches!(
                key.as_str(),
                "org.kframework.attributes.Location"
                    | "org.kframework.attributes.Source"
                    | "contentStartLine"
                    | "contentStartColumn"
            )
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect();
    *attributes = Attributes::new(semantic);
    sentence
}

fn module<'a>(
    definition: &'a Definition,
    name: &str,
) -> Result<&'a k_rust::definition::FlatModule, Box<dyn Error>> {
    definition
        .modules
        .iter()
        .find(|module| module.name == name)
        .ok_or_else(|| format!("missing module {name}").into())
}

fn module_mut<'a>(
    definition: &'a mut Definition,
    name: &str,
) -> Result<&'a mut k_rust::definition::FlatModule, Box<dyn Error>> {
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == name)
        .ok_or_else(|| format!("missing module {name}").into())
}

fn sentence_body(sentence: &Sentence) -> Option<&Term> {
    match sentence {
        Sentence::Rule { body, .. }
        | Sentence::Claim { body, .. }
        | Sentence::Context { body, .. }
        | Sentence::ContextAlias { body, .. }
        | Sentence::Configuration { body, .. } => Some(body),
        _ => None,
    }
}

fn visit_term(term: &Term, visitor: &mut impl FnMut(&Term)) {
    visitor(term);
    match term.unannotated() {
        Term::Rewrite { left, right } | Term::As { pattern: left, alias: right } => {
            visit_term(left, visitor);
            visit_term(right, visitor);
        }
        Term::Sequence(items) | Term::Apply { arguments: items, .. } => {
            for item in items {
                visit_term(item, visitor);
            }
        }
        Term::Annotated { .. } => unreachable!("unannotated removed annotations"),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
    }
}

fn contains_sequence(term: &Term, length: usize) -> bool {
    let mut found = false;
    visit_term(term, &mut |candidate| {
        found |= matches!(candidate.unannotated(), Term::Sequence(items) if items.len() == length);
    });
    found
}

fn contains_label(sentence: &Sentence, label: &str) -> bool {
    count_label(sentence, label) != 0
}

fn count_label(sentence: &Sentence, wanted: &str) -> usize {
    let Some(body) = sentence_body(sentence) else {
        return 0;
    };
    let mut count = 0;
    visit_term(body, &mut |term| {
        if matches!(term.unannotated(), Term::Apply { label, .. } if label.name == wanted) {
            count += 1;
        }
    });
    count
}

#[cfg(test)]
mod tests {
    #[test]
    fn public_native_shapes_match_calc_source() {
        super::verify().unwrap();
    }
}
