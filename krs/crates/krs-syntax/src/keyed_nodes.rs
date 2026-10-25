//! The keyed nodes of a sentence, read back from the AST.
//!
//! A sentence's keying pass stores each key it hands out on the node the key
//! names and records that node's anchor, so the anchors are a projection of
//! the keyed AST. Each sentence type's `keyed_nodes` walk reads the stored
//! keys back, pairing each with the range of the node that holds it, taken
//! from the node. The round-trip test below checks the projection both ways
//! on every krs-syntax fixture and every port source.

use krs_ir::ProvenanceKey;
use quote::ToTokens;

use crate::{ProvenanceAnchor, SyntaxError, TokenRange};

/// The keys stored on a sentence's nodes, each with its node's range.
#[derive(Debug, Default)]
pub(crate) struct KeyedNodes {
    nodes: Vec<(ProvenanceKey, TokenRange)>,
}

impl KeyedNodes {
    /// Records the key a node holds, if it holds one, with the node's range.
    pub(crate) fn push(&mut self, key: Option<&ProvenanceKey>, range: TokenRange) {
        if let Some(key) = key {
            self.nodes.push((key.clone(), range));
        }
    }

    /// Records the key a node holds, if it holds one, with the range of the
    /// node's tokens.
    pub(crate) fn push_tokens(
        &mut self,
        key: Option<&ProvenanceKey>,
        node: &impl ToTokens,
    ) -> Result<(), SyntaxError> {
        if key.is_some() {
            self.push(key, TokenRange::for_tokens(node)?);
        }
        Ok(())
    }

    /// Records every key a node holds, each with the node's range.
    pub(crate) fn push_all<'a>(
        &mut self,
        keys: impl IntoIterator<Item = &'a ProvenanceKey>,
        range: TokenRange,
    ) {
        for key in keys {
            self.push(Some(key), range);
        }
    }

    /// The keyed nodes recorded so far.
    pub(crate) fn into_nodes(self) -> Vec<(ProvenanceKey, TokenRange)> {
        self.nodes
    }
}

/// Collects a sentence's keyed nodes with `walk`.
pub(crate) fn keyed_nodes(
    walk: impl FnOnce(&mut KeyedNodes) -> Result<(), SyntaxError>,
) -> Vec<(ProvenanceKey, TokenRange)> {
    let mut nodes = KeyedNodes::default();
    walk(&mut nodes).expect("a keyed node has authored tokens");
    nodes.into_nodes()
}

/// A node's key and the line and column of its first and last leaves.
type Located = (ProvenanceKey, (usize, usize), (usize, usize));

fn located(key: ProvenanceKey, range: TokenRange) -> Located {
    let (start, end) = (range.start(), range.end());
    (key, (start.line, start.column), (end.line, end.column))
}

/// The disagreements between a sentence's anchors and its keyed nodes:
/// an anchor whose key no node holds at the anchor's range, a key a node
/// holds that no anchor records, or records at another range, and a key
/// two anchors record.
pub(crate) fn round_trip_errors(
    anchors: &[ProvenanceAnchor],
    nodes: &[(ProvenanceKey, TokenRange)],
) -> Vec<String> {
    let anchors = anchors
        .iter()
        .map(|anchor| located(anchor.key(), anchor.range()))
        .collect::<Vec<_>>();
    let nodes = nodes
        .iter()
        .map(|(key, range)| located(key.clone(), *range))
        .collect::<Vec<_>>();
    let mut errors = Vec::new();
    for anchor in &anchors {
        if anchors.iter().filter(|other| other.0 == anchor.0).count() > 1 {
            errors.push(format!("two anchors record {anchor:?}"));
        }
        if !nodes.contains(anchor) {
            errors.push(format!("no node holds the anchor {anchor:?}"));
        }
    }
    for node in &nodes {
        if !anchors.contains(node) {
            errors.push(format!("no anchor records the keyed node {node:?}"));
        }
    }
    errors.dedup();
    errors
}

mod tests {
    use std::fmt::Write as _;
    use std::path::{Path, PathBuf};

    use proc_macro2::TokenStream;
    use syn::visit::Visit;
    use syn::{Attribute, ImplItem, Item, Meta};

    use super::{KeyedNodes, keyed_nodes, round_trip_errors};
    use crate::parse::KrsSyntax;
    use crate::surface::{
        AttributeMacro, AuthoredResolver, Entry, FunctionMacro, Invocation, InvocationKind,
        Resolve, invocations, item_owners,
    };
    use crate::{
        AliasAttribute, AssociativityDeclaration, BracketAttribute, CellAttributePayload,
        ClaimAttribute, ClaimBlock, ConfigurationAttribute, ConfigurationDeclaration, ConstantItem,
        ConstructorAttribute, ConstructorDeclaration, ConstructorsAttribute, ContextAliasAttribute,
        ContextAttribute, DesugarAttribute, EnumConstructorDeclaration, EquationAttribute,
        EquationTable, ExistsAttribute, FunctionAttribute, FunctionShorthand, InitializerFunction,
        LayoutDeclaration, LexicalDeclaration, PrecedenceDeclaration, ProductionAttribute,
        ProductionItem, ProvenanceAnchor, RawKItem, RuleAttribute, RuleBlock, RuleClause,
        RuleDescriptor, RuleItem, RuleSentence, ShorthandItem, SimplificationAttribute,
        SortAttribute, SortsDeclaration, SortsEntry, SpecModuleAttribute, SpecModuleItem,
        StateClaimItem, StateContextAliasItem, StateRuleItem, StateTerm, StaticMode,
        StaticProductionAttribute, SubsortAttribute, SubsortDeclaration, SymbolAttribute,
        SyntaxError, SyntaxListAttribute, SyntaxListDeclaration, TermExpression, TokenAttribute,
        TokenDeclaration, TokenStack, VariantSyntaxAttribute, parse_cells_expression,
        parse_cells_pattern, parse_k_sequence_expression, parse_k_sequence_pattern,
        parse_map_expression, parse_map_pattern, parse_seqstrict_attribute, parse_strict_attribute,
    };

    /// The sentences and descriptors checked so far, and their
    /// disagreements.
    #[derive(Default)]
    struct RoundTrip {
        sentences: usize,
        descriptors: usize,
        anchors: usize,
        failures: String,
    }

    impl RoundTrip {
        /// Checks the anchors of one sentence against the nodes `walk` reads
        /// back from its AST.
        fn sentence(
            &mut self,
            label: &str,
            anchors: Result<Vec<ProvenanceAnchor>, SyntaxError>,
            walk: impl FnOnce(&mut KeyedNodes) -> Result<(), SyntaxError>,
        ) {
            self.sentences += 1;
            self.check(label, anchors, walk);
        }

        /// Checks the anchors of one descriptor, composed of several
        /// sentences, against the nodes `walk` reads back from their ASTs.
        fn descriptor(
            &mut self,
            label: &str,
            anchors: Result<Vec<ProvenanceAnchor>, SyntaxError>,
            walk: impl FnOnce(&mut KeyedNodes) -> Result<(), SyntaxError>,
        ) {
            self.descriptors += 1;
            self.check(label, anchors, walk);
        }

        fn check(
            &mut self,
            label: &str,
            anchors: Result<Vec<ProvenanceAnchor>, SyntaxError>,
            walk: impl FnOnce(&mut KeyedNodes) -> Result<(), SyntaxError>,
        ) {
            let anchors = anchors.unwrap_or_else(|error| panic!("{label}: {error:?}"));
            self.anchors += anchors.len();
            for error in round_trip_errors(&anchors, &keyed_nodes(walk)) {
                writeln!(self.failures, "{label}: {error}").unwrap();
            }
        }

        /// Checks a view whose anchors are the first of `full`'s: a view of
        /// a sentence keyed by one pass, whose nodes hold the full view's
        /// keys. `full` itself is checked both ways.
        fn prefix(&mut self, label: &str, view: &[ProvenanceAnchor], full: &[ProvenanceAnchor]) {
            let prefix = view.len() <= full.len()
                && view.iter().zip(full).all(|(view, full)| {
                    let (left, right) = (view.range(), full.range());
                    view.key() == full.key()
                        && left.start() == right.start()
                        && left.end() == right.end()
                });
            if !prefix {
                writeln!(
                    self.failures,
                    "{label}: a view is not a prefix of its full view"
                )
                .unwrap();
            }
        }
    }

    /// The anchors of a term standing alone: its two views project them by
    /// role, and together they are every anchor its keying recorded.
    fn term_anchors(term: &TermExpression) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = term.provenance()?;
        for anchor in term.full_provenance()? {
            if !anchors.iter().any(|other| other.key() == anchor.key()) {
                anchors.push(anchor);
            }
        }
        Ok(anchors)
    }

    /// Checks the states a `cells!` standing alone holds: a configuration
    /// standing alone keys none of its values, each of which was keyed as
    /// a sentence of its own when it was parsed.
    fn embedded_state(state: &StateTerm, label: &str, round_trip: &mut RoundTrip) {
        match state {
            StateTerm::Term(term) | StateTerm::Group(term) => {
                round_trip.sentence(label, term_anchors(term), |nodes| term.keyed_nodes(nodes));
            }
            StateTerm::KSequence(sequence) => {
                round_trip.sentence(label, sequence.provenance(), |nodes| {
                    sequence.keyed_nodes(nodes)
                });
            }
            StateTerm::Map(map) => {
                round_trip.sentence(label, map.provenance(), |nodes| map.keyed_nodes(nodes));
            }
            StateTerm::Present(_) | StateTerm::Absent(_) | StateTerm::Instances(_) => {
                for nested in state.nested_states() {
                    embedded_state(nested, label, round_trip);
                }
            }
        }
    }

    /// Checks a readable clause, its metadata attribute, and the descriptor
    /// they make.
    fn clause(clause: &RuleClause, label: &str, round_trip: &mut RoundTrip) {
        let attribute = |nodes: &mut KeyedNodes| match clause.claim() {
            Some(claim) => claim.keyed_nodes(nodes),
            None => clause.attribute().keyed_nodes(nodes),
        };
        round_trip.sentence(label, clause.provenance(), |nodes| {
            clause.keyed_nodes(nodes)
        });
        round_trip.sentence(label, clause.attribute_provenance(), attribute);
        round_trip.descriptor(label, clause.descriptor_provenance(), |nodes| {
            clause.keyed_nodes(nodes)?;
            attribute(nodes)
        });
    }

    /// Checks a rule item as a sentence of its own: its full view both
    /// ways, and its catalog view as a prefix of the full view.
    fn rule_item(rule: &RuleItem, label: &str, round_trip: &mut RoundTrip) {
        let full = rule.full_provenance().unwrap();
        round_trip.prefix(label, &rule.provenance().unwrap(), &full);
        round_trip.sentence(label, Ok(full), |nodes| rule.keyed_nodes(nodes));
    }

    /// Records the keys of the attribute that makes a rule fn `sentence`.
    fn rule_sentence_nodes(
        sentence: RuleSentence<'_>,
        nodes: &mut KeyedNodes,
    ) -> Result<(), SyntaxError> {
        match sentence {
            RuleSentence::Transition(attribute) => attribute.keyed_nodes(nodes),
            RuleSentence::Context(context) => context.keyed_nodes(nodes),
            RuleSentence::Equation(equation) => equation.keyed_nodes(nodes),
            RuleSentence::Simplification(simplification) => simplification.keyed_nodes(nodes),
            RuleSentence::Alias => Ok(()),
            RuleSentence::Desugar(desugar) => desugar.keyed_nodes(nodes),
        }
    }

    /// Checks the descriptor of a rule fn whose sides are terms.
    fn rule_descriptor(
        rule: &RuleItem,
        sentence: RuleSentence<'_>,
        label: &str,
        round_trip: &mut RoundTrip,
    ) {
        rule_item(rule, label, round_trip);
        let descriptor = RuleDescriptor::new(rule, sentence).unwrap();
        round_trip.descriptor(label, Ok(descriptor.anchors().to_vec()), |nodes| {
            rule.keyed_nodes(nodes)?;
            rule_sentence_nodes(sentence, nodes)?;
            nodes.push_tokens(descriptor.marker_key(), &rule.item().sig.ident)
        });
    }

    /// Checks the descriptor of a rule fn whose sides are configurations.
    fn state_rule_descriptor(
        rule: &StateRuleItem,
        sentence: RuleSentence<'_>,
        label: &str,
        round_trip: &mut RoundTrip,
    ) {
        round_trip.sentence(label, rule.provenance(), |nodes| rule.keyed_nodes(nodes));
        let descriptor = RuleDescriptor::state(rule, sentence).unwrap();
        round_trip.descriptor(label, Ok(descriptor.anchors().to_vec()), |nodes| {
            rule.keyed_nodes(nodes)?;
            rule_sentence_nodes(sentence, nodes)?;
            nodes.push_tokens(descriptor.marker_key(), &rule.item().sig.ident)
        });
    }

    /// Checks the two descriptors of a production struct, and its pieces.
    /// The grammar descriptor holds the keys of the two kinds of node it
    /// anchors that no parsed piece holds: a total function's name as its
    /// declaration and a static marker's name.
    fn production(production: &ProductionItem<'_>, label: &str, round_trip: &mut RoundTrip) {
        let attribute = production.attribute.production();
        let declaration = production.declaration;
        let full = attribute.full_provenance().unwrap();
        round_trip.prefix(label, &attribute.provenance().unwrap(), &full);
        round_trip.sentence(label, Ok(full), |nodes| attribute.keyed_nodes(nodes));
        round_trip.sentence(label, attribute.sort_argument_provenance(), |nodes| {
            attribute.keyed_sort_argument_nodes(nodes)
        });
        constructor_declaration(declaration, label, round_trip);
        if let ProductionAttribute::Function(function) = production.attribute {
            round_trip.sentence(label, function.provenance(), |nodes| {
                function.keyed_nodes(nodes)
            });
        }
        round_trip.descriptor(label, production.constructor_provenance(), |nodes| {
            attribute.keyed_compact_nodes(nodes)?;
            declaration.keyed_compact_nodes(nodes)?;
            attribute.keyed_sort_argument_nodes(nodes)?;
            declaration.keyed_argument_nodes(nodes)?;
            if let Some(symbol) = production.symbol {
                symbol.keyed_nodes(nodes)?;
            }
            Ok(())
        });
        let grammar = production.grammar_descriptor().unwrap();
        round_trip.descriptor(label, Ok(grammar.anchors().to_vec()), |nodes| {
            attribute.keyed_nodes(nodes)?;
            declaration.keyed_nodes(nodes)?;
            if let Some(symbol) = production.symbol {
                symbol.keyed_nodes(nodes)?;
            }
            for ((marker, name), key) in production
                .static_markers
                .iter()
                .zip(grammar.marker_name_keys())
            {
                nodes.push_tokens(Some(key), name)?;
                marker.keyed_nodes(nodes);
            }
            if let ProductionAttribute::Function(function) = production.attribute {
                nodes.push_tokens(grammar.function_declaration_key(), declaration.name())?;
                function.keyed_function_nodes(nodes)?;
            }
            for strictness in production.strictness {
                strictness.keyed_nodes(nodes)?;
            }
            Ok(())
        });
    }

    /// Checks a struct's three views: the full one both ways, the compact
    /// one as its prefix, and the element types of its field sorts.
    fn constructor_declaration(
        declaration: &ConstructorDeclaration,
        label: &str,
        round_trip: &mut RoundTrip,
    ) {
        let full = declaration.full_provenance().unwrap();
        round_trip.prefix(label, &declaration.provenance().unwrap(), &full);
        round_trip.sentence(label, Ok(full), |nodes| declaration.keyed_nodes(nodes));
        round_trip.sentence(label, declaration.argument_provenance(), |nodes| {
            declaration.keyed_argument_nodes(nodes)
        });
    }

    /// Checks an enum's variants (their two descriptors) and its precedence
    /// and associativity descriptors.
    fn enum_constructors(
        declaration: &EnumConstructorDeclaration,
        label: &str,
        round_trip: &mut RoundTrip,
    ) {
        for variant in declaration.variants() {
            round_trip.sentence(label, declaration.variant_provenance(variant), |nodes| {
                variant.keyed_nodes(nodes)
            });
            round_trip.sentence(label, variant.argument_provenance(), |nodes| {
                variant.keyed_argument_nodes(nodes)
            });
            round_trip.descriptor(label, variant.constructor_provenance(), |nodes| {
                variant.keyed_nodes(nodes)?;
                variant.keyed_argument_nodes(nodes)
            });
        }
        if let Some(anchors) = declaration.precedence_provenance().unwrap() {
            round_trip.sentence(label, Ok(anchors), |nodes| {
                declaration.keyed_precedence_nodes(nodes);
                Ok(())
            });
        }
        if let Some(anchors) = declaration.associativity_provenance().unwrap() {
            round_trip.sentence(label, Ok(anchors), |nodes| {
                declaration.keyed_associativity_nodes(nodes);
                Ok(())
            });
        }
    }

    /// Checks a syntactic list's three descriptors.
    fn syntax_list(declaration: &SyntaxListDeclaration, label: &str, round_trip: &mut RoundTrip) {
        round_trip.sentence(label, declaration.sort_provenance(), |nodes| {
            declaration.keyed_sort_nodes(nodes)
        });
        round_trip.sentence(label, declaration.cons_provenance(), |nodes| {
            declaration.keyed_cons_nodes(nodes)
        });
        round_trip.sentence(label, declaration.terminator_provenance(), |nodes| {
            declaration.keyed_terminator_nodes(nodes)
        });
    }

    /// Checks a `sorts!` block's sorts, their brackets, and its memberships.
    fn sorts(declaration: &SortsDeclaration, label: &str, round_trip: &mut RoundTrip) {
        for entry in declaration.entries() {
            match entry {
                SortsEntry::Sort(sort) => {
                    round_trip.sentence(label, sort.provenance(), |nodes| sort.keyed_nodes(nodes));
                    for (index, (_, anchors)) in sort.bracket_descriptors().enumerate() {
                        round_trip.descriptor(label, Ok(anchors.to_vec()), |nodes| {
                            sort.keyed_bracket_nodes(index, nodes)
                        });
                    }
                }
                SortsEntry::Membership(membership) => {
                    for (index, (_, anchors)) in membership.member_descriptors().enumerate() {
                        round_trip.sentence(label, Ok(anchors.to_vec()), |nodes| {
                            membership.keyed_member_nodes(index, nodes)
                        });
                    }
                }
            }
        }
    }

    /// Checks a token carrier's stack and the stack's descriptor, and a
    /// token struct's sort declaration.
    fn token(token: &TokenDeclaration, stack: &TokenStack, label: &str, rt: &mut RoundTrip) {
        rt.sentence(label, token.provenance(), |nodes| token.keyed_nodes(nodes));
        rt.sentence(label, token.sort_provenance(), |nodes| {
            token.keyed_sort_nodes(nodes)
        });
        rt.sentence(label, stack.provenance(), |nodes| stack.keyed_nodes(nodes));
        rt.descriptor(label, stack.descriptor_provenance(token), |nodes| {
            stack.keyed_nodes(nodes)?;
            token.keyed_nodes(nodes)
        });
    }

    /// Checks every sentence parser that accepts `source`.
    #[expect(
        clippy::too_many_lines,
        reason = "One check per sentence parser, as the parsers are listed."
    )]
    fn fixture_sentences(source: &str, label: &str, round_trip: &mut RoundTrip) {
        /// Checks the one view of each sentence that `$type` parses.
        macro_rules! sentences {
            ($($type:ty),* $(,)?) => {$(
                if let Ok(value) = <$type>::parse_source(source) {
                    let label = format!("{label} {}", stringify!($type));
                    round_trip.sentence(&label, value.provenance(), |nodes| {
                        value.keyed_nodes(nodes)
                    });
                }
            )*};
        }
        sentences!(
            RuleAttribute,
            ClaimAttribute,
            ExistsAttribute,
            StateRuleItem,
            StateClaimItem,
            InitializerFunction,
            ConfigurationDeclaration,
            RawKItem,
            ConstantItem,
            LexicalDeclaration,
            LayoutDeclaration,
            TokenDeclaration,
            PrecedenceDeclaration,
            AssociativityDeclaration,
            BracketAttribute,
            TokenAttribute,
            FunctionAttribute,
            VariantSyntaxAttribute,
            SymbolAttribute,
            EquationAttribute,
            SimplificationAttribute,
            DesugarAttribute,
            ContextAliasAttribute,
            ConfigurationAttribute,
            CellAttributePayload,
            SpecModuleAttribute,
            SyntaxListAttribute,
        );
        let label = |name: &str| format!("{label} {name}");
        if let Ok(value) = TermExpression::parse_source(source) {
            round_trip.sentence(&label("term"), term_anchors(&value), |nodes| {
                value.keyed_nodes(nodes)
            });
        }
        if let Ok(value) = RuleItem::parse_source(source) {
            rule_item(&value, &label("rule"), round_trip);
        }
        if let Ok(value) = TokenDeclaration::parse_source(source) {
            round_trip.sentence(&label("token"), value.sort_provenance(), |nodes| {
                value.keyed_sort_nodes(nodes)
            });
        }
        if let Ok(value) = ConstructorDeclaration::parse_source(source) {
            constructor_declaration(&value, &label("constructor"), round_trip);
        }
        if let Ok(value) = ConstructorAttribute::parse_source(source) {
            let full = value.full_provenance().unwrap();
            round_trip.prefix(&label("constructor"), &value.provenance().unwrap(), &full);
            round_trip.sentence(&label("constructor"), Ok(full), |nodes| {
                value.keyed_nodes(nodes)
            });
            round_trip.sentence(
                &label("constructor"),
                value.sort_argument_provenance(),
                |nodes| value.keyed_sort_argument_nodes(nodes),
            );
        }
        if let Ok(value) = EnumConstructorDeclaration::parse_source(source) {
            enum_constructors(&value, &label("enum"), round_trip);
        }
        if let Ok(value) = RuleBlock::parse_source(source) {
            for item in value.clauses() {
                clause(item, &label("rules"), round_trip);
            }
        }
        if let Ok(value) = ClaimBlock::parse_source(source) {
            for item in value.clauses() {
                clause(item, &label("claims"), round_trip);
            }
        }
        if let Ok(value) = EquationTable::parse_source(source) {
            for row in value.rows() {
                round_trip.descriptor(
                    &label("equations"),
                    row.descriptor().map(|row| row.anchors().to_vec()),
                    |nodes| row.keyed_nodes(nodes),
                );
            }
        }
        if let Ok(value) = SortsDeclaration::parse_source(source) {
            sorts(&value, &label("sorts"), round_trip);
        }
        let Ok(tokens) = source.parse::<TokenStream>() else {
            return;
        };
        for (name, value) in [
            (
                "k_sequence_pattern",
                parse_k_sequence_pattern(tokens.clone()),
            ),
            (
                "k_sequence_expression",
                parse_k_sequence_expression(tokens.clone()),
            ),
        ] {
            if let Ok(value) = value {
                round_trip.sentence(&label(name), value.provenance(), |nodes| {
                    value.keyed_nodes(nodes)
                });
            }
        }
        for (name, value) in [
            ("map_pattern", parse_map_pattern(tokens.clone())),
            ("map_expression", parse_map_expression(tokens.clone())),
        ] {
            if let Ok(value) = value {
                round_trip.sentence(&label(name), value.provenance(), |nodes| {
                    value.keyed_nodes(nodes)
                });
            }
        }
        for (name, value) in [
            ("cells_pattern", parse_cells_pattern(tokens.clone())),
            ("cells_expression", parse_cells_expression(tokens.clone())),
        ] {
            if let Ok(value) = value {
                let label = label(name);
                round_trip.sentence(&label, value.provenance(), |nodes| value.keyed_nodes(nodes));
                for entry in value.entries() {
                    embedded_state(entry.value(), &label, round_trip);
                }
            }
        }
        if let Ok(marker) = StaticProductionAttribute::parse_marker(StaticMode::Alias, tokens) {
            round_trip.sentence(&label("static"), Ok(marker.provenance()), |nodes| {
                marker.keyed_nodes(nodes);
                Ok(())
            });
        }
    }

    /// Every string literal of a file, including those inside macro calls
    /// such as `format!` and `assert!`.
    struct Literals(Vec<String>);

    impl<'ast> Visit<'ast> for Literals {
        fn visit_lit_str(&mut self, literal: &'ast syn::LitStr) {
            self.0.push(literal.value());
        }

        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            if let Ok(arguments) = mac.parse_body_with(
                syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated,
            ) {
                for argument in &arguments {
                    self.visit_expr(argument);
                }
            }
        }
    }

    /// The `.rs` files under `directory`, recursively, in path order.
    fn rust_files(directory: &Path) -> Vec<PathBuf> {
        let mut entries = std::fs::read_dir(directory)
            .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
            .map(|entry| entry.unwrap().path())
            .collect::<Vec<_>>();
        entries.sort();
        let mut files = Vec::new();
        for path in entries {
            if path.is_dir() {
                files.extend(rust_files(&path));
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                files.push(path);
            }
        }
        files
    }

    #[test]
    fn fixture_anchors_are_their_keyed_nodes() {
        let files = rust_files(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests"));
        let mut round_trip = RoundTrip::default();
        let mut literals = 0;
        for file in files {
            let syntax = syn::parse_file(&std::fs::read_to_string(&file).unwrap()).unwrap();
            let mut found = Literals(Vec::new());
            found.visit_file(&syntax);
            let name = file.file_name().unwrap().to_string_lossy().into_owned();
            for (index, literal) in found.0.iter().enumerate() {
                let before = round_trip.sentences + round_trip.descriptors;
                fixture_sentences(literal, &format!("{name} #{index}"), &mut round_trip);
                literals += usize::from(round_trip.sentences + round_trip.descriptors > before);
                proc_macro2::extra::invalidate_current_thread_spans();
            }
        }
        eprintln!(
            "fixtures: {literals} literals, {} sentences, {} descriptors, {} anchors",
            round_trip.sentences, round_trip.descriptors, round_trip.anchors
        );
        assert!(literals > 0, "no fixture literal parses as a sentence");
        assert!(round_trip.failures.is_empty(), "{}", round_trip.failures);
    }

    /// The attributes of `attributes` that invoke `entry`.
    fn invoking<'a>(
        attributes: &'a [Attribute],
        resolve: &'a dyn Resolve,
        entry: AttributeMacro,
    ) -> impl Iterator<Item = &'a Attribute> {
        attributes.iter().filter(move |attribute| {
            resolve.resolve(attribute.path()) == Some(Entry::Attribute(entry))
        })
    }

    /// An attribute's payload: empty for a bare path.
    fn payload(attribute: &Attribute) -> TokenStream {
        match &attribute.meta {
            Meta::Path(_) => TokenStream::new(),
            Meta::List(list) => list.tokens.clone(),
            Meta::NameValue(_) => panic!("a KRS attribute takes a list"),
        }
    }

    /// The `#[k::symbol]` override among `attributes`.
    fn symbol(attributes: &[Attribute], resolve: &dyn Resolve) -> Option<SymbolAttribute> {
        invoking(attributes, resolve, AttributeMacro::Symbol)
            .next()
            .map(|attribute| SymbolAttribute::parse_tokens(payload(attribute)).unwrap())
    }

    /// The static markers, each with its helper's name, and the strictness
    /// helpers among `attributes`, gathered as the collector gathers them.
    fn production_helpers(
        attributes: &[Attribute],
        resolve: &dyn Resolve,
    ) -> (
        Vec<(StaticProductionAttribute, syn::Ident)>,
        Vec<crate::StrictnessAttribute>,
    ) {
        let mut static_markers = Vec::new();
        for (entry, mode) in [
            (AttributeMacro::Alias, StaticMode::Alias),
            (AttributeMacro::Desugar, StaticMode::Desugar),
        ] {
            for helper in invoking(attributes, resolve, entry) {
                let marker =
                    StaticProductionAttribute::parse_marker(mode, payload(helper)).unwrap();
                let name = helper.path().segments.last().unwrap().ident.clone();
                static_markers.push((marker, name));
            }
        }
        let mut strictness = Vec::new();
        for helper in invoking(attributes, resolve, AttributeMacro::Strict) {
            strictness.push(parse_strict_attribute(payload(helper)).unwrap());
        }
        for helper in invoking(attributes, resolve, AttributeMacro::Seqstrict) {
            strictness.push(parse_seqstrict_attribute(payload(helper)).unwrap());
        }
        (static_markers, strictness)
    }

    /// The `#[k::token]` stack among `attributes`, if any.
    fn token_stack(attributes: &[Attribute], resolve: &dyn Resolve) -> Option<TokenStack> {
        let parsed = invoking(attributes, resolve, AttributeMacro::Token)
            .map(|attribute| TokenAttribute::parse_tokens(payload(attribute)).unwrap())
            .collect::<Vec<_>>();
        (!parsed.is_empty()).then(|| TokenStack::new(parsed).unwrap())
    }

    /// The sentences of a port source, dispatched from its KRS invocations
    /// to their parsers and descriptors as the macros and the collector's
    /// reparse dispatch them.
    struct Port<'a> {
        resolve: &'a dyn Resolve,
        owners: std::collections::BTreeMap<*const Item, &'a Invocation<'a>>,
        round_trip: &'a mut RoundTrip,
    }

    impl Port<'_> {
        fn items(&mut self, items: &[Item], label: &str) {
            for item in items {
                self.item(item, label);
            }
        }

        #[expect(
            clippy::too_many_lines,
            reason = "One arm per item kind, as the collector dispatches them."
        )]
        fn item(&mut self, item: &Item, label: &str) {
            let resolve = self.resolve;
            let invocation = self.owners.get(&std::ptr::from_ref(item)).copied();
            match item {
                Item::Trait(item_trait) => {
                    let label = format!("{label} trait {}", item_trait.ident);
                    let sort_symbol = symbol(&item_trait.attrs, resolve);
                    let sorts = invoking(&item_trait.attrs, resolve, AttributeMacro::Sort)
                        .map(|attribute| SortAttribute::parse_tokens(payload(attribute)).unwrap())
                        .collect::<Vec<_>>();
                    for sort in &sorts {
                        let anchors =
                            sort.descriptor_provenance(&item_trait.ident, sort_symbol.as_ref());
                        self.round_trip.descriptor(&label, anchors, |nodes| {
                            sort.keyed_nodes(nodes)?;
                            if let Some(symbol) = &sort_symbol {
                                symbol.keyed_nodes(nodes)?;
                            }
                            Ok(())
                        });
                    }
                    for attribute in invoking(&item_trait.attrs, resolve, AttributeMacro::Bracket) {
                        let bracket = BracketAttribute::parse_tokens(payload(attribute)).unwrap();
                        let sort = sorts.first();
                        self.round_trip
                            .sentence(&label, bracket.provenance(), |nodes| {
                                bracket.keyed_nodes(nodes)
                            });
                        let anchors = bracket.sort_descriptor_provenance(sort, &item_trait.ident);
                        self.round_trip.descriptor(&label, anchors, |nodes| {
                            bracket.keyed_nodes(nodes)?;
                            let sort = sort.expect("a bracketed sort has its sort attribute");
                            sort.keyed_alias_nodes(nodes)
                        });
                    }
                }
                Item::Struct(item_struct) => self.structure(item_struct, label),
                Item::Enum(item_enum) if invocation.is_some() => {
                    let label = format!("{label} enum {}", item_enum.ident);
                    let without = |entry| {
                        let mut reparsed = item_enum.clone();
                        reparsed.attrs.retain(|attribute| {
                            resolve.resolve(attribute.path()) != Some(Entry::Attribute(entry))
                        });
                        reparsed
                    };
                    if let Some(attribute) =
                        invoking(&item_enum.attrs, resolve, AttributeMacro::SyntaxList).next()
                    {
                        let attribute =
                            SyntaxListAttribute::parse_tokens(payload(attribute)).unwrap();
                        let declaration = SyntaxListDeclaration::from_parts(
                            &attribute,
                            without(AttributeMacro::SyntaxList),
                        )
                        .unwrap();
                        syntax_list(&declaration, &label, self.round_trip);
                    } else if let Some(attribute) =
                        invoking(&item_enum.attrs, resolve, AttributeMacro::Constructors).next()
                    {
                        let attribute =
                            ConstructorsAttribute::parse_tokens(payload(attribute)).unwrap();
                        let declaration = EnumConstructorDeclaration::from_parts(
                            &attribute,
                            without(AttributeMacro::Constructors),
                        )
                        .unwrap();
                        enum_constructors(&declaration, &label, self.round_trip);
                    }
                }
                Item::Fn(item_fn) => {
                    let shorthand = ShorthandItem::from_item(item)
                        .is_some_and(|shorthand| self.shorthand(&shorthand, label));
                    if !shorthand {
                        self.function(item_fn, label);
                    }
                }
                Item::Verbatim(_) => {
                    if let Some(shorthand) = ShorthandItem::from_item(item) {
                        self.shorthand(&shorthand, label);
                    }
                }
                Item::Impl(item_impl) => {
                    let label = format!("{label} impl");
                    for attribute in invoking(&item_impl.attrs, resolve, AttributeMacro::Subsort) {
                        let mut reparsed = item_impl.clone();
                        reparsed.attrs.retain(|candidate| {
                            resolve.resolve(candidate.path())
                                != Some(Entry::Attribute(AttributeMacro::Subsort))
                        });
                        let declaration = SubsortDeclaration::from_item(reparsed).unwrap();
                        let reference = SubsortAttribute::parse_tokens(payload(attribute)).unwrap();
                        self.round_trip.descriptor(
                            &label,
                            declaration.provenance(&reference),
                            |nodes| {
                                declaration.keyed_nodes(nodes)?;
                                reference.keyed_nodes(nodes)
                            },
                        );
                    }
                    for implementation_item in &item_impl.items {
                        let ImplItem::Fn(method) = implementation_item else {
                            continue;
                        };
                        if invoking(&method.attrs, resolve, AttributeMacro::Init)
                            .next()
                            .is_none()
                        {
                            continue;
                        }
                        let mut method = method.clone();
                        method.attrs.retain(|attribute| {
                            resolve.resolve(attribute.path())
                                != Some(Entry::Attribute(AttributeMacro::Init))
                        });
                        let initializer = InitializerFunction::from_item(method).unwrap();
                        self.round_trip
                            .sentence(&label, initializer.provenance(), |nodes| {
                                initializer.keyed_nodes(nodes)
                            });
                    }
                }
                Item::Type(item_type) => {
                    if let Some(stack) = token_stack(&item_type.attrs, resolve) {
                        let declaration = TokenDeclaration::from_alias(item_type.clone()).unwrap();
                        let label = format!("{label} type {}", item_type.ident);
                        token(&declaration, &stack, &label, self.round_trip);
                    }
                }
                Item::Const(item_const) => {
                    if invoking(&item_const.attrs, resolve, AttributeMacro::Constant)
                        .next()
                        .is_some()
                    {
                        let constant = ConstantItem::from_item(item_const.clone()).unwrap();
                        let label = format!("{label} const {}", item_const.ident);
                        self.round_trip
                            .sentence(&label, constant.provenance(), |nodes| {
                                constant.keyed_nodes(nodes)
                            });
                    }
                }
                Item::Macro(item_macro) => {
                    if let Some(invocation) = invocation
                        && let InvocationKind::Function { entry, .. } = &invocation.kind
                    {
                        self.macro_sentences(&item_macro.mac.tokens, *entry, label);
                    }
                }
                Item::Mod(module) => {
                    for attribute in invoking(&module.attrs, resolve, AttributeMacro::SpecModule) {
                        let parsed = SpecModuleAttribute::parse_tokens(payload(attribute)).unwrap();
                        let item = SpecModuleItem::from_item(module.clone()).unwrap();
                        let label = format!("{label} mod {}", module.ident);
                        self.round_trip
                            .sentence(&label, Ok(item.provenance()), |nodes| {
                                item.keyed_nodes(nodes)
                            });
                        self.round_trip.descriptor(
                            &label,
                            item.descriptor_provenance(&parsed),
                            |nodes| {
                                item.keyed_nodes(nodes)?;
                                parsed.keyed_nodes(nodes)
                            },
                        );
                    }
                    if let Some((_, nested)) = &module.content {
                        self.items(nested, &format!("{label}::{}", module.ident));
                    }
                }
                _ => {}
            }
        }

        fn structure(&mut self, item_struct: &syn::ItemStruct, label: &str) {
            let resolve = self.resolve;
            let label = format!("{label} struct {}", item_struct.ident);
            let constructor_symbol = symbol(&item_struct.attrs, resolve);
            let (static_markers, strictness) = production_helpers(&item_struct.attrs, resolve);
            for attribute in invoking(&item_struct.attrs, resolve, AttributeMacro::Function) {
                let mut parsed = FunctionAttribute::parse_tokens(payload(attribute)).unwrap();
                let declaration = ConstructorDeclaration::from_item(item_struct.clone()).unwrap();
                parsed.complete_default_syntax(&declaration).unwrap();
                let pieces = ProductionItem {
                    attribute: ProductionAttribute::Function(&parsed),
                    declaration: &declaration,
                    symbol: constructor_symbol.as_ref(),
                    static_markers: &static_markers,
                    strictness: &strictness,
                };
                production(&pieces, &label, self.round_trip);
            }
            for attribute in invoking(&item_struct.attrs, resolve, AttributeMacro::Constructor) {
                let parsed = ConstructorAttribute::parse_tokens(payload(attribute)).unwrap();
                let declaration = ConstructorDeclaration::from_item(item_struct.clone()).unwrap();
                let pieces = ProductionItem {
                    attribute: ProductionAttribute::Constructor(&parsed),
                    declaration: &declaration,
                    symbol: constructor_symbol.as_ref(),
                    static_markers: &static_markers,
                    strictness: &strictness,
                };
                production(&pieces, &label, self.round_trip);
            }
            if let Some(stack) = token_stack(&item_struct.attrs, resolve) {
                let declaration = TokenDeclaration::from_item(item_struct.clone()).unwrap();
                token(&declaration, &stack, &label, self.round_trip);
            }
            for attribute in invoking(&item_struct.attrs, resolve, AttributeMacro::Configuration) {
                let parsed = ConfigurationAttribute::parse_tokens(payload(attribute)).unwrap();
                let declaration = ConfigurationDeclaration::from_item(item_struct.clone()).unwrap();
                self.round_trip
                    .sentence(&label, declaration.provenance(), |nodes| {
                        declaration.keyed_nodes(nodes)
                    });
                self.round_trip.descriptor(
                    &label,
                    declaration.descriptor_provenance(&parsed),
                    |nodes| {
                        declaration.keyed_nodes(nodes)?;
                        parsed.keyed_nodes(nodes)
                    },
                );
            }
            if invoking(&item_struct.attrs, resolve, AttributeMacro::Cell)
                .next()
                .is_some()
            {
                let declaration = ConfigurationDeclaration::from_item(item_struct.clone()).unwrap();
                self.round_trip
                    .sentence(&label, declaration.provenance(), |nodes| {
                        declaration.keyed_nodes(nodes)
                    });
            }
        }

        /// Checks a `#[k::function(..)]` fn: its struct and its equations.
        fn shorthand(&mut self, item: &ShorthandItem, label: &str) -> bool {
            let Some(index) = invoking(&item.attrs, self.resolve, AttributeMacro::Function)
                .next()
                .and_then(|attribute| item.attrs.iter().position(|other| other == attribute))
            else {
                return false;
            };
            let tokens = payload(&item.attrs[index]);
            let mut remaining = item.clone();
            remaining.attrs.remove(index);
            let shorthand = FunctionShorthand::lower(tokens, remaining).unwrap();
            let label = format!("{label} fn {}", shorthand.structure().ident);
            let declaration =
                ConstructorDeclaration::from_item(shorthand.structure().clone()).unwrap();
            let attributes = &shorthand.structure().attrs;
            let constructor_symbol = symbol(attributes, self.resolve);
            let (static_markers, strictness) = production_helpers(attributes, self.resolve);
            let pieces = ProductionItem {
                attribute: ProductionAttribute::Function(shorthand.attribute()),
                declaration: &declaration,
                symbol: constructor_symbol.as_ref(),
                static_markers: &static_markers,
                strictness: &strictness,
            };
            production(&pieces, &label, self.round_trip);
            for equation in shorthand.equations() {
                let attribute = EquationAttribute::parse_tokens(equation.equation_keys()).unwrap();
                let rule = equation.rule().unwrap();
                rule_descriptor(
                    &rule,
                    RuleSentence::Equation(&attribute),
                    &label,
                    self.round_trip,
                );
            }
            true
        }

        /// Checks the sentences of a fn's rule, claim, context and alias
        /// attributes.
        fn function(&mut self, item_fn: &syn::ItemFn, label: &str) {
            let resolve = self.resolve;
            let attributes = &item_fn.attrs;
            let label = format!("{label} fn {}", item_fn.sig.ident);
            let label = label.as_str();
            for attribute in invoking(attributes, resolve, AttributeMacro::Claim) {
                let parsed = ClaimAttribute::parse_tokens(payload(attribute)).unwrap();
                let claim = StateClaimItem::from_item(item_fn.clone()).unwrap();
                self.round_trip
                    .sentence(label, claim.provenance(), |nodes| claim.keyed_nodes(nodes));
                self.round_trip
                    .sentence(label, parsed.provenance(), |nodes| {
                        parsed.keyed_nodes(nodes)
                    });
                self.round_trip
                    .descriptor(label, claim.descriptor_provenance(&parsed), |nodes| {
                        claim.keyed_nodes(nodes)?;
                        parsed.keyed_nodes(nodes)
                    });
            }
            for attribute in invoking(attributes, resolve, AttributeMacro::ContextAlias) {
                let parsed = ContextAliasAttribute::parse_tokens(payload(attribute)).unwrap();
                let alias =
                    StateContextAliasItem::from_item(item_fn.clone(), parsed.here()).unwrap();
                self.round_trip
                    .sentence(label, alias.provenance(), |nodes| alias.keyed_nodes(nodes));
                self.round_trip
                    .descriptor(label, alias.descriptor_provenance(&parsed), |nodes| {
                        parsed.keyed_nodes(nodes)?;
                        alias.keyed_declaration_nodes(nodes)?;
                        alias.keyed_nodes(nodes)
                    });
            }
            for attribute in invoking(attributes, resolve, AttributeMacro::Simplification) {
                let parsed = SimplificationAttribute::parse_tokens(payload(attribute)).unwrap();
                let rule = RuleItem::from_item(item_fn.clone()).unwrap();
                rule_descriptor(
                    &rule,
                    RuleSentence::Simplification(&parsed),
                    label,
                    self.round_trip,
                );
            }
            for attribute in invoking(attributes, resolve, AttributeMacro::Equation) {
                let parsed = EquationAttribute::parse_tokens(payload(attribute)).unwrap();
                let rule = RuleItem::from_equation_item(item_fn.clone()).unwrap();
                rule_descriptor(
                    &rule,
                    RuleSentence::Equation(&parsed),
                    label,
                    self.round_trip,
                );
            }
            for (entry, mode) in [
                (AttributeMacro::Alias, StaticMode::Alias),
                (AttributeMacro::Desugar, StaticMode::Desugar),
            ] {
                for attribute in invoking(attributes, resolve, entry) {
                    let desugar = match mode {
                        StaticMode::Alias => {
                            AliasAttribute::parse_tokens(payload(attribute)).unwrap();
                            DesugarAttribute::default()
                        }
                        StaticMode::Desugar => {
                            DesugarAttribute::parse_tokens(payload(attribute)).unwrap()
                        }
                    };
                    let rule = RuleItem::from_desugar_item(item_fn.clone(), &desugar).unwrap();
                    let sentence = match mode {
                        StaticMode::Alias => RuleSentence::Alias,
                        StaticMode::Desugar => RuleSentence::Desugar(&desugar),
                    };
                    rule_descriptor(&rule, sentence, label, self.round_trip);
                }
            }
            for attribute in invoking(attributes, resolve, AttributeMacro::Rule) {
                let parsed = RuleAttribute::parse_tokens(payload(attribute)).unwrap();
                let sentence = RuleSentence::Transition(&parsed);
                if let Ok(rule) = StateRuleItem::from_item(item_fn.clone()) {
                    state_rule_descriptor(&rule, sentence, label, self.round_trip);
                } else {
                    let rule = RuleItem::from_item(item_fn.clone()).unwrap();
                    rule_descriptor(&rule, sentence, label, self.round_trip);
                }
            }
            for attribute in invoking(attributes, resolve, AttributeMacro::Context) {
                let parsed = ContextAttribute::parse_tokens(payload(attribute)).unwrap();
                let sentence = RuleSentence::Context(&parsed);
                if let Ok(rule) = StateRuleItem::from_context_item(item_fn.clone()) {
                    state_rule_descriptor(&rule, sentence, label, self.round_trip);
                } else {
                    let rule = RuleItem::from_context_item(item_fn.clone()).unwrap();
                    rule_descriptor(&rule, sentence, label, self.round_trip);
                }
            }
        }

        /// Checks the sentences of an item macro.
        fn macro_sentences(&mut self, tokens: &TokenStream, entry: FunctionMacro, label: &str) {
            let label = format!("{label} {}!", entry.name());
            let label = label.as_str();
            let round_trip = &mut *self.round_trip;
            match entry {
                FunctionMacro::Rules => {
                    for item in RuleBlock::parse_tokens(tokens.clone()).unwrap().clauses() {
                        clause(item, label, round_trip);
                    }
                }
                FunctionMacro::Claims => {
                    for item in ClaimBlock::parse_tokens(tokens.clone()).unwrap().clauses() {
                        clause(item, label, round_trip);
                    }
                }
                FunctionMacro::Equations => {
                    for row in EquationTable::parse_tokens(tokens.clone()).unwrap().rows() {
                        round_trip.descriptor(
                            label,
                            row.descriptor().map(|row| row.anchors().to_vec()),
                            |nodes| row.keyed_nodes(nodes),
                        );
                    }
                }
                FunctionMacro::Sorts | FunctionMacro::FrameworkSorts => {
                    sorts(
                        &SortsDeclaration::parse_tokens(tokens.clone()).unwrap(),
                        label,
                        round_trip,
                    );
                }
                FunctionMacro::Precedence => {
                    let value = PrecedenceDeclaration::parse_tokens(tokens.clone()).unwrap();
                    round_trip
                        .sentence(label, value.provenance(), |nodes| value.keyed_nodes(nodes));
                }
                FunctionMacro::Associativity => {
                    let value = AssociativityDeclaration::parse_tokens(tokens.clone()).unwrap();
                    round_trip
                        .sentence(label, value.provenance(), |nodes| value.keyed_nodes(nodes));
                }
                FunctionMacro::Lexical => {
                    let value = LexicalDeclaration::parse_tokens(tokens.clone()).unwrap();
                    round_trip
                        .sentence(label, value.provenance(), |nodes| value.keyed_nodes(nodes));
                }
                FunctionMacro::Layout => {
                    let value = LayoutDeclaration::parse_tokens(tokens.clone()).unwrap();
                    round_trip
                        .sentence(label, value.provenance(), |nodes| value.keyed_nodes(nodes));
                }
                FunctionMacro::RawK => {
                    let value = RawKItem::parse_tokens(tokens.clone()).unwrap();
                    round_trip
                        .sentence(label, value.provenance(), |nodes| value.keyed_nodes(nodes));
                }
                _ => {}
            }
        }
    }

    #[test]
    fn port_anchors_are_their_keyed_nodes() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut round_trip = RoundTrip::default();
        let mut files = 0;
        for port in [
            "tests/imp/rust-definition/src",
            "tests/imp/expanded-definition/src",
            "semantics/kevm/src",
            "semantics/kmir/src",
            "semantics/kwasm/src",
        ] {
            let before = round_trip.sentences + round_trip.descriptors;
            for file in rust_files(&root.join(port)) {
                files += 1;
                let source = std::fs::read_to_string(&file).unwrap();
                let syntax = syn::parse_file(&source).unwrap();
                let resolve = AuthoredResolver::new("k");
                let found = invocations(&syntax, &resolve);
                let label = file.strip_prefix(&root).unwrap().display().to_string();
                let in_file = round_trip.sentences + round_trip.descriptors;
                Port {
                    resolve: &resolve,
                    owners: item_owners(&found),
                    round_trip: &mut round_trip,
                }
                .items(&syntax.items, &label);
                assert!(
                    found.is_empty() || round_trip.sentences + round_trip.descriptors > in_file,
                    "{label}: KRS invocations but no sentence"
                );
                proc_macro2::extra::invalidate_current_thread_spans();
            }
            assert!(
                round_trip.sentences + round_trip.descriptors > before,
                "{port}: no sentence"
            );
        }
        eprintln!(
            "ports: {files} files, {} sentences, {} descriptors, {} anchors",
            round_trip.sentences, round_trip.descriptors, round_trip.anchors
        );
        assert!(round_trip.failures.is_empty(), "{}", round_trip.failures);
    }
}
