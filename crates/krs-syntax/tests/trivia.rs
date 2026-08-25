//! Qualification for lossless source-trivia recovery and F7 source seams.

use krs_syntax::{
    DocCommentStyle, SourceRange, SyntaxErrorKind, TriviaAttachment, TriviaKind, TriviaTable,
    lex_gaps, parse_cells_expression_source_with_trivia, parse_cells_pattern_source_with_trivia,
    parse_map_expression_source_with_trivia, parse_map_pattern_source,
    parse_map_pattern_source_with_trivia, parse_rule_block_source,
    parse_rule_block_source_with_trivia,
};

#[test]
fn unicode_offsets_are_bytes_and_first_newline_splits_attachment() {
    let source = "α // λ\n β";
    let beta = source.find('β').unwrap();
    let alpha = SourceRange::new(0, 'α'.len_utf8());
    let beta = SourceRange::new(beta, beta + 'β'.len_utf8());
    let trivia = lex_gaps(source, &[alpha, beta]).unwrap();

    assert_eq!(trivia.len(), 3);
    assert_eq!(trivia[0].range().text(source), Some(" "));
    assert_eq!(trivia[0].attachment(), TriviaAttachment::Trailing(alpha));
    assert_eq!(trivia[1].range().text(source), Some("// λ"));
    assert!(matches!(trivia[1].kind(), TriviaKind::LineComment(_)));
    assert_eq!(trivia[1].attachment(), TriviaAttachment::Trailing(alpha));
    assert_eq!(trivia[2].range().text(source), Some("\n "));
    assert_eq!(trivia[2].attachment(), TriviaAttachment::Leading(beta));
    assert_eq!(
        match trivia[2].kind() {
            TriviaKind::Whitespace(whitespace) => whitespace.newline_count(),
            other => panic!("expected whitespace, found {other:?}"),
        },
        1
    );
    assert_total_coverage(source, &[alpha, beta], &trivia);
}

#[test]
fn nested_block_comments_are_classified_before_the_dsl_policy_rejects_them() {
    let source = "x /* outer /* inner */ tail */ y";
    let y = source.rfind('y').unwrap();
    let x_range = SourceRange::new(0, 1);
    let y_range = SourceRange::new(y, y + 1);
    let trivia = lex_gaps(source, &[x_range, y_range]).unwrap();
    let block = trivia
        .iter()
        .find_map(|trivia| match trivia.kind() {
            TriviaKind::BlockComment(block) => Some((trivia.range(), block)),
            _ => None,
        })
        .unwrap();
    assert_eq!(block.0.text(source), Some("/* outer /* inner */ tail */"));
    assert_eq!(block.1.maximum_nesting(), 2);
    assert_eq!(block.1.documentation(), None);
    assert_total_coverage(source, &[x_range, y_range], &trivia);

    let source = "X -> V /* outer /* inner */ tail */";
    let expected_start = source.find("/*").unwrap();
    let error = parse_map_pattern_source_with_trivia(source).unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::UnsupportedDslBlockComment { macro_name: "map" }
    );
    assert_eq!(
        error.source_range(),
        Some(SourceRange::new(expected_start, source.len()))
    );
    assert!(error.to_string().contains("use `//`"));
}

#[test]
fn line_comments_and_blank_lines_attach_without_collapsing() {
    let source = "X -> V, // first\n\nY -> W";
    let (_, table) = parse_map_pattern_source_with_trivia(source).unwrap();
    assert_table_totality(source, &table);

    let comment = table
        .trivia()
        .iter()
        .find(|trivia| matches!(trivia.kind(), TriviaKind::LineComment(_)))
        .unwrap();
    assert_eq!(comment.range().text(source), Some("// first"));
    let TriviaAttachment::Trailing(left) = comment.attachment() else {
        panic!("line comment should trail the preceding comma");
    };
    assert_eq!(left.text(source), Some(","));

    let blank_lines = table
        .trivia()
        .iter()
        .find(|trivia| {
            matches!(
                trivia.kind(),
                TriviaKind::Whitespace(whitespace) if whitespace.newline_count() == 2
            )
        })
        .unwrap();
    assert_eq!(blank_lines.range().text(source), Some("\n\n"));
    let TriviaAttachment::Leading(right) = blank_lines.attachment() else {
        panic!("blank lines should lead the following token");
    };
    assert_eq!(right.text(source), Some("Y"));
}

#[test]
fn doc_comment_synthetic_tokens_share_one_authored_union_range() {
    let source = "for Expr;\n/// clause docs\nrule: A(x) => x;";
    let (_, table) = parse_rule_block_source_with_trivia(source).unwrap();
    assert_table_totality(source, &table);

    let doc_start = source.find("///").unwrap();
    let doc_end = source[doc_start..].find('\n').unwrap() + doc_start;
    let doc_range = SourceRange::new(doc_start, doc_end);
    assert_eq!(
        table
            .token_ranges()
            .iter()
            .filter(|range| **range == doc_range)
            .count(),
        1
    );
    assert!(
        !table
            .trivia()
            .iter()
            .any(|trivia| trivia.range() == doc_range)
    );

    let shared_source = "/** docs */ ";
    let shared = SourceRange::new(0, shared_source.len() - 1);
    let manually_lexed = lex_gaps(shared_source, &[shared, shared]).unwrap();
    assert_eq!(manually_lexed.len(), 1);
    assert_eq!(manually_lexed[0].range().text(shared_source), Some(" "));

    let block_doc = "/** structural docs */";
    let trivia = lex_gaps(block_doc, &[]).unwrap();
    assert!(matches!(
        trivia[0].kind(),
        TriviaKind::BlockComment(block)
            if block.documentation() == Some(DocCommentStyle::Outer)
    ));

    let source = "for Expr;\n/** block docs */\nrule: A(x) => x;";
    parse_rule_block_source_with_trivia(source).unwrap();

    let not_doc = "/**/";
    let trivia = lex_gaps(not_doc, &[]).unwrap();
    assert!(matches!(
        trivia[0].kind(),
        TriviaKind::BlockComment(block) if block.documentation().is_none()
    ));
}

#[test]
fn totality_rejects_unclassified_bytes_and_invalid_utf8_boundaries() {
    let source = "x?";
    let error = lex_gaps(source, &[SourceRange::new(0, 1)]).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::InvalidTrivia { .. }
    ));
    assert_eq!(error.source_range(), Some(SourceRange::new(1, 2)));

    let source = "λ";
    let error = lex_gaps(source, &[SourceRange::new(0, 1)]).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::InvalidTrivia { .. }
    ));
}

#[test]
fn every_new_dsl_entry_point_preserves_the_semantic_parser_contract() {
    let map_pattern = "X -> V, rest @ .. // trailing";
    let legacy = parse_map_pattern_source(map_pattern).unwrap();
    let (with_trivia, map_pattern_trivia) =
        parse_map_pattern_source_with_trivia(map_pattern).unwrap();
    assert_eq!(
        legacy.provenance().unwrap().len(),
        with_trivia.provenance().unwrap().len()
    );
    assert_table_totality(map_pattern, &map_pattern_trivia);

    let map_expression = "E; X <- V // trailing";
    let (_, table) = parse_map_expression_source_with_trivia(map_expression).unwrap();
    assert_table_totality(map_expression, &table);

    let cells_pattern = "k: KCell(.K), env: Cell(E), state @ .. // trailing";
    let (_, table) = parse_cells_pattern_source_with_trivia(cells_pattern).unwrap();
    assert_table_totality(cells_pattern, &table);

    let cells_expression = "k: KCell(.K), env: Cell(E), ..state // trailing";
    let (_, table) = parse_cells_expression_source_with_trivia(cells_expression).unwrap();
    assert_table_totality(cells_expression, &table);

    let rule = "for Expr; id: A(x) => x; // trailing";
    let legacy = parse_rule_block_source(rule).unwrap();
    let (with_trivia, table) = parse_rule_block_source_with_trivia(rule).unwrap();
    assert_eq!(legacy.clauses().len(), with_trivia.clauses().len());
    assert_table_totality(rule, &table);
}

#[test]
fn legacy_source_parser_keeps_its_pre_f7_block_comment_behavior() {
    let source = "X -> /* accepted by the legacy token-only seam */ V";
    parse_map_pattern_source(source).unwrap();
    let error = parse_map_pattern_source_with_trivia(source).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnsupportedDslBlockComment { macro_name: "map" }
    ));

    let not_a_doc_comment = "X -> /**/ V";
    parse_map_pattern_source(not_a_doc_comment).unwrap();
    assert!(matches!(
        parse_map_pattern_source_with_trivia(not_a_doc_comment)
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::UnsupportedDslBlockComment { macro_name: "map" }
    ));
}

fn assert_table_totality(source: &str, table: &TriviaTable) {
    assert_eq!(table.source_len(), source.len());
    assert_total_coverage(source, table.token_ranges(), table.trivia());
}

fn assert_total_coverage(source: &str, tokens: &[SourceRange], trivia: &[krs_syntax::Trivia]) {
    let mut ranges = tokens.to_vec();
    ranges.extend(trivia.iter().map(|trivia| trivia.range()));
    ranges.sort_unstable();
    let mut cursor = 0;
    for range in ranges {
        assert_eq!(range.start(), cursor);
        cursor = range.end();
    }
    assert_eq!(cursor, source.len());
}
