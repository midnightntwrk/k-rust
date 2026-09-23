//! The self-contained HTML explorer.
//!
//! The page is one file: the graph, zero or more joins, and the initial filters are embedded as
//! one JSON document in a `<script type="application/json">` block, and the views are drawn by
//! the inline script of `explorer.html`. The page loads nothing over the network.

use serde::Serialize;

use crate::{Error, Filters, Graph, Join};

/// The page template. It holds exactly one occurrence of [`DATA_PLACEHOLDER`].
const TEMPLATE: &str = include_str!("explorer.html");

/// The token in [`TEMPLATE`] that the embedded JSON replaces.
const DATA_PLACEHOLDER: &str = "@@ALGO_GRAPH_DATA@@";

/// The `id` of the script element that holds the embedded JSON.
pub const HTML_DATA_ELEMENT_ID: &str = "algo-graph-data";

/// One embedded run: a display label and the join it names.
#[derive(Debug, Serialize)]
struct EmbeddedRun<'a> {
    label: String,
    join: &'a Join,
}

/// Initial filter state of the page; the reader may change or clear it.
#[derive(Debug, Serialize)]
struct EmbeddedFilters<'a> {
    areas: &'a [String],
    phases: &'a [String],
    counters: &'a [String],
}

/// The JSON document embedded in the page.
#[derive(Debug, Serialize)]
struct Embedded<'a> {
    filters: EmbeddedFilters<'a>,
    graph: &'a Graph,
    runs: Vec<EmbeddedRun<'a>>,
}

/// Render the explorer page for a graph and the joins of zero or more runs.
///
/// The output is a function of its inputs alone: joins keep their argument order, and a run's
/// label is its workload and the first eight characters of its krust revision, suffixed with its
/// position when two runs would share a label.
pub fn render_html(graph: &Graph, joins: &[Join], filters: &Filters) -> Result<String, Error> {
    let base_labels = joins.iter().map(run_label).collect::<Vec<_>>();
    let runs = joins
        .iter()
        .enumerate()
        .map(|(index, join)| {
            let label = &base_labels[index];
            let shared = base_labels.iter().filter(|other| *other == label).count() > 1;
            EmbeddedRun {
                label: if shared {
                    format!("{label} #{}", index + 1)
                } else {
                    label.clone()
                },
                join,
            }
        })
        .collect();
    let embedded = Embedded {
        filters: EmbeddedFilters {
            areas: &filters.areas,
            phases: &filters.phases,
            counters: &filters.counters,
        },
        graph,
        runs,
    };
    // `<` occurs in JSON text only inside strings, where `\u003c` denotes the same character.
    // Escaping every occurrence keeps `</script>` and `<!--` out of the script element.
    let json = serde_json::to_string(&embedded)?.replace('<', "\\u003c");
    debug_assert_eq!(TEMPLATE.matches(DATA_PLACEHOLDER).count(), 1);
    Ok(TEMPLATE.replacen(DATA_PLACEHOLDER, &json, 1))
}

fn run_label(join: &Join) -> String {
    match join.receipt.krust_revision.as_deref() {
        Some(revision) => format!(
            "{} @ {}",
            join.receipt.workload,
            revision.get(..8).unwrap_or(revision)
        ),
        None => join.receipt.workload.clone(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use serde::Deserialize;

    use super::*;
    use crate::{
        Receipt, build_graph,
        join::{parse_trace, project},
        workspace_root,
    };

    #[derive(Deserialize)]
    struct Parsed {
        graph: Graph,
        runs: Vec<ParsedRun>,
    }

    #[derive(Deserialize)]
    struct ParsedRun {
        label: String,
        join: Join,
    }

    fn embedded_json(page: &str) -> &str {
        let open = format!("<script type=\"application/json\" id=\"{HTML_DATA_ELEMENT_ID}\">");
        let start = page.find(&open).expect("the data element is present") + open.len();
        let end = start
            + page[start..]
                .find("</script>")
                .expect("the data element closes");
        &page[start..end]
    }

    /// A join of the workspace graph to a small synthetic trace: one invocation of
    /// `backend.matching.syntactic` nested in `backend.rewrite.apply` inside the `proof` phase.
    fn synthetic_join(graph: &Graph) -> Join {
        let observations = parse_trace(&serde_json::json!([
            {"ph":"B","name":"phase","ts":0,"pid":1,"tid":1,"args":{"name":"proof"}},
            {"ph":"B","name":"algo","ts":1,"pid":1,"tid":1,"args":{"id":"backend.rewrite.apply"}},
            {"ph":"B","name":"algo","ts":2,"pid":1,"tid":1,"args":{"id":"backend.matching.syntactic"}},
            {"ph":"E","name":"algo","ts":5,"pid":1,"tid":1,"args":{"counters":{"matching.problems":1,"matching.pairs":4}}},
            {"ph":"E","name":"algo","ts":9,"pid":1,"tid":1,"args":{"counters":{"matching.problems":1,"matching.pairs":4}}},
            {"ph":"E","name":"phase","ts":10,"pid":1,"tid":1}
        ]))
        .unwrap();
        let receipt = Receipt {
            directory: "evidence/synthetic </script> <!--".to_owned(),
            workload: "synthetic".to_owned(),
            claim: None,
            timestamp: None,
            krust_revision: Some("0123456789abcdef".to_owned()),
            binary_sha256: None,
            metadata_schema: "1".to_owned(),
            timings_schema: "1".to_owned(),
            current_timings_schema: 1,
            timings_partial: false,
            counter_schema: "1".to_owned(),
            current_counter_schema: 1,
            counters_partial: false,
            trace_schema: "chrome-trace-event-B/E".to_owned(),
            tools: Vec::new(),
            revisions: Vec::new(),
            coverage: None,
        };
        project(
            graph,
            observations,
            receipt,
            BTreeMap::from([
                ("matching.problems".to_owned(), 1),
                ("matching.pairs".to_owned(), 4),
                ("rewrite.steps".to_owned(), 0),
            ]),
        )
    }

    #[test]
    fn embeds_the_workspace_graph_and_joins_deterministically() {
        let graph = build_graph(&workspace_root()).unwrap().graph;
        let join = synthetic_join(&graph);
        let joins = [join.clone(), join.clone()];
        let filters = Filters {
            areas: vec!["backend".to_owned()],
            ..Filters::default()
        };
        let page = render_html(&graph, &joins, &filters).unwrap();
        assert_eq!(page, render_html(&graph, &joins, &filters).unwrap());
        assert!(page.contains("<title>k-rust algorithm graph</title>"));
        assert!(!page.contains(DATA_PLACEHOLDER));

        let json = embedded_json(&page);
        assert!(!json.contains('<'), "every `<` in the payload is escaped");
        let parsed: Parsed = serde_json::from_str(json).unwrap();
        assert_eq!(parsed.graph, graph);
        assert_eq!(parsed.runs.len(), 2);
        assert_eq!(parsed.runs[0].join, join);
        assert_eq!(parsed.runs[0].label, "synthetic @ 01234567 #1");
        assert_eq!(parsed.runs[1].label, "synthetic @ 01234567 #2");
    }

    #[test]
    fn renders_without_joins() {
        let graph = build_graph(&workspace_root()).unwrap().graph;
        let page = render_html(&graph, &[], &Filters::default()).unwrap();
        let parsed: Parsed = serde_json::from_str(embedded_json(&page)).unwrap();
        assert_eq!(parsed.graph, graph);
        assert!(parsed.runs.is_empty());
    }
}
