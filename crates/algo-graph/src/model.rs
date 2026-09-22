use serde::{Deserialize, Serialize};

/// A source location stable across edits that do not rename or move an item.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Anchor {
    #[serde(rename = "crate")]
    pub crate_name: String,
    pub file: String,
    pub symbol: String,
}

/// One cost claim from a primary algorithm card.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Cost {
    pub mode: String,
    pub bound: String,
}

/// One canonical graph node.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Node {
    pub kind: String,
    pub id: String,
    pub provenance: String,
    pub anchor: Anchor,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub area: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub sites: Vec<Anchor>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub cost: Vec<Cost>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub variable: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub invariant: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub no_counter: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub table: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub call: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub behavior: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub generating_passes: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub registry_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sequence: Option<usize>,
}

/// One canonical, typed relationship between graph nodes.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Edge {
    pub kind: String,
    pub from: String,
    pub to: String,
    pub provenance: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub order: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub consumer_site: Option<Anchor>,
}

/// The deterministic static algorithm graph.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Graph {
    #[serde(rename = "node", default)]
    pub nodes: Vec<Node>,
    #[serde(rename = "edge", default)]
    pub edges: Vec<Edge>,
}

impl Graph {
    pub(crate) fn sort(&mut self) {
        self.nodes
            .sort_by(|left, right| (&left.id, &left.kind).cmp(&(&right.id, &right.kind)));
        self.edges.sort_by(|left, right| {
            (
                &left.from,
                &left.kind,
                &left.to,
                &left.order,
                &left.detail,
                &left.consumer_site,
            )
                .cmp(&(
                    &right.from,
                    &right.kind,
                    &right.to,
                    &right.order,
                    &right.detail,
                    &right.consumer_site,
                ))
        });
        self.edges.dedup();
    }
}
