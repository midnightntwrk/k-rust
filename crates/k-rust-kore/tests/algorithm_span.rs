//! `algorithm_span` under a scoped subscriber.
//!
//! Every `algorithm_span` call shares one tracing callsite whose interest is cached
//! process-wide, while `with_default` installs its dispatcher on the current thread only. When
//! another thread performs the callsite's first registration without a subscriber, it computes
//! that interest from its own no-op dispatcher and may store `never` after the scoped
//! dispatcher's rebuild, silently disabling later spans on this thread. Whether a span is recorded
//! is therefore a property of the whole process, not of this test alone. This file must hold this
//! single test, so its binary has no other thread that reaches the callsite.

use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
};

use k_rust_kore::measure::{Algorithm, algorithm_span};
#[cfg(feature = "measure")]
use k_rust_kore::measure::{Counter, bump};
use tracing::{field::Visit, span};
use tracing_subscriber::{Layer, layer::Context, prelude::*, registry::LookupSpan};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct CapturedSpan {
    name: String,
    fields: BTreeMap<String, String>,
}

#[derive(Clone, Default)]
struct CaptureLayer(Arc<Mutex<Vec<CapturedSpan>>>);

#[derive(Clone, Copy)]
struct CaptureIndex(usize);

#[derive(Default)]
struct FieldVisitor(BTreeMap<String, String>);

impl Visit for FieldVisitor {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        self.0.insert(field.name().to_owned(), format!("{value:?}"));
    }

    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        self.0.insert(field.name().to_owned(), value.to_owned());
    }
}

impl<S> Layer<S> for CaptureLayer
where
    S: tracing::Subscriber + for<'lookup> LookupSpan<'lookup>,
{
    fn on_new_span(
        &self,
        attributes: &span::Attributes<'_>,
        id: &span::Id,
        context: Context<'_, S>,
    ) {
        let mut visitor = FieldVisitor::default();
        attributes.record(&mut visitor);
        let mut captured = self.0.lock().unwrap();
        let index = captured.len();
        captured.push(CapturedSpan {
            name: attributes.metadata().name().to_owned(),
            fields: visitor.0,
        });
        drop(captured);
        context
            .span(id)
            .unwrap()
            .extensions_mut()
            .insert(CaptureIndex(index));
    }

    fn on_record(&self, id: &span::Id, values: &span::Record<'_>, context: Context<'_, S>) {
        let index = context
            .span(id)
            .unwrap()
            .extensions()
            .get::<CaptureIndex>()
            .unwrap()
            .0;
        let mut visitor = FieldVisitor::default();
        values.record(&mut visitor);
        self.0.lock().unwrap()[index].fields.extend(visitor.0);
    }
}

#[test]
fn algorithm_span_records_compile_checked_ids() {
    let layer = CaptureLayer::default();
    let captured = Arc::clone(&layer.0);
    let subscriber = tracing_subscriber::registry().with(layer);
    tracing::subscriber::with_default(subscriber, || {
        {
            let _span = algorithm_span(Algorithm::BackendMatchingSyntactic);
            #[cfg(feature = "measure")]
            bump(Counter::RewriteSteps);
        }
        let _span = algorithm_span(Algorithm::ParserEarleyRecognize);
    });

    let captured = captured.lock().unwrap();
    assert_eq!(captured.len(), 2);
    assert!(captured.iter().all(|span| span.name == "algo"));
    assert_eq!(
        captured[0].fields.get("id").map(String::as_str),
        Some("backend.matching.syntactic")
    );
    assert_eq!(
        captured[1].fields.get("id").map(String::as_str),
        Some("parser.earley.recognize")
    );
    #[cfg(feature = "measure")]
    {
        let counters = captured[0].fields.get("counters").unwrap();
        let counters: serde_json::Value = serde_json::from_str(counters).unwrap();
        assert_eq!(counters[Counter::RewriteSteps.name()], 1);
        assert_eq!(captured[1].fields.get("counters").unwrap(), "{}");
    }
}
