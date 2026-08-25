use std::collections::BTreeMap;
use std::{env, fs};

use krs_m4_native_comparator::{ComparePolicy, compare_kore, compare_kore_with_reference_claims};

fn main() {
    if let Err(error) = run() {
        eprintln!("krs-m4-native-comparator: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = env::args().skip(1);
    let reference_path = arguments.next().ok_or("missing reference KORE path")?;
    let actual_path = arguments.next().ok_or("missing native KORE path")?;
    let module_name = arguments.next().ok_or("missing module name")?;
    let mut label_map = BTreeMap::new();
    let mut reference_claims = None;
    while let Some(argument) = arguments.next() {
        if argument == "--reference-claims" {
            let path = arguments
                .next()
                .ok_or("--reference-claims needs PATH MODULE")?;
            let module = arguments
                .next()
                .ok_or("--reference-claims needs PATH MODULE")?;
            if reference_claims.replace((path, module)).is_some() {
                return Err("--reference-claims occurs more than once".into());
            }
            continue;
        }
        if argument != "--label" {
            return Err(format!("unknown argument {argument:?}").into());
        }
        let mapping = arguments.next().ok_or("--label needs FROM=CANONICAL")?;
        let (actual, reference) = mapping
            .split_once('=')
            .ok_or("--label needs FROM=CANONICAL")?;
        if actual.is_empty()
            || reference.is_empty()
            || label_map.insert(actual.into(), reference.into()).is_some()
        {
            return Err(format!("invalid or duplicate label mapping {mapping:?}").into());
        }
    }
    let reference = fs::read_to_string(&reference_path)?;
    let actual = fs::read_to_string(&actual_path)?;
    let policy = ComparePolicy { label_map };
    let report = if let Some((path, claims_module)) = reference_claims {
        let claims = fs::read_to_string(path)?;
        compare_kore_with_reference_claims(
            &reference,
            &claims,
            &claims_module,
            &actual,
            &module_name,
            &policy,
        )?
    } else {
        compare_kore(&reference, &actual, &module_name, &policy)?
    };
    println!(
        "PASS native KORE: reference={} native={} reference_projector_pairs={} native_projector_pairs={}",
        report.reference_sentences,
        report.actual_sentences,
        report.reference_projector_pairs,
        report.actual_projector_pairs,
    );
    Ok(())
}
