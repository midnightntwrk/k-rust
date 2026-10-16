//! A run's results file (`results.toml`) and the reference cache (`benchmarks/reference.toml`).

use std::path::Path;

use serde::{Deserialize, Serialize};

pub const RESULTS_SCHEMA: &str = "kbench-results/1";

/// The measured samples of one side of one workload (or one ladder value).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Samples {
    pub wall_seconds: Vec<f64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub cpu_seconds: Vec<f64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub peak_bytes: Vec<u64>,
}

pub fn median(values: &[f64]) -> Option<f64> {
    if values.is_empty() {
        return None;
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    let n = sorted.len();
    Some(if n % 2 == 1 {
        sorted[n / 2]
    } else {
        f64::midpoint(sorted[n / 2 - 1], sorted[n / 2])
    })
}

impl Samples {
    pub fn push(&mut self, sample: &crate::measure::Sample) {
        self.wall_seconds.push(sample.wall_seconds);
        if let Some(cpu) = sample.cpu_seconds {
            self.cpu_seconds.push(cpu);
        }
        if let Some(peak) = sample.peak_bytes {
            self.peak_bytes.push(peak);
        }
    }

    pub fn wall(&self) -> Option<f64> {
        median(&self.wall_seconds)
    }

    pub fn cpu(&self) -> Option<f64> {
        median(&self.cpu_seconds)
    }

    #[allow(clippy::cast_precision_loss)]
    pub fn peak(&self) -> Option<f64> {
        let peaks: Vec<f64> = self.peak_bytes.iter().map(|b| *b as f64).collect();
        median(&peaks)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Point {
    pub param: i64,
    /// `ok`, or the failure (`timeout`, `out of memory`, `check: …`).
    pub status: String,
    #[serde(flatten)]
    pub samples: Samples,
}

/// The reference side as recorded in a run: copied from the cache, or why there is none.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ReferenceResult {
    /// `cached`, `missing` (paired, never measured), `stale` (paired, cache key differs),
    /// `failed` (measured once, the reference failed), `unsupported`, or `untested`.
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub backend: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub measured_at: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub samples: Option<Samples>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub points: Vec<Point>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WorkloadResult {
    pub id: String,
    pub semantics: String,
    pub operation: String,
    pub title: String,
    pub stresses: String,
    pub tier: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub origin: Option<String>,
    /// `ok`, `failed`, `skipped` (not in the selected tier or filter), or `error`.
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ladder_param: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub krust: Option<Samples>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub points: Vec<Point>,
    pub reference: ReferenceResult,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Host {
    pub hostname: String,
    pub kernel: String,
    pub cpus: usize,
    pub memory_bytes: u64,
    pub load_before: String,
    pub load_after: String,
}

/// A semantics and operation without a workload, and why (`[[gap]]` in the registry).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Gap {
    pub semantics: String,
    pub operation: String,
    pub reason: String,
    pub note: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Run {
    pub schema: String,
    pub run_id: String,
    pub started_at: String,
    pub finished_at: String,
    pub tier: String,
    pub filter: Vec<String>,
    pub commit: String,
    pub dirty: bool,
    pub krust_path: String,
    pub krust_sha256: String,
    pub memory_method: String,
    pub reference_k_version: String,
    pub reference_k_opts: String,
    pub host: Host,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub gap: Vec<Gap>,
    pub workload: Vec<WorkloadResult>,
}

impl Run {
    pub fn load(path: &Path) -> Result<Run, String> {
        let text = std::fs::read_to_string(path)
            .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
        let run: Run =
            toml::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))?;
        if run.schema != RESULTS_SCHEMA {
            return Err(format!(
                "{}: unsupported schema {}",
                path.display(),
                run.schema
            ));
        }
        Ok(run)
    }

    pub fn save(&self, path: &Path) -> Result<(), String> {
        let text = toml::to_string(self).map_err(|error| error.to_string())?;
        std::fs::write(path, text)
            .map_err(|error| format!("cannot write {}: {error}", path.display()))
    }
}

/// One cached reference K measurement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Measurement {
    pub workload: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub param: Option<i64>,
    /// SHA-256 of the reference command, its prepare steps, the runtime options, and the pins.
    pub key: String,
    pub k_version: String,
    pub k_opts: String,
    pub measured_at: String,
    pub source: String,
    pub host: String,
    pub method: String,
    /// `ok`, or the failure the reference reported (`timeout`, `out of memory`, `check: …`).
    pub outcome: String,
    #[serde(flatten)]
    pub samples: Samples,
}

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct ReferenceCache {
    pub version: u32,
    #[serde(default)]
    pub measurement: Vec<Measurement>,
}

impl ReferenceCache {
    pub fn load(path: &Path) -> Result<ReferenceCache, String> {
        if !path.exists() {
            return Ok(ReferenceCache {
                version: 1,
                measurement: Vec::new(),
            });
        }
        let text = std::fs::read_to_string(path)
            .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
        toml::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))
    }

    pub fn save(&mut self, path: &Path) -> Result<(), String> {
        self.measurement
            .sort_by(|a, b| (&a.workload, a.param).cmp(&(&b.workload, b.param)));
        let mut text = String::from(
            "# Cached reference K measurements, written by `kbench reference`.\n\
             # A measurement is reused while its key (command, prepare steps, runtime options, pins) matches;\n\
             # reference K is not re-measured otherwise (benchmarks/README.md, \"Reference cache\").\n\n",
        );
        text.push_str(&toml::to_string(self).map_err(|error| error.to_string())?);
        std::fs::write(path, text)
            .map_err(|error| format!("cannot write {}: {error}", path.display()))
    }

    pub fn find(&self, workload: &str, param: Option<i64>) -> Option<&Measurement> {
        self.measurement
            .iter()
            .find(|m| m.workload == workload && m.param == param)
    }

    pub fn upsert(&mut self, measurement: Measurement) {
        self.measurement
            .retain(|m| !(m.workload == measurement.workload && m.param == measurement.param));
        self.measurement.push(measurement);
    }
}
