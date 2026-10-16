//! The statistics of `kbench compare`: paired ratios of interleaved runs, a distribution-free
//! interval for their median, and a verdict per metric.
//!
//! Run `i` of the base and run `i` of the candidate execute back to back (in alternating order),
//! so they see nearly the same host load; their ratio `candidate / base` cancels most of it.
//! The interval is the sign-test confidence interval of the median of those ratios: it assumes
//! only that the pairs are independent, not that the times are normally distributed, which they
//! are not on a loaded host (a run that collides with another job is slow, never fast).

use crate::results::median;

/// The confidence level the interval aims for.
pub const LEVEL: f64 = 0.90;

/// An interval for the median of the paired ratios, and its actual coverage.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Interval {
    pub low: f64,
    pub high: f64,
    /// The probability that the interval contains the true median ratio (sign test).
    pub coverage: f64,
}

impl Interval {
    /// Half the interval's width, relative to 1: the change it cannot tell from noise.
    pub fn half_width(&self) -> f64 {
        (self.high - self.low) / 2.0
    }
}

/// The ratio `candidate[i] / base[i]` of each pair whose base value is positive.
pub fn paired_ratios(base: &[f64], candidate: &[f64]) -> Vec<f64> {
    base.iter()
        .zip(candidate)
        .filter(|(a, _)| **a > 0.0)
        .map(|(a, b)| b / a)
        .collect()
}

/// `P(X <= k)` for `X ~ Binomial(n, 1/2)`.
fn binomial_half_cdf(n: usize, k: usize) -> f64 {
    let mut coefficient = 1.0_f64;
    let mut total = 0.0;
    for i in 0..=k.min(n) {
        if i > 0 {
            #[allow(clippy::cast_precision_loss)]
            {
                coefficient = coefficient * (n + 1 - i) as f64 / i as f64;
            }
        }
        total += coefficient;
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
    let scale = 0.5_f64.powi(n as i32);
    total * scale
}

/// The sign-test interval for the median of `values`: the `k`-th smallest and `k`-th largest
/// value, with the largest `k` whose coverage `1 - 2 P(Bin(n, 1/2) <= k - 1)` is at least
/// `level`, or `k = 1` (smallest to largest) when no `k` reaches it. `None` for no values.
pub fn median_interval(values: &[f64], level: f64) -> Option<Interval> {
    if values.is_empty() {
        return None;
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    let n = sorted.len();
    let coverage = |k: usize| 1.0 - 2.0 * binomial_half_cdf(n, k - 1);
    let mut k = 1;
    while k < n.div_ceil(2) && coverage(k + 1) >= level {
        k += 1;
    }
    Some(Interval {
        low: sorted[k - 1],
        high: sorted[n - k],
        coverage: coverage(k).max(0.0),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Better,
    Worse,
    WithinNoise,
    /// Fewer than `MIN_PAIRS` pairs, or a metric that was not measured.
    Unknown,
}

impl Verdict {
    pub fn label(self) -> &'static str {
        match self {
            Verdict::Better => "better",
            Verdict::Worse => "WORSE",
            Verdict::WithinNoise => "within noise",
            Verdict::Unknown => "—",
        }
    }
}

/// Fewer pairs than this give no verdict: three pairs all on one side happen by chance one time
/// in four.
pub const MIN_PAIRS: usize = 3;

/// One metric of one point: the medians of both sides, their ratio, the interval of the
/// paired ratios, and the verdict.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MetricComparison {
    pub base: Option<f64>,
    pub candidate: Option<f64>,
    /// Candidate median / base median.
    pub ratio: Option<f64>,
    pub interval: Option<Interval>,
    pub verdict: Verdict,
}

/// The verdict of a point estimate of B/A and the interval of `pairs` paired ratios.
fn judge(ratio: Option<f64>, interval: Option<Interval>, pairs: usize, min_effect: f64) -> Verdict {
    match (ratio, interval) {
        (Some(ratio), Some(interval)) if pairs >= MIN_PAIRS => {
            if interval.high < 1.0 && ratio < 1.0 - min_effect {
                Verdict::Better
            } else if interval.low > 1.0 && ratio > 1.0 + min_effect {
                Verdict::Worse
            } else {
                Verdict::WithinNoise
            }
        }
        _ => Verdict::Unknown,
    }
}

/// Judges paired ratios pooled from several points (a ladder's sizes): the estimate is their
/// median, the interval the sign-test interval of that median. Pooling assumes the change is
/// about the same factor at every pooled size; it multiplies the pairs, so one noisy run
/// moves the interval much less than within a single point.
pub fn judge_pooled(ratios: &[f64], level: f64, min_effect: f64) -> MetricComparison {
    let ratio = median(ratios);
    let interval = median_interval(ratios, level);
    MetricComparison {
        base: None,
        candidate: None,
        ratio,
        interval,
        verdict: judge(ratio, interval, ratios.len(), min_effect),
    }
}

/// Compares the paired samples of one metric, where lower is better. A change is better or
/// worse only when the whole interval lies on one side of 1 and the ratio of the medians moves
/// by more than `min_effect` (a fraction): the interval alone flags tiny steady differences that
/// no ticket cares about, and the threshold alone flags a noisy run.
pub fn compare_metric(
    base: &[f64],
    candidate: &[f64],
    level: f64,
    min_effect: f64,
) -> MetricComparison {
    let base_median = median(base);
    let candidate_median = median(candidate);
    let ratio = match (base_median, candidate_median) {
        (Some(a), Some(b)) if a > 0.0 => Some(b / a),
        _ => None,
    };
    let ratios = paired_ratios(base, candidate);
    let interval = median_interval(&ratios, level);
    let verdict = judge(ratio, interval, ratios.len(), min_effect);
    MetricComparison {
        base: base_median,
        candidate: candidate_median,
        ratio,
        interval,
        verdict,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binomial_half_cdf_matches_hand_values() {
        assert!((binomial_half_cdf(5, 0) - 1.0 / 32.0).abs() < 1e-12);
        assert!((binomial_half_cdf(5, 1) - 6.0 / 32.0).abs() < 1e-12);
        assert!((binomial_half_cdf(4, 4) - 1.0).abs() < 1e-12);
    }

    #[test]
    fn five_pairs_give_the_range_at_ninety_four_percent() {
        let interval = median_interval(&[1.03, 0.98, 1.01, 0.99, 1.00], LEVEL).unwrap();
        assert_eq!((interval.low, interval.high), (0.98, 1.03));
        assert!((interval.coverage - 0.9375).abs() < 1e-12);
    }

    #[test]
    fn more_pairs_drop_the_extremes() {
        // n = 10: k = 2 covers 97.9 %, k = 3 covers 89.1 % < 90 %, so k = 2.
        let values: Vec<f64> = (1..=10).map(f64::from).collect();
        let interval = median_interval(&values, LEVEL).unwrap();
        assert_eq!((interval.low, interval.high), (2.0, 9.0));
        assert!(interval.coverage > 0.97 && interval.coverage < 0.98);
    }

    #[test]
    fn three_pairs_reach_only_seventy_five_percent() {
        let interval = median_interval(&[1.0, 2.0, 3.0], LEVEL).unwrap();
        assert_eq!((interval.low, interval.high), (1.0, 3.0));
        assert!((interval.coverage - 0.75).abs() < 1e-12);
        assert!(median_interval(&[], LEVEL).is_none());
    }

    #[test]
    fn identical_binaries_are_within_noise() {
        let base = [10.0, 10.2, 9.9, 10.1, 10.0];
        let candidate = [10.1, 10.0, 10.0, 10.2, 9.9];
        let metric = compare_metric(&base, &candidate, LEVEL, 0.03);
        assert_eq!(metric.verdict, Verdict::WithinNoise);
    }

    #[test]
    fn a_ten_percent_slowdown_is_worse_and_a_speedup_better() {
        let base = [10.0, 10.2, 9.9, 10.1, 10.0];
        let slower: Vec<f64> = base.iter().map(|v| v * 1.1).collect();
        let worse = compare_metric(&base, &slower, LEVEL, 0.03);
        assert_eq!(worse.verdict, Verdict::Worse);
        assert!((worse.ratio.unwrap() - 1.1).abs() < 1e-9);
        let faster: Vec<f64> = base.iter().map(|v| v * 0.8).collect();
        assert_eq!(
            compare_metric(&base, &faster, LEVEL, 0.03).verdict,
            Verdict::Better
        );
    }

    #[test]
    fn a_steady_change_below_the_minimum_effect_is_within_noise() {
        let base = [10.0, 10.0, 10.0, 10.0, 10.0];
        let candidate = [10.1, 10.1, 10.1, 10.1, 10.1];
        let metric = compare_metric(&base, &candidate, LEVEL, 0.03);
        assert!(metric.interval.unwrap().low > 1.0);
        assert_eq!(metric.verdict, Verdict::WithinNoise);
    }

    #[test]
    fn one_noisy_pair_keeps_a_large_median_change_within_noise() {
        // Four pairs say 20 % slower, one (a load spike on the base run) says faster.
        let base = [10.0, 10.0, 13.0, 10.0, 10.0];
        let candidate = [12.0, 12.0, 12.0, 12.0, 12.0];
        let metric = compare_metric(&base, &candidate, LEVEL, 0.03);
        assert!(metric.interval.unwrap().low < 1.0);
        assert_eq!(metric.verdict, Verdict::WithinNoise);
    }

    #[test]
    fn pooling_points_outvotes_one_noisy_pair() {
        // Three points of five pairs at 10 % slower, with one pair per point on the other
        // side of 1: each point alone is within noise, the pooled fifteen pairs are worse.
        let point = [1.1, 1.12, 0.95, 1.09, 1.11];
        let single = median_interval(&point, LEVEL).unwrap();
        assert!(single.low < 1.0);
        let pooled: Vec<f64> = point.iter().cycle().take(15).copied().collect();
        let metric = judge_pooled(&pooled, LEVEL, 0.03);
        assert_eq!(metric.verdict, Verdict::Worse);
        assert!((metric.ratio.unwrap() - 1.1).abs() < 1e-9);
    }

    #[test]
    fn too_few_pairs_or_missing_values_give_no_verdict() {
        assert_eq!(
            compare_metric(&[1.0, 1.0], &[2.0, 2.0], LEVEL, 0.03).verdict,
            Verdict::Unknown
        );
        assert_eq!(
            compare_metric(&[], &[], LEVEL, 0.03).verdict,
            Verdict::Unknown
        );
    }
}
