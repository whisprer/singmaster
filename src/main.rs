//! singmaster_lab — search utilities for binomial coefficient collisions (Singmaster-style exploration).
//!
//! This program scans positions (n,k) with n<=N_MAX and k<=K_MAX, applies optional geometric
//! filters, and groups positions by equal binomial coefficient C(n,k). It can also compute
//! the Gaussian (q-binomial) coefficient at q=2 as an auxiliary signal.
//!
//! Key CLI ergonomics:
//!   - `--half-triangle` (default) / `--no-half-triangle`
//!   - `--print-q2-values` (default) / `--no-print-q2-values`
//!   - `--q2-only` / `--no-q2-only` (default is off)
//!
//! Notes:
//!   - If you disable half-triangle, you will see lots of trivial symmetry pairs
//!     (n,k) and (n,n-k). That's expected.

use std::collections::{BTreeMap, HashMap};

use clap::{ArgAction, Parser};
use num_bigint::BigUint;
use num_traits::One;

/// Search for collisions in binomial coefficients (and optionally inspect q=2 gaussian values).
#[derive(Parser, Debug, Clone)]
#[command(name = "singmaster_lab", version, about)]
struct Args {
    /// Maximum n to scan (inclusive).
    #[arg(long)]
    n_max: u32,

    /// Maximum k to scan (inclusive).
    #[arg(long)]
    k_max: u32,

    /// Limit to half of Pascal's triangle (k <= n/2).
    ///
    /// Default is enabled. Use `--no-half-triangle` to disable.
    #[arg(long = "half-triangle", action = ArgAction::SetTrue)]
    half_triangle: bool,

    /// Disable half-triangle restriction (include both sides).
    #[arg(long = "no-half-triangle", action = ArgAction::SetTrue)]
    no_half_triangle: bool,

    /// Keep k=1 and k=n-1 entries (normally skipped because they create many trivial repeats).
    #[arg(long, action = ArgAction::SetTrue)]
    keep_k1: bool,

    /// Optional diagonal band around the central diagonal k ~= n/2, in k-units.
    ///
    /// If set to W, a position (n,k) is kept iff |2k - n| <= 2W.
    #[arg(long)]
    diag_band: Option<u32>,

    /// Minimum multiplicity to report (>=2 means collisions).
    #[arg(long, default_value_t = 2)]
    min_mult: usize,

    /// Only keep collision groups that also contain a q=2 gaussian collision internally.
    ///
    /// (i.e. within an equal-binomial group, at least `min_mult` positions share the same
    /// q=2 gaussian value).
    #[arg(long = "q2-only", action = ArgAction::SetTrue)]
    q2_only: bool,

    /// Explicitly disable q2-only mode (default is off anyway).
    #[arg(long = "no-q2-only", action = ArgAction::SetTrue)]
    no_q2_only: bool,

    /// Print q=2 gaussian values for each reported position.
    ///
    /// Default is enabled. Use `--no-print-q2-values` to disable.
    #[arg(long = "print-q2-values", action = ArgAction::SetTrue)]
    print_q2_values: bool,

    /// Disable printing q=2 gaussian values.
    #[arg(long = "no-print-q2-values", action = ArgAction::SetTrue)]
    no_print_q2_values: bool,

    /// Maximum number of collision groups to print (0 = no limit).
    #[arg(long, default_value_t = 0)]
    collision_print_limit: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Fingerprint {
    /// number of 32-bit limbs
    len: u32,
    lo0: u32,
    lo1: u32,
    hi0: u32,
    hi1: u32,
}

fn fingerprint_biguint(x: &BigUint) -> Fingerprint {
    let digits = x.to_u32_digits(); // little-endian limbs
    let len = digits.len() as u32;
    let lo0 = *digits.get(0).unwrap_or(&0);
    let lo1 = *digits.get(1).unwrap_or(&0);
    let hi0 = *digits.get(digits.len().wrapping_sub(1)).unwrap_or(&0);
    let hi1 = *digits.get(digits.len().wrapping_sub(2)).unwrap_or(&0);
    Fingerprint {
        len,
        lo0,
        lo1,
        hi0,
        hi1,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Pos {
    n: u32,
    k: u32,
}

fn within_diag_band(n: u32, k: u32, band: Option<u32>) -> bool {
    let Some(w) = band else { return true; };
    let n_i = n as i64;
    let k_i = k as i64;
    let w_i = w as i64;
    (2 * k_i - n_i).abs() <= 2 * w_i
}

fn effective_half_triangle(args: &Args) -> bool {
    // Default is ON unless explicitly disabled.
    if args.no_half_triangle {
        false
    } else if args.half_triangle {
        true
    } else {
        true
    }
}

fn effective_print_q2(args: &Args) -> bool {
    // Default is ON unless explicitly disabled.
    if args.no_print_q2_values {
        false
    } else if args.print_q2_values {
        true
    } else {
        true
    }
}

fn effective_q2_only(args: &Args) -> bool {
    if args.no_q2_only {
        false
    } else if args.q2_only {
        true
    } else {
        false
    }
}

fn include_pos(half_triangle: bool, args: &Args, n: u32, k: u32) -> bool {
    if k > args.k_max || k > n {
        return false;
    }

    // Always skip the boundary values: C(n,0)=C(n,n)=1 (huge trivial "collision group").
    if k == 0 || k == n {
        return false;
    }

    if half_triangle && k > n / 2 {
        return false;
    }

    if !args.keep_k1 {
        if k == 1 || (n >= 1 && k == n - 1) {
            return false;
        }
    }

    if !within_diag_band(n, k, args.diag_band) {
        return false;
    }

    true
}

/// Binomial coefficient C(n,k) computed via multiplicative method (exact).
fn binom(n: u32, k: u32) -> BigUint {
    if k == 0 || k == n {
        return BigUint::one();
    }
    let k_eff = k.min(n - k);
    let mut acc = BigUint::one();
    for i in 1..=k_eff {
        acc *= BigUint::from(n - k_eff + i);
        acc /= BigUint::from(i);
    }
    acc
}

/// Gaussian binomial coefficient [n k]_q for q=2, computed across k for a fixed n.
///
/// Recurrence:
/// [n 0]_2 = 1
/// [n k]_2 = [n k-1]_2 * (2^(n-k+1)-1) / (2^k - 1)
fn gaussian_q2_row(n: u32, k_max: u32) -> Vec<BigUint> {
    let mut row: Vec<BigUint> = Vec::with_capacity((k_max + 1) as usize);
    row.push(BigUint::one()); // k=0
    let mut cur = BigUint::one();

    for k in 1..=k_max {
        let num_exp = n - k + 1;
        let denom_exp = k;

        let numerator = (BigUint::one() << num_exp) - BigUint::one();
        let denominator = (BigUint::one() << denom_exp) - BigUint::one();

        cur *= numerator;
        cur /= denominator; // exact
        row.push(cur.clone());
    }
    row
}

fn degree_pattern_key(ks_sorted: &[u32]) -> String {
    if ks_sorted.is_empty() {
        return "(empty)".to_string();
    }
    let mut out = String::new();
    let mut i = 0usize;
    while i < ks_sorted.len() {
        let v = ks_sorted[i];
        let mut j = i + 1;
        while j < ks_sorted.len() && ks_sorted[j] == v {
            j += 1;
        }
        let cnt = j - i;
        if !out.is_empty() {
            out.push(' ');
        }
        out.push_str(&format!("{v}^{cnt}"));
        i = j;
    }
    out
}

fn main() {
    let args = Args::parse();

    let half_triangle = effective_half_triangle(&args);
    let print_q2_values = effective_print_q2(&args);
    let q2_only = effective_q2_only(&args);

    eprintln!(
        "scan: n<= {}  k<= {}  half_triangle={}  diag_band={:?}  keep_k1={}  min_mult={}  q2_only={}  print_q2_values={}",
        args.n_max,
        args.k_max,
        half_triangle,
        args.diag_band,
        args.keep_k1,
        args.min_mult,
        q2_only,
        print_q2_values
    );

    let t0 = std::time::Instant::now();

    // PASS 1: fingerprint bucketization to find likely collisions without storing huge BigUints as keys.
    let mut buckets: HashMap<Fingerprint, Vec<Pos>> = HashMap::new();

    for n in 0..=args.n_max {
        let k_lim = args.k_max.min(n);
        for k in 0..=k_lim {
            if !include_pos(half_triangle, &args, n, k) {
                continue;
            }
            let v = binom(n, k);
            let fp = fingerprint_biguint(&v);
            buckets.entry(fp).or_default().push(Pos { n, k });
        }
    }

    buckets.retain(|_, v| v.len() >= args.min_mult);

    eprintln!(
        "pass1: candidate buckets={}  elapsed={:.2}s",
        buckets.len(),
        t0.elapsed().as_secs_f64()
    );

    // Flatten candidates.
    let mut candidates: Vec<Pos> = Vec::new();
    for v in buckets.values() {
        candidates.extend_from_slice(v);
    }

    // PASS 2: exact grouping by true BigUint value, but only for candidates.
    let mut exact: HashMap<BigUint, Vec<Pos>> = HashMap::new();
    for pos in &candidates {
        let v = binom(pos.n, pos.k);
        exact.entry(v).or_default().push(*pos);
    }
    exact.retain(|_, v| v.len() >= args.min_mult);

    eprintln!(
        "pass2: exact collision groups={}  elapsed={:.2}s",
        exact.len(),
        t0.elapsed().as_secs_f64()
    );

    // Optional q2-only filter: inside each binomial-collision group, check whether q=2 gaussian values collide.
    let mut kept_groups: Vec<Vec<Pos>> = Vec::new();

    for (_key, mut positions) in exact {
        positions.sort_by_key(|p| (p.n, p.k));

        if q2_only {
            let mut q2_counts: HashMap<Fingerprint, usize> = HashMap::new();
            for p in &positions {
                let row = gaussian_q2_row(p.n, p.k);
                let q2v = &row[p.k as usize];
                *q2_counts.entry(fingerprint_biguint(q2v)).or_insert(0) += 1;
            }
            let survives = q2_counts.values().any(|&c| c >= args.min_mult);
            if !survives {
                continue;
            }
        }

        kept_groups.push(positions);
    }

    eprintln!(
        "q2-filter: kept={}  elapsed={:.2}s",
        kept_groups.len(),
        t0.elapsed().as_secs_f64()
    );

    // Sort by multiplicity descending, then by first (n,k) for determinism.
    kept_groups.sort_by(|a, b| {
        b.len()
            .cmp(&a.len())
            .then_with(|| a[0].n.cmp(&b[0].n))
            .then_with(|| a[0].k.cmp(&b[0].k))
    });

    let mut pattern_summary: BTreeMap<String, Vec<Vec<Pos>>> = BTreeMap::new();

    let mut printed_groups = 0usize;
    for positions in &kept_groups {
        let mult = positions.len();

        // Pattern summary uses the multiset of k values for the group.
        let mut ks: Vec<u32> = positions.iter().map(|p| p.k).collect();
        ks.sort_unstable();
        let pat = degree_pattern_key(&ks);
        pattern_summary.entry(pat).or_default().push(positions.clone());

        if args.collision_print_limit != 0 && printed_groups >= args.collision_print_limit {
            continue;
        }

        println!("== Collision (mult={}) ==", mult);
        let pos_list: Vec<(u32, u32)> = positions.iter().map(|p| (p.n, p.k)).collect();
        println!("positions: {:?}", pos_list);

        if print_q2_values {
            println!("q=2 values:");
            for p in positions {
                let row = gaussian_q2_row(p.n, p.k);
                let q2v = &row[p.k as usize];
                println!("  [{},{}]  {}", p.n, p.k, q2v);
            }
            println!();
        }

        printed_groups += 1;
    }

    println!("=== Degree-pattern summary ===");
    for (pat, groups) in &pattern_summary {
        println!("pattern {}  count={}", pat, groups.len());
        let mut shown = 0usize;
        for g in groups {
            let pos_list: Vec<(u32, u32)> = g.iter().map(|p| (p.n, p.k)).collect();
            println!("  {:?}", pos_list);
            shown += 1;
            if shown >= 20 {
                if groups.len() > shown {
                    println!("  ... ({} more)", groups.len() - shown);
                }
                break;
            }
        }
    }

    println!("done. total elapsed={:.2}s", t0.elapsed().as_secs_f64());
}
