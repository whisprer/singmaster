use clap::{ArgAction, Parser};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::collections::HashMap;

#[derive(Clone, Debug)]
struct PosInfo {
    n: u32,
    k: u32,
    entropy: f64, // k/n
}

#[derive(Parser, Debug)]
#[command(
    author,
    version,
    about = "Singmaster lab: two-pass fingerprint scan + prime-exponent exact verification + q=2 deformation filter"
)]
struct Args {
    /// Max n to scan (inclusive).
    #[arg(long, default_value_t = 1000)]
    n_max: u32,

    /// Only keep k <= n/2 (removes trivial symmetry k <-> n-k).
    #[arg(long, default_value_t = true)]
    half_triangle: bool,

    /// k=0 is always ignored. k=1 is ignored by default; pass --keep-k1 to include it.
    #[arg(long, default_value_t = false)]
    keep_k1: bool,

    /// Minimum multiplicity (2 = pair collisions, 3 = triple collisions, ...).
    #[arg(long, default_value_t = 2)]
    min_mult: usize,

    /// Only print collisions that ALSO collide at q=2 (Gaussian binomials).
    /// Use --no-q2-only to disable.
    #[arg(long, action = ArgAction::SetTrue, default_value_t = true)]
    #[arg(long = "no-q2-only", action = ArgAction::SetFalse)]
    q2_only: bool,

    /// Maximum k to scan (caps width; keeps laptops alive).
    #[arg(long, default_value_t = 64)]
    k_max: u32,

    /// How many collision values to print in detail.
    #[arg(long, default_value_t = 80)]
    collision_print_limit: usize,

    /// Also print a summary grouped by degree-pattern (k-multiset).
    #[arg(long, default_value_t = true)]
    print_degree_pattern_summary: bool,

    /// Print q=2 values for the positions.
    /// Use --no-print-q2-values to disable.
    #[arg(long, action = ArgAction::SetTrue, default_value_t = true)]
    #[arg(long = "no-print-q2-values", action = ArgAction::SetFalse)]
    print_q2_values: bool,
}

// Two distinct 64-bit primes < 2^64 for fast modular hashing.
const P1: u64 = 18446744073709551557u64; // 2^64 - 59
const P2: u64 = 18446744073709551533u64; // 2^64 - 83

fn main() {
    let args = Args::parse();

    // We always ignore k=0; ignore k=1 unless keep_k1.
    let k_start: u32 = if args.keep_k1 { 1 } else { 2 };

    if args.k_max < k_start {
        eprintln!(
            "k_max={} is < k_start={} (keep_k1={}). Nothing to scan.",
            args.k_max, k_start, args.keep_k1
        );
        return;
    }

    // -------------------------
    // PASS 1: Fingerprint scan
    // -------------------------
    let inv1 = precompute_inverses(P1, args.k_max);
    let inv2 = precompute_inverses(P2, args.k_max);

    // fingerprint(u128) -> positions
    let mut fp_hits: HashMap<u128, Vec<PosInfo>> = HashMap::new();

    let mut positions_scanned: u64 = 0;
    for n in 0..=args.n_max {
        let mut k_lim = if args.half_triangle { n / 2 } else { n };
        if k_lim > args.k_max {
            k_lim = args.k_max;
        }
        if k_lim < k_start {
            continue;
        }

        for k in k_start..=k_lim {
            let fp = fingerprint_binom_mod(n, k, &inv1, &inv2);
            // n>=1 here because k>=1
            let entropy = (k as f64) / (n as f64);
            fp_hits
                .entry(fp)
                .or_default()
                .push(PosInfo { n, k, entropy });
            positions_scanned += 1;
        }
    }

    let mut candidates: Vec<(u128, Vec<PosInfo>)> = fp_hits
        .into_iter()
        .filter(|(_, pos)| pos.len() >= args.min_mult)
        .collect();

    candidates.sort_by(|(_, a), (_, b)| b.len().cmp(&a.len()));

    println!(
        "PASS1: scanned n=0..={} (half_triangle={}, keep_k1={}, k_max={}), positions_scanned={}, fp_buckets_with_count>=min_mult({})={}",
        args.n_max,
        args.half_triangle,
        args.keep_k1,
        args.k_max,
        positions_scanned,
        args.min_mult,
        candidates.len()
    );

    if candidates.is_empty() {
        println!("No fingerprint buckets reached multiplicity >= {}. Done.", args.min_mult);
        return;
    }

    // -------------------------
    // PASS 2: Exact verification
    // -------------------------
    let primes = sieve_primes(args.n_max);

    let mut exact_hits: HashMap<BigUint, Vec<PosInfo>> = HashMap::new();
    let mut exact_positions_verified: u64 = 0;

    for (_fp, positions) in candidates {
        for p in positions {
            let v = binom_big_prime_exponent(p.n, p.k, &primes);
            exact_hits.entry(v).or_default().push(p);
            exact_positions_verified += 1;
        }
    }

    let mut collisions: Vec<(BigUint, Vec<PosInfo>)> = exact_hits
        .into_iter()
        .filter(|(_, pos)| pos.len() >= args.min_mult)
        .collect();

    collisions.sort_by(|(va, pa), (vb, pb)| {
        pb.len()
            .cmp(&pa.len())
            .then_with(|| va.bits().cmp(&vb.bits()))
            .then_with(|| va.cmp(vb))
    });

    println!(
        "PASS2: verified_positions={}, exact_collision_values_with_mult>={}={}",
        exact_positions_verified,
        args.min_mult,
        collisions.len()
    );

    // Pattern groups (only for what we actually print)
    let mut pattern_groups: HashMap<String, Vec<BigUint>> = HashMap::new();

    println!(
        "\nDetailed collisions (q2_only={}, showing up to {}):",
        args.q2_only, args.collision_print_limit
    );

    let mut shown = 0usize;
    for (value, mut pos) in collisions.iter().cloned() {
        pos.sort_by(|a, b| (a.n, a.k).cmp(&(b.n, b.k)));

        let pat = degree_pattern_key(pos.iter().map(|p| p.k).collect::<Vec<_>>());

        // q=2 deformation test
        let q = 2u32;
        let mut q2_vals: Vec<BigUint> = Vec::with_capacity(pos.len());
        for p in &pos {
            q2_vals.push(gauss_binom_eval(p.n, p.k, q));
        }
        let survives_q2 = q2_vals
            .first()
            .map(|first| q2_vals.iter().all(|x| x == first))
            .unwrap_or(false);

        // Apply q2-only filter
        if args.q2_only && !survives_q2 {
            continue;
        }

        pattern_groups.entry(pat.clone()).or_default().push(value.clone());

        shown += 1;
        if shown > args.collision_print_limit {
            break;
        }

        println!(
            "\nvalue={}  mult={}  bits={}  degree_pattern=[{}]  survives_at_q2={}",
            value,
            pos.len(),
            value.bits(),
            pat,
            survives_q2
        );

        print!("  positions:");
        for p in &pos {
            print!(" ({},{})", p.n, p.k);
        }
        println!();

        print!("  entropy(k/n):");
        for p in &pos {
            print!(" {:.6}", p.entropy);
        }
        println!();

        if args.print_q2_values {
            print!("  q=2 values:");
            for v2 in &q2_vals {
                print!(" {}", v2);
            }
            println!();
        }
    }

    if shown == 0 {
        println!("(none printed) — either no collisions met mult>=min_mult, or q2_only filtered them all out.");
    }

    if args.print_degree_pattern_summary {
        let mut pats: Vec<(String, Vec<BigUint>)> = pattern_groups.into_iter().collect();
        pats.sort_by(|(pa, va), (pb, vb)| vb.len().cmp(&va.len()).then_with(|| pa.cmp(pb)));

        println!("\nDegree-pattern summary (pattern -> how many collision-values share it):");
        for (pat, mut values) in pats {
            values.sort();
            println!(
                "  pattern=[{}]  collision_values_count={}  smallest_value={}  largest_value={}",
                pat,
                values.len(),
                values.first().unwrap(),
                values.last().unwrap()
            );
        }
    }

    println!("\nNotes:");
    println!("  - k=0 is always ignored.");
    println!("  - k=1 is ignored by default; pass --keep-k1 to include it.");
    println!("  - PASS1 uses (C(n,k) mod P1, C(n,k) mod P2) fingerprints to cheaply find candidates.");
    println!("  - PASS2 verifies candidates exactly via prime-exponent (Legendre) BigUint construction.");
    println!("  - Use --no-q2-only to print all q=1 collisions (including those that do not survive at q=2).");
    println!("  - Use --no-print-q2-values to suppress large q=2 numbers in output.");
}

// --------------------------
// PASS1: fingerprint helpers
// --------------------------

fn precompute_inverses(p: u64, k_max: u32) -> Vec<u64> {
    // inv[0] unused; inv[1]=1; inv[i] = p - (p/i) * inv[p%i] mod p for prime p.
    let km = k_max as usize;
    let mut inv = vec![0u64; km + 1];
    if km >= 1 {
        inv[1] = 1;
    }
    for i in 2..=km {
        let i_u64 = i as u64;
        let q = p / i_u64;
        let r = (p % i_u64) as usize;
        let prod = mul_mod_u64(q % p, inv[r], p);
        inv[i] = if prod == 0 { 0 } else { p - prod };
    }
    inv
}

fn fingerprint_binom_mod(n: u32, k: u32, inv1: &[u64], inv2: &[u64]) -> u128 {
    let r1 = binom_mod_prime(n, k, P1, inv1);
    let r2 = binom_mod_prime(n, k, P2, inv2);
    ((r1 as u128) << 64) | (r2 as u128)
}

fn binom_mod_prime(n: u32, k: u32, p: u64, inv: &[u64]) -> u64 {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }
    let k = k.min(n - k);
    let mut acc: u64 = 1;
    for i in 1..=k {
        let num = (n - k + i) as u64 % p;
        acc = mul_mod_u64(acc, num, p);
        acc = mul_mod_u64(acc, inv[i as usize], p);
    }
    acc
}

#[inline]
fn mul_mod_u64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % (m as u128)) as u64
}

// -------------------------------------
// PASS2: prime-exponent exact binomials
// -------------------------------------

fn sieve_primes(n_max: u32) -> Vec<u32> {
    if n_max < 2 {
        return vec![];
    }
    let n = n_max as usize;
    let mut is_prime = vec![true; n + 1];
    is_prime[0] = false;
    is_prime[1] = false;

    let mut p = 2usize;
    while p * p <= n {
        if is_prime[p] {
            let mut j = p * p;
            while j <= n {
                is_prime[j] = false;
                j += p;
            }
        }
        p += 1;
    }

    let mut primes = Vec::new();
    for i in 2..=n {
        if is_prime[i] {
            primes.push(i as u32);
        }
    }
    primes
}

fn v_p_factorial(mut n: u32, p: u32) -> u32 {
    let mut acc: u32 = 0;
    while n > 0 {
        n /= p;
        acc += n;
    }
    acc
}

fn binom_big_prime_exponent(n: u32, k: u32, primes: &[u32]) -> BigUint {
    if k > n {
        return BigUint::zero();
    }
    if k == 0 || k == n {
        return BigUint::one();
    }
    let k = k.min(n - k);

    let mut out = BigUint::one();
    for &p in primes {
        if p > n {
            break;
        }
        let e = v_p_factorial(n, p) - v_p_factorial(k, p) - v_p_factorial(n - k, p);
        if e > 0 {
            out *= BigUint::from(p as u64).pow(e);
        }
    }
    out
}

// ------------------------------------
// q=2 evaluation (Gaussian binomials)
// ------------------------------------

fn gauss_binom_eval(n: u32, k: u32, q: u32) -> BigUint {
    if k > n {
        return BigUint::zero();
    }
    if k == 0 || k == n {
        return BigUint::one();
    }
    assert!(q >= 2, "gauss_binom_eval expects q >= 2");

    let k = k.min(n - k);
    let q_big = BigUint::from(q as u64);

    let mut num = BigUint::one();
    let mut den = BigUint::one();

    for t in 1..=k {
        let exp_num = n - k + t;
        let exp_den = t;

        let mut a = q_big.pow(exp_num);
        let mut b = q_big.pow(exp_den);

        a -= BigUint::one();
        b -= BigUint::one();

        let g1 = gcd_big(&a, &den);
        if g1 > BigUint::one() {
            a /= &g1;
            den /= &g1;
        }

        let g2 = gcd_big(&b, &num);
        if g2 > BigUint::one() {
            b /= &g2;
            num /= &g2;
        }

        let g3 = gcd_big(&a, &b);
        if g3 > BigUint::one() {
            a /= &g3;
            b /= &g3;
        }

        num *= a;
        den *= b;

        let g = gcd_big(&num, &den);
        if g > BigUint::one() {
            num /= &g;
            den /= &g;
        }
    }

    if den != BigUint::one() {
        num / den
    } else {
        num
    }
}

fn gcd_big(a: &BigUint, b: &BigUint) -> BigUint {
    let mut x = a.clone();
    let mut y = b.clone();
    while !y.is_zero() {
        let r = &x % &y;
        x = y;
        y = r;
    }
    x
}

// --------------------------
// Reporting helper
// --------------------------

fn degree_pattern_key(mut ks: Vec<u32>) -> String {
    ks.sort_unstable();
    let mut out = String::new();
    for (i, k) in ks.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&k.to_string());
    }
    out
}
