use clap::Parser;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::collections::HashMap;

/// Singmaster exploration lab:
/// - exact BigUint binomials
/// - multiplicity map value -> positions (n,k)
/// - report top multiplicities / collisions
#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// Max n to scan (inclusive).
    #[arg(long, default_value_t = 200)]
    n_max: u32,

    /// If set, only keep k <= n/2 (removes trivial symmetry).
    #[arg(long, default_value_t = true)]
    half_triangle: bool,

    /// Report the top K most frequent values found.
    #[arg(long, default_value_t = 20)]
    top_k: usize,

    /// Minimum multiplicity to print.
    #[arg(long, default_value_t = 2)]
    min_mult: usize,

    /// Also print example nontrivial collisions (distinct positions same value).
    #[arg(long, default_value_t = true)]
    print_collisions: bool,

    /// Limit number of collision values printed (to avoid huge output).
    #[arg(long, default_value_t = 50)]
    collision_print_limit: usize,
}

/// Exact binomial coefficient C(n,k) as BigUint, via multiplicative product with reduction.
/// Complexity OK up to a few thousand with BigUint, more if you optimize prime-factor method.
fn binom_big(n: u32, k: u32) -> BigUint {
    if k > n {
        return BigUint::zero();
    }
    if k == 0 || k == n {
        return BigUint::one();
    }
    let k = k.min(n - k); // symmetry for speed
    let mut num = BigUint::one();
    let mut den = BigUint::one();

    for i in 1..=k {
        // multiply numerator by (n - k + i)
        let a = BigUint::from((n - k + i) as u64);
        let b = BigUint::from(i as u64);
        num *= a;
        den *= b;

        // keep numbers small by gcd reduction each step
        let g = gcd_big(&num, &den);
        if g > BigUint::one() {
            num /= &g;
            den /= &g;
        }
    }

    // den should be 1 after reductions, but to be safe:
    if den != BigUint::one() {
        num / den
    } else {
        num
    }
}

/// Euclid gcd for BigUint.
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

fn main() {
    let args = Args::parse();

    // value -> Vec<(n,k)>
    let mut hits: HashMap<BigUint, Vec<(u32, u32)>> = HashMap::new();

    for n in 0..=args.n_max {
        let k_max = if args.half_triangle { n / 2 } else { n };
        for k in 0..=k_max {
            let v = binom_big(n, k);
            hits.entry(v).or_default().push((n, k));
        }
    }

    // Gather and sort by multiplicity desc, then by value size (approx via bit length) asc.
    let mut mults: Vec<(usize, BigUint)> = hits
        .iter()
        .map(|(v, pos)| (pos.len(), v.clone()))
        .collect();

    mults.sort_by(|(ca, va), (cb, vb)| {
        cb.cmp(ca)
            .then_with(|| va.bits().cmp(&vb.bits()))
            .then_with(|| va.cmp(vb))
    });

    println!(
        "Scanned n=0..={} (half_triangle={}), unique values={}",
        args.n_max,
        args.half_triangle,
        hits.len()
    );

    println!("\nTop multiplicities (min_mult >= {}):", args.min_mult);
    let mut printed = 0usize;
    for (count, value) in mults.iter() {
        if *count < args.min_mult {
            break;
        }
        printed += 1;
        if printed > args.top_k {
            break;
        }
        let positions = &hits[value];
        println!(
            "mult={}  bits={}  value={}",
            count,
            value.bits(),
            value
        );
        if args.print_collisions {
            // Print positions (n,k)
            let mut ps = positions.clone();
            ps.sort();
            print!("  positions:");
            for (n, k) in ps {
                print!(" ({},{})", n, k);
            }
            println!();
        }
    }

    if args.print_collisions {
        println!("\nExample collision values (nontrivial):");
        let mut shown = 0usize;
        for (count, value) in mults.iter() {
            if *count < 2 {
                break;
            }
            // Avoid printing ultra-trivial edge values if you want; for now we print all.
            let positions = &hits[value];
            if positions.len() >= args.min_mult {
                shown += 1;
                println!(
                    "value={}  mult={}  sample_positions={:?}",
                    value,
                    positions.len(),
                    &positions[..positions.len().min(10)]
                );
                if shown >= args.collision_print_limit {
                    break;
                }
            }
        }
    }
}
