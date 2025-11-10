use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use rand_core::{RngCore, SeedableRng};
use rand_pcg::Lcg128Xsl64 as Pcg;
use rc_hashmap::RcHashMap;
use std::time::Duration;

fn key(n: u64) -> String {
    format!("k{:016x}", n)
}

fn bench_insert_fresh_100k(c: &mut Criterion) {
    c.bench_function("rc::insert_fresh_100k", |b| {
        b.iter_batched(
            RcHashMap::<String, u64>::new,
            |mut m| {
                let mut rng = Pcg::seed_from_u64(1);
                let mut refs = Vec::with_capacity(100_000);
                for i in 0..100_000 {
                    refs.push(m.insert(key(rng.next_u64()), i as u64).unwrap());
                }
                black_box((m, refs))
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_insert_warm_100k(c: &mut Criterion) {
    c.bench_function("rc::insert_warm_100k", |b| {
        b.iter_batched(
            || {
                let mut m = RcHashMap::new();
                let mut rng = Pcg::seed_from_u64(2);
                let refs: Vec<_> = (0..110_000)
                    .map(|i| m.insert(key(rng.next_u64()), i as u64).unwrap())
                    .collect();
                drop(refs);
                m
            },
            |mut m| {
                let mut rng = Pcg::seed_from_u64(3);
                let mut refs = Vec::with_capacity(100_000);
                for i in 0..100_000 {
                    refs.push(m.insert(key(rng.next_u64()), i as u64).unwrap());
                }
                black_box((m, refs))
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_remove_random_10k(c: &mut Criterion) {
    c.bench_function("rc::remove_random_10k_of_110k", |b| {
        b.iter_batched(
            || {
                let mut m = RcHashMap::new();
                let mut rng = Pcg::seed_from_u64(5);
                let all: Vec<_> = (0..110_000)
                    .map(|i| m.insert(key(rng.next_u64()), i as u64).unwrap())
                    .collect();
                // Precompute 10k unique indices via PCG
                let n = all.len();
                let mut sel = std::collections::HashSet::with_capacity(10_000);
                let mut idx_rng = Pcg::seed_from_u64(0x9e3779b97f4a7c15);
                while sel.len() < 10_000 { sel.insert((idx_rng.next_u64() as usize) % n); }
                let mut to_drop = Vec::with_capacity(10_000);
                let mut remain = Vec::with_capacity(n - 10_000);
                for (i, r) in all.into_iter().enumerate() {
                    if sel.contains(&i) { to_drop.push(r); } else { remain.push(r); }
                }
                (m, to_drop, remain)
            },
            |(m, to_drop, remain)| {
                for r in to_drop { drop(r); }
                // Defer drop of remaining refs to after timing
                black_box((m, remain))
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_get_hit_10k(c: &mut Criterion) {
    c.bench_function("rc::get_hit_10k_on_100k", |b| {
        let mut m = RcHashMap::new();
        let mut rng_keys = Pcg::seed_from_u64(7);
        let keys: Vec<_> = (0..100_000).map(|_| key(rng_keys.next_u64())).collect();
        let _held: Vec<_> = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, k)| m.insert(k, i as u64).unwrap())
            .collect();
        // Precompute 10k random query keys using PCG
        let n = keys.len();
        let mut rng_q = Pcg::seed_from_u64(0x9e3779b97f4a7c15);
        let queries: Vec<String> = (0..10_000)
            .map(|_| keys[(rng_q.next_u64() as usize) % n].clone())
            .collect();
        b.iter(|| {
            for k in &queries { let r = m.find(k).unwrap(); black_box(r); }
        })
    });
}

fn bench_get_miss_10k(c: &mut Criterion) {
    c.bench_function("rc::get_miss_10k_on_100k", |b| {
        let mut m = RcHashMap::new();
        let mut rng_ins = Pcg::seed_from_u64(11);
        for i in 0..100_000 {
            let _ = m.insert(key(rng_ins.next_u64()), i as u64).unwrap();
        }
        let mut miss = Pcg::seed_from_u64(0xdead_beefu64);
        b.iter(|| {
            for _ in 0..10_000 {
                let k = key(miss.next_u64());
                black_box(m.find(&k));
            }
        })
    });
}

fn bench_handle_access_increment(c: &mut Criterion) {
    c.bench_function("rc::handle_access_increment_10k", |b| {
        b.iter_batched(
            || {
                let mut m: RcHashMap<String, u64> = RcHashMap::new();
                let mut rng = Pcg::seed_from_u64(123);
                let refs: Vec<_> = (0..100_000)
                    .map(|i| m.insert(key(rng.next_u64()), i as u64).unwrap())
                    .collect();
                // Precompute 10k random refs to touch
                let n = refs.len();
                let mut rsel = Pcg::seed_from_u64(0x9e3779b97f4a7c15);
                let mut targets = Vec::with_capacity(10_000);
                for _ in 0..10_000 {
                    let idx = (rsel.next_u64() as usize) % n;
                    targets.push(refs[idx].clone());
                }
                // Keep original refs alive as well to avoid removal; drop after timing
                let remain = refs;
                (m, targets, remain)
            },
            |(mut m, targets, remain)| {
                for r in &targets { let v = r.value_mut(&mut m).unwrap(); *v = v.wrapping_add(1); }
                // Return both map and refs so ref-drop occurs after timing
                black_box((m, targets, remain))
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_iter_and_iter_mut(c: &mut Criterion) {
    c.bench_function("rc::iter_all_100k", |b| {
        let mut m = RcHashMap::new();
        let mut rng = Pcg::seed_from_u64(999);
        let _held: Vec<_> = (0..100_000)
            .map(|i| m.insert(key(rng.next_u64()), i as u64).unwrap())
            .collect();
        b.iter(|| {
            let mut cnt = 0usize;
            for _r in m.iter() {
                cnt += 1;
            }
            black_box(cnt)
        })
    });

    c.bench_function("rc::iter_mut_increment_all_100k", |b| {
        b.iter_batched(
            || {
                let mut m: RcHashMap<String, u64> = RcHashMap::new();
                let mut rng = Pcg::seed_from_u64(1001);
                let _held: Vec<_> = (0..100_000)
                    .map(|i| m.insert(key(rng.next_u64()), i as u64).unwrap())
                    .collect();
                m
            },
            |mut m| {
                for mut item in m.iter_mut() {
                    let v = item.value_mut();
                    *v = v.wrapping_add(1);
                }
                black_box(m)
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_config() -> Criterion {
    Criterion::default()
        .sample_size(12)
        .measurement_time(Duration::from_secs(5))
        .warm_up_time(Duration::from_secs(1))
}

criterion_group! {
    name = benches_insert;
    config = bench_config();
    targets = bench_insert_fresh_100k, bench_insert_warm_100k
}
criterion_group! {
    name = benches_ops;
    config = bench_config();
    targets = bench_remove_random_10k,
              bench_get_hit_10k,
              bench_get_miss_10k,
              bench_handle_access_increment,
              bench_iter_and_iter_mut
}
criterion_main!(benches_insert, benches_ops);
