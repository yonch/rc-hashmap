use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use rc_hashmap::counted_hash_map::{CountedHashMap, PutResult};
use std::time::Duration;

fn lcg(mut s: u64) -> impl Iterator<Item = u64> {
    std::iter::from_fn(move || {
        s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
        Some(s)
    })
}

fn key(n: u64) -> String {
    format!("k{:016x}", n)
}

fn bench_insert_fresh_100k(c: &mut Criterion) {
    c.bench_function("counted::insert_fresh_100k", |b| {
        b.iter_batched(
            CountedHashMap::<String, u64>::new,
            |mut m| {
                let mut hs = Vec::with_capacity(100_000);
                for (i, x) in lcg(1).take(100_000).enumerate() {
                    hs.push(m.insert(key(x), i as u64).unwrap());
                }
                // Return tokens to avoid panic; included in measurement.
                for h in hs { let _ = m.put(h); }
                black_box(m)
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_insert_warm_100k(c: &mut Criterion) {
    c.bench_function("counted::insert_warm_100k", |b| {
        b.iter_batched(
            || {
                let mut m = CountedHashMap::new();
                // Grow to 110k then remove all to keep capacity
                let handles: Vec<_> = lcg(2)
                    .take(110_000)
                    .enumerate()
                    .map(|(i, x)| m.insert(key(x), i as u64).unwrap())
                    .collect();
                for h in handles { let _ = m.put(h); }
                m
            },
            |mut m| {
                let mut hs = Vec::with_capacity(100_000);
                for (i, x) in lcg(3).take(100_000).enumerate() {
                    hs.push(m.insert(key(x), i as u64).unwrap());
                }
                for h in hs { let _ = m.put(h); }
                black_box(m)
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_remove_random_10k(c: &mut Criterion) {
    c.bench_function("counted::remove_random_10k_of_110k", |b| {
        b.iter_batched(
            || {
                let mut m = CountedHashMap::new();
                let handles: Vec<Option<_>> = lcg(5)
                    .take(110_000)
                    .enumerate()
                    .map(|(i, x)| Some(m.insert(key(x), i as u64).unwrap()))
                    .collect();
                (m, handles)
            },
            |(mut m, mut handles)| {
                // Remove 10k pseudo-random via put(); skip duplicates.
                let mut s = 0x9e3779b97f4a7c15u64;
                let n = handles.len() as u64;
                let mut removed = 0usize;
                while removed < 10_000 {
                    s = s.wrapping_mul(2862933555777941757).wrapping_add(3037000493);
                    let idx = (s % n) as usize;
                    if let Some(h) = handles.get_mut(idx).and_then(Option::take) {
                        match m.put(h) {
                            PutResult::Live => {}
                            PutResult::Removed { .. } => {}
                        }
                        removed += 1;
                    }
                }
                // Return remaining tokens
                for h in handles.into_iter().flatten() { let _ = m.put(h); }
                black_box(m)
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_find_hit_10k(c: &mut Criterion) {
    c.bench_function("counted::find_hit_10k_on_100k", |b| {
        let mut m = CountedHashMap::new();
        let keys: Vec<_> = lcg(7).take(100_000).map(key).collect();
        let held: Vec<_> = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, k)| m.insert(k, i as u64).unwrap())
            .collect();
        // Keep tokens alive for the duration of the benchmark; avoid drop at end.
        core::mem::forget(held);
        let mut it = keys.iter().cycle();
        b.iter(|| {
            for _ in 0..10_000 {
                let k = it.next().unwrap();
                if let Some(h) = m.find(k) { let _ = m.put(h); }
            }
        })
    });
}

fn bench_find_miss_10k(c: &mut Criterion) {
    c.bench_function("counted::find_miss_10k_on_100k", |b| {
        let mut m = CountedHashMap::new();
        let held: Vec<_> = lcg(11)
            .take(100_000)
            .enumerate()
            .map(|(i, x)| m.insert(key(x), i as u64).unwrap())
            .collect();
        core::mem::forget(held);
        let mut miss = lcg(0xdead_beef);
        b.iter(|| {
            for _ in 0..10_000 {
                let k = key(miss.next().unwrap());
                black_box(m.find(&k));
            }
        })
    });
}

fn bench_handle_access_increment(c: &mut Criterion) {
    c.bench_function("counted::handle_access_increment_10k", |b| {
        b.iter_batched(
            || {
                let mut m = CountedHashMap::new();
                let handles: Vec<_> = lcg(123)
                    .take(10_000)
                    .enumerate()
                    .map(|(i, x)| m.insert(key(x), i as u64).unwrap())
                    .collect();
                (m, handles)
            },
            |(mut m, handles)| {
                let mut idx = 0usize;
                for _ in 0..10_000 {
                    let h = &handles[idx];
                    if let Some(v) = h.value_mut(&mut m) {
                        *v = v.wrapping_add(1);
                    }
                    idx += 1;
                    if idx == handles.len() { idx = 0; }
                }
                // Return tokens to avoid panic
                for h in handles { let _ = m.put(h); }
                black_box(m)
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_iter_and_iter_mut(c: &mut Criterion) {
    c.bench_function("counted::iter_all_100k", |b| {
        b.iter_batched(
            || {
                let mut m = CountedHashMap::new();
                let held: Vec<_> = lcg(999)
                    .take(100_000)
                    .enumerate()
                    .map(|(i, x)| m.insert(key(x), i as u64).unwrap())
                    .collect();
                core::mem::forget(held);
                m
            },
            |m| {
                let mut sum = 0u64;
                for (_h, _k, v) in m.iter() { sum = sum.wrapping_add(*v); }
                black_box(sum)
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("counted::iter_mut_increment_all_100k", |b| {
        b.iter_batched(
            || {
                let mut m = CountedHashMap::new();
                let held: Vec<_> = lcg(1001)
                    .take(100_000)
                    .enumerate()
                    .map(|(i, x)| m.insert(key(x), i as u64).unwrap())
                    .collect();
                core::mem::forget(held);
                m
            },
            |mut m| {
                for (_h, _k, v) in m.iter_mut() { *v = v.wrapping_add(1); }
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
              bench_find_hit_10k,
              bench_find_miss_10k,
              bench_handle_access_increment,
              bench_iter_and_iter_mut
}
criterion_main!(benches_insert, benches_ops);
