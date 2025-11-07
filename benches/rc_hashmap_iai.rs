#[cfg(target_os = "linux")]
mod bench {
    use iai::black_box;
    use rc_hashmap::RcHashMap;

    fn lcg(mut s: u64) -> impl Iterator<Item = u64> {
        std::iter::from_fn(move || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
            Some(s)
        })
    }

    fn key(n: u64) -> String {
        format!("k{:016x}", n)
    }

    // Insert 10k entries holding refs to avoid immediate removals.
    pub fn rc_hashmap_insert_10k() {
        let mut m = RcHashMap::<String, u64>::new();
        let mut refs = Vec::with_capacity(10_000);
        for (i, x) in lcg(1).take(10_000).enumerate() {
            refs.push(m.insert(key(x), i as u64).unwrap());
        }
        black_box((m.len(), refs.len()));
    }

    // Repeated hits on existing keys.
    pub fn rc_hashmap_get_hit() {
        let mut m = RcHashMap::new();
        let keys: Vec<_> = lcg(7).take(20_000).map(key).collect();
        // Keep the inserted refs alive so entries remain in the map.
        let _held: Vec<_> = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, k)| m.insert(k, i as u64).unwrap())
            .collect();

        // Perform 10k successful lookups.
        let mut it = keys.iter().cycle();
        for _ in 0..10_000 {
            let k = it.next().unwrap();
            let r = m.find(k).unwrap();
            black_box(&r);
        }
    }

    // Repeated misses for keys unlikely to be present.
    pub fn rc_hashmap_get_miss() {
        let mut m = RcHashMap::new();
        for (i, x) in lcg(11).take(10_000).enumerate() {
            let _ = m.insert(key(x), i as u64).unwrap();
        }
        let mut miss = lcg(0xdead_beef);
        for _ in 0..10_000 {
            let k = key(miss.next().unwrap());
            black_box(m.find(&k));
        }
    }

    // Clone and drop a Ref repeatedly.
    pub fn rc_hashmap_clone_drop_ref() {
        let mut m = RcHashMap::new();
        let r = m.insert("key".to_string(), 1u64).unwrap();
        for _ in 0..10_000 {
            let x = r.clone();
            black_box(&x);
            drop(x);
        }
    }
}

#[cfg(target_os = "linux")]
iai::main!(
    bench::rc_hashmap_insert_10k,
    bench::rc_hashmap_get_hit,
    bench::rc_hashmap_get_miss,
    bench::rc_hashmap_clone_drop_ref
);

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("Skipping: iai benches require Linux/valgrind.");
}
