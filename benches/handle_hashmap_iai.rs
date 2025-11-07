#[cfg(target_os = "linux")]
mod bench {
    use iai::black_box;
    use rc_hashmap::handle_hash_map::HandleHashMap;

    fn lcg(mut s: u64) -> impl Iterator<Item = u64> {
        std::iter::from_fn(move || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
            Some(s)
        })
    }

    fn key(n: u64) -> String {
        format!("k{:016x}", n)
    }

    // Insert 10k entries.
    pub fn handle_hashmap_insert_10k() {
        let mut m = HandleHashMap::<String, u64>::new();
        for (i, x) in lcg(1).take(10_000).enumerate() {
            let _ = m.insert(key(x), i as u64).unwrap();
        }
        black_box(m);
    }

    // Repeated hits on existing keys.
    pub fn handle_hashmap_find_hit() {
        let mut m = HandleHashMap::new();
        let keys: Vec<_> = lcg(7).take(20_000).map(key).collect();
        for (i, k) in keys.iter().enumerate() {
            let _ = m.insert(k.clone(), i as u64).unwrap();
        }
        let mut it = keys.iter().cycle();
        for _ in 0..10_000 {
            let k = it.next().unwrap();
            black_box(m.find(k));
        }
    }

    // Repeated misses for keys unlikely to be present.
    pub fn handle_hashmap_find_miss() {
        let mut m = HandleHashMap::new();
        for (i, x) in lcg(11).take(10_000).enumerate() {
            let _ = m.insert(key(x), i as u64).unwrap();
        }
        let mut miss = lcg(0xdead_beef);
        for _ in 0..10_000 {
            let k = key(miss.next().unwrap());
            black_box(m.find(&k));
        }
    }

    // Remove by handle.
    pub fn handle_hashmap_remove_by_handle() {
        let mut m = HandleHashMap::new();
        let h = m.insert("k".to_string(), 1u64).unwrap();
        black_box(m.remove(h));
    }
}

#[cfg(target_os = "linux")]
iai::main!(
    bench::handle_hashmap_insert_10k,
    bench::handle_hashmap_find_hit,
    bench::handle_hashmap_find_miss,
    bench::handle_hashmap_remove_by_handle
);

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("Skipping: iai benches require Linux/valgrind.");
}
