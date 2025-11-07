use rc_hashmap::{InsertError, RcHashMap, Ref};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[test]
fn insert_get_clone_drop_removes() {
    let mut m = RcHashMap::new();
    let r = m.insert("k1".to_string(), 42).expect("insert ok");
    assert_eq!(m.len(), 1);
    assert!(m.contains_key(&"k1".to_string()));

    // find returns a new Ref and increments the count
    let g = m.find(&"k1".to_string()).expect("found");
    assert_eq!(*g.value(&m).expect("value borrow"), 42);

    // clone keeps entry alive
    let g2 = g.clone();
    drop(g);
    assert!(m.contains_key(&"k1".to_string()));

    // dropping the last runtime ref that's not `r` should keep entry (since `r` still alive)
    drop(g2);
    assert_eq!(m.len(), 1);
    assert!(m.contains_key(&"k1".to_string()));

    // drop the original returned ref as well; now removal should occur
    drop(r);
    assert_eq!(m.len(), 0);
    assert!(!m.contains_key(&"k1".to_string()));
}

#[test]
fn duplicate_insert_rejected() {
    let mut m = RcHashMap::new();
    let r = m.insert("dup".to_string(), 1).unwrap();
    let e = m.insert("dup".to_string(), 2);
    match e {
        Err(InsertError::DuplicateKey) => {}
        Ok(_) => panic!("expected duplicate insert to error"),
    }
    drop(r);
}

#[test]
fn ref_equality_and_hash() {
    let mut m = RcHashMap::new();
    let r1 = m.insert("a".to_string(), 10).unwrap();
    let r1b = r1.clone();
    assert!(r1 == r1b);

    let mut h1 = DefaultHasher::new();
    r1.hash(&mut h1);
    let mut h2 = DefaultHasher::new();
    r1b.hash(&mut h2);
    assert_eq!(h1.finish(), h2.finish());

    let r2 = m.insert("b".to_string(), 20).unwrap();
    assert!(r1 != r2);
}

#[test]
fn wrong_map_accessors_reject() {
    let mut m1 = RcHashMap::new();
    let m2 = RcHashMap::new();
    let r = m1.insert("a".to_string(), 11).unwrap();

    // Owner-checked accessors
    assert!(r.value(&m1).is_ok());
    assert!(r.key(&m1).is_ok());
    assert!(r.value_mut(&mut m1).is_ok());

    // Wrong map should be rejected
    assert!(r.value(&m2).is_err());
    assert!(r.key(&m2).is_err());
}

#[test]
fn iter_returns_refs() {
    let mut m = RcHashMap::new();
    let _ = m.insert("k1".to_string(), 1).unwrap();
    let _ = m.insert("k2".to_string(), 2).unwrap();
    let _ = m.insert("k3".to_string(), 3).unwrap();

    let count = m.iter().count();
    assert_eq!(count, m.len());

    // Values are reachable via returned Refs
    for r in m.iter() {
        let v = r.value(&m).expect("value borrow");
        assert!(*v == 1 || *v == 2 || *v == 3);
    }
}

#[test]
fn iter_mut_updates_and_allows_cloning_ref() {
    let mut m = RcHashMap::new();
    let r1 = m.insert("k1".to_string(), 1).unwrap();
    let r2 = m.insert("k2".to_string(), 2).unwrap();

    // Mutate values in place and keep clones alive until after iteration
    let mut held = Vec::new();
    for mut it in m.iter_mut() {
        *it.value_mut() += 10;
        // Clone a Ref from the item to keep the entry alive beyond this iteration
        held.push(it.r#ref().clone());
    }
    assert_eq!(m.len(), 2);

    // Verify values updated using existing Refs to keep tokens alive
    assert_eq!(*r1.value(&m).unwrap(), 11);
    assert_eq!(*r2.value(&m).unwrap(), 12);
}

// ---- DAG tests (values and keys hold Refs) ----

use std::fmt;

// Concrete types for DAG scenarios
#[derive(Clone)]
struct K {
    id: u32,
    hold: Option<Ref<K, V>>, // key may hold a Ref to another entry
}

impl K {
    fn new(id: u32) -> Self { Self { id, hold: None } }
    fn with_ref(id: u32, r: Ref<K, V>) -> Self { Self { id, hold: Some(r) } }
}

impl PartialEq for K { fn eq(&self, other: &Self) -> bool { self.id == other.id } }
impl Eq for K {}
impl Hash for K { fn hash<H: Hasher>(&self, state: &mut H) { self.id.hash(state) } }
impl fmt::Debug for K { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "K({})", self.id) } }

#[derive(Default)]
struct V {
    name: String,
    children: Vec<Ref<K, V>>, // DAG edges to other entries
}

impl fmt::Debug for V {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Node({},{})", self.name, self.children.len()) }
}

type M = RcHashMap<K, V>;

fn probe(id: u32) -> K { K { id, hold: None } }

#[test]
fn value_dag_cascade_drop() {
    // Build: B.value -> C; then drop C (kept alive by B.value), drop B; C should be removed during B's value drop.
    let mut m: M = RcHashMap::new();

    let r_a = m.insert(K::new(1), V { name: "A".into(), children: vec![] }).unwrap();
    let r_b = m.insert(K::new(2), V { name: "B".into(), children: vec![] }).unwrap();
    let r_c = m.insert(K::new(3), V { name: "C".into(), children: vec![] }).unwrap();

    // B -> C
    {
        let b = r_b.value_mut(&mut m).unwrap();
        b.children.push(r_c.clone());
    }

    // Drop external C; C remains due to B.children
    drop(r_c);
    assert!(m.contains_key(&probe(3)));

    // Now drop B; should remove B, and during drop of B.value drop C's Ref, removing C.
    drop(r_b);
    assert!(!m.contains_key(&probe(2)));
    assert!(!m.contains_key(&probe(3)));

    // A remains
    assert!(m.contains_key(&probe(1)));
    drop(r_a);
}

#[test]
fn key_holds_ref_cascade() {
    // Build: Y.key holds Ref(X). Drop X external, then drop Y; dropping Y.key's Ref removes X.
    let mut m: M = RcHashMap::new();

    let r_x = m.insert(K::new(10), V { name: "X".into(), children: vec![] }).unwrap();
    let r_y = m.insert(K::with_ref(20, r_x.clone()), V { name: "Y".into(), children: vec![] }).unwrap();

    // After dropping external X, it survives thanks to Y.key
    drop(r_x);
    assert!(m.contains_key(&probe(10)));

    // Drop Y; its key drops Ref(X) and cascades X removal
    drop(r_y);
    assert!(!m.contains_key(&probe(20)));
    assert!(!m.contains_key(&probe(10)));
}

#[test]
fn deep_key_chain_drop_cascades() {
    // Z.key -> Y, Y.key -> X; dropping Z then Y should cascade and finally drop X through key drops.
    let mut m: M = RcHashMap::new();

    let r_x = m.insert(K::new(1), V { name: "X".into(), children: vec![] }).unwrap();
    let r_y = m.insert(K::with_ref(2, r_x.clone()), V { name: "Y".into(), children: vec![] }).unwrap();
    let r_z = m.insert(K::with_ref(3, r_y.clone()), V { name: "Z".into(), children: vec![] }).unwrap();

    // Drop Z external; Z removed, drops key's Ref to Y; Y still has external r_y, so still present.
    drop(r_z);
    assert!(!m.contains_key(&probe(3)));
    assert!(m.contains_key(&probe(2)));
    assert!(m.contains_key(&probe(1)));

    // Drop Y external; Y removed, key's Ref to X dropped; X had only r_x external, so keep it for now.
    drop(r_y);
    assert!(!m.contains_key(&probe(2)));
    assert!(m.contains_key(&probe(1)));

    // Finally drop X external; no more refs -> X removed
    drop(r_x);
    assert!(!m.contains_key(&probe(1)));
}

// ---- Drops during iter and borrows ----

#[test]
fn drop_other_refs_during_iter() {
    let mut m: RcHashMap<String, i32> = RcHashMap::new();
    let r1 = m.insert("a".into(), 1).unwrap();
    let r2 = m.insert("b".into(), 2).unwrap();
    let r3 = m.insert("c".into(), 3).unwrap();

    let mut keep = vec![r1.clone(), r2.clone(), r3.clone()];

    let mut seen = 0;
    for r in m.iter() {
        if let Some(x) = keep.pop() { drop(x); }
        let _ = r.value(&m).unwrap();
        seen += 1;
    }
    assert_eq!(seen, 3);
}

#[test]
fn drop_refs_during_iter_mut_and_update() {
    let mut m: RcHashMap<String, i32> = RcHashMap::new();
    let r1 = m.insert("x".into(), 10).unwrap();
    let r2 = m.insert("y".into(), 20).unwrap();

    for mut item in m.iter_mut() {
        *item.value_mut() += 1;
        if item.key() == &"x" { drop(r2.clone()); } else { drop(r1.clone()); }
    }

    if let Some(rx) = m.find(&"x".to_string()) {
        assert_eq!(*rx.value(&m).unwrap(), 11);
    }
    if let Some(ry) = m.find(&"y".to_string()) {
        assert_eq!(*ry.value(&m).unwrap(), 21);
    }
}

#[test]
fn hold_shared_value_and_drop_others() {
    let mut m: RcHashMap<String, i32> = RcHashMap::new();
    let ra = m.insert("a".into(), 1).unwrap();
    let rb = m.insert("b".into(), 2).unwrap();

    {
        let va = ra.value(&m).unwrap();
        assert_eq!(*va, 1);
        drop(rb);
    }

    assert!(m.contains_key(&"a".to_string()));
    assert!(!m.contains_key(&"b".to_string()));

    drop(ra);
}

#[test]
fn hold_mut_value_and_drop_others() {
    let mut m: RcHashMap<String, i32> = RcHashMap::new();
    let ra = m.insert("a".into(), 10).unwrap();
    let rb = m.insert("b".into(), 20).unwrap();

    {
        let va = ra.value_mut(&mut m).unwrap();
        *va += 5;
        drop(rb);
    }

    let ra2 = m.find(&"a".to_string()).unwrap();
    assert_eq!(*ra2.value(&m).unwrap(), 15);
    assert!(!m.contains_key(&"b".to_string()));

    drop(ra);
    drop(ra2);
}

#[test]
fn refs_survive_map_drop_and_can_clone_then_drop() {
    let r = {
        let mut m: RcHashMap<String, i32> = RcHashMap::new();
        m.insert("k".into(), 7).unwrap()
    }; // drop map here

    let r2 = r.clone();
    let r3 = r2.clone();
    drop(r);
    drop(r2);
    drop(r3);
}

